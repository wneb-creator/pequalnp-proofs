import PEqualNP.Defs

-- The signed circuit and cofactor framework follows L_meta_10802, L_meta_1674, L_meta_670,
-- and the checker in L_meta_1667 (Apache-2.0).
-- The verified restriction bounds and monotone witness below concern this graph.

namespace PEqualNP.Outside.L_meta_10760
open PEqualNP.CircuitLowerBounds
abbrev Sig := BitVec 128
def zero : Sig := 0
def one : Sig := BitVec.allOnes 128
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

def bit (i : Fin 128) (a : Sig) : Bool := a.getLsbD i.val
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


abbrev Row := Fin 128
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

def inputs : List Sig := [0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffff0000ffff0000ffff0000ffff0000,0xffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000]
def graph : Sig := 0xfffffffffffefffafffeffeefefeeca0
def sample (r : Row) (j : Fin 7) := bit r (inputs.getD j.val zero)
def edge (x : Fin 7 → Bool) : Bool :=
 (x 0 && x 2) || (x 1 && x 3) || (x 0 && x 4) || (x 1 && x 4) || (x 2 && x 4) || (x 0 && x 5) || (x 1 && x 5) || (x 3 && x 5) || (x 0 && x 6) || (x 2 && x 6) || (x 3 && x 6) || (x 5 && x 6)
theorem edge_table : ∀ r : Row, bit r graph = edge (sample r) := by decide +kernel
theorem graph_proper : proper graph := by unfold proper; decide +kernel
theorem input_list : List.ofFn (fun j : Fin 7 => inputs.getD j.val zero) = inputs := rfl
theorem sampled (r : Row) : List.ofFn (sample r) = inputs.map (bit r) := by
  rw [←input_list]
  rw [List.map_ofFn]
  rfl

theorem table_eval (C : Circuit) (h : PEqualNP.MetaComplexity.FanInTwo C)
    (i : Nat) (r : Row) : bit r ((execute C.gates inputs).getD i zero) =
      (C.wires (List.ofFn (sample r))).getD i false := by
  rw [←b_read,execute_bits _ _ _ (fun g hg => (h g hg).1),sampled]
  rfl

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
  if h : r.val < 128-d.val then ⟨d.val+r.val,by omega⟩ else ⟨r.val-(128-d.val),by omega⟩
def backwards (d : Row) : Row := Fin.ofNat 128 (128-d.val)
def rowMove (m : Move) (r : Row) : Row :=
  if bit r m.1 then shifted m.2.2 r else if bit r m.2.1 then shifted (backwards m.2.2) r else r
def mux (m a b : Sig) := (m &&& a) ||| (~~~m &&& b)
def wordMove (m : Move) (a : Sig) :=
  mux m.1 (a.rotateRight m.2.2.val) (mux m.2.1 (a.rotateRight (backwards m.2.2).val) a)

theorem bit_shift (d r : Row) (a : Sig) : bit r (a.rotateRight d.val) = bit (shifted d r) a := by
  unfold bit
  rw [BitVec.getLsbD_rotateRight_of_lt d.isLt]
  by_cases h : r.val < 128-d.val <;> simp [shifted,h,r.isLt]

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
  (List.range 7).filterMap fun i => if m.testBit i then some (i,inputs.getD i zero) else none
def vars (m : Nat) := (selected m).map Prod.snd
def typeWord (t : Nat) : Sig := bin (t/81) (inputs.getD (t/9 % 9) zero) (inputs.getD (t % 9) zero)
def varsX (m : Nat) : List Sig := if m<512 then vars m else vars m ++ [typeWord (m/512-1)]
def vertex (m j : Nat) := if m.testBit j then inputs.getD j zero else zero
def graphGoal (m : Nat) : Sig :=
  let x := vertex m
 (x 0 &&& x 2) ||| (x 1 &&& x 3) ||| (x 0 &&& x 4) ||| (x 1 &&& x 4) ||| (x 2 &&& x 4) ||| (x 0 &&& x 5) ||| (x 1 &&& x 5) ||| (x 3 &&& x 5) ||| (x 0 &&& x 6) ||| (x 2 &&& x 6) ||| (x 3 &&& x 6) ||| (x 5 &&& x 6)
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
    BitVec.ofNat 128 ((cube0 (fixed &&& 7)*cube3 ((fixed >>> 3) &&& 7)*cube6 ((fixed >>> 6) &&& 7)) <<< o)
def fixRows (z o : Nat) : List Move :=
  (List.range 7).filterMap fun j =>
    let x := inputs.getD j zero
    let step := Fin.ofNat 128 (1 <<< j)
    if z.testBit j then some (zero,x,step)
    else if o.testBit j then some (~~~x,zero,step) else none
def swapRows (v : Nat) : Move :=
  let i := v &&& 15
  let j := v >>> 4
  let a := inputs.getD i zero
  let b := inputs.getD j zero
  let d := (1 <<< j)-(1 <<< i)
  (a &&& ~~~b,b &&& ~~~a,Fin.ofNat 128 d)

def supportPairs (t : Nat) (mask : Nat) : List (Sig × Row × Row) :=
  (selected mask).map fun (i,a) =>
    let r := if t/81==2 && i==t/9 % 9 then 1 <<< (t % 9) else if t/81==2 && i==t % 9 then 1 <<< (t/9 % 9) else 0
    (a,Fin.ofNat 128 r,Fin.ofNat 128 (r ||| (1 <<< i)))

def graphPairs (m hints : Nat) : List (Sig × Row × Row) :=
  (selected m).map fun (i,a) =>
    let r := 1 <<< ((hints >>> (4*i)) &&& 15)
    (a,Fin.ofNat 128 r,Fin.ofNat 128 (r ||| (1 <<< i)))

def properB (T : Sig) := T != zero && T != one
theorem proper_of (T : Sig) (h : properB T = true) : proper T := by
  simpa only [properB,proper,Bool.and_eq_true,bne_iff_ne] using h
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



def target (x : Fin 7 → Bool) : Bool := decide (∃ i < ([0, 2, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 2, 6, 3, 6, 5, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 2, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 2, 6, 3, 6, 5, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 2, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 2, 6, 3, 6, 5, 6] : List ℕ).getD (2 * i + 1) 0) false = true)
def smallCircuit : Circuit := ⟨[⟨.or, [1, 6]⟩, ⟨.or, [3, 5]⟩, ⟨.and, [7, 8]⟩, ⟨.or, [0, 2]⟩, ⟨.or, [10, 1]⟩, ⟨.and, [4, 11]⟩, ⟨.or, [2, 5]⟩, ⟨.and, [0, 13]⟩, ⟨.and, [3, 5]⟩, ⟨.and, [6, 10]⟩, ⟨.or, [9, 12]⟩, ⟨.or, [17, 14]⟩, ⟨.or, [18, 15]⟩, ⟨.or, [19, 16]⟩], 20⟩

theorem witnessMonotone : ∀ g ∈ smallCircuit.gates,
    (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [smallCircuit,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first | exact ⟨Or.inl rfl,by decide⟩ | exact ⟨Or.inr rfl,by decide⟩

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem witnessCorrect : ∀ x : Fin 7 → Bool, smallCircuit.eval (List.ofFn x) = target x := by
  decide +kernel

theorem witnessSize : smallCircuit.gates.length = 14 := rfl

theorem noNotReuse {gates : List Gate} (fit : ∀ g ∈ gates,
    (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2)
    (h : ∀ g ∈ gates, g.op ≠ GateOp.not) :
    ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  obtain ⟨ops,arity⟩ := fit g hg
  refine ⟨?_,arity⟩
  rcases ops with a | b | c
  · exact Or.inl a
  · exact Or.inr b
  · exact (h g hg c).elim


def sevenInputs : List Sig := vars 127
def sampleSeven (r : Row) (i : Fin 7) : Bool := bit r (sevenInputs.getD i.val zero)
theorem sevenList : List.ofFn (fun i : Fin 7 => sevenInputs.getD i.val zero) = sevenInputs := rfl
theorem sevenSampled (r : Row) : List.ofFn (sampleSeven r) = sevenInputs.map (bit r) := by
  rw [←sevenList,List.map_ofFn]
  rfl

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem sevenTable : ∀ r : Row, bit r graph = target (sampleSeven r) := by decide +kernel

theorem sevenEval (C : Circuit) (h : PEqualNP.MetaComplexity.FanInTwo C)
    (i : Nat) (r : Row) : bit r ((execute C.gates sevenInputs).getD i zero) =
      (C.wires (List.ofFn (sampleSeven r))).getD i false := by
  rw [←b_read,execute_bits _ _ _ (fun g hg => (h g hg).1),sevenSampled]
  rfl

def lowRow (i : Fin 7) : Row := Fin.ofNat 128 (1 <<< ([2, 3, 0, 1, 0, 0, 0] : List Nat).getD i.val 0)
def highRow (i : Fin 7) : Row := Fin.ofNat 128 ((1 <<< i.val) ||| (1 <<< ([2, 3, 0, 1, 0, 0, 0] : List Nat).getD i.val 0))

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem allSevenRequired :
    (∀ i : Fin 7, bit (lowRow i) graph ≠ bit (highRow i) graph) ∧
    (∀ i j : Fin 7, i ≠ j →
      bit (lowRow i) (sevenInputs.getD j.val zero) =
      bit (highRow i) (sevenInputs.getD j.val zero)) := by decide +kernel

theorem physicalSigned (C : Circuit) (legal : PEqualNP.MetaComplexity.FanInTwo C)
    (computes : ∀ x : Fin 7 → Bool, C.eval (List.ofFn x)=target x) :
    ∃ k, k ≤ C.gates.countP (fun g => !isNot g) ∧ Live true graph k sevenInputs.toFinset := by
  have goalEq : (execute C.gates sevenInputs).getD C.output zero = graph := by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    let r : Row := ⟨j,hj⟩
    exact (sevenEval C legal C.output r).trans ((computes (sampleSeven r)).trans (sevenTable r).symm)
  have out := get_rep (u:=true) (execute C.gates sevenInputs) C.output
  rw [goalEq] at out
  unfold Repr at out
  have pg : bit 0 graph = false := by decide +kernel
  rw [nrm_id pg] at out
  obtain ⟨k,S,hk,run,sub⟩ := extract (u:=true) C.gates sevenInputs legal (by simp) graph_proper
    (out.resolve_right (fun h => h graph_proper))
  have ns : sevenInputs.all plainWord = true := by decide +kernel
  rw [nrm_map ns] at sub
  have idx (a : Sig) (ha : a ∈ sevenInputs) : ∃ i : Fin 7, sevenInputs.getD i.val zero = a := by
    rw [←sevenList] at ha
    exact List.mem_ofFn.mp ha
  have eq : S = sevenInputs.toFinset := by
    ext a
    constructor
    · exact fun h => List.mem_toFinset.mpr (sub a h)
    · intro ha
      obtain ⟨i,rfl⟩ := idx a (List.mem_toFinset.mp ha)
      apply raw_required run sevenInputs (sevenInputs.getD i.val zero) sub (lowRow i) (highRow i)
        (allSevenRequired.1 i)
      intro v hv hn
      obtain ⟨j,rfl⟩ := idx v hv
      apply allSevenRequired.2 i j
      rintro rfl
      exact hn rfl
  exact ⟨k,hk,eq ▸ run⟩

theorem replaceShort
    (lower : Impossible true graph 12 sevenInputs.toFinset) (gates : List Gate) (o : Nat)
    (fit : ∀ g ∈ gates, (g.op=GateOp.and ∨ g.op=GateOp.or ∨ g.op=GateOp.not) ∧ g.inputs.length≤2)
    (correct : ∀ x : Fin 7 → Bool, (Circuit.mk gates o).eval (List.ofFn x)=target x) :
    ∃ (gs : List Gate) (out : Nat), (∀ g ∈ gs, (g.op=GateOp.and ∨ g.op=GateOp.or) ∧ g.inputs.length≤2) ∧
       gs.length≤gates.length ∧ ∀ x : Fin 7 → Bool, (Circuit.mk gs out).eval (List.ofFn x)=target x := by
  classical
  by_cases big : 14 ≤ gates.length
  · exact ⟨smallCircuit.gates,smallCircuit.output,witnessMonotone,(by simpa only [witnessSize] using big),witnessCorrect⟩
  by_cases mono : ∀ g ∈ gates, g.op ≠ GateOp.not
  · exact ⟨gates,o,noNotReuse fit mono,Nat.le_refl _,correct⟩
  push Not at mono
  obtain ⟨g,hg,hop⟩ := mono
  have lt : gates.countP (fun q => !isNot q) < gates.length := by
    rcases Nat.lt_or_ge (gates.countP (fun q => !isNot q)) gates.length with h | h
    · exact h
    · have eq := List.countP_eq_length.mp (Nat.le_antisymm List.countP_le_length h) g hg
      simp [isNot,hop] at eq
  have legal : PEqualNP.MetaComplexity.FanInTwo (Circuit.mk gates o) := by
    intro g hg
    simpa only [Set.mem_insert_iff,Set.mem_singleton_iff] using fit g hg
  obtain ⟨k,hk,run⟩ := physicalSigned (Circuit.mk gates o) legal correct
  change k ≤ gates.countP (fun q => !isNot q) at hk
  exact (lower k (by omega) run).elim


def paidSliceChoices (d : Sig) (pool : List Sig) : List Choice → List Choice
  | [] => []
  | c :: hist =>
    if availableB true d pool (choiceVal c) then paidSliceChoices d pool hist
    else c :: paidSliceChoices d (choiceVal c :: pool) hist

def zeroSliceOK (m s : Nat) : Bool :=
  let fixed := m - s
  let moves := fixRows fixed 0
  properB (graphGoal s) && (movedWord moves (subcube fixed 0) == one &&
    checkMap moves (vars m) (graphGoal m) (vars s) (graphGoal s))

theorem zeroSlice_sound {m s l} (ok : zeroSliceOK m s = true)
    (prior : Lower true (vars s) (graphGoal s) l) :
    Slice true (vars m) (graphGoal m) (subcube (m - s) 0) l := by
  simp only [zeroSliceOK, Bool.and_eq_true, beq_iff_eq] at ok
  exact slice_correct ok.2.2 ok.2.1 (proper_of _ ok.1) prior

def mixedPairs (support hints : Nat) : List (Sig × Row × Row) :=
  (selected support).map fun (i, w) =>
    let j := (hints >>> (4 * i)) &&& 15
    let r : Nat := if j < 7 then 1 <<< j else 0
    (w, Fin.ofNat 128 r, Fin.ofNat 128 (r ||| (1 <<< i)))

def mixedColumnOK (m z o q support hints L base : Nat) : Bool :=
  let ms := fixRows z o
  let free := colFree m z o
  let G := movedWord ms (graphGoal m)
  let xs := mixedPairs support hints
  let count := (xs.map Prod.fst).toFinset.card
  properB G && checkMap ms (vars m) (graphGoal m) (vars free) G &&
    (movedWord ms (subcube z o) == one) &&
    (if q = 0 then checkEssential G (vars free) xs && decide (L ≤ count - 1)
     else properB (graphGoal q) &&
       checkLift (fixRows (colFree free q 0) 0) G (vars free) (vars q) (graphGoal q) xs &&
       decide (L ≤ base + count))

theorem mixedColumn_sound {m z o q support hints L base : Nat}
    (prior : Lower true (vars q) (graphGoal q) base)
    (ok : mixedColumnOK m z o q support hints L base = true) :
    Slice true (vars m) (graphGoal m) (subcube z o) L := by
  let ms := fixRows z o
  let free := colFree m z o
  let G := movedWord ms (graphGoal m)
  let xs := mixedPairs support hints
  change (((properB G && checkMap ms (vars m) (graphGoal m) (vars free) G) &&
    (movedWord ms (subcube z o) == one)) && _) = true at ok
  simp only [Bool.and_eq_true, beq_iff_eq] at ok
  apply slice_correct ok.1.1.2 ok.1.2 (proper_of _ ok.1.1.1)
  intro p bank hr ha
  have h := ok.2
  by_cases hq : q = 0
  · simp only [hq, if_true, Bool.and_eq_true, decide_eq_true_eq] at h
    exact h.2.trans (lower_count (proper_of _ ok.1.1.1) xs h.1 p bank hr ha)
  · simp only [hq, if_false, Bool.and_eq_true, decide_eq_true_eq] at h
    exact h.2.trans (lift_ok h.1.2 (proper_of _ ok.1.1.1) (proper_of _ h.1.1) prior p bank hr ha)

theorem mixedBaseZero : Lower true (vars 0) (graphGoal 0) 0 :=
  fun _ _ _ _ => Nat.zero_le _

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


abbrev Bits := BitVec 1024
abbrev Signals := Bits × Bits
abbrev Decor := Sig × Signals

def ofRows {n : Nat} (r : Fin n → Row) (v : Sig) : BitVec n :=
  (BitVec.ofBoolListLE (List.ofFn (fun i => bit (r i) v))).cast List.length_ofFn
theorem ofRows_bit {n : Nat} (r : Fin n → Row) (v : Sig) (i : Fin n) :
    (ofRows r v).getLsbD i.val = bit (r i) v := by
  simp only [ofRows,BitVec.getLsbD_cast,BitVec.getLsbD_ofBoolListLE,List.getD_eq_getElem?_getD,List.getElem?_ofFn]
  simp [i.isLt]
def pairSig (r s : Fin 1024 → Row) (a : Sig) : Signals := (ofRows r a,ofRows s a)
def properPairs (T : Sig) (r s : Fin 1024 → Row) :=
  ∀ i, bit (r i) T = true ∧ bit (s i) T = false
theorem pair_sep {T r s} (h : properPairs T r s) : Sep T 1024 r s (pairSig r s) := by
  exact ⟨h,fun a i => ⟨ofRows_bit _ _ _,ofRows_bit _ _ _⟩⟩
def faithful (r s : Fin 1024 → Row) (x : Decor) := x.2 = pairSig r s x.1
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

def asRow (cols : Nat → Bits) (i : Fin 1024) : Row :=
  (BitVec.ofBoolListLE (List.ofFn (fun j : Fin 7 => (cols j.val).getLsbD i.val))).toFin.cast
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
theorem input_coords : ∀ (j : Fin 7) (r : Row),
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
theorem asRow_bit (cols : Nat → Bits) (i : Fin 1024) (j : Fin 7) :
    bit (asRow cols i) (inputs.getD j.val zero) = (cols j.val).getLsbD i.val := by
  rw [input_coords]
  change (BitVec.ofBoolListLE (List.ofFn (fun h : Fin 7 => (cols h.val).getLsbD i.val))).getLsbD j.val = _
  simp only [BitVec.getLsbD_ofBoolListLE,List.getD_eq_getElem?_getD,List.getElem?_ofFn]
  simp [j.isLt]
def rawDecor (m : Nat) (p q : Nat → Bits) : List Decor :=
  (selected m).map (fun (j,a) => (a,p j,q j))
theorem selected_entry {m j a} (h : (j,a) ∈ selected m) :
    j<7 ∧ a=inputs.getD j zero := by
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
  (x 0 &&& x 2) ||| (x 1 &&& x 3) ||| (x 0 &&& x 4) ||| (x 1 &&& x 4) ||| (x 2 &&& x 4) ||| (x 0 &&& x 5) ||| (x 1 &&& x 5) ||| (x 3 &&& x 5) ||| (x 0 &&& x 6) ||| (x 2 &&& x 6) ||| (x 3 &&& x 6) ||| (x 5 &&& x 6)
theorem bit_vertex (m : Nat) (v : Nat → Bits) (i : Fin 1024) (j : Fin 7) :
    bit (asRow v i) (vertex m j.val) =
    ((if m.testBit j.val then v j.val else 0) : Bits).getLsbD i.val := by
  by_cases hh : m.testBit j.val = true
  · simpa [vertex,hh] using asRow_bit v i j
  · simp [vertex,hh,bit_zero]
theorem bit_liftGoal (m : Nat) (v : Nat → Bits) (i : Fin 1024) :
    bit (asRow v i) (graphGoal m) = (liftGoal m v).getLsbD i.val := by
  have pos (j : Nat) (hj : j<7) : (vertex m j).getLsbD (asRow v i).val = ((if m.testBit j then v j else 0) : Bits).getLsbD i.val := bit_vertex m v i ⟨j,hj⟩
  simp only [bit,graphGoal,liftGoal,BitVec.getLsbD_and,BitVec.getLsbD_or]
  simp only [pos 0 (by decide),pos 1 (by decide),pos 2 (by decide),pos 3 (by decide),pos 4 (by decide),pos 5 (by decide),pos 6 (by decide)]
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
  let n := (v.toNat * 232657547755585) % 2305843009213693921
  (n*(n+971)) % 2305843009213693921
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
    if (rs ||| column d z.2) != BitVec.allOnes 1024 then true else
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
  have be : ((restCov (coverage (!u) ws) (column (!u) a.2) (column (!u) b.2) ka kb ||| column (!u) z.2) != BitVec.allOnes 1024) = false := by
    simpa using sep
  change (if (restCov (coverage (!u) ws) (column (!u) a.2) (column (!u) b.2) ka kb ||| column (!u) z.2) != BitVec.allOnes 1024 then true else if !properB z.1 || ws.any (fun v => v.1==z.1) then true else _) = true at test
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
  by_cases hj : j<7
  · let i : Fin 7 := ⟨j,hj⟩
    have hm : inputs.getD i.val zero ∈ inputs := by
      rw [← input_list]
      exact List.mem_ofFn.mpr ⟨i,rfl⟩
    exact (input_coords i r).symm.trans ((h _ hm).trans (input_coords i s))
  · have le : 128 ≤ 2^j := by
      change 2^7 ≤ 2^j
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


def compactNext (path : Nat) (ws : List Decor) (hist : List Choice) :
    List Decor × List Choice :=
  let a := ws.getD (path &&& 31) defaultDecor
  let b := ws.getD ((path >>> 5) &&& 31) defaultDecor
  let d := (path >>> 10) &&& 3
  (ws ++ [dbin d a b], hist ++ [(d, a.1, b.1)])

def walkCompact : Nat → Nat → List Decor → List Choice → List Decor × List Choice
  | 0, _, ws, hist => (ws, hist)
  | depth + 1, path, ws, hist =>
    let next := compactNext path ws hist
    walkCompact depth (path >>> 12) next.1 next.2

theorem walkCompact_faithful (depth path : Nat) (ws : List Decor) (hist : List Choice)
    {r s} (base : ∀ v ∈ ws, faithful r s v) :
    ∀ v ∈ (walkCompact depth path ws hist).1, faithful r s v := by
  induction depth generalizing path ws hist with
  | zero => exact base
  | succ depth ih =>
    apply ih
    intro v hv
    rcases List.mem_append.mp hv with hb | hz
    · exact base _ hb
    · obtain rfl := List.mem_singleton.mp hz
      exact faithful_bin _ (faithful_get base _) (faithful_get base _)

def rowWires : List Decor → Nat → List Decor
  | [], _ => []
  | v :: bank, mask =>
    if mask.testBit 0 then v :: rowWires bank (mask >>> 1)
    else rowWires bank (mask >>> 1)

theorem rowWires_faithful (bank : List Decor) (mask : Nat) {r s}
    (base : ∀ v ∈ bank, faithful r s v) :
    ∀ v ∈ rowWires bank mask, faithful r s v := by
  induction bank generalizing mask with
  | nil => simp [rowWires]
  | cons v bank ih =>
    have hv := List.forall_mem_cons.mp base
    unfold rowWires
    split
    · exact List.forall_mem_cons.mpr ⟨hv.1, ih _ hv.2⟩
    · exact ih _ hv.2

def compactPool (m : Nat) (domain : Sig × Nat) (hist : List Choice) : Option BoundPool :=
  materialize true (vars m) (paidSliceChoices domain.1 (vars m) hist) domain.1 domain.2

theorem compactPool_sound {m : Nat} {domain : Sig × Nat} {hist : List Choice} {pool : BoundPool}
    (slice : Slice true (vars m) (graphGoal m) domain.1 domain.2)
    (ok : compactPool m domain hist = some pool) :
    ValidPool true (vars m) (graphGoal m) pool :=
  materialize_sound slice ok

abbrev CompactGrid := Nat × Nat × (Nat → Bits) × (Nat → Bits)
def CompactGrid.mask (g : CompactGrid) := g.1
def CompactGrid.top (g : CompactGrid) := g.2.1
def CompactGrid.pos (g : CompactGrid) := g.2.2.1
def CompactGrid.neg (g : CompactGrid) := g.2.2.2

abbrev CompactTable := (Nat → Nat) × (Nat → Nat → Nat) × (Nat → Nat → Nat) ×
  (Nat → Nat → List Nat) × (Nat → Nat → List Nat)
def CompactTable.count (t : CompactTable) := t.1
def CompactTable.path (t : CompactTable) := t.2.1
def CompactTable.live (t : CompactTable) := t.2.2.1
def CompactTable.picks (t : CompactTable) := t.2.2.2.1
def CompactTable.bucket (t : CompactTable) := t.2.2.2.2

def chartAt (g : CompactGrid) (t : CompactTable) (k i : Nat) :=
  let bank := walkCompact (g.top-k) (t.path k i) (rawDecor g.mask g.pos g.neg) []
  (rowWires bank.1 (t.live k i), bank.2)

def wordsAt (g : CompactGrid) (t : CompactTable) (k i : Nat) :=
  (chartAt g t k i).1.map Prod.fst

abbrev Domains := Array (Sig × Nat)
abbrev Perms := Array (List Nat)

def selectedHistory : List Choice → Nat → List Choice
  | [], _ => []
  | a :: rest, mask =>
    if mask.testBit 0 then a :: selectedHistory rest (mask >>> 1)
    else selectedHistory rest (mask >>> 1)

def poolList (m : Nat) (dom : Domains) (h : List Choice) (picks : List Nat) :=
  picks.filterMap (fun j => dom[j % dom.size]?.bind (fun d => compactPool m d (selectedHistory h (j / dom.size))))

theorem poolList_valid {m dom h picks} (valid : ∀ d ∈ dom, Slice true (vars m) (graphGoal m) d.1 d.2) :
    ∀ pool ∈ poolList m dom h picks, ValidPool true (vars m) (graphGoal m) pool := by
  intro pool hp
  obtain ⟨j,_,hj⟩ := List.mem_filterMap.mp hp
  cases e : dom[j % dom.size]? with
  | none => simp [e] at hj
  | some d =>
    simp only [e,Option.bind_some] at hj
    exact compactPool_sound (valid d (Array.mem_of_getElem? e)) hj

def applySwaps : List Nat → List Sig → List Sig
  | [], xs => xs
  | p::ps,xs => xs.map (movedWord ((p::ps).map swapRows))

theorem applySwaps_valid {T k xs} {p : List Nat}
    (ok : autoOK T (p.map swapRows).reverse = true)
    (ih : Impossible true T k (List.toFinset xs)) :
    Impossible true T k (applySwaps p xs).toFinset := by
  cases p with
  | nil => exact ih
  | cons a p =>
    have := rotate_excluded ih (((a::p).map swapRows).reverse) ok
    simpa only [List.reverse_reverse,applySwaps] using this

def linkedCandidates (g : CompactGrid) (t : CompactTable) (perms : Perms) (k tag : Nat) :=
  (t.bucket k tag).filterMap (fun code =>
    let name := code / perms.size
    if name < t.count k then
      perms[code % perms.size]?.map (fun swaps => applySwaps swaps (wordsAt g t k name))
    else none)

theorem linkedCandidates_valid {g t perms k}
    (autos : ∀ p ∈ perms, autoOK (graphGoal g.mask) (p.map swapRows).reverse = true)
    (prev : ∀ i < t.count k, Impossible true (graphGoal g.mask) k (wordsAt g t k i).toFinset) :
    ∀ tag xs, xs ∈ linkedCandidates g t perms k tag → Impossible true (graphGoal g.mask) k xs.toFinset := by
  intro tag xs hx
  obtain ⟨code,_,he⟩ := List.mem_filterMap.mp hx
  dsimp only at he
  split at he
  next small =>
    cases eq : perms[code % perms.size]? with
    | none => simp [eq] at he
    | some p =>
      simp only [eq,Option.map_some,Option.some.injEq] at he
      subst xs
      exact applySwaps_valid (autos p (Array.mem_of_getElem? eq)) (prev _ small)
  next => contradiction

theorem cachedLiveSize {u target k S} (h : Live u target k S) : S.card ≤ k+1 := by
  induction h using Live.ind with
  | stop hp => simp
  | @binary k U a b d hd ha hb hab hf _ ih =>
    have hu : bin d a b ∉ U := fun hm => hf (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hm))
    rw [Finset.card_insert_of_notMem hu] at ih
    have h1 := Finset.card_insert_le (a := a) (s := insert b U)
    have h2 := Finset.card_insert_le (a := b) (s := U)
    omega


abbrev NodePool := BoundPool × List Sig × List Sig × Nat

def cacheOnePool (u : Bool) (front : List Sig) (p : BoundPool) : NodePool :=
  (p, front.filter (fun a => !(availableB u p.domain p.wires a)),
    p.wires.map (masked p.domain), front.countP (isMaskedConstant p.domain))

def maskedAvailable (u : Bool) (d : Sig) (pool : List Sig) (a : Sig) : Bool :=
  let m := masked d a
  m == zero || m == d || pool.any (fun v => v==m) ||
    (u && (let c := masked d (neg a); pool.any (fun v => v==c)))

def cachedPoolCut (u : Bool) (a : NodePool) (k : Nat) (rest : List Sig) (op : Choice) : Bool :=
  let (c,missing,bank,maxCon) := a
  if c.bound + maxCon + 1 ≤ k + c.paid then false else
  let z := choiceVal op
  let con := c.bound + (z::rest).countP (isMaskedConstant c.domain)
  if con ≤ k+c.paid then false else
  let extra := !(maskedAvailable u c.domain bank z)
  (decide (k+c.paid+extra.toNat < con) &&
   missing.all (fun w => !(rest.contains w))) &&
    (!extra || (allowedB u op.1 && (!missing.contains op.2.1 && !missing.contains op.2.2)))

theorem cachedCut_ok {u p k rest op front}
    (sub : ∀ w ∈ rest, w ∈ front) (ha : op.2.1 ∈ front) (hb : op.2.2 ∈ front)
    (ok : cachedPoolCut u (cacheOnePool u front p) k rest op = true) :
    scalarPoolCut u p k rest op = true := by
  let miss := front.filter (fun a => !(availableB u p.domain p.wires a))
  let extra := !(availableB u p.domain p.wires (choiceVal op))
  have know (w) (hm : w ∈ front) (hn : w ∉ miss) : availableB u p.domain p.wires w = true := by
    by_contra h
    apply hn
    apply List.mem_filter.mpr
    exact ⟨hm, by simpa using h⟩
  dsimp only [cachedPoolCut, cacheOnePool] at ok
  split at ok
  · contradiction
  split at ok
  · contradiction
  change ((_ && miss.all (fun w => !(rest.contains w))) &&
    (!extra || (allowedB u op.1 && (!miss.contains op.2.1 && !miss.contains op.2.2)))) = true at ok
  simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true', List.all_eq_true] at ok
  change ((_ && rest.all (availableB u p.domain p.wires)) && (!extra || choiceOK u p.domain p.wires op)) = true
  simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true', List.all_eq_true]
  refine ⟨⟨ok.1.1, ?_⟩, ?_⟩
  · intro w hw
    apply know w (sub w hw)
    intro no
    have contra := ok.1.2 w no
    simpa [hw] using contra
  · rcases ok.2 with h | ⟨allowed, ah, bh⟩
    · exact Or.inl h
    · right
      simp only [choiceOK, Bool.and_eq_true]
      exact ⟨allowed, know _ ha (by simpa using ah), know _ hb (by simpa using bh)⟩

def cachedClose (u : Bool) (pools : List NodePool) (links : Nat → List (List Sig)) (k : Nat)
    (rest : List Sig) (op : Choice) : Bool :=
  pools.any (fun p => cachedPoolCut u p k rest op) ||
    (let ws := choiceVal op::rest; (links (keySet ws)).any (sameWords ws))

theorem cachedClose_sound {u raw T} {pools : List BoundPool} {links k rest op front}
    (pValid : ∀ p ∈ pools, ValidPool u raw T p)
    (lValid : ∀ tag xs, xs ∈ links tag → Impossible u T k (List.toFinset xs))
    (nd : (choiceVal op::rest).Nodup)
    (sub : ∀ w ∈ rest, w ∈ front) (ha : op.2.1 ∈ front) (hb : op.2.2 ∈ front)
    (ok : cachedClose u (pools.map (cacheOnePool u front)) links k rest op = true) :
    Impossible u T k (choiceVal op::rest).toFinset := by
  simp only [cachedClose,Bool.or_eq_true,List.any_eq_true] at ok
  rcases ok with ⟨c,hc,cut⟩ | ⟨w,hw,eq⟩
  · obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hc
    exact scalarPoolCut_sound (pValid p hp) nd (cachedCut_ok sub ha hb cut)
  · rw [sameWords_sound eq]
    exact lValid _ _ hw

abbrev cached_NodeContext := Nat × Nat × List Decor × CovPair × List NodePool × (Nat → List (List Sig))
def cached_evalMove (c : cached_NodeContext) (op : Nat) (a b z : Decor) (ka kb : Bool) :=
  let (cap,n,ws,cov,pools,links) := c
  let len := 1+(n - (if ka then 0 else 1) - (if kb then 0 else 1))
  if len>cap then true else
    let d := !cov.2
    let rs := restCov cov.1 (column d a.2) (column d b.2) ka kb
    if (rs ||| column d z.2) != BitVec.allOnes 1024 then true else
    if !properB z.1 || ws.any (fun v => v.1==z.1) then true else
      let rest := (delTwo ws a b ka kb).map Prod.fst
      cachedClose cov.2 pools links (cap-1) rest (movedChoice op a b)

def cached_moveFront (ws : List Decor) (op : Nat) (a b : Decor) (ka kb : Bool) :=
  (dbin op a b).1 :: (delTwo ws a b ka kb).map Prod.fst
theorem cached_evalMove_sound {u raw T r s ws} {pools : List BoundPool} {links cap a b op ka kb}
    (pairs : properPairs T r s) (faith : ∀ w ∈ ws, faithful r s w)
    (nd : (ws.map Prod.fst).Nodup) (ha : a ∈ ws) (hb : b ∈ ws)
    (ne : a≠b) (hcap : 0<cap)
    (pv : ∀ p ∈ pools, ValidPool u raw T p)
    (lv : ∀ tag xs, xs ∈ links tag → Impossible u T (cap-1) (List.toFinset xs))
    (pro : proper (dbin op a b).1) (fresh : (dbin op a b).1 ∉ ws.map Prod.fst)
    (test : cached_evalMove (cap,ws.length,ws,preCov u ws,pools.map (cacheOnePool u (ws.map Prod.fst)),links) op a b (dbin op a b) ka kb = true) :
    Impossible u T (cap-1) (cached_moveFront ws op a b ka kb).toFinset := by
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
  have hsz := cachedLiveSize h
  change child.toFinset.card ≤ k+1 at hsz
  rw [List.toFinset_card_of_nodup ndc] at hsz
  have len : child.length ≤ cap := by omega
  unfold cached_evalMove at test
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
  have be : ((restCov (coverage (!u) ws) (column (!u) a.2) (column (!u) b.2) ka kb ||| column (!u) z.2) != BitVec.allOnes 1024) = false := by
    simpa using sep
  change (if (restCov (coverage (!u) ws) (column (!u) a.2) (column (!u) b.2) ka kb ||| column (!u) z.2) != BitVec.allOnes 1024 then true else if !properB z.1 || ws.any (fun v => v.1==z.1) then true else _) = true at test
  rw [be,pp,fr] at test
  exact cachedClose_sound (op:=movedChoice op a b) (rest:=rest.map Prod.fst) pv lv ndc (sub.map _).subset (List.mem_map_of_mem ha) (List.mem_map_of_mem hb) test k hk h

def cached_testPair (ctx : cached_NodeContext) (a b : Decor) (op : Nat) :=
  let z := dbin op a b
  let attempt := cached_evalMove ctx op a b z
  attempt false false && attempt true false && attempt false true && attempt true true
def cached_opsOf (u : Bool) : List Nat := if u then [0,1,2,3] else [0,1]
theorem cached_opsOf_mem {u d} (h : allowed u d) : d ∈ cached_opsOf u := by
  rcases allowed_four h with rfl | rfl | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · cases u <;> simp [cached_opsOf]
  · cases u <;> simp [cached_opsOf]
  · simp [cached_opsOf]
  · simp [cached_opsOf]
def cached_testRow (ctx : cached_NodeContext) (a : Decor) (bs : List Decor) :=
    bs.all (fun b => (cached_opsOf ctx.2.2.2.1.2).all (cached_testPair ctx a b))
def cached_testAll (ctx : cached_NodeContext) : List Decor → Bool
  | [] => true
  | a::bs => cached_testRow ctx a bs && cached_testAll ctx bs

theorem cached_all_binary {ctx ws} (h : cached_testAll ctx ws=true) {a b : Decor} (ha : a∈ws) (hb : b∈ws)
    (ne : a≠b) : (∀ d, allowed ctx.2.2.2.1.2 d → cached_testPair ctx a b d=true) ∨
      (∀ d, allowed ctx.2.2.2.1.2 d → cached_testPair ctx b a d=true) := by
  induction ws with
  | nil => simp at ha
  | cons w ws ih =>
    simp only [cached_testAll,Bool.and_eq_true,cached_testRow,List.all_eq_true] at h
    rcases List.mem_cons.mp ha with rfl | haTail
    · have bm := (List.mem_cons.mp hb).resolve_left (Ne.symm ne)
      exact Or.inl fun d hd => h.1 b bm d (cached_opsOf_mem hd)
    · rcases List.mem_cons.mp hb with rfl | hbTail
      · exact Or.inr fun d hd => h.1 a haTail d (cached_opsOf_mem hd)
      · exact ih h.2 haTail hbTail

theorem cached_testPair_at {ctx a b d} (h : cached_testPair ctx a b d = true) (ka kb : Bool) :
    cached_evalMove ctx d a b (dbin d a b) ka kb = true := by
  simp only [cached_testPair,Bool.and_eq_true] at h
  cases ka <;> cases kb <;> first | exact h.1.1.1 | exact h.1.2 | exact h.1.1.2 | exact h.2

theorem cached_keep_mem {v : List Sig} {w : Sig} (a : Sig) (k : Bool) :
    w ∈ kept k a v ↔ (w=a ∧ k=true) ∨ w∈v := by cases k <;> simp [kept]
theorem cached_mem_delone {v : List Decor} (nd : v.Nodup) (a w : Decor) (k : Bool) :
    w ∈ delOne v a k ↔ w∈v ∧ (w≠a ∨ k=true) := by
  cases k <;> simp [delOne,nd.mem_erase_iff,and_comm]

theorem cached_unique_value {ws : List Decor} (nd : (ws.map Prod.fst).Nodup) {a b : Decor}
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

theorem cached_kept_value {ws : List Decor} (nd : (ws.map Prod.fst).Nodup) {a b : Decor}
    (ha : a ∈ ws) (hb : b ∈ ws) (ka kb : Bool) (v : Sig) :
    v ∈ (delTwo ws a b ka kb).map Prod.fst ↔
    v ∈ ws.map Prod.fst ∧ (v≠a.1 ∨ ka=true) ∧ (v≠b.1 ∨ kb=true) := by
  have wn := nd.of_map
  have dn := wn.sublist (delOne_sub ws a ka)
  simp only [delTwo,List.mem_map,cached_mem_delone wn,cached_mem_delone dn]
  constructor
  · rintro ⟨w,hw,rfl⟩
    exact ⟨⟨_,hw.1.1,rfl⟩,hw.1.2.imp (fun ne eq => ne (cached_unique_value nd hw.1.1 ha eq)) id,
          hw.2.imp (fun ne eq => ne (cached_unique_value nd hw.1.1 hb eq)) id⟩
  · rintro ⟨⟨w,hm,rfl⟩,h1,h2⟩
    exact ⟨w,⟨⟨hm,h1.imp (fun ne eq => ne (congrArg Prod.fst eq)) id⟩,
        h2.imp (fun ne eq => ne (congrArg Prod.fst eq)) id⟩,rfl⟩

theorem cached_binary_front {ws : List Decor} (nd : (ws.map Prod.fst).Nodup) {a b : Decor}
    (ha : a∈ws) (hb : b∈ws) (ne : a.1≠b.1) (d : Nat) (ka kb : Bool) :
    (cached_moveFront ws d a b ka kb).toFinset =
      (childTwo (ws.map Prod.fst) a.1 b.1 d ka kb).toFinset := by
  ext v
  have av := List.mem_map_of_mem (f:=Prod.fst) ha
  have bv' := List.mem_map_of_mem (f:=Prod.fst) hb
  simp only [cached_moveFront,childTwo,List.toFinset_cons,Finset.mem_insert,List.mem_toFinset,
    cached_kept_value nd ha hb,cached_keep_mem,(nd.erase _).mem_erase_iff,nd.mem_erase_iff,dbin]
  by_cases va : v=a.1 <;> by_cases vb : v=b.1 <;> cases ka <;> cases kb <;> simp_all

theorem cached_childTwo_swap {u} (v : List Sig) (nd : v.Nodup) (a b : Sig) (d : Nat) (hd : allowed u d) (ka kb : Bool) :
    (childTwo v a b d ka kb).toFinset = (childTwo v b a (flipOp d) kb ka).toFinset := by
  ext x
  simp only [childTwo,List.toFinset_cons,Finset.mem_insert,List.mem_toFinset,
    cached_keep_mem,(nd.erase _).mem_erase_iff,nd.mem_erase_iff,bin_flip hd a b]
  tauto

theorem cached_node_sound {u raw T r s ws} {pools : List BoundPool} {links cap}
    (pairs : properPairs T r s) (faith : ∀ w ∈ ws, faithful r s w)
    (nd : (ws.map Prod.fst).Nodup) (out : T ∉ ws.map Prod.fst)
    (pv : ∀ p ∈ pools, ValidPool u raw T p)
    (lv : ∀ tag xs, xs ∈ links tag → Impossible u T (cap-1) (List.toFinset xs))
    (checks : cached_testAll (cap,ws.length,ws,preCov u ws,pools.map (cacheOnePool u (ws.map Prod.fst)),links) ws = true) :
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
      (test : cached_testPair (cap,ws.length,ws,preCov u ws,pools.map (cacheOnePool u (ws.map Prod.fst)),links) a b d = true) :
      Impossible u T (cap-1) (childTwo (ws.map Prod.fst) a.1 b.1 d ka kb).toFinset := by
    rw [←cached_binary_front nd aa bb ne']
    exact cached_evalMove_sound pairs faith nd aa bb (fun e => ne' (congrArg Prod.fst e)) hc' pv lv
      pr fr (cached_testPair_at test ka kb)
  rcases cached_all_binary checks haW hbW ab with hh | hh
  · exact one a b d haW hbW ne ka kb pro fresh (hh d hd)
  · rw [cached_childTwo_swap _ nd _ _ d hd]
    exact one b a (flipOp d) hbW haW (Ne.symm ne) kb ka (bin_flip hd a.1 b.1 ▸ pro)
      (bin_flip hd a.1 b.1 ▸ fresh) (hh _ (flip_flip hd).1)



def compactNode (g : CompactGrid) (t : CompactTable) (dom : Domains) (perms : Perms) (k i : Nat) : Bool :=
  let state := chartAt g t k i
  let ws := state.1
  let words := ws.map Prod.fst
  let pools := poolList g.mask dom state.2 (t.picks k i)
  let links := linkedCandidates g t perms (k-1)
  decide words.Nodup && (!(words.contains (graphGoal g.mask)) &&
    (if k=0 then true else cached_testAll (k,ws.length,ws,preCov true ws,pools.map (cacheOnePool true words),links) ws))

theorem compactNode_sound {g t dom perms k i}
    (pairs : properPairs (graphGoal g.mask) (asRow g.pos) (asRow g.neg))
    (valid : ∀ d ∈ dom, Slice true (vars g.mask) (graphGoal g.mask) d.1 d.2)
    (autos : ∀ p ∈ perms, autoOK (graphGoal g.mask) (p.map swapRows).reverse = true)
    (prev : 0 < k → ∀ j < t.count (k-1),
      Impossible true (graphGoal g.mask) (k-1) (wordsAt g t (k-1) j).toFinset)
    (check : compactNode g t dom perms k i = true) :
    Impossible true (graphGoal g.mask) k (wordsAt g t k i).toFinset := by
  simp only [compactNode,Bool.and_eq_true,decide_eq_true_eq] at check
  have out : graphGoal g.mask ∉ wordsAt g t k i := by simpa [wordsAt] using check.2.1
  by_cases hz : k=0
  · subst k
    intro n hn run
    obtain rfl : n = 0 := by omega
    exact out (List.mem_toFinset.mp (run.1.symm ▸ Finset.mem_singleton_self _))
  · have f : ∀ v ∈ (chartAt g t k i).1, faithful (asRow g.pos) (asRow g.neg) v :=
      rowWires_faithful _ (t.live k i) (walkCompact_faithful (g.top-k) (t.path k i)
        (rawDecor g.mask g.pos g.neg) [] (raw_faithful g.mask g.pos g.neg))
    apply cached_node_sound pairs f check.1 out (poolList_valid valid) (linkedCandidates_valid autos (prev (by omega)))
    simpa only [hz,ite_false] using check.2.2


def chartBlock (test : Nat → Bool) (start : Nat) : Nat → Bool
  | 0 => true
  | n+1 => test (start+n) && chartBlock test start n

theorem chartBlock_at {test start n} (ok : chartBlock test start n = true) (i)
    (a : start ≤ i) (b : i < start+n) : test i = true := by
  induction n with
  | zero => omega
  | succ n ih =>
    simp only [chartBlock,Bool.and_eq_true] at ok
    by_cases h : i=start+n
    · simpa only [h] using ok.1
    · exact ih ok.2 (by omega)

theorem chartBlock_join {test start a b}
    (left : chartBlock test start a = true) (right : chartBlock test (start+a) b = true) :
    chartBlock test start (a+b) = true := by
  induction b with
  | zero => simpa using left
  | succ b ih =>
    simp only [chartBlock,Bool.and_eq_true] at right
    simp only [Nat.add_succ,chartBlock,Bool.and_eq_true]
    constructor
    · change test (start + (a+b)) = true
      rw [← Nat.add_assoc]
      exact right.1
    · exact ih right.2

theorem compactAll {g t dom perms}
    (pairs : properPairs (graphGoal g.mask) (asRow g.pos) (asRow g.neg))
    (valid : ∀ d ∈ dom, Slice true (vars g.mask) (graphGoal g.mask) d.1 d.2)
    (autos : ∀ p ∈ perms, autoOK (graphGoal g.mask) (p.map swapRows).reverse = true)
    (blocks : ∀ k ≤ g.top, chartBlock (compactNode g t dom perms k) 0 (t.count k) = true) :
    ∀ k ≤ g.top, ∀ i < t.count k, Impossible true (graphGoal g.mask) k (wordsAt g t k i).toFinset := by
  intro k
  induction k with
  | zero =>
    intro h i hi
    exact compactNode_sound pairs valid autos (by omega) (chartBlock_at (blocks 0 h) i (by omega) (by simpa using hi))
  | succ k ih =>
    intro h i hi
    exact compactNode_sound pairs valid autos (fun _ => ih (by omega)) (chartBlock_at (blocks _ h) i (by omega) (by simpa using hi))

theorem compactPairs {g : CompactGrid}
    (yes : liftGoal g.mask g.pos = BitVec.allOnes 1024) (no : liftGoal g.mask g.neg = 0) :
    properPairs (graphGoal g.mask) (asRow g.pos) (asRow g.neg) := by
  intro i
  constructor
  · rw [bit_liftGoal,yes,BitVec.getLsbD_allOnes]
    exact decide_eq_true i.isLt
  · rw [bit_liftGoal,no]
    simp

abbrev SliceSpec := Nat × Nat × Nat × Nat × Nat × Nat × Nat

def specDomain (s : SliceSpec) : Sig × Nat :=
  (subcube s.1 s.2.1, s.2.2.2.2.2.1)

def certifiesSlice (m : Nat) (earlier : List (Nat × Nat)) (s : SliceSpec) : Bool :=
  let (z,o,q,support,hints,L,base) := s
  ((q == 0 && base == 0) || earlier.contains (q,base)) &&
    ((z == m-q && o == 0 && L == base && zeroSliceOK m q) ||
      mixedColumnOK m z o q support hints L base)

theorem certifiesSlice_sound {m earlier s}
    (prior : ∀ e ∈ earlier, Lower true (vars e.1) (graphGoal e.1) e.2)
    (ok : certifiesSlice m earlier s = true) :
    Slice true (vars m) (graphGoal m) (specDomain s).1 (specDomain s).2 := by
  obtain ⟨z,o,q,support,hints,L,base⟩ := s
  simp only [certifiesSlice,Bool.and_eq_true,Bool.or_eq_true,beq_iff_eq,
    List.contains_eq_mem,decide_eq_true_eq] at ok
  have lower : Lower true (vars q) (graphGoal q) base := by
    rcases ok.1 with ⟨rfl,rfl⟩ | he
    · exact mixedBaseZero
    · exact prior (q,base) he
  rcases ok.2 with ⟨⟨⟨rfl,rfl⟩,rfl⟩,h⟩ | h
  · exact zeroSlice_sound h lower
  · exact mixedColumn_sound lower h

theorem compactDomains_valid {m earlier specs ds}
    (prior : ∀ e ∈ earlier, Lower true (vars e.1) (graphGoal e.1) e.2)
    (ok : List.all specs (certifiesSlice m earlier) = true)
    (matchDs : (specs.map specDomain).toArray = ds) :
    ∀ d ∈ ds, Slice true (vars m) (graphGoal m) d.1 d.2 := by
  subst ds
  intro d hd
  obtain ⟨s,hs,rfl⟩ := List.mem_map.mp (List.mem_toArray.mp hd)
  exact certifiesSlice_sound prior (List.all_eq_true.mp ok _ hs)

theorem compactAutos_valid {T : Sig} {ps : Perms}
    (ok : ps.toList.all (fun p => autoOK T (p.map swapRows).reverse) = true) :
    ∀ p ∈ ps, autoOK T (p.map swapRows).reverse = true := by
  intro p hp
  exact List.all_eq_true.mp ok _ (Array.mem_toList_iff.mpr hp)

theorem compactRoot {g t dom perms}
    (pairs : properPairs (graphGoal g.mask) (asRow g.pos) (asRow g.neg))
    (valid : ∀ d ∈ dom, Slice true (vars g.mask) (graphGoal g.mask) d.1 d.2)
    (autos : ∀ p ∈ perms, autoOK (graphGoal g.mask) (p.map swapRows).reverse = true)
    (blocks : ∀ k ≤ g.top, chartBlock (compactNode g t dom perms k) 0 (t.count k) = true)
    (existsRoot : 0 < t.count g.top)
    (root : wordsAt g t g.top 0 = vars g.mask) :
    Impossible true (graphGoal g.mask) g.top (vars g.mask).toFinset := by
  rw [←root]
  exact compactAll pairs valid autos blocks _ (Nat.le_refl _) 0 existsRoot

theorem augmentedLower {roots : List Sig} {T a b : Sig} {d k : Nat}
    (hT : proper T) (plainT : plainWord T = true)
    (plainRoots : (bin d a b :: roots).all plainWord = true)
    (nd : roots.Nodup) (ess : ∀ w ∈ roots, Essential T roots w)
    (base : Impossible true T k roots.toFinset)
    (ha : a ∈ roots) (hb : b ∈ roots) (ne : a ≠ b)
    (pa : proper a) (pb : proper b) (allowedOp : allowed true d)
    (fresh : bin d a b ∉ roots)
    (first : ∀ ka kb, Impossible true T k (childTwo roots a b d ka kb).toFinset) :
    Lower true (bin d a b :: roots) T (k+1) := by
  classical
  intro n bank walk found
  by_contra! small
  obtain ⟨j,S,hj,run,sub⟩ := reach_live hT plainT plainRoots walk found
  let z := bin d a b
  have exactRoots {R : Finset Sig} {l : Nat} (h : Live true T l R)
      (s : ∀ w ∈ R, w ∈ roots) : R = roots.toFinset := by
    ext w
    rw [List.mem_toFinset]
    constructor
    · exact s w
    · intro hw
      obtain ⟨r,t,dif,iso⟩ := ess w hw
      exact raw_required h roots w s r t dif iso
  by_cases hz : z ∈ S
  · let U := S.erase z
    have fin : insert z U = S := Finset.insert_erase hz
    have uraw : ∀ w ∈ U, w ∈ roots := by
      intro w hw
      obtain ⟨hn,hs⟩ := Finset.mem_erase.mp hw
      exact (List.mem_cons.mp (sub w hs)).resolve_left hn
    have old : ∀ w ∈ insert a (insert b U), w ∈ roots := by
      intro w hw
      rcases Finset.mem_insert.mp hw with rfl | h
      · exact ha
      rcases Finset.mem_insert.mp h with rfl | h
      · exact hb
      · exact uraw w h
    have hnew : z ∉ insert a (insert b U) := fun h => fresh (old _ h)
    have r' := Live.binary allowedOp pa pb ne hnew (fin.symm ▸ run)
    have whole := exactRoots r' old
    let ka := decide (a ∈ U)
    let kb := decide (b ∈ U)
    have front : (childTwo roots a b d ka kb).toFinset = S := by
      rw [←fin]
      simp only [childTwo,List.toFinset_cons,kept_fin,erase_fin (nd.erase _) b,erase_fin nd a]
      apply congrArg (insert z)
      rw [←whole]
      ext w
      by_cases aw : w = a <;> by_cases bw : w = b <;>
        by_cases au : a ∈ U <;> by_cases bu : b ∈ U <;> simp [ka,kb,aw,bw,au,bu,ne,Ne.symm ne]
    exact first ka kb j (by omega) (front.symm ▸ run)
  · have old : ∀ w ∈ S, w ∈ roots := by
      intro w hw
      rcases List.mem_cons.mp (sub w hw) with h | h
      · apply False.elim (hz ?_)
        change bin d a b ∈ S
        rw [←h]
        exact hw
      · exact h
    exact base j (by omega) (exactRoots run old ▸ run)

def augmentedZeroOK (root minor t : Nat) : Bool :=
  let transform := fixRows (root-minor) 0
  let h := typeWord t
  checkMap transform (h :: vars root) (graphGoal root) (h :: vars minor) (graphGoal minor) &&
    (movedWord transform (subcube (root-minor) 0) == one) && properB (graphGoal minor)

theorem augmentedZero_sound {root minor t L}
    (ok : augmentedZeroOK root minor t = true)
    (prior : Lower true (typeWord t :: vars minor) (graphGoal minor) L) :
    Slice true (typeWord t :: vars root) (graphGoal root) (subcube (root-minor) 0) L := by
  simp only [augmentedZeroOK,Bool.and_eq_true,beq_iff_eq] at ok
  exact slice_correct ok.1.1 ok.1.2 (by simpa [properB,proper] using ok.2) prior

def augmentedPool (root t : Nat) (domain : Sig × Nat) (hist : List Choice) : Option BoundPool :=
  let raw := typeWord t :: vars root
  materialize true raw (paidSliceChoices domain.1 raw hist) domain.1 domain.2

theorem augmentedPool_sound {root t : Nat} {domain : Sig × Nat} {hist : List Choice} {pool : BoundPool}
    (slice : Slice true (typeWord t :: vars root) (graphGoal root) domain.1 domain.2)
    (ok : augmentedPool root t domain hist = some pool) :
    ValidPool true (vars root) (graphGoal root) pool :=
  materialize_sound (raw:=typeWord t :: vars root) slice ok

theorem augmentedPairLower {m hints top : Nat} {P Q : Nat → Bits} {pools : List BoundPool}
    {links : Nat → List (List Sig)} {a b : Decor} {op : Nat}
    (pairs : properPairs (graphGoal m) (asRow P) (asRow Q))
    (valid : ∀ p ∈ pools, ValidPool true (vars m) (graphGoal m) p)
    (link : ∀ tag xs, xs ∈ links tag → Impossible true (graphGoal m) (top-1) xs.toFinset)
    (raw : (rawDecor m P Q).map Prod.fst = vars m)
    (essen : essOK m hints = true) (nd : (vars m).Nodup)
    (prior : Impossible true (graphGoal m) (top-1) (vars m).toFinset)
    (ha : a ∈ rawDecor m P Q) (hb : b ∈ rawDecor m P Q) (diff : a.1 ≠ b.1)
    (pa : proper a.1) (pb : proper b.1) (pt : 0 < top) (allow : allowed true op)
    (pg : proper (bin op a.1 b.1)) (plain : plainWord (bin op a.1 b.1) = true)
    (new : bin op a.1 b.1 ∉ vars m)
    (check : testPair (top,(rawDecor m P Q).length,rawDecor m P Q,preCov true (rawDecor m P Q),pools,links) a b op = true) :
    Lower true (bin op a.1 b.1 :: vars m) (graphGoal m) top := by
  have rt := essen
  simp only [essOK,Bool.and_eq_true,beq_iff_eq] at rt
  have rn : ((rawDecor m P Q).map Prod.fst).Nodup := raw ▸ nd
  have amin : a.1 ∈ vars m := raw ▸ List.mem_map_of_mem (f:=Prod.fst) ha
  have bmin : b.1 ∈ vars m := raw ▸ List.mem_map_of_mem (f:=Prod.fst) hb
  have fresh : bin op a.1 b.1 ∉ (rawDecor m P Q).map Prod.fst := raw ▸ new
  have eq : top-1+1=top := by omega
  rw [←eq] at ⊢
  refine augmentedLower (proper_of _ rt.1.1) (essential_plain rt.1.2).1 ?_ nd ?_ prior
    amin bmin diff pa pb allow new ?_
  · simp only [List.all_cons,plain,(essential_plain rt.1.2).2,Bool.and_self]
  · intro w hw
    apply essential_ok rt.1.2 w
    rw [rt.2]
    exact List.mem_toFinset.mpr hw
  · intro ka kb
    rw [←raw,←binary_front rn ha hb diff]
    exact evalMove_sound pairs (raw_faithful m P Q) rn ha hb (fun e => diff (congrArg Prod.fst e)) pt valid link pg fresh (testPair_at check ka kb)
abbrev RichDomains := Array (Nat × Sig × Nat)

def richRaw (m code : Nat) : List Sig :=
  if code = 0 then vars m else typeWord (code-1) :: vars m

def richPoolList (m : Nat) (dom : RichDomains) (h : List Choice) (picks : List Nat) :=
  picks.filterMap (fun j => dom[j % dom.size]?.bind (fun d =>
    let raw := richRaw m d.1
    let selected := selectedHistory h (j / dom.size)
    materialize true raw (paidSliceChoices d.2.1 raw selected) d.2.1 d.2.2))

def RichValid (m : Nat) (ds : RichDomains) :=
  ∀ d ∈ ds, Slice true (richRaw m d.1) (graphGoal m) d.2.1 d.2.2

theorem richPool_valid {m dom h picks} (valid : RichValid m dom) :
    ∀ pool ∈ richPoolList m dom h picks, ValidPool true (vars m) (graphGoal m) pool := by
  intro pool hp
  obtain ⟨j,_,hj⟩ := List.mem_filterMap.mp hp
  cases e : dom[j % dom.size]? with
  | none => simp [e] at hj
  | some d =>
    simp only [e,Option.bind_some] at hj
    exact materialize_sound (raw:=richRaw m d.1) (valid d (Array.mem_of_getElem? e)) hj

def richSpecDomain (s : Nat × SliceSpec) := (s.1, specDomain s.2)

def richNode (g : CompactGrid) (t : CompactTable) (dom : RichDomains) (perms : Perms) (k i : Nat) : Bool :=
  let state := chartAt g t k i
  let ws := state.1
  let words := ws.map Prod.fst
  let pools := richPoolList g.mask dom state.2 (t.picks k i)
  let links := linkedCandidates g t perms (k-1)
  decide words.Nodup && (!(words.contains (graphGoal g.mask)) &&
    (if k=0 then true else cached_testAll (k,ws.length,ws,preCov true ws,pools.map (cacheOnePool true words),links) ws))

theorem richNode_sound {g t dom perms k i}
    (pairs : properPairs (graphGoal g.mask) (asRow g.pos) (asRow g.neg))
    (valid : RichValid g.mask dom)
    (autos : ∀ p ∈ perms, autoOK (graphGoal g.mask) (p.map swapRows).reverse = true)
    (prev : 0 < k → ∀ j < t.count (k-1),
      Impossible true (graphGoal g.mask) (k-1) (wordsAt g t (k-1) j).toFinset)
    (check : richNode g t dom perms k i = true) :
    Impossible true (graphGoal g.mask) k (wordsAt g t k i).toFinset := by
  simp only [richNode,Bool.and_eq_true,decide_eq_true_eq] at check
  have out : graphGoal g.mask ∉ wordsAt g t k i := by simpa [wordsAt] using check.2.1
  by_cases hz : k=0
  · subst k
    intro n hn run
    obtain rfl : n = 0 := by omega
    exact out (List.mem_toFinset.mp (run.1.symm ▸ Finset.mem_singleton_self _))
  · have f : ∀ v ∈ (chartAt g t k i).1, faithful (asRow g.pos) (asRow g.neg) v :=
      rowWires_faithful _ (t.live k i) (walkCompact_faithful (g.top-k) (t.path k i)
        (rawDecor g.mask g.pos g.neg) [] (raw_faithful g.mask g.pos g.neg))
    apply cached_node_sound pairs f check.1 out (richPool_valid valid) (linkedCandidates_valid autos (prev (by omega)))
    simpa only [hz,ite_false] using check.2.2

theorem richAll {g t dom perms}
    (pairs : properPairs (graphGoal g.mask) (asRow g.pos) (asRow g.neg))
    (valid : RichValid g.mask dom)
    (autos : ∀ p ∈ perms, autoOK (graphGoal g.mask) (p.map swapRows).reverse = true)
    (blocks : ∀ k ≤ g.top, chartBlock (richNode g t dom perms k) 0 (t.count k) = true) :
    ∀ k ≤ g.top, ∀ i < t.count k, Impossible true (graphGoal g.mask) k (wordsAt g t k i).toFinset := by
  intro k
  induction k with
  | zero =>
    intro h i hi
    exact richNode_sound pairs valid autos (by omega) (chartBlock_at (blocks 0 h) i (by omega) (by simpa using hi))
  | succ k ih =>
    intro h i hi
    exact richNode_sound pairs valid autos (fun _ => ih (by omega)) (chartBlock_at (blocks _ h) i (by omega) (by simpa using hi))


theorem richRoot {g t dom perms}
    (pairs : properPairs (graphGoal g.mask) (asRow g.pos) (asRow g.neg))
    (valid : RichValid g.mask dom)
    (autos : ∀ p ∈ perms, autoOK (graphGoal g.mask) (p.map swapRows).reverse = true)
    (blocks : ∀ k ≤ g.top, chartBlock (richNode g t dom perms k) 0 (t.count k) = true)
    (existsRoot : 0 < t.count g.top)
    (root : wordsAt g t g.top 0 = vars g.mask) :
    Impossible true (graphGoal g.mask) g.top (vars g.mask).toFinset := by
  rw [←root]
  exact richAll pairs valid autos blocks _ (Nat.le_refl _) 0 existsRoot


abbrev ExtraGroup := Nat × Nat × List Nat

def extraOK (extras : List ExtraGroup) (m l t : Nat) : Bool :=
  extras.any fun e => (e.1 == m && e.2.1 == l) && e.2.2.contains t

def ExtrasValid (extras : List ExtraGroup) : Prop :=
  ∀ e ∈ extras, ∀ t ∈ e.2.2, Lower true (typeWord t :: vars e.1) (graphGoal e.1) e.2.1

def flexibleCheck (m : Nat) (prior : List (Nat × Nat)) (extras : List ExtraGroup)
    (s : Nat × SliceSpec) : Bool :=
  if s.1 == 0 then certifiesSlice m prior s.2 else
  let t := s.1 - 1
  let q := s.2.2.2.1
  let l := (specDomain s.2).2
  (extraOK extras q l t && augmentedZeroOK m q t) &&
    ((specDomain s.2).1 == subcube (m-q) 0)

theorem flexibleOK {m prior extras ds specs}
    (pr : ∀ e ∈ prior, Lower true (vars e.1) (graphGoal e.1) e.2)
    (extra : ExtrasValid extras)
    (ok : List.all specs (flexibleCheck m prior extras) = true)
    (same : (specs.map richSpecDomain).toArray = ds) : RichValid m ds := by
  subst ds
  intro d hd
  obtain ⟨⟨code,s⟩,hs,rfl⟩ := List.mem_map.mp (List.mem_toArray.mp hd)
  have good := List.all_eq_true.mp ok _ hs
  change Slice true (richRaw m code) (graphGoal m) (specDomain s).1 (specDomain s).2
  by_cases hc : code=0
  · simp only [hc,richRaw,ite_true]
    exact certifiesSlice_sound pr (by simpa [flexibleCheck,hc] using good)
  · simp only [flexibleCheck,hc,beq_iff_eq,Bool.false_eq_true,ite_false,Bool.and_eq_true] at good
    obtain ⟨⟨good,mapOK⟩,dEq⟩ := good
    simp only [extraOK,List.any_eq_true,Bool.and_eq_true,beq_iff_eq,List.contains_eq_mem,decide_eq_true_eq] at good
    obtain ⟨e,he,⟨em,el⟩,et⟩ := good
    have lb := extra e he _ et
    rw [em,el] at lb
    rw [dEq]
    simpa [richRaw,hc] using augmentedZero_sound mapOK lb

def primCheck (g : CompactGrid) (pools : List BoundPool) (links : Nat → List (List Sig)) (t : Nat) : Bool :=
  let allW := rawDecor 127 g.pos g.neg
  let ws := rawDecor g.mask g.pos g.neg
  let a := allW.getD (t/9%9) defaultDecor
  let b := allW.getD (t%9) defaultDecor
  let d := t/81
  (ws.contains a && ws.contains b && (a.1 != b.1) && properB a.1 && properB b.1 && allowedB true d &&
    properB (bin d a.1 b.1) && plainWord (bin d a.1 b.1) && !((vars g.mask).contains (bin d a.1 b.1)) &&
    (typeWord t == bin d a.1 b.1)) &&
    testPair (g.top,ws.length,ws,preCov true ws,pools,links) a b d

theorem primOK {g : CompactGrid} {pools links t hints}
    (pairs : properPairs (graphGoal g.mask) (asRow g.pos) (asRow g.neg))
    (valid : ∀ p ∈ pools, ValidPool true (vars g.mask) (graphGoal g.mask) p)
    (lk : ∀ tag xs, xs ∈ links tag → Impossible true (graphGoal g.mask) (g.top-1) xs.toFinset)
    (raw : (rawDecor g.mask g.pos g.neg).map Prod.fst = vars g.mask)
    (ess : essOK g.mask hints = true) (nodup : (vars g.mask).Nodup)
    (base : Impossible true (graphGoal g.mask) (g.top-1) (vars g.mask).toFinset)
    (tp : 0 < g.top) (ok : primCheck g pools links t = true) :
    Lower true (typeWord t :: vars g.mask) (graphGoal g.mask) g.top := by
  simp only [primCheck,Bool.and_eq_true,List.contains_eq_mem,decide_eq_true_eq,bne_iff_ne,beq_iff_eq,Bool.not_eq_true'] at ok
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨am,bm⟩,diff⟩,pa⟩,pb⟩,allow⟩,pg⟩,pl⟩,new⟩,repr⟩,check⟩ := ok
  rw [repr]
  exact augmentedPairLower pairs valid lk raw ess nodup base am bm diff
    (proper_of _ pa) (proper_of _ pb) tp (allowedB_ok allow) (proper_of _ pg) pl
    (by simpa using new) check

def augCarryOK (m rep code repCode : Nat) (swaps : List Nat) :=
  properB (graphGoal m) && plainWord (graphGoal m) && (typeWord code :: vars m).all plainWord &&
    properB (graphGoal rep) &&
    checkMap (swaps.map swapRows) (typeWord code::vars m) (graphGoal m) (typeWord repCode::vars rep) (graphGoal rep)

theorem augCarry {m rep code repCode swaps l} (ok : augCarryOK m rep code repCode swaps = true)
    (lower : Lower true (typeWord repCode :: vars rep) (graphGoal rep) l) :
    Lower true (typeWord code :: vars m) (graphGoal m) l := by
  simp only [augCarryOK,Bool.and_eq_true] at ok
  exact lower_map ok.2 (proper_of _ ok.1.1.1.1) ok.1.1.1.2 ok.1.1.2 (proper_of _ ok.1.2) lower

def readCompactBits (table : Nat → Nat) (start width : Nat) : Nat :=
  let i := start / 4096
  let j := start % 4096
  let low := table i >>> j
  let result := if j + width ≤ 4096 then low else low ||| (table (i+1) <<< (4096-j))
  result &&& ((1 <<< width)-1)

def compactIDsFromBits (bits width : Nat) : Nat → List Nat
  | 0 => []
  | n+1 => (bits &&& ((1 <<< width)-1)) :: compactIDsFromBits (bits >>> width) width n
def samplesP21 : Nat → Bits
  | 0 => ~~~(0x4046 : Bits)
  | 2 => 0xeef6
  | 4 => ~~~(0x20b0 : Bits)
  | _ => 0

def samplesQ21 : Nat → Bits
  | 0 => ~~~(0xbbde : Bits)
  | 2 => 0x1214
  | 4 => 0x280a
  | _ => 0

def compactPerms21 : Array (List Nat) := ([[], [66], [32], [32, 66], [64, 66], [64]] : List (List Nat)).toArray

def compactDomains21 : Array (Sig × Nat) := ([] : List (Sig × Nat)).toArray

def compactWords21 : Nat → Nat
  | 0 => 0x7
  | _ => 0

def compactCount21 (k : Nat) : Nat := match k with
  | 3 => 1
  | _ => 0

def compactPath21 (k : Nat) (i : Nat) : Nat := match k with
  | 3 => 0
  | _ => 0

def compactLive21 (k : Nat) (i : Nat) : Nat := match k with
  | 3 => readCompactBits compactWords21 (0 + 3*i) 3
  | _ => 0

def compactPoolIDs21 (k : Nat) (i : Nat) : List Nat := match k with
  | 3 => let v := readCompactBits compactWords21 (3 + 2*i) 2
    let n := v >>> 1
    let bits := readCompactBits compactWords21 (3 + 1*(v &&& 1)) (1*n)
    compactIDsFromBits bits 1 n
  | _ => []

def compactBucket21 (k : Nat) (i : Nat) : List Nat := match k with
  | _ => []
def samplesP23 : Nat → Bits
  | 0 => 0x5eff31efd7bc8ee2
  | 1 => ~~~(0x130c29f084bea0fa : Bits)
  | 2 => 0x79fde8dfadcea7d8
  | 4 => ~~~(0x80100c3010c86c0 : Bits)
  | _ => 0

def samplesQ23 : Nat → Bits
  | 0 => 0x21284c0606144c82
  | 1 => ~~~(0x6cb1bea3eeab00fe : Bits)
  | 2 => 0x61602292080b350
  | 4 => 0x8800080c800002c
  | _ => 0

def compactPerms23 : Array (List Nat) := ([[], [32]] : List (List Nat)).toArray

def compactDomains23 : Array (Sig × Nat) := ([(subcube 2 0, 4)] : List (Sig × Nat)).toArray

def compactWords23 : Nat → Nat
  | 0 => 0x4f
  | _ => 0

def compactCount23 (k : Nat) : Nat := match k with
  | 4 => 1
  | _ => 0

def compactPath23 (k : Nat) (i : Nat) : Nat := match k with
  | 4 => 0
  | _ => 0

def compactLive23 (k : Nat) (i : Nat) : Nat := match k with
  | 4 => readCompactBits compactWords23 (0 + 4*i) 4
  | _ => 0

def compactPoolIDs23 (k : Nat) (i : Nat) : List Nat := match k with
  | 4 => let v := readCompactBits compactWords23 (5 + 2*i) 2
    let n := v >>> 1
    let bits := readCompactBits compactWords23 (4 + 1*(v &&& 1)) (1*n)
    compactIDsFromBits bits 1 n
  | _ => []

def compactBucket23 (k : Nat) (i : Nat) : List Nat := match k with
  | _ => []
def samplesP27 : Nat → Bits
  | 0 => 0xbbf8f1bfbb341bd2
  | 1 => ~~~(0x20006184a0341252 : Bits)
  | 3 => 0xf3f7627cf7c167e8
  | 4 => ~~~(0x10300240134161a8 : Bits)
  | _ => 0

def samplesQ27 : Nat → Bits
  | 0 => 0x448b26282954ab82
  | 1 => ~~~(0xddfddef6ebef56de : Bits)
  | 3 => 0xd2988b082cd16c8
  | 4 => 0x1060805640091454
  | _ => 0

def compactPerms27 : Array (List Nat) := ([[], [48, 65]] : List (List Nat)).toArray

def compactDomains27 : Array (Sig × Nat) := ([] : List (Sig × Nat)).toArray

def compactWords27 : Nat → Nat
  | 0 => 0xf
  | _ => 0

def compactCount27 (k : Nat) : Nat := match k with
  | 3 => 1
  | _ => 0

def compactPath27 (k : Nat) (i : Nat) : Nat := match k with
  | 3 => 0
  | _ => 0

def compactLive27 (k : Nat) (i : Nat) : Nat := match k with
  | 3 => readCompactBits compactWords27 (0 + 4*i) 4
  | _ => 0

def compactPoolIDs27 (k : Nat) (i : Nat) : List Nat := match k with
  | 3 => let v := readCompactBits compactWords27 (4 + 2*i) 2
    let n := v >>> 1
    let bits := readCompactBits compactWords27 (4 + 1*(v &&& 1)) (1*n)
    compactIDsFromBits bits 1 n
  | _ => []

def compactBucket27 (k : Nat) (i : Nat) : List Nat := match k with
  | _ => []
def samplesP31 : Nat → Bits
  | 0 => 0x7daff4ff85feae1f7df77fdd780a5af02f2feeeb94dbd5538a285fd2c2
  | 1 => ~~~(0x21400052059b1f800920271e309012ea2fa9040d0691995bcb2c925aea : Bits)
  | 2 => 0x7adfdfde2bb9799fdb7fe72e73b3756a0abbfd776a33b909cb2586eea8
  | 3 => 0x774feb77d6cb501fafebf9569ddda3a0505dff9c2fc4dfa01053bb5d10
  | 4 => ~~~(0x1080400482e8680000434944590b61205a60e8322842d5a19a730fc790 : Bits)
  | _ => 0

def samplesQ31 : Nat → Bits
  | 0 => 0x25213104a0011c50191040d04362183400ca0e00098149286105f0202
  | 1 => ~~~(0x5eb7fdecfaf6faf9cfb7f97be31fdf7fdd7d2f2fefb9dfef726db35afe : Bits)
  | 2 => 0x5212403900286328024429038c8c400910359064801012009a700eca0
  | 3 => 0x8b4358420142af90c028839211edd2c043d2f002400caae122db35810
  | 4 => 0x1080808400e048084200382001001820085006098320000c1008a0104c
  | _ => 0

def compactPerms31 : Array (List Nat) := ([[], [32]] : List (List Nat)).toArray

def compactDomains31 : Array (Sig × Nat) := ([(subcube 8 0, 5), (subcube 0 8, 5), (subcube 1 0, 4), (subcube 4 0, 4), (subcube 2 8, 4)] : List (Sig × Nat)).toArray

def compactWords31 : Nat → Nat
  | 0 => 0xe47fbfc3fff05bca2404bd4153fc369bcbfe3fc5ebff1fe192503dffffc02202201401a9f
  | _ => 0

def compactCount31 (k : Nat) : Nat := match k with
  | 6 => 1
  | 5 => 3
  | 4 => 1
  | _ => 0

def compactPath31 (k : Nat) (i : Nat) : Nat := match k with
  | 6 => 0
  | 5 => readCompactBits compactWords31 (23 + 12*i) 12
  | 4 => let v := readCompactBits compactWords31 (224 + 12*i) 12
    (readCompactBits compactWords31 (212 + 12*(v >>> 12)) 12) ||| ((v &&& 4095) <<< 12)
  | _ => 0

def compactLive31 (k : Nat) (i : Nat) : Nat := match k with
  | 6 => readCompactBits compactWords31 (0 + 5*i) 5
  | 5 => readCompactBits compactWords31 (59 + 6*i) 6
  | 4 => readCompactBits compactWords31 (236 + 7*i) 7
  | _ => 0

def compactPoolIDs31 (k : Nat) (i : Nat) : List Nat := match k with
  | 6 => let v := readCompactBits compactWords31 (17 + 6*i) 6
    let n := v >>> 3
    let bits := readCompactBits compactWords31 (5 + 3*(v &&& 7)) (3*n)
    compactIDsFromBits bits 3 n
  | 5 => let v := readCompactBits compactWords31 (85 + 5*i) 5
    let n := v >>> 3
    let bits := readCompactBits compactWords31 (77 + 2*(v &&& 7)) (2*n)
    compactIDsFromBits bits 2 n
  | 4 => let v := readCompactBits compactWords31 (243 + 2*i) 2
    let n := v >>> 1
    let bits := readCompactBits compactWords31 (243 + 1*(v &&& 1)) (1*n)
    compactIDsFromBits bits 1 n
  | _ => []

def compactBucket31 (k : Nat) (i : Nat) : List Nat := match k with
  | 5 => let d := readCompactBits compactWords31 (100 + 1*(i % 2)) 1
    let off := ((i/2 + d) % 10)
    let v := readCompactBits compactWords31 (102 + 11*off) 11
    if v >>> 3 == (i/104729)%251 then [v &&& 7] else []
  | 4 => let d := readCompactBits compactWords31 (245 + 1*(i % 2)) 1
    let off := ((i/2 + d) % 5)
    let v := readCompactBits compactWords31 (247 + 9*off) 9
    if v >>> 1 == (i/104729)%251 then [v &&& 1] else []
  | _ => []
def samplesP55 : Nat → Bits
  | 0 => 0xbf7fff90eb7bcfff7df17fcf634587ec2fe63b9af0f8a66c386ef42
  | 1 => ~~~(0x11809809c123ec024111734a3224c7ef0441128e92cca76f3107fca : Bits)
  | 2 => 0xf8ffd9ffc2e627fecf7ff0beba2640e337df36e5be4407630775688
  | 4 => ~~~(0x841010222f20c180060c88da34294f8838223e028727e68b66ce70 : Bits)
  | 5 => 0xddbfbf6b35b30bdbf3fccb49b7fa94189ff9c3ee0bf27808b78f870
  | _ => 0

def samplesQ55 : Nat → Bits
  | 0 => 0x408410251080221009818110208060100a060300c080c2102848442
  | 1 => ~~~(0xee6fe3d77efd54fbdfb65aefdc4f7dbdd4eb7fafdbdf2dad9387fde : Bits)
  | 2 => 0x7024e002409d988841034440b780c04a5982484180018635635280
  | 4 => 0x86100820230046302024802c00010881060180903052004818210c
  | 5 => 0x22494280484454c050265846c848012154e94022005528259387810
  | _ => 0

def compactPerms55 : Array (List Nat) := ([[], [81, 64]] : List (List Nat)).toArray

def compactDomains55 : Array (Sig × Nat) := ([(subcube 2 0, 5)] : List (Sig × Nat)).toArray

def compactWords55 : Nat → Nat
  | 0 => 0x9f
  | _ => 0

def compactCount55 (k : Nat) : Nat := match k with
  | 5 => 1
  | _ => 0

def compactPath55 (k : Nat) (i : Nat) : Nat := match k with
  | 5 => 0
  | _ => 0

def compactLive55 (k : Nat) (i : Nat) : Nat := match k with
  | 5 => readCompactBits compactWords55 (0 + 5*i) 5
  | _ => 0

def compactPoolIDs55 (k : Nat) (i : Nat) : List Nat := match k with
  | 5 => let v := readCompactBits compactWords55 (6 + 2*i) 2
    let n := v >>> 1
    let bits := readCompactBits compactWords55 (5 + 1*(v &&& 1)) (1*n)
    compactIDsFromBits bits 1 n
  | _ => []

def compactBucket55 (k : Nat) (i : Nat) : List Nat := match k with
  | _ => []
def samplesP63 : Nat → Bits
  | 0 => 0xbfb7fffa7fb93bf7cb65ec2abffbffbf3d7ff6fcf2ed02d55fee01a30f6b9f07e3673047dffe7b55cdf37f63f64fe7117bdcded0853adc036e4505ce045a9b04b95efebf29c8ba4988e6764cf4140e1b84d4120bebcda02
  | 1 => ~~~(0x114002000970094363064f6500108122006452a0b84821810b84513f6e078bc265ff3544910810188661544a4482c1b1f15e4e95e5ac1645437615c734dbbbc5889832c630acd288dcccb2e9c6371f3be5dd66652dede9a : Bits)
  | 2 => 0xfcdbfe6ffdf277cf345e00f73ff79f6fffbc3fe33cf8e79b7f90f34c3e0fa0d61b840505f7fbf7f9f3ecdcb9cf8fd8f3f02e1f0f607d0fc3c0fa06d1100218c79f8f79ded774378e741c79e0c2010718e088e1e374b5408
  | 3 => 0xfb57f7f5df7d9cf9771237293ffdf3fedecdc9e5dd1f79efa7af3c375225c7e82c98800bb9ffbffebe27ecdef3b1e72c94d72673eb8470dc831e3b6060a5200bebb7f7e23e9cc1b03fa99667486210600323ee2dad12190
  | 4 => ~~~(0x8900440108814e5045d243b8040000c158d00c5108d4058662239e4132de6372b3ce86c00e22014f1040880f20da32f9cc5175309335cd3aa59267266e77e2c0306e8ba06d0a3fe32285e44f96ed67a97e7c1abe39f3f0 : Bits)
  | 5 => 0xdfebffdfbbcecd67ec8d4f55ffdeedfff7e7529fbbcffd78ea7459fce1946a3365786862ffeffc9ef75d13ce7cfeb9af8d4141951da316753b71f43626c1662146f8aafff6a3c2fed2488a99b12ed022154545f403e82f0
  | _ => 0

def samplesQ63 : Nat → Bits
  | 0 => 0x4048200981444400100a02c54880103104c0310032120531200102103084401000904582588202544000602206400012840cc02005442c009141032018210400a15288a0094082400086004c081a0a048424120b8304202
  | 1 => ~~~(0xeebefcfefedff6feddfdb8bedf5fb7f77fbfecefeff1cbfedef7bff9f7fef77fdae5fbbdbb3efcffd77ff5efdfd7efc5bdfbbb9fbcbffbfe4fdf7eddff6fef7feeba77ef72edffdaffdebeffdfe77debb3ddeef5adedfbe : Bits)
  | 2 => 0x3241392040880104ba0fd00b44402022010c658844d3840c19a042041100120806b1a598761a52083080481000300ac62110fc06210510f2aa8d400014421201a0d615ad6042408600828004060d01868cac1a074b1400
  | 3 => 0x4a8441aa082020280cd8894cd0101801285a402a2504370cc50818880023000422479b139123c4a002600408100a280847989061404685a47c116458400c006aab255a2308041001a00142208433840819caa25ad00110
  | 4 => 0x8920420300010640455003a031a004009050023402042020e601840022802030804a024201c58810450800c080047410860000798098050440208442202020b44a0160520081800851080900285206111102c54084080c
  | 5 => 0x201480a0141120880130302a1200a404411040694421080202a020010440844c1001820c822cc080100111005094094528000281a8199104080a4800400808514408224d422100920040020192a44029304044d000e80a0
  | _ => 0

def compactPerms63 : Array (List Nat) := ([[], [64, 81], [50, 16, 84], [50, 80, 65]] : List (List Nat)).toArray

def compactDomains63 : Array (Sig × Nat) := ([(subcube 1 0, 7), (subcube 2 0, 7), (subcube 16 0, 7), (subcube 32 0, 7), (subcube 4 0, 6), (subcube 0 4, 6)] : List (Sig × Nat)).toArray

def compactWords63 : Nat → Nat
  | 0 => 0x3076223f
  | _ => 0

def compactCount63 (k : Nat) : Nat := match k with
  | 8 => 1
  | _ => 0

def compactPath63 (k : Nat) (i : Nat) : Nat := match k with
  | 8 => 0
  | _ => 0

def compactLive63 (k : Nat) (i : Nat) : Nat := match k with
  | 8 => readCompactBits compactWords63 (0 + 6*i) 6
  | _ => 0

def compactPoolIDs63 (k : Nat) (i : Nat) : List Nat := match k with
  | 8 => let v := readCompactBits compactWords63 (24 + 6*i) 6
    let n := v >>> 3
    let bits := readCompactBits compactWords63 (6 + 3*(v &&& 7)) (3*n)
    compactIDsFromBits bits 3 n
  | _ => []

def compactBucket63 (k : Nat) (i : Nat) : List Nat := match k with
  | _ => []
def samplesP85 : Nat → Bits
  | 0 => 0xdffb4f7fcd93bb4
  | 2 => ~~~(0x4020075441838b4 : Bits)
  | 4 => 0xf3e7a33c7f8cccc
  | 6 => ~~~(0x1403eb080d9c3cc : Bits)
  | _ => 0

def samplesQ85 : Nat → Bits
  | 0 => 0x204080920800224
  | 2 => 0x420006012400142
  | 4 => 0xc89186842a5c88
  | 6 => ~~~(0xeaf69edb6f5a3ee : Bits)
  | _ => 0

def compactPerms85 : Array (List Nat) := ([[], [32], [100], [100, 32]] : List (List Nat)).toArray

def compactDomains85 : Array (Sig × Nat) := ([(subcube 16 0, 4)] : List (Sig × Nat)).toArray

def compactWords85 : Nat → Nat
  | 0 => 0x4f
  | _ => 0

def compactCount85 (k : Nat) : Nat := match k with
  | 4 => 1
  | _ => 0

def compactPath85 (k : Nat) (i : Nat) : Nat := match k with
  | 4 => 0
  | _ => 0

def compactLive85 (k : Nat) (i : Nat) : Nat := match k with
  | 4 => readCompactBits compactWords85 (0 + 4*i) 4
  | _ => 0

def compactPoolIDs85 (k : Nat) (i : Nat) : List Nat := match k with
  | 4 => let v := readCompactBits compactWords85 (5 + 2*i) 2
    let n := v >>> 1
    let bits := readCompactBits compactWords85 (4 + 1*(v &&& 1)) (1*n)
    compactIDsFromBits bits 1 n
  | _ => []

def compactBucket85 (k : Nat) (i : Nat) : List Nat := match k with
  | _ => []
def samplesP87 : Nat → Bits
  | 0 => 0xdfbfff3b167bd5ffbf3bab65be76583b9fd9bf3f43c39210f4e5ec8
  | 1 => 0xed3f47f6679d00f9fdfdd7db4c9845800bffd9d98db8006b0f77014
  | 2 => ~~~(0x4080440103d9c1008109c3248c9855a993806b594503806bfc872dc : Bits)
  | 4 => 0xfafffcf5d9f8caf7e3ffeb3ec18fe7a1cfa767d07f6781ef0c9a33c
  | 6 => ~~~(0xb0100365438de012030ab5b40066fb3c80195900be393ff0470f3c : Bits)
  | _ => 0

def samplesQ87 : Nat → Bits
  | 0 => 0x204820440904284010232086020824002141a028030082082444888
  | 1 => 0x12d13c489040ef7860086b87c279902649df085080a08e1f3f75004
  | 2 => 0x408414010290812408904a000051010908141084205008160230502
  | 4 => 0x520011024031081030484081402005016204500480520a0408a230
  | 6 => ~~~(0xf4fcf6edbfd7a96d7bbf7af62bdd757f7955fdfcebf6db5ea674fbe : Bits)
  | _ => 0

def compactPerms87 : Array (List Nat) := ([[], [32]] : List (List Nat)).toArray

def compactDomains87 : Array (Sig × Nat) := ([(subcube 2 0, 5), (subcube 64 0, 5), (subcube 0 2, 5), (subcube 1 0, 4), (subcube 4 0, 4), (subcube 16 2, 4)] : List (Sig × Nat)).toArray

def compactWords87 : Nat → Nat
  | 0 => 0x39627e522017650397e8058231d1f
  | _ => 0

def compactCount87 (k : Nat) : Nat := match k with
  | 6 => 1
  | 5 => 1
  | 4 => 1
  | _ => 0

def compactPath87 (k : Nat) (i : Nat) : Nat := match k with
  | 6 => 0
  | 5 => readCompactBits compactWords87 (29 + 12*i) 12
  | 4 => let v := readCompactBits compactWords87 (83 + 12*i) 12
    (readCompactBits compactWords87 (71 + 12*(v >>> 12)) 12) ||| ((v &&& 4095) <<< 12)
  | _ => 0

def compactLive87 (k : Nat) (i : Nat) : Nat := match k with
  | 6 => readCompactBits compactWords87 (0 + 5*i) 5
  | 5 => readCompactBits compactWords87 (41 + 6*i) 6
  | 4 => readCompactBits compactWords87 (95 + 7*i) 7
  | _ => 0

def compactPoolIDs87 (k : Nat) (i : Nat) : List Nat := match k with
  | 6 => let v := readCompactBits compactWords87 (23 + 6*i) 6
    let n := v >>> 3
    let bits := readCompactBits compactWords87 (5 + 3*(v &&& 7)) (3*n)
    compactIDsFromBits bits 3 n
  | 5 => let v := readCompactBits compactWords87 (55 + 6*i) 6
    let n := v >>> 3
    let bits := readCompactBits compactWords87 (47 + 2*(v &&& 7)) (2*n)
    compactIDsFromBits bits 2 n
  | 4 => let v := readCompactBits compactWords87 (102 + 2*i) 2
    let n := v >>> 1
    let bits := readCompactBits compactWords87 (102 + 1*(v &&& 1)) (1*n)
    compactIDsFromBits bits 1 n
  | _ => []

def compactBucket87 (k : Nat) (i : Nat) : List Nat := match k with
  | 5 => let d := readCompactBits compactWords87 (61 + 1*(i % 1)) 1
    let off := ((i/1 + d) % 1)
    let v := readCompactBits compactWords87 (62 + 9*off) 9
    if v >>> 1 == (i/104729)%251 then [v &&& 1] else []
  | 4 => let d := readCompactBits compactWords87 (104 + 1*(i % 1)) 1
    let off := ((i/1 + d) % 1)
    let v := readCompactBits compactWords87 (105 + 9*off) 9
    if v >>> 1 == (i/104729)%251 then [v &&& 1] else []
  | _ => []
def samplesP91 : Nat → Bits
  | 0 => 0x5f6fffcd469bf67deef7f8f1b73799514afbdb7eba7949c901b2adad64
  | 1 => ~~~(0x11103200250b3e000415008197391d956ea2016ce33011fd81ba26c976 : Bits)
  | 3 => 0x7d5fb7bffd8d197eff9f972eeb993d84b566ff44e7aafe34924c7bca92
  | 4 => ~~~(0x46005804a855b00a8021f22a3172015b5805814ac4a6a7493de192ef2 : Bits)
  | 6 => 0x76bffff22b677a7fbd7f4f83977f669524bf7dbded563074819b167c72
  | _ => 0

def samplesQ91 : Nat → Bits
  | 0 => 0x20911052812408a82084491250b00388844a4a2088210a498850a92844
  | 1 => ~~~(0x6eebedeedbfde3cdbfddfebf83eef8ef9ff6a9eeebf77ff3f3a867d9fe : Bits)
  | 3 => 0x2a244420250228c9210189280e0a0a108468904420246439028638890
  | 4 => 0x4684484088143440448b2848142a80401b4a1c20090109230a846d108
  | 6 => 0x940828550088551090122442d030c0212313408214420942487145422
  | _ => 0

def compactPerms91 : Array (List Nat) := ([[], [49, 100], [16, 99], [16, 97, 99, 100], [48, 49, 67, 100], [48, 65], [64, 49, 99, 100], [64, 97], [96, 67], [96, 65, 67, 100]] : List (List Nat)).toArray

def compactDomains91 : Array (Sig × Nat) := ([(subcube 1 0, 4), (subcube 2 0, 4), (subcube 8 0, 4), (subcube 16 0, 4), (subcube 64 0, 4)] : List (Sig × Nat)).toArray

def compactWords91 : Nat → Nat
  | 0 => 0xff0ff0339b38c447f6452ff0ff082be51a00d04ffc1fe05749e23196566ff03544885fe0bd68f93a1ffe006fffd08900688d11f
  | _ => 0

def compactCount91 (k : Nat) : Nat := match k with
  | 6 => 1
  | 5 => 2
  | 4 => 1
  | _ => 0

def compactPath91 (k : Nat) (i : Nat) : Nat := match k with
  | 6 => 0
  | 5 => readCompactBits compactWords91 (26 + 12*i) 12
  | 4 => let v := readCompactBits compactWords91 (279 + 12*i) 12
    (readCompactBits compactWords91 (267 + 12*(v >>> 12)) 12) ||| ((v &&& 4095) <<< 12)
  | _ => 0

def compactLive91 (k : Nat) (i : Nat) : Nat := match k with
  | 6 => readCompactBits compactWords91 (0 + 5*i) 5
  | 5 => readCompactBits compactWords91 (50 + 6*i) 6
  | 4 => readCompactBits compactWords91 (291 + 7*i) 7
  | _ => 0

def compactPoolIDs91 (k : Nat) (i : Nat) : List Nat := match k with
  | 6 => let v := readCompactBits compactWords91 (20 + 6*i) 6
    let n := v >>> 3
    let bits := readCompactBits compactWords91 (5 + 3*(v &&& 7)) (3*n)
    compactIDsFromBits bits 3 n
  | 5 => let v := readCompactBits compactWords91 (64 + 2*i) 2
    let n := v >>> 1
    let bits := readCompactBits compactWords91 (62 + 2*(v &&& 1)) (2*n)
    compactIDsFromBits bits 2 n
  | 4 => let v := readCompactBits compactWords91 (298 + 2*i) 2
    let n := v >>> 1
    let bits := readCompactBits compactWords91 (298 + 1*(v &&& 1)) (1*n)
    compactIDsFromBits bits 1 n
  | _ => []

def compactBucket91 (k : Nat) (i : Nat) : List Nat := match k with
  | 5 => let d := readCompactBits compactWords91 (68 + 1*(i % 4)) 1
    let off := ((i/4 + d) % 15)
    let v := readCompactBits compactWords91 (72 + 13*off) 13
    if v >>> 5 == (i/104729)%251 then [v &&& 31] else []
  | 4 => let d := readCompactBits compactWords91 (300 + 2*(i % 2)) 2
    let off := ((i/2 + d) % 9)
    let v := readCompactBits compactWords91 (304 + 12*off) 12
    if v >>> 4 == (i/104729)%251 then [v &&& 15] else []
  | _ => []
def samplesP95 : Nat → Bits
  | 0 => 0xbeefffff5b5b0fbfdb3759cc3ff7cfeff6bdc7defb75fc665eae88c39c43761f1ef6660bfbfb9f4feb7d95f8dca77f8a58e58a7d0856a36ee43b3e846091b30dd7ccf56ee59bf1795688dc92271062048751152dd13b310
  | 1 => 0xdfabf59fffebf9ce7039ccb07ffeffb67fdef8f90f878f879fdfc78ce0739863ec0000b1fddffbf8f39e1f3f7f3b8ff1a0fa0f87f3e0fc1f07c1c00513260012eaef67f7b9e31e1e0d0f70e3c82080393886dbc9a1d4424
  | 2 => ~~~(0x24804120041a5844b1988cf000041242109844c0b460607030fa64686699e57469f22b8d100011063889230088d2ff510ec0daf1b16cb964575a30557beab548489c5c5245975db2e8b60a70ff1d0793bdf9f2315b577c : Bits)
  | 3 => 0xfad7fefebeb7a7d4bf4332273ffffb7fe945bd3d375a36ff677fb6164ed827c4c1c90083d73ffff12febfaa9a7ff69350b2cf59f370ec59148f46718042e0853be77bfcd663423c7aa1927bf28e11048088e6f175c64448
  | 4 => 0xf75fff73ffd4ffa96f8caa5bbfa9fffdff3bf6e7ccee4b7ff92d776a132cdf1b03062973fff477f6d691faf6f8dcfe4c54d56d62cf995a909734b9679b102383d59bde913f5cdc91aae6e84d1612c1b17060bc223e818b4
  | 6 => ~~~(0x108400001a920b8833277a3000208a004014f0b1040008665c2fd78a5852770b89666df100101260821118a8f4324b0848f5ef57e7c8f41986b07c07bb37339bd246360021b69a158a0cfcdb2e32e3bdfce67d0df84fcb4 : Bits)
  | _ => 0

def samplesQ95 : Nat → Bits
  | 0 => 0x411042012404904020c82412a410080c10404c2204340200e1810100420480c0210898604b089040090400a04024148900039882088863012000e18090200821820c812c218801280200c012091052018090150d0128210
  | 1 => 0x205502702210042087443247b820018208500437c8103619c02c282210802110008f8d0858cb7218121200082801004943ca80170fd01101608fa060401850806a4a4163b92104120108304000110e05709793c8a154004
  | 2 => 0x2482052404121000a10884d120422010582808088406411022a044004090c024015201900a24aa40040440492020046468c0054162080180209024002048240706222025206080440400a00a020084664244090e842802
  | 3 => 0x52880834508480140b88d984748806001aac98804e4488027804001812050200a30327507308dc12481100104900186141518c83029ea188e4047830080240b9035b60c46002281001104890922d04a84686c175820440
  | 4 => 0x8a2008409220016002341a04181441040281108118088a20c1000142842000494204286a4140500800088500048cb1030102108600308228c500c080441001605911c900450900088840004124680980148282216810a0
  | 6 => ~~~(0xef7befdbf57ffd77eef8addff77defff5defefeaaeff6fd5f7eb6d77ffeffdf6ffbdba7d4fbadffdbfd7dcfdfeffddefdebfdefebeadefddbf69f7d7d6fdfefff27fb72e77ffbfbfcbddfedfbdbafb6feefc7d9ff96fef6 : Bits)
  | _ => 0

def compactPerms95 : Array (List Nat) := ([[], [32], [49, 100], [49, 32, 100]] : List (List Nat)).toArray

def compactDomains95 : Array (Sig × Nat) := ([(subcube 1 0, 7), (subcube 2 0, 7), (subcube 4 0, 7), (subcube 8 0, 7), (subcube 16 0, 7), (subcube 64 0, 7), (subcube 0 2, 6), (subcube 0 8, 6), (subcube 10 0, 5), (subcube 18 0, 5), (subcube 72 0, 5), (subcube 2 8, 5), (subcube 16 2, 5), (subcube 64 8, 5), (subcube 3 0, 4), (subcube 5 0, 4), (subcube 6 0, 4), (subcube 9 0, 4), (subcube 17 0, 4), (subcube 20 0, 4), (subcube 65 0, 4), (subcube 68 0, 4), (subcube 24 2, 4)] : List (Sig × Nat)).toArray

def compactWords95 : Nat → Nat
  | 0 => 0x9058af2ce4c2749e8299a99d9a6c7e4b907674515674d5f72fdead3b2d5a8b4c5d2662910e5caa3054063d1e9c01434ff01ea14a5f83276916fce2f6bff803385fe03fc07f80be101a197027f80ff01fe0119ab1139240ad42267b995c253fe03fc017a330c5a07de90e50fff010085645806890c011bc048bc20604095573eb34d2951451050d2faaf14dcececc34aeaa489ca9268d07d864c59246640e3242f619800102802ec82c7661c1820c040172450c9700363b28ac434824d462f0814e005c1c515247018704180805c4891c286429c6448a0706180ae044898c046402e221cd18065a505061c30132017121e48c93041422e1eb8c071e59706123c0126810d8260141308c6c3830c047805c3cdae244c21b0a3c38324180935c1841b5c38318200430e480c3860a7060200b874804382840e0cc8c001977fdfffdef7ffffdfffdff7ffdfffffffffff5fffdfffffffdfdfccc099811301e60a48548ca9115662a4c5498a9111261acc249845214a32142428087310a6214c4284653042228cc5198490a8c8808804803fe0ff03acf417fe08819603c986b5ff030eca85fe0ff0511fc9ade1a77d54721c8d77011cfddc430e44e6f4770038c46080a4ceaf86b020cb6f63f01a5e6e9314e31183cd0332c30806e597418a438cc1e6f5803c5c290e316d9a5e4060ffffffffffffd21519109101108d0090070b1a23f
  | 1 => 0xf499fe0002839d05fe0104b718f7fe0050f52eafd2d80ab4e489fe0012949e777485208b2408ce4b8eea92ef968c485e16ece8c61ec4ce91fe012017fe00fc7fd446d02e3c67866bca9b242bbc0bfe01445b6ed54859d28e8a6f72adfe01b66866cf7833fe01fe0026a73ae6fccaba5dfe01e0cdfe01fe01121e3e9f9c43cc0f963f3802da0c1e5654010cf0ae362692d0146c87e8bf744edc1a7e659a543ec8a8db9480d0e8367266dc3e9dfe011e9754054607ee10c8d232d77ce5fe01fe01fe00fa6ca0fca026b6a5fe01c4d0b8de20f244bd1d079afedc3bfe0158e2f00106262001b231268811210000818010000238020b0b1a8a8a8a8a9a0a1989899909189808179707169615e282a19101011090000045000100002545450901011848022e0100230182c500cfef76ff773e7f7bbf4ff773bddefadf6fd7cfe7f7df77eafd7ef54ff5faf9fcfedf7e9fcfd69c47ce236711b380690b04e256712b38159c4ace256712838959c01ce50a72b5215a9ca5ce6267081214088a0ce5027281111c9cae4644a42a739529ca8ce416703d38989cb98a80998a80398880598480998480398090a98a80898880498280498090a90a80890a8048c880488a80888a80288880880880483546ddff8061a5cb182a47f806b035eebfc020977ebd0f0fcc6a0d4ff017d2a9f1ff80d3be789506982827bcd7d6d518dab64f3ba4dfcd
  | 2 => 0x28de93fe0b05c7a3fc064f253e24bfc1fe0ff07f828cbfe0ff029bbfc1fe0ff07f83fc1fe0f724d1abd5042ac9ff81805619d795755d51f61c4a429a0a282da019c098a8089ca98880488a8088048888088041013
  | _ => 0

def compactCount95 (k : Nat) : Nat := match k with
  | 9 => 1
  | 8 => 7
  | 7 => 26
  | 6 => 33
  | 5 => 5
  | _ => 0

def compactPath95 (k : Nat) (i : Nat) : Nat := match k with
  | 9 => 0
  | 8 => readCompactBits compactWords95 (30 + 12*i) 12
  | 7 => let v := readCompactBits compactWords95 (973 + 15*i) 15
    (readCompactBits compactWords95 (913 + 12*(v >>> 12)) 12) ||| ((v &&& 4095) <<< 12)
  | 6 => let v := readCompactBits compactWords95 (4949 + 17*i) 17
    (readCompactBits compactWords95 (4541 + 24*(v >>> 12)) 24) ||| ((v &&& 4095) <<< 24)
  | 5 => let v := readCompactBits compactWords95 (8353 + 14*i) 14
    (readCompactBits compactWords95 (8209 + 36*(v >>> 12)) 36) ||| ((v &&& 4095) <<< 36)
  | _ => 0

def compactLive95 (k : Nat) (i : Nat) : Nat := match k with
  | 9 => readCompactBits compactWords95 (0 + 6*i) 6
  | 8 => readCompactBits compactWords95 (114 + 7*i) 7
  | 7 => readCompactBits compactWords95 (1363 + 8*i) 8
  | 6 => readCompactBits compactWords95 (5510 + 9*i) 9
  | 5 => readCompactBits compactWords95 (8423 + 10*i) 10
  | _ => 0

def compactPoolIDs95 (k : Nat) (i : Nat) : List Nat := match k with
  | 9 => let v := readCompactBits compactWords95 (24 + 6*i) 6
    let n := v >>> 3
    let bits := readCompactBits compactWords95 (6 + 3*(v &&& 7)) (3*n)
    compactIDsFromBits bits 3 n
  | 8 => let v := readCompactBits compactWords95 (548 + 11*i) 11
    let n := v >>> 7
    let bits := readCompactBits compactWords95 (163 + 5*(v &&& 127)) (5*n)
    compactIDsFromBits bits 5 n
  | 7 => let v := readCompactBits compactWords95 (2789 + 12*i) 12
    let n := v >>> 8
    let bits := readCompactBits compactWords95 (1571 + 7*(v &&& 255)) (7*n)
    compactIDsFromBits bits 7 n
  | 6 => let v := readCompactBits compactWords95 (5983 + 8*i) 8
    let n := v >>> 5
    let bits := readCompactBits compactWords95 (5807 + 8*(v &&& 31)) (8*n)
    compactIDsFromBits bits 8 n
  | 5 => let v := readCompactBits compactWords95 (8474 + 2*i) 2
    let n := v >>> 1
    let bits := readCompactBits compactWords95 (8473 + 1*(v &&& 1)) (1*n)
    compactIDsFromBits bits 1 n
  | _ => []

def compactBucket95 (k : Nat) (i : Nat) : List Nat := match k with
  | 8 => let d := readCompactBits compactWords95 (625 + 3*(i % 5)) 3
    let off := ((i/5 + d) % 21)
    let v := readCompactBits compactWords95 (640 + 13*off) 13
    if v >>> 5 == (i/104729)%251 then [v &&& 31] else []
  | 7 => let d := readCompactBits compactWords95 (3101 + 5*(i % 24)) 5
    let off := ((i/24 + d) % 88)
    let v := readCompactBits compactWords95 (3221 + 15*off) 15
    if v >>> 7 == (i/104729)%251 then [v &&& 127] else []
  | 6 => let d := readCompactBits compactWords95 (6247 + 6*(i % 31)) 6
    let off := ((i/31 + d) % 111)
    let v := readCompactBits compactWords95 (6433 + 16*off) 16
    if v >>> 8 == (i/104729)%251 then [v &&& 255] else []
  | 5 => let d := readCompactBits compactWords95 (8484 + 2*(i % 5)) 2
    let off := ((i/5 + d) % 29)
    let v := readCompactBits compactWords95 (8494 + 13*off) 13
    if v >>> 5 == (i/104729)%251 then [v &&& 31] else []
  | _ => []
def samplesP107 : Nat → Bits
  | 0 => 0x7abf2fefd4580fffe76c98cbfa8ec006feece7267402acb7e488
  | 1 => 0x5e7ffcbd6d8447dd3ffb73515d20252bfc573e9cf990517d5260
  | 3 => ~~~(0x841009dd004780c240c89115adec13a0454a5383597ac8d6cea : Bits)
  | 5 => 0x7dfff7d6db677faeffb5adbd1fd343bfa797897b31d7860e2d72
  | 6 => ~~~(0x108024264d434880032130c91da367a8a2870a0679d2d7363770 : Bits)
  | _ => 0

def samplesQ107 : Nat → Bits
  | 0 => 0x545511008a2f590a00c6a1c89102264ec8c21004cc89c378480
  | 1 => 0x21a045408253ae081245c078b1891013d442121020b199ed5040
  | 3 => 0x84910051004514200a82a04084281042a2008850c4804128214
  | 5 => 0x21000082408002409000000002408000001804a100000002122
  | 6 => ~~~(0x6f7dfb9dbefef5febbee7f9fcfffbb74eeefbbdf7fcefe37b7f6 : Bits)
  | _ => 0

def compactPerms107 : Array (List Nat) := ([[], [16, 99]] : List (List Nat)).toArray

def compactDomains107 : Array (Sig × Nat) := ([(subcube 1 0, 5), (subcube 2 0, 5), (subcube 8 0, 5), (subcube 64 0, 5)] : List (Sig × Nat)).toArray

def compactWords107 : Nat → Nat
  | 0 => 0x41b1f
  | _ => 0

def compactCount107 (k : Nat) : Nat := match k with
  | 6 => 1
  | _ => 0

def compactPath107 (k : Nat) (i : Nat) : Nat := match k with
  | 6 => 0
  | _ => 0

def compactLive107 (k : Nat) (i : Nat) : Nat := match k with
  | 6 => readCompactBits compactWords107 (0 + 5*i) 5
  | _ => 0

def compactPoolIDs107 (k : Nat) (i : Nat) : List Nat := match k with
  | 6 => let v := readCompactBits compactWords107 (13 + 6*i) 6
    let n := v >>> 3
    let bits := readCompactBits compactWords107 (5 + 2*(v &&& 7)) (2*n)
    compactIDsFromBits bits 2 n
  | _ => []

def compactBucket107 (k : Nat) (i : Nat) : List Nat := match k with
  | _ => []
def samplesP111 : Nat → Bits
  | 0 => 0x7d6ffd5fffff6c6cc32c675ffffff3d9edca3916fdf7bef98dedee19903099d10099c77ffff9f3ff3f2398df964310624670f0cf3e7f1eec479c10300f18c6fffe67299e4698d0673a00105a6ec408f5ef5220
  | 1 => 0x5f5bfffb4f3bb9c3f2c508dfefed3fff9f1dd9e35f1dcfa7c2f0967271ed70200a023fffb7ae9e3bdcbcf5fe9cbc62d4e9d9347a8b1c65519002610231fdfcbdbbb314e1e9d283cadcc9c000112adeb3348980
  | 2 => ~~~(0x44c08010cb1244263b66bd0060520000c8c81c15e0722d1a27cce385998c57feb7f80012408c21e222c80e09ebb4278a0ff88fc625e05697dfff3cbb5014031224d31ec499b41fa1fefe8a3b7fc1823aebffc : Bits)
  | 3 => 0x77affaffbcf19fbeec9e632fff3fecff13b5bfddfee761d7e00e19e5df88c5cee0027fffec59eec6e6dc1ff3f9b8df5ba67e888ce142e11b1023e2c884ffc77365dc276439371c7e25662820113b3964988c54
  | 5 => 0x7ef7ffedfdf677733972fcbfded7ffef6eeee7fb9e1bf75a333e660c6dd38e3e0b7c7fa57fcf5d3c637feaed7b3f82a891a7cb75449f85a1e8ec03c337237bde03ccdaf9910d63b118ade083a251e00bc235c8
  | 6 => ~~~(0x1020004801721920884c6430080000c9030039129c11c503c1ae3645f5e1989e0a9a072400491c20441018df113c92c2c770f04f8d1fe591d2ae63f23838c6de01f60ef1b11492673cedf05a7b7be8f5d3ddc0 : Bits)
  | _ => 0

def samplesQ111 : Nat → Bits
  | 0 => 0x29104a0800010921451982881031001124980392000a12812001004424824089d2004631c483201212000100604c22720018803212104150802020a4410c0f0e224098240080006060c084061c008e1a91200
  | 1 => 0x20a42088b88402280d1ae62d0480089078008eb0b4b4211a080241010802890ed1d92e5932a0081084084088832d499604539321257432414421082101d968a99b11004108508100100b4550a1ac9e93348100
  | 2 => 0x44c89022c21044023a643d648208204cc9214c09acd0cc120180c10011040156257f394c30500a01012040241720c108f4c263c4c9a58c800485080a2ae370e1582801024040a00a061a63d0a23e51c504002
  | 3 => 0x8520d200108600102611890e014002882cb0009020984a001218008200412310e2440a68c1080044080122114408221a1080c0a4883049c209001040c24855264402400112210500644282448422164880850
  | 5 => 0x10810020600880440840142124004400410104008400840444000a290200040200291004100450800442844001204000a04201400084800110084100202120400800228800120a10820820902014008420488
  | 6 => ~~~(0x6fdfbff7efadfeff77f7dbfefff79efddffff5fffbcfffed7f7bddbffb7eff7dff77f7f7df7dffbdf5fe7effd7f6fe7fffedeeffffbbddfffdfbdfbfeebef7fef7f7affbfd7fbbf7bffdbeff7ff3edfdfbdfda : Bits)
  | _ => 0

def compactPerms111 : Array (List Nat) := ([[], [33, 48, 101]] : List (List Nat)).toArray

def compactDomains111 : Array (Sig × Nat) := ([(subcube 1 0, 7), (subcube 2 0, 7), (subcube 4 0, 7), (subcube 8 0, 7), (subcube 32 0, 7), (subcube 64 0, 7), (subcube 0 2, 6), (subcube 0 4, 6), (subcube 3 0, 5), (subcube 5 0, 5), (subcube 34 0, 5), (subcube 1 4, 5), (subcube 8 2, 5), (subcube 32 2, 5), (subcube 64 4, 5), (subcube 9 0, 4), (subcube 33 0, 4), (subcube 72 0, 4), (subcube 7 0, 4), (subcube 40 2, 4), (subcube 42 0, 4), (subcube 65 4, 4), (subcube 69 0, 4)] : List (Sig × Nat)).toArray

def compactWords111 : Nat → Nat
  | 0 => 0x3820c05995005c80e325c0156a1419c624ccaf265654765158863914c146068185640a286020073016c24028c3629538c1cb22ad64451c60ab92721ac51c35802767191d3114b8e1668307146430a20d4f0d081401c5c4ca9120c5ab002b8a182ac98b560b89951a40e850871915061c1060200aae2040e0b3214a900e0c3015c541160864110911869516b8a130a34d3b0e0830100b880f2068c03264c2151e507c73c6020036b89c666352345e0971b2c658998c9198d68bcdb12a2ca131f188196874584066d89426146a40e0830136007ae1e6c818084d70f200428704509980e27feffffbffef7e6ffafe7e7efffffbffff7f7fafffeffaeffffffdfefeffafffeffff6606cc0c9815216a02dcc1f84b330e242cc25884b330da22b405490a9195612a425480ab315262a4c54888b30d261948528c87110a22140439885310a620464c44485464444424404403402ff01d47fc1fe0d61004e88bfe0091ff8302abc86007f83ad9eae797ff8174e98da84de045e1d0adb5ff802244206e1fce94d4ec7ea9692e85e67e498318198003388c1068a4ce2ee6d0a238780cde76d131768b851982023b58689773d5cbe0b443e2ede024cba8dc28ce230600d670d5938521c460bc1bce18b19483db81a6b2eb30cc1de92e9600710ceb1690ccb4060ffffefffbffffffffffd21519311111111109101100d0890090070b1a23f
  | 1 => 0x48f89e23826ccc48f11c2348590920e218822000000c0226088e0d1c260890901a8c2718e827483865422a1a080b22261b14652298f20ab82a08000c022a002a2c0026e826261e8ee826262a2a2a32074420083320b91a162a260a0e04260a260a0a0c020e040c033ff3f3f7b3df5faf937bf773f9bce9fdfa7fbed7efa7feb9ff9fedeefb5fafdeadbefa7fafdbefa7f3fbec138d99c634858a02c539579c6b4e32a428b38959c0848522428521689c6fce07e71bf382490b24059272b511139cc74853a028121408ca0ce502728111268cb34059a72b9215c8cae4057672b9394d9c398a8099888079868099828c998090a98a80898880698680890a8c890a88890a80890a8068ca8088c88068c880484a88884a80880a8c880a84880a808808806db067d427a2ff00467b71c6e304979d49ffc07f80ff01fe03fc052846737fe003ce84192b197ab3b97bf3f801012df8e1bba3a7353e994daae06f929fe02f52c918d323e20f79cbb178d67627e949330ee92a9c353d0858999525100e8e4882ff01fe01fd5873eca2caa4d05e820a565a62c8282cf42601636d0698ff80ff01fe00887ff803c0f2802ec0b0a0ba76886b2c00681398410608410410e11402c231f8cf667823b19ccae1c6ac3365890bcc581ab4d552a144eca51d1ae8693eb1de4dd464d2bb14509b443c1bd8b343fa12606480cc0010a85005d9058e0c
  | 2 => 0x259058ff87f83107f87f8129ff8014acd3b69b3e459d2e54402aad6b9f338ef1bc6e1f8e5a05b401a428485890b5214a42a42a12a02232a62201a32a02201a02e61a02202e60a32202a62201a02a322018ba23f50e6ee09d269bd427fe03c53ea43ff00bc45621568d57592712d0a1f8819129ec48d19749c96fd849ac21c0bff016d21b20e09aff01d6f9b5a0dafd2145ccbfc0159dff013917fc07f805c725ea529717835481a816f933faa184bfe02f59fd3d5b6aecaffc06bbf7d484d29290ff808b70b65bfc0108eff00dc01107b697ff01fe018cff5b00a21fe03e83d39eff005c655835d0c9e02cc575e5e3470d5a61aa0201c02020e00078054c10000a306695129e13c6714c3929165e03c1760ed5b4ad2564a4149a614a0941292304648
  | _ => 0

def compactCount111 (k : Nat) : Nat := match k with
  | 9 => 1
  | 8 => 11
  | 7 => 34
  | 6 => 38
  | 5 => 7
  | _ => 0

def compactPath111 (k : Nat) (i : Nat) : Nat := match k with
  | 9 => 0
  | 8 => readCompactBits compactWords111 (30 + 12*i) 12
  | 7 => let v := readCompactBits compactWords111 (1496 + 15*i) 15
    (readCompactBits compactWords111 (1400 + 12*(v >>> 12)) 12) ||| ((v &&& 4095) <<< 12)
  | 6 => let v := readCompactBits compactWords111 (6373 + 17*i) 17
    (readCompactBits compactWords111 (5869 + 24*(v >>> 12)) 24) ||| ((v &&& 4095) <<< 24)
  | 5 => let v := readCompactBits compactWords111 (10123 + 15*i) 15
    (readCompactBits compactWords111 (9871 + 36*(v >>> 12)) 36) ||| ((v &&& 4095) <<< 36)
  | _ => 0

def compactLive111 (k : Nat) (i : Nat) : Nat := match k with
  | 9 => readCompactBits compactWords111 (0 + 6*i) 6
  | 8 => readCompactBits compactWords111 (162 + 7*i) 7
  | 7 => readCompactBits compactWords111 (2006 + 8*i) 8
  | 6 => readCompactBits compactWords111 (7019 + 9*i) 9
  | 5 => readCompactBits compactWords111 (10228 + 10*i) 10
  | _ => 0

def compactPoolIDs111 (k : Nat) (i : Nat) : List Nat := match k with
  | 9 => let v := readCompactBits compactWords111 (24 + 6*i) 6
    let n := v >>> 3
    let bits := readCompactBits compactWords111 (6 + 3*(v &&& 7)) (3*n)
    compactIDsFromBits bits 3 n
  | 8 => let v := readCompactBits compactWords111 (889 + 12*i) 12
    let n := v >>> 8
    let bits := readCompactBits compactWords111 (239 + 5*(v &&& 255)) (5*n)
    compactIDsFromBits bits 5 n
  | 7 => let v := readCompactBits compactWords111 (4161 + 13*i) 13
    let n := v >>> 9
    let bits := readCompactBits compactWords111 (2278 + 7*(v &&& 511)) (7*n)
    compactIDsFromBits bits 7 n
  | 6 => let v := readCompactBits compactWords111 (8025 + 11*i) 11
    let n := v >>> 7
    let bits := readCompactBits compactWords111 (7361 + 8*(v &&& 127)) (8*n)
    compactIDsFromBits bits 8 n
  | 5 => let v := readCompactBits compactWords111 (10301 + 2*i) 2
    let n := v >>> 1
    let bits := readCompactBits compactWords111 (10298 + 3*(v &&& 1)) (3*n)
    compactIDsFromBits bits 3 n
  | _ => []

def compactBucket111 (k : Nat) (i : Nat) : List Nat := match k with
  | 8 => let d := readCompactBits compactWords111 (1021 + 4*(i % 7)) 4
    let off := ((i/7 + d) % 27)
    let v := readCompactBits compactWords111 (1049 + 13*off) 13
    if v >>> 5 == (i/104729)%251 then [v &&& 31] else []
  | 7 => let d := readCompactBits compactWords111 (4603 + 6*(i % 21)) 6
    let off := ((i/21 + d) % 76)
    let v := readCompactBits compactWords111 (4729 + 15*off) 15
    if v >>> 7 == (i/104729)%251 then [v &&& 127] else []
  | 6 => let d := readCompactBits compactWords111 (8443 + 6*(i % 23)) 6
    let off := ((i/23 + d) % 86)
    let v := readCompactBits compactWords111 (8581 + 15*off) 15
    if v >>> 7 == (i/104729)%251 then [v &&& 127] else []
  | 5 => let d := readCompactBits compactWords111 (10315 + 2*(i % 4)) 2
    let off := ((i/4 + d) % 16)
    let v := readCompactBits compactWords111 (10323 + 12*off) 12
    if v >>> 4 == (i/104729)%251 then [v &&& 15] else []
  | _ => []
def samplesP119 : Nat → Bits
  | 0 => 0x6f7ffffff3d70bdbe5bef46fdfe7fcfff7ccd9eff9dc7f7133c06ec184e7d1eecc3f1ff7dfd4bfe8fafeb0fd32bb6e32213d630af59a5d85380fc6b03e3e35e98b26b279ae95f00c7444410d417c81c367cc90
  | 1 => 0x7b5bffb1feee70fe7898127fee7ff7bf3d8f2ef0f6f3a7e60f0f13c7eb80fa500081ffddfd3ecf2fcdf3e372fc44f4545ed83e6567a5e00e04e00101cce7e7bfef5e1d47230ac793619380320682eeda2c0324
  | 2 => ~~~(0x200c001180c1006d6ece7020082004181c0f08e0590c062309c543e6ce35d47e66b700148004664b08e2314437186fa273846e0567a5f887aeef49f1ea6632080c7a39d1b296a3387dd78633e7ff89166e6fbc : Bits)
  | 4 => 0x7eafff7f9c6bef3debc6698ff9ff1fff0bffdbe73f2f896f84738d7e46175c2e1181ffffa2d761df3dd0bfcffd832fa2af4142f50a65a5f44563003c47fe3a5e76f8b581d0fb90f896c000f25a83990cd85074
  | 5 => 0x77b7fddfed9ddce5f6479d1ffffbeff8fe7fb4f8cf3d569bc88ce3b61d78a4b02631f63ffe29fedf12ef5ffcc3785ba970a6bd9587c59a0b828c09c19be9dfce1c994af6d0142f7c69178601a5117837522b08
  | 6 => ~~~(0x2300d00000e4890e1969d50004300a023cc90e0a6310141860aafd705c2f8be9db816010010898c10d082f8d8e37e302c7933f587c5850d55ef87bdc4a805ce039c9667c019d4dc77d7c1ff5f90f8cb53db74 : Bits)
  | _ => 0

def samplesQ119 : Nat → Bits
  | 0 => 0x1082000804082420120108841800808408008110012080104c00810841100201300011044000a020023000c122c0006001c0010012002000c4000102002204200b200248200580080050010201088082210c10
  | 1 => 0x4a4210f04108a0107474d8684121010d8b291b511358010a0204820040c008b3b34b5c4d50205020081202086ca34e001cac92096d6e051200224480c636525ea120105010042804052a90a338ec6da240204
  | 2 => 0x200d0025804100444cc4602301004222952310c610082004004402048220442c02a6c68218a00804840888080413210420120c40855d4060024840211509818740050420484014020003300c9a106469109002
  | 4 => 0x1504480318010820038925860440c002044060862401ae00088100118408150c449083922114088280012021820c2019605121320000b820090888022941a5814409080808800508e8c025044211904c84060
  | 5 => 0x84810a09222010808a82261420900482501024a600828a4111104402081080440cb420b0a0012111040401448314104a2151640010902a20801120453888aca00880012101009042a851004cc103825520108
  | 6 => ~~~(0x7dcf7afddffbbfef5eed6ae77f5fdefebf2bfbdefdaaedbefdfddf6dfffdcfed72efd78f5bb3ffbfbef9faffeff7697eebf73fccdf7d76efeedbffef77ab8fef4bff97fff9dddfdefbf775afdf58fcef73df7e : Bits)
  | _ => 0

def compactPerms119 : Array (List Nat) := ([[], [98, 84]] : List (List Nat)).toArray

def compactDomains119 : Array (Sig × Nat) := ([(subcube 1 0, 7), (subcube 2 0, 7), (subcube 16 0, 7), (subcube 32 0, 7), (subcube 4 0, 6), (subcube 64 0, 6), (subcube 0 2, 6), (subcube 6 0, 5), (subcube 18 0, 5), (subcube 20 0, 5), (subcube 34 0, 5), (subcube 66 0, 5), (subcube 96 0, 5), (subcube 16 2, 5), (subcube 32 2, 5), (subcube 3 0, 4), (subcube 5 0, 4), (subcube 17 0, 4), (subcube 33 0, 4), (subcube 36 0, 4), (subcube 65 0, 4), (subcube 80 0, 4), (subcube 22 0, 4), (subcube 48 2, 4), (subcube 50 0, 4), (subcube 98 0, 4)] : List (Sig × Nat)).toArray

def compactWords119 : Nat → Nat
  | 0 => 0xfdff5fffdffffefeffdffefefefefefefefe7efeda61da615a603661b661b261b660b260b6603660326002618260826002603a22be60ea22ea62ea60ea602a32ae22aa22aa22ae62aa62aa322e61aa61ae602a606442e262e232626262602442a242a232a262a2621c429a429a329c229a229e629c629a629a321a221e621a621a621a219e611a615262d26252604c42ca42ca22ca62ca224a62144292429432923296229422922292229412921292029662946292629262923216221222122212121662126212621621922192019661926192619260c222c2220a228e610c228a2288228e220a220e218a218a018e610861622621c22c11401400a32222a22221a01a01200822bb1c2e677158a5ff81606e9285e83f038cea093581cf8bfe07cc3fe036b08cb163eaccbba44cd938c983ff81fe03c2bfe06040728b511fe07f81c0b8827527d20a0a0b955d397233118f9adf8c76b0ea388b476e69455a3b02ba110009104c0e136c5e8a71d8460833de6c9a28c460819b4e8e5293016013abb0a730403da74e21446081891f37a74ca3384c0e8b7a690a3b04c0eedba4ac0eb690628c860f629db402594600bb4d219607374731461374fb4808728ec2307bcd8090ce17db700159462393aee34060ddcd0f78607fffffffffffffffffffffffff7ffd845445045464c44444c434434234038224228024028014014018393f
  | 1 => 0xcd0008141820c040360e5dd833ae02cf0e043002e4c28300180906c682090a304956b44b040a24a830c040162618280025cb172214b9119448b52a1468068108850a441840c04034224429b1a504950a448b806740342e5c9910a103012200bb4227491b065c89202142182e446840025a05061808900d0890221048b0a0c1001c180896afda8909387106a04283043820012683040a302096810a05060830112002349ee8009684c9830b3c10602740096814810186c8052a40289201080568008340a1001008140340a703100c2c80028102830b4410602008342014a05204018228180b4365c8033ae84842075a10260c04f2011b3a260ce8068185053a0830100d08103a489833a401120c049856809d1c201083a04704806840011741048238141829e1809c0041a10384448220442836818089383c31b0e04e9c0004cb53ed0b1fa0700013259a353ad430f1e0428e06086800cd5a1e38d430f4cd0fb50074e063c7c7b43a71a803c3c32646d0f9f74003236838f1f3d40e002ed071f74003176834f1f740030d2ed11806a05d111a8cb9ca2d400f3e74e0e1a783343e007230cd0f5fdfdfffdfffffffffdfffdbdedfdf7fdefddfdedffffdfffddffff7dfffdfffffdffbdfdffffffbdfdffffffbffffdffffffbffdfffdffbdfffdfd7dffffffddffddffffffffffdfffffdffffff5fffffdffffdfffdffdfffdffd
  | 2 => 0x540a7deef7cdafc88f21f76b07a867fc01616ffc02cce0165ffc03fc03fc03fc03fc025487fc03fc009ddbd41e797ffc03fc028609b8973656769948f1093d64a3fc037b1b266cb05311ef140ffc0369709617e146be878406c03c86d93188914ffc03fc0025582c0500728d20104a4c4181cc0e4036e38c29b1401122031c02800040654c700301810100100403d0150400c81000480820458a56a8b8a0ce8059ed27739d166f49ae263497d25b595a24e6920a466901a3a98c5a2b789122078656148831e05380a5f977c9deb67959df2775dd657461c997009be26f1db566bdda83694da28668d972655d8e462958575f8d7b85cd96d75999608561154a529944c4e093624d1130949d921b4589142448d0f2435109441550053ed0f723d54f0939c8e53389cdb33618d263328c223020b852ce4aa5295c9e825a88c521e07f61e6470a198c63b162050911ec3c80d202c809201c904f007700278b021800c1254d030418080182428704003011850d050808e030c040161270a8236180871618d81081401a08141820c0401a2050d00193838918267070c1e786023048521444d0193c3b52f01b379cf43090e7100418301820c04037121e03713383860a0048602108373854989388098718109840adc19308710050665b82021a700324c98518e099b7258202385c296021801726249971c6c11c0a08086344c610244
  | 3 => 0x1608931600931511131510d31500d31500931200931110d31100d31100930d00930a11530500930311130310d30111130011519510d19500d19310d19111119100d19100911711111600911519111511111500d11500911500511200911100d11100911100510d00d10d00910d00501500900d00900d0043090041150044a0da6a8540bfc002ee7fc03fc03fc03fc015f2ffc02c1354060875360e6e6887da3fc0015e6ae97330e7551662251e9ca538182cf59801bc87819e3fc03fc026f3ddcf7a337e5ff3a661e3ffc033c8bfc00a2dfb6189d96caece5079a24c637fc00fc37fc03fc03d0a7e499dc715d12255cb36d8a621083674702389a2ddebdcf150ab6d675c68e15b5a4b7282e349c84b950fffc0329605447787e46cd364f251c66d7fc03a9bcc1d1085c919b0f4fd6e9b9c5fd8e8417fc029db0f001b811d25bc57909183233e280adf3894b84c4966bfc015ea7fc02c0aab9204b664da736b33757fc02774bfc03fc03fc03fc03fc00b9562e1dc9435ac625faa44b62b8bc295c32e12b04f841683603c763fc0351aba977fc03fc03fc0376a0f59d664865d458917ad1de915103884ee2ff00ed59bb7ee3c0da871f4cdd49925cd609ccd86c8d84d07718c3d5dda7739d0fb64720cb02115f243a28aead0207792d2b7508bd88cec8ad04b151674cd2a525842695158679c29e013a7ec14931935eec213dcb7
  | 4 => 0x88af9395f2323e4e3359cad539956722ace02d10a59314da32334e3669cc63381367226ce34d9c0891951672a24e5459c0c938d927317ce42f9c4bd1957a71af4e61c8ca3b39a4a72494e26e9c6dd381ba7325ce22910a53314a2728a4648e8cb1d3963a7121444439c41f3143a72874e4848cb0a1161272c2444849c8a7381a271344e6239c8a33905a428b4c5169ca8d2151a22a34e5629c4c53818a73304e2609c2c138182733c4e45c9c4361946a328dce41b9c6373816271ac4e2589c0b13982422844450888b220964212c84e4909c6d9389b270364e6499c09338d267013ce17680aed315da72894851280a273144a6289ce5129ca251904e71c64458c80b193963271a0ce5401ca812150622a0445419ca833950672a00e5408c88338dca02b94e5728c8e53903232864050c9ca193901a3283445079ca0d3941a3203444068870d3961a32434e43e8ca7f394fa729fce43e9c87738c6670414e55a9c6b538866718cce0199c00138c0270008e67488ae9395d47308c451088a23395c272854650a9ca09194142282445051ca093941221824e2829ca0539731511331500f31500b31100f31100b30d11730d11330d00b30900f30900730519330111730111311511311500b11100b11100710d00b10d00631500e31500a21710e21600a21510e21500e21500a19500a11500e11500a11500609500931711131710d3
  | 5 => 0x1f83f07e4f89ea3bc6a0d5199322620c41883165c0b89682d05a4b09592a252c9a90c1d03a4720c01822e05c8b1152290408790e418c2682202004800093dd1c40c041819ac4c7008180400e60c4c720c0c0c18040c1401a41418040018045c00105e700000148000105c080c5c01b05c145c0c5da410005c000c1804140014001400001000140414101401a014100004000000004e140e700000d93c000c1414141671b4080000001009a8442689a00810013c0c141414180404000000049a748e7498048c7c988e767000e88e167074007c0044005c347044d4e844508c5c4434008c408c2c027f3f9fcff79779fef67b7b9feeef7dbf5def3f3f9fdbfcfeb9fcff773fd7cfebf3f9fcffcfb7dbdde7f779fede7fb79fcfe7f779fddeefd7bbcffaf3f9fcfeef7e9fdefcfb7bbf9f6f3f9febe7fb7bbddf6fbb9feee7f3fbdcfef73ff5eeef7afddcfef77e9fdeefb7e9fdeef7dbeddeef7fabbdeefd3fef77bb59fcfcfe7f7bbf4fefd3fdf5f7f5bbbdfaff5bbdddeef7ebbdeef7d3f9fd7ebfafddeee7f9f8fe7f5f3ffd5efe77bf9feaf77bfb7eafd7efb7ebe53fdbcff6f3f9fcfe7f77bf4fefb7dbeff2f975be4f7f37d9efe7f37dbefd6fbf4fe7f3f9fcfa7f2fb7d3d9c1153922a703f4e3329c24338c867340445809c04b3815e701c4457a9c03d1947e720fce0948cb2938e527027ce42a8ca551162272c44e07c
  | 6 => 0x57f803fc01a16e057288d0ffc016e2fff003325bfc016b453319a91415623760929292bce300175f024235c4872d88a31107e71e59550626f50af17d7f8028801ccfeff00095f7fc01c02d55c4ff803fc01fe00f49d7f803fc000942ff001d2c1f402e47a735a9cc829a7cdd1c92bb41d4bddc4a756ddbcd845f21f1fe00ff00770e0066ec2d5fa4312de3fc01fe0013c47f8015589fe004c4ca4c27fc01fe004e7b544901018e0158e4c1a46bfc001c76ff0066333003a53810d393f3002931408080002c3140201294842030208987150628625020020504654090210082020ce00006080101101011e24182060000b020c2001c00402160058c000009e001810d00140850000011000cb000404200140878900001060e1c103000800b28140000e08002282898000387101566a8550aa74e699520a434628c518a3146e80500a033ea744e99c732e58ca89512a2544aa9312624c498931266484919112224448990120a384738b512a1cc3185308210c188310620c41883304dfcbf07e4f85ed3ca774ea1d4ba3710e21c4b826e0dc1b83716d4d61ac3586b0d61ac3586b0d65a83506a2d25a0341670ce598331652c8190320640c858c319622c2580afb5c8b0160ab8570ae558aa8552a8150a98530a614c298532a4544a824e29a92ca504a094128a4849092520a394608c514a204448410821042084504208412804fc
  | 7 => 0x18a14eb23ed1f2905e1c088e127fc01fe00324e9e1d036e7e02137c2a70aeb8b7ba836a0f02bf4d1c3fe004b208483e32d0f37ba197c0b91dd925aedd33d8a8c441c1811fff003926ffc01d405a4612e2a7fc0053471a5e5aa6a08889c47b28b390f088147ead2b0d83438a6c0a0daff00305513d8ffe00ff000b0d405f7fe00ff0019bc1487b1cd4a26ddb843fc012058f6307f801788dfe007a259accada51fe002d2eff801092aea518d490a067fc009665b240c256ab9944b4949b26b2ff118c72f13c3eff8012db9084d9c5ec29bd40c76b84e979083fdec6f5077b16fc7bb3c5453cc5725451d57c0254e3bff004425ede0b5923ff0049ae3a1417c53ff0054b2f82892eefff000ac1ffc00d67ea8422bb7bfc0070e710a69bb65d6eb704c818c8b102b1631cceb5690f33e215f30ea02a31f1b59a29fe00b36871dc6dad29c0660aeff80168860493ae891b837fc01cf15ed38491e62c111c5a69800baee7673fe0013b3f35d390c528eb920122addd1d3d0fc5398cc83bb512a4183d92ff80342a6d765c15d7295c78cd90acf648518978504e8f7d337678f87147131da846e40808a45996b5324724139c949cf48f39df17288e3bab60fa5e929f026a24e828a7c8a9945cc8366e887c4a2c8da3209fca5f061a89110006c602b1a4f7deb09f0dd5a713ddf6075a6d3088c321f3ad188242c2819f2cffc0028750b9
  | 8 => 0x95e57943f1dc3f3e4f97c4f97c4f93e5e9ea5e9ea4f97a5f17a128caf28329a00ce81388caea8036a043e81b080a0a22ac80a0232a480a3232a088a2232079ca1a7286a0a1a821da0a9e811ba0a668040a0656802fa0046802ba008e8017a04d232b4a062a328ba0efa819fa041282e70222a00c72a01a00c42a32621c32a22a01422e61201c22a02a01422a01a00a73442a01a72e22201272e22200a72e21a01272e21a00a72a62221a72a61a01272a21a01272a21a00a72a01a01272a01a00a72661a01272261a01271422a00a32a01a00a22e22200a22a32222222a22200a22a02a01222a01a01222a01a00a22201a01221a01a01221a01a00a02e62201202a21a013e4323e800003c714290c92168dad84895ee5ff2c09fe00afa4409fffc0110b9ff007c5b39ac7c8f300c3c9bbbfc01fe00ff007f803fc018627ff004e08d5a5dbc22ff004842d9d1c9e914f61f89e2ab07e8699d2a3fda9d6998f6f2d43d48d039285d08ff001cccd56a3fe007860d6603fc00dcaa8130f22846c27fe009433da5cbfc01fe00919e7f8031a3c795eff000705acc3eaf8bf89dec377ce7fc407b70d54c6d3d5caf2ddbc317aacfe0274c811adc8c854ab200d69b7ad5053907fc736ccb0e757de6b853278b960497d5daf424e7e94a4203014b4e6448935905f959bbf306db6e293c35380106b61cd19642c5c7f579f42da22874d07d4
  | 9 => 0x68e7295ff8028515a68805d930ff00a079751d68cff010a83fc07f804015fe01b0965c59b4e66f3fc04029c28e3e5eaa4ab22f955e2e8200ccb54e3a78c5d86ff80f029fe017411bb6ff01fe000876f007c4c4b0e842ff80323f8d10fa5d209ff00eb07fc0092c0b81b6dcac269a1880e3cca24b77914467a4d1f926f030727bef4c03171b3f1f48bb7616d2d1c31aa664129c38ff018ebc79dff80ff007cfc6443215eb20039d2301d40845c62b8b15844310011020408102040810204084c183240810222040810204081020408102040810204854da6130e000d4000078753c7d1df276d5b56d6b5cd6b5e96b5e96b5f16e5b
  | _ => 0

def compactCount119 (k : Nat) : Nat := match k with
  | 9 => 1
  | 8 => 17
  | 7 => 111
  | 6 => 198
  | 5 => 38
  | _ => 0

def compactPath119 (k : Nat) (i : Nat) : Nat := match k with
  | 9 => 0
  | 8 => readCompactBits compactWords119 (20 + 12*i) 12
  | 7 => let v := readCompactBits compactWords119 (2159 + 16*i) 16
    (readCompactBits compactWords119 (1991 + 12*(v >>> 12)) 12) ||| ((v &&& 4095) <<< 12)
  | 6 => let v := readCompactBits compactWords119 (17182 + 19*i) 19
    (readCompactBits compactWords119 (15382 + 24*(v >>> 12)) 24) ||| ((v &&& 4095) <<< 24)
  | 5 => let v := readCompactBits compactWords119 (35975 + 18*i) 18
    (readCompactBits compactWords119 (34787 + 36*(v >>> 12)) 36) ||| ((v &&& 4095) <<< 36)
  | _ => 0

def compactLive119 (k : Nat) (i : Nat) : Nat := match k with
  | 9 => readCompactBits compactWords119 (0 + 6*i) 6
  | 8 => readCompactBits compactWords119 (224 + 7*i) 7
  | 7 => readCompactBits compactWords119 (3935 + 8*i) 8
  | 6 => readCompactBits compactWords119 (20944 + 9*i) 9
  | 5 => readCompactBits compactWords119 (36659 + 10*i) 10
  | _ => 0

def compactPoolIDs119 (k : Nat) (i : Nat) : List Nat := match k with
  | 9 => let v := readCompactBits compactWords119 (14 + 6*i) 6
    let n := v >>> 3
    let bits := readCompactBits compactWords119 (6 + 2*(v &&& 7)) (2*n)
    compactIDsFromBits bits 2 n
  | 8 => let v := readCompactBits compactWords119 (1253 + 12*i) 12
    let n := v >>> 8
    let bits := readCompactBits compactWords119 (343 + 5*(v &&& 255)) (5*n)
    compactIDsFromBits bits 5 n
  | 7 => let v := readCompactBits compactWords119 (9506 + 14*i) 14
    let n := v >>> 10
    let bits := readCompactBits compactWords119 (4823 + 7*(v &&& 1023)) (7*n)
    compactIDsFromBits bits 7 n
  | 6 => let v := readCompactBits compactWords119 (24094 + 11*i) 11
    let n := v >>> 8
    let bits := readCompactBits compactWords119 (22726 + 8*(v &&& 255)) (8*n)
    compactIDsFromBits bits 8 n
  | 5 => let v := readCompactBits compactWords119 (37111 + 7*i) 7
    let n := v >>> 4
    let bits := readCompactBits compactWords119 (37039 + 9*(v &&& 15)) (9*n)
    compactIDsFromBits bits 9 n
  | _ => []

def compactBucket119 (k : Nat) (i : Nat) : List Nat := match k with
  | 8 => let d := readCompactBits compactWords119 (1457 + 3*(i % 10)) 3
    let off := ((i/10 + d) % 36)
    let v := readCompactBits compactWords119 (1487 + 14*off) 14
    if v >>> 6 == (i/104729)%251 then [v &&& 63] else []
  | 7 => let d := readCompactBits compactWords119 (11060 + 6*(i % 67)) 6
    let off := ((i/67 + d) % 245)
    let v := readCompactBits compactWords119 (11462 + 16*off) 16
    if v >>> 8 == (i/104729)%251 then [v &&& 255] else []
  | 6 => let d := readCompactBits compactWords119 (26272 + 7*(i % 126)) 7
    let off := ((i/126 + d) % 449)
    let v := readCompactBits compactWords119 (27154 + 17*off) 17
    if v >>> 9 == (i/104729)%251 then [v &&& 511] else []
  | 5 => let d := readCompactBits compactWords119 (37377 + 5*(i % 24)) 5
    let off := ((i/24 + d) % 88)
    let v := readCompactBits compactWords119 (37497 + 15*off) 15
    if v >>> 7 == (i/104729)%251 then [v &&& 127] else []
  | _ => []
theorem compactHalves {test : Nat → Bool} {start n : Nat}
    (first : chartBlock test start (n / 2) = true)
    (last : chartBlock test (start + n / 2) (n - n / 2) = true) :
    chartBlock test start n = true := by
  have eq : n / 2 + (n - n / 2) = n := by omega
  simpa only [eq] using chartBlock_join first last

def grid21 : CompactGrid := (21, 3, samplesP21, samplesQ21)
def tab21 : CompactTable := (compactCount21, compactPath21, compactLive21, compactPoolIDs21, compactBucket21)
def check21 (k : Nat) := compactNode grid21 tab21 compactDomains21 compactPerms21 k
def sliceSpecs21 : List SliceSpec := []
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem domains21 : ∀ d ∈ compactDomains21, Slice true (vars 21) (graphGoal 21) d.1 d.2 := by
  apply compactDomains_valid (earlier := []) (specs := sliceSpecs21)
  · simp
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem pairs21 : properPairs (graphGoal 21) (asRow samplesP21) (asRow samplesQ21) :=
  compactPairs (g := grid21) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem autos21 : ∀ p ∈ compactPerms21, autoOK (graphGoal 21) (p.map swapRows).reverse = true :=
  compactAutos_valid (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c21k3p0 : chartBlock (check21 3) 0 1 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev21k3 : chartBlock (check21 3) 0 1 = true :=
  c21k3p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem excluded21 : Impossible true (graphGoal 21) 3 (vars 21).toFinset := by
  apply compactRoot (g := grid21) (t := tab21) (dom := compactDomains21) (perms := compactPerms21) pairs21 domains21 autos21
  · intro k hk
    change k ≤ 3 at hk
    interval_cases k
    · rfl
    · rfl
    · rfl
    · exact lev21k3
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound21 : Lower true (vars 21) (graphGoal 21) 4 :=
  plain_low (hints := 2) (by decide +kernel) excluded21
def grid23 : CompactGrid := (23, 4, samplesP23, samplesQ23)
def tab23 : CompactTable := (compactCount23, compactPath23, compactLive23, compactPoolIDs23, compactBucket23)
def check23 (k : Nat) := compactNode grid23 tab23 compactDomains23 compactPerms23 k
def sliceSpecs23 : List SliceSpec := [(2, 0, 21, 0, 0, 4, 4)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem domains23 : ∀ d ∈ compactDomains23, Slice true (vars 23) (graphGoal 23) d.1 d.2 := by
  apply compactDomains_valid (earlier := [(21, 4)]) (specs := sliceSpecs23)
  · intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl
    · exact bound21
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem pairs23 : properPairs (graphGoal 23) (asRow samplesP23) (asRow samplesQ23) :=
  compactPairs (g := grid23) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem autos23 : ∀ p ∈ compactPerms23, autoOK (graphGoal 23) (p.map swapRows).reverse = true :=
  compactAutos_valid (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c23k4p0 : chartBlock (check23 4) 0 1 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev23k4 : chartBlock (check23 4) 0 1 = true :=
  c23k4p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem excluded23 : Impossible true (graphGoal 23) 4 (vars 23).toFinset := by
  apply compactRoot (g := grid23) (t := tab23) (dom := compactDomains23) (perms := compactPerms23) pairs23 domains23 autos23
  · intro k hk
    change k ≤ 4 at hk
    interval_cases k
    · rfl
    · rfl
    · rfl
    · rfl
    · exact lev23k4
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound23 : Lower true (vars 23) (graphGoal 23) 5 :=
  plain_low (hints := 66) (by decide +kernel) excluded23
def grid27 : CompactGrid := (27, 3, samplesP27, samplesQ27)
def tab27 : CompactTable := (compactCount27, compactPath27, compactLive27, compactPoolIDs27, compactBucket27)
def check27 (k : Nat) := compactNode grid27 tab27 compactDomains27 compactPerms27 k
def sliceSpecs27 : List SliceSpec := []
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem domains27 : ∀ d ∈ compactDomains27, Slice true (vars 27) (graphGoal 27) d.1 d.2 := by
  apply compactDomains_valid (earlier := []) (specs := sliceSpecs27)
  · simp
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem pairs27 : properPairs (graphGoal 27) (asRow samplesP27) (asRow samplesQ27) :=
  compactPairs (g := grid27) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem autos27 : ∀ p ∈ compactPerms27, autoOK (graphGoal 27) (p.map swapRows).reverse = true :=
  compactAutos_valid (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c27k3p0 : chartBlock (check27 3) 0 1 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev27k3 : chartBlock (check27 3) 0 1 = true :=
  c27k3p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem excluded27 : Impossible true (graphGoal 27) 3 (vars 27).toFinset := by
  apply compactRoot (g := grid27) (t := tab27) (dom := compactDomains27) (perms := compactPerms27) pairs27 domains27 autos27
  · intro k hk
    change k ≤ 3 at hk
    interval_cases k
    · rfl
    · rfl
    · rfl
    · exact lev27k3
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound27 : Lower true (vars 27) (graphGoal 27) 4 :=
  plain_low (hints := 4148) (by decide +kernel) excluded27
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound30 : Lower true (vars 30) (graphGoal 30) 4 :=
  carry_of (old := 30) (rep := 27) (swaps := [32]) (by decide +kernel) bound27
def grid31 : CompactGrid := (31, 6, samplesP31, samplesQ31)
def tab31 : CompactTable := (compactCount31, compactPath31, compactLive31, compactPoolIDs31, compactBucket31)
def check31 (k : Nat) := compactNode grid31 tab31 compactDomains31 compactPerms31 k
def sliceSpecs31 : List SliceSpec := [(8, 0, 23, 0, 0, 5, 5), (0, 8, 21, 2, 240, 5, 4), (1, 0, 30, 0, 0, 4, 4), (4, 0, 27, 0, 0, 4, 4), (2, 8, 21, 0, 0, 4, 4)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem domains31 : ∀ d ∈ compactDomains31, Slice true (vars 31) (graphGoal 31) d.1 d.2 := by
  apply compactDomains_valid (earlier := [(23, 5), (21, 4), (30, 4), (27, 4)]) (specs := sliceSpecs31)
  · intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl
    · exact bound23
    · exact bound21
    · exact bound30
    · exact bound27
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem pairs31 : properPairs (graphGoal 31) (asRow samplesP31) (asRow samplesQ31) :=
  compactPairs (g := grid31) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem autos31 : ∀ p ∈ compactPerms31, autoOK (graphGoal 31) (p.map swapRows).reverse = true :=
  compactAutos_valid (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c31k4p0 : chartBlock (check31 4) 0 1 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev31k4 : chartBlock (check31 4) 0 1 = true :=
  c31k4p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c31k5p0 : chartBlock (check31 5) 0 3 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev31k5 : chartBlock (check31 5) 0 3 = true :=
  c31k5p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c31k6p0 : chartBlock (check31 6) 0 1 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev31k6 : chartBlock (check31 6) 0 1 = true :=
  c31k6p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem excluded31 : Impossible true (graphGoal 31) 6 (vars 31).toFinset := by
  apply compactRoot (g := grid31) (t := tab31) (dom := compactDomains31) (perms := compactPerms31) pairs31 domains31 autos31
  · intro k hk
    change k ≤ 6 at hk
    interval_cases k
    · rfl
    · rfl
    · rfl
    · rfl
    · exact lev31k4
    · exact lev31k5
    · exact lev31k6
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound31 : Lower true (vars 31) (graphGoal 31) 7 :=
  plain_low (hints := 4146) (by decide +kernel) excluded31
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound39 : Lower true (vars 39) (graphGoal 39) 4 :=
  carry_of (old := 39) (rep := 27) (swaps := [16, 50, 84]) (by decide +kernel) bound27
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound42 : Lower true (vars 42) (graphGoal 42) 4 :=
  carry_of (old := 42) (rep := 21) (swaps := [16, 50, 84]) (by decide +kernel) bound21
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound43 : Lower true (vars 43) (graphGoal 43) 5 :=
  carry_of (old := 43) (rep := 23) (swaps := [16, 50, 84]) (by decide +kernel) bound23
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound45 : Lower true (vars 45) (graphGoal 45) 4 :=
  carry_of (old := 45) (rep := 27) (swaps := [16, 50, 49, 84]) (by decide +kernel) bound27
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound47 : Lower true (vars 47) (graphGoal 47) 7 :=
  carry_of (old := 47) (rep := 31) (swaps := [16, 50, 84]) (by decide +kernel) bound31
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound53 : Lower true (vars 53) (graphGoal 53) 5 :=
  carry_of (old := 53) (rep := 23) (swaps := [64, 81]) (by decide +kernel) bound23
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound54 : Lower true (vars 54) (graphGoal 54) 4 :=
  carry_of (old := 54) (rep := 27) (swaps := [32, 83]) (by decide +kernel) bound27
def grid55 : CompactGrid := (55, 5, samplesP55, samplesQ55)
def tab55 : CompactTable := (compactCount55, compactPath55, compactLive55, compactPoolIDs55, compactBucket55)
def check55 (k : Nat) := compactNode grid55 tab55 compactDomains55 compactPerms55 k
def sliceSpecs55 : List SliceSpec := [(2, 0, 53, 0, 0, 5, 5)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem domains55 : ∀ d ∈ compactDomains55, Slice true (vars 55) (graphGoal 55) d.1 d.2 := by
  apply compactDomains_valid (earlier := [(53, 5)]) (specs := sliceSpecs55)
  · intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl
    · exact bound53
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem pairs55 : properPairs (graphGoal 55) (asRow samplesP55) (asRow samplesQ55) :=
  compactPairs (g := grid55) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem autos55 : ∀ p ∈ compactPerms55, autoOK (graphGoal 55) (p.map swapRows).reverse = true :=
  compactAutos_valid (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c55k5p0 : chartBlock (check55 5) 0 1 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev55k5 : chartBlock (check55 5) 0 1 = true :=
  c55k5p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem excluded55 : Impossible true (graphGoal 55) 5 (vars 55).toFinset := by
  apply compactRoot (g := grid55) (t := tab55) (dom := compactDomains55) (perms := compactPerms55) pairs55 domains55 autos55
  · intro k hk
    change k ≤ 5 at hk
    interval_cases k
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · exact lev55k5
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound55 : Lower true (vars 55) (graphGoal 55) 6 :=
  plain_low (hints := 66) (by decide +kernel) excluded55
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound58 : Lower true (vars 58) (graphGoal 58) 5 :=
  carry_of (old := 58) (rep := 23) (swaps := [65, 48, 82]) (by decide +kernel) bound23
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound59 : Lower true (vars 59) (graphGoal 59) 6 :=
  carry_of (old := 59) (rep := 55) (swaps := [16, 50, 84]) (by decide +kernel) bound55
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound61 : Lower true (vars 61) (graphGoal 61) 7 :=
  carry_of (old := 61) (rep := 31) (swaps := [64, 81]) (by decide +kernel) bound31
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound62 : Lower true (vars 62) (graphGoal 62) 7 :=
  carry_of (old := 62) (rep := 31) (swaps := [65, 50, 80]) (by decide +kernel) bound31
def grid63 : CompactGrid := (63, 8, samplesP63, samplesQ63)
def tab63 : CompactTable := (compactCount63, compactPath63, compactLive63, compactPoolIDs63, compactBucket63)
def check63 (k : Nat) := compactNode grid63 tab63 compactDomains63 compactPerms63 k
def sliceSpecs63 : List SliceSpec := [(1, 0, 62, 0, 0, 7, 7), (2, 0, 61, 0, 0, 7, 7), (16, 0, 47, 0, 0, 7, 7), (32, 0, 31, 0, 0, 7, 7), (4, 0, 59, 0, 0, 6, 6), (0, 4, 42, 17, 983055, 6, 4)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem domains63 : ∀ d ∈ compactDomains63, Slice true (vars 63) (graphGoal 63) d.1 d.2 := by
  apply compactDomains_valid (earlier := [(62, 7), (61, 7), (47, 7), (31, 7), (59, 6), (42, 4)]) (specs := sliceSpecs63)
  · intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl
    · exact bound62
    · exact bound61
    · exact bound47
    · exact bound31
    · exact bound59
    · exact bound42
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem pairs63 : properPairs (graphGoal 63) (asRow samplesP63) (asRow samplesQ63) :=
  compactPairs (g := grid63) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem autos63 : ∀ p ∈ compactPerms63, autoOK (graphGoal 63) (p.map swapRows).reverse = true :=
  compactAutos_valid (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c63k8p0 : chartBlock (check63 8) 0 1 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev63k8 : chartBlock (check63 8) 0 1 = true :=
  c63k8p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem excluded63 : Impossible true (graphGoal 63) 8 (vars 63).toFinset := by
  apply compactRoot (g := grid63) (t := tab63) (dom := compactDomains63) (perms := compactPerms63) pairs63 domains63 autos63
  · intro k hk
    change k ≤ 8 at hk
    interval_cases k
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · exact lev63k8
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound63 : Lower true (vars 63) (graphGoal 63) 9 :=
  plain_low (hints := 4146) (by decide +kernel) excluded63
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound69 : Lower true (vars 69) (graphGoal 69) 4 :=
  carry_of (old := 69) (rep := 21) (swaps := [100]) (by decide +kernel) bound21
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound75 : Lower true (vars 75) (graphGoal 75) 4 :=
  carry_of (old := 75) (rep := 27) (swaps := [49, 100]) (by decide +kernel) bound27
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound77 : Lower true (vars 77) (graphGoal 77) 5 :=
  carry_of (old := 77) (rep := 23) (swaps := [49, 100]) (by decide +kernel) bound23
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound78 : Lower true (vars 78) (graphGoal 78) 4 :=
  carry_of (old := 78) (rep := 27) (swaps := [49, 32, 100]) (by decide +kernel) bound27
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound79 : Lower true (vars 79) (graphGoal 79) 7 :=
  carry_of (old := 79) (rep := 31) (swaps := [49, 100]) (by decide +kernel) bound31
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound83 : Lower true (vars 83) (graphGoal 83) 4 :=
  carry_of (old := 83) (rep := 27) (swaps := [16, 99]) (by decide +kernel) bound27
def grid85 : CompactGrid := (85, 4, samplesP85, samplesQ85)
def tab85 : CompactTable := (compactCount85, compactPath85, compactLive85, compactPoolIDs85, compactBucket85)
def check85 (k : Nat) := compactNode grid85 tab85 compactDomains85 compactPerms85 k
def sliceSpecs85 : List SliceSpec := [(16, 0, 69, 0, 0, 4, 4)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem domains85 : ∀ d ∈ compactDomains85, Slice true (vars 85) (graphGoal 85) d.1 d.2 := by
  apply compactDomains_valid (earlier := [(69, 4)]) (specs := sliceSpecs85)
  · intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl
    · exact bound69
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem pairs85 : properPairs (graphGoal 85) (asRow samplesP85) (asRow samplesQ85) :=
  compactPairs (g := grid85) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem autos85 : ∀ p ∈ compactPerms85, autoOK (graphGoal 85) (p.map swapRows).reverse = true :=
  compactAutos_valid (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c85k4p0 : chartBlock (check85 4) 0 1 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev85k4 : chartBlock (check85 4) 0 1 = true :=
  c85k4p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem excluded85 : Impossible true (graphGoal 85) 4 (vars 85).toFinset := by
  apply compactRoot (g := grid85) (t := tab85) (dom := compactDomains85) (perms := compactPerms85) pairs85 domains85 autos85
  · intro k hk
    change k ≤ 4 at hk
    interval_cases k
    · rfl
    · rfl
    · rfl
    · rfl
    · exact lev85k4
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound85 : Lower true (vars 85) (graphGoal 85) 5 :=
  plain_low (hints := 2) (by decide +kernel) excluded85
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound86 : Lower true (vars 86) (graphGoal 86) 4 :=
  carry_of (old := 86) (rep := 27) (swaps := [16, 32, 99]) (by decide +kernel) bound27
def grid87 : CompactGrid := (87, 6, samplesP87, samplesQ87)
def tab87 : CompactTable := (compactCount87, compactPath87, compactLive87, compactPoolIDs87, compactBucket87)
def check87 (k : Nat) := compactNode grid87 tab87 compactDomains87 compactPerms87 k
def sliceSpecs87 : List SliceSpec := [(2, 0, 85, 0, 0, 5, 5), (64, 0, 23, 0, 0, 5, 5), (0, 2, 69, 16, 983040, 5, 4), (1, 0, 86, 0, 0, 4, 4), (4, 0, 83, 0, 0, 4, 4), (16, 2, 69, 0, 0, 4, 4)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem domains87 : ∀ d ∈ compactDomains87, Slice true (vars 87) (graphGoal 87) d.1 d.2 := by
  apply compactDomains_valid (earlier := [(85, 5), (23, 5), (69, 4), (86, 4), (83, 4)]) (specs := sliceSpecs87)
  · intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl | rfl
    · exact bound85
    · exact bound23
    · exact bound69
    · exact bound86
    · exact bound83
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem pairs87 : properPairs (graphGoal 87) (asRow samplesP87) (asRow samplesQ87) :=
  compactPairs (g := grid87) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem autos87 : ∀ p ∈ compactPerms87, autoOK (graphGoal 87) (p.map swapRows).reverse = true :=
  compactAutos_valid (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c87k4p0 : chartBlock (check87 4) 0 1 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev87k4 : chartBlock (check87 4) 0 1 = true :=
  c87k4p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c87k5p0 : chartBlock (check87 5) 0 1 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev87k5 : chartBlock (check87 5) 0 1 = true :=
  c87k5p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c87k6p0 : chartBlock (check87 6) 0 1 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev87k6 : chartBlock (check87 6) 0 1 = true :=
  c87k6p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem excluded87 : Impossible true (graphGoal 87) 6 (vars 87).toFinset := by
  apply compactRoot (g := grid87) (t := tab87) (dom := compactDomains87) (perms := compactPerms87) pairs87 domains87 autos87
  · intro k hk
    change k ≤ 6 at hk
    interval_cases k
    · rfl
    · rfl
    · rfl
    · rfl
    · exact lev87k4
    · exact lev87k5
    · exact lev87k6
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound87 : Lower true (vars 87) (graphGoal 87) 7 :=
  plain_low (hints := 66) (by decide +kernel) excluded87
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound89 : Lower true (vars 89) (graphGoal 89) 4 :=
  carry_of (old := 89) (rep := 27) (swaps := [64, 97]) (by decide +kernel) bound27
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound90 : Lower true (vars 90) (graphGoal 90) 4 :=
  carry_of (old := 90) (rep := 27) (swaps := [67, 96]) (by decide +kernel) bound27
def grid91 : CompactGrid := (91, 6, samplesP91, samplesQ91)
def tab91 : CompactTable := (compactCount91, compactPath91, compactLive91, compactPoolIDs91, compactBucket91)
def check91 (k : Nat) := compactNode grid91 tab91 compactDomains91 compactPerms91 k
def sliceSpecs91 : List SliceSpec := [(1, 0, 90, 0, 0, 4, 4), (2, 0, 89, 0, 0, 4, 4), (8, 0, 83, 0, 0, 4, 4), (16, 0, 75, 0, 0, 4, 4), (64, 0, 27, 0, 0, 4, 4)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem domains91 : ∀ d ∈ compactDomains91, Slice true (vars 91) (graphGoal 91) d.1 d.2 := by
  apply compactDomains_valid (earlier := [(90, 4), (89, 4), (83, 4), (75, 4), (27, 4)]) (specs := sliceSpecs91)
  · intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl | rfl
    · exact bound90
    · exact bound89
    · exact bound83
    · exact bound75
    · exact bound27
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem pairs91 : properPairs (graphGoal 91) (asRow samplesP91) (asRow samplesQ91) :=
  compactPairs (g := grid91) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem autos91 : ∀ p ∈ compactPerms91, autoOK (graphGoal 91) (p.map swapRows).reverse = true :=
  compactAutos_valid (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c91k4p0 : chartBlock (check91 4) 0 1 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev91k4 : chartBlock (check91 4) 0 1 = true :=
  c91k4p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c91k5p0 : chartBlock (check91 5) 0 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev91k5 : chartBlock (check91 5) 0 2 = true :=
  c91k5p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c91k6p0 : chartBlock (check91 6) 0 1 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev91k6 : chartBlock (check91 6) 0 1 = true :=
  c91k6p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem excluded91 : Impossible true (graphGoal 91) 6 (vars 91).toFinset := by
  apply compactRoot (g := grid91) (t := tab91) (dom := compactDomains91) (perms := compactPerms91) pairs91 domains91 autos91
  · intro k hk
    change k ≤ 6 at hk
    interval_cases k
    · rfl
    · rfl
    · rfl
    · rfl
    · exact lev91k4
    · exact lev91k5
    · exact lev91k6
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound91 : Lower true (vars 91) (graphGoal 91) 7 :=
  plain_low (hints := 4148) (by decide +kernel) excluded91
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound92 : Lower true (vars 92) (graphGoal 92) 4 :=
  carry_of (old := 92) (rep := 27) (swaps := [66, 64, 97]) (by decide +kernel) bound27
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound93 : Lower true (vars 93) (graphGoal 93) 7 :=
  carry_of (old := 93) (rep := 87) (swaps := [49, 100]) (by decide +kernel) bound87
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound94 : Lower true (vars 94) (graphGoal 94) 7 :=
  carry_of (old := 94) (rep := 91) (swaps := [32]) (by decide +kernel) bound91
def grid95 : CompactGrid := (95, 9, samplesP95, samplesQ95)
def tab95 : CompactTable := (compactCount95, compactPath95, compactLive95, compactPoolIDs95, compactBucket95)
def check95 (k : Nat) := compactNode grid95 tab95 compactDomains95 compactPerms95 k
def sliceSpecs95 : List SliceSpec := [(1, 0, 94, 0, 0, 7, 7), (2, 0, 93, 0, 0, 7, 7), (4, 0, 91, 0, 0, 7, 7), (8, 0, 87, 0, 0, 7, 7), (16, 0, 79, 0, 0, 7, 7), (64, 0, 31, 0, 0, 7, 7), (0, 2, 69, 24, 1044480, 6, 4), (0, 8, 21, 66, 251658480, 6, 4), (10, 0, 85, 0, 0, 5, 5), (18, 0, 77, 0, 0, 5, 5), (72, 0, 23, 0, 0, 5, 5), (2, 8, 21, 64, 251658240, 5, 4), (16, 2, 69, 8, 61440, 5, 4), (64, 8, 21, 2, 240, 5, 4), (3, 0, 92, 0, 0, 4, 4), (5, 0, 90, 0, 0, 4, 4), (6, 0, 89, 0, 0, 4, 4), (9, 0, 86, 0, 0, 4, 4), (17, 0, 78, 0, 0, 4, 4), (20, 0, 75, 0, 0, 4, 4), (65, 0, 30, 0, 0, 4, 4), (68, 0, 27, 0, 0, 4, 4), (24, 2, 69, 0, 0, 4, 4)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem domains95 : ∀ d ∈ compactDomains95, Slice true (vars 95) (graphGoal 95) d.1 d.2 := by
  apply compactDomains_valid (earlier := [(94, 7), (93, 7), (91, 7), (87, 7), (79, 7), (31, 7), (69, 4), (21, 4), (85, 5), (77, 5), (23, 5), (92, 4), (90, 4), (89, 4), (86, 4), (78, 4), (75, 4), (30, 4), (27, 4)]) (specs := sliceSpecs95)
  · intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact bound94
    · exact bound93
    · exact bound91
    · exact bound87
    · exact bound79
    · exact bound31
    · exact bound69
    · exact bound21
    · exact bound85
    · exact bound77
    · exact bound23
    · exact bound92
    · exact bound90
    · exact bound89
    · exact bound86
    · exact bound78
    · exact bound75
    · exact bound30
    · exact bound27
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem pairs95 : properPairs (graphGoal 95) (asRow samplesP95) (asRow samplesQ95) :=
  compactPairs (g := grid95) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem autos95 : ∀ p ∈ compactPerms95, autoOK (graphGoal 95) (p.map swapRows).reverse = true :=
  compactAutos_valid (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c95k5p0 : chartBlock (check95 5) 0 5 = true := by
  iterate 1 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev95k5 : chartBlock (check95 5) 0 5 = true :=
  c95k5p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c95k6p0 : chartBlock (check95 6) 0 32 = true := by
  iterate 4 (all_goals apply compactHalves)
  all_goals decide +kernel
theorem c95k6p1 : chartBlock (check95 6) 32 1 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev95k6 : chartBlock (check95 6) 0 33 = true :=
  (chartBlock_join (a := 32) (b := 1) c95k6p0 c95k6p1)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c95k7p0 : chartBlock (check95 7) 0 26 = true := by
  iterate 4 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev95k7 : chartBlock (check95 7) 0 26 = true :=
  c95k7p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c95k8p0 : chartBlock (check95 8) 0 7 = true := by
  iterate 2 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev95k8 : chartBlock (check95 8) 0 7 = true :=
  c95k8p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c95k9p0 : chartBlock (check95 9) 0 1 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev95k9 : chartBlock (check95 9) 0 1 = true :=
  c95k9p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem excluded95 : Impossible true (graphGoal 95) 9 (vars 95).toFinset := by
  apply compactRoot (g := grid95) (t := tab95) (dom := compactDomains95) (perms := compactPerms95) pairs95 domains95 autos95
  · intro k hk
    change k ≤ 9 at hk
    interval_cases k
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · exact lev95k5
    · exact lev95k6
    · exact lev95k7
    · exact lev95k8
    · exact lev95k9
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound95 : Lower true (vars 95) (graphGoal 95) 10 :=
  plain_low (hints := 4146) (by decide +kernel) excluded95
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound97 : Lower true (vars 97) (graphGoal 97) 4 :=
  carry_of (old := 97) (rep := 21) (swaps := [82, 100]) (by decide +kernel) bound21
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound99 : Lower true (vars 99) (graphGoal 99) 5 :=
  carry_of (old := 99) (rep := 23) (swaps := [84, 98, 66]) (by decide +kernel) bound23
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound101 : Lower true (vars 101) (graphGoal 101) 5 :=
  carry_of (old := 101) (rep := 85) (swaps := [98, 84]) (by decide +kernel) bound85
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound102 : Lower true (vars 102) (graphGoal 102) 4 :=
  carry_of (old := 102) (rep := 27) (swaps := [49, 32, 83, 100]) (by decide +kernel) bound27
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound103 : Lower true (vars 103) (graphGoal 103) 7 :=
  carry_of (old := 103) (rep := 87) (swaps := [98, 84]) (by decide +kernel) bound87
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound104 : Lower true (vars 104) (graphGoal 104) 4 :=
  carry_of (old := 104) (rep := 21) (swaps := [48, 82, 100]) (by decide +kernel) bound21
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound105 : Lower true (vars 105) (graphGoal 105) 5 :=
  carry_of (old := 105) (rep := 85) (swaps := [64, 99, 84, 98]) (by decide +kernel) bound85
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound106 : Lower true (vars 106) (graphGoal 106) 5 :=
  carry_of (old := 106) (rep := 85) (swaps := [65, 50, 80, 64]) (by decide +kernel) bound85
def grid107 : CompactGrid := (107, 6, samplesP107, samplesQ107)
def tab107 : CompactTable := (compactCount107, compactPath107, compactLive107, compactPoolIDs107, compactBucket107)
def check107 (k : Nat) := compactNode grid107 tab107 compactDomains107 compactPerms107 k
def sliceSpecs107 : List SliceSpec := [(1, 0, 106, 0, 0, 5, 5), (2, 0, 105, 0, 0, 5, 5), (8, 0, 99, 0, 0, 5, 5), (64, 0, 43, 0, 0, 5, 5)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem domains107 : ∀ d ∈ compactDomains107, Slice true (vars 107) (graphGoal 107) d.1 d.2 := by
  apply compactDomains_valid (earlier := [(106, 5), (105, 5), (99, 5), (43, 5)]) (specs := sliceSpecs107)
  · intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl
    · exact bound106
    · exact bound105
    · exact bound99
    · exact bound43
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem pairs107 : properPairs (graphGoal 107) (asRow samplesP107) (asRow samplesQ107) :=
  compactPairs (g := grid107) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem autos107 : ∀ p ∈ compactPerms107, autoOK (graphGoal 107) (p.map swapRows).reverse = true :=
  compactAutos_valid (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c107k6p0 : chartBlock (check107 6) 0 1 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev107k6 : chartBlock (check107 6) 0 1 = true :=
  c107k6p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem excluded107 : Impossible true (graphGoal 107) 6 (vars 107).toFinset := by
  apply compactRoot (g := grid107) (t := tab107) (dom := compactDomains107) (perms := compactPerms107) pairs107 domains107 autos107
  · intro k hk
    change k ≤ 6 at hk
    interval_cases k
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · exact lev107k6
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound107 : Lower true (vars 107) (graphGoal 107) 7 :=
  plain_low (hints := 4149) (by decide +kernel) excluded107
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound108 : Lower true (vars 108) (graphGoal 108) 5 :=
  carry_of (old := 108) (rep := 23) (swaps := [33, 48, 81, 100]) (by decide +kernel) bound23
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound109 : Lower true (vars 109) (graphGoal 109) 7 :=
  carry_of (old := 109) (rep := 107) (swaps := [48, 33, 101]) (by decide +kernel) bound107
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound110 : Lower true (vars 110) (graphGoal 110) 7 :=
  carry_of (old := 110) (rep := 87) (swaps := [97, 98, 48, 101, 100]) (by decide +kernel) bound87
def grid111 : CompactGrid := (111, 9, samplesP111, samplesQ111)
def tab111 : CompactTable := (compactCount111, compactPath111, compactLive111, compactPoolIDs111, compactBucket111)
def check111 (k : Nat) := compactNode grid111 tab111 compactDomains111 compactPerms111 k
def sliceSpecs111 : List SliceSpec := [(1, 0, 110, 0, 0, 7, 7), (2, 0, 109, 0, 0, 7, 7), (4, 0, 107, 0, 0, 7, 7), (8, 0, 103, 0, 0, 7, 7), (32, 0, 79, 0, 0, 7, 7), (64, 0, 47, 0, 0, 7, 7), (0, 2, 69, 40, 15790080, 6, 4), (0, 4, 42, 65, 251658255, 6, 4), (3, 0, 108, 0, 0, 5, 5), (5, 0, 106, 0, 0, 5, 5), (34, 0, 77, 0, 0, 5, 5), (1, 4, 42, 64, 251658240, 5, 4), (8, 2, 69, 32, 15728640, 5, 4), (32, 2, 69, 8, 61440, 5, 4), (64, 4, 42, 1, 15, 5, 4), (9, 0, 102, 0, 0, 4, 4), (33, 0, 78, 0, 0, 4, 4), (72, 0, 39, 0, 0, 4, 4), (7, 0, 104, 0, 0, 4, 4), (40, 2, 69, 0, 0, 4, 4), (42, 0, 69, 0, 0, 4, 4), (65, 4, 42, 0, 0, 4, 4), (69, 0, 42, 0, 0, 4, 4)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem domains111 : ∀ d ∈ compactDomains111, Slice true (vars 111) (graphGoal 111) d.1 d.2 := by
  apply compactDomains_valid (earlier := [(110, 7), (109, 7), (107, 7), (103, 7), (79, 7), (47, 7), (69, 4), (42, 4), (108, 5), (106, 5), (77, 5), (102, 4), (78, 4), (39, 4), (104, 4)]) (specs := sliceSpecs111)
  · intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact bound110
    · exact bound109
    · exact bound107
    · exact bound103
    · exact bound79
    · exact bound47
    · exact bound69
    · exact bound42
    · exact bound108
    · exact bound106
    · exact bound77
    · exact bound102
    · exact bound78
    · exact bound39
    · exact bound104
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem pairs111 : properPairs (graphGoal 111) (asRow samplesP111) (asRow samplesQ111) :=
  compactPairs (g := grid111) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem autos111 : ∀ p ∈ compactPerms111, autoOK (graphGoal 111) (p.map swapRows).reverse = true :=
  compactAutos_valid (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c111k5p0 : chartBlock (check111 5) 0 7 = true := by
  iterate 2 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev111k5 : chartBlock (check111 5) 0 7 = true :=
  c111k5p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c111k6p0 : chartBlock (check111 6) 0 32 = true := by
  iterate 4 (all_goals apply compactHalves)
  all_goals decide +kernel
theorem c111k6p1 : chartBlock (check111 6) 32 6 = true := by
  iterate 1 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev111k6 : chartBlock (check111 6) 0 38 = true :=
  (chartBlock_join (a := 32) (b := 6) c111k6p0 c111k6p1)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c111k7p0 : chartBlock (check111 7) 0 32 = true := by
  iterate 4 (all_goals apply compactHalves)
  all_goals decide +kernel
theorem c111k7p1 : chartBlock (check111 7) 32 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev111k7 : chartBlock (check111 7) 0 34 = true :=
  (chartBlock_join (a := 32) (b := 2) c111k7p0 c111k7p1)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c111k8p0 : chartBlock (check111 8) 0 11 = true := by
  iterate 2 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev111k8 : chartBlock (check111 8) 0 11 = true :=
  c111k8p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c111k9p0 : chartBlock (check111 9) 0 1 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev111k9 : chartBlock (check111 9) 0 1 = true :=
  c111k9p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem excluded111 : Impossible true (graphGoal 111) 9 (vars 111).toFinset := by
  apply compactRoot (g := grid111) (t := tab111) (dom := compactDomains111) (perms := compactPerms111) pairs111 domains111 autos111
  · intro k hk
    change k ≤ 9 at hk
    interval_cases k
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · exact lev111k5
    · exact lev111k6
    · exact lev111k7
    · exact lev111k8
    · exact lev111k9
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound111 : Lower true (vars 111) (graphGoal 111) 10 :=
  plain_low (hints := 4146) (by decide +kernel) excluded111
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound113 : Lower true (vars 113) (graphGoal 113) 5 :=
  carry_of (old := 113) (rep := 23) (swaps := [64, 65, 81, 98]) (by decide +kernel) bound23
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound114 : Lower true (vars 114) (graphGoal 114) 4 :=
  carry_of (old := 114) (rep := 27) (swaps := [65, 64, 80, 99]) (by decide +kernel) bound27
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound115 : Lower true (vars 115) (graphGoal 115) 6 :=
  carry_of (old := 115) (rep := 55) (swaps := [84, 98]) (by decide +kernel) bound55
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound116 : Lower true (vars 116) (graphGoal 116) 4 :=
  carry_of (old := 116) (rep := 27) (swaps := [33, 67, 80, 99, 16]) (by decide +kernel) bound27
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound117 : Lower true (vars 117) (graphGoal 117) 7 :=
  carry_of (old := 117) (rep := 107) (swaps := [80, 50, 65, 49]) (by decide +kernel) bound107
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound118 : Lower true (vars 118) (graphGoal 118) 7 :=
  carry_of (old := 118) (rep := 91) (swaps := [32, 83]) (by decide +kernel) bound91
def grid119 : CompactGrid := (119, 9, samplesP119, samplesQ119)
def tab119 : CompactTable := (compactCount119, compactPath119, compactLive119, compactPoolIDs119, compactBucket119)
def check119 (k : Nat) := compactNode grid119 tab119 compactDomains119 compactPerms119 k
def sliceSpecs119 : List SliceSpec := [(1, 0, 118, 0, 0, 7, 7), (2, 0, 117, 0, 0, 7, 7), (16, 0, 103, 0, 0, 7, 7), (32, 0, 87, 0, 0, 7, 7), (4, 0, 115, 0, 0, 6, 6), (64, 0, 55, 0, 0, 6, 6), (0, 2, 69, 48, 16711680, 6, 4), (6, 0, 113, 0, 0, 5, 5), (18, 0, 101, 0, 0, 5, 5), (20, 0, 99, 0, 0, 5, 5), (34, 0, 85, 0, 0, 5, 5), (66, 0, 53, 0, 0, 5, 5), (96, 0, 23, 0, 0, 5, 5), (16, 2, 69, 32, 15728640, 5, 4), (32, 2, 69, 16, 983040, 5, 4), (3, 0, 116, 0, 0, 4, 4), (5, 0, 114, 0, 0, 4, 4), (17, 0, 102, 0, 0, 4, 4), (33, 0, 86, 0, 0, 4, 4), (36, 0, 83, 0, 0, 4, 4), (65, 0, 54, 0, 0, 4, 4), (80, 0, 39, 0, 0, 4, 4), (22, 0, 97, 0, 0, 4, 4), (48, 2, 69, 0, 0, 4, 4), (50, 0, 69, 0, 0, 4, 4), (98, 0, 21, 0, 0, 4, 4)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem domains119 : ∀ d ∈ compactDomains119, Slice true (vars 119) (graphGoal 119) d.1 d.2 := by
  apply compactDomains_valid (earlier := [(118, 7), (117, 7), (103, 7), (87, 7), (115, 6), (55, 6), (69, 4), (113, 5), (101, 5), (99, 5), (85, 5), (53, 5), (23, 5), (116, 4), (114, 4), (102, 4), (86, 4), (83, 4), (54, 4), (39, 4), (97, 4), (21, 4)]) (specs := sliceSpecs119)
  · intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact bound118
    · exact bound117
    · exact bound103
    · exact bound87
    · exact bound115
    · exact bound55
    · exact bound69
    · exact bound113
    · exact bound101
    · exact bound99
    · exact bound85
    · exact bound53
    · exact bound23
    · exact bound116
    · exact bound114
    · exact bound102
    · exact bound86
    · exact bound83
    · exact bound54
    · exact bound39
    · exact bound97
    · exact bound21
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem pairs119 : properPairs (graphGoal 119) (asRow samplesP119) (asRow samplesQ119) :=
  compactPairs (g := grid119) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem autos119 : ∀ p ∈ compactPerms119, autoOK (graphGoal 119) (p.map swapRows).reverse = true :=
  compactAutos_valid (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c119k5p0 : chartBlock (check119 5) 0 32 = true := by
  iterate 4 (all_goals apply compactHalves)
  all_goals decide +kernel
theorem c119k5p1 : chartBlock (check119 5) 32 6 = true := by
  iterate 1 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev119k5 : chartBlock (check119 5) 0 38 = true :=
  (chartBlock_join (a := 32) (b := 6) c119k5p0 c119k5p1)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c119k6p0 : chartBlock (check119 6) 0 32 = true := by
  iterate 4 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c119k6p1 : chartBlock (check119 6) 32 32 = true := by
  iterate 4 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c119k6p2 : chartBlock (check119 6) 64 32 = true := by
  iterate 4 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c119k6p3 : chartBlock (check119 6) 96 32 = true := by
  iterate 4 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c119k6p4 : chartBlock (check119 6) 128 32 = true := by
  iterate 4 (all_goals apply compactHalves)
  all_goals decide +kernel
theorem c119k6p5 : chartBlock (check119 6) 160 32 = true := by
  iterate 4 (all_goals apply compactHalves)
  all_goals decide +kernel
theorem c119k6p6 : chartBlock (check119 6) 192 6 = true := by
  iterate 1 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev119k6 : chartBlock (check119 6) 0 198 = true :=
  (chartBlock_join (a := 96) (b := 102) (chartBlock_join (a := 32) (b := 64) c119k6p0 (chartBlock_join (a := 32) (b := 32) c119k6p1 c119k6p2)) (chartBlock_join (a := 64) (b := 38) (chartBlock_join (a := 32) (b := 32) c119k6p3 c119k6p4) (chartBlock_join (a := 32) (b := 6) c119k6p5 c119k6p6)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c119k7p0 : chartBlock (check119 7) 0 32 = true := by
  iterate 4 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c119k7p1 : chartBlock (check119 7) 32 32 = true := by
  iterate 4 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c119k7p2 : chartBlock (check119 7) 64 32 = true := by
  iterate 4 (all_goals apply compactHalves)
  all_goals decide +kernel
theorem c119k7p3 : chartBlock (check119 7) 96 15 = true := by
  iterate 3 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev119k7 : chartBlock (check119 7) 0 111 = true :=
  (chartBlock_join (a := 64) (b := 47) (chartBlock_join (a := 32) (b := 32) c119k7p0 c119k7p1) (chartBlock_join (a := 32) (b := 15) c119k7p2 c119k7p3))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c119k8p0 : chartBlock (check119 8) 0 17 = true := by
  iterate 3 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev119k8 : chartBlock (check119 8) 0 17 = true :=
  c119k8p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c119k9p0 : chartBlock (check119 9) 0 1 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev119k9 : chartBlock (check119 9) 0 1 = true :=
  c119k9p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem excluded119 : Impossible true (graphGoal 119) 9 (vars 119).toFinset := by
  apply compactRoot (g := grid119) (t := tab119) (dom := compactDomains119) (perms := compactPerms119) pairs119 domains119 autos119
  · intro k hk
    change k ≤ 9 at hk
    interval_cases k
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · exact lev119k5
    · exact lev119k6
    · exact lev119k7
    · exact lev119k8
    · exact lev119k9
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound119 : Lower true (vars 119) (graphGoal 119) 10 :=
  plain_low (hints := 66) (by decide +kernel) excluded119
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound121 : Lower true (vars 121) (graphGoal 121) 7 :=
  carry_of (old := 121) (rep := 87) (swaps := [64, 99, 65, 82, 97]) (by decide +kernel) bound87
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound122 : Lower true (vars 122) (graphGoal 122) 7 :=
  carry_of (old := 122) (rep := 87) (swaps := [65, 48, 82]) (by decide +kernel) bound87
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound123 : Lower true (vars 123) (graphGoal 123) 10 :=
  carry_of (old := 123) (rep := 119) (swaps := [80, 65, 50]) (by decide +kernel) bound119
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound124 : Lower true (vars 124) (graphGoal 124) 7 :=
  carry_of (old := 124) (rep := 31) (swaps := [33, 49, 65, 80, 97]) (by decide +kernel) bound31
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound125 : Lower true (vars 125) (graphGoal 125) 10 :=
  carry_of (old := 125) (rep := 111) (swaps := [80, 50, 65]) (by decide +kernel) bound111
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound126 : Lower true (vars 126) (graphGoal 126) 10 :=
  carry_of (old := 126) (rep := 95) (swaps := [65, 50, 80]) (by decide +kernel) bound95
def ax31P : Nat → Bits
  | 0 => 0x7daff4ff85feae1f7df77fdd780a5af02f2feeeb94dbd5538a285fd2c2
  | 1 => ~~~(0x21400052059b1f800920271e309012ea2fa9040d0691995bcb2c925aea : Bits)
  | 2 => 0x7adfdfde2bb9799fdb7fe72e73b3756a0abbfd776a33b909cb2586eea8
  | 3 => 0x774feb77d6cb501fafebf9569ddda3a0505dff9c2fc4dfa01053bb5d10
  | 4 => ~~~(0x1080400482e8680000434944590b61205a60e8322842d5a19a730fc790 : Bits)
  | _ => 0

def ax31Q : Nat → Bits
  | 0 => 0x25213104a0011c50191040d04362183400ca0e00098149286105f0202
  | 1 => ~~~(0x5eb7fdecfaf6faf9cfb7f97be31fdf7fdd7d2f2fefb9dfef726db35afe : Bits)
  | 2 => 0x5212403900286328024429038c8c400910359064801012009a700eca0
  | 3 => 0x8b4358420142af90c028839211edd2c043d2f002400caae122db35810
  | 4 => 0x1080808400e048084200382001001820085006098320000c1008a0104c
  | _ => 0

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
def ax31Perms : Array (List Nat) := ([[], [32]] : List (List Nat)).toArray

def ax31Domains : Array (Sig × Nat) := ([(subcube 8 0, 5), (subcube 0 8, 5), (subcube 1 0, 4), (subcube 4 0, 4), (subcube 2 8, 4), (subcube 10 0, 4)] : List (Sig × Nat)).toArray

def ax31Words : Nat → Nat
  | 0 => 0x83f18da8f5a2ff807e55fe03fc07f80ff0115be844deb69fb3fe00d52c467ca9ffe02f6861ab4b25fe03fc02f087a4332e26c7f2cda03ffe00f9e97d7ff01fe009226cd3ad7624dd657b168b7c7739438864ceff017baffc06d2cff004903fc07a96e4bbb054f77781eff019385620ff80ef666f1e00777db1f688617fc04a9725aa89b62197f806c0ffe03fc06a80c0ccded45003001300cc41032092c3010188b400c044400d04100e10601dfd0d0d0d0d2c8c8c9c4c5c1bcbeb5b0b1ada9a4a5a0a29b8e8582787879747477686869665d5859564c4e44463c3e362c2e27181a130500d1404084040cc10505041311008049040880501041004911880440d2ffdbfdfbdfbfdfbeffddfbdfbf7fbeffddfbf7efdebf5efdfbf7f7fbf5fbfdfbdfbfdff5fefdff77fd7effebff7f5fbffa5281b285b282f192d192d28ad2863192119221123012228e128e128a12861281719161117280719330132013101300131290a090b010a011f191d191d111e011c011e291d291f08dc08dd285d281319130112291308c31902010308e9012a2929292a00a9288d090f010e290d290e00b08f01300609201200909101100900408c0100087a5703fc3d5578429ac0ba3ffc3fc15a3fc3fc3fc3fc1d6f5f414ffc2f1ffc3fc029bd59aa44218c982d02c02b5056a07130a08428e86a6fffffffbfffe32412212602402611c01600c09f
  | 1 => 0x2a1161f3828f41ff01f4a4136bb9b786bfe02941e233ff017123a97ff80d7bd6c07fc02863ec9d9a942a6392aa8b23e99f65cbabd5a0ca94c2840003c518024628024000b00000e0000570c42492492492496082082082082082082171e55044d2082082441041041041041041041041041041041413005051126ed6d6d74f4f6a5e5e7b4f4f565ececececed65ed756d65f1f1f5716d7aaeaf29f567a7a5faa7b1f1f3b1f1e5fcaebcb5756ea6fd357d0dcc230304b0c1483065c641319240a28d3149cc51b315dc6447190fc646d3148cc22030818c20530814c105315c4c071315f4c1653154c04520114cc153304a0c16911004c20130434c44008e08c55b30224c56211184c57b1913c644f30218a48529214c51719058c41708cec233b19070c2573082c040a2917023ca2404ca0404c64004c64002c23002c04402c040238a40028a2004824023804c238048028040238040028024014a44024a44014a40234a40024a38044a20044a18024a10044a10024a0824464c04464804464802464004404c23404c014040044020020a2404023802023401004c2300480298160445beb08243527fe03fc03a5eca51fe011130b60bda3af0c7aa74309c98f034aefbd06ff010e6e513c8039fa5d0b85e44a4be574f5ab2cc8564ee5b7c747d4a5c9708c8208ab4ebb1d784a0e695fc6daf495fe03fc02a017ac5a0125c541d
  | 2 => 0xd4ff7faebfe090740938330529008dca3fe0ff007050970e9ff047819aa893272ff83fc1fe0ff00bd315ca07342458be06e0d3587f83fc1e5220675bc45180aaaab498d168b45c570b15c2d2616c879c529c0c9c209c8b08858c8e9490948980899ca29c998294804784680400518880400518094804698b008004988046802981048046948804004047004802046943004cb7ced0af4f91d60af6948dd17ff01ceb7fc0523b3fb842fe6c5e94a6d1e9467a648d61cb5069a7c3240aebd65fe00e68ff80ff01fe037207f8036b5fe03913d5d4ff00516e7e21f3eff016a18a1a6e04dec49680af2db899cbb6b343b01ebc9b61ef63291cc2c0786099c7e3b857ff01fe024dcfae6c9d4c023fc0540d092b5a77fc01e9f7dd1d91760d67c6a5a7b957b1d6256602761b2ee949377d627803fc01b82
  | _ => 0

def ax31Count (k : Nat) : Nat := match k with
  | 7 => 1
  | 6 => 8
  | 5 => 56
  | 4 => 55
  | 3 => 11
  | 2 => 1
  | _ => 0

def ax31Path (k : Nat) (i : Nat) : Nat := match k with
  | 7 => 0
  | 6 => readCompactBits ax31Words (15 + 12*i) 12
  | 5 => let v := readCompactBits ax31Words (758 + 16*i) 16
    (readCompactBits ax31Words (602 + 12*(v >>> 12)) 12) ||| ((v &&& 4095) <<< 12)
  | 4 => let v := readCompactBits ax31Words (5784 + 18*i) 18
    (readCompactBits ax31Words (4872 + 24*(v >>> 12)) 24) ||| ((v &&& 4095) <<< 24)
  | 3 => let v := readCompactBits ax31Words (9857 + 16*i) 16
    (readCompactBits ax31Words (9497 + 36*(v >>> 12)) 36) ||| ((v &&& 4095) <<< 36)
  | 2 => let v := readCompactBits ax31Words (10590 + 12*i) 12
    (readCompactBits ax31Words (10542 + 48*(v >>> 12)) 48) ||| ((v &&& 4095) <<< 48)
  | _ => 0

def ax31Live (k : Nat) (i : Nat) : Nat := match k with
  | 7 => readCompactBits ax31Words (0 + 5*i) 5
  | 6 => readCompactBits ax31Words (111 + 6*i) 6
  | 5 => readCompactBits ax31Words (1654 + 7*i) 7
  | 4 => readCompactBits ax31Words (6774 + 8*i) 8
  | 3 => readCompactBits ax31Words (10033 + 9*i) 9
  | 2 => readCompactBits ax31Words (10602 + 10*i) 10
  | _ => 0

def ax31PoolIDs (k : Nat) (i : Nat) : List Nat := match k with
  | 7 => let v := readCompactBits ax31Words (11 + 4*i) 4
    let n := v >>> 2
    let bits := readCompactBits ax31Words (5 + 3*(v &&& 3)) (3*n)
    compactIDsFromBits bits 3 n
  | 6 => let v := readCompactBits ax31Words (258 + 9*i) 9
    let n := v >>> 6
    let bits := readCompactBits ax31Words (159 + 3*(v &&& 63)) (3*n)
    compactIDsFromBits bits 3 n
  | 5 => let v := readCompactBits ax31Words (2270 + 8*i) 8
    let n := v >>> 6
    let bits := readCompactBits ax31Words (2046 + 4*(v &&& 63)) (4*n)
    compactIDsFromBits bits 4 n
  | 4 => let v := readCompactBits ax31Words (7250 + 6*i) 6
    let n := v >>> 4
    let bits := readCompactBits ax31Words (7214 + 4*(v &&& 15)) (4*n)
    compactIDsFromBits bits 4 n
  | 3 => let v := readCompactBits ax31Words (10135 + 2*i) 2
    let n := v >>> 1
    let bits := readCompactBits ax31Words (10132 + 3*(v &&& 1)) (3*n)
    compactIDsFromBits bits 3 n
  | 2 => let v := readCompactBits ax31Words (10612 + 2*i) 2
    let n := v >>> 1
    let bits := readCompactBits ax31Words (10612 + 1*(v &&& 1)) (1*n)
    compactIDsFromBits bits 1 n
  | _ => []

def ax31Bucket (k : Nat) (i : Nat) : List Nat := match k with
  | 6 => let d := readCompactBits ax31Words (330 + 2*(i % 4)) 2
    let off := ((i/4 + d) % 22)
    let v := readCompactBits ax31Words (338 + 12*off) 12
    if v >>> 4 == (i/104729)%251 then [v &&& 15] else []
  | 5 => let d := readCompactBits ax31Words (2718 + 6*(i % 34)) 6
    let off := ((i/34 + d) % 130)
    let v := readCompactBits ax31Words (2922 + 15*off) 15
    if v >>> 7 == (i/104729)%251 then [v &&& 127] else []
  | 4 => let d := readCompactBits ax31Words (7580 + 6*(i % 32)) 6
    let off := ((i/32 + d) % 115)
    let v := readCompactBits ax31Words (7772 + 15*off) 15
    if v >>> 7 == (i/104729)%251 then [v &&& 127] else []
  | 3 => let d := readCompactBits ax31Words (10157 + 3*(i % 7)) 3
    let off := ((i/7 + d) % 28)
    let v := readCompactBits ax31Words (10178 + 13*off) 13
    if v >>> 5 == (i/104729)%251 then [v &&& 31] else []
  | 2 => let d := readCompactBits ax31Words (10614 + 1*(i % 2)) 1
    let off := ((i/2 + d) % 5)
    let v := readCompactBits ax31Words (10616 + 9*off) 9
    if v >>> 1 == (i/104729)%251 then [v &&& 1] else []
  | _ => []

def ax55P : Nat → Bits
  | 0 => 0xbf7fff90eb7bcfff7df17fcf634587ec2fe63b9af0f8a66c386ef42
  | 1 => ~~~(0x11809809c123ec024111734a3224c7ef0441128e92cca76f3107fca : Bits)
  | 2 => 0xf8ffd9ffc2e627fecf7ff0beba2640e337df36e5be4407630775688
  | 4 => ~~~(0x841010222f20c180060c88da34294f8838223e028727e68b66ce70 : Bits)
  | 5 => 0xddbfbf6b35b30bdbf3fccb49b7fa94189ff9c3ee0bf27808b78f870
  | _ => 0

def ax55Q : Nat → Bits
  | 0 => 0x408410251080221009818110208060100a060300c080c2102848442
  | 1 => ~~~(0xee6fe3d77efd54fbdfb65aefdc4f7dbdd4eb7fafdbdf2dad9387fde : Bits)
  | 2 => 0x7024e002409d988841034440b780c04a5982484180018635635280
  | 4 => 0x86100820230046302024802c00010881060180903052004818210c
  | 5 => 0x22494280484454c050265846c848012154e94022005528259387810
  | _ => 0

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
def ax55Perms : Array (List Nat) := ([[], [81, 64]] : List (List Nat)).toArray

def ax55Domains : Array (Sig × Nat) := ([(subcube 2 0, 5), (subcube 32 0, 5), (subcube 1 0, 4), (subcube 16 0, 4)] : List (Sig × Nat)).toArray

def ax55Words : Nat → Nat
  | 0 => 0x10bfeff7fbb41fa0141c9f
  | _ => 0

def ax55Count (k : Nat) : Nat := match k with
  | 6 => 1
  | 5 => 1
  | _ => 0

def ax55Path (k : Nat) (i : Nat) : Nat := match k with
  | 6 => 0
  | 5 => readCompactBits ax55Words (19 + 12*i) 12
  | _ => 0

def ax55Live (k : Nat) (i : Nat) : Nat := match k with
  | 6 => readCompactBits ax55Words (0 + 5*i) 5
  | 5 => readCompactBits ax55Words (31 + 6*i) 6
  | _ => 0

def ax55PoolIDs (k : Nat) (i : Nat) : List Nat := match k with
  | 6 => let v := readCompactBits ax55Words (13 + 6*i) 6
    let n := v >>> 3
    let bits := readCompactBits ax55Words (5 + 2*(v &&& 7)) (2*n)
    compactIDsFromBits bits 2 n
  | 5 => let v := readCompactBits ax55Words (37 + 2*i) 2
    let n := v >>> 1
    let bits := readCompactBits ax55Words (37 + 1*(v &&& 1)) (1*n)
    compactIDsFromBits bits 1 n
  | _ => []

def ax55Bucket (k : Nat) (i : Nat) : List Nat := match k with
  | 5 => let d := readCompactBits ax55Words (39 + 1*(i % 2)) 1
    let off := ((i/2 + d) % 5)
    let v := readCompactBits ax55Words (41 + 9*off) 9
    if v >>> 1 == (i/104729)%251 then [v &&& 1] else []
  | _ => []

def ax87P : Nat → Bits
  | 0 => 0xdfbfff3b167bd5ffbf3bab65be76583b9fd9bf3f43c39210f4e5ec8
  | 1 => 0xed3f47f6679d00f9fdfdd7db4c9845800bffd9d98db8006b0f77014
  | 2 => ~~~(0x4080440103d9c1008109c3248c9855a993806b594503806bfc872dc : Bits)
  | 4 => 0xfafffcf5d9f8caf7e3ffeb3ec18fe7a1cfa767d07f6781ef0c9a33c
  | 6 => ~~~(0xb0100365438de012030ab5b40066fb3c80195900be393ff0470f3c : Bits)
  | _ => 0

def ax87Q : Nat → Bits
  | 0 => 0x204820440904284010232086020824002141a028030082082444888
  | 1 => 0x12d13c489040ef7860086b87c279902649df085080a08e1f3f75004
  | 2 => 0x408414010290812408904a000051010908141084205008160230502
  | 4 => 0x520011024031081030484081402005016204500480520a0408a230
  | 6 => ~~~(0xf4fcf6edbfd7a96d7bbf7af62bdd757f7955fdfcebf6db5ea674fbe : Bits)
  | _ => 0

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
def ax87Perms : Array (List Nat) := ([[], [32]] : List (List Nat)).toArray

def ax87Domains : Array (Sig × Nat) := ([(subcube 2 0, 5), (subcube 64 0, 5), (subcube 0 2, 5), (subcube 1 0, 4), (subcube 4 0, 4), (subcube 16 2, 4), (subcube 18 0, 4), (subcube 66 0, 4)] : List (Sig × Nat)).toArray

def ax87Words : Nat → Nat
  | 0 => 0x7f80ff005c8ac507f80c40000188a7ff806a7ffe0324aff80bb3aea6bfc06219ff01b762b452fd9eb8e20def4bff80bdb61b562e15db6735fec3bfc06d88d605fe03fc02b40ff01fe02348ff80dc30486fb13e04b784bfe03fc010bbff013237d479b31ff00e4e3fc025a3bb1686254d6c4c48f91170d5a0d1460c728b01402801320044800a00278000008201e0027705c76557750d37405033c4f7304c725c670c437013e4f13a6dc370dcb62d4b44ca2e6ad2949c27495234859e8699745611a308b2288941e03600f028440008e328c2010802284022c0213148200ca20424584a42008011805090423206221c88508805848312880248c02c94023086900923008402efdf7efefdf7effdfb76fdfef9efdfef7f7eff77fdfdfb7efeffdfaffdfdfafeffbf7eddfbf7efdfb7651927112528e528911911111328d3289f011d011d28212921288d190d190f290d290d10cf289a191919191119291910da08d808d928d9280a190b01090109290a08cb00c900c928c2190208d60095009528871105110501060085008728b01300e08e00a00501100d00900400b9a3e2d2e5ff81241fe0ff07f8104c2ec681ff83fc0827ff01a935511819d4b50a10b1eeff061bf94028a5fe8f0c772f91c5e1680d02aa8e40266a840e212a42c806a0268ca2a60484ea6c12064b7ffffbfffffbec32602202411e01a01c01400a00c06a1f
  | 1 => 0x125ebd43779836962a44f4391991ec51ae35ff0056e7fc00b277d944a7640631a91669fe029cfff80ff002c17fc01042ff01fe0130068cdff01fe03fc0768fff005005b9b55975e37fe00e45c2b7ff00a6c69a07f80f77d1e0968c90d2c183dc549e82f13ff0032189844443ff01fe00268b6bc11130f1046727c6a123e153725ba5500a7dce00263449627e4a1f450860024802d848010018211000618400200a2305e3c78f5cb46ac562c5aa14a54270e1d3060c1832587040810204081020408140000000002081a6a0ca0000803cb20e0059c7c79d9d8fe6e69bc7e3b99de5b9bc9dc78feaea8fcdbc9de6f2c78f8fcd9dc7d5eaf8add9d99dbcadd9d9823271193098aacc266622730121811cc2da321d192898544c5023201308098004c57a325a316f88864440c62cf292698134c52a321510dc8c8ecc4aa62c9292498ad8646c118a19050464cc45c012d00b318a8cc01e626a00b48059468099448079448038888038090478088050c88050c80050470050468050460049488069478089470049468049460049458069450029410468c88068888028870048088048068048050028048028040041488040470054ac2200d805bc65cf44f62ee49112720e5ce9cd35794204a22cfd2dc2da896d031774d60da1b574f880f0459543a0f62ba4b3c5192536a15aecce094a8fbfc001ac220e8ea5f5e68bdff00093bfc0
  | 2 => 0x7ef411ff83acbfe0840ff808e7fe0ff07f83ae010eee3daa7fc1fe03997f82099fe0725ff8269aaf1c212b000008102c5a1d26161b4ae456385d009c4d1912324464e9cd9396a5254e530c8608f29208d00a19100800a08d00800931408e00930808e00930008e00928d00800830119100f3826b3a4d15fe00257f2ad8167de3acd5dd832e51b097c
  | _ => 0

def ax87Count (k : Nat) : Nat := match k with
  | 7 => 1
  | 6 => 9
  | 5 => 47
  | 4 => 43
  | 3 => 10
  | _ => 0

def ax87Path (k : Nat) (i : Nat) : Nat := match k with
  | 7 => 0
  | 6 => readCompactBits ax87Words (23 + 12*i) 12
  | 5 => let v := readCompactBits ax87Words (926 + 16*i) 16
    (readCompactBits ax87Words (806 + 12*(v >>> 12)) 12) ||| ((v &&& 4095) <<< 12)
  | 4 => let v := readCompactBits ax87Words (5421 + 17*i) 17
    (readCompactBits ax87Words (4725 + 24*(v >>> 12)) 24) ||| ((v &&& 4095) <<< 24)
  | 3 => let v := readCompactBits ax87Words (8666 + 15*i) 15
    (readCompactBits ax87Words (8378 + 36*(v >>> 12)) 36) ||| ((v &&& 4095) <<< 36)
  | _ => 0

def ax87Live (k : Nat) (i : Nat) : Nat := match k with
  | 7 => readCompactBits ax87Words (0 + 5*i) 5
  | 6 => readCompactBits ax87Words (131 + 6*i) 6
  | 5 => readCompactBits ax87Words (1678 + 7*i) 7
  | 4 => readCompactBits ax87Words (6152 + 8*i) 8
  | 3 => readCompactBits ax87Words (8816 + 9*i) 9
  | _ => 0

def ax87PoolIDs (k : Nat) (i : Nat) : List Nat := match k with
  | 7 => let v := readCompactBits ax87Words (17 + 6*i) 6
    let n := v >>> 3
    let bits := readCompactBits ax87Words (5 + 3*(v &&& 7)) (3*n)
    compactIDsFromBits bits 3 n
  | 6 => let v := readCompactBits ax87Words (389 + 9*i) 9
    let n := v >>> 6
    let bits := readCompactBits ax87Words (185 + 4*(v &&& 63)) (4*n)
    compactIDsFromBits bits 4 n
  | 5 => let v := readCompactBits ax87Words (2482 + 10*i) 10
    let n := v >>> 7
    let bits := readCompactBits ax87Words (2007 + 5*(v &&& 127)) (5*n)
    compactIDsFromBits bits 5 n
  | 4 => let v := readCompactBits ax87Words (6598 + 7*i) 7
    let n := v >>> 5
    let bits := readCompactBits ax87Words (6496 + 6*(v &&& 31)) (6*n)
    compactIDsFromBits bits 6 n
  | 3 => let v := readCompactBits ax87Words (8920 + 3*i) 3
    let n := v >>> 2
    let bits := readCompactBits ax87Words (8906 + 7*(v &&& 3)) (7*n)
    compactIDsFromBits bits 7 n
  | _ => []

def ax87Bucket (k : Nat) (i : Nat) : List Nat := match k with
  | 6 => let d := readCompactBits ax87Words (470 + 4*(i % 6)) 4
    let off := ((i/6 + d) % 24)
    let v := readCompactBits ax87Words (494 + 13*off) 13
    if v >>> 5 == (i/104729)%251 then [v &&& 31] else []
  | 5 => let d := readCompactBits ax87Words (2952 + 6*(i % 28)) 6
    let off := ((i/28 + d) % 107)
    let v := readCompactBits ax87Words (3120 + 15*off) 15
    if v >>> 7 == (i/104729)%251 then [v &&& 127] else []
  | 4 => let d := readCompactBits ax87Words (6899 + 6*(i % 24)) 6
    let off := ((i/24 + d) % 89)
    let v := readCompactBits ax87Words (7043 + 15*off) 15
    if v >>> 7 == (i/104729)%251 then [v &&& 127] else []
  | 3 => let d := readCompactBits ax87Words (8950 + 2*(i % 5)) 2
    let off := ((i/5 + d) % 25)
    let v := readCompactBits ax87Words (8960 + 13*off) 13
    if v >>> 5 == (i/104729)%251 then [v &&& 31] else []
  | _ => []

def ax91P : Nat → Bits
  | 0 => 0x5f6fffcd469bf67deef7f8f1b73799514afbdb7eba7949c901b2adad64
  | 1 => ~~~(0x11103200250b3e000415008197391d956ea2016ce33011fd81ba26c976 : Bits)
  | 3 => 0x7d5fb7bffd8d197eff9f972eeb993d84b566ff44e7aafe34924c7bca92
  | 4 => ~~~(0x46005804a855b00a8021f22a3172015b5805814ac4a6a7493de192ef2 : Bits)
  | 6 => 0x76bffff22b677a7fbd7f4f83977f669524bf7dbded563074819b167c72
  | _ => 0

def ax91Q : Nat → Bits
  | 0 => 0x20911052812408a82084491250b00388844a4a2088210a498850a92844
  | 1 => ~~~(0x6eebedeedbfde3cdbfddfebf83eef8ef9ff6a9eeebf77ff3f3a867d9fe : Bits)
  | 3 => 0x2a244420250228c9210189280e0a0a108468904420246439028638890
  | 4 => 0x4684484088143440448b2848142a80401b4a1c20090109230a846d108
  | 6 => 0x940828550088551090122442d030c0212313408214420942487145422
  | _ => 0

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
def ax91Perms : Array (List Nat) := ([[], [49, 100], [16, 99], [16, 97, 99, 100], [48, 49, 67, 100], [48, 65], [64, 49, 99, 100], [64, 97], [96, 67], [96, 65, 67, 100]] : List (List Nat)).toArray

def ax91Domains : Array (Sig × Nat) := ([(subcube 1 0, 4), (subcube 2 0, 4), (subcube 8 0, 4), (subcube 16 0, 4), (subcube 64 0, 4)] : List (Sig × Nat)).toArray

def ax91Words : Nat → Nat
  | 0 => 0xaf8391ff003bb79f3862e67812d81d452145e4f36cf8c566449e9634487423a9051fa05a8cae69a5bd22529ea2ff0062a7283b1e92ff0068d8ff0057599319ff004e87ff00cf742ddaff00db8aaa707315ff00aa7835b9ff00ff009ba8a5d79f04767a2582b336ff00438665d9ff00ff00ae850e3a9f2dfab8559f2c22abbba5469431439d4bd2b3b6ee17d37ee0e21f0ec93f9400dd6f185bc693eae0e8cd76010bed24b152245295a21bb84ac14ea468497fdcc0dab434c6bee5ff005171893eff00411072a5238e2465e55ccab3352bff00ff00572ccd7d4a83c840949a113c9989716dc94f254cff008213ff0054e33003d26a6bbaa0d1702f2c88ff00c87380643c585bb1731000232f84e20400a301b28504114124040510204005f0017041d42546080910008080802c00000082810001c000314904b2cb2da28a2a82082082175955044d280002181b60c77fedfbf7efdffb3efcffb7fedfbffbf5ffbfafdfbf5292c11d4a3a9435281e51bca03047229225244a48847128e41144a28940b00d201a4a35044b00925104a309450450028448020440022c263a3fe05b91fe07f80324e4a0da71ac4750bbbdfe040c7d0ca115acfff81fe01a26953931b8d203cd40ec3996707c857ab9525fe07f80747ff80b52ff80d4dff80145ff812c3632bfe0301859900057d552d046428c151a063447fffffc112114008009f
  | 1 => 0x8c1544fbfc02b05b554fc3d68a7484f698fb0eb5e62c40462b6424a7c408ea03fe0175c92000d185cd8e67250d3467d735c997f80334e6b155646312da27630301a602cff01392bfc07f80ff019e27fc012c9ae601c726c162836e16bc1d9dc091bae5de8f7e8aff801c31fe0011ad9a63e35471aa0cb5bbff01fe03fc06916ff01fe037c3768e9075fe02120c7c73a2e44fdfd26222ff008a802dba3c2ff00d12c9889b1d381a40e022680a311123091002a00100008fd3d5f497d5d6973988e111e60ec23118b028e851acc3c03401c024018224014a30224a24014a08220a3401f760ff00364335bc507bff0082a6ff00ff008a755762ff00ff009c8bff00b7804899be42e209ff0086e7c2db1fb5ff00a91f865e3eabff006d8426c22bc486761381ff00d60c0d97ff0060c720ec8dd500c131ad6a5fb6e8d72a4166ff00f4bfff0035411f5475d313207e4d985dd0a95aa1d9496028e14bff005c47df3d6acfcd94799b80a3327c865aeba40a30c6c9921e67ee7d024eeb2067b479b59c84becaeac5d43c27ff006c34ff0069c3c226d34550ef7072ff00ab072b56b08fee6e5c63f808352ebdcbff00387729d6e16b392987e920614c8d7d9e25988425709076064
  | _ => 0

def ax91Count (k : Nat) : Nat := match k with
  | 7 => 1
  | 6 => 4
  | 5 => 24
  | 4 => 8
  | _ => 0

def ax91Path (k : Nat) (i : Nat) : Nat := match k with
  | 7 => 0
  | 6 => readCompactBits ax91Words (7 + 12*i) 12
  | 5 => let v := readCompactBits ax91Words (885 + 15*i) 15
    (readCompactBits ax91Words (813 + 12*(v >>> 12)) 12) ||| ((v &&& 4095) <<< 12)
  | 4 => let v := readCompactBits ax91Words (6076 + 15*i) 15
    (readCompactBits ax91Words (5908 + 24*(v >>> 12)) 24) ||| ((v &&& 4095) <<< 24)
  | _ => 0

def ax91Live (k : Nat) (i : Nat) : Nat := match k with
  | 7 => readCompactBits ax91Words (0 + 5*i) 5
  | 6 => readCompactBits ax91Words (55 + 6*i) 6
  | 5 => readCompactBits ax91Words (1245 + 7*i) 7
  | 4 => readCompactBits ax91Words (6196 + 8*i) 8
  | _ => 0

def ax91PoolIDs (k : Nat) (i : Nat) : List Nat := match k with
  | 7 => let v := readCompactBits ax91Words (5 + 2*i) 2
    let n := v >>> 1
    let bits := readCompactBits ax91Words (5 + 1*(v &&& 1)) (1*n)
    compactIDsFromBits bits 1 n
  | 6 => let v := readCompactBits ax91Words (139 + 8*i) 8
    let n := v >>> 5
    let bits := readCompactBits ax91Words (79 + 3*(v &&& 31)) (3*n)
    compactIDsFromBits bits 3 n
  | 5 => let v := readCompactBits ax91Words (1446 + 6*i) 6
    let n := v >>> 4
    let bits := readCompactBits ax91Words (1413 + 3*(v &&& 15)) (3*n)
    compactIDsFromBits bits 3 n
  | 4 => let v := readCompactBits ax91Words (6260 + 2*i) 2
    let n := v >>> 1
    let bits := readCompactBits ax91Words (6260 + 1*(v &&& 1)) (1*n)
    compactIDsFromBits bits 1 n
  | _ => []

def ax91Bucket (k : Nat) (i : Nat) : List Nat := match k with
  | 6 => let d := readCompactBits ax91Words (171 + 4*(i % 10)) 4
    let off := ((i/10 + d) % 43)
    let v := readCompactBits ax91Words (211 + 14*off) 14
    if v >>> 6 == (i/104729)%251 then [v &&& 63] else []
  | 5 => let d := readCompactBits ax91Words (1590 + 6*(i % 69)) 6
    let off := ((i/69 + d) % 244)
    let v := readCompactBits ax91Words (2004 + 16*off) 16
    if v >>> 8 == (i/104729)%251 then [v &&& 255] else []
  | 4 => let d := readCompactBits ax91Words (6276 + 5*(i % 24)) 5
    let off := ((i/24 + d) % 88)
    let v := readCompactBits ax91Words (6396 + 15*off) 15
    if v >>> 7 == (i/104729)%251 then [v &&& 127] else []
  | _ => []

def ax107P : Nat → Bits
  | 0 => 0x7abf2fefd4580fffe76c98cbfa8ec006feece7267402acb7e488
  | 1 => 0x5e7ffcbd6d8447dd3ffb73515d20252bfc573e9cf990517d5260
  | 3 => ~~~(0x841009dd004780c240c89115adec13a0454a5383597ac8d6cea : Bits)
  | 5 => 0x7dfff7d6db677faeffb5adbd1fd343bfa797897b31d7860e2d72
  | 6 => ~~~(0x108024264d434880032130c91da367a8a2870a0679d2d7363770 : Bits)
  | _ => 0

def ax107Q : Nat → Bits
  | 0 => 0x545511008a2f590a00c6a1c89102264ec8c21004cc89c378480
  | 1 => 0x21a045408253ae081245c078b1891013d442121020b199ed5040
  | 3 => 0x84910051004514200a82a04084281042a2008850c4804128214
  | 5 => 0x21000082408002409000000002408000001804a100000002122
  | 6 => ~~~(0x6f7dfb9dbefef5febbee7f9fcfffbb74eeefbbdf7fcefe37b7f6 : Bits)
  | _ => 0

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
def ax107Perms : Array (List Nat) := ([[], [16, 99]] : List (List Nat)).toArray

def ax107Domains : Array (Sig × Nat) := ([(subcube 1 0, 5), (subcube 2 0, 5), (subcube 8 0, 5), (subcube 64 0, 5), (subcube 32 0, 4), (subcube 3 0, 4), (subcube 10 0, 4), (subcube 65 0, 4)] : List (Sig × Nat)).toArray

def ax107Words : Nat → Nat
  | 0 => 0x7f9c3fe7f9fe451004da350ce3a12262221a012222122013513fc1fe02ba59edd5ffe0c747f836168e6239fa57fc1bfdff06734471fe0ff02f85c21cd14c1605feb2d76194e39541dcdca63ca8dc587b26007f83fc06a202005006318c6334a598c71401304a4099ee39e9d8f9dbaeabae8eaf2bababa7cc034646cc04cc15cc45cc194c224642cc30444a4441c6414c484c25cc2ca4402c644028a34024a48434a44434a34024a2803444443444402443402424402915efc43d2e821db3a981d1cd4a787f83e5ffe09a1b6061c9fe0ff0025f6d9dea05cff83fc0825e8a8783fc18edd69709f627fe09a80036007113010102f4d4b2a29284625a00310100223126290bbf7eff7f77efdffdfaffef4f28ea5254a058c8911125244a23944200c20184a318c8111210e00d11110d00d00bfc14c949f78cc06bc3fc3fc25dbfc0317fc38527a7fc3fc3fc3cb490abc5a04106730642507432147597620fffffff911210e00d00f00a8dd51f
  | _ => 0

def ax107Count (k : Nat) : Nat := match k with
  | 7 => 1
  | 6 => 5
  | 5 => 13
  | 4 => 15
  | 3 => 2
  | _ => 0

def ax107Path (k : Nat) (i : Nat) : Nat := match k with
  | 7 => 0
  | 6 => readCompactBits ax107Words (26 + 12*i) 12
  | 5 => let v := readCompactBits ax107Words (538 + 15*i) 15
    (readCompactBits ax107Words (466 + 12*(v >>> 12)) 12) ||| ((v &&& 4095) <<< 12)
  | 4 => let v := readCompactBits ax107Words (1716 + 16*i) 16
    (readCompactBits ax107Words (1452 + 24*(v >>> 12)) 24) ||| ((v &&& 4095) <<< 24)
  | 3 => let v := readCompactBits ax107Words (2787 + 13*i) 13
    (readCompactBits ax107Words (2715 + 36*(v >>> 12)) 36) ||| ((v &&& 4095) <<< 36)
  | _ => 0

def ax107Live (k : Nat) (i : Nat) : Nat := match k with
  | 7 => readCompactBits ax107Words (0 + 5*i) 5
  | 6 => readCompactBits ax107Words (86 + 6*i) 6
  | 5 => readCompactBits ax107Words (733 + 7*i) 7
  | 4 => readCompactBits ax107Words (1956 + 8*i) 8
  | 3 => readCompactBits ax107Words (2813 + 9*i) 9
  | _ => 0

def ax107PoolIDs (k : Nat) (i : Nat) : List Nat := match k with
  | 7 => let v := readCompactBits ax107Words (20 + 6*i) 6
    let n := v >>> 3
    let bits := readCompactBits ax107Words (5 + 3*(v &&& 7)) (3*n)
    compactIDsFromBits bits 3 n
  | 6 => let v := readCompactBits ax107Words (216 + 8*i) 8
    let n := v >>> 5
    let bits := readCompactBits ax107Words (116 + 4*(v &&& 31)) (4*n)
    compactIDsFromBits bits 4 n
  | 5 => let v := readCompactBits ax107Words (892 + 8*i) 8
    let n := v >>> 5
    let bits := readCompactBits ax107Words (824 + 4*(v &&& 31)) (4*n)
    compactIDsFromBits bits 4 n
  | 4 => let v := readCompactBits ax107Words (2106 + 5*i) 5
    let n := v >>> 3
    let bits := readCompactBits ax107Words (2076 + 5*(v &&& 7)) (5*n)
    compactIDsFromBits bits 5 n
  | 3 => let v := readCompactBits ax107Words (2845 + 4*i) 4
    let n := v >>> 2
    let bits := readCompactBits ax107Words (2831 + 7*(v &&& 3)) (7*n)
    compactIDsFromBits bits 7 n
  | _ => []

def ax107Bucket (k : Nat) (i : Nat) : List Nat := match k with
  | 6 => let d := readCompactBits ax107Words (256 + 2*(i % 3)) 2
    let off := ((i/3 + d) % 17)
    let v := readCompactBits ax107Words (262 + 12*off) 12
    if v >>> 4 == (i/104729)%251 then [v &&& 15] else []
  | 5 => let d := readCompactBits ax107Words (996 + 5*(i % 8)) 5
    let off := ((i/8 + d) % 32)
    let v := readCompactBits ax107Words (1036 + 13*off) 13
    if v >>> 5 == (i/104729)%251 then [v &&& 31] else []
  | 4 => let d := readCompactBits ax107Words (2181 + 4*(i % 10)) 4
    let off := ((i/10 + d) % 38)
    let v := readCompactBits ax107Words (2221 + 13*off) 13
    if v >>> 5 == (i/104729)%251 then [v &&& 31] else []
  | 3 => let d := readCompactBits ax107Words (2853 + 1*(i % 2)) 1
    let off := ((i/2 + d) % 5)
    let v := readCompactBits ax107Words (2855 + 10*off) 10
    if v >>> 2 == (i/104729)%251 then [v &&& 3] else []
  | _ => []

def ax63P : Nat → Bits
  | 0 => 0xbfb7fffa7fb93bf7cb65ec2abffbffbf3d7ff6fcf2ed02d55fee01a30f6b9f07e3673047dffe7b55cdf37f63f64fe7117bdcded0853adc036e4505ce045a9b04b95efebf29c8ba4988e6764cf4140e1b84d4120bebcda02
  | 1 => ~~~(0x114002000970094363064f6500108122006452a0b84821810b84513f6e078bc265ff3544910810188661544a4482c1b1f15e4e95e5ac1645437615c734dbbbc5889832c630acd288dcccb2e9c6371f3be5dd66652dede9a : Bits)
  | 2 => 0xfcdbfe6ffdf277cf345e00f73ff79f6fffbc3fe33cf8e79b7f90f34c3e0fa0d61b840505f7fbf7f9f3ecdcb9cf8fd8f3f02e1f0f607d0fc3c0fa06d1100218c79f8f79ded774378e741c79e0c2010718e088e1e374b5408
  | 3 => 0xfb57f7f5df7d9cf9771237293ffdf3fedecdc9e5dd1f79efa7af3c375225c7e82c98800bb9ffbffebe27ecdef3b1e72c94d72673eb8470dc831e3b6060a5200bebb7f7e23e9cc1b03fa99667486210600323ee2dad12190
  | 4 => ~~~(0x8900440108814e5045d243b8040000c158d00c5108d4058662239e4132de6372b3ce86c00e22014f1040880f20da32f9cc5175309335cd3aa59267266e77e2c0306e8ba06d0a3fe32285e44f96ed67a97e7c1abe39f3f0 : Bits)
  | 5 => 0xdfebffdfbbcecd67ec8d4f55ffdeedfff7e7529fbbcffd78ea7459fce1946a3365786862ffeffc9ef75d13ce7cfeb9af8d4141951da316753b71f43626c1662146f8aafff6a3c2fed2488a99b12ed022154545f403e82f0
  | _ => 0

def ax63Q : Nat → Bits
  | 0 => 0x4048200981444400100a02c54880103104c0310032120531200102103084401000904582588202544000602206400012840cc02005442c009141032018210400a15288a0094082400086004c081a0a048424120b8304202
  | 1 => ~~~(0xeebefcfefedff6feddfdb8bedf5fb7f77fbfecefeff1cbfedef7bff9f7fef77fdae5fbbdbb3efcffd77ff5efdfd7efc5bdfbbb9fbcbffbfe4fdf7eddff6fef7feeba77ef72edffdaffdebeffdfe77debb3ddeef5adedfbe : Bits)
  | 2 => 0x3241392040880104ba0fd00b44402022010c658844d3840c19a042041100120806b1a598761a52083080481000300ac62110fc06210510f2aa8d400014421201a0d615ad6042408600828004060d01868cac1a074b1400
  | 3 => 0x4a8441aa082020280cd8894cd0101801285a402a2504370cc50818880023000422479b139123c4a002600408100a280847989061404685a47c116458400c006aab255a2308041001a00142208433840819caa25ad00110
  | 4 => 0x8920420300010640455003a031a004009050023402042020e601840022802030804a024201c58810450800c080047410860000798098050440208442202020b44a0160520081800851080900285206111102c54084080c
  | 5 => 0x201480a0141120880130302a1200a404411040694421080202a020010440844c1001820c822cc080100111005094094528000281a8199104080a4800400808514408224d422100920040020192a44029304044d000e80a0
  | _ => 0

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
def ax63Perms : Array (List Nat) := ([[], [64, 81], [50, 16, 84], [50, 80, 65]] : List (List Nat)).toArray

def ax63Domains : Array (Sig × Nat) := ([(subcube 1 0, 7), (subcube 1 0, 7), (subcube 1 0, 7), (subcube 1 0, 7), (subcube 1 0, 7), (subcube 1 0, 7), (subcube 1 0, 7), (subcube 1 0, 7), (subcube 1 0, 7), (subcube 1 0, 7), (subcube 1 0, 7), (subcube 1 0, 7), (subcube 1 0, 7), (subcube 2 0, 7), (subcube 2 0, 7), (subcube 2 0, 7), (subcube 2 0, 7), (subcube 2 0, 7), (subcube 2 0, 7), (subcube 2 0, 7), (subcube 2 0, 7), (subcube 2 0, 7), (subcube 2 0, 7), (subcube 2 0, 7), (subcube 2 0, 7), (subcube 2 0, 7), (subcube 2 0, 7), (subcube 2 0, 7), (subcube 2 0, 7), (subcube 16 0, 7), (subcube 16 0, 7), (subcube 16 0, 7), (subcube 16 0, 7), (subcube 16 0, 7), (subcube 16 0, 7), (subcube 16 0, 7), (subcube 16 0, 7), (subcube 32 0, 7), (subcube 32 0, 7), (subcube 32 0, 7), (subcube 32 0, 7), (subcube 32 0, 7), (subcube 32 0, 7), (subcube 8 0, 6), (subcube 0 4, 6), (subcube 0 8, 6), (subcube 5 0, 5), (subcube 1 4, 5)] : List (Sig × Nat)).toArray

def ax63Words : Nat → Nat
  | 0 => 0x589ff84b2ff85937f858bb1159530dff823254d0902c5d1d5ac5cb177fffffa32a12a11a017f833c7e41ff069be8c0655889e1264d9fe0e968abbfc054a1eba997989fe0e93c099bd055ad017f82ab66cbff07f80181080204edae83a13d9c11cc84001828407252c687950044f20aa9d819067408d00a96a47a518085894e899a9868042b5eb020096253a500101c62acd528d6066034e124a747553664c009a817b026b14253a2010d0a1048116885559af49ac003129d0e240861a2c5559a7de8059ffffffffffff42484344382242280240282574d03f
  | _ => 0

def ax63Count (k : Nat) : Nat := match k with
  | 9 => 1
  | 8 => 7
  | 7 => 3
  | _ => 0

def ax63Path (k : Nat) (i : Nat) : Nat := match k with
  | 9 => 0
  | 8 => readCompactBits ax63Words (36 + 12*i) 12
  | 7 => let v := readCompactBits ax63Words (1447 + 12*i) 12
    (readCompactBits ax63Words (1435 + 12*(v >>> 12)) 12) ||| ((v &&& 4095) <<< 12)
  | _ => 0

def ax63Live (k : Nat) (i : Nat) : Nat := match k with
  | 9 => readCompactBits ax63Words (0 + 6*i) 6
  | 8 => readCompactBits ax63Words (120 + 7*i) 7
  | 7 => readCompactBits ax63Words (1483 + 8*i) 8
  | _ => 0

def ax63PoolIDs (k : Nat) (i : Nat) : List Nat := match k with
  | 9 => let v := readCompactBits ax63Words (30 + 6*i) 6
    let n := v >>> 3
    let bits := readCompactBits ax63Words (6 + 6*(v &&& 7)) (6*n)
    compactIDsFromBits bits 6 n
  | 8 => let v := readCompactBits ax63Words (939 + 12*i) 12
    let n := v >>> 7
    let bits := readCompactBits ax63Words (169 + 7*(v &&& 127)) (7*n)
    compactIDsFromBits bits 7 n
  | 7 => let v := readCompactBits ax63Words (1563 + 7*i) 7
    let n := v >>> 4
    let bits := readCompactBits ax63Words (1507 + 7*(v &&& 15)) (7*n)
    compactIDsFromBits bits 7 n
  | _ => []

def ax63Bucket (k : Nat) (i : Nat) : List Nat := match k with
  | 8 => let d := readCompactBits ax63Words (1023 + 5*(i % 7)) 5
    let off := ((i/7 + d) % 29)
    let v := readCompactBits ax63Words (1058 + 13*off) 13
    if v >>> 5 == (i/104729)%251 then [v &&& 31] else []
  | 7 => let d := readCompactBits ax63Words (1584 + 1*(i % 3)) 1
    let off := ((i/3 + d) % 12)
    let v := readCompactBits ax63Words (1587 + 12*off) 12
    if v >>> 4 == (i/104729)%251 then [v &&& 15] else []
  | _ => []

def ax95P : Nat → Bits
  | 0 => 0xbeefffff5b5b0fbfdb3759cc3ff7cfeff6bdc7defb75fc665eae88c39c43761f1ef6660bfbfb9f4feb7d95f8dca77f8a58e58a7d0856a36ee43b3e846091b30dd7ccf56ee59bf1795688dc92271062048751152dd13b310
  | 1 => 0xdfabf59fffebf9ce7039ccb07ffeffb67fdef8f90f878f879fdfc78ce0739863ec0000b1fddffbf8f39e1f3f7f3b8ff1a0fa0f87f3e0fc1f07c1c00513260012eaef67f7b9e31e1e0d0f70e3c82080393886dbc9a1d4424
  | 2 => ~~~(0x24804120041a5844b1988cf000041242109844c0b460607030fa64686699e57469f22b8d100011063889230088d2ff510ec0daf1b16cb964575a30557beab548489c5c5245975db2e8b60a70ff1d0793bdf9f2315b577c : Bits)
  | 3 => 0xfad7fefebeb7a7d4bf4332273ffffb7fe945bd3d375a36ff677fb6164ed827c4c1c90083d73ffff12febfaa9a7ff69350b2cf59f370ec59148f46718042e0853be77bfcd663423c7aa1927bf28e11048088e6f175c64448
  | 4 => 0xf75fff73ffd4ffa96f8caa5bbfa9fffdff3bf6e7ccee4b7ff92d776a132cdf1b03062973fff477f6d691faf6f8dcfe4c54d56d62cf995a909734b9679b102383d59bde913f5cdc91aae6e84d1612c1b17060bc223e818b4
  | 6 => ~~~(0x108400001a920b8833277a3000208a004014f0b1040008665c2fd78a5852770b89666df100101260821118a8f4324b0848f5ef57e7c8f41986b07c07bb37339bd246360021b69a158a0cfcdb2e32e3bdfce67d0df84fcb4 : Bits)
  | _ => 0

def ax95Q : Nat → Bits
  | 0 => 0x411042012404904020c82412a410080c10404c2204340200e1810100420480c0210898604b089040090400a04024148900039882088863012000e18090200821820c812c218801280200c012091052018090150d0128210
  | 1 => 0x205502702210042087443247b820018208500437c8103619c02c282210802110008f8d0858cb7218121200082801004943ca80170fd01101608fa060401850806a4a4163b92104120108304000110e05709793c8a154004
  | 2 => 0x2482052404121000a10884d120422010582808088406411022a044004090c024015201900a24aa40040440492020046468c0054162080180209024002048240706222025206080440400a00a020084664244090e842802
  | 3 => 0x52880834508480140b88d984748806001aac98804e4488027804001812050200a30327507308dc12481100104900186141518c83029ea188e4047830080240b9035b60c46002281001104890922d04a84686c175820440
  | 4 => 0x8a2008409220016002341a04181441040281108118088a20c1000142842000494204286a4140500800088500048cb1030102108600308228c500c080441001605911c900450900088840004124680980148282216810a0
  | 6 => ~~~(0xef7befdbf57ffd77eef8addff77defff5defefeaaeff6fd5f7eb6d77ffeffdf6ffbdba7d4fbadffdbfd7dcfdfeffddefdebfdefebeadefddbf69f7d7d6fdfefff27fb72e77ffbfbfcbddfedfbdbafb6feefc7d9ff96fef6 : Bits)
  | _ => 0

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
def ax95Perms : Array (List Nat) := ([[], [32], [49, 100], [49, 32, 100]] : List (List Nat)).toArray

def ax95Domains : Array (Sig × Nat) := ([(subcube 1 0, 7), (subcube 1 0, 7), (subcube 1 0, 7), (subcube 1 0, 7), (subcube 1 0, 7), (subcube 1 0, 7), (subcube 1 0, 7), (subcube 1 0, 7), (subcube 1 0, 7), (subcube 1 0, 7), (subcube 1 0, 7), (subcube 1 0, 7), (subcube 1 0, 7), (subcube 1 0, 7), (subcube 1 0, 7), (subcube 1 0, 7), (subcube 1 0, 7), (subcube 1 0, 7), (subcube 1 0, 7), (subcube 1 0, 7), (subcube 1 0, 7), (subcube 1 0, 7), (subcube 1 0, 7), (subcube 1 0, 7), (subcube 1 0, 7), (subcube 1 0, 7), (subcube 1 0, 7), (subcube 1 0, 7), (subcube 2 0, 7), (subcube 2 0, 7), (subcube 2 0, 7), (subcube 2 0, 7), (subcube 2 0, 7), (subcube 2 0, 7), (subcube 2 0, 7), (subcube 2 0, 7), (subcube 2 0, 7), (subcube 2 0, 7), (subcube 2 0, 7), (subcube 2 0, 7), (subcube 2 0, 7), (subcube 2 0, 7), (subcube 2 0, 7), (subcube 2 0, 7), (subcube 2 0, 7), (subcube 2 0, 7), (subcube 2 0, 7), (subcube 2 0, 7), (subcube 2 0, 7), (subcube 2 0, 7), (subcube 2 0, 7), (subcube 2 0, 7), (subcube 2 0, 7), (subcube 2 0, 7), (subcube 2 0, 7), (subcube 2 0, 7), (subcube 2 0, 7), (subcube 2 0, 7), (subcube 2 0, 7), (subcube 2 0, 7), (subcube 2 0, 7), (subcube 2 0, 7), (subcube 4 0, 7), (subcube 4 0, 7), (subcube 4 0, 7), (subcube 4 0, 7), (subcube 4 0, 7), (subcube 4 0, 7), (subcube 4 0, 7), (subcube 4 0, 7), (subcube 4 0, 7), (subcube 4 0, 7), (subcube 4 0, 7), (subcube 4 0, 7), (subcube 4 0, 7), (subcube 8 0, 7), (subcube 8 0, 7), (subcube 8 0, 7), (subcube 8 0, 7), (subcube 8 0, 7), (subcube 8 0, 7), (subcube 8 0, 7), (subcube 8 0, 7), (subcube 8 0, 7), (subcube 8 0, 7), (subcube 8 0, 7), (subcube 8 0, 7), (subcube 8 0, 7), (subcube 8 0, 7), (subcube 8 0, 7), (subcube 8 0, 7), (subcube 8 0, 7), (subcube 8 0, 7), (subcube 8 0, 7), (subcube 8 0, 7), (subcube 8 0, 7), (subcube 8 0, 7), (subcube 8 0, 7), (subcube 8 0, 7), (subcube 8 0, 7), (subcube 8 0, 7), (subcube 8 0, 7), (subcube 16 0, 7), (subcube 16 0, 7), (subcube 16 0, 7), (subcube 16 0, 7), (subcube 16 0, 7), (subcube 16 0, 7), (subcube 16 0, 7), (subcube 16 0, 7), (subcube 16 0, 7), (subcube 16 0, 7), (subcube 16 0, 7), (subcube 16 0, 7), (subcube 16 0, 7), (subcube 16 0, 7), (subcube 16 0, 7), (subcube 16 0, 7), (subcube 16 0, 7), (subcube 16 0, 7), (subcube 16 0, 7), (subcube 16 0, 7), (subcube 16 0, 7), (subcube 16 0, 7), (subcube 64 0, 7), (subcube 64 0, 7), (subcube 64 0, 7), (subcube 64 0, 7), (subcube 64 0, 7), (subcube 64 0, 7), (subcube 64 0, 7), (subcube 64 0, 7), (subcube 64 0, 7), (subcube 64 0, 7), (subcube 0 2, 6), (subcube 0 8, 6), (subcube 10 0, 5), (subcube 18 0, 5), (subcube 72 0, 5), (subcube 2 8, 5), (subcube 8 2, 5), (subcube 16 2, 5), (subcube 64 8, 5), (subcube 3 0, 4), (subcube 5 0, 4), (subcube 6 0, 4), (subcube 17 0, 4), (subcube 20 0, 4), (subcube 65 0, 4), (subcube 68 0, 4), (subcube 24 2, 4), (subcube 26 0, 4), (subcube 66 8, 4), (subcube 74 0, 4)] : List (Sig × Nat)).toArray

def word95_0 : Nat → Nat
  | 0 => 0x638135fc7c01cf60a6ad809218397f72870003e9a3611a8c4337e2cda8004c06e54586360060a8133405c15fc25500e2187c006c04c06080c6c032068b054099a0b0160182bfa2dca126c5410c1c1f007043e8b401188b72a3c25500e0011b346c0d50c963e1990e4b43070019e6c23f0412a84d06a7c4392c6a2c33362688c46a1a2ce545a33043e0023c0334b4a346a866c7fdfdfdfdfffffdfdff7f7dfdfffffffdffbdfdfdffffbfbffdfdfdffffffffffefffffffffffffffffefeffffffdfdffffffffefeff7fff5fdfffffff7fff5fdffefeffffffdfdfffc242c262c260c2603a61a242a232a662a262a43222322661a660123292123242b262b23232623260b2601a429e321a321a021e621a621e600e320a120c118a11aa120442824284328232862284228222802286128212840282028662866282628062862202220612021206020202020206620262062182218601820182018661826186110211040102010661066102610061632432411c00a12211a02201200ff83fc1a716f09600d27029aa6e81f817fe0ff01509d5f103ff05005df358e0cb463002eaaae2a2da9be2928a830a79f2b270e42801d33248ba5cb3e259f00400e3328a0824344af2eaaae2a2da9be2928ac2833309f2b27a70037a1848e25be331f003fb60e25c39f81c3444b46c63e33259f3527000e437ffffffffc644248234234013f
  | 1 => 0x66c0010e999201d148b46019b6da80395161c1e66b057fa82611e8e430f832d86c46a01829439516060e6691d7f1f540648f431f01f16c1070019a8023afe8b72d4130d88b4d0548f4aa180cdb71369161c0008b3c6a941391e8ec14d2a0868b0f9b02b150a04e261c095ca7ccd0d848350145b3d829b219c8180e138387c0060a2c8c9a2350d008c04c06e503b7db0180a8133582bf84ae406430a4f9500e0022c020ae093013018400e12026682300bfb96e40f033603116a81f0380e14a31ca8b3e3611b500e00268188b2191e664392c7c86cf0700182478eea1344c0603066438f8624b14c5a688d4621a30e545b60387c46d32a0184323e2c39d8458cd7f72a2c39ba4b2182c3e6c237617f9a0722cd84b22dca0013a4c0a8d198ac7832150886e25120d705340a8711b1a72b6ccc00464000934352181e060c22c02e2090792d82a90011a18d806c2a13bfb68240c8b25916e5b9015b100a8198388d1302cd400459992d820e36a015013234d47c4392c703e4b60838000ad42686a469f10e4b130f91982350110dba0e21828984b0f918d8d845b35002712c7c1c002612c8c4583c0c0170860241da8a5b748c00063601a8b05734178004814984b5c9b04b72d40388c1222c124e0012d301c4b39449504622c9c361f2392d9e0e000268ca84d10e4e3e1987c8e4693806861a0cc5632150a44228138944836728d47
  | 2 => 0x78a0a07a3c1b0e86d399a6fee53b9aee4d8371aa689a3925a2d503e070e2804d4d10c9746225328b25a1c7d8500202ea989c2247a34438f89600404e11a8c431e850983612cee6e10234606b356d0a2e5bad527066ba92d31ba0e4e1cb5045c8518280023aea7843ce119b43e12d0e3e0e25c0975a82191250b9361195046adb346d8b21d24964501cf27a8b1e0d8763b9ab608bbfb96e46b6c1d52cb69a010001c3709b1387c36110dbf6c269164b46dfd3082291409e4e2f1987c1c0022cba552de8eef509e8aca65d2a96ca6522c9409e4e0e262017725cf5165d2a96ca64d27938ca7c2d0f8b26600260a45845dde013d14140f8661f000506cd19fc383f2580cba552998cf852311989e98300f839a3275dc1224a822c968e33459b09a43267788846a5caa531419360663095840542793b666c805cea93725dcccc1c474dd2f00a80a10f166c218068846a5c01734ccdd108d2c8011d374ba187c1c4ca5c0773a8219111f77bb62d00763a96db0a85c920494692c2ee5d8459177f72dc96d0020a410c89023bddb16763aa00b601ec2139ab921920434592c12e5d845b350043dc96c3f72a192088018cc563c190a844231b8943e6e1ea1860e5178e44c001409ccf8a024d2021cc14a11d7f72a2ee4d80e6e86886089f11b16335fee5340e5422c8e45b95b0004b237748725dc9b01c19a1820963e459199ab94d0389
  | 3 => 0x3b8c560f3d363ff802a04c58ea4e1505baffc01fe00ff0042997fc01fe00e437d8a2e2d215ef09071d38eb147aaced0e85ac19de03a1672556ce43e5c957ca00ff004a1e9c8f2e46bd78b4d1d4d8a7fe00ff001f96f08c77917ff000f92e786e0a0a8b7473a50a22842935d404c34cba0f2850ac81a03d7663240cfd71586922f944d273ff004225c6177fe00ff00069a88007f06467473129d989dfe00ff006eb27fc01880dff0017a76cc652615f378ff80159d9201eba4ca927b40737c0c8f680522bd4d27802ff007f803fc01fe00eb6e844e007a2281852b4000018450a8042ca00c04029ca19280540900024003062e29cef28864008a0100814912008462ac5c8c4b9439bc22a40ecbf543ed53e35bd89bc563b93bb263a67b97c37f6b72a35e834ebb37632bab165b0b9af852ee3ae732e132db4ad28ac16ab49aa16a94da798269725b6a4e72409a2da2199a06a1f2b1dc51d2c1bad1a0719279836177696a795b714d793e59336926c10e610270f450ea48e168d460c8b8b158a668994091d876506cc054c83b882a801a580f7800c4e1f0d6ec223ae5509a1d0e6d85b1c5344b46c58f97f3693c9c7c1f070005d2a96cb8548b5f6dd4b3694caa53141f0383e00190c24f2b15372b6bed2cd84e2a950a4513093cc67c1f158981c29db8a0602f93b739abe85c968e39954e2533d9f01a70290f8001c2c5e10f413
  | 4 => 0xa80388880388680384a80384880384480318280510a8030ca8030c880508a80304680500a80300480298a84898a8029888049888029868089868029850029848029828049818c890b8c890b04690a84690a8028ca8088c90048c800488a80288880888880288680284a80284900284880884880484880284680484480280a80280884680880480880280480218a80218480208a8024c57ff007f80020840011ff0050937fc00d25cd10fde807fc0168a0ff007f8006c89fe007e8ad4ae61d840d1dbe1f7f8019d876e5fff00418d82076d2877f91aba23c8f6048f2f3c59306b8c25c23b6095793305676af2036940155d5344721c165bb0f014e236892642a70fd1a27aefd58218a11e01b67a076c70ff803fc01fe00363f7f803181fb6a3618f8e09ec44aa66d707dadbfd80faa049a70447983849ecab1e84e59a84d439f216774c1ac455016a676f586ff801ccd9fe00ff0067245816ffe00ff007f802c13fc8bdda68a3104641cd277cc72d9301005dc701b9081e2b484ddb84ad482e5206ecb45c95be491fb177449810fd06b9a0e2c9060214d3294f2344d52eaf7485b05a18195fc6df8d2f708bf58a2da310019ac067fc01211b254b4e0c2b02ea059ff007306f78e0d609ff0069a6fa48ccc0561776a1d2f9087c544177a890038b1c85d7d11463a4a97f3a66ff004420b0cad287f31738d04e41188c455c340e9f
  | 5 => 0xa70479c71e70689cba2712a90aae712b9cdd232a28ca62429898a62223e9cbb232b19c0c2702f9c032428d9ca32728c8883671669c4a272a89c39272e49c39473649cd9273509c65e72969ca5c32168c85e71979cc2a328a849c232f184bc632708490a32c384b0e32428493662cc98b3272cc8c936624c98932724c9cc4e32128c84a02139884a62139c84a72139cd5a1257046de12b6848da7237046da71a69ca9a709a9caea12549c554732d9c4b470ad9c0b4732c1ccb073529c54c73629c98c734e90b3a724f1cc9442a490a9672249c29670259c09473249cc9073009c80272009c60270009c004735c90b72725c9c476229c88a76714a90b2a720e90a3a12f29c5ca42f388bca22f29c9ca72731c5ca71729c51622c488b1671c59c412716198b8272e11cc8242a198a8672a09ca8473201cd6a429488a5672959c422428900a2202889ca22428908a2222899ca2472889ca2072888882671089c5ba42ef88bbc22ee88bb822ef9cbbe224188b0422c088b0022c19cb06715f1cc78733d9c56242d89cb62721100a4202919cb2212c898b22018684a1a028698a1a02068061a116a9cbac42ea90bac32ea8cbac22ea88baa12eb9cbac72ea9cbaa72ea889aa126a809ae726a9c9aa726a887aa71b984ae402b880ae672b99c8e201029cb98a84998a80998a8039888059888039848099848039808499808478c880588
  | 6 => 0x40861300f80281533405809008508568a82a61b06080a0082a0a986c26807c0700000e0f80f88b08f1b02344308f0f82343e29d0cc3604308f1186084308f0f82304315010e228478860f837c4308f0f8540462ef3041f446a7a10c1982588753a0013d01c11e23c3e19e10c360ae87c11e0a44786610e12c4329d4f40f86d2ee33c2183308c2a0864cf06810c4e0468da11efa89a2ee124678ad07c68021c2588f4f40700008d11e6797706633c0101307c11e21c2588653a9e81f0872a06084304b10e4f4a804b3041f1672ef4329e81615011a2196715010c1f1670d8122218a187c11e245f508d0cc21c258860f8d004639c11ab38091502c00709e0860621f08b08fbfeff7f3f9bcfe7f3ff7dfeffbff7fbf7fefbfefeff7fbffbeff7ff7dfe7f7fbfdfeff3fbfcfeff7fbffbfdf7fbfffbfdbfdfeff7fbfdfeff7fbfdfdffefbfdfdfefff7fbffb7fbfbfdfefffdfeff7fb7ffedfeff7fbeef6ff3fbfff6ffbfdfcfeff3fbfcffbf7f9ff7fbf7ffeffafdbfdfcfeff6fbbdfefd3ffedf6fbfdfedf7bf7fefff6ffbfdfeff7f3fdfefe7fbfdfcde7f7fdfdfe7fefdfdfeffbf9ffb7fb7dbefbffdfebffbbfdfeff7fbfdfef77fbfdafdfeff7fbf9febf7fbfdfefe7f3f9fcfe7ffdbedf7fbfdbeff77ffefeffb7ffeff7f6ffbfdfeff7fbfdfef67fbfdfcff7fbddf4ff7f3fdfeff7bbfdfcfe5fbfbfb29c0d242b49c5d
  | 7 => 0x5187c3042604783e10c4581f08f10c1984384b11ea8d4007c11cacca808607c2395993411e2188d83e11cdf846b9c52221c478660962194889811a0f84302c07c3604788d10c23c1f2ce1be2184788d0000704787c10cfa84384b4fc6e9690d807ca99420d811a2344988f10c23c4308f6802344308f12c6e83e34010e12c46ad207c0703300051e9b54d292518a75f527d11aa109a26811221872a84118218448025a4224460e510ca1000ad236045846a6850823cdd2ce2a04000880e2a0a10d81164fab386c28e10c070332847d44a13400051c23480150374a1080150374a1000100374541672ce2a06e8088da59c6e8a8100000540dd2ce0cc36934000126a38468002006e8a806659c0586d2ce37454177aa0508fa97720c10c1f046a7d41823c4683e11e2343e08f11a6081f08f11a12c4383e11a0700008f5dc2353e8864185404303e07c2183e08612a400c11502682181f0870960f8432d24d8a383e07c11821c258865a4a393603e0000703e066130e704b03e1b0230458980f82583328d11812c1f01c0002383e06611a21935ab607ca3148a8e540a10478860380cc158260480d13d0e50640a81d82107a0a013a7a048414000e5070678a62a6038218a60d82860a44a0021c83940e284030234461824f46c04c0862fe2604303e3044857717f508395409823609e84309800c060d8116024541530d85025fd3
  | _ => 0

def word95_1 : Nat → Nat
  | 0 => 0x84826b10c9e8430901129e84308b432450a627a18c070480b62709e95501c2002404490927a9e95501c12045880088360a405b00010e2581f08e10e4244303e12e4694c29059c0d0000e55082181902207a0c01403904e0dc12a1905e4e00f91b10c23c8c04b10e0000e03e7382343e11611e5c84308f2b4b384788d23452567086038234431ba0f823c9a08611a12c4383e0380004788d56c21d5991b10c23c0001c12c0f8461160f823c6d08611e1f06d8da000070333ea10e12d4088f1b00f94d19a5dca68cd08611e1988c04b10e0000e03e22c1f04791b5dca48cd0d85dc6684308f1c86088f26e2680704aa922a0001f51348044846f91b038a493715010c6684717f4dc23c3304b10ea483e03e0389b8000955144687119a1b421847bea1c42009408e7cee71453b81264686d0e21b42020103e7383608d08b268ee01f0d81c00708d0e21b4fa870bb80fd008473e71c00f88c28a0383608d0da1c20000e07e0ccfa84384b11ee71dc1181b00f97728e3342184781c234468142800480d4178270003944699a0706781303904a0900002a04ea00728351c8ad88f07c10c0a95b11e26846c150950024780e08c1ca2194201211a6697707c5229f44799a4fa0e00f0864fa6693b07c52223c002683041f00e0000100f83e0d811e4597719e10c1984788607c46c4308f07cbb84799e27e5403308f04c21c2583e500235
  | 1 => 0x618a604a5f0e5d4c5bca5a9458085706564455c854ce530a51c6510650444fcc4e504c524a14479644d2428e40d63e143b883a8a3950374a3608350c338c3210300c2e962bcc2a48294c27c826ce250a23ca228621c820d01ed01ccc1b441ad2188a174e15921352110810160d4a0c0a0ad20888078c061203c802cc014a0006c13410e12d5c2ef13421c4a2bb1062396405707c5f43e0870960f9740895d0e804688610eba00208d0cc21c2583e2702181a08910e12c1f2960f8011362960f821c2583e1120113611669a1f04517212422843887096a983d1160d41b8d80b65085c9470860381ac3b86a0dc9a1421721b0360468b61143604388a10c12c458d810c12c458861102344b9b022cbc0430881b0218440d810c2203e06607c2644b803110a5535ab316c0004383e21225c4303e11c4013f8901149fc430881de3b43e0ec1d419843a7f096f69ce0e510c0701f0001209fc258fa1e23bc768ec1d41803e2b110e1987d08603815c78a7f4ea4245b0871202593608612022472a8410c241362ee1125fcdda6c5082245b2ee4d823043a6c10ca99531ba11221c451ea10c2400e0870967a84301c10e2284301c10e12c4301c10cd342588b11612d3888611422c8499a4e2bb85b04b1164248008609622c4304b1169c48488b11a459388fa1e212d358885dc669358885dc2d8b910010c220430884d62204690912e21
  | 2 => 0x4340070040c78000004740020705484b4081400042040143860040400a800a000083c20c4042428285c0000180814845814041824311021182c0420c838d00c1804107004840c346c200008000c940404080050000800001010140028100034080000002854004800c840385c7c14481870301804007014201c00101400383800002c140c0000180434381c1c000004002800385024480400080c9c00400008002000042000100004001814182030080400081c3c04741010280034005c0040007c08001424000c18040c00080892e912c892b8d2a0b28d32693245122492147208320451fc31f8f1dc91cd11ac919c719071849174516cb15851507144314051393114b10090f0b0dc70d2308c907df040d028901890086ffcefe06fd44fcc2fc86fbc4fb48fa44f9c6f904f884f804f784f708f604f588f48ef2caf186f0c8efcaee86edcaec82ec46eb84eb06ea48e944e8c8e7c8e6cee50ce382e34ce1c6e10edf4cddd2db9ad846d796d4c6d40ad2c8d1c4d14ccfcece0ccc90ca86c9dac686c5c8c4d4c244c1c8c0c6c00ebe46bd90bb86bacab994b70eb558b252b00caea0aaa0a68ea4daa1969eca9d8c9c1299cc984a970e954a940c9288918690c88fcc8e528c0c8a848a10880a86ce850c8390818a80487f487e5c7ac879c6790478847806775e73907188708e6ece6d0c6b886a8c690c679065886488638a6246
  | 3 => 0x54e1d9b393fc00ca343fc00aead7fc0080293e759d1bd7fc00e110fd0c9b0667fc00757132a0300c30595691054a35e05438ca65b5381c88a3c7a7d045ff0021f1c75387fc009f309df42d10b6f0800117860555f55ffc004686242dd0099c741065430b065ff003fc00de5a62878913cffc0099109029583350fcebf3c55534b10a0c509ab24d6588de99be35adea5f8562cff003fc0081074b99fff0034546ff003fc00ff003fc005cc2e6d03ff000db31e84ce4dc05018bfc00ff00030fa6bba7922dff001a064ff0010c311a1affc006d5a9ba5b7892d0e9375d6f6115e66522327ff003fc00cc9c719723547d217a11873fc0038ce1c5523e42cc5f98c49bfc00e11587e05ff002b2915bb8db5f8b22d406be5fbec48143b977b1c54b2bf4c75a66a0ac5de437ae9dd0c94d967313ae64b2af51a7924d86833d190793a3c1c78d4a6ec40ff001d68b4a77aea226876beb1ac726f40f66f6fda734eac4ad82fff002def6dea073d5cb1534d93cff002a188ff00098f1ff003fc00cb4187a1b4a6b3fc00786dbfc005233d50b9b7533fc00ff003fc00ff0032d16ee5f3e179bb87bad271a8519c5c1f04a12097c529d60e7da257a26f046e85a5995419cd174bf87c13ff003fc0066b55c0ae8c8d441b9f1af02050a0005c3900b4741414a8782c9000044c1c1c2008353c181038801aac30441558f06d286c08000420040
  | 4 => 0xca32457542fa7ebc3fc00007effc00f0d83a047d6506703dff003fc00c90732225ad411b8f74012525ec2b8026545ff003fc00ff002f00fff002db49c42974092ff0035dd24a608a90f9e6f8b8ec195d6ee8592c060b225f00f5dd30032b1308ff0024affff000b62fde2427d42432ebc9f093bb6a074f2478f7454e7045cf4ec2ab44efe4c0fd8f0d5a9e435aa556939cf716e0ad5fe490ea09f575137009655d2c5f136cdf656c547e88b2f618131c96646ec8ae129605d5a2f9a34fad3769865de28c09c3299d6d36793871467b706763b40f1673d72a9f2ca4b7a45b22baf5c25e21486c8fb266c4d22be13e207d6e137ddd8655bbfc00a30ffe1057648e4ab3ff003fc00086376c335551f94daf94c1a1b0b45955d1cff003fc00ff0031559c825ccde6ff0025902ff000e4f84ad877120ff003c841a35cffc00c3afdb320ff003fc00f802ffc004a06fbaefd363ffc00ff002262103205d58eff003fc006c69ea84ce8bcad2020f403fc008f5827b14ff003fc00e881bfc0097b95a2138f8e47b21cb0aed0262950ca83c519b32cfc45616b1baae0dbc517cb2cfd4b4857408851b37927e87c9554e9cadb1cb4da3874b24d58d3b6ca49dd215240e50a75101e32e19a41db03a8fc507ed425ac232e7d6ad78a23113b1e00c363e6bc1680c829d1d112d9de7b3c2c3bca01f91ab863ed1f07ec1fd5f177b1d9c5df35a7
  | 5 => 0xc8d3b94b4602b2cc801a154cf0d3e528a044ac25b4d453295391908890e2360da61fb0180345dea83ecad77922e22a3ce563ff002c5fea40aaf7546bc96f92472315aec1cd450a928cd38e654b539dfa8950571a473c4b3ca5c3aff001f70f0021f14322a72d2dc3ff0014a79beccce4dbee377a1b55ab26d5f6313fffc00007d3fc00c332c84be9b4eb68c8d94bbfc007d19ffc00557aacd930853f946d6cc7f8a7dd72e1c8b7020dc9a272f30ea0bcf052540001865fda32ccb15d2d1161e551923c4bc69bd232190b2eff003fc00ff0031f284f8ffbaafff003fc0076c6d8d3da6d8ca5cc12ab66446b37ad9b13ff002d12a8f82015e036905ff35ff00239dc4765bfc00ef00bb230c3463fc00dc6abfc00145c22a51905effc004538aeed7252f7fc007f588108c29685815edb787fc007d15c682ea235421d9a57deda63ff001fc21cd221b137b14f86233db485a6b7ff001405fd169af587c58ec5d2b7dc2bfc00d5cb3fc00ff00299d1b718425fc52d5a4968960c01ec717c655e2a5fa7ea1841d83e7c63e3bf0aeb81e082c9b71e39a8a23781bc2571ab6c68477e9d4f3c4bbd1a98dbce336276288137c7e97252088729584d2a4890f9a7621150405d82c91a8421a92d85b5e4fb175d2510d9af7aa01d5cb61083c6aea719a6f5461e1784d5ddcc75691c32f7f2182e8cde0447ae319a475a6cd4486b858ca5c745
  | 6 => 0x45cc44010454c44019bc63fc003e143996bb6b9c34c01e87e685a5e089cc48ac5f4f161ff001bc4e354fffc0077723fc00cd3f7fc000f253fc00ea663fc009f3fa0c99ff003fc00ff00084a7ff003fc00ff00145b4872c55f43b58ac6d91ff001fa07aa56fc9d55f927e011f867258a034aaffc009f318e09c9dc3a373ae51effc00a0d05f87cff0039b2bcebc6073b6823bfc0093693fc00ff001618692d46058aff00110246eac464ea64034ad54485bda07361593fc00b39568340a597ffc005bd3b6b0975734e34a8567bcc05ff00326df1e70bfc00ed727b629d3828375f61893fc00058676ca6ff0030ad96e39ffc0057067fc00a3d60f1ffff003fc00b573bfc00ff001457604263fc00aacf9009eff0034948a0a6ffc00ff000611ad18401cabb83e640a1974c991aeef7f51d12459ef4c353ed3f69666705be913ac4db2859123d602c3d47a01525c36bc7723c22ef801e8f43471e557cda31396635bda37d2a97920bff003fc00ac7b7fc00399b7fc00e760fdc1fc08482c5888245f08b8c4c4c9eecbd30f8442f1e89e6e6f9d655f38235df0c17c370467f140d3e0d9a54eeca1506bf63abb4265605b29b95f2493e4aa51b3f0ed1d4d7f37338f9407c79e06f45e62de0bf8c2c0f1891e05d343951d8b81b3762db7245cbd57290abd88241efd60a1f3483cbcf333997cf68ce96375b70d2492cb3567401a234c
  | 7 => 0x1dac42b54856b08ad5115ae820dd051090b7d216fa82a9d0552a0aa51131c02e3405c6a017a016f20286ce4ce6465404ce6424402ce6423402ce5cc4401ce5cc2401ce54c4401ce54c2401ce5424402ce5424401ce5404401ce4cc2401ce44c2401ce4423402ce24c5401ce24c4401ce2465404ce2424401ce2404401ce04c5424ce0445401cc5c44401cc5444401cc4823402cc4423402c454c4401c45425401c44cc4401c25cc4402c254c44028e6c644028e6c454018e6c444018e68854018e68654018e68454018e64454018e60454018e5cc24018e54044018e2cc5401885cc2401865cc2401864cc4402845cc44018454c44018454044018238c14028054224018054044014e6c644024e68234024e64454014e5cc24014e5cc04244e5c224014e54c34044e54648024e54640024e54444014e54248014e54244024e54044234e54044014e4cc54014e4cc24014e4c224014e48234024e44c14024e40454014e34c14024e2cc54014e2cc04244e14020024e0cc54244e0485c644e04858234c58024014c54244044c5402401485cc2401485c244014854c0c64485404401465cc24044644c4002464402002445cc44014454244014454044014444044024444044014254c4002424cc24014248c14024244c2801424404402405404401404cc24014044234024024c24010e64854010e64454010e64444010e54044010
  | _ => 0

def word95_2 : Nat → Nat
  | 0 => 0xa7cbe5ffaba7cbe7edf37c9fa6f9fa7d9fa3fabeafabeafbeafabeafa9f6bd8fe3f8fe3f8ff7cd7a7edf33eabf3e8ff2fcbe3faf72f8febecef3b8ff3bceebb8fe3faee3f9fb2f8ffadbf27d9f7cef3a7bbbbaeabbcebbbce9fa7ef3aeebebced7aeebbbeae3eafe3eafabeb7afa3fabe3f8feafadebe8fe3fcef3b8fe3fd767d9f6b7aeeb7aee3faee3f8fe3fabe3fc7f1fc7f1f8febdebb2f8fe3f8ff2fc7f1f8ff2fcbf2f3fa046140106815750269a048b416d28369504d2a0073409968232d0265a005b408f6812cd0263a02c74018e834c50571a0b894196e81add06d0a004119452224e5077ea073641e6a83d34644f988df4143a2252464bb9899d40062703b4e04da0093411268030d0161a00c34187282155052aa023940ca2829450142a088540d76810b50592a041540a42814b5048ea0959386b242d6504aca031b381b68236ce008a08964192a8345504a120ca92155681425004788a8d1151e825cc45b888b5540aaa83ca505a8a055141d7e800348506a0a64418968061502b2a0ae52144a42abd022fa045c418b8833c48578a08452148e8391107c090b0d4115e8102485049ca3f4147a82d84447c90af94109a4293d0402a080540c0a80665029ea0b4641dec838050400a06014000483e4502b708b6c116de82db5056690aa1415d4839dd033ba046f40cde814150735a046b41e0283e550488a09114
  | 1 => 0xe4412704106818e08100000c3161e1822302080000204102180488a022008214047000000507080410006401060811312182c00010040080822d448893102204418730c6144298410860cc1082104208c088110220440881102600bfb7c0f89e83d1794ee5d8ba9742e65c8b88710e25c03816fad45a5b33636c0978aea5b2b41692c0582ae955298530a65492814f09e5382704e49852c2594a2925212304628a1152184308650821042084504a013f6784ec1d93a0740e99bb340684cd9842c4548a1131254468849011f23c0780f21c4340688c91822e4580b01602c0580b01622a450899120244448801021e4380700e01c0388690c01842d04809012024048092100208380700e8148200400840c81002202004008012008303e3dd10e0f81f03e07c21c4383ea1da2844aa63d412c0e55663c12fa097263c2181f03e07da03cf78310c22c438860380f90c80007c7a80003e2120f9009ea1208f5252344321980e066000071f508fec4fab3501c0000f81f7869d80f81f39c07c0f83301c0382343e0660009a34575411f37baa11611e237af26811e1e446f5ed15d53aa08fd15d500e000039a29672cef3da2847800d141983e20c10c0f81f03e07c0f84308610d3db9c03e10c1f01f06607c2344787c10c0f81f5a89eebe8fe3f8fe3f8fe6f9fabb9be7b9fabb9ee7b9f67e8fe3f8fe3f9de3f9fbeafaa3fabe3f8ff
  | 2 => 0xda767304f2602bfc0096580a5852a26f0e8c535c7e06d206cad674ff0021cadf20bf0d385f3c3fc00860e36d110e06ffc00962d2ad3fab5e6b07c4467668bcad4cabd7beb08749fbe6a26e90b5e436302da41c3a0fcb2106fa4c7f96c291bac5156d906b8f659748a537a4b1d43a2c91ecd2bb7d023729f1d4af87bc2d9c77804c9429e2beb4548b2942ce4694f2a11db6158b066ff002c89e982580831bf62af1deb89635931d46248c1da923c1e8a2f91c795867264ac572458dd104352a44a4dff003e99e1c76fc24b9c04a157f8a1ec513b200f3fc006e8750a538c17ae17090980848863492f999a74bb04ab4024dc5d15e32949034a5ae6d2c243b28a6578503dcba1944bfc006e7363da01e6570e85c3253fc00ff002b9096d3745dddff003288a335d4d2716f1b99209f7312bd8d1c9a6325acc0acf1bf24061b40f2c469f14e965dd3a87c00a265541055b0a8020577fc00e603bb550b9a0ab968f447f05b74a438f1a5b01115176c93c87a27a71f79617248d4f830ff002a58cff0005cc39c04edc3339608e0a6060c68412040150e0c9121a18092b8043010604cab4a15ca556048800d440040068482101c1030f24f0200040352025111000000100014240200b93023091c10340020a711140218f820610300022421200104331204303124858104080080a603018268f0906740140a1c095043810110145000
  | 3 => 0x3ea4c046ba185a5d5999a497d295e331e11e371410a73015ac856624044f99b05c0625db75ce0f5a33ce96791425c89fdec456a239c0948c953263d88e7a2816cdc82331722a23356ee828fb199cc42ad762ce1f2ab4305e73b165b65cbc0047fc00566a2027b2053184d5c55213c73d46d7058fff003fc00ff0026a68ff00195b3ff002c0efff001aceb3e6606cbbff002240841368dd938b188688cdd1bdac770b4b5b615ff003fc00ff003901607407fc00e2453fc00ff003fc00ff00135b06134c39917598ba129e104190d17c17eb9df060d7fc006f41ca14bff00380f70d027fc00ff00308f862913fc0059907fc00ff0035a7638887fc008b3508e64864674256994d06050ff003fc00ff0019465ff00361c9ff003fc003914c1d51ff003021b453f900cbff003fc00ff003fc00d09dffc0024363fc00ff003fc00075faa48bd59f3fc00ff00358145d5cbfc007095129626f57d38c78a0e9247a2c3835d18d3255b48d436208455ff003595bff0007e84ff003fc00ff0004994611a3fc00183a7640bb628d2a5cc42f7cc76d854bfc003e49f20800551bd1135a054f648634149219034cd8dacb82e37c27189c028a4c9183a01e205b96d00a88bbe4c6e034bfc008b5f1ee37d939a909ddb2b3fc002a123fc00033f7fc002e8fffc00f6073866bfa7ea9dd5ff0008d92ff001d1e3ff003fc00ff003fc0008611a851
  | 4 => 0x6243eb693fde7f1e0e721f68b70c2a0fed3062cb6756a9983695081b801146a6acee675a859ebf466b81b48b69abdff104e96483383654e8807335f1edbf423b4432332190ed9f47071105b9b6ba4ac74bde607a356425a7a168d1dcff833ac8e5c0282ec987b0dd2071ff001dd37cd07c8986054187c29625a74046977d7fc00f49e0581a876930823117bbfc00484c16dc7d901d4e2bb92abce59d93d15c86c02fc85b16598f802c680cbfc00ff001168dff003385293177fc00b54831a29ff002a84aed1ab8147ff003e0ffff003fc00704953879294a85e7dff001085a876dbfc00ff0039cb2837d0a68bc26f4887513557fc00a179828fb7491b8cb5ec58499abff003fc0070138d0b7c1597cc4262a040d83273855c22649a91ca19633ffc00829b85dd31b19348ea130f7a52172166425e882135df3ff003fc002b6b795a220226f980ff0017935be6bbfc00419b0d472f65937d169b1d12ddcf12cc10c9ff003e661ff002f97ac4207ad5c6e7c7fc00ff003fc00611ff88a87f8efc96da65be64a2e53899d9b92035155a0a45e3a83ce21dd891401034058d88b2844c1348e5936db0bbd10fde03149ecc41349e05f54f92867f967d786c8e095662d0a8c56249ff002dc6bd8309f157886060c3bb706569f0d730068782711491c5268cd9d67ff003927edf2fb85289a53e360d276866d8e4c23aa6453a37885c1e0
  | 5 => 0x804005fe0078d8edb544bfe027a87f803d83e935e098f150d9d4eff9489a04ff017c518e9ff800157d71d0c6ff805611fe03fc0174c620b3e2414938271742152ffc00e0298a48e38322ff80ff01048ffc07f80ff00013f594a10bff00c327b8352adff01fe01a40c4af1f66884268bb6b53818c0295ecc8d1aeabaeefa07e7036e6fac5811ce0d75c0edc77fc003bdff004001c61fb9f14633468200880d0241b100651a80539ce739dcd62c6318e210850000009028a447a8d37d446812529e56cae95d3e23d5aab556aad569ad552ea756aa9d52ea1f4aea574ce9d5aa8d23bd216d20cd20ad21ad27352445254521352394c594c49d26192874c47d247d26d52825220524052305205d22ce08e64454015054e34c40025054644c40025054644020025044e14020025044254c40025034e14020025014e54c4002485404cc24014644c44020024254c44020021064854044011044e1402002045ce24c4401f63c7fc005d80d8cb04526848c5ff003fc006b7df312bb11a4cc7e91330a2116d84fc9447379c8e8e1318f2d73589be815eff0032e1ff99ca24035724934df043421cdb164998a5f8338fdcd7540d3fc00cb0ff353dca11d4a57909d789226652764062159831392261c316cff000449fd190f6997e1507fc002b35b749c877a604e7ff0028c4b8f50e4c61d58bc65af6f82dcc249c1273c26ed9559e4e252e
  | 6 => 0xff0293ee939d5adff3f50f2adbea8ed2d66e7b3ff07f83fc0425ff050b438fe43ae0960000000001345351255255915915155154b50dea09d479a8f5317262fd441293a4ca069c2804005a48a069c28040052502089c2804004a4aa06988804004a4a8c8988804004a4884a988804004a42a0a988804004249a0c9c2
  | _ => 0

def ax95Words (i : Nat) : Nat :=
  if i < 23 then (if i < 8 then word95_0 (i % 8) else (if i < 16 then word95_1 (i % 8) else word95_2 (i % 8))) else 0

def ax95Count (k : Nat) : Nat := match k with
  | 10 => 1
  | 9 => 5
  | 8 => 73
  | 7 => 217
  | 6 => 164
  | 5 => 23
  | 4 => 8
  | _ => 0

def ax95Path (k : Nat) (i : Nat) : Nat := match k with
  | 10 => 0
  | 9 => readCompactBits ax95Words (8 + 12*i) 12
  | 8 => let v := readCompactBits ax95Words (1171 + 16*i) 16
    (readCompactBits ax95Words (1063 + 12*(v >>> 12)) 12) ||| ((v &&& 4095) <<< 12)
  | 7 => let v := readCompactBits ax95Words (20729 + 18*i) 18
    (readCompactBits ax95Words (19289 + 24*(v >>> 12)) 24) ||| ((v &&& 4095) <<< 24)
  | 6 => let v := readCompactBits ax95Words (65188 + 19*i) 19
    (readCompactBits ax95Words (61372 + 36*(v >>> 12)) 36) ||| ((v &&& 4095) <<< 36)
  | 5 => let v := readCompactBits ax95Words (87964 + 16*i) 16
    (readCompactBits ax95Words (87292 + 48*(v >>> 12)) 48) ||| ((v &&& 4095) <<< 48)
  | 4 => let v := readCompactBits ax95Words (90569 + 15*i) 15
    (readCompactBits ax95Words (90089 + 60*(v >>> 12)) 60) ||| ((v &&& 4095) <<< 60)
  | _ => 0

def ax95Live (k : Nat) (i : Nat) : Nat := match k with
  | 10 => readCompactBits ax95Words (0 + 6*i) 6
  | 9 => readCompactBits ax95Words (68 + 7*i) 7
  | 8 => readCompactBits ax95Words (2339 + 8*i) 8
  | 7 => readCompactBits ax95Words (24635 + 9*i) 9
  | 6 => readCompactBits ax95Words (68304 + 10*i) 10
  | 5 => readCompactBits ax95Words (88332 + 11*i) 11
  | 4 => readCompactBits ax95Words (90689 + 12*i) 12
  | _ => 0

def ax95PoolIDs (k : Nat) (i : Nat) : List Nat := match k with
  | 10 => let v := readCompactBits ax95Words (6 + 2*i) 2
    let n := v >>> 1
    let bits := readCompactBits ax95Words (6 + 1*(v &&& 1)) (1*n)
    compactIDsFromBits bits 1 n
  | 9 => let v := readCompactBits ax95Words (783 + 12*i) 12
    let n := v >>> 7
    let bits := readCompactBits ax95Words (103 + 8*(v &&& 127)) (8*n)
    compactIDsFromBits bits 8 n
  | 8 => let v := readCompactBits ax95Words (13156 + 16*i) 16
    let n := v >>> 11
    let bits := readCompactBits ax95Words (2923 + 9*(v &&& 2047)) (9*n)
    compactIDsFromBits bits 9 n
  | 7 => let v := readCompactBits ax95Words (39942 + 16*i) 16
    let n := v >>> 11
    let bits := readCompactBits ax95Words (26588 + 11*(v &&& 2047)) (11*n)
    compactIDsFromBits bits 11 n
  | 6 => let v := readCompactBits ax95Words (71473 + 11*i) 11
    let n := v >>> 8
    let bits := readCompactBits ax95Words (69944 + 11*(v &&& 255)) (11*n)
    compactIDsFromBits bits 11 n
  | 5 => let v := readCompactBits ax95Words (88669 + 5*i) 5
    let n := v >>> 3
    let bits := readCompactBits ax95Words (88585 + 12*(v &&& 7)) (12*n)
    compactIDsFromBits bits 12 n
  | 4 => let v := readCompactBits ax95Words (90785 + 2*i) 2
    let n := v >>> 1
    let bits := readCompactBits ax95Words (90785 + 1*(v &&& 1)) (1*n)
    compactIDsFromBits bits 1 n
  | _ => []

def ax95Bucket (k : Nat) (i : Nat) : List Nat := match k with
  | 9 => let d := readCompactBits ax95Words (843 + 3*(i % 4)) 3
    let off := ((i/4 + d) % 16)
    let v := readCompactBits ax95Words (855 + 13*off) 13
    if v >>> 5 == (i/104729)%251 then [v &&& 31] else []
  | 8 => let d := readCompactBits ax95Words (14324 + 5*(i % 75)) 5
    let off := ((i/75 + d) % 270)
    let v := readCompactBits ax95Words (14699 + 17*off) 17
    if v >>> 9 == (i/104729)%251 then [v &&& 511] else []
  | 7 => let d := readCompactBits ax95Words (43414 + 8*(i % 249)) 8
    let off := ((i/249 + d) % 887)
    let v := readCompactBits ax95Words (45406 + 18*off) 18
    if v >>> 10 == (i/104729)%251 then [v &&& 1023] else []
  | 6 => let d := readCompactBits ax95Words (73277 + 7*(i % 197)) 7
    let off := ((i/197 + d) % 702)
    let v := readCompactBits ax95Words (74656 + 18*off) 18
    if v >>> 10 == (i/104729)%251 then [v &&& 1023] else []
  | 5 => let d := readCompactBits ax95Words (88784 + 5*(i % 21)) 5
    let off := ((i/21 + d) % 80)
    let v := readCompactBits ax95Words (88889 + 15*off) 15
    if v >>> 7 == (i/104729)%251 then [v &&& 127] else []
  | 4 => let d := readCompactBits ax95Words (90801 + 5*(i % 6)) 5
    let off := ((i/6 + d) % 21)
    let v := readCompactBits ax95Words (90831 + 13*off) 13
    if v >>> 5 == (i/104729)%251 then [v &&& 31] else []
  | _ => []

def ax111P : Nat → Bits
  | 0 => 0x7d6ffd5fffff6c6cc32c675ffffff3d9edca3916fdf7bef98dedee19903099d10099c77ffff9f3ff3f2398df964310624670f0cf3e7f1eec479c10300f18c6fffe67299e4698d0673a00105a6ec408f5ef5220
  | 1 => 0x5f5bfffb4f3bb9c3f2c508dfefed3fff9f1dd9e35f1dcfa7c2f0967271ed70200a023fffb7ae9e3bdcbcf5fe9cbc62d4e9d9347a8b1c65519002610231fdfcbdbbb314e1e9d283cadcc9c000112adeb3348980
  | 2 => ~~~(0x44c08010cb1244263b66bd0060520000c8c81c15e0722d1a27cce385998c57feb7f80012408c21e222c80e09ebb4278a0ff88fc625e05697dfff3cbb5014031224d31ec499b41fa1fefe8a3b7fc1823aebffc : Bits)
  | 3 => 0x77affaffbcf19fbeec9e632fff3fecff13b5bfddfee761d7e00e19e5df88c5cee0027fffec59eec6e6dc1ff3f9b8df5ba67e888ce142e11b1023e2c884ffc77365dc276439371c7e25662820113b3964988c54
  | 5 => 0x7ef7ffedfdf677733972fcbfded7ffef6eeee7fb9e1bf75a333e660c6dd38e3e0b7c7fa57fcf5d3c637feaed7b3f82a891a7cb75449f85a1e8ec03c337237bde03ccdaf9910d63b118ade083a251e00bc235c8
  | 6 => ~~~(0x1020004801721920884c6430080000c9030039129c11c503c1ae3645f5e1989e0a9a072400491c20441018df113c92c2c770f04f8d1fe591d2ae63f23838c6de01f60ef1b11492673cedf05a7b7be8f5d3ddc0 : Bits)
  | _ => 0

def ax111Q : Nat → Bits
  | 0 => 0x29104a0800010921451982881031001124980392000a12812001004424824089d2004631c483201212000100604c22720018803212104150802020a4410c0f0e224098240080006060c084061c008e1a91200
  | 1 => 0x20a42088b88402280d1ae62d0480089078008eb0b4b4211a080241010802890ed1d92e5932a0081084084088832d499604539321257432414421082101d968a99b11004108508100100b4550a1ac9e93348100
  | 2 => 0x44c89022c21044023a643d648208204cc9214c09acd0cc120180c10011040156257f394c30500a01012040241720c108f4c263c4c9a58c800485080a2ae370e1582801024040a00a061a63d0a23e51c504002
  | 3 => 0x8520d200108600102611890e014002882cb0009020984a001218008200412310e2440a68c1080044080122114408221a1080c0a4883049c209001040c24855264402400112210500644282448422164880850
  | 5 => 0x10810020600880440840142124004400410104008400840444000a290200040200291004100450800442844001204000a04201400084800110084100202120400800228800120a10820820902014008420488
  | 6 => ~~~(0x6fdfbff7efadfeff77f7dbfefff79efddffff5fffbcfffed7f7bddbffb7eff7dff77f7f7df7dffbdf5fe7effd7f6fe7fffedeeffffbbddfffdfbdfbfeebef7fef7f7affbfd7fbbf7bffdbeff7ff3edfdfbdfda : Bits)
  | _ => 0

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
def ax111Perms : Array (List Nat) := ([[], [33, 48, 101]] : List (List Nat)).toArray

def ax111Domains : Array (Sig × Nat) := ([(subcube 1 0, 7), (subcube 1 0, 7), (subcube 1 0, 7), (subcube 1 0, 7), (subcube 1 0, 7), (subcube 1 0, 7), (subcube 2 0, 7), (subcube 2 0, 7), (subcube 2 0, 7), (subcube 2 0, 7), (subcube 2 0, 7), (subcube 2 0, 7), (subcube 2 0, 7), (subcube 2 0, 7), (subcube 2 0, 7), (subcube 2 0, 7), (subcube 2 0, 7), (subcube 2 0, 7), (subcube 2 0, 7), (subcube 4 0, 7), (subcube 4 0, 7), (subcube 4 0, 7), (subcube 4 0, 7), (subcube 4 0, 7), (subcube 4 0, 7), (subcube 4 0, 7), (subcube 4 0, 7), (subcube 4 0, 7), (subcube 4 0, 7), (subcube 4 0, 7), (subcube 8 0, 7), (subcube 8 0, 7), (subcube 8 0, 7), (subcube 8 0, 7), (subcube 8 0, 7), (subcube 8 0, 7), (subcube 8 0, 7), (subcube 32 0, 7), (subcube 32 0, 7), (subcube 32 0, 7), (subcube 32 0, 7), (subcube 32 0, 7), (subcube 32 0, 7), (subcube 32 0, 7), (subcube 32 0, 7), (subcube 32 0, 7), (subcube 32 0, 7), (subcube 32 0, 7), (subcube 32 0, 7), (subcube 32 0, 7), (subcube 32 0, 7), (subcube 32 0, 7), (subcube 32 0, 7), (subcube 32 0, 7), (subcube 32 0, 7), (subcube 32 0, 7), (subcube 64 0, 7), (subcube 64 0, 7), (subcube 64 0, 7), (subcube 64 0, 7), (subcube 64 0, 7), (subcube 64 0, 7), (subcube 0 2, 6), (subcube 0 4, 6), (subcube 6 0, 5), (subcube 1 4, 5), (subcube 8 2, 5), (subcube 32 2, 5), (subcube 64 4, 5), (subcube 9 0, 4), (subcube 7 0, 4), (subcube 14 0, 4), (subcube 40 2, 4), (subcube 65 4, 4)] : List (Sig × Nat)).toArray

def ax111Words : Nat → Nat
  | 0 => 0x44808807fe07f81fe07f814b4b7511e60eab6e77ac51eed608f31a4a016d3102ae54d016c4a3be60dc7333e37f800c7ff81705a6421ac7f81fe02739ca3ff81fe03c2f18120ad269f5c05a6b549473b8cc56f07874a8d00bad2b82428000718c6018002229f8b78a9cf16b3d8ef5c3d527513d2734030e8c3434b6a289c94a203466d134828b04a4006056d87342869d064a92865e543c0c7d42013256926a70269256014e7f32906c705e54682a523c360c0142887e304c06566a866c2654685a53a07f6f424c0670926a3c0c006654596ea08532305054063c260c62509b6f4e93422e824a4a7e9088928704546426066202500b682ebb2b3c924aae3d1aa08512ba7e2606873564468a4a920adf65354f29a4d0947c928090883833983b2810342d392c2691982606884a0c829ade9134527f04d0de7c90869280828c269200912c80867030203c0088852c827c0104de84d07c8e9291a880828c3c260c928e8166354f3482047c2422160e201e18d000122892e728bc04820cd00c92260086bb2884047c704a3c8886842c047ddf7f7f7f777f7ff7dffffff7f7ff7f7fff7ffbfb7f9217262e4c3c985930b260e4c0904aa110c2234857888d111a023cc46988d00de6054220844130a11200511108901100d004b6ff289ff3fc64c839c056d61b8547940601251bf26342a590e129e0125486267df827d03fff8444223f
  | 1 => 0x7f9fe0cbf5ff806140002fc650c92002085cbe31c503c21d9337d41120f10a84a88908898680957c17c7f8073bfe0ff07f83fc1fe03c6f757b0fc883fb8002647910f88fb07b5e63aa167f83fc0a923ccfc2b157fe03b9ff81c1c5c63e2ff8052dfe08ddff82c523202e508c0067d875d68c5c557552e44c38c2c329d1cd0f30c309900158a89030361242636c010f7e6c2720886854221c4f00246c2f049df91104872410d0a8409e591178df911048435efc8843a425c873217204eb85468fd1243281e04b2d00124de7d3d9c8f85d21d2cc2250f1bc9238142247e131f01a5a1e001c8927c3c094647c390e1123f09cb47c06171e09261be1f08a0194974064312d20de491f90c8843220fd4e132210452e1e10fc87afb5f2ed779f7ddefd3fbfcffddbfdfeada42e4e4890b1392270a844a9c75382c7354e6a9cc2110c7310e6e88998884510a88908880704a88898708898680890a8
  | _ => 0

def ax111Count (k : Nat) : Nat := match k with
  | 10 => 1
  | 9 => 2
  | 8 => 21
  | 7 => 15
  | 6 => 2
  | _ => 0

def ax111Path (k : Nat) (i : Nat) : Nat := match k with
  | 10 => 0
  | 9 => readCompactBits ax111Words (8 + 12*i) 12
  | 8 => let v := readCompactBits ax111Words (422 + 15*i) 15
    (readCompactBits ax111Words (338 + 12*(v >>> 12)) 12) ||| ((v &&& 4095) <<< 12)
  | 7 => let v := readCompactBits ax111Words (4257 + 15*i) 15
    (readCompactBits ax111Words (4065 + 24*(v >>> 12)) 24) ||| ((v &&& 4095) <<< 24)
  | 6 => let v := readCompactBits ax111Words (6613 + 13*i) 13
    (readCompactBits ax111Words (6541 + 36*(v >>> 12)) 36) ||| ((v &&& 4095) <<< 36)
  | _ => 0

def ax111Live (k : Nat) (i : Nat) : Nat := match k with
  | 10 => readCompactBits ax111Words (0 + 6*i) 6
  | 9 => readCompactBits ax111Words (32 + 7*i) 7
  | 8 => readCompactBits ax111Words (737 + 8*i) 8
  | 7 => readCompactBits ax111Words (4482 + 9*i) 9
  | 6 => readCompactBits ax111Words (6639 + 10*i) 10
  | _ => 0

def ax111PoolIDs (k : Nat) (i : Nat) : List Nat := match k with
  | 10 => let v := readCompactBits ax111Words (6 + 2*i) 2
    let n := v >>> 1
    let bits := readCompactBits ax111Words (6 + 1*(v &&& 1)) (1*n)
    compactIDsFromBits bits 1 n
  | 9 => let v := readCompactBits ax111Words (256 + 10*i) 10
    let n := v >>> 5
    let bits := readCompactBits ax111Words (46 + 7*(v &&& 31)) (7*n)
    compactIDsFromBits bits 7 n
  | 8 => let v := readCompactBits ax111Words (3001 + 14*i) 14
    let n := v >>> 9
    let bits := readCompactBits ax111Words (905 + 8*(v &&& 511)) (8*n)
    compactIDsFromBits bits 8 n
  | 7 => let v := readCompactBits ax111Words (5796 + 12*i) 12
    let n := v >>> 8
    let bits := readCompactBits ax111Words (4617 + 9*(v &&& 255)) (9*n)
    compactIDsFromBits bits 9 n
  | 6 => let v := readCompactBits ax111Words (6769 + 8*i) 8
    let n := v >>> 4
    let bits := readCompactBits ax111Words (6659 + 11*(v &&& 15)) (11*n)
    compactIDsFromBits bits 11 n
  | _ => []

def ax111Bucket (k : Nat) (i : Nat) : List Nat := match k with
  | 9 => let d := readCompactBits ax111Words (276 + 1*(i % 2)) 1
    let off := ((i/2 + d) % 6)
    let v := readCompactBits ax111Words (278 + 10*off) 10
    if v >>> 2 == (i/104729)%251 then [v &&& 3] else []
  | 8 => let d := readCompactBits ax111Words (3295 + 5*(i % 14)) 5
    let off := ((i/14 + d) % 50)
    let v := readCompactBits ax111Words (3365 + 14*off) 14
    if v >>> 6 == (i/104729)%251 then [v &&& 63] else []
  | 7 => let d := readCompactBits ax111Words (5976 + 5*(i % 9)) 5
    let off := ((i/9 + d) % 40)
    let v := readCompactBits ax111Words (6021 + 13*off) 13
    if v >>> 5 == (i/104729)%251 then [v &&& 31] else []
  | 6 => let d := readCompactBits ax111Words (6785 + 1*(i % 2)) 1
    let off := ((i/2 + d) % 6)
    let v := readCompactBits ax111Words (6787 + 10*off) 10
    if v >>> 2 == (i/104729)%251 then [v &&& 3] else []
  | _ => []

def ax127P : Nat → Bits
  | 0 => 0xc1f2283873ca6006965c501c3f705cbb0d61b0e00c1de3d7e5cdfe738ff8afdd57a3e5e51d3ffce06afecb8cad782c633f972f482871b42fa150686e2b00a0a362b46e01a879d6c80ab41aef40580e80b618862c035bca2de18c795b1fd967147145ae429e6854d1a19d0608c96b01100c080ca847aa209022da2763d92220
  | 1 => 0x403ec2c3444c0e731f21ea01f183ab94044002440311c0be5bfba7cfd7f3eefcfa7f4a3f51f1878d27d39733f61bd14fb5f2c1fe71478644b54480de80ddbc074d4807f4e8175c1e92701bad0002e1810e086020403c8795ea73e7e0753cf675c7d61983a8e1ca83a0d4d03d1166701c41e000e101b04158ccec99842d209844
  | 2 => 0xeac38d86889f9186247e802e58d08ad9500805098860135f3d7ebcf7fce7bf4f73b7f3ce9f623cc79c92eb7c47a39fd2783b7ac0a228cbdb5040dd09dd80ea18074f4a07dc2867611ce1a4113a7d8214204016068342b8bd74bcc3afc68f6ea6e9da2170cc1393342e4917e18c0f8080a405ce0e0e04100b0f0dce9194520103
  | 3 => 0x772c0138f308e1a3c0470cffa104132278b21a00050061c3ee9f7f16fefb3fff9fe97c70e67bd819d8fd529c7b5419fcbec3bd3303d70c13c1873f960e0f0fda789070380ec3848160ff40e1438700c01109e1190084ed1e733efc2b9ff189db19a3a6040f6403eb428e61c63e7110660a120130001845cb71b1723a0620c488
  | 4 => 0x870e1c173783345c7910535c22396c20c20160110a5080ffffe5fbf96f7cd7d93ea9dd951a9ec0e2ff757d2b0f5566335fcc56ecb43001a82e594e746124f0bcdc82c851f1558128b70b4b646cb85311260600800f08adeb9fc57855bce23799fa4d7a2ab10074695d51e401c7b08a89042806c126a03015f25220f8d80a0164
  | 5 => 0xb83122fc87b00e0c98c9b5a1ce42d42b07f08066308f21bdbcfe562fabfcf1f2e5feb43aa9ee677227ac08c7f9feae8fc9fd29d18e87f8049aba20a110f24347b2b5078b1616a21e6d841bd29002bc60c930017870307661db8a179e6adf178827a89e5154f9b502012a2a3ae198641259d03010d14882862f50054750855c10
  | 6 => 0x1dd07d4148647199e3a8238207ec05c7ac069c8a54a20f7ce31bfbf99d1f4f37efde8fcb7e85fb3f5b0fa5f4b0eae7f18604ee185dd8366b403ea303b3501561003db98023e81ae10314e40e95fd242a50c18e4190c15276845f3bd6a160e87efe04c0dd330e0c9cbe360ad872068560a203f10250030c34008f2548ab04229b
  | _ => 0

def ax127Q : Nat → Bits
  | 0 => 0x81200100088240021410002430000824082044b00d0008016808d0011880828414120200505000400085040840400006300020848208c008020d16200040021a4104016018004482800100540c20031000801014040490029018c004310484104504400428208004021800008c01101480a080108404a009020d00622412020
  | 1 => 0x84800800a0220108000410880060102820b33403980c0894125384c411434628d01a0a0010500281020002022202400800a080801a259502740c9020080d00716c458102408024da0420cd0c402a08080105040412000294a82346c04108c435c54210802041408020805011000040014341480914e0497088ac898425201004
  | 2 => 0x1008106002004800520002410401050003255814120acd1b207c00968066244612944108800214001402010840810500000a2000921e218b20150080cca80518410c01a88201e2145440aa58013000004420481008a010b840b8432a048d06a28980214080101210080804a0000500060191810e4684910a0d090e9114120002
  | 3 => 0x102040c4010100090c10000804011850c807c40d38302ac842910c89838c50b4110504200801080c40010080010a090010102c098082880e141c242804c048018483427034301f910105103c01700808000a08002c9085314a823165109c2182002040900014202040104242011040c3a0122080c36095111723202008480
  | 4 => 0x20202180400480208408240008060244004883a065213260c90072296e1091912c2084040888004060102400011020120400502720c0406402c0260413107a8600a21a40340e0901811700209e013040184010402005a44316443015b8623108320500221000202110402000830086a8342012702109240562522068c8080140
  | 5 => 0x41404401100100c1002208043008080008004a8006205429002812032224800204a480002020610201200805100088040854004120026085001002008520138a012202c880008004004522201410208200028202010834610088110c2886120000880800042884000102020a0018248a10808014630080022640044150804810
  | 6 => 0x204800a01100206080000308010a00010502100a90420444103406804014310a00a008300000828080180a00068024100000c1400411040560824041011204008c19000500c088200224500880900042210200804100206844200d08020a01c620080190004000c841008405002022022405240102100740086010889040209
  | _ => 0

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
def ax127Perms : Array (List Nat) := ([[], [65, 50, 80]] : List (List Nat)).toArray

def ax127Domains : Array (Sig × Nat) := ([(subcube 1 0, 10), (subcube 1 0, 10), (subcube 1 0, 10), (subcube 1 0, 10), (subcube 1 0, 10), (subcube 1 0, 10), (subcube 1 0, 10), (subcube 1 0, 10), (subcube 1 0, 10), (subcube 1 0, 10), (subcube 1 0, 10), (subcube 1 0, 10), (subcube 2 0, 10), (subcube 2 0, 10), (subcube 2 0, 10), (subcube 2 0, 10), (subcube 4 0, 10), (subcube 8 0, 10), (subcube 16 0, 10), (subcube 16 0, 10), (subcube 16 0, 10), (subcube 32 0, 10), (subcube 32 0, 10), (subcube 32 0, 10), (subcube 32 0, 10), (subcube 32 0, 10), (subcube 32 0, 10), (subcube 32 0, 10), (subcube 32 0, 10), (subcube 32 0, 10), (subcube 32 0, 10), (subcube 32 0, 10), (subcube 64 0, 9), (subcube 64 0, 9), (subcube 64 0, 9), (subcube 64 0, 9), (subcube 64 0, 9), (subcube 64 0, 9), (subcube 64 0, 9), (subcube 64 0, 9), (subcube 64 0, 9), (subcube 64 0, 9), (subcube 64 0, 9), (subcube 64 0, 9), (subcube 64 0, 9), (subcube 64 0, 9), (subcube 64 0, 9), (subcube 64 0, 9), (subcube 64 0, 9), (subcube 64 0, 9), (subcube 64 0, 9), (subcube 64 0, 9), (subcube 0 2, 7), (subcube 0 4, 7), (subcube 0 8, 7), (subcube 0 16, 7), (subcube 3 0, 7), (subcube 5 0, 7), (subcube 6 0, 7), (subcube 9 0, 7), (subcube 10 0, 7), (subcube 17 0, 7), (subcube 18 0, 7), (subcube 20 0, 7), (subcube 24 0, 7), (subcube 33 0, 7), (subcube 34 0, 7), (subcube 36 0, 7), (subcube 40 0, 7), (subcube 48 0, 7), (subcube 65 0, 7), (subcube 66 0, 7), (subcube 80 0, 7), (subcube 96 0, 7), (subcube 12 0, 6), (subcube 68 0, 6), (subcube 72 0, 6), (subcube 1 4, 6), (subcube 1 16, 6), (subcube 2 8, 6), (subcube 2 16, 6), (subcube 4 16, 6), (subcube 8 2, 6), (subcube 16 2, 6), (subcube 16 4, 6), (subcube 32 2, 6), (subcube 32 8, 6), (subcube 64 4, 6), (subcube 64 8, 6), (subcube 14 0, 5), (subcube 19 0, 5), (subcube 21 0, 5), (subcube 26 0, 5), (subcube 69 0, 5), (subcube 74 0, 5), (subcube 84 0, 5), (subcube 104 0, 5), (subcube 3 16, 5), (subcube 5 16, 5), (subcube 6 16, 5), (subcube 17 4, 5), (subcube 24 2, 5), (subcube 34 8, 5), (subcube 40 2, 5), (subcube 48 2, 5), (subcube 65 4, 5), (subcube 66 8, 5), (subcube 80 4, 5), (subcube 96 8, 5), (subcube 11 0, 4), (subcube 13 0, 4), (subcube 25 0, 4), (subcube 35 0, 4), (subcube 37 0, 4), (subcube 38 0, 4), (subcube 41 0, 4), (subcube 44 0, 4), (subcube 49 0, 4), (subcube 73 0, 4), (subcube 82 0, 4), (subcube 88 0, 4), (subcube 97 0, 4), (subcube 7 16, 4), (subcube 30 0, 4), (subcube 56 2, 4), (subcube 81 4, 4), (subcube 85 0, 4), (subcube 98 8, 4), (subcube 106 0, 4)] : List (Sig × Nat)).toArray

def word127_0 : Nat → Nat
  | 0 => 0xc531a531a431c331a331c231a131c731a731a731a129e729e719e70d2235213567356735273527352125670d670d270ba433a233a133a033e733a733a733a223a023e723e713a713e703a7012431233121312031673127312731672167116709270b233321332033673327332733221b201b671b271b271b67032700a530a430a330a130a030e730a328a128e728a020a118e718a70824304330233042302130673047302730273020206720201827182718211067102710271423413403223221a13212211a11203202a02201a01200afc7fc1d4d0aedeae5afbba76e7b9e909fe066c3dd9acbb02ff07f83fc0199d70e0ccb19fe0ff0048cb53fe02daff83ca8be6aadefbc2d00526107f8081008038574279a548261dcf2e6b92ca146280739418b09503b00d680149413124b49c946c08811904b49c9468803949291cb4948c0860a1086904b4948c0c9a387030282018100924b49c948c68391030282018100904b49c948c6a3038e03820181008c8b830c2094c9c948c6828b1f134948868d8109838a05828084900201031ecb4948c6898192c9c688008d089e1249c8c0888c86838181021d91c9c8c6888c009d11494088060b8983020105040083829c90cb49c94688018703820180901c49c8c9010b07ffffffffffffffffffffffffffffffc23223413213403203202a12202221a11a01a11201200e159460c07f
  | 1 => 0x64f2b941c0d08f1881c2606a130e5729938c0e127935094a303829c248d932394a303829c260d052991b29101c65726478194a300700810065029e4c703dca4621c94848820794c9c6128380380c0401520132a4f2964c703b8c439246a84a84763cc9a4a303829c260c53490f0403bcae4e0a5888c6147941c0e868918c2520620834132a91ca460d638498ea143848c60a47a8341608521c0e8401248e521d0a8c1afff7fbfdfeff7fffffeffffffdffffffbffffff7fffeffffffbfdbeff7fbffff7fbfffeffff7fffffeffffbfffeffffdfffeff7fbfdff7fffdfeffffbfffeffff7fffdffff7fffdfeffffffffaffffbfdfeffffbfffeff7ffffffdffffffffffffffdffff7fbfdfff7ffffdffff7fffffeffffffffffbffbfffeffffffdfeffffbfffffff7ffffaffffbfdfeff7fffffffbffbfffefffbffdffff7fbffffffffffffffd7fffffefffeffdffffffffffffffdbffffff7fff5fffdffbfff6ffffbff232f272f2727271f270f2705a335e72de72da72de725e725a725e71de71da71de70de70da70ea336a32ea22ea72ea726a71ea716a704a434a434c334a334a334a234e72ca72ca724e71ca71ce714a714e704a7062436232e272e2726271e270ac532a532a532c432a432a432a332c232a132e72aa72ae722a722e71aa71ae712e70aa70a213220326732273227326712670c22346734273427346711
  | 2 => 0x3264e11e3e7a958d1620d05820471f95c98ec9e238d40d1b1323e4c779582c68d404018080207cae4cb0461de3c471a89c160903cae4f1e238d0ee0a46cae4c471a1d93e0b041d91b1f13cae4c470327c6a130392e4f1e948d0ee0d0492e55238f8d1ac7709834164b95c9a36343b828f32b934846876589e248ae3ac1c389e2289456325eca60c8e3a1a08a3315894488d941d43a331534e5306228ac64743a23c64451529134a43a23e0e25941143a33152684074828cc561c574924a1c3a91285783b8913d05158c94a7924c1c5525191d0f232578a8e89a3a100f30692874662a699265103198a8e8703a8ca262a572941a090c4d428926c82988731265657298f10ced3b072be62139482920726b3d412070a829886d12260e72b8f10ced249d8615e18393541c6847893233194caa3443052b9e80e060200c04012301731948963c42393ec220f06826632b94c78847304862788862338d46c3984a758b23cae3e25054926a769d50430cc9f2140e0a351a0e51b958930e479484a68f49d8498a4795ca63d34390382c0a03030224798ca144a8391ee3e2495860e60a351a0f11b95892f54b0949268f46c848820f98c7a48c595331a87293cc0e0750aca234ae7a873247093ca122307a829847057294eb2b938724a310451c260b0330a4870a1cac3b273a2794a09182f0d0719587651230435460f4a184c1a0a0f07
  | 3 => 0x71a95e5729934690628911f65280262a1461f1d4417e1f15ca64cf6268ec107c3e884584d1d82148a30f8a9447d948864c4c528ec122d28ca246091d1f26a0d044ba87283dc7a74fb0d4d1b216494bc1a0a371ee4d9594c7c5a089d3e8520f0881c18270b82e632993c78f46e4884c114308cc0f71e923ec3617051b8d87a4cc9c5b1f0449274fb068584209081ee63298f52992130d83c0e2b0b1e9a8c908cc6508e8d8b64d913f28414f88dcc65142501e9473046488f72848281f61308829182048c7c573194c9c34a07d4ec2606978410940663243644a14d42c7b94c9b0e7e5082a7ca69d1026b2993c79f52e3d36424410883c57318f4964ccc6a1e8821198ca64d1a7d338f4205412c4e38883544f2a478940e386a088404b1c81928d712cae3e271c81894f71c81894a84fcac4f1f12129509f1c81a3a44a14a0fa39033dc4d1b1c81928d48f278832b1329c4a071c470f0751c2a40d1a57878f0d693c9e0c911329cf8491b3d0d4963c89e54489187a22373e2c0372783ca91c78341246e2684231a4791363e57262487a227d1b2c65727833d892363cc98f08f838d94cbc3c23c384913cae4f06348d97a44a11f8f236843da221c3d46191083c9364d7d3e89a2a365029e4f072649c6cc43c358821f95c1a44c91b348f0743c4896236532ca210b26cae4d091b1e64e223b1e206365829c260a94358ed93038992
  | 4 => 0x32a97b2b8348e60d5943211c742bc1a44a655239490e86421ab3195ca64d04471c11b2681299548e528441e0d03122504f98ca64f1f09244164595c991212603541e0d05822693195ca64f1f0324c261107122504c2813e632993c7c0c910883c144428168906625cc63c6395c9c105c668441e0a26350904598ca64f2b0323c1a0b0481a684223cae531f934c11853068226842234ec272b9434e4f1e4624c1e0d058240d349d4c6572993c791893094cc1c5303118873193ca23d26468441e06244a0844c29118a04f09cc653278f2411a1107834160798ca64c9c462463d290982c104622108c45109170b4482c12e57278f492748d0814c1a082411e632b8fca2448d0883c144c21148904509cc1ab2993ca9188f0682c12069a4ce572993c7a608d06822688309249e72b94c99a71e99234260f03cc653278f4a1181708232449093cc6531e7d84413318f49654d3933311a1104161d92509cc63c7795c99a4fe468441a0998ca63f2a91234220f0682c0f319446e572667234220c388491f3195ca64cd28d2347a0d0581c6cd5192091e111aa1b20ab94c9e54530747c6008030100637198c0180e05cae53278f23104531a83c1a0b0481c6e3519cae53278f149060d058240e37192342235078c124f395ca64f1e2920c1c8d0682c1236418c9272b94c9e3c53038d47a11068246e579548e531e6b20c7a1308834160
  | 5 => 0x19d3197498e31883981a16d4165895481447935512ba117a10348fa80ea78db60cf48c640be68b180a15896688948803879407170636856404e783f50356828481f4816400e700091657064489180d4284e269329714e57298fc1c4892291208c4d831463f319430c489029130a05a2419e631e2318e570712161985226cc0932a6aca60cd11223a1d0a83120a44798cae531f12230984a30138c4502f170ac442dcae3c489d84c49249b106531f094d17d389aca8ca2594c7c25365f21c489394c795d35092a043319449e3e1254259531f98ca0c0a11284a4c7e48cc24f298f848d4be20cc63d25093f97f3195c7a485f1284998be25176631f1249424fe54cc6511b092fa3b3195ca1a057098919c744789663282246c24a821170b04b93c18f22d0e4e88d369d2264d33838b48cce9d2c0d486c4ca2461c868b26e449d4da644229ca64f0716871245225118a04398ca64f064813c385236108cc5c2c12e6327834945a1c23148d44632178a84b98ca60d2316870850c821488c4398ca64e2d0e230a52624139a8d798ca64f06472411c910f4a1f0f429138884395c1e4d247c2389c4c21188a0442e168b04a23c9e0f2a924e91c8e20c99489f83cac39249d2f15c4c321809c482bcc1ab299548a208e9d87a6d3499cae5327834b91c8e9224e4f06a0299fc7d93c1a54aa7a2394b2b98c9e0d247c238f08e2dc9e0d245
  | 6 => 0xa584b2d2db28fcbca0503adc552a41258e98626539e3206bfc00eabb706a6805e9e9568719464fc4ca746865074500ff8026c737a8242a5aea27988c133add2d30ba3043cf6da4608a39a430c4dcd7a777d3d4684801a6a6490f6ad6c5fd0e0eff003805ace234b2864211e990b57400c7d29f0608c34fc353634aa16c67664eec85287e5c120791ea28c7228a983445cbe6601600028002c8002a0028000664823e041824060a800a086900410111000440d1000303000c5021e2410000041a804089a82a5ca0000000801c040001e4420010683010e080010a182830400a230a2c080000008600701030e0028006082893f67675b674f7f405f35672997173f1057064efd46f54eec4ee33edc4ed34eca2ec54ebc4eb35ea84e9f66935e88667c766e76605e556649364356398e285e1d760f5e0445fc45f43ded4de445dc45d455ca45c26db545ad65a175938d826d756d687d5985495d3e952c751e9d0b64ff84ef64e374d54ccc54c254b874aa4ca164956489ac74946274549c41843164256c18640c4c0343fb63ef33e953df93cd83bd43b573a75b9cab873b804378736abb534b4a6b3d4b343b2d3b263b1f43172b124b09430132fb52f13aea6add62d152c772b93ab23aab5aa03a9982893a8252783a7142694261924f5a444a3b722d4a24421c6210420849ff49f641ee61e249d941d131cb39c459b941b171a33
  | 7 => 0x3d8676855cb3ca117906920825dc86d4c33fc01e6e6483bcbd57bea4de73920c124b3fc01231d4ea3961b50de352afd7098c13bfc00530163817f803fc01ecf8ff002009f8545fe00ff007f803fc01fe000f5c5f027fc01fe00128a730be0141fe0083a27f803d92bfe00ab688eaf4353648ceff007f802856f212e6ba6ff803c5da9aa7ff007f8017d01fe00a341af03cf4cf5a456499c998fb153a42c0b20aba45bcb2ac88e614b707fcdbc9a7ce39b9c8ec1c9e412b9e3ff2b4aa9e8f62e6897d4b2c7db80e2118757ac579672a4d355408f9d86a8ce62b4461d3a34ed9a1c84ca168fbed4420f342490a5e497889a38497879c690ffc01fe00a58b554fd9627312dea6b7f803111dfe00ff006347d75b3fe003309638a8e5ea949c012bdd1335915ce78ff003429aa1c586ddff007f8005588d69dff007f803ba4dc2530a1945ac2352f4e54068d2b1d7fc0121092339298f03d83fe0057a1a50d601631a1cf503cb2e7fc01763d519813c0c7aa0094ced4d7f80182a7fe00d101c8341708fa8dbff007f802f4fae89e9b51bb2d3fc00e46eeaa2ae2b3fc0034b34d7664ca7fc015ec61d2ede911a21f5d4ff38b8eaaea8d81d0091921538ffc01fe0096188415b9cf7fe00b15fac3a6340d77127f7c9219b6a31e83ead11394e39d65069349914621e819fa8194b704646ed5ef3cd52ba741832a9b0bf23ca62dd3fce95
  | _ => 0

def word127_1 : Nat → Nat
  | 0 => 0x484d9c48499c48479c480d9c480b9c48079c48039c288d9c28879c280d9c280b9c28099c28079c084d9c08479c08451cc8091cc80314c80d14c80910c80d0cc84d0cc8090cc80308c80d08c80908c8029cc8869cc8489cc8469cc8449cc80a9cc8089cc8069cc8029cb08c9cb04c9cb00c9ca88c9ca84c9ca80c9c908c9c904c9c900c9c884c9c880c9c708c9c704c9c700c9c688c9c68449c680c9c68029c504c9c484c9c48469c48029c300c9c288c9c280c9c28069c28049c108c9c104c9c084c9c08469c084494c80c94c80894c80490c84690c80c90c80890c80690c80490c8028cc84c8cc8448cc80c8cc8088cc8068cc8048cc8028cb08c8cb04c8cb00c8ca80488c88688c84c88c84888c84688b04c88884688684484c88684c84684c84484c80c84c80a84c80884c80684c80484c80284a80884a80484888684680484480280c84680c84480c80a80c80680c804808846808804808802806844806802b652cb52cb8a23cd187350445d64f5267664e4766141bf47cca7838ff00501bffc012e1d4d87474d33d3e0c05260db405436178e58ff001d172c804fb10592f8bcab5e41920a7e3802266f1d6224a7d8524aa1546ffe005005ff802896c8d3169a007b843a82c3058335a4c23fc016608ff007f801d143fe009c437118625dc98e70a7d3837c346d3600ff0010bdbfc01fe00ea836e013fc00422057571689
  | 1 => 0xa0c87a0287a00cc8cccc84ccca0ccca0667a0860a0861a0660a0460a04609c261a0260a026120e60a0e60a0e56a0456a0e49a0848a0849a0249a0248a0249a0e48a0e2094c208cc21a0a20a0a21a0620a060a94c0a90c0aa0a0ba080aa060aa030e84d0ea0b0ea090ea070ea023e84c3e80c3fa0c3ea0e3ea0e1a84c1a80c1b9cc1aa0c1aa0c1aa0e1aa0f0284d0280d02a0d02a0902a0702a020694c0690c068cc0684c06a0c068ca0684a1684c1680c179cc17a0c16a0c16a0c1680816a0eec80ceca0ceca0aeca08eca02708ca71a0855a06bca04bca02bca0e4690c47a0446a0447a0247a0247a0eb6a06b6a02b6a0e1e90c1e90c1f0cc1e8cc1e8cc1ea081fa050c8cd0ca090ca070ca04c8a08c8a04c8a02c8a00c8a0ea7a04a690ca690ca68cca7a08a6a08a7a06a7a04a7a040490c050cc048cc0508c0484c05a06f890cf90ccf88ccf908cf8a0cf8a06f8a040090c008cc0084c019cc009cc01a0883a0c83a048290c8284c83a0c82a0c83a0882a0883a0483a04148cc159cc149cc15a0c14a0c14806de8ccde84cdea0cde808dea08dea067ba087a8cc7a84c7ba0c7aa0c7a8087ba087ba087ba087aa087a2087ba067aa079cc8879cc8499cc8479cc8459cc80b9cc8079cc8059cc8039ca88d9ca84d9ca80d9ca8099ca8059c888d9c88479c880d9c88079c88039c688d9c684d9c68459c680d9c68099c68059c
  | 2 => 0xe4ca0eb890cb88cab8a0ab8a08b8a06b8a02b8a0e2514c2494c2494c2490c2490c250cc248cc248cc25a0a25a06ca8cacaa0acaa08caa06caa02caa00caa0eaba04aa94caa8ccab08caa84caba0aaaa0aaba06aba04aba04aba04aa204aba021d08c1c84c1ca0c1ca0f0490d0484d04a0d04a0704a0504a02ee90ceea0ceea0aeea04eea02d494cd48ccd484cd4a0cd4a0ad4a06d4a043da063da023da022e90c2e8cd1a88d1aa02b5a04b5a0cb5a04b5a021888c189cc18a0cda90cdba0cdaa0cdba08daa085fa045fa003690c37a0837a0836a0837a0e2c90c1290c13a0812a0813a041320e12a0f16a0916a0516a00b1a02b1a08b0a08b1a04b1a02b1a003284c32a0c32a0e0890c0884c099cc089cc08a0cfe90cfe88cfe80cfea0cfea04fea00e684ce6a0ce6a08e6a007da02ce90cce84ccea0ccea08cea0469a0459a0458a044ba084ba084aa084ba044ba044aa044ba002290c228cc22a0823a060c90c0ca080da020ca0310a0910a0510a02a9a08a9a04a9a00a9a08a9a08a8a08a9a04a9a04a9a02a9a00fa84cfaa0cfaa04faa02e08cce084ce080ce0a0ce0a08e0a02d290cd2a0cd2a08d2a0473a0873a0451a0051a0e2a8cc2ba0011a0514a0714a00afa02afa06afa02afa00308cc3084c319cc309cc31a02028cc0284c0280c039cc029cc03a0c02a0cf284cf280cf2a0cf2806f2a0087a028684c87a0c86
  | 3 => 0xa96a008c8ca8c88a8ca0a808ca8088a80a0a6c8cac088ac0a0ac0a0853a0852a0853a023a90c3a8cc3a88a3aa0b08a0908a0708a0508a009da0693a0493a00f4a0af4a08f4a04f4a00ea90ceaa0aeaa08eaa06eaa007fa00d090cd0a0ad0a08d0a06d0a046ba044094c4090ca08caa0a04948ca94a0a8a8ca8aa0a7890cc6a08c6a04c69c2648ca64a04c28cac2a0ac2a045c8ca5ca0a5da0a5ca0a5da045ca044e90cba8cabaa0abaa082894c2890c288cd06a0906a0706a0506a029a90c9ba089aa089ba069aa069ba029aa02fca0afca06fca04fca029094c909ca90a0a91a04f094cf0a0af0a08f0a04f0a028494c8490c849ca85a0a849c885a0884a0885a0285a00e490ce4a0ae4a08e4a06e4a02d894cd890cd8a0ad8a08d8a06d8a047494c7490c749ca75a0a75a0a74a0a749c875a0875a0874a0874a08749c675a0675a0674a062690c26a0827a0626a0627a0426a0427a0e0e94c0e90c0ea080fa060ea060ea060fa020ea020ea0312a0512a02ada04aca04aca04ada02aca02aca02ada04ada04aca04ada02ada02aca02e294ce284ce280ce2a0ce2a08e2a06e2a02d690cd6a0cd6a08d6a06d6a0439a0639a0f18a04b3a04e88cce8a0ce8a06c4a08c4a02c4a0e62a0863a0663a0262a026320e62a0e62a0e5a94c5ba0a5aa0a5ba045aa04be94cbea0abea08bea02bea0e4c90c4da024da024ca024da0e4da
  | 4 => 0x7df7fdbf773fdf79fef73fff7bfdffbfcff3fcff3fdff7ff7fffdffffcffdef7f7ffff7feffbfcff3fcff7ecff3fcffbecfffedff3ffdffeeffbfdffb7effbfcff3fcffbecff3fcff7eeffbecff3fcff7fdff7ffef7bdeffbdef7bfeddff6f7fdefdf7fd7f7fd3fcff3fdff7fdfdbfcff3feff3fcffbf6ff3fcff3feefbfefd3fcff3feff3fcff3fdff7fdff3ff7b7edf73fcff7ecffbecfff9ff3bdef7fcfeffeffdbfeff7fdffbeeff3feef3fdfbbecff3fefb3feffbecff3fddfffdfffddf7bfdffffeffbfcff7dcfffffffffdffffcff3ff7fdfdffffdfffff7ddf7fd7f7fdff67f3fcff3fcffffffd7ffff3fffbff6ffffdffffcffbfefd3fcff3fcffff7ddff7fd7f7fdff7fbff6ff7ffff7fffdffefd3fcff3fcffffddf7fdff7ecffffdff7fffb7ecff7fdfb3fffbdef7bfef7b7edfbbfcff3fcff77dff7edfd3fdffbfe7fbfcff3fcffbfcfff77fdff7fdfe5fdb7effbfeff3fcff3fffdfb7f9bf6fd7f5ff7feffbecff3fcff3feff3fffbbeefb7edfbfe6ffbecffbf4ff3fddfbfefb3fcffbf4ffb7cdf3fedf3fcfe4490ca48ca988ca8e8ca8ea0a6e8cb0aa070aa030aa090aa070aa070aa030aa029fa069fa0300a0b00a0700a02f69caf6a0af6a02f6a0af6a08f6a0289a0c899ca89a0a89a02dc9cadca0adc9c6dca06dca0adca08dca06779ca77a0a779c677a064294c3494ca28caa288a968ca9688a96a0
  | 5 => 0xbe25836383586eca7338e52a1c0b14a8a78e0a51e42c1b09983638290d70b2201052b830a58e0a61b86dccf31896158e0ae1b025cc60d8e0ae29b2a82aa49fe258e0d78960c1be3835b2b830a58e0ae298ae1b8a7cc52b896398306dcc60c1a32b8e0af83638ca8a42bd2b836382c0a41b8241a614ca6382bf7fafeffbbcffbfdff7fcffbfcffbfcff7fdff3fcff3feff7fdff3fcff3fd7fbfdff7feff7feff7fcff3fcffbfdffbfdffcff3fafebfb7edfb7edfbbeff3feffbdcffbff7f5fd7f5fd7fdef7fdfff77fcff3fcff3fdef7fdff3fcff3fcff9fcff3fcff3fdff9fcff3fcff3fdffcff7fafcffbfcffbbcff9fd7f5fe7fefd7fdfd7f5ffff7fd7f5fd7f5ff7fdfd7f5ff7fdff7f3fcff3fcffdfdffffdffffdffffcff3fcff3ff7fbfdff7de7f3fcff3fcffdff7fbfdffbfdff7fdffff67f3fcff3fcff9fe7f3fcff3fcffdff7fbffff7ffffbffff7ffff7feffffdfffff7f7fdff7fdff7fdffcf77dff5fdff5fd7f7fd7f4ff3fdffffdff7ffff7feff3feffbfcffbfebfbfefd3fcff3fcffbfcff3fcff3fdff3fcff3feff3fcff77dff3ffdf7fdffffeffffefff7ddf77ddf77f7f7fddf7fcfff7fff7ffffffcfffff5fffdff77dff7fcffdffffdffdfd7f7ffff7f7fdffffdff77dff7edfd3fdf7bfeff9feff3fcff3fcffbdcf7bdcffffffb7fcffb7eff3fcff3fcffb7cff3fcff3feffbfefb3fcff3fcfff9ff7
  | 6 => 0xe0fcbf318e14829c78521604914d8e47829e0e5272fcc6382387029a065272fcc0718e08c2986c1ae25cc72f839498e0a786b278e0a51e0a7868ae2386e5472e23638648ca2a08f8932aa919384e3832e1a520ae57c28533261b08eca638230cb52e25cb86f8e61a328b58906b52821cbb2b86e382906e1af33cbe2584e382c479868a58e3262986dcc6382be25830a83507ad1e25cc47829e3831b26acc0e280c989638d18cb038d702b46c9970326258e0ca6cc79208a7cc52f8e34631c16358c823f2f03a92284838e0cb4c0712bc798e07a350b04a730103478e0a31e06e2b8c829f2eca6394c3471e60e32347cbe391e0cb0a8b0ca0a78e478d18a386b461af2f8e0703286bcbe0d896394b8b01b7318e52e1c0ae5216f1fe258e0ca3d40e30871ccc0dcb8a51e1498e09e1de38350cb03c1102f33cbc7f4b1498e071cbe254b40b1f9498e0cb5441702f2f890778e0ca269234b63829c78c9e394b0a6348a6246382c0f4870afcb840d1e1b4b6382986e1af33cbe2584e382c06e1af33cb86984e382c0b1cb86f8e52d868a61af2f83068cae382c60cc9e38298b01bf338e52d896142b87466c791f068ca1474c52b8e60f838694ac7c51d318e07051e0d4ad318e0a509868a4731839474c6381d1474ae394c60c290768189e9ed2b4c6382906c263298e478358b01a2938e0703586dcc6258e60c35aa49fe381c0d61
  | 7 => 0x6c1a731c9f323153c2ee4fcc542280b61bb281a733c9e2d845342c64fcc069508f503c18ca31f208a38b33e35c17ce730318d703e2d06328c797120b3e35c1229c0ecc3294cab31ea4631d2f04c0fce62d05f30acc7a918c705b4107b3ed1c0e32b1e9bb285c47b20b398b416d134303e2cd1b289bc1f1eb3831e201e6314bc726417a3d62c1a6134b53c52a1282d2f1ce2ca452d4f14a3d0c48a0a14b8681e52c52d3d492761a8738314b4f0f65e9902f0698817a645238c0a24986a1cd2c528698b0bd84d3c84a1b52c729da0b4f0c63db2a368dc2c8f484f32a40c43562c360698b60dccf274b0c4366181b869ccf278b610360d8280b629e2d8309e2ad2f1e61d48b411f06a3d739cc5222a0af1e92226e2c7607183638648ca1a6241c6394b156320af8352d8e08e2986e1ae25ccf2e50e134b6381a6245914864c789d0ca1a0718915f8e52c320681c14d8e09e3221c32e386689e2695d4b60d8e0a78906b52f2f86d2d8e0a649e301a0718452b8e1642794888d2b83638238a61b731831494ae38298afcb95023e1b8e192328d63208eca8a064e138e0ca2be0d8e08e329482b95e53099cbe1b8e08e3288e27b282f60f8e0ca268d653e38cae0c290d5cc0691e638238c90b164549485195e2bc28ca94cc986c57638ca4798686c1ad4acb731cbe3983e241b86e1ab29ccf2f84e258e0b18506e1b327ccf318e0702b
  | _ => 0

def word127_2 : Nat → Nat
  | 0 => 0x435e141b86c1a733cc72712d3d8406bce60dcc0c23f739cc0a03f0a22ba76ca86c2618228b2a2ba76648981b1242ba76c786c26620c7e30289261a8734b0698b09f50e131297a640ae9db1e2606c1b869ccf274b61150c4a1a86e1a733c9c4b4b6115086b883382b8d584ac98bf322a990652778b52385b3f88612b20ae9c099cc8a4642778b60ecfd22ca33f8812628924356318b86a1ce2cce61264344ca0ae9d9941a1918812628e178c06a1cf38ca62d849905e8ae9d95c1a1910440f03338364123162dcc726231951eb3e3ef3903f303d0fb058d820b28c7b318b0fb05f3904f312dc7a230c7058ba1db30c7b298b0fb05b1e2eb30cab283d62c34e162809e50f386473133732c7c7b856101b86c1a733cc726ce6182bf39cc44a280b61bb29cce2d8309f128ac1b86c0931fccf318b615128ab1e8af50d3d240a462a926421282d441c8c54bd231d0ae9da914b62d4f247881262891b9fe3033e241a8738b2478498a918dc388e63a18a9d86e1a041ccf274d52d840af50e2151990216314be2f1c986350f58b06984d3c91a1282d463552f4b47348e2ca453c918f48a0a08989f51d2f4b068212c891d234f2775224664328650fe1a5426462148d3d8c0a249e2e6506a1c924918695262c3fe12ca8e0388e4618f58506e1b025ccf314d069860af508a10a8b0ca08f33069ccb1f4f2471ea122c727cc7323153c2e8
  | 1 => 0x4b8af94f2e1a61b8f62e2809827b3e1d8d623868c7e3d1f8d78f62e348d61b869ccf278be118f0af8f62f830a02a31e1060d8be3d4a8a62424b8f47e3d06e1af33cba4b84e3c27e53cb86f8be1b8f0a61bf338be158f5222b89bcbd238f47e2c09c49d238f47e2c0758ce3a2f0d38963b8cd2d1309a5089e2f62d8ce3a290698b47cc26338e88e27e3b1350b8ce241a86d8ee258c8d21b730c1e3b8c8742be2d8e869136322686d8cc4d8b63a2962c1a44d8ee322686dcc44d8ee258c89b1f4298cd0c9263a27a1ca4d2d8ed0d8c8af8ce3b8952d430af892498ee334352c1aa1d8ed2d436322ba798b50b8c9498e89e2c50d8b1498ce3a290a45e0b1896338ed2c3486c1dd2d8c9498ed0c9e06c1de2d436325263a2950c1a075891498ce3b8b1781d06a5250b8b6338e89f8b6338e8a42c0a58ce258e8b034e2d8ce3a2c0a58ce2d8963ac18b18e8a43d62d8e8af4b63226a494b0698ee3234e338ed2d890d29252c1a6338e89b8b0698c89b4b0af8ee338952c3486c2624942e32ca33f1f0b01a248a4d0b8ee321d06dcc2498963b8c89b8b6258ce3b428b1428a78e8af1f18c9d8c435e158812628e30338721af278b32984994218d9cc72659d4383194358d9c9f3112d3d830a88a0f424e0c338d750e20498a2490d58c62e1c86ac7e2d84994503298b191858ae9d9942c0aa2bf31c9d42650fc2c0aa2ef3150f278319
  | 2 => 0x18d74752b20d109362f8f8a61b87b42a4d8f8f74709a8952a1b87b8ba4d4463e299221a0798bd0a9363e319261063f8b8a38909c2586a9363ec5480288a62324d8fc80310a78f8c42f62f8909b8fd2e2be54c572f8be3e270a687a9234e3f8b8d61bf338962f8f8d38fe2f8909c2a30e1bf338962f8f8d21e52b8f8b0298909363f200f5448afcb86893732a4d118f8781b86bccf2f4463e2f655cb86f8fd182e06fcce2f8963f448aec9e3f428b029e821ae2f8f1923d06d8b87626c4f8f0c235b2634e0d8f09e2609b0a8d61b47f8f44e308d626b2b13e3d8309e2663c278fb8409d0af321b47fc9e3d1389a2732713e3d8309e82f33cbe3c2609f8b273848d748e3c328d430943cbd23cc8a4646138f09e2692348e0f8b0d61b076cac4f8563c296122709bccf2e1b60f8f1910440e35c162440a32f2e271922c47fc988d8f62ecb47e05b26caf278be3c3ef2f8bc0b1f88d8f0ca1c417ccf2e34e2f8f08c3506a1a32dcbf278be0f8f44e1b86e1a733c9e2f8463d1386a1b86bccf2f84e2f13e3c1a09a48c4f8f09f1fe1b8b89cc9f338f47e27a0bccf2f8f09e2672f13e0c3ee3cca89ecb06a1a72fc9e3d13e2f8386e1a868cb021cbf2713e2f83e3c1bb278f09e3e86e1a327c9f338f44f8be101a86e1af33cbc4f8be138f06882f33cbe3c278990a0af8f47e350ca9286e1a62f8372fc98ed4be3c3e869c9e2f8363d
  | 3 => 0x6334d8b01b069cc7278c60d4f0ae3272f4d0a42d61a2b86ea50d81e8d41a869cbf278ce1a3606acc869cbf278ce16360cc2b8b62c72f86e302a89e248a0338fa2606ccf8a43ef2e468ae10347868a58c0aa338a03e8c9cbe16280cf85f39cbe31860b0290ce2b8b7905182a0978be41460a825c289f51990452328a0278a829e2c68990649a82be0f9062f4932c31943cc8a46460f8b33e27e418b8a8c50ae1bf338b62f83e41148698be418386b1489f9060e278ae1ac5383e402786fccc538be4183e2c1a52493e418bb142a0681f52e93e2d83e4027d241a8958b52f83a4f900a54924e1b8918be4183e2c2986fcca4f8b60f9062e1a06fcca4f9060f8b09e1032b8b60f9062e1a06f9062f8b60e29e2f8f9923d31435e2d8be3e648c264c7225e2ecae3f460c62c27cca86a258c61a0798bd2b1463f460a0600a0ca8b09f1922586a1bf338bd2b464518f869088d6238918be3e3d0a66488d8bb2b8f8f41a0798be3e638c646326648b09f18e1a0783d7338bb278fe266389c2bf33cb8b14663e9f18e270afccf2f895182f63e638b01af2f8be258fc502706fcce2f8963f1409a1b86bccf2ec30798f8b1cbf0f1463e1e0a71463f8b8a22986bcbc501a62f8f89c1bf338fc518962e26f2fc38a78f8bc1b86bccf2ec363e2f4869f52aa48694462f8fd2e930681e62f4aa4d8fd102862e1a52f8fd102bc818ba4d8fd0a3
  | 4 => 0xd4b0a03e94587e2d4b612640d00852c280fb869458795e5415c5294d4ae254886e9f8994b54384890c7898278cb8792226e2c1b87b4b612575422997a640a6c78bc1b06e1b27f8686b8cd4bcbe0f50d2c280de3b3261b8f03ef3987f30320c787c2850c82a318a2c62f8512587c28cce10468a78906e650c9ce730508a03263787c298415d8914b8612c4686c2616832190298c831f39cc14a280c82833e5161fa18aa2c62e52e2d8cb3384990cce222827e2a990656162861e6462c24d23848f9ce730528a0640fa3509023e0c3e0c62814587e2d849903e6222815c9f8b03299183e1e6462c9c09984d22cf8cacfe1e3562f8b612640d187e2d849903e5221bc823e616cc9245109a488a6469941bc8386e1783945ce72fcc0901e8a05a1445792c48b28530a120e1783991cb86e510f920a1283a0651739cbf301e88c28021ce730280fbce730280fb0a8b0ca0ab0831f0a33e650fa5714a294210a31eca33e3ee31ce021cc60c508c6cc3290a14a640a03e86c1a731c9b383ee1b8386c1a82152f31cbb3f858a01a869cbf262c60d8c8adce731830ae31f38c9f30280fb52f39cc7261a8a383635ce730280fb86d4bcb8a5838aa2861e8953720a7e618a631e238661e359878b482646134d0cb889418789a489249162c1b87b4d612328414d60c290a34f0b1cc7274d8fa238fa3e06c1a731c9d3c3eb281a869cbf2783
  | 5 => 0xa38494ca0aac7c8a3f89dcc09bccc5b86125cbe163fc8a2ae3c36731c9b263c8fb8506e1b068c9f31c9f3316e118f86b228ba3649b8f731c9b263ee1634869ccf31cb8fec78f3856121b86c1af33cc72f16e0f8f06922e1725068ca45a348f38df33cc72ec78fe8d8b08f731c9a96208d79163f0a8b0ca08e1a31f228d62c727cc0d38f8d78506e1b069ccf31c9e118f8af97f319160c280a81b869ccf27846374a8b0c786d97f31836454a8a695c8a240ca3d0681b86a3ca578df31ccf2f48e123fe1b97f31cb86f9160e29f33cbe138d8b0296141b86dccf318de19488ae1a07d8c4554652b9089e1b731156314652b908681b7318963190e111506a1b7311563190e258406a2606c9452b84328cfc841b7318c62590e102be318961190d2a2c60e2c145cc72f4de1e240a1509245161e4886e2c62e52e2c51e861a6314de126406c1a86808633cc72fc9e0e5153c1b8d9cc72f4df275088b850fa6561e4889b8b07aca06fc9e31848f86561e4889b8b06e1ee12650ca501918c3294d994c78aa3f8b02b8aa1bacdcc72fc9d429f9943ae0c3cb26650fbcb8f3508b02af31c9a25830fa6561a2c32854326ccb1e1be2520b3e35e1424195cc3383609bc986fcb8d720e14cc8915288a36730cf8a1830a3ce7302461631f3983730280fd8594587b32340cb8b62433e314b61265616511222691b87e2d8907b4b06f848f8656
  | 6 => 0x328c234617856121be0ecd86c1af33cc72e230ab85f39cb86e230cb84f33cb8a4230ac338a82ee1b1e733cc72e308d23fb302332a23f39cc0c23e8691e2863cc96a5d2e30b2a3652c353294ab2695e1a34d22cdc7925496cc5231e09c2be1bccf2fcc0fecc4951e330ca069488f23fb2725d354b0c23e86925b2a308b148f39cc32b250c427327258b43eb2a2c0d2488b5ce73148c943147830b2ac986948d2f4ae1a34b283fc781a3283509c2bd23ccf2f86b29250d91e3302c3281a5223b0bc350cc358c98f62f85e2cca8c234614350ac4909a48d2385e3d8be2c35882cac5b860ab8f68e1b62d859903e62d858d0400d4490ad8e62e20e3c640c8c98ac4963d8b8d420d2251e383209c2b09bccf31cb8ab8663d85990a1c1103c0d0540a8da3c8cc168c23504f33cc083cbf26230930440f02e3e35c178e41434413cc72fc989c64c8a2332d8f48a05c14ca0d8c9b1f8f0fb03c0d8e8ab05413ccf2fc9c8aca6382348a1dc15ccf2e304178d8d2230ff03c0cca63a2ae3905413ccf2fc9c8a520ad028d42b413cc63dcbc8a230d122c141c417ccf31cb8d23fe362340a350acc7f318f413cbc8b168d18506e1b069ccf31c9e3f8445a1ae158486e1b06bccf31cbe0f16e3c1a09c2b0ab52f33cc63dc9e198e3272289a3889ac9c9b228ba270ac2af33cc7262ee3d8663916c8a2689c2b09b26f33cc619cbe3d85b1e2ac8
  | 7 => 0x6848130ca1086212d2a13859c9d2d50890230c4cab374ac94350538561027338cdf33c9f314a8922373814847cc0914a88c30852130c38bd2c10e2d4ae1a12732350d22488e236374d62f4b62d4a84214846120442308e240c213062140478b05c16859cc8421104acfb282388d8386c1a8201a32dcc72fc9d3c2306f84e101bb281a869ccf2fc9d382306d856101b86c1a733cc7274f06a236158486f8386c1ab1fccf31cbd3a23069850f22752c24f2620d3a3e8b0caf3030d3b250c52289cc9c9a630fa270afccf2f86b294d4943548a3b0b0ca4943009c2b869ccf31cbe1a3fb1e3cc8aca4943c8fe1b0683cf31c9f2e34b394b88c1ab281a72fc9d30230adce7301a88c31e17ce72e2808c2952c3652b48a96243363ea863c86f4b0d94ad22a5b28c7b363e8b0349226373030b37250c5ce731c9d2e34e1784b342af33c9f2f840d985e138406ecd06a1a733cbf26230ad4b0a03ee198452dcc86a330bb84f33cb89e230ab868591ff33cbb303488c3fe183b09c16535c98774b0faa1d2f4ab30cab27868d34b0fe1de18270afccf2e2661b250ff1fe18cc0ec1bb26c7d3548d2c3eb2bce0c34b494310d248982350d83109c2bf33cb86986c943f877ccf2e34a123508c360edce730cb08c3d615843381b86c1a0f3cc727ccb354a88ccb739cc0a0230a81bf322b52a2309e1b7302ad2a230a7cb8d2a58d0230ce2a090
  | _ => 0

def word127_3 : Nat → Nat
  | 0 => 0x85f4d52c158494a88f460c63584c1804e188501285c1685e15f32cfd18ca52a23e2f198b11445ecfd19258d62c1254ae2f14068cfd19258d6ca86c1af31cbd3e2389dcbf0e2f0d18986e1b327ccf314d08e26b0ec306f4e86c1af33cc72ec208e2af2fc3d34290a7258a54bc962a8d22b9234b8a5258abcbf0e238ac3286bcb88e270ce1bf322389a3386e1af33cbb0c238ce35730318c81bb32320fe357302a08e270ac320bc0af303508e3252a290a7258ab450a9ce72ecb7303508e3086e1af33cbd103fd141ab2dce0d5cc72f4306e2386e1af33cbd10238adce327cc0d54288e2a50a290ab258a7cc8afcb893848d42bd2b242534f61aa50d5849302b8a4ca733cbf27840922c6141bb261b069ccf31c9c494f6101ac282bb261bc56ce61b260d58386c1a8694c731cbf27123398586e2bf33cbe12cc44827e121b86a1a733cbf27123358406d85f382408e35731cb8a630f2f83843cc0902353a30e158453c1784215844150601384bccf31c9b274e88d8561230d3a2c31fccf2fcc60f120aa4ec4a2bf33cbe1aca093250d58509cc9d3d84733cc7274e8d3128aeca326a352f49b372561614e0ecd84226f31cbd274b892230521904610f39cc32749d2e2309aca18b2533ea34982c617168b1128af4b98d86f31cbc4ecfc9430e15c9b3834730cd8fb4bc49cc60d250c2cd8c5ce60dcc0d23d73983730308fc1185c1
  | 1 => 0x56501318040800c1c02250061400e70004918b294300d44e1344b8a4ca7324cf27c3e2c304098b498300d5ccb31c3e2c278c0cf333ccf27c386d8b0c10b0c4ca8898b337250d417535868d42ff303fe1b4d0be1b069cc7271b62d86d3c1bb29868be3f86e1a733c9e2d1b61b5006dcc5343fe1a2fb201b86dccf311b62d86d3e1a32986d342a0d5cc0a83fe1b4d0ae1b069cc726ce469868a81a7278b46986d2e2b52f1a62d868a42818b868a83fd2d868be3fd2d868be3fb3c1b869ccf278b467868ad4b61a280bf19e2d8689e2ae1a2a0b262e1a2a0fecc61a2a0ff4b61a2a0fe353298b0d94b186cc45f868a9cc5223fe1acc0be5ee1a2a0feca523868d82fd241bb3a1b733cc45f8b61a2a86f17e2d868cb8b45f868a42b0d94b62c3532861d2386c4c2a731135223fe1acc0a85ee1a2a0feca523868a8362464df2e4cf0f8d092338b1cc1366252b8d625450924e937cb933c3e35128ce4e8b0627304db278d624c4093cbc4bc38b03e0b0c9f3028c98cc624c40ae2c730cc0a3890902706e3e0fb12b3acdf2fc3e35138cf4b4742186a1b0a4c9e35893111233bcbf0e1b635128cec1c5d023361a8978d44a338b189634c43311986b4a86dcc331126358909b0a0af12b262206cca63589337253114b335258d610853cbf0e238923e053ce09035f2fc38a032d42238c6308cb891c75089e32f2fc3d42278cb8d8658b
  | 2 => 0x89399a4e54639220e38638b1ce1ea382acdf4437b28dd8937198dba636bacd9873629cd7c535c98d664357a0d4e53511cd36534b20d1c73439cd00633d18ce8533798cd273311ccb6732a14c9e732418c84631e18c6c73179cc50731098c36730a18c1c73039cc0082fc20be082f424bbe82eb94ba462e614b8e62e08cb7c62dc18b6452d698b4e62d094b3882ca20b1872c298afe52bd10aecd2b4a4ac072ac98aa6e2a2a0a7a829aa4a58b29094a38428c18a24828518a08e27b1c9de9273249bb0266bc97ce2581c952c24e9892ef24414906823da08e68235a48c4b22bac8985223a087ea21aa4858f20eb881e7204247ff11f7347c2e1e99c79931dc98766a1d4b473881ca2071851c3a46fc51bca46e051b5a46c4a1ac2c69af19f30664e19228634b187986124182c05ea9176145ce7170205b081680c59a516420580615d24562715518548a14d1c52671461850c5140984f68139a44d471319c4b8812a24496512328478711a9c45c7113c042eb1062440690fd1c3e670f6203c880ee243a660e6a838690dd3435a70d32833880ca1831c70c3a42fc90baa82d690b12c2ae70a820290a09f1c26e80979c250709098236708a2c2124082a81f68079a01d66072941c0506da41a4806520184705d9c16850579c150b04ea012a6047a410c6040200f06039180d86033140c2502e1c0aa50281c0928020a007270191c
  | 3 => 0x7321dcba572c29c9cc72111c7c971aa1c5ab71145c22770511c0c96feadbe4c6f34dba736e025b6ed6d52db3ee6c8a9b0eb6be2dae2b6b331ab4d6a699a8ed69d35a5a769331a347689b1a0e967f259eac674b99b68669a99926661a99726659a195686519593cc649219146642258f68639a18d68631a18b686299d89866232587b161631840a60b318149600a57f0b5f6997ceb5ee3d79ac5e0a177255da1575ed5d13972845c81d71245c2c96e645b7ad6c865af0d6b695a91969855a39d680d5999565ce59011638558bb96127581255f26579995da75731d5bea56aa159a556411588b55ca955e95532153ca54a1551e4545a9502953c1d4e27535194c8b52ca14a255261548e851f91476751a21458b510b542855079941235031940094fba13de54f51d3c674ee213a834e89939644e39538494dc8d36c54d89d35434d39134654cf19330f4c4a530054bda12e664b6912d254b2212b864ab2129c94a2a5278849a1d25a749319240448e1d22a84869920e847fa11ee8477a11ce6470991b6646aa51989461a917274591d15684519913a544c1d12274451510a743f290e88436190cc6430250ae6428ad08c841f1d06e741819054441319040740c99026640695010740094ff853fba8fda73f318fc073ec94fa863e71cf8e73e020f7073d890f5aa3d198f3a63cba0f1ea3c2b4ef093b7c4ebc83ab1ce9e93a328e7
  | 4 => 0xe14080e061a002a0822081a04100c000000005e080000104a000a000a001c00060a2a141e0024060c0a041a182c0002001212241604080002042a080a0a020c04100e080a1a2e0e360e040400040e00020206000008160006120602000004182616060c1600000200080400000800120404000a1a0c201c02040210041c000400081204040e59c0ae6ec59b89a6d689b1a26b659ab166a299a412688999d9666ca9961664e6990a263279891a6184984126084980265ee4979965dc3975925ce4971925bea96a9a59e49659658ca95e1656e59592a55079509253a594c225209943a24fea93a964e099339e4c0392ea24aac9249a486991d1e4668915ae440590d9e42889061640e5901163fad8f8423c098ebaa39a88e29238298dc3235868d31634268cd9632c58c89631878c29230248be962f038ba962e058b5a62c468ae2a2a478a59e288589f9a2728898ae24cc88d26222c8829e1fcb879a61d48871461a2c862aa176a858a6150c84e2e12278453a0f8783aa20da5834160c718291a098c8202207108143e0330804b1ffac7f8adfccd7eca5fa077e499f8697dd19f68a7d515f4aa7cda1f2657c719f1087c031ee897b595ecc97aeb1ea237a71de8e67a0a5e709797a9e4aa78dade20678519e08877e25de6577735dc2676d99daa676799d92576235d6e675899d56375429d3c674c51d0847402dcea773719cd04
  | 5 => 0x10c7a724421f9ddd881f25326a47c4d36bff000f268264097f800048647ea078c847f800ff001fe00380a511c93ec912803ea00cb7f800d11b72c5ca48ed26cbe308997461989c329039f077860853366fe4a96d35c9fe002954e2213a287fee2fb4c5748da417a089d488bfc0002910c620c3a292419e4f0c28960cfd2b1e1392784b5e36334b4a9522e7050c386dde107c02df305a4169b6cdbd6159449d7d34914254f44fb522c51e8438cc54f51b769a706700ec615f1d34e9a4830a3d4bedf0320a8e0a333a680d5b4e5d8c0eb61e03a99ffc0046cd8c29bdfe0029030123c5317162e1c280a6c1016001604882aec166206147804006a5e102a00080002742e1c1c1a143c06063606128e2e00103e22580e18220a0c16200242020200001034000200228200180a002802020604060864003214061c10080c4200060632140c040a0a5200009908001040007012140c1a000a0e502a00042a00380400100622080c1000361062044a0000260082061e00040618105c500000202a040c140602000e1c141a1400180a0c0012362a0018160a02183c060c341246121a4a0c1a583000000a1c0800001000000008020004040e000600320a140412000c0e00000e260412080000000e1a0056000a08000e060804040202020004001e000a12143a32241a1400260200100222120042040050000802080600040e067e00000
  | 6 => 0xa01bfc007caeee327f2e608b14072a139941c4c0cb3dfcb4a5fac00ef13aa7026a69372d0302d1243203e7babc23e5e6886099784a11de584e209c4457449d2a88b79118cd0c1bca2c16376cd388ec90462f81c5898c47fc97ed5260ba2b788d7b910287cd3c07a026939e8851bc2e305364892bfc007f8005e34d7ac1ca24ff888e0850ae905e084a97bb93d8fc4b157fc00763de011585094bfc0010013a33034531ef90b850e9a1999fe003fc0048acfff000271effc002d3bb438dedb35640aaa6ac7e13d576a94216fb3b196f477fe0027445ff800b20b1fe003fc0000021ff00082de9f4a0cd932ff001fe003fc00769b9f0713c2646bc0786b0160787fe003c641ff800326487e28e19468b9462a355fe0025a41560043093c30643fc002d1f903081fe003fc007f8005c784aadba30e81c1df7752ffe003fc00529e6c66825e87bd9552f20d2a6d9286af84fd63888506442444741783ba88ff0005a703fc0025308ff0010d197fc0077aae5e7e65637bfc007f8005d709fe00098fa63140ff0009e08ffc00703be4025b0e321d87089b44c848189339f8d280c2a0e5d6f29d78483ae8cd4d75244fbecc8d16b919e492c71a170693347c1f122fa590155880453546764a728fe20df9c6d4515be81808b4d194f0a6378eef714685135da33705834dac6b073d9813a210d54a408100be1579446c2b5889b0277679a
  | 7 => 0x2c15c861e0d82876c0fa91c28791ee1944327b5d9a400880ff0000e5c5b4cfd6acd0228842cdca5e6ae9a9a9653ce3c93421f389eff001fe003fc007706dff00144e775d31d73640235ee3030e8cf7f8005e828f6f7cfe6943cadff0012ec3694df662dbff001fe00018feff800eb4a6fcfc7fc0075c999373402cfffc00431ba0b86974931f63ba49685073de4001c9af94474423cf9ed1c419916c5e5939ff46c259196ec6c8e8136c00f5c0ba2a6aff001f4587fc0055a3e584bce2e4278f9fcb3d6c5e9229bffc007f800ff001fe00060153c25d306ff2d067354f8bc6e61475a2859b83bff80006867f3101f058c98a6147c1c86d2f627734b3ff0005936ee8737f800722463aeebfc0051b40a26ade40bcc5b8cf2e2b17c5ae58de80e4580e0f244ac4ed6004e94c29b81516075a21ca28839214a583ed993b182dd6b50dfe0035c3398be909760ca5eed61ec0885738113696114e2b93db5e57d0c132381a559c2a181b6661f81755914b2574e9445171cb9f41e5f8adfe0012da7de310b124e203b7fc003baf586768ead182cec312d0ff00116a43b18b754157372a0309bb0673c4512375ad06cd0e61cd08cff0019affbfc0022b65ce704cd396016ad088aff000ac27605017f8003d2b9fe002510434bc1cf63ac0f93fc005809cd22db7b21c892dba96bf31514ac793d009e1300d07f12e90b5080ea89d357f0
  | _ => 0

def word127_4 : Nat → Nat
  | 0 => 0xfc0069934091be2c667fc002eab844917fe003fc007f8007066c8277381427f800ff001fe003fc003b44d3b5e6df13ffc0044089ff000bf1ebfc007f800ff001fe003c5d2d83eeff0018e477fc00009491d0b3a075891dc494edff001fe003c0fc7f8009991d7a0bbfc00723cbf9317423c6ed3f7c430ff001fe003988c0c92b3a6f94e7b971169089bb38e0faccc08b053811d832b361d6ed49bd8cbeb65dfe001ec4d2a157ff0008a06df5c7b781f1e425fe0027e4a45c57da09ffe003fc007f80035960465dffc002a04890263fe00055b47f800bf61e343beddcb0f2ef7f7b54083ca4c7094d7ea979b2efd15f28c9db8231fc008bfc000d47d0075041260320e39b05922ebc021ffc0058a9ace187c0396a1d64932bc412c423a2fce77f8002d619fe003fc001e842823c2624f6ecbd58c80a3170a2d5e1d03dea9941048ccf9df83d5ec3eeb5188438824ffe946d239c0d806a4c60a248f64743bf3102e65019a1159646a35456486848df294d40adaf55b8c4278c4a2f864ab21b941b6bd75c1e4d7d65c03c88e559ca25c05913e8998617f52e3b3fc007f800ff001320f4fda51d2b0b935bfe000e8437f8000d5d9630c4c9057f80058389a11e40e57089cc344e20b228ddf645a5915638fece4ba6096aaf2324b18cc1a10d292700240618c999cb1040f7313c48a46ffc00310a700310f41561a53dd8816c805fe0
  | 1 => 0xfe76b6df62bdfe003fc00344c6ff001df295243c38a6164848172e56633a2ab4ff001fe003788e7f800ff001fe003fc00732a1872fffe001f87e042798527018cc4a156e6376309a9fe001953d052e6ff001fe00005ad5414ddf29c6acb00c56cd0cc844fabafda615e343e82b7c342ff7fc007f8005c897fe002aa34ff800677a86e499842fb59b29704b241dbfc007f80040441fe00290dab44d6b24a87c4b9a64dbc836ff0006939b1e1e6406ca788609198303ded0f4ff001fe000595059237f93effe001d0c6ff80002057fe002208167174ff001fe000fcc54f1fbff00116bfa1222df49176076683f7fc007f800ff00136df7fc004ea62ff0000a3662e00deb88ff000a41256238a419c965b3fe0007657ff800710531cd9d5e39814008265b6ac6a1e55ff80074699fe001fccbb6b69ff00106c0de02b7f8008a5a81f32324f1ff8002817ffe003a84c7f800d5462330e2ee2816444f038e4c3d7fc007f800ff0004a9359c055ec7faf04c5264f793426124b128b1a0df2875de4bae52fdfe003fc0018bf2ff0009ce80f267ee0740f318bc9cd889c883f4483d9db2557230ee909613e3fe0037d609e4727e1edb70a3d01d29247ff001fe000f0ad23a2f29258f537659f1cd13cc52cba7286e8384d294eb600790ae89bdca4b4126c13a5b28240a5b0b4a763b6b2e8cbeff800ff001f4d0dae4252b818422502317
  | 2 => 0x85a38567bbf0a5598be0b2f2e91ff90f9b990002a696b11eb2f46cdf5b203c2f43b1e055c8af832929323260a8bd4169bc2c2a08b9e752985b4724f2e99bb2e7c14ac5dc352076e2a4fb0d0ad804705559c4455725baa0c9a9167b0345d97fb544aa671a6d182c5db478634179ca4f5a1d2ade16a358c8f60159945c28d8bb46602ca0142a7f800d3630201a264f2de3dcff000009fd1e117f80000298af2a9e9aca80b0a9383d8b943473ff800083c86c8acbde4488b2107e0e292ffc002cb5bff001fe0027857ff8005b209747a3fc0002865c32069101b7a0c7f8001196b12177cc5485082a27affe003fc00551ef73479fe002003e9f1949c4af1d04fa605f0c201673782dd7794f12a56f06a09cf56f16d7f800ff000a2c806911fb947b55f3fe003fc004741a1b1c9d6f4ae5c9b142dec0619f38c199a4ab2aff000f6e7110637f8007a8a8bea3a9c49ff800d139324e3be5a956496254f60c24ab21d022f1da488e2c135e5b038eee92dc7308c256b86338353eb3ade2b00130152936e4661fbd450888016221faca1cb4d42cb9281947070742235ff800399d3fe0016d92ff800fa25532ed7366058c2f453e0547afddb31749a3d68ba2e1d4976ed0caff0013ef63545bff800d125264139d504ff800ff001732a5018a47094ff00134352f98fce852050e5fe001d984d32e0ff0016cad7900cff800bb6c22861214
  | 3 => 0x1fed283e2a2aea60d8c26c5b472b9011ae2cae979ea35dfe003d51803ab335449fe003fc001eae1541ae6b39d4121af02ccc5f5ea9b7985d38ade3984b58b9f5c3fff800b712e173723018aa0624e2505438d5e42ce2d6239398215e6890d129d528ba34aa79e70a63b27e21d1868af0b3d549dac18fbef109ccd6ab0228439af1d97252374059f59943281182e75486bd419b13a3300f6d3d3689248e8d794dfb0342d720a2633eeda4ae4422e5a3d05754805ebcd11d6c76691a91898028f4e852823cfc23acc2bdb421a2c2e4a25db2ba34f53018dc1ddfa9f412f67069686c9086743998f4cb66de4f993e3ac0c06a3d1316c10c689547678c18a9ec03371b584a674bea467951bf34bb7625641c5f4bc0e099ba7f0fcebffc004bb218b5570714be4752a942df69dfe00285d13cc6a7d6e6921ac04eadf0dd2b5ee7e5cd5d3a17a293634634dd3dd35d33530b7d4724054e08f12dc5f0414e8649cc03f3b35e5d1da8fe94deff8001801992767483ccf014df0f9d48ab2c30ff8009c61cf88a04897ff8009c962e66f1722d7f800df359fe003fc007f800f71b84e4ce98b7ff8003a3bc470efb4dba20bc9e7319242c157b6245fff001fe001b1e38fc468a1813d3926835492506d6c4d725fe80b3021f650708523029fde7225db729e845cb201e52caa42acd4522a56999090423a6013ad085110abb2b313342aba846
  | 4 => 0xe64044e54e44064e54e34064e54e14064e44e34064e44e14064e34e14064e14a64024a6ce24054a6ce14044a64e64044a64864044a64264044a64264024a64064024a6404402486ce04264864e3406486426404486406405486406403486406402486404402466ce44014664264044664264024664044024664044014664034014658464044654e38264654e38064654e08464654e08264654864064654044024454e3826445446426426ce6402426ce5404426ce5402426ce2405426ce2403426ce2401426ce0423426ce04224264e6404426465402426444423426443422426425404426425402426404423426404402426404401426403422426403401425404402406ce4423406ce24054064654024064254024064234024044234024034224011044e24016c95026b273954552ba06507fe0038439d433e782a392813fc0046bccf64f88f1621406fc45cc59b5fe001de08204620d7f9862f6918bf40a0263376612929ae7f800b75c746a09392d3fa2e2b755601b815e01eb77865b01036ade5eb3846c41690614e226cd52429017770cd40505903111701126458211a38869e8997bb1e2397e5e0332e54c950fd31e4fd23db9591b03e5fc37ce15978391fe0031e247f800702a0a84da20625c0b57c13f525992e76219763079ee8fde265fbeb6a5982cb2d523991e805e0688e08b0ea4e1ff800fa39ad0b1a8c1470
  | 5 => 0xb4860b4862a4868b52325d22094667bd250146601ce601d06164667ad24a24660092855d24d07466404d07426405d06465402d054e3406d054e1406d05426402d04ce1443d044e3406d044e2401d044e1406d044e1402d034e5406d034e1406d034a6402d03426402d03406405d024e6405d024e6404d024e4406d02426405d014e6405d014e5406d014e3406d014a6402d01406405d004e3406ce6425402ce64234029074a64049074a6402907406423846ce44018464e64048464044015078e64045078a64045078664045078464045074a64045074a6402507486402507465402507425404507425402507406423506ce4403506ce14055064e34015064e2401506425404506425402506423402506404423505ce6402505ce4406505ce24065058e64045058864065058664265058464065058464045054e64045054e44065054e1406505426402505406402504ce6401504ce5406504ce04265048e64045048464065048464045044e64035044e64015044e54065044e34065044e14065044a64045044264055044064235044064055044064035038e64045038464045034e54065034e24015034e1406503406405503406402502ce04265028864065024e6405502486403502466401502426405501ce6402501ce2405501ce24035014e64055014e54065014a64045014a64025014064055014064035014064025008
  | 6 => 0xfd214fd20965249650248d2648d2648d2548d2548d044850448d244852448d2348d234812348d024850239521184a618d2318523064a64ad267c5247c52287d225dd204650446d238e5268e5258e50184d2084d2684d2684d2284d22841228450184d203646586d22aa524aa520244866e465634655746557525854653552435927355272f4a62fd2529486724656546558465585254146588465374658a465134a6134666dd266dd22994a699466994260f4860f48679486794e679d2380d261a48638528a45265bd228c4868c5268c5047e4867ed267ed257e504114860d48676d2207528154864ed202dd222d52259d22434864350443d244352462d227d5211746649d26104660a466144669d5213ad243ad289352345d23455028d5268d50183d268350182d223450334d2334522349273452728d21a55236ad239c4a69c525335243352233522335212c52269d2369d21524a65250552d2552d21424a64250542d254250342d231b5251b523754264bd2412523054a60548605d24055230592805528a8486a8ce6a852181d2681d260ed230e5230452104928045289042678d2378d2378d2378d2378523781237fd2419d23195233252432d2332d212b52227d210c4a60c4660cd250cd231e4a61e4861e5061ed2608426085260846503928035288f42677d2177d210242602506a04654dd206846661d222648689523
  | 7 => 0xd9ffaff3fe7fcfe3fc7bcf79ef3dfedf5bbbf3fcf78ffcbf3fc7fbf7cfe9fe7fe7f4feafe7ff5beb67de7fe7b3fadf5bebf5efb7f5febfd1ef3ff378ffec7daf3d9ff5bebfcffbefbee9fe7fa7f9fe3debfb7feef9ff3ff7b3fefbebf9ffefbdd5baf7d6eaff5fef7dbfaff5fef7dbfaff6febfdcff9fe3f8df7dfcf7bebfdfdb7f6fed7f8fe7fdbf87f7f6feffcdfdbfb9edf79ffbde7bcffdef1bebfd7ffdd7faff5eabfdefbdf5febfdf7bf76febfdff2ff7dedfdbfb9edfddfbff37f6ef9fd9fe3dfeebfdfb3d676faff7dbda45ffe9df37e73d8df9be37c6f21486234a61d4a6204a6704451c4a631d2566d2551d25224a671465504651f4a61fd266f4656446567d2260d2660d209f48656d269548647d2647d2547d23745237452140d2340d216cd266cd20984a6984e5305253f4863fd24a74a6a74863d4a63dd053d5253dd22a34a6a34e5a35255fd265fd2094486944e491486914e47352473523735213e486a64a6a64e5a64a6a64866bd266bd233c4a63cd053cd22a14a6a14e5a15255ed205e4a65e4e55ed255ed203b4863bd043b5049e4869e4e454d2654d255cd275cd279752097527975274cd274cd27a95252ed222e5225a4a65ad229b4a6534a65348653d255350453d24534a6924a6444a64448644d2544d254450444d2444524444a64fd204fd2048d2548d2348d2548d239a5214fd264fd034f5034
  | _ => 0

def word127_5 : Nat → Nat
  | 0 => 0xd783c498b82244df0e60f1262e089137c39e93d00d10fd83f0e611c1e3462de0f32916f07e1cc1f870cfe0fc38653099a3c2783d0a60fc3983f0e1980c783cca61cc1e6730e194a228e78f5115348e78f7120a00f34fe9ed4c322a189212418e86d1a52d4368d03547ac205c4aee49a7b8d04d8280d82071ae1dc92ce857a2c858329b021d87bcfa4135456464e13e4852432e0d0d6193cfa970d5e8064a41579c902985306e68c29837c1c5485b9b807110f924ace34a5b9204f0cbe87cff110b01574ea3e88069b5072409f918d350bd400e39259ca1786c1d9a6291a839259c47c131cc149e4910035f1ae1c0df920576240ddd3e9de1d16f92398e35c381bf240afa778d037e496738773fe2fc7f8fe9ff374fe3fc7fe2fa7f5ff9fb7fa7f5fc7bb7f7fb5fdbfd7f6feefdf7cff9febfd7f97f3fb5de7bb7fcfebfe9fd7fcff3fd7faf7aff3fcff97f3fb5fe7ff7ddfb3fe7fcffcffcff5fd3fafedfdf7e7f9febdebfcff3feff6bfcff3fe7f73fcff9ff5fe7fb7f77e7fc7f9fd3fe3fcff8ff37edf5bef3d7eb4f79ef7d77b7f5fed3da7bcf7befbd77b7f5febfda7aff4febbf7de6fcf7aff4ff3fe7faff5fabfe7fe7f4ffafd5fcff9febfd7feef5dfbbe7fcffd7f8fd7faffc7a3fe7fcff1eff76efbef4feafe7fbfdcfe9ff7baf7def3ff7ef9f1eef7dfef5fb7f77ef79ff9ffd7f3fe7febed7fafdbfbbf7bcffdf
  | 1 => 0x9c17b48857091a40a4f27733112cde2fe4dc7c30937f3791f9344e72e327cdc4eb3a0ef9371f09b91e22f9bb3a3639371f89d8412604e0b146cca8464b8e5c5ad1b62e6578f98f09c16834993271c7f17f1fe4d6741af0e06814023f0ee4c13c35e9d06e0481a726e3fc3acb949d1dc85d184f0af4f89e71ed1bc84a4ea509e131cc68de42525d1c4206a0e7568370a7c7b870670aa15c1a839e3dc4e28d9c06a4ed8371e44a1889c136e1da89cc034727c7912fa02704db870ca7300d1c9fa4f418b41af0e0a147c4b7134ada649d8b3093a65830571948e34c85d471a642b9380980d41c83489ee7389835073c786523d0d71385986cf4169fcde0c1941af0804e0d983bd0fa0f37690348c87301242ba3dc23e93d00610fd84f8f138c27c781d998e3c1a709e11a346518b6130766638f13707384f8f038331c7834e13c23468c7b16c260e06413722513f09994a34c5b09f1e89ee71cc0ca084e605703cf430fe1f047727c52d2057c5bc781bf0e0a425a86a9ee3d90865057d3c52286a974ab1042bd11a220ef8f29aa228e78f511473c799f893295c461e83567f336950350720d6a1fa1f37a8b4f7100afa884b511070a6b8f511473c7a88a96473c7b8a050d5613c2169f191a9aa18348940e41ab1706c2481a07fe31c830c036e3c14b5152be220d41c8340ffcbfd071ee1c0df4cea906c1484b05e0680e46371e0
  | 2 => 0x706965c3c87fe1cc783ca45f4036126d97b380f81b995b38e5c1a59706ee64361940d264c1f0343281ff91e551b2e6326e52f43e7f89d9706965c3fd9c3260d41d59c06a0d0c7b97242e603fb1f0b011ecb94b48a1ac290470bc0d01ab1f0b0c8bd079b2961a435e9d06e0481b011069c8f8759706e14c38835522e5fd079be41c3a54835d4d1362859cd460dc9fb06e411449c136d441f4322a12704df870ca7300d1c9b0627fc803c87de264e09b2a50ea4483ef20f41e6f54857e1d3483eb98a340d1c987d33f83050ca9d3c0d787050d3c4ff4f13fe2e4fc9cccde2f8704944527e0df8be1c12dc5f0e03707a0d822048b423291c6990fac591c699091861ce8ca7411caa3848e24e774c86b0cb8609c8ae9340dc1bc4506e0dc1e83788b0601b04433f8711d0441430630e1980fa8eb0e43c42a6520a0360220d408034019c82d0713f41e6f9070eb4815dcc393e40e8c2bf0e59cac954b98727c83873a30aee71cc2a9e4015f872cc48248850a41e1da9032863935a8c1b83d60d2698b03707bc678bd2ae3d8601b7201a7a8b888360220d4086a2e41c381a6a60b015c23a68295a8ecba410aa1f79471ee3fc3ece83489c1609cb99e3e4e49ba28d1bc9dcb83773347c2f139733c689c937451c7f93e8df43e7f8d6940d933e8fb9706ee6521f1fd3b11393e901925278fa41d1bc9c29863c3c0d78d68d1a54bb93f1f
  | 3 => 0x4e0d82e21e39972e0fa4d29608c1d81b29672ee641ba950a81d81b3987300d1c9c9e878a5cca8d1879a65259980686634cf0e0ae6603fc0873211c5c048069a6525da0c880d329e99b36a683ed9b06e31b221590a394f5169ed3313acec9560c2e022c955221383859d4781381a699b3a1a64c8960b41a64c83e7381683bb9c61b678270771a30f14b99593410148c950d2a541b59cb38e642c39708125548858069a6525d9cc880d329e9909c1541b01106a040276350aa1a85bf261901902687f06e0482687f09a1541b81206c04426e350aba671a8b816cc78a1e1126f9379344e0c4106cec4ee4c136ce06cb3765d8f07dc9b116ce8d8e4d13b07e0ec24c7708b1c0abe87cff9b48a1b309c43f42183cfb1b0d21183fe1209c130ca846a3e0ef09a4509c362ce4430ff849cbd1f0fbc8cca04ec1f83b0959c63b8458e055f43e7fcda450d81a82b322f40c7922a4df3e1a434613881e87d079f0c21a58d87f08c11e8f9950c21185ad97880c6f09a45b2e1383f8d8c6b1018de1272f47c3ef2331e1382d6120d264c3bf23c1a1a82b322c2365d8f7a0f3e91526868494136cda45c6be87920b7b362d5862450aa936cba45ca59372af0e171e805b635b2ec7b56fa1f3e14b91f1416f65f89e4de260d1c9d9be4c937d059b0d21281b035326e601a83472766d228d9f4366c348377320e81a5970f21fd2507949bc4f9359
  | 4 => 0xa3334086710cc1995332446408c7118c2314861a4bec97462dc85a8cb3916542c2a5718ab115442a0a52d8a2a141327c84e8c9bc12f525424a6090a91c1236845cc8a191152186424c83110461fc23f447e20f831ea83c647410e641c4637e46b10d421a4e32c864a0c53184c2f185b20b2216082b0c5490a7214a828484f989c21348258c49a08f31188222040087f10fc81e883c107670de61b1433986430c321630261849208f20f901d2835705ce09e40f30185027002d403300089816112f9ff1f0fb910490cfe851484333bc6acdd90093a791284444e15f8d19b09292a2c7a13341274f38c72f13d1985845e8a024e944961aca539cd2367a27e8d06c0441a81006f67627e8d06e0481b01106b66e27f1133415d18fa1f3fe6c24f1087d0a4a30490afa7f4d99b89d0a4c9ba160ce7d138463369312570e0b0671cc049d3a66e27195170c19cffa0f376741aea689c13926d9d4949142759d4942e352849733c482c24db389285c43c7329352507948a9354d64dca5957512970ec0d9cc0340a0a5b4e8403300db4e83e33127ad1b260c41d586f9f16e2d985da0494d3f4f85773e929a3c5f0a2d3dcc39373e92b4fa9ad3d0d01dc9e52e6564d0403312782b84c331c383f84c1701238a59b5341f78a198b360dc6329a0d264c1b69ec8e56428ea2d33a7a2759d934e705c03608b2694b04e0e76743606261a2db4f0
  | 5 => 0x42450840340820c002010c0008100381016624000060870e18207800c10281140c000105c39b1a6019f02180010614581040489b020400a0010382001408002080000210016097c0537e62f8c5e98bc2b7722ea45ccab8516e96daa5b13b5cd6a12d2359e4b3496596c8a58d3b14761cec225804af855e96baa5714adaf5996b0cd584aa89540ea6ad484a88750569e2d378a5e74b12941d252a46b478e8da5172a2a9444e871d0b3a10b40d27f94fd59f0b3cd277a4eb39d0739666e1cd939ac734d66724ca498c730d25facba396e92cce5824ac594e928ca50bc9a592a524d247948d790cd201a3d2c7568ded1a722ecc54789af1192211c3fd86550a2a0f2c19482b30312041c0567ff8fcd1f7c3e747c66f81decd3cf4796af185e2a3c1477aaee09db0bb54762cead1d3c39f273ace5c9caab90371b4e0cdc0237c56ee6dd1db6936b36d10d825ab935546a2ed289a42b4326828cf599b9b3436624cbd595132876422c8118e0b1b3630ac4c988930f46166c20d829b0245fc4bf0d7c92f745e68bbe173aae215c24b7c56f12dc25b46b5d5690ad1359ccb2255fb2b975650aa9d519aa05536aa591495288850129dc93ab26f14dc69ad9329a6244bce95d928a24d848ac8fe11b9235845aa8a1d10ba1a8424e82d9029a0253fac7dc8faa9f083d0c78a0ed39d323a2c72c8e491c733888701cdc99b6735e66b18d319
  | 6 => 0xfc0071223fc00e78f78cd1d8822a01fac61a2079269d93d7d67448a9ae948c95e5cba09d3679801f64851de608a846b8a358c41ac027fc00c22e9358a060bf3a9f398e2b66eff003fc0018769f0b8e140fb052769a36821079d5f96170932b162f394bfc00723ca6481c1102d63b8a7eec4e1f42c05915a30a451ec680d960ded97382cbc235173056994025cfe5a7b7714bea3f715833a32b86709f42a8a9ae843ffc002495f25c2a56dffc005177cc26566956e15a1700bfc00f418ffc00f23de4d88cf53ab0744a8adf1846b81c425faf9904e89036a2592d2012fe00f057e7fc007ca83cc22e349ffc004185379d7de453b2258d127fc00f8863a4cfb6742d87181922e8e90957e783d3516a188734503fc00b572579011d5513c83344400d0433988a95ec684af8c7d456459e5ba2d828eae26effc001c2e7693dff003fc003438bfc004359e0e92e42bc55580724a724fea6d7fc00015c580f80a9a4e1f52014ea1a2bc76ffc00755987e4bd9a4ffc00ff003fc00ff0035220ff000c9efb096bfc0000dc015040cb8652047a102193010c44000221c4045808b89580c20412003860a1808014e400d025088c042519506240005620b880f00102042508700a0a05086801f2008b801c242050020600120454708180040c040060008f00060458012881860009d01005533836200120400b80028408510044813c000170
  | 7 => 0xc61118828ff0019c8b9f4ef726d928d3747bad4ccde0f7ea47bc391b270e979c90c14a13f93fd741b9e1fbd8c674177c25bad3ad4884c26975058f77053a6161730186c789d1e40bd93ba029b9a4b266581a7e2646f0a94338e08983af95506979a9232d54b264de1482f57a3858c22475a71d655c9a52435dd1a4de4591771a84cf676012121d7a263b813e753304c20a55de490f8326018ca5a7a4c329188ef82378669f54f47199e875e8041b414bc9cda01af570366199f77325f36c353ca366aa31147ad7590c59dad7eb41c8545da4d75d28c5796ed658244620f377fc00f1840bd9c2c62ffc00c478ed4f0c9315805b4126bfc00ff003fc007824535ee320fe08b7b738fe8120a6d07482705c1412b585ed98fbdc01de13293887fc00ff0004496c43d7356b807c90e7ef08bcb1d9ff0010d9fff001fd561d4a7fc00ff003a5b1ff000c8506329cb4a2b78b3d6845d03bfc00ff001ca7b7aa0e4113ab907888c1e3569dbac90ebfc00905fc84f4bf1fc2e45ff0030417495064cc3a67d145e0ac45898daaa2a3a49bd047ffc00ee42e1e0aaa467fc003c9fec58e41a15fdb9a927775953c123c0e7a395b70a4df031d9d660a74b25dff00271786b69d88add0522ad5b2882f220688393fc00be3634e03bfa5bfc000c893fc00ff00099def3066a1426e8442447ae37c5dbeff001fe28082a7a854ff003fc00ff003
  | _ => 0

def word127_6 : Nat → Nat
  | 0 => 0xff003fc005b8fd71a1b49649a7a0441f064aff0030a3cb4a60f14a868129c06c143a04256f2d3fc00ff003fc00ff0010059d2225fe05ff001e0119f0de51a3c16b028f9e02bbba67d05a5fca013a01da6af9305928b7ba1f9630b874f7dfe9e0b7fc002612aa1b0c1607128622888957cad28e79fd438eae85e5d1b6481d760d585f03c1dd609f039affc00072516a820810ffc00ff0005908ff00389e6ff00154f3ad86bad928b298ade102237fc00ff0019998f590bfc00c411410ceff003fc00be80538cdff0037e99ff0032c26a04ff2147996ff7e465800ebd85d26f17517da435c0b2d664fde8a57a41c015b4826b45f608b6a5ea9d0719d3a0372f1de9be2cce1e2208d4e80a401368d443b73cf48e17a22ce153550ee57217718d018b74bd3251f265239d44e85b20e54b901bc6ee50af7ce88c6b600fad33bcf0bf799f7856d849807138168abe420b14bb242afa13cac4e692175469f89f3e424eb36d44867a9dffc00f0747fc00e0430e278cf10880c8d94872aa152755dc3e228dffc00985bfd502ff001f60d900ed5a54ff002d11ded0cffc00ff002b60cff002c8e6a2447fc00ff0032d749e6bda1aa2a87a34f1538e79551eb7deb62e437ac40c09c5b234dcff0003c08c22f5bd9b953b59139442ede9e4b094c5c5546737fc005f5a9447278427fc009e5756e27e393bfc006e037fc00a8287fc00700c7fc
  | 1 => 0x5521505ce24065214a6ce24055214a6406402504907406423504507406423504503406405504501406405504501406403502d014e64055025014e64055025014a64025019074a64045019074a64025015074a64045015074a64024e5d024e44064e4d034e14064e4d014e34064e4d004e34064a6d024e64044a65014064054a6406ce2405486d054e3406486465404402486406465402426d024e64041235064254021235014e64051225074a6404db311dd3eff003426fff003fc00ff003fc00de86d9c16ff003fc00ff003fc00ba535b5a64e7fffc00ff0011587d94dbfc000fa3bfc00341730281e43b3fc002e5cffc003879ffc003f34a70cc2f85ffc00ff00361e8067dbfc002276045c35c5f930d34ea73149ecb3f0ad1c692fb05fc002ad15c543713921f3d13014cb036589cd9e3a5cc000161943d25cf2b07e43264f20c936923cc41e0d35bd5350c2c5ad99aa2aaca6c6b4a87dca466a4d468a79c7dc9991a3cc5b3e9017fc00f61c3fc00ef871c9d294192d4a5f898f318d816f69565cf46d95b6b125f8d30ea8a6bcb50d926e5802f257fc00e14c5ca3eff003fc0012643fc00a26c8d6950319d48d04a0d3fc00ff0030934586ad6001ab35f9946ec1ae156891899c98f6e0f20633110ba519e0f5dfb860105410d977154db5f14318608805591289895b1cfd666e3416d672df15ffc007946a282c78493fc00
  | 2 => 0xdf1df1de73e3bd3de8fe2fd3dd7d679d3be1fd3bddb6dd6cf6cf59bddd7cb55f55f61fd5f55f57b47bcafdf56d74fb55f55f56f23d461ba863750432a2b44a669a0a2f50856a11cd4539a86cd2999e82c24a66294c33509aa53414862e94c5f509e2533e4862c94c5b509da53244a649a8a21508eea294d4629a80ff4992ea325d4073a4ce7495ce823950403a4c07495869193d4627a464f500dea1b74a64294c1d504fea03850423a86db49806930fd431fa44cb49990912c54551a84251941a53034667490ce9398cea14348631a4a63508aea112d2321a863b49876a19ad4334a4501299ea5326d4308a84812997aa32bd463d9ccb951956a32ad43052928b5142aa1444864fa86b55194ea329d45d26465404402d25507406423d255044e1406d25503406405d25503406402d255014e6405d25501406405d25501406402d24503406405d24501406405d23506425404d235014e6405d235014a6404d23426ce2405d225074a6404d22504406405d224e44e3406d224e44e1406d205074a6404d205044e1406d025014e64059284064654029284064254029284064234029274a64264045284064654025284064254025284064234025274a6426404526425404402525426ce64025245014e6405524501406405523505ce4406523426ce5402523426ce2405523406465402522506ce1405521d06465402521d024e640
  | 3 => 0xcc1294d0baa2b60c5181ae18df23d8f589d868497622dcf3cff803eb67f805d1014bb812ff58564b3ff8045967f807f802447b181a534ab22a2197f807f807f807f804aa059b297be7f80548aff80524879b84045f2c44fa8e357064f2ab7911e7f807f8056217f807108c9540004808c4860014480050a0c3110c404026a75582300400c00002820e5809d24540040a0400e06005030648006223438400000040800406002f8be2f9bc6e8ba2e9b86d8b66d0b46c9b02c5a66959a663926448861a835e1771b96c1b06c1b16a5a16659064589605785e9685a560581605895054548525414e5314a1284a12948911425013e4f03c4e9384d9344c8328b82e4b32649122480208711a85816451128380e4300c03208419048042e351655008b5103b83bed6ca38dc3932270dd463dd3a8f98dcd2697b91cd20dd0dd5d3c62a8fccfe97ccf8dd034cd183b82d08b82d3cf927a5ea200080088089cc1cc3cf808ed3ed60060063d003fb873d03d06955d47549d19cc1c99cc38738f3d0dd3e97e95d8b5d4006710dd409bb064a3ca3e1279714d11c91cf9711c91ce90f9701a70ff1611c91ce90f9751fd3dd3dd4fe9de3dd3ddbd52fd3be9de3de4fe5f53decd6cf74f57d6cf6cf74f57d6cf6cf4ef74f4afd1fd3f68fc9fcbf69beabe3be3be9beabe3bd1fe3bd3f5abe8fe8ff8f53f673d3be9de9dd3be3de9f6bd58fd9df2
  | 4 => 0x35c85b82fcc8c037fc3dc7fc3fc2ee5433fc1faeb8341ce6275bfc3bd4495556b166a6b535473b8b61ce8e785bcd964a6a94c7589eb1cd431ac5f4956a1ea1282283a03211ea1282281a03202ea1282280a03202e91280a83a532022a0a53203671202a91290a53203201282691a80a73202a73691a83212a025723cfd5b724da9c55317f8078b580d3749cff807f8072cddeda89d2f742e7cfff802109c6041c920ed622464b40719a7f807f807f80062bff807f8072a71f8017c37f807f807f804a3c0f307f801a33730d76b43f47412e382c5b5bd1d1b103ff8012185b94831d3453aec9245a7598aa96e344b1d237d4e22acad523416d51448c504393325831bc919b880d028382770ff50a26d023dc35a67c2d26c8b846b156854a2c9d904d6e1fbb80deaf1da52f0e26b8bdca9f3e8619f8409015db17ff8001a7b457a6115429af3fef3ad54e7f80051b7f804f394c142dbb15139e92e53f2ca30ba87a0ee9dc90b094d81541e6a1ccba74aee2861d220736f325c0837c42468f7a07d7d97b9329cba45b4c26c84c7f801f0b488764897f803d1bff8008cca0374a2c9e9ef2d9d6a0c00121cb78b99205a1d0ab2a7f805b498090a9957f804bb5181f7f805c24364eff807f8044
  | _ => 0

def ax127Words (i : Nat) : Nat :=
  if i < 53 then (if i < 24 then (if i < 8 then word127_0 (i % 8) else (if i < 16 then word127_1 (i % 8) else word127_2 (i % 8))) else (if i < 40 then (if i < 32 then word127_3 (i % 8) else word127_4 (i % 8)) else (if i < 48 then word127_5 (i % 8) else word127_6 (i % 8)))) else 0

def ax127Count (k : Nat) : Nat := match k with
  | 12 => 1
  | 11 => 15
  | 10 => 171
  | 9 => 631
  | 8 => 337
  | 7 => 93
  | 6 => 8
  | _ => 0

def ax127Path (k : Nat) (i : Nat) : Nat := match k with
  | 12 => 0
  | 11 => readCompactBits ax127Words (43 + 12*i) 12
  | 10 => let v := readCompactBits ax127Words (2611 + 16*i) 16
    (readCompactBits ax127Words (2431 + 12*(v >>> 12)) 12) ||| ((v &&& 4095) <<< 12)
  | 9 => let v := readCompactBits ax127Words (37449 + 20*i) 20
    (readCompactBits ax127Words (34041 + 24*(v >>> 12)) 24) ||| ((v &&& 4095) <<< 24)
  | 8 => let v := readCompactBits ax127Words (155348 + 20*i) 20
    (readCompactBits ax127Words (149192 + 36*(v >>> 12)) 36) ||| ((v &&& 4095) <<< 36)
  | 7 => let v := readCompactBits ax127Words (206716 + 19*i) 19
    (readCompactBits ax127Words (203404 + 48*(v >>> 12)) 48) ||| ((v &&& 4095) <<< 48)
  | 6 => let v := readCompactBits ax127Words (216167 + 15*i) 15
    (readCompactBits ax127Words (215687 + 60*(v >>> 12)) 60) ||| ((v &&& 4095) <<< 60)
  | _ => 0

def ax127Live (k : Nat) (i : Nat) : Nat := match k with
  | 12 => readCompactBits ax127Words (0 + 7*i) 7
  | 11 => readCompactBits ax127Words (223 + 8*i) 8
  | 10 => readCompactBits ax127Words (5347 + 9*i) 9
  | 9 => readCompactBits ax127Words (50069 + 10*i) 10
  | 8 => readCompactBits ax127Words (162088 + 11*i) 11
  | 7 => readCompactBits ax127Words (208483 + 12*i) 12
  | 6 => readCompactBits ax127Words (216287 + 13*i) 13
  | _ => 0

def ax127PoolIDs (k : Nat) (i : Nat) : List Nat := match k with
  | 12 => let v := readCompactBits ax127Words (37 + 6*i) 6
    let n := v >>> 3
    let bits := readCompactBits ax127Words (7 + 5*(v &&& 7)) (5*n)
    compactIDsFromBits bits 5 n
  | 11 => let v := readCompactBits ax127Words (1719 + 13*i) 13
    let n := v >>> 8
    let bits := readCompactBits ax127Words (343 + 8*(v &&& 255)) (8*n)
    compactIDsFromBits bits 8 n
  | 10 => let v := readCompactBits ax127Words (24004 + 16*i) 16
    let n := v >>> 11
    let bits := readCompactBits ax127Words (6886 + 9*(v &&& 2047)) (9*n)
    compactIDsFromBits bits 9 n
  | 9 => let v := readCompactBits ax127Words (106359 + 18*i) 18
    let n := v >>> 13
    let bits := readCompactBits ax127Words (56379 + 10*(v &&& 8191)) (10*n)
    compactIDsFromBits bits 10 n
  | 8 => let v := readCompactBits ax127Words (182812 + 15*i) 15
    let n := v >>> 11
    let bits := readCompactBits ax127Words (165795 + 11*(v &&& 2047)) (11*n)
    compactIDsFromBits bits 11 n
  | 7 => let v := readCompactBits ax127Words (210739 + 10*i) 10
    let n := v >>> 7
    let bits := readCompactBits ax127Words (209599 + 12*(v &&& 127)) (12*n)
    compactIDsFromBits bits 12 n
  | 6 => let v := readCompactBits ax127Words (216404 + 2*i) 2
    let n := v >>> 1
    let bits := readCompactBits ax127Words (216391 + 13*(v &&& 1)) (13*n)
    compactIDsFromBits bits 13 n
  | _ => []

def ax127Bucket (k : Nat) (i : Nat) : List Nat := match k with
  | 11 => let d := readCompactBits ax127Words (1914 + 4*(i % 9)) 4
    let off := ((i/9 + d) % 37)
    let v := readCompactBits ax127Words (1950 + 13*off) 13
    if v >>> 5 == (i/104729)%251 then [v &&& 31] else []
  | 10 => let d := readCompactBits ax127Words (26740 + 7*(i % 108)) 7
    let off := ((i/108 + d) % 385)
    let v := readCompactBits ax127Words (27496 + 17*off) 17
    if v >>> 9 == (i/104729)%251 then [v &&& 511] else []
  | 9 => let d := readCompactBits ax127Words (117717 + 8*(i % 417)) 8
    let off := ((i/417 + d) % 1481)
    let v := readCompactBits ax127Words (121053 + 19*off) 19
    if v >>> 11 == (i/104729)%251 then [v &&& 2047] else []
  | 8 => let d := readCompactBits ax127Words (187867 + 7*(i % 219)) 7
    let off := ((i/219 + d) % 778)
    let v := readCompactBits ax127Words (189400 + 18*off) 18
    if v >>> 10 == (i/104729)%251 then [v &&& 1023] else []
  | 7 => let d := readCompactBits ax127Words (211669 + 7*(i % 62)) 7
    let off := ((i/62 + d) % 224)
    let v := readCompactBits ax127Words (212103 + 16*off) 16
    if v >>> 8 == (i/104729)%251 then [v &&& 255] else []
  | 6 => let d := readCompactBits ax127Words (216420 + 2*(i % 5)) 2
    let off := ((i/5 + d) % 19)
    let v := readCompactBits ax127Words (216430 + 12*off) 12
    if v >>> 4 == (i/104729)%251 then [v &&& 15] else []
  | _ => []
def ax31G : CompactGrid := (31,7,ax31P,ax31Q)
def ax31T : CompactTable := ((fun k => if k=7 then 0 else ax31Count k),ax31Path,ax31Live,ax31PoolIDs,ax31Bucket)
def ax31S : List (Nat × SliceSpec) := [(0, 8, 0, 23, 0, 0, 5, 5), (0, 0, 8, 21, 2, 240, 5, 4), (0, 1, 0, 30, 0, 0, 4, 4), (0, 4, 0, 27, 0, 0, 4, 4), (0, 2, 8, 21, 0, 0, 4, 4), (0, 10, 0, 21, 0, 0, 4, 4)]
def ax31D : RichDomains := (ax31S.map richSpecDomain).toArray
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ax31domains : RichValid 31 ax31D := by
  apply flexibleOK (m:=31) (ds:=ax31D) (prior:=[(21, 4), (23, 5), (27, 4), (30, 4)]) (extras:=[]) (specs:=ax31S)
  · intro e he
    simp only [List.mem_cons,List.not_mem_nil,or_false] at he
    rcases he with rfl | rfl | rfl | rfl
    · exact bound21
    · exact bound23
    · exact bound27
    · exact bound30
  · simp [ExtrasValid]
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ax31pairs : properPairs (graphGoal 31) (asRow ax31P) (asRow ax31Q) := compactPairs (g:=ax31G) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ax31autos : ∀ p ∈ ax31Perms, autoOK (graphGoal 31) (p.map swapRows).reverse = true := compactAutos_valid (by decide +kernel)
def ax31check (k : Nat) := richNode ax31G ax31T ax31D ax31Perms k
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem zc31k2p0 : chartBlock (ax31check 2) 0 1 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem zlev31k2 : chartBlock (ax31check 2) 0 1 = true :=
  zc31k2p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem zc31k3p0 : chartBlock (ax31check 3) 0 11 = true := by
  iterate 2 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem zlev31k3 : chartBlock (ax31check 3) 0 11 = true :=
  zc31k3p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem zc31k4p0 : chartBlock (ax31check 4) 0 32 = true := by
  iterate 4 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem zc31k4p1 : chartBlock (ax31check 4) 32 23 = true := by
  iterate 3 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem zlev31k4 : chartBlock (ax31check 4) 0 55 = true :=
  (chartBlock_join (a := 32) (b := 23) zc31k4p0 zc31k4p1)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem zc31k5p0 : chartBlock (ax31check 5) 0 32 = true := by
  iterate 4 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem zc31k5p1 : chartBlock (ax31check 5) 32 24 = true := by
  iterate 3 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem zlev31k5 : chartBlock (ax31check 5) 0 56 = true :=
  (chartBlock_join (a := 32) (b := 24) zc31k5p0 zc31k5p1)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem zc31k6p0 : chartBlock (ax31check 6) 0 8 = true := by
  iterate 2 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem zlev31k6 : chartBlock (ax31check 6) 0 8 = true :=
  zc31k6p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ax31blocks : ∀ k ≤ ax31G.top, chartBlock (ax31check k) 0 (ax31T.count k) = true := by
  intro k hk
  change k ≤ 7 at hk
  interval_cases k
  · rfl
  · rfl
  · exact zlev31k2
  · exact zlev31k3
  · exact zlev31k4
  · exact zlev31k5
  · exact zlev31k6
  · rfl
def ax31pools := richPoolList 31 ax31D [] (ax31PoolIDs 7 0)
def ax31links := linkedCandidates ax31G ax31T ax31Perms 6
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ax31base : Impossible true (graphGoal 31) 6 (vars 31).toFinset := @poolCut_sound true (vars 31) (graphGoal 31) (subcube (31-31) 0) 7 (@zeroSlice_sound 31 31 7 (by decide +kernel) bound31) [] (vars 31) (vars 31) 6 rfl (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ax31makes (t : Nat) (ok : primCheck ax31G ax31pools ax31links t = true) : Lower true (typeWord t :: vars 31) (graphGoal 31) 7 := by
  exact primOK (g:=ax31G) (pools:=ax31pools) (links:=ax31links) (t:=t) (hints:=4146) ax31pairs (richPool_valid (m:=31) (dom:=ax31D) (h:=[]) (picks:=ax31PoolIDs 7 0) ax31domains) (linkedCandidates_valid (g:=ax31G) (t:=ax31T) (perms:=ax31Perms) (k:=6) ax31autos (richAll (g:=ax31G) (t:=ax31T) (dom:=ax31D) (perms:=ax31Perms) ax31pairs ax31domains ax31autos ax31blocks 6 (by decide))) (by rfl) (by decide +kernel) (by decide +kernel) ax31base (by decide) ok
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem rep31t9 : Lower true (typeWord 9 :: vars 31) (graphGoal 31) 7 := ax31makes 9 (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem rep31t27 : Lower true (typeWord 27 :: vars 31) (graphGoal 31) 7 := ax31makes 27 (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem rep31t39 : Lower true (typeWord 39 :: vars 31) (graphGoal 31) 7 := ax31makes 39 (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem rep31t108 : Lower true (typeWord 108 :: vars 31) (graphGoal 31) 7 := ax31makes 108 (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem rep31t109 : Lower true (typeWord 109 :: vars 31) (graphGoal 31) 7 := ax31makes 109 (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem rep31t118 : Lower true (typeWord 118 :: vars 31) (graphGoal 31) 7 := ax31makes 118 (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem rep31t171 : Lower true (typeWord 171 :: vars 31) (graphGoal 31) 7 := ax31makes 171 (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem rep31t180 : Lower true (typeWord 180 :: vars 31) (graphGoal 31) 7 := ax31makes 180 (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem rep31t181 : Lower true (typeWord 181 :: vars 31) (graphGoal 31) 7 := ax31makes 181 (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem rep31t189 : Lower true (typeWord 189 :: vars 31) (graphGoal 31) 7 := ax31makes 189 (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem rep31t190 : Lower true (typeWord 190 :: vars 31) (graphGoal 31) 7 := ax31makes 190 (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem rep31t198 : Lower true (typeWord 198 :: vars 31) (graphGoal 31) 7 := ax31makes 198 (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem rep31t199 : Lower true (typeWord 199 :: vars 31) (graphGoal 31) 7 := ax31makes 199 (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem rep31t201 : Lower true (typeWord 201 :: vars 31) (graphGoal 31) 7 := ax31makes 201 (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem rep31t270 : Lower true (typeWord 270 :: vars 31) (graphGoal 31) 7 := ax31makes 270 (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem rep31t271 : Lower true (typeWord 271 :: vars 31) (graphGoal 31) 7 := ax31makes 271 (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem rep31t279 : Lower true (typeWord 279 :: vars 31) (graphGoal 31) 7 := ax31makes 279 (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem rep31t280 : Lower true (typeWord 280 :: vars 31) (graphGoal 31) 7 := ax31makes 280 (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem rep31t282 : Lower true (typeWord 282 :: vars 31) (graphGoal 31) 7 := ax31makes 282 (by decide +kernel)
theorem ac31t19 : Lower true (typeWord 19 :: vars 31) (graphGoal 31) 7 := @augCarry 31 31 19 9 [32] 7 (by decide +kernel) rep31t9
theorem ac31t108 : Lower true (typeWord 108 :: vars 31) (graphGoal 31) 7 := rep31t108
theorem ac31t109 : Lower true (typeWord 109 :: vars 31) (graphGoal 31) 7 := rep31t109
theorem ac31t110 : Lower true (typeWord 110 :: vars 31) (graphGoal 31) 7 := @augCarry 31 31 110 108 [32] 7 (by decide +kernel) rep31t108
theorem ac31t118 : Lower true (typeWord 118 :: vars 31) (graphGoal 31) 7 := rep31t118
theorem ac31t180 : Lower true (typeWord 180 :: vars 31) (graphGoal 31) 7 := rep31t180
theorem ac31t181 : Lower true (typeWord 181 :: vars 31) (graphGoal 31) 7 := rep31t181
theorem ac31t190 : Lower true (typeWord 190 :: vars 31) (graphGoal 31) 7 := rep31t190
theorem ac31t191 : Lower true (typeWord 191 :: vars 31) (graphGoal 31) 7 := @augCarry 31 31 191 189 [32] 7 (by decide +kernel) rep31t189
theorem ac31t198 : Lower true (typeWord 198 :: vars 31) (graphGoal 31) 7 := rep31t198
theorem ac31t262 : Lower true (typeWord 262 :: vars 31) (graphGoal 31) 7 := @augCarry 31 31 262 171 [32] 7 (by decide +kernel) rep31t171
theorem ac31t282 : Lower true (typeWord 282 :: vars 31) (graphGoal 31) 7 := rep31t282
theorem ac47t19 : Lower true (typeWord 19 :: vars 47) (graphGoal 47) 7 := @augCarry 47 31 19 27 [16, 50, 84] 7 (by decide +kernel) rep31t27
theorem ac47t47 : Lower true (typeWord 47 :: vars 47) (graphGoal 47) 7 := @augCarry 47 31 47 39 [16, 50, 84] 7 (by decide +kernel) rep31t39
theorem ac47t99 : Lower true (typeWord 99 :: vars 47) (graphGoal 47) 7 := @augCarry 47 31 99 109 [16, 50, 84] 7 (by decide +kernel) rep31t109
theorem ac47t100 : Lower true (typeWord 100 :: vars 47) (graphGoal 47) 7 := @augCarry 47 31 100 108 [16, 50, 84] 7 (by decide +kernel) rep31t108
theorem ac47t110 : Lower true (typeWord 110 :: vars 47) (graphGoal 47) 7 := @augCarry 47 31 110 108 [16, 33, 50, 84] 7 (by decide +kernel) rep31t108
theorem ac47t126 : Lower true (typeWord 126 :: vars 47) (graphGoal 47) 7 := @augCarry 47 31 126 118 [16, 50, 84] 7 (by decide +kernel) rep31t118
theorem ac47t180 : Lower true (typeWord 180 :: vars 47) (graphGoal 47) 7 := @augCarry 47 31 180 190 [16, 50, 84] 7 (by decide +kernel) rep31t190
theorem ac47t181 : Lower true (typeWord 181 :: vars 47) (graphGoal 47) 7 := @augCarry 47 31 181 189 [16, 50, 84] 7 (by decide +kernel) rep31t189
theorem ac47t191 : Lower true (typeWord 191 :: vars 47) (graphGoal 47) 7 := @augCarry 47 31 191 270 [16, 33, 50, 84] 7 (by decide +kernel) rep31t270
theorem ac47t207 : Lower true (typeWord 207 :: vars 47) (graphGoal 47) 7 := @augCarry 47 31 207 199 [16, 50, 84] 7 (by decide +kernel) rep31t199
theorem ac47t209 : Lower true (typeWord 209 :: vars 47) (graphGoal 47) 7 := @augCarry 47 31 209 201 [16, 50, 84] 7 (by decide +kernel) rep31t201
theorem ac47t290 : Lower true (typeWord 290 :: vars 47) (graphGoal 47) 7 := @augCarry 47 31 290 282 [16, 50, 84] 7 (by decide +kernel) rep31t282
theorem ac61t29 : Lower true (typeWord 29 :: vars 61) (graphGoal 61) 7 := @augCarry 61 31 29 27 [64, 66, 81] 7 (by decide +kernel) rep31t27
theorem ac61t39 : Lower true (typeWord 39 :: vars 61) (graphGoal 61) 7 := @augCarry 61 31 39 27 [64, 81] 7 (by decide +kernel) rep31t27
theorem ac61t110 : Lower true (typeWord 110 :: vars 61) (graphGoal 61) 7 := @augCarry 61 31 110 108 [64, 66, 81] 7 (by decide +kernel) rep31t108
theorem ac61t120 : Lower true (typeWord 120 :: vars 61) (graphGoal 61) 7 := @augCarry 61 31 120 108 [64, 81] 7 (by decide +kernel) rep31t108
theorem ac61t129 : Lower true (typeWord 129 :: vars 61) (graphGoal 61) 7 := @augCarry 61 31 129 109 [64, 81] 7 (by decide +kernel) rep31t109
theorem ac61t180 : Lower true (typeWord 180 :: vars 61) (graphGoal 61) 7 := @augCarry 61 31 180 279 [64, 66, 81] 7 (by decide +kernel) rep31t279
theorem ac61t191 : Lower true (typeWord 191 :: vars 61) (graphGoal 61) 7 := @augCarry 61 31 191 189 [64, 66, 81] 7 (by decide +kernel) rep31t189
theorem ac61t200 : Lower true (typeWord 200 :: vars 61) (graphGoal 61) 7 := @augCarry 61 31 200 180 [64, 66, 81] 7 (by decide +kernel) rep31t180
theorem ac61t201 : Lower true (typeWord 201 :: vars 61) (graphGoal 61) 7 := @augCarry 61 31 201 270 [64, 81] 7 (by decide +kernel) rep31t270
theorem ac61t210 : Lower true (typeWord 210 :: vars 61) (graphGoal 61) 7 := @augCarry 61 31 210 271 [64, 81] 7 (by decide +kernel) rep31t271
theorem ac61t272 : Lower true (typeWord 272 :: vars 61) (graphGoal 61) 7 := @augCarry 61 31 272 270 [64, 66, 81] 7 (by decide +kernel) rep31t270
theorem ac61t281 : Lower true (typeWord 281 :: vars 61) (graphGoal 61) 7 := @augCarry 61 31 281 180 [64, 81] 7 (by decide +kernel) rep31t180
theorem ac61t282 : Lower true (typeWord 282 :: vars 61) (graphGoal 61) 7 := @augCarry 61 31 282 189 [64, 81] 7 (by decide +kernel) rep31t189
theorem ac61t290 : Lower true (typeWord 290 :: vars 61) (graphGoal 61) 7 := @augCarry 61 31 290 181 [64, 81] 7 (by decide +kernel) rep31t181
theorem ac61t291 : Lower true (typeWord 291 :: vars 61) (graphGoal 61) 7 := @augCarry 61 31 291 190 [64, 81] 7 (by decide +kernel) rep31t190
theorem ac62t29 : Lower true (typeWord 29 :: vars 62) (graphGoal 62) 7 := @augCarry 62 31 29 27 [65, 50, 48, 80] 7 (by decide +kernel) rep31t27
theorem ac62t110 : Lower true (typeWord 110 :: vars 62) (graphGoal 62) 7 := @augCarry 62 31 110 108 [65, 50, 48, 80] 7 (by decide +kernel) rep31t108
theorem ac62t118 : Lower true (typeWord 118 :: vars 62) (graphGoal 62) 7 := @augCarry 62 31 118 118 [65, 50, 80] 7 (by decide +kernel) rep31t118
theorem ac62t119 : Lower true (typeWord 119 :: vars 62) (graphGoal 62) 7 := @augCarry 62 31 119 109 [65, 50, 80] 7 (by decide +kernel) rep31t109
theorem ac62t128 : Lower true (typeWord 128 :: vars 62) (graphGoal 62) 7 := @augCarry 62 31 128 108 [65, 50, 80] 7 (by decide +kernel) rep31t108
theorem ac62t181 : Lower true (typeWord 181 :: vars 62) (graphGoal 62) 7 := @augCarry 62 31 181 282 [65, 50, 80] 7 (by decide +kernel) rep31t282
theorem ac62t190 : Lower true (typeWord 190 :: vars 62) (graphGoal 62) 7 := @augCarry 62 31 190 279 [65, 50, 48, 80] 7 (by decide +kernel) rep31t279
theorem ac62t191 : Lower true (typeWord 191 :: vars 62) (graphGoal 62) 7 := @augCarry 62 31 191 270 [65, 50, 48, 80] 7 (by decide +kernel) rep31t270
theorem ac62t272 : Lower true (typeWord 272 :: vars 62) (graphGoal 62) 7 := @augCarry 62 31 272 189 [65, 50, 48, 80] 7 (by decide +kernel) rep31t189
theorem ac62t281 : Lower true (typeWord 281 :: vars 62) (graphGoal 62) 7 := @augCarry 62 31 281 190 [65, 50, 80] 7 (by decide +kernel) rep31t190
theorem ac62t290 : Lower true (typeWord 290 :: vars 62) (graphGoal 62) 7 := @augCarry 62 31 290 189 [65, 50, 80] 7 (by decide +kernel) rep31t189
theorem ac62t291 : Lower true (typeWord 291 :: vars 62) (graphGoal 62) 7 := @augCarry 62 31 291 180 [65, 50, 80] 7 (by decide +kernel) rep31t180
theorem ac79t9 : Lower true (typeWord 9 :: vars 79) (graphGoal 79) 7 := @augCarry 79 31 9 27 [49, 100] 7 (by decide +kernel) rep31t27
theorem ac79t19 : Lower true (typeWord 19 :: vars 79) (graphGoal 79) 7 := @augCarry 79 31 19 27 [32, 49, 100] 7 (by decide +kernel) rep31t27
theorem ac79t55 : Lower true (typeWord 55 :: vars 79) (graphGoal 79) 7 := @augCarry 79 31 55 39 [49, 100] 7 (by decide +kernel) rep31t39
theorem ac79t90 : Lower true (typeWord 90 :: vars 79) (graphGoal 79) 7 := @augCarry 79 31 90 108 [49, 100] 7 (by decide +kernel) rep31t108
theorem ac79t100 : Lower true (typeWord 100 :: vars 79) (graphGoal 79) 7 := @augCarry 79 31 100 108 [32, 49, 100] 7 (by decide +kernel) rep31t108
theorem ac79t109 : Lower true (typeWord 109 :: vars 79) (graphGoal 79) 7 := @augCarry 79 31 109 109 [49, 100] 7 (by decide +kernel) rep31t109
theorem ac79t138 : Lower true (typeWord 138 :: vars 79) (graphGoal 79) 7 := @augCarry 79 31 138 118 [49, 100] 7 (by decide +kernel) rep31t118
theorem ac79t171 : Lower true (typeWord 171 :: vars 79) (graphGoal 79) 7 := @augCarry 79 31 171 189 [49, 100] 7 (by decide +kernel) rep31t189
theorem ac79t181 : Lower true (typeWord 181 :: vars 79) (graphGoal 79) 7 := @augCarry 79 31 181 270 [32, 49, 100] 7 (by decide +kernel) rep31t270
theorem ac79t189 : Lower true (typeWord 189 :: vars 79) (graphGoal 79) 7 := @augCarry 79 31 189 171 [49, 100] 7 (by decide +kernel) rep31t171
theorem ac79t190 : Lower true (typeWord 190 :: vars 79) (graphGoal 79) 7 := @augCarry 79 31 190 271 [49, 100] 7 (by decide +kernel) rep31t271
theorem ac79t191 : Lower true (typeWord 191 :: vars 79) (graphGoal 79) 7 := @augCarry 79 31 191 171 [32, 49, 100] 7 (by decide +kernel) rep31t171
theorem ac79t216 : Lower true (typeWord 216 :: vars 79) (graphGoal 79) 7 := @augCarry 79 31 216 198 [49, 100] 7 (by decide +kernel) rep31t198
theorem ac79t217 : Lower true (typeWord 217 :: vars 79) (graphGoal 79) 7 := @augCarry 79 31 217 201 [49, 100] 7 (by decide +kernel) rep31t201
theorem ac79t218 : Lower true (typeWord 218 :: vars 79) (graphGoal 79) 7 := @augCarry 79 31 218 198 [32, 49, 100] 7 (by decide +kernel) rep31t198
theorem ac79t219 : Lower true (typeWord 219 :: vars 79) (graphGoal 79) 7 := @augCarry 79 31 219 199 [49, 100] 7 (by decide +kernel) rep31t199
theorem ac79t252 : Lower true (typeWord 252 :: vars 79) (graphGoal 79) 7 := @augCarry 79 31 252 270 [49, 100] 7 (by decide +kernel) rep31t270
theorem ac79t261 : Lower true (typeWord 261 :: vars 79) (graphGoal 79) 7 := @augCarry 79 31 261 180 [32, 49, 100] 7 (by decide +kernel) rep31t180
theorem ac79t262 : Lower true (typeWord 262 :: vars 79) (graphGoal 79) 7 := @augCarry 79 31 262 189 [32, 49, 100] 7 (by decide +kernel) rep31t189
theorem ac79t270 : Lower true (typeWord 270 :: vars 79) (graphGoal 79) 7 := @augCarry 79 31 270 181 [32, 49, 100] 7 (by decide +kernel) rep31t181
theorem ac79t271 : Lower true (typeWord 271 :: vars 79) (graphGoal 79) 7 := @augCarry 79 31 271 190 [49, 100] 7 (by decide +kernel) rep31t190
theorem ac79t272 : Lower true (typeWord 272 :: vars 79) (graphGoal 79) 7 := @augCarry 79 31 272 181 [49, 100] 7 (by decide +kernel) rep31t181
theorem ac79t297 : Lower true (typeWord 297 :: vars 79) (graphGoal 79) 7 := @augCarry 79 31 297 279 [49, 100] 7 (by decide +kernel) rep31t279
theorem ac79t298 : Lower true (typeWord 298 :: vars 79) (graphGoal 79) 7 := @augCarry 79 31 298 282 [49, 100] 7 (by decide +kernel) rep31t282
theorem ac79t299 : Lower true (typeWord 299 :: vars 79) (graphGoal 79) 7 := @augCarry 79 31 299 279 [32, 49, 100] 7 (by decide +kernel) rep31t279
theorem ac79t300 : Lower true (typeWord 300 :: vars 79) (graphGoal 79) 7 := @augCarry 79 31 300 280 [49, 100] 7 (by decide +kernel) rep31t280
def ax55G : CompactGrid := (55,6,ax55P,ax55Q)
def ax55T : CompactTable := ((fun k => if k=6 then 0 else ax55Count k),ax55Path,ax55Live,ax55PoolIDs,ax55Bucket)
def ax55S : List (Nat × SliceSpec) := [(0, 2, 0, 53, 0, 0, 5, 5), (0, 32, 0, 23, 0, 0, 5, 5), (0, 1, 0, 54, 0, 0, 4, 4), (0, 16, 0, 39, 0, 0, 4, 4)]
def ax55D : RichDomains := (ax55S.map richSpecDomain).toArray
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ax55domains : RichValid 55 ax55D := by
  apply flexibleOK (m:=55) (ds:=ax55D) (prior:=[(23, 5), (39, 4), (53, 5), (54, 4)]) (extras:=[]) (specs:=ax55S)
  · intro e he
    simp only [List.mem_cons,List.not_mem_nil,or_false] at he
    rcases he with rfl | rfl | rfl | rfl
    · exact bound23
    · exact bound39
    · exact bound53
    · exact bound54
  · simp [ExtrasValid]
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ax55pairs : properPairs (graphGoal 55) (asRow ax55P) (asRow ax55Q) := compactPairs (g:=ax55G) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ax55autos : ∀ p ∈ ax55Perms, autoOK (graphGoal 55) (p.map swapRows).reverse = true := compactAutos_valid (by decide +kernel)
def ax55check (k : Nat) := richNode ax55G ax55T ax55D ax55Perms k
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem zc55k5p0 : chartBlock (ax55check 5) 0 1 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem zlev55k5 : chartBlock (ax55check 5) 0 1 = true :=
  zc55k5p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ax55blocks : ∀ k ≤ ax55G.top, chartBlock (ax55check k) 0 (ax55T.count k) = true := by
  intro k hk
  change k ≤ 6 at hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact zlev55k5
  · rfl
def ax55pools := richPoolList 55 ax55D [] (ax55PoolIDs 6 0)
def ax55links := linkedCandidates ax55G ax55T ax55Perms 5
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ax55base : Impossible true (graphGoal 55) 5 (vars 55).toFinset := @poolCut_sound true (vars 55) (graphGoal 55) (subcube (55-55) 0) 6 (@zeroSlice_sound 55 55 6 (by decide +kernel) bound55) [] (vars 55) (vars 55) 5 rfl (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ax55makes (t : Nat) (ok : primCheck ax55G ax55pools ax55links t = true) : Lower true (typeWord t :: vars 55) (graphGoal 55) 6 := by
  exact primOK (g:=ax55G) (pools:=ax55pools) (links:=ax55links) (t:=t) (hints:=66) ax55pairs (richPool_valid (m:=55) (dom:=ax55D) (h:=[]) (picks:=ax55PoolIDs 6 0) ax55domains) (linkedCandidates_valid (g:=ax55G) (t:=ax55T) (perms:=ax55Perms) (k:=5) ax55autos (richAll (g:=ax55G) (t:=ax55T) (dom:=ax55D) (perms:=ax55Perms) ax55pairs ax55domains ax55autos ax55blocks 5 (by decide))) (by rfl) (by decide +kernel) (by decide +kernel) ax55base (by decide) ok
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem rep55t99 : Lower true (typeWord 99 :: vars 55) (graphGoal 55) 6 := ax55makes 99 (by decide +kernel)
theorem ac55t99 : Lower true (typeWord 99 :: vars 55) (graphGoal 55) 6 := rep55t99
def ax87G : CompactGrid := (87,7,ax87P,ax87Q)
def ax87T : CompactTable := ((fun k => if k=7 then 0 else ax87Count k),ax87Path,ax87Live,ax87PoolIDs,ax87Bucket)
def ax87S : List (Nat × SliceSpec) := [(0, 2, 0, 85, 0, 0, 5, 5), (0, 64, 0, 23, 0, 0, 5, 5), (0, 0, 2, 69, 16, 983040, 5, 4), (0, 1, 0, 86, 0, 0, 4, 4), (0, 4, 0, 83, 0, 0, 4, 4), (0, 16, 2, 69, 0, 0, 4, 4), (0, 18, 0, 69, 0, 0, 4, 4), (0, 66, 0, 21, 0, 0, 4, 4)]
def ax87D : RichDomains := (ax87S.map richSpecDomain).toArray
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ax87domains : RichValid 87 ax87D := by
  apply flexibleOK (m:=87) (ds:=ax87D) (prior:=[(21, 4), (23, 5), (69, 4), (83, 4), (85, 5), (86, 4)]) (extras:=[]) (specs:=ax87S)
  · intro e he
    simp only [List.mem_cons,List.not_mem_nil,or_false] at he
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl
    · exact bound21
    · exact bound23
    · exact bound69
    · exact bound83
    · exact bound85
    · exact bound86
  · simp [ExtrasValid]
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ax87pairs : properPairs (graphGoal 87) (asRow ax87P) (asRow ax87Q) := compactPairs (g:=ax87G) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ax87autos : ∀ p ∈ ax87Perms, autoOK (graphGoal 87) (p.map swapRows).reverse = true := compactAutos_valid (by decide +kernel)
def ax87check (k : Nat) := richNode ax87G ax87T ax87D ax87Perms k
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem zc87k3p0 : chartBlock (ax87check 3) 0 10 = true := by
  iterate 2 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem zlev87k3 : chartBlock (ax87check 3) 0 10 = true :=
  zc87k3p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem zc87k4p0 : chartBlock (ax87check 4) 0 32 = true := by
  iterate 4 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem zc87k4p1 : chartBlock (ax87check 4) 32 11 = true := by
  iterate 2 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem zlev87k4 : chartBlock (ax87check 4) 0 43 = true :=
  (chartBlock_join (a := 32) (b := 11) zc87k4p0 zc87k4p1)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem zc87k5p0 : chartBlock (ax87check 5) 0 32 = true := by
  iterate 4 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem zc87k5p1 : chartBlock (ax87check 5) 32 15 = true := by
  iterate 3 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem zlev87k5 : chartBlock (ax87check 5) 0 47 = true :=
  (chartBlock_join (a := 32) (b := 15) zc87k5p0 zc87k5p1)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem zc87k6p0 : chartBlock (ax87check 6) 0 9 = true := by
  iterate 2 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem zlev87k6 : chartBlock (ax87check 6) 0 9 = true :=
  zc87k6p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ax87blocks : ∀ k ≤ ax87G.top, chartBlock (ax87check k) 0 (ax87T.count k) = true := by
  intro k hk
  change k ≤ 7 at hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · exact zlev87k3
  · exact zlev87k4
  · exact zlev87k5
  · exact zlev87k6
  · rfl
def ax87pools := richPoolList 87 ax87D [] (ax87PoolIDs 7 0)
def ax87links := linkedCandidates ax87G ax87T ax87Perms 6
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ax87base : Impossible true (graphGoal 87) 6 (vars 87).toFinset := @poolCut_sound true (vars 87) (graphGoal 87) (subcube (87-87) 0) 7 (@zeroSlice_sound 87 87 7 (by decide +kernel) bound87) [] (vars 87) (vars 87) 6 rfl (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ax87makes (t : Nat) (ok : primCheck ax87G ax87pools ax87links t = true) : Lower true (typeWord t :: vars 87) (graphGoal 87) 7 := by
  exact primOK (g:=ax87G) (pools:=ax87pools) (links:=ax87links) (t:=t) (hints:=66) ax87pairs (richPool_valid (m:=87) (dom:=ax87D) (h:=[]) (picks:=ax87PoolIDs 7 0) ax87domains) (linkedCandidates_valid (g:=ax87G) (t:=ax87T) (perms:=ax87Perms) (k:=6) ax87autos (richAll (g:=ax87G) (t:=ax87T) (dom:=ax87D) (perms:=ax87Perms) ax87pairs ax87domains ax87autos ax87blocks 6 (by decide))) (by rfl) (by decide +kernel) (by decide +kernel) ax87base (by decide) ok
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem rep87t9 : Lower true (typeWord 9 :: vars 87) (graphGoal 87) 7 := ax87makes 9 (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem rep87t36 : Lower true (typeWord 36 :: vars 87) (graphGoal 87) 7 := ax87makes 36 (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem rep87t54 : Lower true (typeWord 54 :: vars 87) (graphGoal 87) 7 := ax87makes 54 (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem rep87t55 : Lower true (typeWord 55 :: vars 87) (graphGoal 87) 7 := ax87makes 55 (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem rep87t58 : Lower true (typeWord 58 :: vars 87) (graphGoal 87) 7 := ax87makes 58 (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem rep87t90 : Lower true (typeWord 90 :: vars 87) (graphGoal 87) 7 := ax87makes 90 (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem rep87t117 : Lower true (typeWord 117 :: vars 87) (graphGoal 87) 7 := ax87makes 117 (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem rep87t118 : Lower true (typeWord 118 :: vars 87) (graphGoal 87) 7 := ax87makes 118 (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem rep87t135 : Lower true (typeWord 135 :: vars 87) (graphGoal 87) 7 := ax87makes 135 (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem rep87t136 : Lower true (typeWord 136 :: vars 87) (graphGoal 87) 7 := ax87makes 136 (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem rep87t171 : Lower true (typeWord 171 :: vars 87) (graphGoal 87) 7 := ax87makes 171 (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem rep87t180 : Lower true (typeWord 180 :: vars 87) (graphGoal 87) 7 := ax87makes 180 (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem rep87t181 : Lower true (typeWord 181 :: vars 87) (graphGoal 87) 7 := ax87makes 181 (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem rep87t198 : Lower true (typeWord 198 :: vars 87) (graphGoal 87) 7 := ax87makes 198 (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem rep87t199 : Lower true (typeWord 199 :: vars 87) (graphGoal 87) 7 := ax87makes 199 (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem rep87t216 : Lower true (typeWord 216 :: vars 87) (graphGoal 87) 7 := ax87makes 216 (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem rep87t217 : Lower true (typeWord 217 :: vars 87) (graphGoal 87) 7 := ax87makes 217 (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem rep87t220 : Lower true (typeWord 220 :: vars 87) (graphGoal 87) 7 := ax87makes 220 (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem rep87t279 : Lower true (typeWord 279 :: vars 87) (graphGoal 87) 7 := ax87makes 279 (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem rep87t297 : Lower true (typeWord 297 :: vars 87) (graphGoal 87) 7 := ax87makes 297 (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem rep87t298 : Lower true (typeWord 298 :: vars 87) (graphGoal 87) 7 := ax87makes 298 (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem rep87t301 : Lower true (typeWord 301 :: vars 87) (graphGoal 87) 7 := ax87makes 301 (by decide +kernel)
theorem ac87t9 : Lower true (typeWord 9 :: vars 87) (graphGoal 87) 7 := rep87t9
theorem ac87t58 : Lower true (typeWord 58 :: vars 87) (graphGoal 87) 7 := rep87t58
theorem ac87t90 : Lower true (typeWord 90 :: vars 87) (graphGoal 87) 7 := rep87t90
theorem ac87t100 : Lower true (typeWord 100 :: vars 87) (graphGoal 87) 7 := @augCarry 87 87 100 90 [32] 7 (by decide +kernel) rep87t90
theorem ac87t117 : Lower true (typeWord 117 :: vars 87) (graphGoal 87) 7 := rep87t117
theorem ac87t118 : Lower true (typeWord 118 :: vars 87) (graphGoal 87) 7 := rep87t118
theorem ac87t119 : Lower true (typeWord 119 :: vars 87) (graphGoal 87) 7 := @augCarry 87 87 119 117 [32] 7 (by decide +kernel) rep87t117
theorem ac87t135 : Lower true (typeWord 135 :: vars 87) (graphGoal 87) 7 := rep87t135
theorem ac87t136 : Lower true (typeWord 136 :: vars 87) (graphGoal 87) 7 := rep87t136
theorem ac87t137 : Lower true (typeWord 137 :: vars 87) (graphGoal 87) 7 := @augCarry 87 87 137 135 [32] 7 (by decide +kernel) rep87t135
theorem ac87t171 : Lower true (typeWord 171 :: vars 87) (graphGoal 87) 7 := rep87t171
theorem ac87t180 : Lower true (typeWord 180 :: vars 87) (graphGoal 87) 7 := rep87t180
theorem ac87t198 : Lower true (typeWord 198 :: vars 87) (graphGoal 87) 7 := rep87t198
theorem ac87t199 : Lower true (typeWord 199 :: vars 87) (graphGoal 87) 7 := rep87t199
theorem ac87t200 : Lower true (typeWord 200 :: vars 87) (graphGoal 87) 7 := @augCarry 87 87 200 198 [32] 7 (by decide +kernel) rep87t198
theorem ac87t216 : Lower true (typeWord 216 :: vars 87) (graphGoal 87) 7 := rep87t216
theorem ac87t217 : Lower true (typeWord 217 :: vars 87) (graphGoal 87) 7 := rep87t217
theorem ac87t218 : Lower true (typeWord 218 :: vars 87) (graphGoal 87) 7 := @augCarry 87 87 218 216 [32] 7 (by decide +kernel) rep87t216
theorem ac87t220 : Lower true (typeWord 220 :: vars 87) (graphGoal 87) 7 := rep87t220
theorem ac87t252 : Lower true (typeWord 252 :: vars 87) (graphGoal 87) 7 := @augCarry 87 87 252 181 [32] 7 (by decide +kernel) rep87t181
theorem ac87t261 : Lower true (typeWord 261 :: vars 87) (graphGoal 87) 7 := @augCarry 87 87 261 180 [32] 7 (by decide +kernel) rep87t180
theorem ac87t262 : Lower true (typeWord 262 :: vars 87) (graphGoal 87) 7 := @augCarry 87 87 262 171 [32] 7 (by decide +kernel) rep87t171
theorem ac87t279 : Lower true (typeWord 279 :: vars 87) (graphGoal 87) 7 := rep87t279
theorem ac87t297 : Lower true (typeWord 297 :: vars 87) (graphGoal 87) 7 := rep87t297
theorem ac87t298 : Lower true (typeWord 298 :: vars 87) (graphGoal 87) 7 := rep87t298
theorem ac87t301 : Lower true (typeWord 301 :: vars 87) (graphGoal 87) 7 := rep87t301
theorem ac93t27 : Lower true (typeWord 27 :: vars 93) (graphGoal 93) 7 := @augCarry 93 87 27 9 [49, 100] 7 (by decide +kernel) rep87t9
theorem ac93t36 : Lower true (typeWord 36 :: vars 93) (graphGoal 93) 7 := @augCarry 93 87 36 54 [49, 100] 7 (by decide +kernel) rep87t54
theorem ac93t38 : Lower true (typeWord 38 :: vars 93) (graphGoal 93) 7 := @augCarry 93 87 38 54 [32, 49, 100] 7 (by decide +kernel) rep87t54
theorem ac93t39 : Lower true (typeWord 39 :: vars 93) (graphGoal 93) 7 := @augCarry 93 87 39 55 [49, 100] 7 (by decide +kernel) rep87t55
theorem ac93t54 : Lower true (typeWord 54 :: vars 93) (graphGoal 93) 7 := @augCarry 93 87 54 36 [49, 100] 7 (by decide +kernel) rep87t36
theorem ac93t56 : Lower true (typeWord 56 :: vars 93) (graphGoal 93) 7 := @augCarry 93 87 56 36 [32, 49, 100] 7 (by decide +kernel) rep87t36
theorem ac93t58 : Lower true (typeWord 58 :: vars 93) (graphGoal 93) 7 := @augCarry 93 87 58 58 [49, 100] 7 (by decide +kernel) rep87t58
theorem ac93t108 : Lower true (typeWord 108 :: vars 93) (graphGoal 93) 7 := @augCarry 93 87 108 90 [49, 100] 7 (by decide +kernel) rep87t90
theorem ac93t110 : Lower true (typeWord 110 :: vars 93) (graphGoal 93) 7 := @augCarry 93 87 110 90 [32, 49, 100] 7 (by decide +kernel) rep87t90
theorem ac93t117 : Lower true (typeWord 117 :: vars 93) (graphGoal 93) 7 := @augCarry 93 87 117 135 [49, 100] 7 (by decide +kernel) rep87t135
theorem ac93t119 : Lower true (typeWord 119 :: vars 93) (graphGoal 93) 7 := @augCarry 93 87 119 135 [32, 49, 100] 7 (by decide +kernel) rep87t135
theorem ac93t120 : Lower true (typeWord 120 :: vars 93) (graphGoal 93) 7 := @augCarry 93 87 120 136 [49, 100] 7 (by decide +kernel) rep87t136
theorem ac93t135 : Lower true (typeWord 135 :: vars 93) (graphGoal 93) 7 := @augCarry 93 87 135 117 [49, 100] 7 (by decide +kernel) rep87t117
theorem ac93t137 : Lower true (typeWord 137 :: vars 93) (graphGoal 93) 7 := @augCarry 93 87 137 117 [32, 49, 100] 7 (by decide +kernel) rep87t117
theorem ac93t138 : Lower true (typeWord 138 :: vars 93) (graphGoal 93) 7 := @augCarry 93 87 138 118 [49, 100] 7 (by decide +kernel) rep87t118
theorem ac93t180 : Lower true (typeWord 180 :: vars 93) (graphGoal 93) 7 := @augCarry 93 87 180 180 [49, 100] 7 (by decide +kernel) rep87t180
theorem ac93t189 : Lower true (typeWord 189 :: vars 93) (graphGoal 93) 7 := @augCarry 93 87 189 171 [49, 100] 7 (by decide +kernel) rep87t171
theorem ac93t198 : Lower true (typeWord 198 :: vars 93) (graphGoal 93) 7 := @augCarry 93 87 198 216 [49, 100] 7 (by decide +kernel) rep87t216
theorem ac93t200 : Lower true (typeWord 200 :: vars 93) (graphGoal 93) 7 := @augCarry 93 87 200 216 [32, 49, 100] 7 (by decide +kernel) rep87t216
theorem ac93t201 : Lower true (typeWord 201 :: vars 93) (graphGoal 93) 7 := @augCarry 93 87 201 217 [49, 100] 7 (by decide +kernel) rep87t217
theorem ac93t216 : Lower true (typeWord 216 :: vars 93) (graphGoal 93) 7 := @augCarry 93 87 216 198 [49, 100] 7 (by decide +kernel) rep87t198
theorem ac93t218 : Lower true (typeWord 218 :: vars 93) (graphGoal 93) 7 := @augCarry 93 87 218 198 [32, 49, 100] 7 (by decide +kernel) rep87t198
theorem ac93t219 : Lower true (typeWord 219 :: vars 93) (graphGoal 93) 7 := @augCarry 93 87 219 199 [49, 100] 7 (by decide +kernel) rep87t199
theorem ac93t220 : Lower true (typeWord 220 :: vars 93) (graphGoal 93) 7 := @augCarry 93 87 220 301 [49, 100] 7 (by decide +kernel) rep87t301
theorem ac93t261 : Lower true (typeWord 261 :: vars 93) (graphGoal 93) 7 := @augCarry 93 87 261 180 [32, 49, 100] 7 (by decide +kernel) rep87t180
theorem ac93t270 : Lower true (typeWord 270 :: vars 93) (graphGoal 93) 7 := @augCarry 93 87 270 181 [32, 49, 100] 7 (by decide +kernel) rep87t181
theorem ac93t272 : Lower true (typeWord 272 :: vars 93) (graphGoal 93) 7 := @augCarry 93 87 272 181 [49, 100] 7 (by decide +kernel) rep87t181
theorem ac93t279 : Lower true (typeWord 279 :: vars 93) (graphGoal 93) 7 := @augCarry 93 87 279 297 [49, 100] 7 (by decide +kernel) rep87t297
theorem ac93t281 : Lower true (typeWord 281 :: vars 93) (graphGoal 93) 7 := @augCarry 93 87 281 297 [32, 49, 100] 7 (by decide +kernel) rep87t297
theorem ac93t282 : Lower true (typeWord 282 :: vars 93) (graphGoal 93) 7 := @augCarry 93 87 282 298 [49, 100] 7 (by decide +kernel) rep87t298
theorem ac93t297 : Lower true (typeWord 297 :: vars 93) (graphGoal 93) 7 := @augCarry 93 87 297 279 [49, 100] 7 (by decide +kernel) rep87t279
theorem ac93t299 : Lower true (typeWord 299 :: vars 93) (graphGoal 93) 7 := @augCarry 93 87 299 279 [32, 49, 100] 7 (by decide +kernel) rep87t279
theorem ac93t301 : Lower true (typeWord 301 :: vars 93) (graphGoal 93) 7 := @augCarry 93 87 301 220 [49, 100] 7 (by decide +kernel) rep87t220
theorem ac103t100 : Lower true (typeWord 100 :: vars 103) (graphGoal 103) 7 := @augCarry 103 87 100 136 [98, 84] 7 (by decide +kernel) rep87t136
theorem ac103t126 : Lower true (typeWord 126 :: vars 103) (graphGoal 103) 7 := @augCarry 103 87 126 117 [98, 84] 7 (by decide +kernel) rep87t117
theorem ac103t136 : Lower true (typeWord 136 :: vars 103) (graphGoal 103) 7 := @augCarry 103 87 136 90 [32, 98, 84] 7 (by decide +kernel) rep87t90
theorem ac103t140 : Lower true (typeWord 140 :: vars 103) (graphGoal 103) 7 := @augCarry 103 87 140 117 [32, 98, 84] 7 (by decide +kernel) rep87t117
theorem ac103t209 : Lower true (typeWord 209 :: vars 103) (graphGoal 103) 7 := @augCarry 103 87 209 301 [98, 84] 7 (by decide +kernel) rep87t301
theorem ac103t217 : Lower true (typeWord 217 :: vars 103) (graphGoal 103) 7 := @augCarry 103 87 217 181 [98, 84] 7 (by decide +kernel) rep87t181
theorem ac110t47 : Lower true (typeWord 47 :: vars 110) (graphGoal 110) 7 := @augCarry 110 87 47 9 [97, 98, 99, 80, 100, 64] 7 (by decide +kernel) rep87t9
theorem ac110t100 : Lower true (typeWord 100 :: vars 110) (graphGoal 110) 7 := @augCarry 110 87 100 136 [97, 98, 48, 101, 100] 7 (by decide +kernel) rep87t136
theorem ac110t128 : Lower true (typeWord 128 :: vars 110) (graphGoal 110) 7 := @augCarry 110 87 128 90 [97, 98, 99, 80, 100, 64] 7 (by decide +kernel) rep87t90
theorem ac110t140 : Lower true (typeWord 140 :: vars 110) (graphGoal 110) 7 := @augCarry 110 87 140 117 [97, 98, 99, 80, 100, 64] 7 (by decide +kernel) rep87t117
theorem ac110t209 : Lower true (typeWord 209 :: vars 110) (graphGoal 110) 7 := @augCarry 110 87 209 181 [97, 98, 48, 101, 100] 7 (by decide +kernel) rep87t181
def ax91G : CompactGrid := (91,7,ax91P,ax91Q)
def ax91T : CompactTable := ((fun k => if k=7 then 0 else ax91Count k),ax91Path,ax91Live,ax91PoolIDs,ax91Bucket)
def ax91S : List (Nat × SliceSpec) := [(0, 1, 0, 90, 0, 0, 4, 4), (0, 2, 0, 89, 0, 0, 4, 4), (0, 8, 0, 83, 0, 0, 4, 4), (0, 16, 0, 75, 0, 0, 4, 4), (0, 64, 0, 27, 0, 0, 4, 4)]
def ax91D : RichDomains := (ax91S.map richSpecDomain).toArray
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ax91domains : RichValid 91 ax91D := by
  apply flexibleOK (m:=91) (ds:=ax91D) (prior:=[(27, 4), (75, 4), (83, 4), (89, 4), (90, 4)]) (extras:=[]) (specs:=ax91S)
  · intro e he
    simp only [List.mem_cons,List.not_mem_nil,or_false] at he
    rcases he with rfl | rfl | rfl | rfl | rfl
    · exact bound27
    · exact bound75
    · exact bound83
    · exact bound89
    · exact bound90
  · simp [ExtrasValid]
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ax91pairs : properPairs (graphGoal 91) (asRow ax91P) (asRow ax91Q) := compactPairs (g:=ax91G) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ax91autos : ∀ p ∈ ax91Perms, autoOK (graphGoal 91) (p.map swapRows).reverse = true := compactAutos_valid (by decide +kernel)
def ax91check (k : Nat) := richNode ax91G ax91T ax91D ax91Perms k
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem zc91k4p0 : chartBlock (ax91check 4) 0 8 = true := by
  iterate 2 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem zlev91k4 : chartBlock (ax91check 4) 0 8 = true :=
  zc91k4p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem zc91k5p0 : chartBlock (ax91check 5) 0 24 = true := by
  iterate 3 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem zlev91k5 : chartBlock (ax91check 5) 0 24 = true :=
  zc91k5p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem zc91k6p0 : chartBlock (ax91check 6) 0 4 = true := by
  iterate 1 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem zlev91k6 : chartBlock (ax91check 6) 0 4 = true :=
  zc91k6p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ax91blocks : ∀ k ≤ ax91G.top, chartBlock (ax91check k) 0 (ax91T.count k) = true := by
  intro k hk
  change k ≤ 7 at hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · exact zlev91k4
  · exact zlev91k5
  · exact zlev91k6
  · rfl
def ax91pools := richPoolList 91 ax91D [] (ax91PoolIDs 7 0)
def ax91links := linkedCandidates ax91G ax91T ax91Perms 6
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ax91base : Impossible true (graphGoal 91) 6 (vars 91).toFinset := @poolCut_sound true (vars 91) (graphGoal 91) (subcube (91-91) 0) 7 (@zeroSlice_sound 91 91 7 (by decide +kernel) bound91) [] (vars 91) (vars 91) 6 rfl (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ax91makes (t : Nat) (ok : primCheck ax91G ax91pools ax91links t = true) : Lower true (typeWord t :: vars 91) (graphGoal 91) 7 := by
  exact primOK (g:=ax91G) (pools:=ax91pools) (links:=ax91links) (t:=t) (hints:=4148) ax91pairs (richPool_valid (m:=91) (dom:=ax91D) (h:=[]) (picks:=ax91PoolIDs 7 0) ax91domains) (linkedCandidates_valid (g:=ax91G) (t:=ax91T) (perms:=ax91Perms) (k:=6) ax91autos (richAll (g:=ax91G) (t:=ax91T) (dom:=ax91D) (perms:=ax91Perms) ax91pairs ax91domains ax91autos ax91blocks 6 (by decide))) (by rfl) (by decide +kernel) (by decide +kernel) ax91base (by decide) ok
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem rep91t9 : Lower true (typeWord 9 :: vars 91) (graphGoal 91) 7 := ax91makes 9 (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem rep91t109 : Lower true (typeWord 109 :: vars 91) (graphGoal 91) 7 := ax91makes 109 (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem rep91t171 : Lower true (typeWord 171 :: vars 91) (graphGoal 91) 7 := ax91makes 171 (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem rep91t190 : Lower true (typeWord 190 :: vars 91) (graphGoal 91) 7 := ax91makes 190 (by decide +kernel)
theorem ac91t109 : Lower true (typeWord 109 :: vars 91) (graphGoal 91) 7 := rep91t109
theorem ac91t117 : Lower true (typeWord 117 :: vars 91) (graphGoal 91) 7 := @augCarry 91 91 117 109 [48, 65] 7 (by decide +kernel) rep91t109
theorem ac91t118 : Lower true (typeWord 118 :: vars 91) (graphGoal 91) 7 := @augCarry 91 91 118 109 [96, 67] 7 (by decide +kernel) rep91t109
theorem ac91t171 : Lower true (typeWord 171 :: vars 91) (graphGoal 91) 7 := rep91t171
theorem ac91t190 : Lower true (typeWord 190 :: vars 91) (graphGoal 91) 7 := rep91t190
theorem ac91t201 : Lower true (typeWord 201 :: vars 91) (graphGoal 91) 7 := @augCarry 91 91 201 171 [48, 65] 7 (by decide +kernel) rep91t171
theorem ac91t216 : Lower true (typeWord 216 :: vars 91) (graphGoal 91) 7 := @augCarry 91 91 216 190 [16, 99] 7 (by decide +kernel) rep91t190
theorem ac91t252 : Lower true (typeWord 252 :: vars 91) (graphGoal 91) 7 := @augCarry 91 91 252 171 [16, 99] 7 (by decide +kernel) rep91t171
theorem ac91t270 : Lower true (typeWord 270 :: vars 91) (graphGoal 91) 7 := @augCarry 91 91 270 171 [16, 97, 99, 100] 7 (by decide +kernel) rep91t171
theorem ac91t279 : Lower true (typeWord 279 :: vars 91) (graphGoal 91) 7 := @augCarry 91 91 279 190 [48, 65] 7 (by decide +kernel) rep91t190
theorem ac91t282 : Lower true (typeWord 282 :: vars 91) (graphGoal 91) 7 := @augCarry 91 91 282 171 [96, 65, 67, 100] 7 (by decide +kernel) rep91t171
theorem ac91t298 : Lower true (typeWord 298 :: vars 91) (graphGoal 91) 7 := @augCarry 91 91 298 171 [96, 67] 7 (by decide +kernel) rep91t171
theorem ac94t19 : Lower true (typeWord 19 :: vars 94) (graphGoal 94) 7 := @augCarry 94 91 19 9 [32] 7 (by decide +kernel) rep91t9
theorem ac94t55 : Lower true (typeWord 55 :: vars 94) (graphGoal 94) 7 := @augCarry 94 91 55 9 [98, 67, 96] 7 (by decide +kernel) rep91t9
theorem ac94t109 : Lower true (typeWord 109 :: vars 94) (graphGoal 94) 7 := @augCarry 94 91 109 109 [32] 7 (by decide +kernel) rep91t109
theorem ac94t118 : Lower true (typeWord 118 :: vars 94) (graphGoal 94) 7 := @augCarry 94 91 118 109 [98, 67, 96] 7 (by decide +kernel) rep91t109
theorem ac94t119 : Lower true (typeWord 119 :: vars 94) (graphGoal 94) 7 := @augCarry 94 91 119 109 [65, 50, 48] 7 (by decide +kernel) rep91t109
theorem ac94t137 : Lower true (typeWord 137 :: vars 94) (graphGoal 94) 7 := @augCarry 94 91 137 109 [16, 32, 99] 7 (by decide +kernel) rep91t109
theorem ac94t138 : Lower true (typeWord 138 :: vars 94) (graphGoal 94) 7 := @augCarry 94 91 138 109 [97, 66, 64] 7 (by decide +kernel) rep91t109
theorem ac94t181 : Lower true (typeWord 181 :: vars 94) (graphGoal 94) 7 := @augCarry 94 91 181 171 [16, 32, 99] 7 (by decide +kernel) rep91t171
theorem ac94t190 : Lower true (typeWord 190 :: vars 94) (graphGoal 94) 7 := @augCarry 94 91 190 190 [32] 7 (by decide +kernel) rep91t190
theorem ac94t191 : Lower true (typeWord 191 :: vars 94) (graphGoal 94) 7 := @augCarry 94 91 191 171 [49, 32, 100] 7 (by decide +kernel) rep91t171
theorem ac94t199 : Lower true (typeWord 199 :: vars 94) (graphGoal 94) 7 := @augCarry 94 91 199 190 [98, 67, 96] 7 (by decide +kernel) rep91t190
theorem ac94t200 : Lower true (typeWord 200 :: vars 94) (graphGoal 94) 7 := @augCarry 94 91 200 190 [97, 98, 48, 64, 96] 7 (by decide +kernel) rep91t190
theorem ac94t201 : Lower true (typeWord 201 :: vars 94) (graphGoal 94) 7 := @augCarry 94 91 201 171 [65, 50, 48] 7 (by decide +kernel) rep91t171
theorem ac94t217 : Lower true (typeWord 217 :: vars 94) (graphGoal 94) 7 := @augCarry 94 91 217 171 [16, 50, 67, 100, 96] 7 (by decide +kernel) rep91t171
theorem ac94t218 : Lower true (typeWord 218 :: vars 94) (graphGoal 94) 7 := @augCarry 94 91 218 190 [16, 32, 99] 7 (by decide +kernel) rep91t190
theorem ac94t219 : Lower true (typeWord 219 :: vars 94) (graphGoal 94) 7 := @augCarry 94 91 219 190 [65, 98, 67, 64, 96] 7 (by decide +kernel) rep91t190
theorem ac94t220 : Lower true (typeWord 220 :: vars 94) (graphGoal 94) 7 := @augCarry 94 91 220 171 [97, 66, 64] 7 (by decide +kernel) rep91t171
theorem ac94t262 : Lower true (typeWord 262 :: vars 94) (graphGoal 94) 7 := @augCarry 94 91 262 171 [32] 7 (by decide +kernel) rep91t171
theorem ac94t271 : Lower true (typeWord 271 :: vars 94) (graphGoal 94) 7 := @augCarry 94 91 271 190 [49, 32, 100] 7 (by decide +kernel) rep91t190
theorem ac94t272 : Lower true (typeWord 272 :: vars 94) (graphGoal 94) 7 := @augCarry 94 91 272 171 [97, 98, 48, 64, 96] 7 (by decide +kernel) rep91t171
theorem ac94t280 : Lower true (typeWord 280 :: vars 94) (graphGoal 94) 7 := @augCarry 94 91 280 190 [49, 66, 99, 100, 96] 7 (by decide +kernel) rep91t190
theorem ac94t281 : Lower true (typeWord 281 :: vars 94) (graphGoal 94) 7 := @augCarry 94 91 281 190 [65, 50, 48] 7 (by decide +kernel) rep91t190
theorem ac94t282 : Lower true (typeWord 282 :: vars 94) (graphGoal 94) 7 := @augCarry 94 91 282 171 [65, 98, 67, 64, 96] 7 (by decide +kernel) rep91t171
theorem ac94t298 : Lower true (typeWord 298 :: vars 94) (graphGoal 94) 7 := @augCarry 94 91 298 171 [98, 67, 96] 7 (by decide +kernel) rep91t171
theorem ac94t299 : Lower true (typeWord 299 :: vars 94) (graphGoal 94) 7 := @augCarry 94 91 299 190 [16, 50, 67, 100, 96] 7 (by decide +kernel) rep91t190
theorem ac94t300 : Lower true (typeWord 300 :: vars 94) (graphGoal 94) 7 := @augCarry 94 91 300 190 [97, 66, 64] 7 (by decide +kernel) rep91t190
theorem ac94t301 : Lower true (typeWord 301 :: vars 94) (graphGoal 94) 7 := @augCarry 94 91 301 171 [49, 66, 99, 100, 96] 7 (by decide +kernel) rep91t171
def ax107G : CompactGrid := (107,7,ax107P,ax107Q)
def ax107T : CompactTable := ((fun k => if k=7 then 0 else ax107Count k),ax107Path,ax107Live,ax107PoolIDs,ax107Bucket)
def ax107S : List (Nat × SliceSpec) := [(0, 1, 0, 106, 0, 0, 5, 5), (0, 2, 0, 105, 0, 0, 5, 5), (0, 8, 0, 99, 0, 0, 5, 5), (0, 64, 0, 43, 0, 0, 5, 5), (0, 32, 0, 75, 0, 0, 4, 4), (0, 3, 0, 104, 0, 0, 4, 4), (0, 10, 0, 97, 0, 0, 4, 4), (0, 65, 0, 42, 0, 0, 4, 4)]
def ax107D : RichDomains := (ax107S.map richSpecDomain).toArray
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ax107domains : RichValid 107 ax107D := by
  apply flexibleOK (m:=107) (ds:=ax107D) (prior:=[(42, 4), (43, 5), (75, 4), (97, 4), (99, 5), (104, 4), (105, 5), (106, 5)]) (extras:=[]) (specs:=ax107S)
  · intro e he
    simp only [List.mem_cons,List.not_mem_nil,or_false] at he
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact bound42
    · exact bound43
    · exact bound75
    · exact bound97
    · exact bound99
    · exact bound104
    · exact bound105
    · exact bound106
  · simp [ExtrasValid]
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ax107pairs : properPairs (graphGoal 107) (asRow ax107P) (asRow ax107Q) := compactPairs (g:=ax107G) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ax107autos : ∀ p ∈ ax107Perms, autoOK (graphGoal 107) (p.map swapRows).reverse = true := compactAutos_valid (by decide +kernel)
def ax107check (k : Nat) := richNode ax107G ax107T ax107D ax107Perms k
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem zc107k3p0 : chartBlock (ax107check 3) 0 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem zlev107k3 : chartBlock (ax107check 3) 0 2 = true :=
  zc107k3p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem zc107k4p0 : chartBlock (ax107check 4) 0 15 = true := by
  iterate 3 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem zlev107k4 : chartBlock (ax107check 4) 0 15 = true :=
  zc107k4p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem zc107k5p0 : chartBlock (ax107check 5) 0 13 = true := by
  iterate 3 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem zlev107k5 : chartBlock (ax107check 5) 0 13 = true :=
  zc107k5p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem zc107k6p0 : chartBlock (ax107check 6) 0 5 = true := by
  iterate 1 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem zlev107k6 : chartBlock (ax107check 6) 0 5 = true :=
  zc107k6p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ax107blocks : ∀ k ≤ ax107G.top, chartBlock (ax107check k) 0 (ax107T.count k) = true := by
  intro k hk
  change k ≤ 7 at hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · exact zlev107k3
  · exact zlev107k4
  · exact zlev107k5
  · exact zlev107k6
  · rfl
def ax107pools := richPoolList 107 ax107D [] (ax107PoolIDs 7 0)
def ax107links := linkedCandidates ax107G ax107T ax107Perms 6
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ax107base : Impossible true (graphGoal 107) 6 (vars 107).toFinset := @poolCut_sound true (vars 107) (graphGoal 107) (subcube (107-107) 0) 7 (@zeroSlice_sound 107 107 7 (by decide +kernel) bound107) [] (vars 107) (vars 107) 6 rfl (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ax107makes (t : Nat) (ok : primCheck ax107G ax107pools ax107links t = true) : Lower true (typeWord t :: vars 107) (graphGoal 107) 7 := by
  exact primOK (g:=ax107G) (pools:=ax107pools) (links:=ax107links) (t:=t) (hints:=4149) ax107pairs (richPool_valid (m:=107) (dom:=ax107D) (h:=[]) (picks:=ax107PoolIDs 7 0) ax107domains) (linkedCandidates_valid (g:=ax107G) (t:=ax107T) (perms:=ax107Perms) (k:=6) ax107autos (richAll (g:=ax107G) (t:=ax107T) (dom:=ax107D) (perms:=ax107Perms) ax107pairs ax107domains ax107autos ax107blocks 6 (by decide))) (by rfl) (by decide +kernel) (by decide +kernel) ax107base (by decide) ok
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem rep107t9 : Lower true (typeWord 9 :: vars 107) (graphGoal 107) 7 := ax107makes 9 (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem rep107t27 : Lower true (typeWord 27 :: vars 107) (graphGoal 107) 7 := ax107makes 27 (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem rep107t48 : Lower true (typeWord 48 :: vars 107) (graphGoal 107) 7 := ax107makes 48 (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem rep107t90 : Lower true (typeWord 90 :: vars 107) (graphGoal 107) 7 := ax107makes 90 (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem rep107t109 : Lower true (typeWord 109 :: vars 107) (graphGoal 107) 7 := ax107makes 109 (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem rep107t126 : Lower true (typeWord 126 :: vars 107) (graphGoal 107) 7 := ax107makes 126 (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem rep107t138 : Lower true (typeWord 138 :: vars 107) (graphGoal 107) 7 := ax107makes 138 (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem rep107t171 : Lower true (typeWord 171 :: vars 107) (graphGoal 107) 7 := ax107makes 171 (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem rep107t189 : Lower true (typeWord 189 :: vars 107) (graphGoal 107) 7 := ax107makes 189 (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem rep107t190 : Lower true (typeWord 190 :: vars 107) (graphGoal 107) 7 := ax107makes 190 (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem rep107t207 : Lower true (typeWord 207 :: vars 107) (graphGoal 107) 7 := ax107makes 207 (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem rep107t210 : Lower true (typeWord 210 :: vars 107) (graphGoal 107) 7 := ax107makes 210 (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem rep107t270 : Lower true (typeWord 270 :: vars 107) (graphGoal 107) 7 := ax107makes 270 (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem rep107t271 : Lower true (typeWord 271 :: vars 107) (graphGoal 107) 7 := ax107makes 271 (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem rep107t288 : Lower true (typeWord 288 :: vars 107) (graphGoal 107) 7 := ax107makes 288 (by decide +kernel)
theorem ac107t9 : Lower true (typeWord 9 :: vars 107) (graphGoal 107) 7 := rep107t9
theorem ac107t48 : Lower true (typeWord 48 :: vars 107) (graphGoal 107) 7 := rep107t48
theorem ac107t90 : Lower true (typeWord 90 :: vars 107) (graphGoal 107) 7 := rep107t90
theorem ac107t126 : Lower true (typeWord 126 :: vars 107) (graphGoal 107) 7 := rep107t126
theorem ac107t127 : Lower true (typeWord 127 :: vars 107) (graphGoal 107) 7 := @augCarry 107 107 127 126 [16, 99] 7 (by decide +kernel) rep107t126
theorem ac107t135 : Lower true (typeWord 135 :: vars 107) (graphGoal 107) 7 := @augCarry 107 107 135 109 [16, 99] 7 (by decide +kernel) rep107t109
theorem ac107t171 : Lower true (typeWord 171 :: vars 107) (graphGoal 107) 7 := rep107t171
theorem ac107t208 : Lower true (typeWord 208 :: vars 107) (graphGoal 107) 7 := @augCarry 107 107 208 207 [16, 99] 7 (by decide +kernel) rep107t207
theorem ac107t216 : Lower true (typeWord 216 :: vars 107) (graphGoal 107) 7 := @augCarry 107 107 216 190 [16, 99] 7 (by decide +kernel) rep107t190
theorem ac107t298 : Lower true (typeWord 298 :: vars 107) (graphGoal 107) 7 := @augCarry 107 107 298 270 [16, 99] 7 (by decide +kernel) rep107t270
theorem ac109t29 : Lower true (typeWord 29 :: vars 109) (graphGoal 109) 7 := @augCarry 109 107 29 9 [48, 33, 101] 7 (by decide +kernel) rep107t9
theorem ac109t47 : Lower true (typeWord 47 :: vars 109) (graphGoal 109) 7 := @augCarry 109 107 47 27 [96, 98, 49, 81, 97] 7 (by decide +kernel) rep107t27
theorem ac109t110 : Lower true (typeWord 110 :: vars 109) (graphGoal 109) 7 := @augCarry 109 107 110 90 [48, 33, 101] 7 (by decide +kernel) rep107t90
theorem ac109t126 : Lower true (typeWord 126 :: vars 109) (graphGoal 109) 7 := @augCarry 109 107 126 138 [48, 33, 101] 7 (by decide +kernel) rep107t138
theorem ac109t129 : Lower true (typeWord 129 :: vars 109) (graphGoal 109) 7 := @augCarry 109 107 129 109 [96, 98, 49, 81, 97] 7 (by decide +kernel) rep107t109
theorem ac109t191 : Lower true (typeWord 191 :: vars 109) (graphGoal 109) 7 := @augCarry 109 107 191 171 [96, 98, 49, 81, 97] 7 (by decide +kernel) rep107t171
theorem ac109t209 : Lower true (typeWord 209 :: vars 109) (graphGoal 109) 7 := @augCarry 109 107 209 189 [96, 98, 49, 81, 97] 7 (by decide +kernel) rep107t189
theorem ac109t221 : Lower true (typeWord 221 :: vars 109) (graphGoal 109) 7 := @augCarry 109 107 221 210 [96, 98, 49, 81, 97] 7 (by decide +kernel) rep107t210
theorem ac109t272 : Lower true (typeWord 272 :: vars 109) (graphGoal 109) 7 := @augCarry 109 107 272 171 [48, 33, 101] 7 (by decide +kernel) rep107t171
theorem ac109t290 : Lower true (typeWord 290 :: vars 109) (graphGoal 109) 7 := @augCarry 109 107 290 270 [96, 98, 49, 81, 97] 7 (by decide +kernel) rep107t270
theorem ac109t291 : Lower true (typeWord 291 :: vars 109) (graphGoal 109) 7 := @augCarry 109 107 291 271 [96, 98, 49, 81, 97] 7 (by decide +kernel) rep107t271
theorem ac109t299 : Lower true (typeWord 299 :: vars 109) (graphGoal 109) 7 := @augCarry 109 107 299 288 [96, 98, 49, 81, 97] 7 (by decide +kernel) rep107t288
def ax63G : CompactGrid := (63,9,ax63P,ax63Q)
def ax63T : CompactTable := ((fun k => if k=9 then 0 else ax63Count k),ax63Path,ax63Live,ax63PoolIDs,ax63Bucket)
def ax63S : List (Nat × SliceSpec) := [(0, 1, 0, 62, 0, 0, 7, 7), (30, 1, 0, 62, 0, 0, 7, 7), (111, 1, 0, 62, 0, 0, 7, 7), (119, 1, 0, 62, 0, 0, 7, 7), (120, 1, 0, 62, 0, 0, 7, 7), (129, 1, 0, 62, 0, 0, 7, 7), (182, 1, 0, 62, 0, 0, 7, 7), (191, 1, 0, 62, 0, 0, 7, 7), (192, 1, 0, 62, 0, 0, 7, 7), (273, 1, 0, 62, 0, 0, 7, 7), (282, 1, 0, 62, 0, 0, 7, 7), (291, 1, 0, 62, 0, 0, 7, 7), (292, 1, 0, 62, 0, 0, 7, 7), (0, 2, 0, 61, 0, 0, 7, 7), (30, 2, 0, 61, 0, 0, 7, 7), (40, 2, 0, 61, 0, 0, 7, 7), (111, 2, 0, 61, 0, 0, 7, 7), (121, 2, 0, 61, 0, 0, 7, 7), (130, 2, 0, 61, 0, 0, 7, 7), (181, 2, 0, 61, 0, 0, 7, 7), (192, 2, 0, 61, 0, 0, 7, 7), (201, 2, 0, 61, 0, 0, 7, 7), (202, 2, 0, 61, 0, 0, 7, 7), (211, 2, 0, 61, 0, 0, 7, 7), (273, 2, 0, 61, 0, 0, 7, 7), (282, 2, 0, 61, 0, 0, 7, 7), (283, 2, 0, 61, 0, 0, 7, 7), (291, 2, 0, 61, 0, 0, 7, 7), (292, 2, 0, 61, 0, 0, 7, 7), (0, 16, 0, 47, 0, 0, 7, 7), (20, 16, 0, 47, 0, 0, 7, 7), (100, 16, 0, 47, 0, 0, 7, 7), (101, 16, 0, 47, 0, 0, 7, 7), (111, 16, 0, 47, 0, 0, 7, 7), (181, 16, 0, 47, 0, 0, 7, 7), (182, 16, 0, 47, 0, 0, 7, 7), (192, 16, 0, 47, 0, 0, 7, 7), (0, 32, 0, 31, 0, 0, 7, 7), (111, 32, 0, 31, 0, 0, 7, 7), (119, 32, 0, 31, 0, 0, 7, 7), (181, 32, 0, 31, 0, 0, 7, 7), (182, 32, 0, 31, 0, 0, 7, 7), (192, 32, 0, 31, 0, 0, 7, 7), (100, 8, 0, 55, 0, 0, 6, 6), (0, 0, 4, 42, 17, 983055, 6, 4), (0, 0, 8, 21, 34, 15728880, 6, 4), (0, 5, 0, 58, 0, 0, 5, 5), (0, 1, 4, 42, 16, 983040, 5, 4)]
def ax63D : RichDomains := (ax63S.map richSpecDomain).toArray
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ax63domains : RichValid 63 ax63D := by
  apply flexibleOK (m:=63) (ds:=ax63D) (prior:=[(21, 4), (31, 7), (42, 4), (47, 7), (58, 5), (61, 7), (62, 7)]) (extras:=[(62, 7, [29, 110, 118, 119, 128, 181, 190, 191, 272, 281, 290, 291]), (61, 7, [29, 39, 110, 120, 129, 180, 191, 200, 201, 210, 272, 281, 282, 290, 291]), (47, 7, [19, 99, 100, 110, 180, 181, 191]), (31, 7, [110, 118, 180, 181, 191]), (55, 6, [99])]) (specs:=ax63S)
  · intro e he
    simp only [List.mem_cons,List.not_mem_nil,or_false] at he
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact bound21
    · exact bound31
    · exact bound42
    · exact bound47
    · exact bound58
    · exact bound61
    · exact bound62
  · intro e he
    simp only [List.mem_cons,List.not_mem_nil,or_false] at he
    rcases he with rfl | rfl | rfl | rfl | rfl
    · intro t ht
      simp only [List.mem_cons,List.not_mem_nil,or_false] at ht
      rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact ac62t29
      · exact ac62t110
      · exact ac62t118
      · exact ac62t119
      · exact ac62t128
      · exact ac62t181
      · exact ac62t190
      · exact ac62t191
      · exact ac62t272
      · exact ac62t281
      · exact ac62t290
      · exact ac62t291
    · intro t ht
      simp only [List.mem_cons,List.not_mem_nil,or_false] at ht
      rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact ac61t29
      · exact ac61t39
      · exact ac61t110
      · exact ac61t120
      · exact ac61t129
      · exact ac61t180
      · exact ac61t191
      · exact ac61t200
      · exact ac61t201
      · exact ac61t210
      · exact ac61t272
      · exact ac61t281
      · exact ac61t282
      · exact ac61t290
      · exact ac61t291
    · intro t ht
      simp only [List.mem_cons,List.not_mem_nil,or_false] at ht
      rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact ac47t19
      · exact ac47t99
      · exact ac47t100
      · exact ac47t110
      · exact ac47t180
      · exact ac47t181
      · exact ac47t191
    · intro t ht
      simp only [List.mem_cons,List.not_mem_nil,or_false] at ht
      rcases ht with rfl | rfl | rfl | rfl | rfl
      · exact ac31t110
      · exact ac31t118
      · exact ac31t180
      · exact ac31t181
      · exact ac31t191
    · intro t ht
      simp only [List.mem_cons,List.not_mem_nil,or_false] at ht
      rcases ht with rfl
      · exact ac55t99
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ax63pairs : properPairs (graphGoal 63) (asRow ax63P) (asRow ax63Q) := compactPairs (g:=ax63G) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ax63autos : ∀ p ∈ ax63Perms, autoOK (graphGoal 63) (p.map swapRows).reverse = true := compactAutos_valid (by decide +kernel)
def ax63check (k : Nat) := richNode ax63G ax63T ax63D ax63Perms k
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem zc63k7p0 : chartBlock (ax63check 7) 0 3 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem zlev63k7 : chartBlock (ax63check 7) 0 3 = true :=
  zc63k7p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem zc63k8p0 : chartBlock (ax63check 8) 0 7 = true := by
  iterate 2 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem zlev63k8 : chartBlock (ax63check 8) 0 7 = true :=
  zc63k8p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ax63blocks : ∀ k ≤ ax63G.top, chartBlock (ax63check k) 0 (ax63T.count k) = true := by
  intro k hk
  change k ≤ 9 at hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact zlev63k7
  · exact zlev63k8
  · rfl
def ax63pools := richPoolList 63 ax63D [] (ax63PoolIDs 9 0)
def ax63links := linkedCandidates ax63G ax63T ax63Perms 8
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ax63base : Impossible true (graphGoal 63) 8 (vars 63).toFinset := @poolCut_sound true (vars 63) (graphGoal 63) (subcube (63-63) 0) 9 (@zeroSlice_sound 63 63 9 (by decide +kernel) bound63) [] (vars 63) (vars 63) 8 rfl (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ax63makes (t : Nat) (ok : primCheck ax63G ax63pools ax63links t = true) : Lower true (typeWord t :: vars 63) (graphGoal 63) 9 := by
  exact primOK (g:=ax63G) (pools:=ax63pools) (links:=ax63links) (t:=t) (hints:=4146) ax63pairs (richPool_valid (m:=63) (dom:=ax63D) (h:=[]) (picks:=ax63PoolIDs 9 0) ax63domains) (linkedCandidates_valid (g:=ax63G) (t:=ax63T) (perms:=ax63Perms) (k:=8) ax63autos (richAll (g:=ax63G) (t:=ax63T) (dom:=ax63D) (perms:=ax63Perms) ax63pairs ax63domains ax63autos ax63blocks 8 (by decide))) (by rfl) (by decide +kernel) (by decide +kernel) ax63base (by decide) ok
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem rep63t100 : Lower true (typeWord 100 :: vars 63) (graphGoal 63) 9 := ax63makes 100 (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem rep63t108 : Lower true (typeWord 108 :: vars 63) (graphGoal 63) 9 := ax63makes 108 (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem rep63t110 : Lower true (typeWord 110 :: vars 63) (graphGoal 63) 9 := ax63makes 110 (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem rep63t118 : Lower true (typeWord 118 :: vars 63) (graphGoal 63) 9 := ax63makes 118 (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem rep63t120 : Lower true (typeWord 120 :: vars 63) (graphGoal 63) 9 := ax63makes 120 (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem rep63t126 : Lower true (typeWord 126 :: vars 63) (graphGoal 63) 9 := ax63makes 126 (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem rep63t129 : Lower true (typeWord 129 :: vars 63) (graphGoal 63) 9 := ax63makes 129 (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem rep63t272 : Lower true (typeWord 272 :: vars 63) (graphGoal 63) 9 := ax63makes 272 (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem rep63t281 : Lower true (typeWord 281 :: vars 63) (graphGoal 63) 9 := ax63makes 281 (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem rep63t282 : Lower true (typeWord 282 :: vars 63) (graphGoal 63) 9 := ax63makes 282 (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem rep63t290 : Lower true (typeWord 290 :: vars 63) (graphGoal 63) 9 := ax63makes 290 (by decide +kernel)
theorem ac63t99 : Lower true (typeWord 99 :: vars 63) (graphGoal 63) 9 := @augCarry 63 63 99 129 [80, 65, 50] 9 (by decide +kernel) rep63t129
theorem ac63t100 : Lower true (typeWord 100 :: vars 63) (graphGoal 63) 9 := @augCarry 63 63 100 108 [16, 50, 84] 9 (by decide +kernel) rep63t108
theorem ac63t108 : Lower true (typeWord 108 :: vars 63) (graphGoal 63) 9 := @augCarry 63 63 108 100 [16, 50, 84] 9 (by decide +kernel) rep63t100
theorem ac63t109 : Lower true (typeWord 109 :: vars 63) (graphGoal 63) 9 := @augCarry 63 63 109 129 [64, 81] 9 (by decide +kernel) rep63t129
theorem ac63t110 : Lower true (typeWord 110 :: vars 63) (graphGoal 63) 9 := rep63t110
theorem ac63t118 : Lower true (typeWord 118 :: vars 63) (graphGoal 63) 9 := @augCarry 63 63 118 126 [64, 81] 9 (by decide +kernel) rep63t126
theorem ac63t119 : Lower true (typeWord 119 :: vars 63) (graphGoal 63) 9 := @augCarry 63 63 119 129 [16, 50, 84] 9 (by decide +kernel) rep63t129
theorem ac63t120 : Lower true (typeWord 120 :: vars 63) (graphGoal 63) 9 := rep63t120
theorem ac63t126 : Lower true (typeWord 126 :: vars 63) (graphGoal 63) 9 := @augCarry 63 63 126 118 [64, 81] 9 (by decide +kernel) rep63t118
theorem ac63t180 : Lower true (typeWord 180 :: vars 63) (graphGoal 63) 9 := @augCarry 63 63 180 281 [64, 81] 9 (by decide +kernel) rep63t281
theorem ac63t181 : Lower true (typeWord 181 :: vars 63) (graphGoal 63) 9 := @augCarry 63 63 181 290 [64, 81] 9 (by decide +kernel) rep63t290
theorem ac63t189 : Lower true (typeWord 189 :: vars 63) (graphGoal 63) 9 := @augCarry 63 63 189 282 [64, 81] 9 (by decide +kernel) rep63t282
theorem ac63t190 : Lower true (typeWord 190 :: vars 63) (graphGoal 63) 9 := @augCarry 63 63 190 281 [80, 65, 50] 9 (by decide +kernel) rep63t281
theorem ac63t191 : Lower true (typeWord 191 :: vars 63) (graphGoal 63) 9 := @augCarry 63 63 191 272 [16, 50, 84] 9 (by decide +kernel) rep63t272
theorem ac63t272 : Lower true (typeWord 272 :: vars 63) (graphGoal 63) 9 := rep63t272
theorem ac63t281 : Lower true (typeWord 281 :: vars 63) (graphGoal 63) 9 := rep63t281
theorem ac63t282 : Lower true (typeWord 282 :: vars 63) (graphGoal 63) 9 := rep63t282
theorem ac63t290 : Lower true (typeWord 290 :: vars 63) (graphGoal 63) 9 := rep63t290
theorem ac63t291 : Lower true (typeWord 291 :: vars 63) (graphGoal 63) 9 := @augCarry 63 63 291 281 [16, 50, 84] 9 (by decide +kernel) rep63t281
def ax95G : CompactGrid := (95,10,ax95P,ax95Q)
def ax95T : CompactTable := ((fun k => if k=10 then 0 else ax95Count k),ax95Path,ax95Live,ax95PoolIDs,ax95Bucket)
def ax95S : List (Nat × SliceSpec) := [(0, 1, 0, 94, 0, 0, 7, 7), (20, 1, 0, 94, 0, 0, 7, 7), (56, 1, 0, 94, 0, 0, 7, 7), (110, 1, 0, 94, 0, 0, 7, 7), (119, 1, 0, 94, 0, 0, 7, 7), (120, 1, 0, 94, 0, 0, 7, 7), (138, 1, 0, 94, 0, 0, 7, 7), (139, 1, 0, 94, 0, 0, 7, 7), (182, 1, 0, 94, 0, 0, 7, 7), (191, 1, 0, 94, 0, 0, 7, 7), (192, 1, 0, 94, 0, 0, 7, 7), (200, 1, 0, 94, 0, 0, 7, 7), (201, 1, 0, 94, 0, 0, 7, 7), (202, 1, 0, 94, 0, 0, 7, 7), (218, 1, 0, 94, 0, 0, 7, 7), (219, 1, 0, 94, 0, 0, 7, 7), (220, 1, 0, 94, 0, 0, 7, 7), (221, 1, 0, 94, 0, 0, 7, 7), (263, 1, 0, 94, 0, 0, 7, 7), (272, 1, 0, 94, 0, 0, 7, 7), (273, 1, 0, 94, 0, 0, 7, 7), (281, 1, 0, 94, 0, 0, 7, 7), (282, 1, 0, 94, 0, 0, 7, 7), (283, 1, 0, 94, 0, 0, 7, 7), (299, 1, 0, 94, 0, 0, 7, 7), (300, 1, 0, 94, 0, 0, 7, 7), (301, 1, 0, 94, 0, 0, 7, 7), (302, 1, 0, 94, 0, 0, 7, 7), (0, 2, 0, 93, 0, 0, 7, 7), (28, 2, 0, 93, 0, 0, 7, 7), (37, 2, 0, 93, 0, 0, 7, 7), (39, 2, 0, 93, 0, 0, 7, 7), (40, 2, 0, 93, 0, 0, 7, 7), (55, 2, 0, 93, 0, 0, 7, 7), (57, 2, 0, 93, 0, 0, 7, 7), (59, 2, 0, 93, 0, 0, 7, 7), (109, 2, 0, 93, 0, 0, 7, 7), (111, 2, 0, 93, 0, 0, 7, 7), (118, 2, 0, 93, 0, 0, 7, 7), (120, 2, 0, 93, 0, 0, 7, 7), (121, 2, 0, 93, 0, 0, 7, 7), (136, 2, 0, 93, 0, 0, 7, 7), (138, 2, 0, 93, 0, 0, 7, 7), (139, 2, 0, 93, 0, 0, 7, 7), (181, 2, 0, 93, 0, 0, 7, 7), (190, 2, 0, 93, 0, 0, 7, 7), (199, 2, 0, 93, 0, 0, 7, 7), (201, 2, 0, 93, 0, 0, 7, 7), (202, 2, 0, 93, 0, 0, 7, 7), (217, 2, 0, 93, 0, 0, 7, 7), (219, 2, 0, 93, 0, 0, 7, 7), (220, 2, 0, 93, 0, 0, 7, 7), (221, 2, 0, 93, 0, 0, 7, 7), (262, 2, 0, 93, 0, 0, 7, 7), (271, 2, 0, 93, 0, 0, 7, 7), (273, 2, 0, 93, 0, 0, 7, 7), (280, 2, 0, 93, 0, 0, 7, 7), (282, 2, 0, 93, 0, 0, 7, 7), (283, 2, 0, 93, 0, 0, 7, 7), (298, 2, 0, 93, 0, 0, 7, 7), (300, 2, 0, 93, 0, 0, 7, 7), (302, 2, 0, 93, 0, 0, 7, 7), (0, 4, 0, 91, 0, 0, 7, 7), (110, 4, 0, 91, 0, 0, 7, 7), (118, 4, 0, 91, 0, 0, 7, 7), (119, 4, 0, 91, 0, 0, 7, 7), (172, 4, 0, 91, 0, 0, 7, 7), (191, 4, 0, 91, 0, 0, 7, 7), (202, 4, 0, 91, 0, 0, 7, 7), (217, 4, 0, 91, 0, 0, 7, 7), (253, 4, 0, 91, 0, 0, 7, 7), (271, 4, 0, 91, 0, 0, 7, 7), (280, 4, 0, 91, 0, 0, 7, 7), (283, 4, 0, 91, 0, 0, 7, 7), (299, 4, 0, 91, 0, 0, 7, 7), (0, 8, 0, 87, 0, 0, 7, 7), (10, 8, 0, 87, 0, 0, 7, 7), (59, 8, 0, 87, 0, 0, 7, 7), (91, 8, 0, 87, 0, 0, 7, 7), (101, 8, 0, 87, 0, 0, 7, 7), (118, 8, 0, 87, 0, 0, 7, 7), (119, 8, 0, 87, 0, 0, 7, 7), (120, 8, 0, 87, 0, 0, 7, 7), (136, 8, 0, 87, 0, 0, 7, 7), (137, 8, 0, 87, 0, 0, 7, 7), (138, 8, 0, 87, 0, 0, 7, 7), (172, 8, 0, 87, 0, 0, 7, 7), (181, 8, 0, 87, 0, 0, 7, 7), (199, 8, 0, 87, 0, 0, 7, 7), (200, 8, 0, 87, 0, 0, 7, 7), (201, 8, 0, 87, 0, 0, 7, 7), (217, 8, 0, 87, 0, 0, 7, 7), (218, 8, 0, 87, 0, 0, 7, 7), (219, 8, 0, 87, 0, 0, 7, 7), (221, 8, 0, 87, 0, 0, 7, 7), (253, 8, 0, 87, 0, 0, 7, 7), (262, 8, 0, 87, 0, 0, 7, 7), (263, 8, 0, 87, 0, 0, 7, 7), (280, 8, 0, 87, 0, 0, 7, 7), (298, 8, 0, 87, 0, 0, 7, 7), (299, 8, 0, 87, 0, 0, 7, 7), (302, 8, 0, 87, 0, 0, 7, 7), (0, 16, 0, 79, 0, 0, 7, 7), (10, 16, 0, 79, 0, 0, 7, 7), (20, 16, 0, 79, 0, 0, 7, 7), (56, 16, 0, 79, 0, 0, 7, 7), (91, 16, 0, 79, 0, 0, 7, 7), (101, 16, 0, 79, 0, 0, 7, 7), (110, 16, 0, 79, 0, 0, 7, 7), (139, 16, 0, 79, 0, 0, 7, 7), (172, 16, 0, 79, 0, 0, 7, 7), (191, 16, 0, 79, 0, 0, 7, 7), (192, 16, 0, 79, 0, 0, 7, 7), (217, 16, 0, 79, 0, 0, 7, 7), (218, 16, 0, 79, 0, 0, 7, 7), (219, 16, 0, 79, 0, 0, 7, 7), (220, 16, 0, 79, 0, 0, 7, 7), (253, 16, 0, 79, 0, 0, 7, 7), (262, 16, 0, 79, 0, 0, 7, 7), (263, 16, 0, 79, 0, 0, 7, 7), (272, 16, 0, 79, 0, 0, 7, 7), (298, 16, 0, 79, 0, 0, 7, 7), (299, 16, 0, 79, 0, 0, 7, 7), (301, 16, 0, 79, 0, 0, 7, 7), (0, 64, 0, 31, 0, 0, 7, 7), (20, 64, 0, 31, 0, 0, 7, 7), (109, 64, 0, 31, 0, 0, 7, 7), (110, 64, 0, 31, 0, 0, 7, 7), (119, 64, 0, 31, 0, 0, 7, 7), (181, 64, 0, 31, 0, 0, 7, 7), (191, 64, 0, 31, 0, 0, 7, 7), (199, 64, 0, 31, 0, 0, 7, 7), (263, 64, 0, 31, 0, 0, 7, 7), (283, 64, 0, 31, 0, 0, 7, 7), (0, 0, 2, 69, 24, 1044480, 6, 4), (0, 0, 8, 21, 66, 251658480, 6, 4), (0, 10, 0, 85, 0, 0, 5, 5), (0, 18, 0, 77, 0, 0, 5, 5), (0, 72, 0, 23, 0, 0, 5, 5), (0, 2, 8, 21, 64, 251658240, 5, 4), (0, 8, 2, 69, 16, 983040, 5, 4), (0, 16, 2, 69, 8, 61440, 5, 4), (0, 64, 8, 21, 2, 240, 5, 4), (0, 3, 0, 92, 0, 0, 4, 4), (0, 5, 0, 90, 0, 0, 4, 4), (0, 6, 0, 89, 0, 0, 4, 4), (0, 17, 0, 78, 0, 0, 4, 4), (0, 20, 0, 75, 0, 0, 4, 4), (0, 65, 0, 30, 0, 0, 4, 4), (0, 68, 0, 27, 0, 0, 4, 4), (0, 24, 2, 69, 0, 0, 4, 4), (0, 26, 0, 69, 0, 0, 4, 4), (0, 66, 8, 21, 0, 0, 4, 4), (0, 74, 0, 21, 0, 0, 4, 4)]
def ax95D : RichDomains := (ax95S.map richSpecDomain).toArray
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ax95domains : RichValid 95 ax95D := by
  apply flexibleOK (m:=95) (ds:=ax95D) (prior:=[(21, 4), (23, 5), (27, 4), (30, 4), (31, 7), (69, 4), (75, 4), (77, 5), (78, 4), (79, 7), (85, 5), (87, 7), (89, 4), (90, 4), (91, 7), (92, 4), (93, 7), (94, 7)]) (extras:=[(94, 7, [19, 55, 109, 118, 119, 137, 138, 181, 190, 191, 199, 200, 201, 217, 218, 219, 220, 262, 271, 272, 280, 281, 282, 298, 299, 300, 301]), (93, 7, [27, 36, 38, 39, 54, 56, 58, 108, 110, 117, 119, 120, 135, 137, 138, 180, 189, 198, 200, 201, 216, 218, 219, 220, 261, 270, 272, 279, 281, 282, 297, 299, 301]), (91, 7, [109, 117, 118, 171, 190, 201, 216, 252, 270, 279, 282, 298]), (87, 7, [9, 58, 90, 100, 117, 118, 119, 135, 136, 137, 171, 180, 198, 199, 200, 216, 217, 218, 220, 252, 261, 262, 279, 297, 298, 301]), (79, 7, [9, 19, 55, 90, 100, 109, 138, 171, 190, 191, 216, 217, 218, 219, 252, 261, 262, 271, 297, 298, 300]), (31, 7, [19, 108, 109, 118, 180, 190, 198, 262, 282])]) (specs:=ax95S)
  · intro e he
    simp only [List.mem_cons,List.not_mem_nil,or_false] at he
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact bound21
    · exact bound23
    · exact bound27
    · exact bound30
    · exact bound31
    · exact bound69
    · exact bound75
    · exact bound77
    · exact bound78
    · exact bound79
    · exact bound85
    · exact bound87
    · exact bound89
    · exact bound90
    · exact bound91
    · exact bound92
    · exact bound93
    · exact bound94
  · intro e he
    simp only [List.mem_cons,List.not_mem_nil,or_false] at he
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl
    · intro t ht
      simp only [List.mem_cons,List.not_mem_nil,or_false] at ht
      rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact ac94t19
      · exact ac94t55
      · exact ac94t109
      · exact ac94t118
      · exact ac94t119
      · exact ac94t137
      · exact ac94t138
      · exact ac94t181
      · exact ac94t190
      · exact ac94t191
      · exact ac94t199
      · exact ac94t200
      · exact ac94t201
      · exact ac94t217
      · exact ac94t218
      · exact ac94t219
      · exact ac94t220
      · exact ac94t262
      · exact ac94t271
      · exact ac94t272
      · exact ac94t280
      · exact ac94t281
      · exact ac94t282
      · exact ac94t298
      · exact ac94t299
      · exact ac94t300
      · exact ac94t301
    · intro t ht
      simp only [List.mem_cons,List.not_mem_nil,or_false] at ht
      rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact ac93t27
      · exact ac93t36
      · exact ac93t38
      · exact ac93t39
      · exact ac93t54
      · exact ac93t56
      · exact ac93t58
      · exact ac93t108
      · exact ac93t110
      · exact ac93t117
      · exact ac93t119
      · exact ac93t120
      · exact ac93t135
      · exact ac93t137
      · exact ac93t138
      · exact ac93t180
      · exact ac93t189
      · exact ac93t198
      · exact ac93t200
      · exact ac93t201
      · exact ac93t216
      · exact ac93t218
      · exact ac93t219
      · exact ac93t220
      · exact ac93t261
      · exact ac93t270
      · exact ac93t272
      · exact ac93t279
      · exact ac93t281
      · exact ac93t282
      · exact ac93t297
      · exact ac93t299
      · exact ac93t301
    · intro t ht
      simp only [List.mem_cons,List.not_mem_nil,or_false] at ht
      rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact ac91t109
      · exact ac91t117
      · exact ac91t118
      · exact ac91t171
      · exact ac91t190
      · exact ac91t201
      · exact ac91t216
      · exact ac91t252
      · exact ac91t270
      · exact ac91t279
      · exact ac91t282
      · exact ac91t298
    · intro t ht
      simp only [List.mem_cons,List.not_mem_nil,or_false] at ht
      rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact ac87t9
      · exact ac87t58
      · exact ac87t90
      · exact ac87t100
      · exact ac87t117
      · exact ac87t118
      · exact ac87t119
      · exact ac87t135
      · exact ac87t136
      · exact ac87t137
      · exact ac87t171
      · exact ac87t180
      · exact ac87t198
      · exact ac87t199
      · exact ac87t200
      · exact ac87t216
      · exact ac87t217
      · exact ac87t218
      · exact ac87t220
      · exact ac87t252
      · exact ac87t261
      · exact ac87t262
      · exact ac87t279
      · exact ac87t297
      · exact ac87t298
      · exact ac87t301
    · intro t ht
      simp only [List.mem_cons,List.not_mem_nil,or_false] at ht
      rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact ac79t9
      · exact ac79t19
      · exact ac79t55
      · exact ac79t90
      · exact ac79t100
      · exact ac79t109
      · exact ac79t138
      · exact ac79t171
      · exact ac79t190
      · exact ac79t191
      · exact ac79t216
      · exact ac79t217
      · exact ac79t218
      · exact ac79t219
      · exact ac79t252
      · exact ac79t261
      · exact ac79t262
      · exact ac79t271
      · exact ac79t297
      · exact ac79t298
      · exact ac79t300
    · intro t ht
      simp only [List.mem_cons,List.not_mem_nil,or_false] at ht
      rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact ac31t19
      · exact ac31t108
      · exact ac31t109
      · exact ac31t118
      · exact ac31t180
      · exact ac31t190
      · exact ac31t198
      · exact ac31t262
      · exact ac31t282
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ax95pairs : properPairs (graphGoal 95) (asRow ax95P) (asRow ax95Q) := compactPairs (g:=ax95G) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ax95autos : ∀ p ∈ ax95Perms, autoOK (graphGoal 95) (p.map swapRows).reverse = true := compactAutos_valid (by decide +kernel)
def ax95check (k : Nat) := richNode ax95G ax95T ax95D ax95Perms k
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem zc95k4p0 : chartBlock (ax95check 4) 0 8 = true := by
  iterate 2 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem zlev95k4 : chartBlock (ax95check 4) 0 8 = true :=
  zc95k4p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem zc95k5p0 : chartBlock (ax95check 5) 0 23 = true := by
  iterate 3 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem zlev95k5 : chartBlock (ax95check 5) 0 23 = true :=
  zc95k5p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem zc95k6p0 : chartBlock (ax95check 6) 0 32 = true := by
  iterate 4 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem zc95k6p1 : chartBlock (ax95check 6) 32 32 = true := by
  iterate 4 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem zc95k6p2 : chartBlock (ax95check 6) 64 32 = true := by
  iterate 4 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem zc95k6p3 : chartBlock (ax95check 6) 96 32 = true := by
  iterate 4 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem zc95k6p4 : chartBlock (ax95check 6) 128 32 = true := by
  iterate 4 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem zc95k6p5 : chartBlock (ax95check 6) 160 4 = true := by
  iterate 1 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem zlev95k6 : chartBlock (ax95check 6) 0 164 = true :=
  (chartBlock_join (a := 96) (b := 68) (chartBlock_join (a := 32) (b := 64) zc95k6p0 (chartBlock_join (a := 32) (b := 32) zc95k6p1 zc95k6p2)) (chartBlock_join (a := 32) (b := 36) zc95k6p3 (chartBlock_join (a := 32) (b := 4) zc95k6p4 zc95k6p5)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem zc95k7p0 : chartBlock (ax95check 7) 0 32 = true := by
  iterate 4 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem zc95k7p1 : chartBlock (ax95check 7) 32 32 = true := by
  iterate 4 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem zc95k7p2 : chartBlock (ax95check 7) 64 32 = true := by
  iterate 4 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem zc95k7p3 : chartBlock (ax95check 7) 96 32 = true := by
  iterate 4 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem zc95k7p4 : chartBlock (ax95check 7) 128 32 = true := by
  iterate 4 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem zc95k7p5 : chartBlock (ax95check 7) 160 32 = true := by
  iterate 4 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem zc95k7p6 : chartBlock (ax95check 7) 192 25 = true := by
  iterate 4 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem zlev95k7 : chartBlock (ax95check 7) 0 217 = true :=
  (chartBlock_join (a := 96) (b := 121) (chartBlock_join (a := 32) (b := 64) zc95k7p0 (chartBlock_join (a := 32) (b := 32) zc95k7p1 zc95k7p2)) (chartBlock_join (a := 64) (b := 57) (chartBlock_join (a := 32) (b := 32) zc95k7p3 zc95k7p4) (chartBlock_join (a := 32) (b := 25) zc95k7p5 zc95k7p6)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem zc95k8p0 : chartBlock (ax95check 8) 0 32 = true := by
  iterate 4 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem zc95k8p1 : chartBlock (ax95check 8) 32 32 = true := by
  iterate 4 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem zc95k8p2 : chartBlock (ax95check 8) 64 9 = true := by
  iterate 2 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem zlev95k8 : chartBlock (ax95check 8) 0 73 = true :=
  (chartBlock_join (a := 32) (b := 41) zc95k8p0 (chartBlock_join (a := 32) (b := 9) zc95k8p1 zc95k8p2))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem zc95k9p0 : chartBlock (ax95check 9) 0 5 = true := by
  iterate 1 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem zlev95k9 : chartBlock (ax95check 9) 0 5 = true :=
  zc95k9p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ax95blocks : ∀ k ≤ ax95G.top, chartBlock (ax95check k) 0 (ax95T.count k) = true := by
  intro k hk
  change k ≤ 10 at hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · exact zlev95k4
  · exact zlev95k5
  · exact zlev95k6
  · exact zlev95k7
  · exact zlev95k8
  · exact zlev95k9
  · rfl
def ax95pools := richPoolList 95 ax95D [] (ax95PoolIDs 10 0)
def ax95links := linkedCandidates ax95G ax95T ax95Perms 9
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ax95base : Impossible true (graphGoal 95) 9 (vars 95).toFinset := @poolCut_sound true (vars 95) (graphGoal 95) (subcube (95-95) 0) 10 (@zeroSlice_sound 95 95 10 (by decide +kernel) bound95) [] (vars 95) (vars 95) 9 rfl (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ax95makes (t : Nat) (ok : primCheck ax95G ax95pools ax95links t = true) : Lower true (typeWord t :: vars 95) (graphGoal 95) 10 := by
  exact primOK (g:=ax95G) (pools:=ax95pools) (links:=ax95links) (t:=t) (hints:=4146) ax95pairs (richPool_valid (m:=95) (dom:=ax95D) (h:=[]) (picks:=ax95PoolIDs 10 0) ax95domains) (linkedCandidates_valid (g:=ax95G) (t:=ax95T) (perms:=ax95Perms) (k:=9) ax95autos (richAll (g:=ax95G) (t:=ax95T) (dom:=ax95D) (perms:=ax95Perms) ax95pairs ax95domains ax95autos ax95blocks 9 (by decide))) (by rfl) (by decide +kernel) (by decide +kernel) ax95base (by decide) ok
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem rep95t100 : Lower true (typeWord 100 :: vars 95) (graphGoal 95) 10 := ax95makes 100 (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem rep95t108 : Lower true (typeWord 108 :: vars 95) (graphGoal 95) 10 := ax95makes 108 (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem rep95t109 : Lower true (typeWord 109 :: vars 95) (graphGoal 95) 10 := ax95makes 109 (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem rep95t138 : Lower true (typeWord 138 :: vars 95) (graphGoal 95) 10 := ax95makes 138 (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem rep95t190 : Lower true (typeWord 190 :: vars 95) (graphGoal 95) 10 := ax95makes 190 (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem rep95t282 : Lower true (typeWord 282 :: vars 95) (graphGoal 95) 10 := ax95makes 282 (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem rep95t298 : Lower true (typeWord 298 :: vars 95) (graphGoal 95) 10 := ax95makes 298 (by decide +kernel)
theorem ac95t90 : Lower true (typeWord 90 :: vars 95) (graphGoal 95) 10 := @augCarry 95 95 90 100 [32] 10 (by decide +kernel) rep95t100
theorem ac95t100 : Lower true (typeWord 100 :: vars 95) (graphGoal 95) 10 := @augCarry 95 95 100 108 [32, 49, 100] 10 (by decide +kernel) rep95t108
theorem ac95t108 : Lower true (typeWord 108 :: vars 95) (graphGoal 95) 10 := @augCarry 95 95 108 100 [32, 49, 100] 10 (by decide +kernel) rep95t100
theorem ac95t109 : Lower true (typeWord 109 :: vars 95) (graphGoal 95) 10 := rep95t109
theorem ac95t110 : Lower true (typeWord 110 :: vars 95) (graphGoal 95) 10 := @augCarry 95 95 110 108 [32] 10 (by decide +kernel) rep95t108
theorem ac95t118 : Lower true (typeWord 118 :: vars 95) (graphGoal 95) 10 := @augCarry 95 95 118 138 [49, 100] 10 (by decide +kernel) rep95t138
theorem ac95t138 : Lower true (typeWord 138 :: vars 95) (graphGoal 95) 10 := rep95t138
theorem ac95t190 : Lower true (typeWord 190 :: vars 95) (graphGoal 95) 10 := rep95t190
theorem ac95t271 : Lower true (typeWord 271 :: vars 95) (graphGoal 95) 10 := @augCarry 95 95 271 190 [49, 100] 10 (by decide +kernel) rep95t190
theorem ac95t298 : Lower true (typeWord 298 :: vars 95) (graphGoal 95) 10 := rep95t298
theorem ac126t110 : Lower true (typeWord 110 :: vars 126) (graphGoal 126) 10 := @augCarry 126 95 110 100 [97, 98, 99, 100, 80] 10 (by decide +kernel) rep95t100
theorem ac126t118 : Lower true (typeWord 118 :: vars 126) (graphGoal 126) 10 := @augCarry 126 95 118 138 [97, 98, 99, 100, 80] 10 (by decide +kernel) rep95t138
theorem ac126t119 : Lower true (typeWord 119 :: vars 126) (graphGoal 126) 10 := @augCarry 126 95 119 109 [65, 50, 80] 10 (by decide +kernel) rep95t109
theorem ac126t120 : Lower true (typeWord 120 :: vars 126) (graphGoal 126) 10 := @augCarry 126 95 120 108 [97, 98, 48, 64, 101, 96] 10 (by decide +kernel) rep95t108
theorem ac126t128 : Lower true (typeWord 128 :: vars 126) (graphGoal 126) 10 := @augCarry 126 95 128 100 [97, 98, 48, 64, 101, 96] 10 (by decide +kernel) rep95t100
theorem ac126t130 : Lower true (typeWord 130 :: vars 126) (graphGoal 126) 10 := @augCarry 126 95 130 108 [97, 98, 99, 100, 80] 10 (by decide +kernel) rep95t108
theorem ac126t137 : Lower true (typeWord 137 :: vars 126) (graphGoal 126) 10 := @augCarry 126 95 137 138 [65, 50, 80] 10 (by decide +kernel) rep95t138
theorem ac126t181 : Lower true (typeWord 181 :: vars 126) (graphGoal 126) 10 := @augCarry 126 95 181 282 [65, 50, 80] 10 (by decide +kernel) rep95t282
theorem ac126t200 : Lower true (typeWord 200 :: vars 126) (graphGoal 126) 10 := @augCarry 126 95 200 190 [97, 98, 99, 100, 80] 10 (by decide +kernel) rep95t190
theorem ac126t281 : Lower true (typeWord 281 :: vars 126) (graphGoal 126) 10 := @augCarry 126 95 281 190 [65, 50, 80] 10 (by decide +kernel) rep95t190
theorem ac126t301 : Lower true (typeWord 301 :: vars 126) (graphGoal 126) 10 := @augCarry 126 95 301 298 [65, 50, 80] 10 (by decide +kernel) rep95t298
def ax111G : CompactGrid := (111,10,ax111P,ax111Q)
def ax111T : CompactTable := ((fun k => if k=10 then 0 else ax111Count k),ax111Path,ax111Live,ax111PoolIDs,ax111Bucket)
def ax111S : List (Nat × SliceSpec) := [(0, 1, 0, 110, 0, 0, 7, 7), (48, 1, 0, 110, 0, 0, 7, 7), (101, 1, 0, 110, 0, 0, 7, 7), (129, 1, 0, 110, 0, 0, 7, 7), (141, 1, 0, 110, 0, 0, 7, 7), (210, 1, 0, 110, 0, 0, 7, 7), (0, 2, 0, 109, 0, 0, 7, 7), (30, 2, 0, 109, 0, 0, 7, 7), (48, 2, 0, 109, 0, 0, 7, 7), (111, 2, 0, 109, 0, 0, 7, 7), (127, 2, 0, 109, 0, 0, 7, 7), (130, 2, 0, 109, 0, 0, 7, 7), (192, 2, 0, 109, 0, 0, 7, 7), (210, 2, 0, 109, 0, 0, 7, 7), (222, 2, 0, 109, 0, 0, 7, 7), (273, 2, 0, 109, 0, 0, 7, 7), (291, 2, 0, 109, 0, 0, 7, 7), (292, 2, 0, 109, 0, 0, 7, 7), (300, 2, 0, 109, 0, 0, 7, 7), (0, 4, 0, 107, 0, 0, 7, 7), (10, 4, 0, 107, 0, 0, 7, 7), (49, 4, 0, 107, 0, 0, 7, 7), (91, 4, 0, 107, 0, 0, 7, 7), (127, 4, 0, 107, 0, 0, 7, 7), (128, 4, 0, 107, 0, 0, 7, 7), (136, 4, 0, 107, 0, 0, 7, 7), (172, 4, 0, 107, 0, 0, 7, 7), (209, 4, 0, 107, 0, 0, 7, 7), (217, 4, 0, 107, 0, 0, 7, 7), (299, 4, 0, 107, 0, 0, 7, 7), (0, 8, 0, 103, 0, 0, 7, 7), (101, 8, 0, 103, 0, 0, 7, 7), (127, 8, 0, 103, 0, 0, 7, 7), (137, 8, 0, 103, 0, 0, 7, 7), (141, 8, 0, 103, 0, 0, 7, 7), (210, 8, 0, 103, 0, 0, 7, 7), (218, 8, 0, 103, 0, 0, 7, 7), (0, 32, 0, 79, 0, 0, 7, 7), (20, 32, 0, 79, 0, 0, 7, 7), (56, 32, 0, 79, 0, 0, 7, 7), (91, 32, 0, 79, 0, 0, 7, 7), (101, 32, 0, 79, 0, 0, 7, 7), (110, 32, 0, 79, 0, 0, 7, 7), (139, 32, 0, 79, 0, 0, 7, 7), (172, 32, 0, 79, 0, 0, 7, 7), (182, 32, 0, 79, 0, 0, 7, 7), (190, 32, 0, 79, 0, 0, 7, 7), (191, 32, 0, 79, 0, 0, 7, 7), (220, 32, 0, 79, 0, 0, 7, 7), (253, 32, 0, 79, 0, 0, 7, 7), (271, 32, 0, 79, 0, 0, 7, 7), (272, 32, 0, 79, 0, 0, 7, 7), (273, 32, 0, 79, 0, 0, 7, 7), (299, 32, 0, 79, 0, 0, 7, 7), (300, 32, 0, 79, 0, 0, 7, 7), (301, 32, 0, 79, 0, 0, 7, 7), (0, 64, 0, 47, 0, 0, 7, 7), (48, 64, 0, 47, 0, 0, 7, 7), (127, 64, 0, 47, 0, 0, 7, 7), (208, 64, 0, 47, 0, 0, 7, 7), (210, 64, 0, 47, 0, 0, 7, 7), (291, 64, 0, 47, 0, 0, 7, 7), (0, 0, 2, 69, 40, 15790080, 6, 4), (0, 0, 4, 42, 65, 251658255, 6, 4), (0, 6, 0, 105, 0, 0, 5, 5), (0, 1, 4, 42, 64, 251658240, 5, 4), (0, 8, 2, 69, 32, 15728640, 5, 4), (0, 32, 2, 69, 8, 61440, 5, 4), (0, 64, 4, 42, 1, 15, 5, 4), (0, 9, 0, 102, 0, 0, 4, 4), (0, 7, 0, 104, 0, 0, 4, 4), (0, 14, 0, 97, 0, 0, 4, 4), (0, 40, 2, 69, 0, 0, 4, 4), (0, 65, 4, 42, 0, 0, 4, 4)]
def ax111D : RichDomains := (ax111S.map richSpecDomain).toArray
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ax111domains : RichValid 111 ax111D := by
  apply flexibleOK (m:=111) (ds:=ax111D) (prior:=[(42, 4), (47, 7), (69, 4), (79, 7), (97, 4), (102, 4), (103, 7), (104, 4), (105, 5), (107, 7), (109, 7), (110, 7)]) (extras:=[(110, 7, [47, 100, 128, 140, 209]), (109, 7, [29, 47, 110, 126, 129, 191, 209, 221, 272, 290, 291, 299]), (107, 7, [9, 48, 90, 126, 127, 135, 171, 208, 216, 298]), (103, 7, [100, 126, 136, 140, 209, 217]), (79, 7, [19, 55, 90, 100, 109, 138, 171, 181, 189, 190, 219, 252, 270, 271, 272, 298, 299, 300]), (47, 7, [47, 126, 207, 209, 290])]) (specs:=ax111S)
  · intro e he
    simp only [List.mem_cons,List.not_mem_nil,or_false] at he
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact bound42
    · exact bound47
    · exact bound69
    · exact bound79
    · exact bound97
    · exact bound102
    · exact bound103
    · exact bound104
    · exact bound105
    · exact bound107
    · exact bound109
    · exact bound110
  · intro e he
    simp only [List.mem_cons,List.not_mem_nil,or_false] at he
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl
    · intro t ht
      simp only [List.mem_cons,List.not_mem_nil,or_false] at ht
      rcases ht with rfl | rfl | rfl | rfl | rfl
      · exact ac110t47
      · exact ac110t100
      · exact ac110t128
      · exact ac110t140
      · exact ac110t209
    · intro t ht
      simp only [List.mem_cons,List.not_mem_nil,or_false] at ht
      rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact ac109t29
      · exact ac109t47
      · exact ac109t110
      · exact ac109t126
      · exact ac109t129
      · exact ac109t191
      · exact ac109t209
      · exact ac109t221
      · exact ac109t272
      · exact ac109t290
      · exact ac109t291
      · exact ac109t299
    · intro t ht
      simp only [List.mem_cons,List.not_mem_nil,or_false] at ht
      rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact ac107t9
      · exact ac107t48
      · exact ac107t90
      · exact ac107t126
      · exact ac107t127
      · exact ac107t135
      · exact ac107t171
      · exact ac107t208
      · exact ac107t216
      · exact ac107t298
    · intro t ht
      simp only [List.mem_cons,List.not_mem_nil,or_false] at ht
      rcases ht with rfl | rfl | rfl | rfl | rfl | rfl
      · exact ac103t100
      · exact ac103t126
      · exact ac103t136
      · exact ac103t140
      · exact ac103t209
      · exact ac103t217
    · intro t ht
      simp only [List.mem_cons,List.not_mem_nil,or_false] at ht
      rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact ac79t19
      · exact ac79t55
      · exact ac79t90
      · exact ac79t100
      · exact ac79t109
      · exact ac79t138
      · exact ac79t171
      · exact ac79t181
      · exact ac79t189
      · exact ac79t190
      · exact ac79t219
      · exact ac79t252
      · exact ac79t270
      · exact ac79t271
      · exact ac79t272
      · exact ac79t298
      · exact ac79t299
      · exact ac79t300
    · intro t ht
      simp only [List.mem_cons,List.not_mem_nil,or_false] at ht
      rcases ht with rfl | rfl | rfl | rfl | rfl
      · exact ac47t47
      · exact ac47t126
      · exact ac47t207
      · exact ac47t209
      · exact ac47t290
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ax111pairs : properPairs (graphGoal 111) (asRow ax111P) (asRow ax111Q) := compactPairs (g:=ax111G) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ax111autos : ∀ p ∈ ax111Perms, autoOK (graphGoal 111) (p.map swapRows).reverse = true := compactAutos_valid (by decide +kernel)
def ax111check (k : Nat) := richNode ax111G ax111T ax111D ax111Perms k
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem zc111k6p0 : chartBlock (ax111check 6) 0 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem zlev111k6 : chartBlock (ax111check 6) 0 2 = true :=
  zc111k6p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem zc111k7p0 : chartBlock (ax111check 7) 0 15 = true := by
  iterate 3 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem zlev111k7 : chartBlock (ax111check 7) 0 15 = true :=
  zc111k7p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem zc111k8p0 : chartBlock (ax111check 8) 0 21 = true := by
  iterate 3 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem zlev111k8 : chartBlock (ax111check 8) 0 21 = true :=
  zc111k8p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem zc111k9p0 : chartBlock (ax111check 9) 0 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem zlev111k9 : chartBlock (ax111check 9) 0 2 = true :=
  zc111k9p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ax111blocks : ∀ k ≤ ax111G.top, chartBlock (ax111check k) 0 (ax111T.count k) = true := by
  intro k hk
  change k ≤ 10 at hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact zlev111k6
  · exact zlev111k7
  · exact zlev111k8
  · exact zlev111k9
  · rfl
def ax111pools := richPoolList 111 ax111D [] (ax111PoolIDs 10 0)
def ax111links := linkedCandidates ax111G ax111T ax111Perms 9
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ax111base : Impossible true (graphGoal 111) 9 (vars 111).toFinset := @poolCut_sound true (vars 111) (graphGoal 111) (subcube (111-111) 0) 10 (@zeroSlice_sound 111 111 10 (by decide +kernel) bound111) [] (vars 111) (vars 111) 9 rfl (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ax111makes (t : Nat) (ok : primCheck ax111G ax111pools ax111links t = true) : Lower true (typeWord t :: vars 111) (graphGoal 111) 10 := by
  exact primOK (g:=ax111G) (pools:=ax111pools) (links:=ax111links) (t:=t) (hints:=4146) ax111pairs (richPool_valid (m:=111) (dom:=ax111D) (h:=[]) (picks:=ax111PoolIDs 10 0) ax111domains) (linkedCandidates_valid (g:=ax111G) (t:=ax111T) (perms:=ax111Perms) (k:=9) ax111autos (richAll (g:=ax111G) (t:=ax111T) (dom:=ax111D) (perms:=ax111Perms) ax111pairs ax111domains ax111autos ax111blocks 9 (by decide))) (by rfl) (by decide +kernel) (by decide +kernel) ax111base (by decide) ok
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem rep111t100 : Lower true (typeWord 100 :: vars 111) (graphGoal 111) 10 := ax111makes 100 (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem rep111t209 : Lower true (typeWord 209 :: vars 111) (graphGoal 111) 10 := ax111makes 209 (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem rep111t217 : Lower true (typeWord 217 :: vars 111) (graphGoal 111) 10 := ax111makes 217 (by decide +kernel)
theorem ac111t100 : Lower true (typeWord 100 :: vars 111) (graphGoal 111) 10 := rep111t100
theorem ac111t217 : Lower true (typeWord 217 :: vars 111) (graphGoal 111) 10 := rep111t217
theorem ac125t120 : Lower true (typeWord 120 :: vars 125) (graphGoal 125) 10 := @augCarry 125 111 120 100 [80, 50, 65] 10 (by decide +kernel) rep111t100
theorem ac125t220 : Lower true (typeWord 220 :: vars 125) (graphGoal 125) 10 := @augCarry 125 111 220 217 [80, 50, 65] 10 (by decide +kernel) rep111t217
theorem ac125t270 : Lower true (typeWord 270 :: vars 125) (graphGoal 125) 10 := @augCarry 125 111 270 209 [80, 50, 65] 10 (by decide +kernel) rep111t209
def ax127G : CompactGrid := (127,12,ax127P,ax127Q)
def ax127T : CompactTable := (ax127Count,ax127Path,ax127Live,ax127PoolIDs,ax127Bucket)
def ax127S : List (Nat × SliceSpec) := [(0, 1, 0, 126, 0, 0, 10, 10), (111, 1, 0, 126, 0, 0, 10, 10), (119, 1, 0, 126, 0, 0, 10, 10), (120, 1, 0, 126, 0, 0, 10, 10), (121, 1, 0, 126, 0, 0, 10, 10), (129, 1, 0, 126, 0, 0, 10, 10), (131, 1, 0, 126, 0, 0, 10, 10), (138, 1, 0, 126, 0, 0, 10, 10), (182, 1, 0, 126, 0, 0, 10, 10), (201, 1, 0, 126, 0, 0, 10, 10), (282, 1, 0, 126, 0, 0, 10, 10), (302, 1, 0, 126, 0, 0, 10, 10), (0, 2, 0, 125, 0, 0, 10, 10), (121, 2, 0, 125, 0, 0, 10, 10), (221, 2, 0, 125, 0, 0, 10, 10), (271, 2, 0, 125, 0, 0, 10, 10), (0, 4, 0, 123, 0, 0, 10, 10), (0, 8, 0, 119, 0, 0, 10, 10), (0, 16, 0, 111, 0, 0, 10, 10), (101, 16, 0, 111, 0, 0, 10, 10), (218, 16, 0, 111, 0, 0, 10, 10), (0, 32, 0, 95, 0, 0, 10, 10), (91, 32, 0, 95, 0, 0, 10, 10), (101, 32, 0, 95, 0, 0, 10, 10), (109, 32, 0, 95, 0, 0, 10, 10), (110, 32, 0, 95, 0, 0, 10, 10), (111, 32, 0, 95, 0, 0, 10, 10), (119, 32, 0, 95, 0, 0, 10, 10), (139, 32, 0, 95, 0, 0, 10, 10), (191, 32, 0, 95, 0, 0, 10, 10), (272, 32, 0, 95, 0, 0, 10, 10), (299, 32, 0, 95, 0, 0, 10, 10), (0, 64, 0, 63, 0, 0, 9, 9), (100, 64, 0, 63, 0, 0, 9, 9), (101, 64, 0, 63, 0, 0, 9, 9), (109, 64, 0, 63, 0, 0, 9, 9), (110, 64, 0, 63, 0, 0, 9, 9), (111, 64, 0, 63, 0, 0, 9, 9), (119, 64, 0, 63, 0, 0, 9, 9), (120, 64, 0, 63, 0, 0, 9, 9), (121, 64, 0, 63, 0, 0, 9, 9), (127, 64, 0, 63, 0, 0, 9, 9), (181, 64, 0, 63, 0, 0, 9, 9), (182, 64, 0, 63, 0, 0, 9, 9), (190, 64, 0, 63, 0, 0, 9, 9), (191, 64, 0, 63, 0, 0, 9, 9), (192, 64, 0, 63, 0, 0, 9, 9), (273, 64, 0, 63, 0, 0, 9, 9), (282, 64, 0, 63, 0, 0, 9, 9), (283, 64, 0, 63, 0, 0, 9, 9), (291, 64, 0, 63, 0, 0, 9, 9), (292, 64, 0, 63, 0, 0, 9, 9), (0, 0, 2, 69, 56, 16773120, 7, 4), (0, 0, 4, 42, 81, 252641295, 7, 4), (0, 0, 8, 21, 98, 267387120, 7, 4), (0, 0, 16, 104, 7, 4095, 7, 4), (0, 3, 0, 124, 0, 0, 7, 7), (0, 5, 0, 122, 0, 0, 7, 7), (0, 6, 0, 121, 0, 0, 7, 7), (0, 9, 0, 118, 0, 0, 7, 7), (0, 10, 0, 117, 0, 0, 7, 7), (0, 17, 0, 110, 0, 0, 7, 7), (0, 18, 0, 109, 0, 0, 7, 7), (0, 20, 0, 107, 0, 0, 7, 7), (0, 24, 0, 103, 0, 0, 7, 7), (0, 33, 0, 94, 0, 0, 7, 7), (0, 34, 0, 93, 0, 0, 7, 7), (0, 36, 0, 91, 0, 0, 7, 7), (0, 40, 0, 87, 0, 0, 7, 7), (0, 48, 0, 79, 0, 0, 7, 7), (0, 65, 0, 62, 0, 0, 7, 7), (0, 66, 0, 61, 0, 0, 7, 7), (0, 80, 0, 47, 0, 0, 7, 7), (0, 96, 0, 31, 0, 0, 7, 7), (0, 12, 0, 115, 0, 0, 6, 6), (0, 68, 0, 59, 0, 0, 6, 6), (0, 72, 0, 55, 0, 0, 6, 6), (0, 1, 4, 42, 80, 252641280, 6, 4), (0, 1, 16, 104, 6, 4080, 6, 4), (0, 2, 8, 21, 96, 267386880, 6, 4), (0, 2, 16, 104, 5, 3855, 6, 4), (0, 4, 16, 104, 3, 255, 6, 4), (0, 8, 2, 69, 48, 16711680, 6, 4), (0, 16, 2, 69, 40, 15790080, 6, 4), (0, 16, 4, 42, 65, 251658255, 6, 4), (0, 32, 2, 69, 24, 1044480, 6, 4), (0, 32, 8, 21, 66, 251658480, 6, 4), (0, 64, 4, 42, 17, 983055, 6, 4), (0, 64, 8, 21, 34, 15728880, 6, 4), (0, 14, 0, 113, 0, 0, 5, 5), (0, 19, 0, 108, 0, 0, 5, 5), (0, 21, 0, 106, 0, 0, 5, 5), (0, 26, 0, 101, 0, 0, 5, 5), (0, 69, 0, 58, 0, 0, 5, 5), (0, 74, 0, 53, 0, 0, 5, 5), (0, 84, 0, 43, 0, 0, 5, 5), (0, 104, 0, 23, 0, 0, 5, 5), (0, 3, 16, 104, 4, 3840, 5, 4), (0, 5, 16, 104, 2, 240, 5, 4), (0, 6, 16, 104, 1, 15, 5, 4), (0, 17, 4, 42, 64, 251658240, 5, 4), (0, 24, 2, 69, 32, 15728640, 5, 4), (0, 34, 8, 21, 64, 251658240, 5, 4), (0, 40, 2, 69, 16, 983040, 5, 4), (0, 48, 2, 69, 8, 61440, 5, 4), (0, 65, 4, 42, 16, 983040, 5, 4), (0, 66, 8, 21, 32, 15728640, 5, 4), (0, 80, 4, 42, 1, 15, 5, 4), (0, 96, 8, 21, 2, 240, 5, 4), (0, 11, 0, 116, 0, 0, 4, 4), (0, 13, 0, 114, 0, 0, 4, 4), (0, 25, 0, 102, 0, 0, 4, 4), (0, 35, 0, 92, 0, 0, 4, 4), (0, 37, 0, 90, 0, 0, 4, 4), (0, 38, 0, 89, 0, 0, 4, 4), (0, 41, 0, 86, 0, 0, 4, 4), (0, 44, 0, 83, 0, 0, 4, 4), (0, 49, 0, 78, 0, 0, 4, 4), (0, 73, 0, 54, 0, 0, 4, 4), (0, 82, 0, 45, 0, 0, 4, 4), (0, 88, 0, 39, 0, 0, 4, 4), (0, 97, 0, 30, 0, 0, 4, 4), (0, 7, 16, 104, 0, 0, 4, 4), (0, 30, 0, 97, 0, 0, 4, 4), (0, 56, 2, 69, 0, 0, 4, 4), (0, 81, 4, 42, 0, 0, 4, 4), (0, 85, 0, 42, 0, 0, 4, 4), (0, 98, 8, 21, 0, 0, 4, 4), (0, 106, 0, 21, 0, 0, 4, 4)]
def ax127D : RichDomains := (ax127S.map richSpecDomain).toArray
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ax127domains : RichValid 127 ax127D := by
  apply flexibleOK (m:=127) (ds:=ax127D) (prior:=[(21, 4), (23, 5), (30, 4), (31, 7), (39, 4), (42, 4), (43, 5), (45, 4), (47, 7), (53, 5), (54, 4), (55, 6), (58, 5), (59, 6), (61, 7), (62, 7), (63, 9), (69, 4), (78, 4), (79, 7), (83, 4), (86, 4), (87, 7), (89, 4), (90, 4), (91, 7), (92, 4), (93, 7), (94, 7), (95, 10), (97, 4), (101, 5), (102, 4), (103, 7), (104, 4), (106, 5), (107, 7), (108, 5), (109, 7), (110, 7), (111, 10), (113, 5), (114, 4), (115, 6), (116, 4), (117, 7), (118, 7), (119, 10), (121, 7), (122, 7), (123, 10), (124, 7), (125, 10), (126, 10)]) (extras:=[(126, 10, [110, 118, 119, 120, 128, 130, 137, 181, 200, 281, 301]), (125, 10, [120, 220, 270]), (111, 10, [100, 217]), (95, 10, [90, 100, 108, 109, 110, 118, 138, 190, 271, 298]), (63, 9, [99, 100, 108, 109, 110, 118, 119, 120, 126, 180, 181, 189, 190, 191, 272, 281, 282, 290, 291])]) (specs:=ax127S)
  · intro e he
    simp only [List.mem_cons,List.not_mem_nil,or_false] at he
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact bound21
    · exact bound23
    · exact bound30
    · exact bound31
    · exact bound39
    · exact bound42
    · exact bound43
    · exact bound45
    · exact bound47
    · exact bound53
    · exact bound54
    · exact bound55
    · exact bound58
    · exact bound59
    · exact bound61
    · exact bound62
    · exact bound63
    · exact bound69
    · exact bound78
    · exact bound79
    · exact bound83
    · exact bound86
    · exact bound87
    · exact bound89
    · exact bound90
    · exact bound91
    · exact bound92
    · exact bound93
    · exact bound94
    · exact bound95
    · exact bound97
    · exact bound101
    · exact bound102
    · exact bound103
    · exact bound104
    · exact bound106
    · exact bound107
    · exact bound108
    · exact bound109
    · exact bound110
    · exact bound111
    · exact bound113
    · exact bound114
    · exact bound115
    · exact bound116
    · exact bound117
    · exact bound118
    · exact bound119
    · exact bound121
    · exact bound122
    · exact bound123
    · exact bound124
    · exact bound125
    · exact bound126
  · intro e he
    simp only [List.mem_cons,List.not_mem_nil,or_false] at he
    rcases he with rfl | rfl | rfl | rfl | rfl
    · intro t ht
      simp only [List.mem_cons,List.not_mem_nil,or_false] at ht
      rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact ac126t110
      · exact ac126t118
      · exact ac126t119
      · exact ac126t120
      · exact ac126t128
      · exact ac126t130
      · exact ac126t137
      · exact ac126t181
      · exact ac126t200
      · exact ac126t281
      · exact ac126t301
    · intro t ht
      simp only [List.mem_cons,List.not_mem_nil,or_false] at ht
      rcases ht with rfl | rfl | rfl
      · exact ac125t120
      · exact ac125t220
      · exact ac125t270
    · intro t ht
      simp only [List.mem_cons,List.not_mem_nil,or_false] at ht
      rcases ht with rfl | rfl
      · exact ac111t100
      · exact ac111t217
    · intro t ht
      simp only [List.mem_cons,List.not_mem_nil,or_false] at ht
      rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact ac95t90
      · exact ac95t100
      · exact ac95t108
      · exact ac95t109
      · exact ac95t110
      · exact ac95t118
      · exact ac95t138
      · exact ac95t190
      · exact ac95t271
      · exact ac95t298
    · intro t ht
      simp only [List.mem_cons,List.not_mem_nil,or_false] at ht
      rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact ac63t99
      · exact ac63t100
      · exact ac63t108
      · exact ac63t109
      · exact ac63t110
      · exact ac63t118
      · exact ac63t119
      · exact ac63t120
      · exact ac63t126
      · exact ac63t180
      · exact ac63t181
      · exact ac63t189
      · exact ac63t190
      · exact ac63t191
      · exact ac63t272
      · exact ac63t281
      · exact ac63t282
      · exact ac63t290
      · exact ac63t291
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ax127pairs : properPairs (graphGoal 127) (asRow ax127P) (asRow ax127Q) := compactPairs (g:=ax127G) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ax127autos : ∀ p ∈ ax127Perms, autoOK (graphGoal 127) (p.map swapRows).reverse = true := compactAutos_valid (by decide +kernel)
def ax127check (k : Nat) := richNode ax127G ax127T ax127D ax127Perms k
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem zc127k6p0 : chartBlock (ax127check 6) 0 8 = true := by
  iterate 2 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem zlev127k6 : chartBlock (ax127check 6) 0 8 = true :=
  zc127k6p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem zc127k7p0 : chartBlock (ax127check 7) 0 32 = true := by
  iterate 4 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem zc127k7p1 : chartBlock (ax127check 7) 32 32 = true := by
  iterate 4 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem zc127k7p2 : chartBlock (ax127check 7) 64 29 = true := by
  iterate 4 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem zlev127k7 : chartBlock (ax127check 7) 0 93 = true :=
  (chartBlock_join (a := 32) (b := 61) zc127k7p0 (chartBlock_join (a := 32) (b := 29) zc127k7p1 zc127k7p2))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem zc127k8p0 : chartBlock (ax127check 8) 0 32 = true := by
  iterate 4 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem zc127k8p1 : chartBlock (ax127check 8) 32 32 = true := by
  iterate 4 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem zc127k8p2 : chartBlock (ax127check 8) 64 32 = true := by
  iterate 4 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem zc127k8p3 : chartBlock (ax127check 8) 96 32 = true := by
  iterate 4 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem zc127k8p4 : chartBlock (ax127check 8) 128 32 = true := by
  iterate 4 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem zc127k8p5 : chartBlock (ax127check 8) 160 32 = true := by
  iterate 4 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem zc127k8p6 : chartBlock (ax127check 8) 192 32 = true := by
  iterate 4 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem zc127k8p7 : chartBlock (ax127check 8) 224 32 = true := by
  iterate 4 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem zc127k8p8 : chartBlock (ax127check 8) 256 32 = true := by
  iterate 4 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem zc127k8p9 : chartBlock (ax127check 8) 288 32 = true := by
  iterate 4 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem zc127k8p10 : chartBlock (ax127check 8) 320 17 = true := by
  iterate 3 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem zlev127k8 : chartBlock (ax127check 8) 0 337 = true :=
  (chartBlock_join (a := 160) (b := 177) (chartBlock_join (a := 64) (b := 96) (chartBlock_join (a := 32) (b := 32) zc127k8p0 zc127k8p1) (chartBlock_join (a := 32) (b := 64) zc127k8p2 (chartBlock_join (a := 32) (b := 32) zc127k8p3 zc127k8p4))) (chartBlock_join (a := 96) (b := 81) (chartBlock_join (a := 32) (b := 64) zc127k8p5 (chartBlock_join (a := 32) (b := 32) zc127k8p6 zc127k8p7)) (chartBlock_join (a := 32) (b := 49) zc127k8p8 (chartBlock_join (a := 32) (b := 17) zc127k8p9 zc127k8p10))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem zc127k9p0 : chartBlock (ax127check 9) 0 32 = true := by
  iterate 4 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem zc127k9p1 : chartBlock (ax127check 9) 32 32 = true := by
  iterate 4 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem zc127k9p2 : chartBlock (ax127check 9) 64 32 = true := by
  iterate 4 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem zc127k9p3 : chartBlock (ax127check 9) 96 32 = true := by
  iterate 4 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem zc127k9p4 : chartBlock (ax127check 9) 128 32 = true := by
  iterate 4 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem zc127k9p5 : chartBlock (ax127check 9) 160 32 = true := by
  iterate 4 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem zc127k9p6 : chartBlock (ax127check 9) 192 32 = true := by
  iterate 4 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem zc127k9p7 : chartBlock (ax127check 9) 224 32 = true := by
  iterate 4 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem zc127k9p8 : chartBlock (ax127check 9) 256 32 = true := by
  iterate 4 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem zc127k9p9 : chartBlock (ax127check 9) 288 32 = true := by
  iterate 4 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem zc127k9p10 : chartBlock (ax127check 9) 320 32 = true := by
  iterate 4 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem zc127k9p11 : chartBlock (ax127check 9) 352 32 = true := by
  iterate 4 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem zc127k9p12 : chartBlock (ax127check 9) 384 32 = true := by
  iterate 4 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem zc127k9p13 : chartBlock (ax127check 9) 416 32 = true := by
  iterate 4 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem zc127k9p14 : chartBlock (ax127check 9) 448 32 = true := by
  iterate 4 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem zc127k9p15 : chartBlock (ax127check 9) 480 32 = true := by
  iterate 4 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem zc127k9p16 : chartBlock (ax127check 9) 512 32 = true := by
  iterate 4 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem zc127k9p17 : chartBlock (ax127check 9) 544 32 = true := by
  iterate 4 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem zc127k9p18 : chartBlock (ax127check 9) 576 32 = true := by
  iterate 4 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem zc127k9p19 : chartBlock (ax127check 9) 608 23 = true := by
  iterate 3 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem zlev127k9 : chartBlock (ax127check 9) 0 631 = true :=
  (chartBlock_join (a := 320) (b := 311) (chartBlock_join (a := 160) (b := 160) (chartBlock_join (a := 64) (b := 96) (chartBlock_join (a := 32) (b := 32) zc127k9p0 zc127k9p1) (chartBlock_join (a := 32) (b := 64) zc127k9p2 (chartBlock_join (a := 32) (b := 32) zc127k9p3 zc127k9p4))) (chartBlock_join (a := 64) (b := 96) (chartBlock_join (a := 32) (b := 32) zc127k9p5 zc127k9p6) (chartBlock_join (a := 32) (b := 64) zc127k9p7 (chartBlock_join (a := 32) (b := 32) zc127k9p8 zc127k9p9)))) (chartBlock_join (a := 160) (b := 151) (chartBlock_join (a := 64) (b := 96) (chartBlock_join (a := 32) (b := 32) zc127k9p10 zc127k9p11) (chartBlock_join (a := 32) (b := 64) zc127k9p12 (chartBlock_join (a := 32) (b := 32) zc127k9p13 zc127k9p14))) (chartBlock_join (a := 64) (b := 87) (chartBlock_join (a := 32) (b := 32) zc127k9p15 zc127k9p16) (chartBlock_join (a := 32) (b := 55) zc127k9p17 (chartBlock_join (a := 32) (b := 23) zc127k9p18 zc127k9p19)))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem zc127k10p0 : chartBlock (ax127check 10) 0 32 = true := by
  iterate 4 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem zc127k10p1 : chartBlock (ax127check 10) 32 32 = true := by
  iterate 4 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem zc127k10p2 : chartBlock (ax127check 10) 64 32 = true := by
  iterate 4 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem zc127k10p3 : chartBlock (ax127check 10) 96 32 = true := by
  iterate 4 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem zc127k10p4 : chartBlock (ax127check 10) 128 32 = true := by
  iterate 4 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem zc127k10p5 : chartBlock (ax127check 10) 160 11 = true := by
  iterate 2 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem zlev127k10 : chartBlock (ax127check 10) 0 171 = true :=
  (chartBlock_join (a := 96) (b := 75) (chartBlock_join (a := 32) (b := 64) zc127k10p0 (chartBlock_join (a := 32) (b := 32) zc127k10p1 zc127k10p2)) (chartBlock_join (a := 32) (b := 43) zc127k10p3 (chartBlock_join (a := 32) (b := 11) zc127k10p4 zc127k10p5)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem zc127k11p0 : chartBlock (ax127check 11) 0 15 = true := by
  iterate 3 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem zlev127k11 : chartBlock (ax127check 11) 0 15 = true :=
  zc127k11p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem zc127k12p0 : chartBlock (ax127check 12) 0 1 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem zlev127k12 : chartBlock (ax127check 12) 0 1 = true :=
  zc127k12p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem ax127blocks : ∀ k ≤ ax127G.top, chartBlock (ax127check k) 0 (ax127T.count k) = true := by
  intro k hk
  change k ≤ 12 at hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact zlev127k6
  · exact zlev127k7
  · exact zlev127k8
  · exact zlev127k9
  · exact zlev127k10
  · exact zlev127k11
  · exact zlev127k12
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem excluded127 : Impossible true (graphGoal 127) 12 (vars 127).toFinset := richRoot (g:=ax127G) (t:=ax127T) (dom:=ax127D) (perms:=ax127Perms) ax127pairs ax127domains ax127autos ax127blocks (by decide +kernel) (by rfl)

end PEqualNP.Outside.L_meta_10760

open PEqualNP.Outside.L_meta_10760 in
theorem PEqualNP.Outside.L_meta_10760 : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 7 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 2, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 2, 6, 3, 6, 5, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 2, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 2, 6, 3, 6, 5, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 2, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 2, 6, 3, 6, 5, 6] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 7 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 2, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 2, 6, 3, 6, 5, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 2, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 2, 6, 3, 6, 5, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 2, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 2, 6, 3, 6, 5, 6] : List ℕ).getD (2 * i + 1) 0) false = true) := by
  intro gates o fit _oneNot correct
  exact replaceShort (by simpa only [sevenInputs, show graph = graphGoal 127 by decide +kernel] using excluded127) gates o fit correct
