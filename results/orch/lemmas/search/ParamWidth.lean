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


abbrev Bits (W : Nat) := BitVec W
abbrev Signals (W : Nat) := (Bits W) × (Bits W)
abbrev Decor (W : Nat) := Sig × (Signals W)

def ofRows {n : Nat} (r : Fin n → Row) (v : Sig) : BitVec n :=
  (BitVec.ofBoolListLE (List.ofFn (fun i => bit (r i) v))).cast List.length_ofFn
theorem ofRows_bit {n : Nat} (r : Fin n → Row) (v : Sig) (i : Fin n) :
    (ofRows r v).getLsbD i.val = bit (r i) v := by
  simp only [ofRows,BitVec.getLsbD_cast,BitVec.getLsbD_ofBoolListLE,List.getD_eq_getElem?_getD,List.getElem?_ofFn]
  simp [i.isLt]
def pairSig {W : Nat} (r s : Fin W → Row) (a : Sig) : (Signals W) := (ofRows r a,ofRows s a)
def properPairs {W : Nat} (T : Sig) (r s : Fin W → Row) :=
  ∀ i, bit (r i) T = true ∧ bit (s i) T = false
theorem pair_sep {W : Nat} {T r s} (h : (properPairs (W := W)) T r s) : Sep T W r s ((pairSig (W := W)) r s) := by
  exact ⟨h,fun a i => ⟨ofRows_bit _ _ _,ofRows_bit _ _ _⟩⟩
def faithful {W : Nat} (r s : Fin W → Row) (x : (Decor W)) := x.2 = (pairSig (W := W)) r s x.1
def bv {n : Nat} (d : Nat) (a b : BitVec n) : BitVec n :=
  if d=0 then a &&& b else if d=1 then a ||| b else if d=2 then a &&& ~~~b else ~~~a &&& b
def dbin {W : Nat} (d : Nat) (x y : (Decor W)) : (Decor W) := (bin d x.1 y.1,bv d x.2.1 y.2.1,bv d x.2.2 y.2.2)

theorem ofRows_bin {n : Nat} (r : Fin n → Row) (d : Nat) (a b : Sig) :
    ofRows r (bin d a b) = bv d (ofRows r a) (ofRows r b) := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  have h := ofRows_bit r (bin d a b) ⟨j,hj⟩
  rw [bit_bin,←ofRows_bit r a ⟨j,hj⟩,←ofRows_bit r b ⟨j,hj⟩] at h
  rw [h]
  unfold bv
  split_ifs <;> simp [hj]
theorem faithful_bin {W : Nat} {r s x y} (d) (hx : (faithful (W := W)) r s x) (hy : (faithful (W := W)) r s y) :
    (faithful (W := W)) r s ((dbin (W := W)) d x y) := by
  change x.2 = _ at hx
  change y.2 = _ at hy
  simp only [(faithful (W := W)),(dbin (W := W)),(pairSig (W := W)),ofRows_bin,hx,hy]

def defaultDecor {W : Nat} : (Decor W) := (zero,0,0)
theorem faithful_default {W : Nat} (r s) : (faithful (W := W)) r s (defaultDecor (W := W)) := by
  apply Prod.ext <;> apply BitVec.eq_of_getLsbD_eq <;> intro j hj
  · change (0 : (Bits W)).getLsbD j = (ofRows r zero).getLsbD j
    rw [show (ofRows r zero).getLsbD j = bit (r ⟨j,hj⟩) zero from ofRows_bit _ _ ⟨j,hj⟩,bit_zero]
    simp
  · change (0 : (Bits W)).getLsbD j = (ofRows s zero).getLsbD j
    rw [show (ofRows s zero).getLsbD j = bit (s ⟨j,hj⟩) zero from ofRows_bit _ _ ⟨j,hj⟩,bit_zero]
    simp
theorem faithful_get {W : Nat} {r s ws} (all : ∀ v ∈ ws, (faithful (W := W)) r s v) (i : Nat) :
    (faithful (W := W)) r s (List.getD ws i (defaultDecor (W := W))) := by
  simp only [List.getD_eq_getElem?_getD]
  cases e : ws[i]? with
  | none => exact (faithful_default (W := W)) _ _
  | some v => exact all _ (List.mem_of_getElem? e)
def decodeBank {W : Nat} (n : Nat) (bits : Nat) (ws : List (Decor W)) : List (Decor W) :=
  match n with
  | 0 => ws
  | k+1 =>
    let a := ws.getD (bits &&& 15) (defaultDecor (W := W))
    let b := ws.getD ((bits >>> 4) &&& 15) (defaultDecor (W := W))
    (decodeBank (W := W)) k (bits >>> 10) (ws++[(dbin (W := W)) ((bits >>> 8) &&& 3) a b])
theorem decode_faithful {W : Nat} (n bits) (ws) (r s) (base : ∀ v ∈ ws, (faithful (W := W)) r s v) :
    ∀ v ∈ (decodeBank (W := W)) n bits ws, (faithful (W := W)) r s v := by
  induction n generalizing ws bits with
  | zero => exact base
  | succ n ih =>
    apply ih
    intro v hv
    rcases List.mem_append.mp hv with hw | hz
    · exact base _ hw
    · obtain rfl := List.mem_singleton.mp hz
      exact (faithful_bin (W := W)) _ ((faithful_get (W := W)) base _) ((faithful_get (W := W)) base _)

def asRow {W : Nat} (cols : Nat → (Bits W)) (i : Fin W) : Row :=
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
theorem asRow_bit {W : Nat} (cols : Nat → (Bits W)) (i : Fin W) (j : Fin 7) :
    bit ((asRow (W := W)) cols i) (inputs.getD j.val zero) = (cols j.val).getLsbD i.val := by
  rw [input_coords]
  change (BitVec.ofBoolListLE (List.ofFn (fun h : Fin 7 => (cols h.val).getLsbD i.val))).getLsbD j.val = _
  simp only [BitVec.getLsbD_ofBoolListLE,List.getD_eq_getElem?_getD,List.getElem?_ofFn]
  simp [j.isLt]
def rawDecor {W : Nat} (m : Nat) (p q : Nat → (Bits W)) : List (Decor W) :=
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
theorem raw_faithful {W : Nat} (m) (p q : Nat → (Bits W)) :
    ∀ a ∈ (rawDecor (W := W)) m p q, (faithful (W := W)) ((asRow (W := W)) p) ((asRow (W := W)) q) a := by
  intro a ha
  obtain ⟨⟨j,v⟩,hv,rfl⟩ := List.mem_map.mp ha
  obtain ⟨hj,rfl⟩ := selected_entry hv
  apply Prod.ext <;> apply BitVec.eq_of_getLsbD_eq <;> intro i hi
  · exact ((asRow_bit (W := W)) p ⟨i,hi⟩ ⟨j,hj⟩).symm.trans (ofRows_bit _ _ ⟨i,hi⟩).symm
  · exact ((asRow_bit (W := W)) q ⟨i,hi⟩ ⟨j,hj⟩).symm.trans (ofRows_bit _ _ ⟨i,hi⟩).symm

def liftGoal {W : Nat} (m : Nat) (v : Nat → (Bits W)) : (Bits W) :=
  let x := fun j => if m.testBit j then v j else 0
  (x 0 &&& x 2) ||| (x 1 &&& x 3) ||| (x 0 &&& x 4) ||| (x 1 &&& x 4) ||| (x 2 &&& x 4) ||| (x 0 &&& x 5) ||| (x 1 &&& x 5) ||| (x 3 &&& x 5) ||| (x 0 &&& x 6) ||| (x 2 &&& x 6) ||| (x 3 &&& x 6) ||| (x 5 &&& x 6)
theorem bit_vertex {W : Nat} (m : Nat) (v : Nat → (Bits W)) (i : Fin W) (j : Fin 7) :
    bit ((asRow (W := W)) v i) (vertex m j.val) =
    ((if m.testBit j.val then v j.val else 0) : (Bits W)).getLsbD i.val := by
  by_cases hh : m.testBit j.val = true
  · simpa [vertex,hh] using (asRow_bit (W := W)) v i j
  · simp [vertex,hh,bit_zero]
theorem bit_liftGoal {W : Nat} (m : Nat) (v : Nat → (Bits W)) (i : Fin W) :
    bit ((asRow (W := W)) v i) (graphGoal m) = ((liftGoal (W := W)) m v).getLsbD i.val := by
  have pos (j : Nat) (hj : j<7) : (vertex m j).getLsbD ((asRow (W := W)) v i).val = ((if m.testBit j then v j else 0) : (Bits W)).getLsbD i.val := (bit_vertex (W := W)) m v i ⟨j,hj⟩
  simp only [bit,graphGoal,(liftGoal (W := W)),BitVec.getLsbD_and,BitVec.getLsbD_or]
  simp only [pos 0 (by decide),pos 1 (by decide),pos 2 (by decide),pos 3 (by decide),pos 4 (by decide),pos 5 (by decide),pos 6 (by decide)]
abbrev Cov (W : Nat) := (Bits W) × (Bits W) × (Bits W)

def addCov {W : Nat} (z : (Bits W)) (c : (Cov W)) : (Cov W) :=
  (z ||| c.1, (z &&& ~~~c.1) ||| (c.2.1 &&& ~~~z),
   (z &&& c.2.1) ||| (c.2.2 &&& ~~~z))

def coverage {W : Nat} (d : Bool) (v : List (Decor W)) : (Cov W) :=
  v.foldr (fun a c => (addCov (W := W)) (column d a.2) c) (0,0,0)

def takeOne {W : Nat} (c : (Cov W)) (a : (Bits W)) : (Bits W) := c.1 &&& ~~~(c.2.1 &&& a)
def takeTwo {W : Nat} (c : (Cov W)) (a b : (Bits W)) : (Bits W) :=
  c.1 &&& ~~~((c.2.1 &&& (a ||| b)) ||| (c.2.2 &&& (a &&& b)))

private theorem cov_one {W : Nat} (c : (Cov W)) (a : (Bits W)) : (takeOne (W := W)) ((addCov (W := W)) a c) a=c.1 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [(takeOne (W := W)),(addCov (W := W)),BitVec.getLsbD_or,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,decide_true,Bool.true_and]
  cases a.getLsbD i <;> cases c.1.getLsbD i <;> cases c.2.1.getLsbD i <;> rfl

private theorem cov_two {W : Nat} (c : (Cov W)) (a b : (Bits W)) : (takeTwo (W := W)) ((addCov (W := W)) a ((addCov (W := W)) b c)) a b=c.1 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [(takeTwo (W := W)),(addCov (W := W)),BitVec.getLsbD_or,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,decide_true,Bool.true_and]
  cases a.getLsbD i <;> cases b.getLsbD i <;> cases c.1.getLsbD i <;>
    cases c.2.1.getLsbD i <;> cases c.2.2.getLsbD i <;> rfl

private theorem add_swap {W : Nat} (c : (Cov W)) (a b : (Bits W)) : (addCov (W := W)) a ((addCov (W := W)) b c)=(addCov (W := W)) b ((addCov (W := W)) a c) := by
  apply Prod.ext
  · apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [(addCov (W := W)),BitVec.getLsbD_or]
    cases a.getLsbD i <;> cases b.getLsbD i <;> rfl
  · apply Prod.ext <;> apply BitVec.eq_of_getLsbD_eq <;> intro i hi <;>
      simp only [(addCov (W := W)),BitVec.getLsbD_or,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,decide_true,Bool.true_and] <;>
      cases a.getLsbD i <;> cases b.getLsbD i <;> cases c.1.getLsbD i <;>
      cases c.2.1.getLsbD i <;> cases c.2.2.getLsbD i <;> rfl

private theorem cov_perm {W : Nat} (d : Bool) {l r : List (Decor W)} (h : l.Perm r) : (coverage (W := W)) d l=(coverage (W := W)) d r := by
  induction h with
  | nil => rfl
  | cons a _ ih => exact congrArg ((addCov (W := W)) (column d a.2)) ih
  | swap a b t => exact (add_swap (W := W)) _ _ _
  | trans _ _ h1 h2 => exact h1.trans h2



theorem cov_word {W : Nat} (d : Bool) (v : List (Decor W)) {r s} (good : ∀ a ∈ v, (faithful (W := W)) r s a) :
    ((coverage (W := W)) d v).1 = covered d ((pairSig (W := W)) r s) (v.map Prod.fst) := by
  induction v with
  | nil => rfl
  | cons a v ih =>
    change (column d a.2 ||| ((coverage (W := W)) d v).1) = column d ((pairSig (W := W)) r s a.1) ||| _
    rw [show a.2=(pairSig (W := W)) r s a.1 from good _ (by simp),ih (fun a ha => good a (by simp [ha]))]

def delOne {W : Nat} (ws : List (Decor W)) (a : (Decor W)) (keep : Bool) :=
  if keep then ws else ws.erase a
def delTwo {W : Nat} (ws : List (Decor W)) (a b : (Decor W)) (ka kb : Bool) :=
  (delOne (W := W)) ((delOne (W := W)) ws a ka) b kb

theorem delOne_perm {W : Nat} {ws : List (Decor W)} (a : (Decor W)) (ha : a ∈ ws) :
    ws.Perm (a::ws.erase a) := List.perm_cons_erase ha

theorem cover_one {W : Nat} {ws : List (Decor W)} (d : Bool) (a : (Decor W)) (ha : a ∈ ws) (keep : Bool) :
    ((coverage (W := W)) d ((delOne (W := W)) ws a keep)).1 =
      (if keep then ((coverage (W := W)) d ws).1 else (takeOne (W := W)) ((coverage (W := W)) d ws) (column d a.2)) := by
  cases keep
  · change ((coverage (W := W)) d (ws.erase a)).1 = (takeOne (W := W)) ((coverage (W := W)) d ws) _
    rw [(cov_perm (W := W)) d ((delOne_perm (W := W)) a ha)]
    exact ((cov_one (W := W)) _ _).symm
  · rfl
theorem delTwo_perm {W : Nat} {ws : List (Decor W)} (a b : (Decor W)) (ha : a ∈ ws) (hb : b ∈ ws) (hne : a≠b) :
    ws.Perm (a::b::(ws.erase a).erase b) := by
  have hm : b ∈ ws.erase a := (List.mem_erase_of_ne (Ne.symm hne)).mpr hb
  exact ((delOne_perm (W := W)) a ha).trans (List.Perm.cons _ ((delOne_perm (W := W)) b hm))

theorem cover_two {W : Nat} {ws : List (Decor W)} (d : Bool) (a b : (Decor W)) (ha : a ∈ ws) (hb : b ∈ ws)
    (ne : a ≠ b) (ka kb : Bool) :
    ((coverage (W := W)) d ((delTwo (W := W)) ws a b ka kb)).1 =
      (if ka then (if kb then ((coverage (W := W)) d ws).1 else (takeOne (W := W)) ((coverage (W := W)) d ws) (column d b.2))
       else if kb then (takeOne (W := W)) ((coverage (W := W)) d ws) (column d a.2)
       else (takeTwo (W := W)) ((coverage (W := W)) d ws) (column d a.2) (column d b.2)) := by
  cases ka <;> cases kb
  · change ((coverage (W := W)) d ((ws.erase a).erase b)).1 = (takeTwo (W := W)) ((coverage (W := W)) d ws) _ _
    rw [(cov_perm (W := W)) d ((delTwo_perm (W := W)) a b ha hb ne)]
    exact ((cov_two (W := W)) _ _ _).symm
  · exact (cover_one (W := W)) d a ha false
  · exact (cover_one (W := W)) d b hb false
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

abbrev CovPair (W : Nat) := (Cov W) × Bool
def preCov {W : Nat} (u : Bool) (ws : List (Decor W)) : (CovPair W) := ((coverage (W := W)) (!u) ws,u)
def restCov {W : Nat} (v : (Cov W)) (a b : (Bits W)) (ka kb : Bool) :=
  if ka then (if kb then v.1 else (takeOne (W := W)) v b) else if kb then (takeOne (W := W)) v a else (takeTwo (W := W)) v a b

theorem delOne_sub {W : Nat} (ws : List (Decor W)) (a : (Decor W)) (k : Bool) : ((delOne (W := W)) ws a k).Sublist ws := by
  cases k
  · exact List.erase_sublist
  · exact List.Sublist.refl _
theorem keep_sub {W : Nat} (ws : List (Decor W)) (a b : (Decor W)) (ka kb : Bool) :
    ((delTwo (W := W)) ws a b ka kb).Sublist ws := ((delOne_sub (W := W)) _ _ _).trans ((delOne_sub (W := W)) _ _ _)
theorem len_keep {W : Nat} (ws : List (Decor W)) (a b : (Decor W)) (ka kb : Bool) (ha : a ∈ ws) (hb : b ∈ ws) (ne : a≠b) :
    ((delTwo (W := W)) ws a b ka kb).length =
      ws.length - (if ka then 0 else 1) - (if kb then 0 else 1) := by
  have hm : b ∈ ws.erase a := (List.mem_erase_of_ne (Ne.symm ne)).mpr hb
  cases ka <;> cases kb <;> simp [(delTwo (W := W)),(delOne (W := W)),List.length_erase_of_mem ha,List.length_erase_of_mem hb,List.length_erase_of_mem hm]

def movedChoice {W : Nat} (op : Nat) (a b : (Decor W)) : Choice := (op,a.1,b.1)

abbrev NodeContext (W : Nat) := Nat × Nat × List (Decor W) × (CovPair W) × List BoundPool × (Nat → List (List Sig))
def evalMove {W : Nat} (c : (NodeContext W)) (op : Nat) (a b z : (Decor W)) (ka kb : Bool) :=
  let (cap,n,ws,cov,pools,links) := c
  let len := 1+(n - (if ka then 0 else 1) - (if kb then 0 else 1))
  if len>cap then true else
    let d := !cov.2
    let rs := (restCov (W := W)) cov.1 (column d a.2) (column d b.2) ka kb
    if (rs ||| column d z.2) != BitVec.allOnes W then true else
    if !properB z.1 || ws.any (fun v => v.1==z.1) then true else
      let rest := ((delTwo (W := W)) ws a b ka kb).map Prod.fst
      closeChild cov.2 pools links (cap-1) rest ((movedChoice (W := W)) op a b)

def moveFront {W : Nat} (ws : List (Decor W)) (op : Nat) (a b : (Decor W)) (ka kb : Bool) :=
  ((dbin (W := W)) op a b).1 :: ((delTwo (W := W)) ws a b ka kb).map Prod.fst
theorem evalMove_sound {W : Nat} {u raw T r s ws pools links cap a b op ka kb}
    (pairs : (properPairs (W := W)) T r s) (faith : ∀ w ∈ ws, (faithful (W := W)) r s w)
    (nd : (ws.map Prod.fst).Nodup) (ha : a ∈ ws) (hb : b ∈ ws)
    (ne : a≠b) (hcap : 0<cap)
    (pv : ∀ p ∈ pools, ValidPool u raw T p)
    (lv : ∀ tag xs, xs ∈ links tag → Impossible u T (cap-1) (List.toFinset xs))
    (pro : proper ((dbin (W := W)) op a b).1) (fresh : ((dbin (W := W)) op a b).1 ∉ ws.map Prod.fst)
    (test : (evalMove (W := W)) (cap,ws.length,ws,(preCov (W := W)) u ws,pools,links) op a b ((dbin (W := W)) op a b) ka kb = true) :
    Impossible u T (cap-1) ((moveFront (W := W)) ws op a b ka kb).toFinset := by
  let z := (dbin (W := W)) op a b
  let rest := (delTwo (W := W)) ws a b ka kb
  let child := z.1 :: rest.map Prod.fst
  have sub : rest.Sublist ws := (keep_sub (W := W)) _ _ _ _ _
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
    rw [List.length_cons,List.length_map,(len_keep (W := W)) _ _ _ _ _ ha hb ne,Nat.add_comm 1]
  intro k hk h
  have hsz := live_size h
  change child.toFinset.card ≤ k+1 at hsz
  rw [List.toFinset_card_of_nodup ndc] at hsz
  have len : child.length ≤ cap := by omega
  unfold (evalMove (W := W)) at test
  change (if 1+(ws.length-_ - _) > cap then true else _) = true at test
  rw [leq,if_neg (by omega)] at test
  have sep := cover_required h ((pair_sep (W := W)) pairs)
  let d := !u
  have g : ((coverage (W := W)) d rest).1 = covered d ((pairSig (W := W)) r s) (rest.map Prod.fst) :=
    (cov_word (W := W)) _ _ (fun v hv => faith _ (sub.subset hv))
  have rz : ((coverage (W := W)) d rest).1 = (restCov (W := W)) ((coverage (W := W)) d ws) (column d a.2) (column d b.2) ka kb :=
    (cover_two (W := W)) d a b ha hb ne ka kb
  have hf := (faithful_bin (W := W)) op (faith _ ha) (faith _ hb)
  change column d ((pairSig (W := W)) r s z.1) ||| covered d ((pairSig (W := W)) r s) (rest.map Prod.fst) = _ at sep
  change z.2 = (pairSig (W := W)) r s z.1 at hf
  rw [←hf,←g,rz,BitVec.or_comm] at sep
  have be : (((restCov (W := W)) ((coverage (W := W)) (!u) ws) (column (!u) a.2) (column (!u) b.2) ka kb ||| column (!u) z.2) != BitVec.allOnes W) = false := by
    simpa using sep
  change (if ((restCov (W := W)) ((coverage (W := W)) (!u) ws) (column (!u) a.2) (column (!u) b.2) ka kb ||| column (!u) z.2) != BitVec.allOnes W then true else if !properB z.1 || ws.any (fun v => v.1==z.1) then true else _) = true at test
  rw [be,pp,fr] at test
  exact closeChild_sound (op:=(movedChoice (W := W)) op a b) (rest:=rest.map Prod.fst) pv lv ndc test k hk h

def testPair {W : Nat} (ctx : (NodeContext W)) (a b : (Decor W)) (op : Nat) :=
  let z := (dbin (W := W)) op a b
  let attempt := (evalMove (W := W)) ctx op a b z
  attempt false false && attempt true false && attempt false true && attempt true true
def opsOf (u : Bool) : List Nat := if u then [0,1,2,3] else [0,1]
theorem opsOf_mem {u d} (h : allowed u d) : d ∈ opsOf u := by
  rcases allowed_four h with rfl | rfl | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · cases u <;> simp [opsOf]
  · cases u <;> simp [opsOf]
  · simp [opsOf]
  · simp [opsOf]
def testRow {W : Nat} (ctx : (NodeContext W)) (a : (Decor W)) (bs : List (Decor W)) :=
    bs.all (fun b => (opsOf ctx.2.2.2.1.2).all ((testPair (W := W)) ctx a b))
def testAll {W : Nat} (ctx : (NodeContext W)) : List (Decor W) → Bool
  | [] => true
  | a::bs => (testRow (W := W)) ctx a bs && (testAll (W := W)) ctx bs

theorem all_binary {W : Nat} {ctx ws} (h : (testAll (W := W)) ctx ws=true) {a b : (Decor W)} (ha : a∈ws) (hb : b∈ws)
    (ne : a≠b) : (∀ d, allowed ctx.2.2.2.1.2 d → (testPair (W := W)) ctx a b d=true) ∨
      (∀ d, allowed ctx.2.2.2.1.2 d → (testPair (W := W)) ctx b a d=true) := by
  induction ws with
  | nil => simp at ha
  | cons w ws ih =>
    simp only [(testAll (W := W)),Bool.and_eq_true,(testRow (W := W)),List.all_eq_true] at h
    rcases List.mem_cons.mp ha with rfl | haTail
    · have bm := (List.mem_cons.mp hb).resolve_left (Ne.symm ne)
      exact Or.inl fun d hd => h.1 b bm d (opsOf_mem hd)
    · rcases List.mem_cons.mp hb with rfl | hbTail
      · exact Or.inr fun d hd => h.1 a haTail d (opsOf_mem hd)
      · exact ih h.2 haTail hbTail

theorem testPair_at {W : Nat} {ctx a b d} (h : (testPair (W := W)) ctx a b d = true) (ka kb : Bool) :
    (evalMove (W := W)) ctx d a b ((dbin (W := W)) d a b) ka kb = true := by
  simp only [(testPair (W := W)),Bool.and_eq_true] at h
  cases ka <;> cases kb <;> first | exact h.1.1.1 | exact h.1.2 | exact h.1.1.2 | exact h.2

theorem keep_mem {v : List Sig} {w : Sig} (a : Sig) (k : Bool) :
    w ∈ kept k a v ↔ (w=a ∧ k=true) ∨ w∈v := by cases k <;> simp [kept]
theorem mem_delone {W : Nat} {v : List (Decor W)} (nd : v.Nodup) (a w : (Decor W)) (k : Bool) :
    w ∈ (delOne (W := W)) v a k ↔ w∈v ∧ (w≠a ∨ k=true) := by
  cases k <;> simp [(delOne (W := W)),nd.mem_erase_iff,and_comm]

theorem unique_value {W : Nat} {ws : List (Decor W)} (nd : (ws.map Prod.fst).Nodup) {a b : (Decor W)}
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

theorem kept_value {W : Nat} {ws : List (Decor W)} (nd : (ws.map Prod.fst).Nodup) {a b : (Decor W)}
    (ha : a ∈ ws) (hb : b ∈ ws) (ka kb : Bool) (v : Sig) :
    v ∈ ((delTwo (W := W)) ws a b ka kb).map Prod.fst ↔
    v ∈ ws.map Prod.fst ∧ (v≠a.1 ∨ ka=true) ∧ (v≠b.1 ∨ kb=true) := by
  have wn := nd.of_map
  have dn := wn.sublist ((delOne_sub (W := W)) ws a ka)
  simp only [(delTwo (W := W)),List.mem_map,(mem_delone (W := W)) wn,(mem_delone (W := W)) dn]
  constructor
  · rintro ⟨w,hw,rfl⟩
    exact ⟨⟨_,hw.1.1,rfl⟩,hw.1.2.imp (fun ne eq => ne ((unique_value (W := W)) nd hw.1.1 ha eq)) id,
          hw.2.imp (fun ne eq => ne ((unique_value (W := W)) nd hw.1.1 hb eq)) id⟩
  · rintro ⟨⟨w,hm,rfl⟩,h1,h2⟩
    exact ⟨w,⟨⟨hm,h1.imp (fun ne eq => ne (congrArg Prod.fst eq)) id⟩,
        h2.imp (fun ne eq => ne (congrArg Prod.fst eq)) id⟩,rfl⟩

theorem binary_front {W : Nat} {ws : List (Decor W)} (nd : (ws.map Prod.fst).Nodup) {a b : (Decor W)}
    (ha : a∈ws) (hb : b∈ws) (ne : a.1≠b.1) (d : Nat) (ka kb : Bool) :
    ((moveFront (W := W)) ws d a b ka kb).toFinset =
      (childTwo (ws.map Prod.fst) a.1 b.1 d ka kb).toFinset := by
  ext v
  have av := List.mem_map_of_mem (f:=Prod.fst) ha
  have bv' := List.mem_map_of_mem (f:=Prod.fst) hb
  simp only [(moveFront (W := W)),childTwo,List.toFinset_cons,Finset.mem_insert,List.mem_toFinset,
    (kept_value (W := W)) nd ha hb,keep_mem,(nd.erase _).mem_erase_iff,nd.mem_erase_iff,(dbin (W := W))]
  by_cases va : v=a.1 <;> by_cases vb : v=b.1 <;> cases ka <;> cases kb <;> simp_all

theorem childTwo_swap {u} (v : List Sig) (nd : v.Nodup) (a b : Sig) (d : Nat) (hd : allowed u d) (ka kb : Bool) :
    (childTwo v a b d ka kb).toFinset = (childTwo v b a (flipOp d) kb ka).toFinset := by
  ext x
  simp only [childTwo,List.toFinset_cons,Finset.mem_insert,List.mem_toFinset,
    keep_mem,(nd.erase _).mem_erase_iff,nd.mem_erase_iff,bin_flip hd a b]
  tauto

theorem node_sound {W : Nat} {u raw T r s ws pools links cap}
    (pairs : (properPairs (W := W)) T r s) (faith : ∀ w ∈ ws, (faithful (W := W)) r s w)
    (nd : (ws.map Prod.fst).Nodup) (out : T ∉ ws.map Prod.fst)
    (pv : ∀ p ∈ pools, ValidPool u raw T p)
    (lv : ∀ tag xs, xs ∈ links tag → Impossible u T (cap-1) (List.toFinset xs))
    (checks : (testAll (W := W)) (cap,ws.length,ws,(preCov (W := W)) u ws,pools,links) ws = true) :
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
  have one (a b : (Decor W)) (d : Nat) (aa : a∈ws) (bb : b∈ws) (ne' : a.1≠b.1) (ka kb : Bool)
      (pr : proper (bin d a.1 b.1)) (fr : bin d a.1 b.1 ∉ ws.map Prod.fst)
      (test : (testPair (W := W)) (cap,ws.length,ws,(preCov (W := W)) u ws,pools,links) a b d = true) :
      Impossible u T (cap-1) (childTwo (ws.map Prod.fst) a.1 b.1 d ka kb).toFinset := by
    rw [←(binary_front (W := W)) nd aa bb ne']
    exact (evalMove_sound (W := W)) pairs faith nd aa bb (fun e => ne' (congrArg Prod.fst e)) hc' pv lv
      pr fr ((testPair_at (W := W)) test ka kb)
  rcases (all_binary (W := W)) checks haW hbW ab with hh | hh
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


def compactNext {W : Nat} (path : Nat) (ws : List (Decor W)) (hist : List Choice) :
    List (Decor W) × List Choice :=
  let a := ws.getD (path &&& 31) (defaultDecor (W := W))
  let b := ws.getD ((path >>> 5) &&& 31) (defaultDecor (W := W))
  let d := (path >>> 10) &&& 3
  (ws ++ [(dbin (W := W)) d a b], hist ++ [(d, a.1, b.1)])

def walkCompact {W : Nat} : Nat → Nat → List (Decor W) → List Choice → List (Decor W) × List Choice
  | 0, _, ws, hist => (ws, hist)
  | depth + 1, path, ws, hist =>
    let next := (compactNext (W := W)) path ws hist
    (walkCompact (W := W)) depth (path >>> 12) next.1 next.2

theorem walkCompact_faithful {W : Nat} (depth path : Nat) (ws : List (Decor W)) (hist : List Choice)
    {r s} (base : ∀ v ∈ ws, (faithful (W := W)) r s v) :
    ∀ v ∈ ((walkCompact (W := W)) depth path ws hist).1, (faithful (W := W)) r s v := by
  induction depth generalizing path ws hist with
  | zero => exact base
  | succ depth ih =>
    apply ih
    intro v hv
    rcases List.mem_append.mp hv with hb | hz
    · exact base _ hb
    · obtain rfl := List.mem_singleton.mp hz
      exact (faithful_bin (W := W)) _ ((faithful_get (W := W)) base _) ((faithful_get (W := W)) base _)

def rowWires {W : Nat} : List (Decor W) → Nat → List (Decor W)
  | [], _ => []
  | v :: bank, mask =>
    if mask.testBit 0 then v :: (rowWires (W := W)) bank (mask >>> 1)
    else (rowWires (W := W)) bank (mask >>> 1)

theorem rowWires_faithful {W : Nat} (bank : List (Decor W)) (mask : Nat) {r s}
    (base : ∀ v ∈ bank, (faithful (W := W)) r s v) :
    ∀ v ∈ (rowWires (W := W)) bank mask, (faithful (W := W)) r s v := by
  induction bank generalizing mask with
  | nil => simp [(rowWires (W := W))]
  | cons v bank ih =>
    have hv := List.forall_mem_cons.mp base
    unfold (rowWires (W := W))
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

abbrev CompactGrid (W : Nat) := Nat × Nat × (Nat → (Bits W)) × (Nat → (Bits W))
def CompactGrid.mask {W : Nat} (g : (CompactGrid W)) := g.1
def CompactGrid.top {W : Nat} (g : (CompactGrid W)) := g.2.1
def CompactGrid.pos {W : Nat} (g : (CompactGrid W)) := g.2.2.1
def CompactGrid.neg {W : Nat} (g : (CompactGrid W)) := g.2.2.2

abbrev CompactTable := (Nat → Nat) × (Nat → Nat → Nat) × (Nat → Nat → Nat) ×
  (Nat → Nat → List Nat) × (Nat → Nat → List Nat)
def CompactTable.count (t : CompactTable) := t.1
def CompactTable.path (t : CompactTable) := t.2.1
def CompactTable.live (t : CompactTable) := t.2.2.1
def CompactTable.picks (t : CompactTable) := t.2.2.2.1
def CompactTable.bucket (t : CompactTable) := t.2.2.2.2

def chartAt {W : Nat} (g : (CompactGrid W)) (t : CompactTable) (k i : Nat) :=
  let bank := (walkCompact (W := W)) (g.top-k) (t.path k i) ((rawDecor (W := W)) g.mask g.pos g.neg) []
  ((rowWires (W := W)) bank.1 (t.live k i), bank.2)

def wordsAt {W : Nat} (g : (CompactGrid W)) (t : CompactTable) (k i : Nat) :=
  ((chartAt (W := W)) g t k i).1.map Prod.fst

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

def linkedCandidates {W : Nat} (g : (CompactGrid W)) (t : CompactTable) (perms : Perms) (k tag : Nat) :=
  (t.bucket k tag).filterMap (fun code =>
    let name := code / perms.size
    if name < t.count k then
      perms[code % perms.size]?.map (fun swaps => applySwaps swaps ((wordsAt (W := W)) g t k name))
    else none)

theorem linkedCandidates_valid {W : Nat} {g t perms k}
    (autos : ∀ p ∈ perms, autoOK (graphGoal g.mask) (p.map swapRows).reverse = true)
    (prev : ∀ i < t.count k, Impossible true (graphGoal g.mask) k ((wordsAt (W := W)) g t k i).toFinset) :
    ∀ tag xs, xs ∈ (linkedCandidates (W := W)) g t perms k tag → Impossible true (graphGoal g.mask) k xs.toFinset := by
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

abbrev cached_NodeContext (W : Nat) := Nat × Nat × List (Decor W) × (CovPair W) × List NodePool × (Nat → List (List Sig))
def cached_evalMove {W : Nat} (c : (cached_NodeContext W)) (op : Nat) (a b z : (Decor W)) (ka kb : Bool) :=
  let (cap,n,ws,cov,pools,links) := c
  let len := 1+(n - (if ka then 0 else 1) - (if kb then 0 else 1))
  if len>cap then true else
    let d := !cov.2
    let rs := (restCov (W := W)) cov.1 (column d a.2) (column d b.2) ka kb
    if (rs ||| column d z.2) != BitVec.allOnes W then true else
    if !properB z.1 || ws.any (fun v => v.1==z.1) then true else
      let rest := ((delTwo (W := W)) ws a b ka kb).map Prod.fst
      cachedClose cov.2 pools links (cap-1) rest ((movedChoice (W := W)) op a b)

def cached_moveFront {W : Nat} (ws : List (Decor W)) (op : Nat) (a b : (Decor W)) (ka kb : Bool) :=
  ((dbin (W := W)) op a b).1 :: ((delTwo (W := W)) ws a b ka kb).map Prod.fst
theorem cached_evalMove_sound {W : Nat} {u raw T r s ws} {pools : List BoundPool} {links cap a b op ka kb}
    (pairs : (properPairs (W := W)) T r s) (faith : ∀ w ∈ ws, (faithful (W := W)) r s w)
    (nd : (ws.map Prod.fst).Nodup) (ha : a ∈ ws) (hb : b ∈ ws)
    (ne : a≠b) (hcap : 0<cap)
    (pv : ∀ p ∈ pools, ValidPool u raw T p)
    (lv : ∀ tag xs, xs ∈ links tag → Impossible u T (cap-1) (List.toFinset xs))
    (pro : proper ((dbin (W := W)) op a b).1) (fresh : ((dbin (W := W)) op a b).1 ∉ ws.map Prod.fst)
    (test : (cached_evalMove (W := W)) (cap,ws.length,ws,(preCov (W := W)) u ws,pools.map (cacheOnePool u (ws.map Prod.fst)),links) op a b ((dbin (W := W)) op a b) ka kb = true) :
    Impossible u T (cap-1) ((cached_moveFront (W := W)) ws op a b ka kb).toFinset := by
  let z := (dbin (W := W)) op a b
  let rest := (delTwo (W := W)) ws a b ka kb
  let child := z.1 :: rest.map Prod.fst
  have sub : rest.Sublist ws := (keep_sub (W := W)) _ _ _ _ _
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
    rw [List.length_cons,List.length_map,(len_keep (W := W)) _ _ _ _ _ ha hb ne,Nat.add_comm 1]
  intro k hk h
  have hsz := cachedLiveSize h
  change child.toFinset.card ≤ k+1 at hsz
  rw [List.toFinset_card_of_nodup ndc] at hsz
  have len : child.length ≤ cap := by omega
  unfold (cached_evalMove (W := W)) at test
  change (if 1+(ws.length-_ - _) > cap then true else _) = true at test
  rw [leq,if_neg (by omega)] at test
  have sep := cover_required h ((pair_sep (W := W)) pairs)
  let d := !u
  have g : ((coverage (W := W)) d rest).1 = covered d ((pairSig (W := W)) r s) (rest.map Prod.fst) :=
    (cov_word (W := W)) _ _ (fun v hv => faith _ (sub.subset hv))
  have rz : ((coverage (W := W)) d rest).1 = (restCov (W := W)) ((coverage (W := W)) d ws) (column d a.2) (column d b.2) ka kb :=
    (cover_two (W := W)) d a b ha hb ne ka kb
  have hf := (faithful_bin (W := W)) op (faith _ ha) (faith _ hb)
  change column d ((pairSig (W := W)) r s z.1) ||| covered d ((pairSig (W := W)) r s) (rest.map Prod.fst) = _ at sep
  change z.2 = (pairSig (W := W)) r s z.1 at hf
  rw [←hf,←g,rz,BitVec.or_comm] at sep
  have be : (((restCov (W := W)) ((coverage (W := W)) (!u) ws) (column (!u) a.2) (column (!u) b.2) ka kb ||| column (!u) z.2) != BitVec.allOnes W) = false := by
    simpa using sep
  change (if ((restCov (W := W)) ((coverage (W := W)) (!u) ws) (column (!u) a.2) (column (!u) b.2) ka kb ||| column (!u) z.2) != BitVec.allOnes W then true else if !properB z.1 || ws.any (fun v => v.1==z.1) then true else _) = true at test
  rw [be,pp,fr] at test
  exact cachedClose_sound (op:=(movedChoice (W := W)) op a b) (rest:=rest.map Prod.fst) pv lv ndc (sub.map _).subset (List.mem_map_of_mem ha) (List.mem_map_of_mem hb) test k hk h

def cached_testPair {W : Nat} (ctx : (cached_NodeContext W)) (a b : (Decor W)) (op : Nat) :=
  let z := (dbin (W := W)) op a b
  let attempt := (cached_evalMove (W := W)) ctx op a b z
  attempt false false && attempt true false && attempt false true && attempt true true
def cached_opsOf (u : Bool) : List Nat := if u then [0,1,2,3] else [0,1]
theorem cached_opsOf_mem {u d} (h : allowed u d) : d ∈ cached_opsOf u := by
  rcases allowed_four h with rfl | rfl | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · cases u <;> simp [cached_opsOf]
  · cases u <;> simp [cached_opsOf]
  · simp [cached_opsOf]
  · simp [cached_opsOf]
def cached_testRow {W : Nat} (ctx : (cached_NodeContext W)) (a : (Decor W)) (bs : List (Decor W)) :=
    bs.all (fun b => (cached_opsOf ctx.2.2.2.1.2).all ((cached_testPair (W := W)) ctx a b))
def cached_testAll {W : Nat} (ctx : (cached_NodeContext W)) : List (Decor W) → Bool
  | [] => true
  | a::bs => (cached_testRow (W := W)) ctx a bs && (cached_testAll (W := W)) ctx bs

theorem cached_all_binary {W : Nat} {ctx ws} (h : (cached_testAll (W := W)) ctx ws=true) {a b : (Decor W)} (ha : a∈ws) (hb : b∈ws)
    (ne : a≠b) : (∀ d, allowed ctx.2.2.2.1.2 d → (cached_testPair (W := W)) ctx a b d=true) ∨
      (∀ d, allowed ctx.2.2.2.1.2 d → (cached_testPair (W := W)) ctx b a d=true) := by
  induction ws with
  | nil => simp at ha
  | cons w ws ih =>
    simp only [(cached_testAll (W := W)),Bool.and_eq_true,(cached_testRow (W := W)),List.all_eq_true] at h
    rcases List.mem_cons.mp ha with rfl | haTail
    · have bm := (List.mem_cons.mp hb).resolve_left (Ne.symm ne)
      exact Or.inl fun d hd => h.1 b bm d (cached_opsOf_mem hd)
    · rcases List.mem_cons.mp hb with rfl | hbTail
      · exact Or.inr fun d hd => h.1 a haTail d (cached_opsOf_mem hd)
      · exact ih h.2 haTail hbTail

theorem cached_testPair_at {W : Nat} {ctx a b d} (h : (cached_testPair (W := W)) ctx a b d = true) (ka kb : Bool) :
    (cached_evalMove (W := W)) ctx d a b ((dbin (W := W)) d a b) ka kb = true := by
  simp only [(cached_testPair (W := W)),Bool.and_eq_true] at h
  cases ka <;> cases kb <;> first | exact h.1.1.1 | exact h.1.2 | exact h.1.1.2 | exact h.2

theorem cached_keep_mem {v : List Sig} {w : Sig} (a : Sig) (k : Bool) :
    w ∈ kept k a v ↔ (w=a ∧ k=true) ∨ w∈v := by cases k <;> simp [kept]
theorem cached_mem_delone {W : Nat} {v : List (Decor W)} (nd : v.Nodup) (a w : (Decor W)) (k : Bool) :
    w ∈ (delOne (W := W)) v a k ↔ w∈v ∧ (w≠a ∨ k=true) := by
  cases k <;> simp [(delOne (W := W)),nd.mem_erase_iff,and_comm]

theorem cached_unique_value {W : Nat} {ws : List (Decor W)} (nd : (ws.map Prod.fst).Nodup) {a b : (Decor W)}
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

theorem cached_kept_value {W : Nat} {ws : List (Decor W)} (nd : (ws.map Prod.fst).Nodup) {a b : (Decor W)}
    (ha : a ∈ ws) (hb : b ∈ ws) (ka kb : Bool) (v : Sig) :
    v ∈ ((delTwo (W := W)) ws a b ka kb).map Prod.fst ↔
    v ∈ ws.map Prod.fst ∧ (v≠a.1 ∨ ka=true) ∧ (v≠b.1 ∨ kb=true) := by
  have wn := nd.of_map
  have dn := wn.sublist ((delOne_sub (W := W)) ws a ka)
  simp only [(delTwo (W := W)),List.mem_map,(cached_mem_delone (W := W)) wn,(cached_mem_delone (W := W)) dn]
  constructor
  · rintro ⟨w,hw,rfl⟩
    exact ⟨⟨_,hw.1.1,rfl⟩,hw.1.2.imp (fun ne eq => ne ((cached_unique_value (W := W)) nd hw.1.1 ha eq)) id,
          hw.2.imp (fun ne eq => ne ((cached_unique_value (W := W)) nd hw.1.1 hb eq)) id⟩
  · rintro ⟨⟨w,hm,rfl⟩,h1,h2⟩
    exact ⟨w,⟨⟨hm,h1.imp (fun ne eq => ne (congrArg Prod.fst eq)) id⟩,
        h2.imp (fun ne eq => ne (congrArg Prod.fst eq)) id⟩,rfl⟩

theorem cached_binary_front {W : Nat} {ws : List (Decor W)} (nd : (ws.map Prod.fst).Nodup) {a b : (Decor W)}
    (ha : a∈ws) (hb : b∈ws) (ne : a.1≠b.1) (d : Nat) (ka kb : Bool) :
    ((cached_moveFront (W := W)) ws d a b ka kb).toFinset =
      (childTwo (ws.map Prod.fst) a.1 b.1 d ka kb).toFinset := by
  ext v
  have av := List.mem_map_of_mem (f:=Prod.fst) ha
  have bv' := List.mem_map_of_mem (f:=Prod.fst) hb
  simp only [(cached_moveFront (W := W)),childTwo,List.toFinset_cons,Finset.mem_insert,List.mem_toFinset,
    (cached_kept_value (W := W)) nd ha hb,cached_keep_mem,(nd.erase _).mem_erase_iff,nd.mem_erase_iff,(dbin (W := W))]
  by_cases va : v=a.1 <;> by_cases vb : v=b.1 <;> cases ka <;> cases kb <;> simp_all

theorem cached_childTwo_swap {u} (v : List Sig) (nd : v.Nodup) (a b : Sig) (d : Nat) (hd : allowed u d) (ka kb : Bool) :
    (childTwo v a b d ka kb).toFinset = (childTwo v b a (flipOp d) kb ka).toFinset := by
  ext x
  simp only [childTwo,List.toFinset_cons,Finset.mem_insert,List.mem_toFinset,
    cached_keep_mem,(nd.erase _).mem_erase_iff,nd.mem_erase_iff,bin_flip hd a b]
  tauto

theorem cached_node_sound {W : Nat} {u raw T r s ws} {pools : List BoundPool} {links cap}
    (pairs : (properPairs (W := W)) T r s) (faith : ∀ w ∈ ws, (faithful (W := W)) r s w)
    (nd : (ws.map Prod.fst).Nodup) (out : T ∉ ws.map Prod.fst)
    (pv : ∀ p ∈ pools, ValidPool u raw T p)
    (lv : ∀ tag xs, xs ∈ links tag → Impossible u T (cap-1) (List.toFinset xs))
    (checks : (cached_testAll (W := W)) (cap,ws.length,ws,(preCov (W := W)) u ws,pools.map (cacheOnePool u (ws.map Prod.fst)),links) ws = true) :
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
  have one (a b : (Decor W)) (d : Nat) (aa : a∈ws) (bb : b∈ws) (ne' : a.1≠b.1) (ka kb : Bool)
      (pr : proper (bin d a.1 b.1)) (fr : bin d a.1 b.1 ∉ ws.map Prod.fst)
      (test : (cached_testPair (W := W)) (cap,ws.length,ws,(preCov (W := W)) u ws,pools.map (cacheOnePool u (ws.map Prod.fst)),links) a b d = true) :
      Impossible u T (cap-1) (childTwo (ws.map Prod.fst) a.1 b.1 d ka kb).toFinset := by
    rw [←(cached_binary_front (W := W)) nd aa bb ne']
    exact (cached_evalMove_sound (W := W)) pairs faith nd aa bb (fun e => ne' (congrArg Prod.fst e)) hc' pv lv
      pr fr ((cached_testPair_at (W := W)) test ka kb)
  rcases (cached_all_binary (W := W)) checks haW hbW ab with hh | hh
  · exact one a b d haW hbW ne ka kb pro fresh (hh d hd)
  · rw [cached_childTwo_swap _ nd _ _ d hd]
    exact one b a (flipOp d) hbW haW (Ne.symm ne) kb ka (bin_flip hd a.1 b.1 ▸ pro)
      (bin_flip hd a.1 b.1 ▸ fresh) (hh _ (flip_flip hd).1)



def compactNode {W : Nat} (g : (CompactGrid W)) (t : CompactTable) (dom : Domains) (perms : Perms) (k i : Nat) : Bool :=
  let state := (chartAt (W := W)) g t k i
  let ws := state.1
  let words := ws.map Prod.fst
  let pools := poolList g.mask dom state.2 (t.picks k i)
  let links := (linkedCandidates (W := W)) g t perms (k-1)
  decide words.Nodup && (!(words.contains (graphGoal g.mask)) &&
    (if k=0 then true else (cached_testAll (W := W)) (k,ws.length,ws,(preCov (W := W)) true ws,pools.map (cacheOnePool true words),links) ws))

theorem compactNode_sound {W : Nat} {g t dom perms k i}
    (pairs : (properPairs (W := W)) (graphGoal g.mask) ((asRow (W := W)) g.pos) ((asRow (W := W)) g.neg))
    (valid : ∀ d ∈ dom, Slice true (vars g.mask) (graphGoal g.mask) d.1 d.2)
    (autos : ∀ p ∈ perms, autoOK (graphGoal g.mask) (p.map swapRows).reverse = true)
    (prev : 0 < k → ∀ j < t.count (k-1),
      Impossible true (graphGoal g.mask) (k-1) ((wordsAt (W := W)) g t (k-1) j).toFinset)
    (check : (compactNode (W := W)) g t dom perms k i = true) :
    Impossible true (graphGoal g.mask) k ((wordsAt (W := W)) g t k i).toFinset := by
  simp only [(compactNode (W := W)),Bool.and_eq_true,decide_eq_true_eq] at check
  have out : graphGoal g.mask ∉ (wordsAt (W := W)) g t k i := by simpa [(wordsAt (W := W))] using check.2.1
  by_cases hz : k=0
  · subst k
    intro n hn run
    obtain rfl : n = 0 := by omega
    exact out (List.mem_toFinset.mp (run.1.symm ▸ Finset.mem_singleton_self _))
  · have f : ∀ v ∈ ((chartAt (W := W)) g t k i).1, (faithful (W := W)) ((asRow (W := W)) g.pos) ((asRow (W := W)) g.neg) v :=
      (rowWires_faithful (W := W)) _ (t.live k i) ((walkCompact_faithful (W := W)) (g.top-k) (t.path k i)
        ((rawDecor (W := W)) g.mask g.pos g.neg) [] ((raw_faithful (W := W)) g.mask g.pos g.neg))
    apply (cached_node_sound (W := W)) pairs f check.1 out (poolList_valid valid) ((linkedCandidates_valid (W := W)) autos (prev (by omega)))
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

theorem compactAll {W : Nat} {g t dom perms}
    (pairs : (properPairs (W := W)) (graphGoal g.mask) ((asRow (W := W)) g.pos) ((asRow (W := W)) g.neg))
    (valid : ∀ d ∈ dom, Slice true (vars g.mask) (graphGoal g.mask) d.1 d.2)
    (autos : ∀ p ∈ perms, autoOK (graphGoal g.mask) (p.map swapRows).reverse = true)
    (blocks : ∀ k ≤ g.top, chartBlock ((compactNode (W := W)) g t dom perms k) 0 (t.count k) = true) :
    ∀ k ≤ g.top, ∀ i < t.count k, Impossible true (graphGoal g.mask) k ((wordsAt (W := W)) g t k i).toFinset := by
  intro k
  induction k with
  | zero =>
    intro h i hi
    exact (compactNode_sound (W := W)) pairs valid autos (by omega) (chartBlock_at (blocks 0 h) i (by omega) (by simpa using hi))
  | succ k ih =>
    intro h i hi
    exact (compactNode_sound (W := W)) pairs valid autos (fun _ => ih (by omega)) (chartBlock_at (blocks _ h) i (by omega) (by simpa using hi))

theorem compactPairs {W : Nat} {g : (CompactGrid W)}
    (yes : (liftGoal (W := W)) g.mask g.pos = BitVec.allOnes W) (no : (liftGoal (W := W)) g.mask g.neg = 0) :
    (properPairs (W := W)) (graphGoal g.mask) ((asRow (W := W)) g.pos) ((asRow (W := W)) g.neg) := by
  intro i
  constructor
  · rw [(bit_liftGoal (W := W)),yes,BitVec.getLsbD_allOnes]
    exact decide_eq_true i.isLt
  · rw [(bit_liftGoal (W := W)),no]
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

theorem compactRoot {W : Nat} {g t dom perms}
    (pairs : (properPairs (W := W)) (graphGoal g.mask) ((asRow (W := W)) g.pos) ((asRow (W := W)) g.neg))
    (valid : ∀ d ∈ dom, Slice true (vars g.mask) (graphGoal g.mask) d.1 d.2)
    (autos : ∀ p ∈ perms, autoOK (graphGoal g.mask) (p.map swapRows).reverse = true)
    (blocks : ∀ k ≤ g.top, chartBlock ((compactNode (W := W)) g t dom perms k) 0 (t.count k) = true)
    (existsRoot : 0 < t.count g.top)
    (root : (wordsAt (W := W)) g t g.top 0 = vars g.mask) :
    Impossible true (graphGoal g.mask) g.top (vars g.mask).toFinset := by
  rw [←root]
  exact (compactAll (W := W)) pairs valid autos blocks _ (Nat.le_refl _) 0 existsRoot

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

theorem augmentedPairLower {W : Nat} {m hints top : Nat} {P Q : Nat → (Bits W)} {pools : List BoundPool}
    {links : Nat → List (List Sig)} {a b : (Decor W)} {op : Nat}
    (pairs : (properPairs (W := W)) (graphGoal m) ((asRow (W := W)) P) ((asRow (W := W)) Q))
    (valid : ∀ p ∈ pools, ValidPool true (vars m) (graphGoal m) p)
    (link : ∀ tag xs, xs ∈ links tag → Impossible true (graphGoal m) (top-1) xs.toFinset)
    (raw : ((rawDecor (W := W)) m P Q).map Prod.fst = vars m)
    (essen : essOK m hints = true) (nd : (vars m).Nodup)
    (prior : Impossible true (graphGoal m) (top-1) (vars m).toFinset)
    (ha : a ∈ (rawDecor (W := W)) m P Q) (hb : b ∈ (rawDecor (W := W)) m P Q) (diff : a.1 ≠ b.1)
    (pa : proper a.1) (pb : proper b.1) (pt : 0 < top) (allow : allowed true op)
    (pg : proper (bin op a.1 b.1)) (plain : plainWord (bin op a.1 b.1) = true)
    (new : bin op a.1 b.1 ∉ vars m)
    (check : (testPair (W := W)) (top,((rawDecor (W := W)) m P Q).length,(rawDecor (W := W)) m P Q,(preCov (W := W)) true ((rawDecor (W := W)) m P Q),pools,links) a b op = true) :
    Lower true (bin op a.1 b.1 :: vars m) (graphGoal m) top := by
  have rt := essen
  simp only [essOK,Bool.and_eq_true,beq_iff_eq] at rt
  have rn : (((rawDecor (W := W)) m P Q).map Prod.fst).Nodup := raw ▸ nd
  have amin : a.1 ∈ vars m := raw ▸ List.mem_map_of_mem (f:=Prod.fst) ha
  have bmin : b.1 ∈ vars m := raw ▸ List.mem_map_of_mem (f:=Prod.fst) hb
  have fresh : bin op a.1 b.1 ∉ ((rawDecor (W := W)) m P Q).map Prod.fst := raw ▸ new
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
    rw [←raw,←(binary_front (W := W)) rn ha hb diff]
    exact (evalMove_sound (W := W)) pairs ((raw_faithful (W := W)) m P Q) rn ha hb (fun e => diff (congrArg Prod.fst e)) pt valid link pg fresh ((testPair_at (W := W)) check ka kb)
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

def richNode {W : Nat} (g : (CompactGrid W)) (t : CompactTable) (dom : RichDomains) (perms : Perms) (k i : Nat) : Bool :=
  let state := (chartAt (W := W)) g t k i
  let ws := state.1
  let words := ws.map Prod.fst
  let pools := richPoolList g.mask dom state.2 (t.picks k i)
  let links := (linkedCandidates (W := W)) g t perms (k-1)
  decide words.Nodup && (!(words.contains (graphGoal g.mask)) &&
    (if k=0 then true else (cached_testAll (W := W)) (k,ws.length,ws,(preCov (W := W)) true ws,pools.map (cacheOnePool true words),links) ws))

theorem richNode_sound {W : Nat} {g t dom perms k i}
    (pairs : (properPairs (W := W)) (graphGoal g.mask) ((asRow (W := W)) g.pos) ((asRow (W := W)) g.neg))
    (valid : RichValid g.mask dom)
    (autos : ∀ p ∈ perms, autoOK (graphGoal g.mask) (p.map swapRows).reverse = true)
    (prev : 0 < k → ∀ j < t.count (k-1),
      Impossible true (graphGoal g.mask) (k-1) ((wordsAt (W := W)) g t (k-1) j).toFinset)
    (check : (richNode (W := W)) g t dom perms k i = true) :
    Impossible true (graphGoal g.mask) k ((wordsAt (W := W)) g t k i).toFinset := by
  simp only [(richNode (W := W)),Bool.and_eq_true,decide_eq_true_eq] at check
  have out : graphGoal g.mask ∉ (wordsAt (W := W)) g t k i := by simpa [(wordsAt (W := W))] using check.2.1
  by_cases hz : k=0
  · subst k
    intro n hn run
    obtain rfl : n = 0 := by omega
    exact out (List.mem_toFinset.mp (run.1.symm ▸ Finset.mem_singleton_self _))
  · have f : ∀ v ∈ ((chartAt (W := W)) g t k i).1, (faithful (W := W)) ((asRow (W := W)) g.pos) ((asRow (W := W)) g.neg) v :=
      (rowWires_faithful (W := W)) _ (t.live k i) ((walkCompact_faithful (W := W)) (g.top-k) (t.path k i)
        ((rawDecor (W := W)) g.mask g.pos g.neg) [] ((raw_faithful (W := W)) g.mask g.pos g.neg))
    apply (cached_node_sound (W := W)) pairs f check.1 out (richPool_valid valid) ((linkedCandidates_valid (W := W)) autos (prev (by omega)))
    simpa only [hz,ite_false] using check.2.2

theorem richAll {W : Nat} {g t dom perms}
    (pairs : (properPairs (W := W)) (graphGoal g.mask) ((asRow (W := W)) g.pos) ((asRow (W := W)) g.neg))
    (valid : RichValid g.mask dom)
    (autos : ∀ p ∈ perms, autoOK (graphGoal g.mask) (p.map swapRows).reverse = true)
    (blocks : ∀ k ≤ g.top, chartBlock ((richNode (W := W)) g t dom perms k) 0 (t.count k) = true) :
    ∀ k ≤ g.top, ∀ i < t.count k, Impossible true (graphGoal g.mask) k ((wordsAt (W := W)) g t k i).toFinset := by
  intro k
  induction k with
  | zero =>
    intro h i hi
    exact (richNode_sound (W := W)) pairs valid autos (by omega) (chartBlock_at (blocks 0 h) i (by omega) (by simpa using hi))
  | succ k ih =>
    intro h i hi
    exact (richNode_sound (W := W)) pairs valid autos (fun _ => ih (by omega)) (chartBlock_at (blocks _ h) i (by omega) (by simpa using hi))


theorem richRoot {W : Nat} {g t dom perms}
    (pairs : (properPairs (W := W)) (graphGoal g.mask) ((asRow (W := W)) g.pos) ((asRow (W := W)) g.neg))
    (valid : RichValid g.mask dom)
    (autos : ∀ p ∈ perms, autoOK (graphGoal g.mask) (p.map swapRows).reverse = true)
    (blocks : ∀ k ≤ g.top, chartBlock ((richNode (W := W)) g t dom perms k) 0 (t.count k) = true)
    (existsRoot : 0 < t.count g.top)
    (root : (wordsAt (W := W)) g t g.top 0 = vars g.mask) :
    Impossible true (graphGoal g.mask) g.top (vars g.mask).toFinset := by
  rw [←root]
  exact (richAll (W := W)) pairs valid autos blocks _ (Nat.le_refl _) 0 existsRoot


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

def primCheck {W : Nat} (g : (CompactGrid W)) (pools : List BoundPool) (links : Nat → List (List Sig)) (t : Nat) : Bool :=
  let allW := (rawDecor (W := W)) 127 g.pos g.neg
  let ws := (rawDecor (W := W)) g.mask g.pos g.neg
  let a := allW.getD (t/9%9) (defaultDecor (W := W))
  let b := allW.getD (t%9) (defaultDecor (W := W))
  let d := t/81
  (ws.contains a && ws.contains b && (a.1 != b.1) && properB a.1 && properB b.1 && allowedB true d &&
    properB (bin d a.1 b.1) && plainWord (bin d a.1 b.1) && !((vars g.mask).contains (bin d a.1 b.1)) &&
    (typeWord t == bin d a.1 b.1)) &&
    (testPair (W := W)) (g.top,ws.length,ws,(preCov (W := W)) true ws,pools,links) a b d

theorem primOK {W : Nat} {g : (CompactGrid W)} {pools links t hints}
    (pairs : (properPairs (W := W)) (graphGoal g.mask) ((asRow (W := W)) g.pos) ((asRow (W := W)) g.neg))
    (valid : ∀ p ∈ pools, ValidPool true (vars g.mask) (graphGoal g.mask) p)
    (lk : ∀ tag xs, xs ∈ links tag → Impossible true (graphGoal g.mask) (g.top-1) xs.toFinset)
    (raw : ((rawDecor (W := W)) g.mask g.pos g.neg).map Prod.fst = vars g.mask)
    (ess : essOK g.mask hints = true) (nodup : (vars g.mask).Nodup)
    (base : Impossible true (graphGoal g.mask) (g.top-1) (vars g.mask).toFinset)
    (tp : 0 < g.top) (ok : (primCheck (W := W)) g pools links t = true) :
    Lower true (typeWord t :: vars g.mask) (graphGoal g.mask) g.top := by
  simp only [(primCheck (W := W)),Bool.and_eq_true,List.contains_eq_mem,decide_eq_true_eq,bne_iff_ne,beq_iff_eq,Bool.not_eq_true'] at ok
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨am,bm⟩,diff⟩,pa⟩,pb⟩,allow⟩,pg⟩,pl⟩,new⟩,repr⟩,check⟩ := ok
  rw [repr]
  exact (augmentedPairLower (W := W)) pairs valid lk raw ess nodup base am bm diff
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

end PEqualNP.Outside.L_meta_10760
