import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_17271_aux.Pin

namespace Bound
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
def graph : Sig := 0xffffffffffffffe8ffffffffffffeae8ffffffffffeaffe8ffeaffe8eaeaeae8ffffffffffffffe8ffffffffffffeae8ffffffffffeaffe8ffeaffe8eaeaeae8
def sample (r : Row) (j : Fin 9) := bit r (inputs.getD j.val zero)
def edge (x : Fin 9 → Bool) : Bool :=
  (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 3 && x 5) || (x 3 && x 6) || (x 4 && x 7) || (x 5 && x 6) || (x 5 && x 7)
theorem edge_table : ∀ r : Row, bit r graph = edge (sample r) := by decide +kernel
theorem graph_proper : proper graph := by unfold proper; decide +kernel
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
  (x 0 &&& x 1) ||| (x 0 &&& x 2) ||| (x 0 &&& x 3) ||| (x 0 &&& x 4) ||| (x 1 &&& x 2) ||| (x 3 &&& x 5) ||| (x 3 &&& x 6) ||| (x 4 &&& x 7) ||| (x 5 &&& x 6) ||| (x 5 &&& x 7)
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

def liftGoal (m : Nat) (v : Nat → Bits) : Bits :=
  let x := fun j => if m.testBit j then v j else 0
  (x 0 &&& x 1) ||| (x 0 &&& x 2) ||| (x 0 &&& x 3) ||| (x 0 &&& x 4) ||| (x 1 &&& x 2) ||| (x 3 &&& x 5) ||| (x 3 &&& x 6) ||| (x 4 &&& x 7) ||| (x 5 &&& x 6) ||| (x 5 &&& x 7)
theorem bit_vertex (m : Nat) (v : Nat → Bits) (i : Fin 152) (j : Fin 9) :
    bit (asRow v i) (vertex m j.val) =
    ((if m.testBit j.val then v j.val else 0) : Bits).getLsbD i.val := by
  by_cases hh : m.testBit j.val = true
  · simpa [vertex,hh] using asRow_bit v i j
  · simp [vertex,hh,bit_zero]
theorem bit_liftGoal (m : Nat) (v : Nat → Bits) (i : Fin 152) :
    bit (asRow v i) (graphGoal m) = (liftGoal m v).getLsbD i.val := by
  have pos (j : Nat) (hj : j<9) : (vertex m j).getLsbD (asRow v i).val = ((if m.testBit j then v j else 0) : Bits).getLsbD i.val := bit_vertex m v i ⟨j,hj⟩
  simp only [bit,graphGoal,liftGoal,BitVec.getLsbD_and,BitVec.getLsbD_or]
  simp only [pos 0 (by decide),pos 1 (by decide),pos 2 (by decide),pos 3 (by decide),pos 4 (by decide),pos 5 (by decide),pos 6 (by decide),pos 7 (by decide)]
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

def lookupShort (nb slots sw vw iw pw : Nat) (data : Nat → Nat) (h : Nat) : Option (Nat × Nat) :=
  let a := h % nb
  let sh := packedAt data (a*sw) sw
  let row := (h/nb+sh) % slots
  let word := packedAt data (nb*sw+row*vw) vw
  if (word >>> (iw+pw)) == h/(nb*slots) % 4 then
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
theorem chart_bit (m : Nat) (v : Nat → Bits) (i : Fin 152) :
    bit (asRow v i) (chartGoal m) = (chartSamples m v).getLsbD i.val := by
  exact bit_liftGoal m v i
theorem chart_pairs {m : Nat} {p q : Nat → Bits}
    (hp : chartSamples m p = BitVec.allOnes 152) (hq : chartSamples m q = 0) :
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

def prefixWidth (d : Nat) := 10*(d-1)
def denseRowWidth (d flags : Nat) := flags % 16 + (if d=0 then 0 else 10) + flags/16
def denseRowStart (d raw dict : Nat) :=
  (dict % 65536)*prefixWidth d + (dict/65536)*(raw+d)

def forestRecord (tab : Packing) (raw i : Nat) : Nat :=
  let (_,d,_,dict,flags,_,marker,word) := tab
  let width := 10*d+raw+d
  if marker<1024 then packedAt word (i*width) width else
    let off := denseRowStart d raw dict+i*denseRowWidth d flags
    let pre := packedAt word off (flags % 16)
    let lastBits := if d=0 then 0 else 10
    let last := packedAt word (off+flags % 16) lastBits
    let mask := packedAt word (off+flags % 16+lastBits) (flags/16)
    let base := (dict % 65536)*prefixWidth d
    packedAt word (pre*prefixWidth d) (prefixWidth d) |||
      (last <<< prefixWidth d) ||| (packedAt word (base+mask*(raw+d)) (raw+d) <<< (10*d))

def storedDepth (_g : Forest) (depth : Nat) := depth
def readNode (g : Forest) (k i : Nat) : Nat × List Decor × List Decor :=
  let raw := wiresOf g
  let (_,depth,_,_,_,_,_,data) := g.levels k
  let len := 10*storedDepth g depth
  let width := len+raw.length+depth
  let recp := forestRecord (g.levels k) raw.length i
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

def forceDatum {α : Type} : Nat → (Nat → α) → α
  | 0, next => next 0
  | n+1, next => next (n+1)

def readSortedHints (data : Nat → Nat) (dict cw d gapBits : Nat) :
    Nat → Nat → Nat → List (Nat × Nat)
  | 0,_,_ => []
  | left+1,st,first =>
    forceDatum st fun pos => forceDatum first fun base =>
    forceDatum (packedAt data pos 32) fun head =>
    forceDatum (Nat.log2 (head ^^^ (head+1))) fun ones =>
    forceDatum (base+(ones <<< gapBits)+packedAt data (pos+ones+1) gapBits) fun key =>
    forceDatum (packedAt data (dict+key*(cw+d)) (cw+d)) fun pair =>
      (pair &&& ((1 <<< cw)-1),pair >>> cw) ::
        readSortedHints data dict cw d gapBits left (pos+ones+1+gapBits) (key+1)

def promoteHints {α : Type} (a b : Nat) (xs : List α) : List α :=
  let rec collect : List α → Nat → List α → List α → List α → List α
    | [],_,first,second,other => first ++ second ++ other.reverse
    | x::tail,i,first,second,other =>
      if i=a then collect tail (i+1) [x] second other
      else if i=b then collect tail (i+1) first [x] other
      else collect tail (i+1) first second (x::other)
  collect xs 0 [] [] []

def forestHints (tab : Packing) (raw i : Nat) : List (Nat × Nat) :=
  let (num,d,cw,dict,flags,ow,marker,data) := tab
  if marker<1024 then
    let start := num*(10*d+raw+d)
    let pos := start+num*ow+packedAt data (start+i*ow) ow
    getPairs data cw d (packedAt data pos 6) (pos+6+marker)
  else
    let off := denseRowStart d raw dict + num*denseRowWidth d flags
    let pairs := off+num*ow
    let priority := decide (4096≤marker)
    let pos := pairs+(marker-(if priority then 4096 else 1024))*(cw+d)+packedAt data (off+i*ow) ow
    let n := packedAt data pos 5
    let gap := packedAt data (pos+5) 3
    if !priority || decide (n≤1) then readSortedHints data pairs cw d gap n (pos+8) 0 else
      let width := (n-1).log2+1
      let a := packedAt data (pos+8) width
      let b := if n=2 then 1-a else packedAt data (pos+8+width) width
      let extra := if n=2 then width else 2*width
      let xs := readSortedHints data pairs cw d gap n (pos+8+extra) 0
      promoteHints a b xs

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
  let rules := (forestHints (g.levels k) raw.length i).filterMap (fun (a,b) => buildRule g ops depth bank a b)
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
  (chartSamples g.mask (fun j => (g.samples j).1) == BitVec.allOnes 152) &&
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

def Known (u : Bool) (entries : List (Nat × Nat)) := ∀ e ∈ entries, Lower u (varsX e.1) (graphGoal e.1) e.2
def extendKnown (old : List (Nat × Nat)) (L : Nat) (carries : List (Nat × List Nat)) :=
  carries.map (fun v => (v.1,L)) ++ old
theorem extend_ok {u old L m carries} (previous : Known u old)
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
def lanePlace (v : Nat) (upper : Nat) := 2^153*upper+v
def combineLanes {α : Type} (f : α → Bits) : List α → Nat
  | [] => 0
  | x::xs => lanePlace (f x).toNat (combineLanes f xs)
def units : Nat → Nat
  | 0 => 0
  | n+1 => lanePlace 1 (units n)
theorem laneSmall (x : Bits) : x.toNat < 2^153 :=
  lt_trans x.isLt (by decide +kernel)
theorem place_and (a b : Bits) (u v : Nat) :
    lanePlace a.toNat u &&& lanePlace b.toNat v = lanePlace (a &&& b).toNat (u &&& v) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [lanePlace,Nat.testBit_and,Nat.testBit_two_pow_mul_add _ (laneSmall _)]
  by_cases h : i<153 <;> simp only [h,ite_true,ite_false,BitVec.toNat_and,Nat.testBit_and]
theorem place_or (a b : Bits) (u v : Nat) :
    lanePlace a.toNat u ||| lanePlace b.toNat v = lanePlace (a ||| b).toNat (u ||| v) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [lanePlace,Nat.testBit_or,Nat.testBit_two_pow_mul_add _ (laneSmall _)]
  by_cases h : i<153 <;> simp only [h,ite_true,ite_false,BitVec.toNat_or,Nat.testBit_or]
theorem place_xor (a b : Bits) (u v : Nat) :
    lanePlace a.toNat u ^^^ lanePlace b.toNat v = lanePlace (a ^^^ b).toNat (u ^^^ v) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [lanePlace,Nat.testBit_xor,Nat.testBit_two_pow_mul_add _ (laneSmall _)]
  by_cases h : i<153 <;> simp only [h,ite_true,ite_false,BitVec.toNat_xor,Nat.testBit_xor]
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
def fullMarks (r packed : Nat) := ((packed+r) >>> 152) &&& r
theorem unit_bit (n i : Nat) (hi : i<n) : (units n).testBit (153*i) = true := by
  induction n generalizing i with
  | zero => omega
  | succ n ih =>
    rw [units,lanePlace,Nat.testBit_two_pow_mul_add _ (by decide +kernel : 1 < 2^153)]
    cases i with
    | zero => simp
    | succ i =>
      have di : 153*(i+1)-153=153*i := by omega
      have ge : ¬153*(i+1)<153 := by omega
      simp only [ge,ite_false,di]
      exact ih _ (by omega)
set_option maxRecDepth 8192 in
theorem guardBit (a : Bits) : (a.toNat+1).testBit 152 = (a==BitVec.allOnes 152) := by
  by_cases h : a=BitVec.allOnes 152
  · subst a
    decide +kernel
  · have lim := a.isLt
    have ne : a.toNat ≠ 2^152-1 := by
      intro eq
      apply h
      apply BitVec.eq_of_toNat_eq
      simpa only [BitVec.toNat_allOnes] using eq
    have lt : a.toNat+1<2^152 := by omega
    rw [Nat.testBit_eq_false_of_lt lt]
    exact (beq_eq_false_iff_ne.mpr h).symm

set_option maxRecDepth 8192 in
theorem mark_at {α} (f : α → Bits) (xs : List α) (i : Nat) (hi : i<xs.length) :
    (fullMarks (units xs.length) (combineLanes f xs)).testBit (153*i) =
      (f xs[i]==BitVec.allOnes 152) := by
  simp only [fullMarks,Nat.testBit_and,Nat.testBit_shiftRight,unit_bit _ _ hi,Bool.and_true]
  induction xs generalizing i with
  | nil => simp at hi
  | cons a xs ih =>
    simp only [combineLanes,List.length_cons,units,lanePlace]
    have sum (u v x : Nat) : 2^153*u+x+(2^153*v+1)=2^153*(u+v)+(x+1) := by omega
    rw [sum,Nat.testBit_two_pow_mul_add _ (show (f a).toNat+1<2^153 from by have := (f a).isLt; omega)]
    have hi' : i < xs.length+1 := hi
    cases i with
    | zero => simpa using guardBit (f a)
    | succ i =>
      have ge : ¬153*(i+1)+152<153 := by omega
      have di : 153*(i+1)+152-153=153*i+152 := by omega
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
    ((mask &&& 1 == 0) || f x) && onMarks f (mask >>> 153) xs
theorem marked_ok {α} (f : α → Bool) (mask : Nat) (xs : List α) (i : Nat) (hi : i<xs.length)
    (bitOn : mask.testBit (153*i)=true) (ok : onMarks f mask xs=true) : f xs[i]=true := by
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
      apply ih (mask:=mask >>> 153) (i:=i) (by simpa using hi) _ ok.2
      simpa only [Nat.testBit_shiftRight,Nat.mul_succ,Nat.add_comm] using bitOn

abbrev Batch := Nat × Nat × Nat × List PackedSig × PackedCov
def makeBatch (k n : Nat) (xs : List NodeContext) : Batch :=
  (k,n,units xs.length,(List.range n).map (fun i => packedSig (fun c => (contextWire c i).2) xs),
    packedCov (fun c => c.2.2.2.1.1) xs)
def laneWire (b : Batch) (i : Nat) := b.2.2.2.1.getD i (0,0)
theorem laneWire_at (k n) (xs) {i : Nat} (h : i<n) :
    laneWire (makeBatch k n xs) i = packedSig (fun c => (contextWire c i).2) xs := by
  simp [laneWire,makeBatch,List.getD_eq_getElem?_getD,List.getElem?_map,List.getElem?_range,h]

theorem masked_comp (d x : Sig) : masked d (neg x) = d ^^^ masked d x := by
  apply bit_ext
  intro r
  simp only [masked,neg,bit,BitVec.getLsbD_and,BitVec.getLsbD_not,BitVec.getLsbD_xor,r.isLt,decide_true,Bool.true_and]
  cases d.getLsbD r.val <;> cases x.getLsbD r.val <;> rfl
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
  force (forestRecord (g.levels k) (selected g.mask).length i) fun rec =>
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
      if len>k then true else if combField xs[q] (!u) ka kb op i j != BitVec.allOnes 152 then true
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
    by_cases hit : combField xs[q] (!u) ka kb op i j = BitVec.allOnes 152
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
  let rules := (forestHints (g.levels k) raw.length i).filterMap (fun (a,b) => buildRule g ops depth bank a b)
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
theorem pieces_all {α f xs d} (h : @listPieces α f xs d) : xs.all f=true := by
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

structure KWRooms (S : Finset Sig) (T : Sig) where
  owns : Sig → Row → Row → Prop
  total : ∀ p n, bit p T=true → bit n T=false → ∃ v, owns v p n
  valid : ∀ {v p n}, owns v p n → v∈S ∧ bit p v=true ∧ bit n v=false
  unique : ∀ {v w p n}, owns v p n → owns w p n → v=w
  rect : ∀ {v p n p' n'}, owns v p n' → owns v p' n → owns v p n

def kwLeaf (T : Sig) : KWRooms {T} T where
  owns v p n := v=T ∧ bit p T=true ∧ bit n T=false
  total p n hp hn := ⟨T,rfl,hp,hn⟩
  valid := by rintro v p n ⟨rfl,hp,hn⟩; exact ⟨by simp,hp,hn⟩
  unique := by rintro v w p n ⟨rfl,_,_⟩ ⟨eq,_,_⟩; exact eq.symm
  rect := by rintro v p n p' n' ⟨e,hp,_⟩ ⟨_,_,hn⟩; exact ⟨e,hp,hn⟩

def kwFork {U : Finset Sig} {T a b : Sig} {d : Nat} (d01 : d=0 ∨ d=1)
    (ha : a∉U) (hb : b∉U) (hz : bin d a b∉U)
    (H : KWRooms (insert (bin d a b) U) T) : KWRooms (insert a (insert b U)) T := by
  let z := bin d a b
  let sel := fun p n : Row => if d=0 then (if bit n a then b else a)
    else (if bit p a then a else b)
  have pick (p n) : sel p n=a ∨ sel p n=b := by
    dsimp only [sel]; split <;> split <;> simp
  have outside (p n) : sel p n ∉ U := by
    rcases pick p n with eq | eq
    · simpa only [eq] using ha
    · simpa only [eq] using hb
  have separates (p n) (hp : bit p z=true) (hn : bit n z=false) :
      bit p (sel p n) = true ∧ bit n (sel p n) = false := by
    have b0 (r : Row) : bit r (bin 0 a b) = (bit r a && bit r b) := by simp [bin,bit]
    have b1 (r : Row) : bit r (bin 1 a b) = (bit r a || bit r b) := by simp [bin,bit]
    rcases d01 with e | e <;> cases pA : bit p a <;> cases nA : bit n a <;>
      simp_all [sel,z]
  refine { owns := fun v p n => (v∈U ∧ H.owns v p n) ∨ (v=sel p n ∧ H.owns z p n)
           total := ?_
           valid := ?_
           unique := ?_
           rect := ?_ }
  · intro p n hp hn
    obtain ⟨v,hv⟩ := H.total p n hp hn
    rcases Finset.mem_insert.mp (H.valid hv).1 with eq | mem
    · have vz : v=z := eq
      refine ⟨sel p n,Or.inr ⟨rfl,?_⟩⟩
      rw [←vz]
      exact hv
    · exact ⟨v,Or.inl ⟨mem,hv⟩⟩
  · intro v p n h
    rcases h with ⟨mem,hv⟩ | ⟨e,hv⟩
    · exact ⟨Finset.mem_insert_of_mem (Finset.mem_insert_of_mem mem),(H.valid hv).2⟩
    · subst v
      have inS : sel p n ∈ insert a (insert b U) := by
        rcases pick p n with eq | eq <;> simp [eq]
      exact ⟨inS,separates p n (H.valid hv).2.1 (H.valid hv).2.2⟩
  · intro v w p n h1 h2
    rcases h1 with ⟨vU,hv⟩ | ⟨ve,hv⟩ <;> rcases h2 with ⟨wU,hw⟩ | ⟨we,hw⟩
    · exact H.unique hv hw
    · apply False.elim
      apply hz
      change z∈U
      rw [←H.unique hv hw]
      exact vU
    · apply False.elim
      apply hz
      change z∈U
      rw [←H.unique hw hv]
      exact wU
    · exact ve.trans we.symm
  · intro v p n p' n' h1 h2
    rcases h1 with ⟨vU,hv⟩ | ⟨ve,hv⟩ <;> rcases h2 with ⟨wU,hw⟩ | ⟨we,hw⟩
    · exact Or.inl ⟨vU,H.rect hv hw⟩
    · exact False.elim (outside p' n (we ▸ vU))
    · exact False.elim (outside p n' (ve ▸ wU))
    · refine Or.inr ⟨?_,H.rect hv hw⟩
      by_cases h : d=0
      · simpa only [sel,h,ite_true] using we
      · simpa only [sel,h,ite_false] using ve

theorem kwWidth {u T k S} (h : Live u T k S) : S.card ≤ k+1 := by
  induction h using Live.ind with
  | stop hp => simp
  | @binary k U a b d hd ha hb hab hf tail ih =>
    have hu : bin d a b ∉ U := fun hm => hf (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hm))
    rw [Finset.card_insert_of_notMem hu] at ih
    have h1 := Finset.card_insert_le (a:=a) (insert b U)
    have h2 := Finset.card_insert_le (a:=b) U
    omega

theorem kwTight {T k S} (run : Live false T k S) (tight : S.card=k+1) :
    Nonempty (KWRooms S T) := by
  induction k generalizing S with
  | zero =>
    obtain ⟨rfl,_⟩ := run
    exact ⟨kwLeaf T⟩
  | succ k ih =>
    obtain ⟨U,a,b,d,hd,rfl,_,_,hab,hfresh,tail⟩ := run
    have fresh : bin d a b∉U := fun h => hfresh (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem h))
    have li := kwWidth tail
    rw [Finset.card_insert_of_notMem fresh] at li
    have le1 := Finset.card_insert_le (a:=a) (insert b U)
    have le2 := Finset.card_insert_le (a:=b) U
    have ha : a∉U := by
      intro h
      rw [Finset.insert_eq_of_mem (Finset.mem_insert_of_mem h : a∈insert b U)] at tight
      omega
    have hb : b∉U := by
      intro h
      rw [Finset.insert_eq_of_mem h] at tight le1
      omega
    have eq : (insert (bin d a b) U).card=k+1 := by
      rw [Finset.card_insert_of_notMem fresh]
      omega
    obtain ⟨H⟩ := ih tail eq
    have d01 : d=0 ∨ d=1 := by rcases hd with h | ⟨h,_⟩ <;> simp_all <;> omega
    exact ⟨kwFork d01 ha hb fresh H⟩

def onlyWire (S : Finset Sig) (T v : Sig) (p n : Row) :=
  bit p T=true ∧ bit n T=false ∧ ∀ w∈S, bit p w=true → bit n w=false → w=v

theorem kwOwn {S T v p n} (H : KWRooms S T) (one : onlyWire S T v p n) : H.owns v p n := by
  obtain ⟨w,hw⟩ := H.total p n one.1 one.2.1
  have eq := one.2.2 w (H.valid hw).1 (H.valid hw).2.1 (H.valid hw).2.2
  exact eq ▸ hw

theorem kwCross {S T k a b p n pa pb na nb} (size : k+1=S.card) (different : a≠b)
    (A : onlyWire S T a p na) (B : onlyWire S T b p nb)
    (C : onlyWire S T a pa n) (D : onlyWire S T b pb n) : Impossible false T k S := by
  intro j hj run
  have lb := kwWidth run
  have tight : S.card=j+1 := by omega
  obtain ⟨H⟩ := kwTight run tight
  exact different (H.unique (H.rect (kwOwn H A) (kwOwn H C)) (H.rect (kwOwn H B) (kwOwn H D)))
def kwWireB (ws : List Sig) (T v : Sig) (p n : Row) : Bool :=
  bit p T && !bit n T && ws.all (fun w => !bit p w || bit n w || w==v)
theorem kwWireB_sound {ws T v p n} (h : kwWireB ws T v p n=true) :
    onlyWire ws.toFinset T v p n := by
  simp only [kwWireB,Bool.and_eq_true,Bool.not_eq_true',List.all_eq_true] at h
  refine ⟨h.1.1,h.1.2,?_⟩
  intro w hw hp hn
  simpa only [hp,hn,Bool.not_true,Bool.false_or,beq_iff_eq] using
    h.2 w (List.mem_toFinset.mp hw)

def kwProbe (xs q : Nat) : Row := Fin.ofNat 512 ((xs >>> (9*q)) &&& 511)
def kwWord (pos neg : Nat) (T : Sig) (ws : List Sig) (k value : Nat) : Bool :=
  let field := fun i => (value >>> (4*i)) &&& 15
  let a := ws.getD (field 0) zero
  let b := ws.getD (field 1) zero
  let p := kwProbe pos (field 2)
  let n := kwProbe neg (field 3)
  decide (k+1=ws.toFinset.card) && decide (a≠b) &&
    kwWireB ws T a p (kwProbe neg (field 4)) && kwWireB ws T b p (kwProbe neg (field 5)) &&
    kwWireB ws T a (kwProbe pos (field 6)) n && kwWireB ws T b (kwProbe pos (field 7)) n
theorem kwWord_sound {pos neg T ws k v} (h : kwWord pos neg T ws k v=true) : Impossible false T k ws.toFinset := by
  simp only [kwWord,Bool.and_eq_true,decide_eq_true_eq] at h
  exact kwCross h.1.1.1.1.1 h.1.1.1.1.2 (kwWireB_sound h.1.1.1.2)
    (kwWireB_sound h.1.1.2) (kwWireB_sound h.1.2) (kwWireB_sound h.2)

def CutRow (g : Forest) (k start n : Nat) : Prop :=
  ∀ j, start≤j → j<start+n → nodeVerified g k j=true ∨ Impossible g.mode (targetOf g) k (stateSet g k j).toFinset
theorem mixedEmpty (g : Forest) (k a : Nat) : CutRow g k a 0 := by
  intro j lo hi
  omega
theorem checkedRow {g k a n} (h : block g k a n=true) : CutRow g k a n :=
  fun j lo hi => Or.inl (block_at h j lo hi)
theorem joinRow {g k a x y} (first : CutRow g k a x) (last : CutRow g k (a+x) y) :
    CutRow g k a (x+y) := by
  intro j lo hi
  by_cases e : j<a+x
  · exact first j lo e
  · exact last j (by omega) (by omega)
def kwTest (pos neg : Nat) (g : Forest) (k a n : Nat) (data : Nat → Nat) :=
  (List.range n).all (fun j => kwWord pos neg (targetOf g) (stateSet g k (a+j)) k (packedAt data (32*j) 32))
theorem mixedCut {pos neg g k a n data} (mode : g.mode=false) (h : kwTest pos neg g k a n data=true) :
    CutRow g k a n := by
  intro j lo hi
  right
  rw [mode]
  have hh := List.all_eq_true.mp h (j-a) (List.mem_range.mpr (by omega))
  have sum : a+(j-a)=j := by omega
  change kwWord pos neg _ (stateSet g k (a+(j-a))) k _=true at hh
  rw [sum] at hh
  exact kwWord_sound hh

def mixedTables (g : Forest) (top : Nat) := ∀ k ≤ top, CutRow g k 0 (g.levels k).1
theorem mixedForest (g : Forest) (top : Nat) (prior : Nat → Nat)
    (lower : ∀ q, Lower g.mode (varsX q) (graphGoal q) (prior q))
    (geometry : graphValid g prior=true) (rows : mixedTables g top) :
    ∀ k ≤ top, ∀ i < (g.levels k).1, Impossible g.mode (targetOf g) k (stateSet g k i).toFinset := by
  simp only [graphValid,Bool.and_eq_true,List.all_eq_true,beq_iff_eq] at geometry
  intro k
  induction k with
  | zero =>
    intro hk i hi
    rcases rows 0 hk i (by omega) (by omega) with checked | done
    · exact nodeVerified_sound g 0 i (chart_pairs geometry.1.1.1 geometry.1.1.2)
        (fun x hx => col_sound _ prior lower (geometry.1.2 x hx)) geometry.2 (by omega) checked
    · exact done
  | succ k ih =>
    intro hk i hi
    rcases rows _ hk i (by omega) (by omega) with checked | done
    · exact nodeVerified_sound g _ i (chart_pairs geometry.1.1.1 geometry.1.1.2)
        (fun x hx => col_sound _ prior lower (geometry.1.2 x hx)) geometry.2
        (fun _ => by simpa using ih (by omega)) checked
    · exact done
theorem mixedRoot {g top prior k i ws} (lower : ∀ q, Lower g.mode (varsX q) (graphGoal q) (prior q))
    (geom : graphValid g prior=true) (blocks : mixedTables g top) (le : k≤top)
    (idx : indexedRoot g k i ws=true) : Impossible g.mode (targetOf g) k ws.toFinset := by
  simp only [indexedRoot,Bool.and_eq_true,decide_eq_true_eq] at idx
  rw [←sameWords_sound idx.2]
  exact mixedForest g top prior lower geom blocks _ le i idx.1

def eightInputs : List Sig := vars 255
def sampleEight (r : Row) (i : Fin 8) : Bool := bit r (eightInputs.getD i.val zero)
def eightEdge (x : Fin 8 → Bool) := (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 3 && x 5) || (x 3 && x 6) || (x 4 && x 7) || (x 5 && x 6) || (x 5 && x 7)

theorem eightTable : ∀ r : Row, bit r graph = eightEdge (sampleEight r) := by decide +kernel
theorem eightList : List.ofFn (fun i : Fin 8 => eightInputs.getD i.val zero) = eightInputs := rfl
theorem eightSampled (r : Row) : List.ofFn (sampleEight r) = eightInputs.map (bit r) := by
  rw [← eightList, List.map_ofFn]
  rfl

theorem eightEval (C : Circuit) (h : PEqualNP.MetaComplexity.FanInTwo C)
    (i : Nat) (r : Row) : bit r ((execute C.gates eightInputs).getD i zero) =
      (C.wires (List.ofFn (sampleEight r))).getD i false := by
  rw [← b_read,execute_bits _ _ _ (fun g hg => (h g hg).1),eightSampled]
  rfl
def neighbor8453 (i : Fin 8) : Nat := [1,0,0,0,0,3,3,4].getD i.val 0
def absentRow8453 (i : Fin 8) : Row := Fin.ofNat 512 (1 <<< neighbor8453 i)
def presentRow8453 (i : Fin 8) : Row := Fin.ofNat 512 ((1 <<< i.val) ||| (1 <<< neighbor8453 i))

set_option maxHeartbeats 1000000 in
theorem requiredInputs :
    (∀ i : Fin 8, bit (absentRow8453 i) graph ≠ bit (presentRow8453 i) graph) ∧
    (∀ i j : Fin 8, i ≠ j →
      bit (absentRow8453 i) (eightInputs.getD j.val zero) =
      bit (presentRow8453 i) (eightInputs.getD j.val zero)) := by decide +kernel

theorem twoRoots (C : Circuit) (legal : PEqualNP.MetaComplexity.FanInTwo C)
    (computes : PEqualNP.MetaComplexity.circuitFun 8 C = eightEdge) (small : C.size ≤ 13) :
    ∃ (u : Bool) (k : Nat), k ≤ (if u then 12 else 13) ∧ Live u graph k eightInputs.toFinset := by
  have goalEq : (execute C.gates eightInputs).getD C.output zero = graph := by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    let r : Row := ⟨j,hj⟩
    exact (eightEval C legal C.output r).trans ((congrFun computes (sampleEight r)).trans (eightTable r).symm)
  have len : C.gates.length ≤ 13 := small
  have mode : ∃ u : Bool, (u=false → ∀ g ∈ C.gates, isNot g=false) ∧ C.gates.countP (fun g => !isNot g) ≤ (if u then 12 else 13) := by
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

  have out := get_rep (u:=u) (execute C.gates eightInputs) C.output
  rw [goalEq] at out
  unfold Repr at out
  have pg : bit 0 graph = false := by decide +kernel
  rw [nrm_id pg] at out
  obtain ⟨k,S,hk,run,sub⟩ := extract C.gates eightInputs legal mono graph_proper
    (out.resolve_right (fun h => h graph_proper))
  have ns : eightInputs.all plainWord = true := by decide +kernel
  rw [nrm_map ns] at sub
  have idx (a : Sig) (ha : a ∈ eightInputs) : ∃ i : Fin 8, eightInputs.getD i.val zero = a := by
    rw [←eightList] at ha
    exact List.mem_ofFn.mp ha
  have eq : S = eightInputs.toFinset := by
    ext a
    constructor
    · exact fun h => List.mem_toFinset.mpr (sub a h)
    · intro ha
      obtain ⟨i,rfl⟩ := idx a (List.mem_toFinset.mp ha)
      apply raw_required run eightInputs (eightInputs.getD i.val zero) sub (absentRow8453 i) (presentRow8453 i)
        (requiredInputs.1 i)
      intro v hv hn
      obtain ⟨j,rfl⟩ := idx v hv
      apply requiredInputs.2 i j
      rintro rfl
      exact hn rfl
  exact ⟨u,k,hk.trans count,eq ▸ run⟩

theorem directSplit
    (m : ∀ k, k ≤ 13 → ¬Live false graph k eightInputs.toFinset)
    (s : ∀ k, k ≤ 12 → ¬Live true graph k eightInputs.toFinset) :
    ¬ PEqualNP.MetaComplexity.HasCircuitSize 8 eightEdge 13 := by
  rintro ⟨C,legal,small,computes⟩
  obtain ⟨mode,k,hk,run⟩ := twoRoots C legal (funext computes) small
  cases mode
  · exact m k hk run
  · exact s k hk run
def g7Y : Array (Bits × Bits) := #[(0x3ff63ff63ff63ff63ff63ff63ff63ff63ff63f,0x49204920492049204920492049204920492049),(0xc7fbc7fbc7fbc7fbc7fbc7fbc7fbc7fbc7fbc7,0x92409240924092409240924092409240924092),(0xf8fdf8fdf8fdf8fdf8fdf8fdf8fdf8fdf8fdf8,0x24812481248124812481248124812481248124),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def g7C : List ColumnInfo := []
def g7A : List (List Nat) := [[],[33],[16],[16,32],[32,16],[32]]
def g7D3 (j : Nat) : Nat := 0x7
def g7L : Nat → Packing
  | 3 => (1,0,1,0,0,0,0,g7D3)
  | _ => emptyPacking
def g7I (_ _ : Nat) : Option (Nat × Nat) := none
def g7 : Forest := ⟨7,3,fun i => g7Y[i]?.getD (0,0),g7C,g7A,g7L,g7I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g7P3_0 : block g7 3 0 1=true := by
  apply cellsBlock (ar:=3) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g7B3 : block g7 3 0 1=true := g7P3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g7T : checkedTables g7 3 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g7 0 0 0 = true)
  · exact (rfl : block g7 1 0 0 = true)
  · exact (rfl : block g7 2 0 0 = true)
  · exact g7B3
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g7G : graphValid g7 (boundsBefore []) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low7 : Lower true (varsX 7) (graphGoal 7) 4 := lower_forest (g:=g7) (i:=0) (hints:=1) (before_sound [] baseKnown) g7G g7T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K7 := extendKnown [] 4 [(7,[]),(104,[48,81,98,65,66])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V7 : Known true K7 := extend_ok (m:=7) baseKnown low7 (by decide +kernel)
def g15Y : Array (Bits × Bits) := #[(0xfd587fff83fffff3fab0ffff07ffffe7f561ff,0x9241082080200001248210410040000249),(0x3baf81fffc0fc7fc775f03fff81f8ff8eebe07,0x818d249212411241031a492424822482063492),(0xc6b78e3ffff007ff8d6f1c7fffe00fff1ade38,0x16324924208a24802c6492484114490058c924),(0x64c703ffffff8000c98e07ffffff0001931c0,0x264f6db8430c070a4c9edb7086180e14993db6),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def g15C : List ColumnInfo := [(8,0,7,0,4)]
def g15A : List (List Nat) := [[],[33]]
def g15D4 (j : Nat) : Nat := 0x1f
def g15L : Nat → Packing
  | 4 => (1,0,1,0,0,0,0,g15D4)
  | _ => emptyPacking
def g15I (_ _ : Nat) : Option (Nat × Nat) := none
def g15 : Forest := ⟨15,4,fun i => g15Y[i]?.getD (0,0),g15C,g15A,g15L,g15I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g15P4_0 : block g15 4 0 1=true := by
  apply cellsBlock (ar:=4) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g15B4 : block g15 4 0 1=true := g15P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g15T : checkedTables g15 4 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g15 0 0 0 = true)
  · exact (rfl : block g15 1 0 0 = true)
  · exact (rfl : block g15 2 0 0 = true)
  · exact (rfl : block g15 3 0 0 = true)
  · exact g15B4
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g15G : graphValid g15 (boundsBefore K7) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low15 : Lower true (varsX 15) (graphGoal 15) 5 := lower_forest (g:=g15) (i:=0) (hints:=1) (before_sound K7 V7) g15G g15T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K15 := extendKnown K7 5 [(15,[]),(23,[67]),(105,[48,81,98,65,66]),(232,[80,49,98,113,64,65])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V15 : Known true K15 := extend_ok (m:=15) V7 low15 (by decide +kernel)
def g43Y : Array (Bits × Bits) := #[(0xf6d63fff03f8fffff6d63fff03f8fffff6d63f,0x4549242881209100454924288120910045492),(0xfe3207fffc00fff8fe3207fffc00fff8fe3207,0x1a236d9412a452221a236d9412a452221a236d),(0x0,0x0),(0xbedf8ffffff03ff0bedf8ffffff03ff0bedf8,0x43a0491820c0604043a0491820c0604043a049),(0x0,0x0),(0x193dc0fffffffc00193dc0fffffffc00193dc0,0x981db6e0c3008384981db6e0c3008384981db6),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def g43C : List ColumnInfo := []
def g43A : List (List Nat) := [[],[48,81]]
def g43D3 (j : Nat) : Nat := 0xf
def g43L : Nat → Packing
  | 3 => (1,0,1,0,0,0,0,g43D3)
  | _ => emptyPacking
def g43I (_ _ : Nat) : Option (Nat × Nat) := none
def g43 : Forest := ⟨43,3,fun i => g43Y[i]?.getD (0,0),g43C,g43A,g43L,g43I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g43P3_0 : block g43 3 0 1=true := by
  apply cellsBlock (ar:=4) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g43B3 : block g43 3 0 1=true := g43P3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g43T : checkedTables g43 3 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g43 0 0 0 = true)
  · exact (rfl : block g43 1 0 0 = true)
  · exact (rfl : block g43 2 0 0 = true)
  · exact g43B3
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g43G : graphValid g43 (boundsBefore K15) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low43 : Lower true (varsX 43) (graphGoal 43) 4 := lower_forest (g:=g43) (i:=0) (hints:=3145729) (before_sound K15 V15) g43G g43T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K43 := extendKnown K15 4 [(43,[]),(45,[33]),(57,[65,33]),(75,[101]),(147,[67,117,101]),(153,[49,33,66,117,101]),(169,[48,16,33,82,66,116,100]),(177,[64,16,33,115,99]),(184,[80,49,32,113,65,66,98]),(240,[112,65,32,83,99,50])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V43 : Known true K43 := extend_ok (m:=43) V15 low43 (by decide +kernel)
def g31Y : Array (Bits × Bits) := #[(0xffffffffe003fffffffffff00ffffcad3b8fff,0x100000400800800800002000000000001249),(0x7ff803fffffc003ffc01fffff007ff73ec7007,0x21214924891129121094924242512233682492),(0x800003ffffffffc00001fffffff803dad57038,0x4a42924912224224a1292484848249c8954924),(0x3fffffffffffffe00000000007f1601c0,0x7384e38e1c438c38c231c708e8e4707f166db6),(0xfffffc00000000000000000000000322378e00,0x7c0703f01f83f03f03c1f80f0f07832237edb6),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def g31C : List ColumnInfo := [(8,0,23,0,5)]
def g31A : List (List Nat) := [[],[67],[33],[33,67]]
def g31D5 (j : Nat) : Nat := 0x3f
def g31L : Nat → Packing
  | 5 => (1,0,1,0,0,0,0,g31D5)
  | _ => emptyPacking
def g31I (_ _ : Nat) : Option (Nat × Nat) := none
def g31 : Forest := ⟨31,5,fun i => g31Y[i]?.getD (0,0),g31C,g31A,g31L,g31I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g31P5_0 : block g31 5 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g31B5 : block g31 5 0 1=true := g31P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g31T : checkedTables g31 5 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g31 0 0 0 = true)
  · exact (rfl : block g31 1 0 0 = true)
  · exact (rfl : block g31 2 0 0 = true)
  · exact (rfl : block g31 3 0 0 = true)
  · exact (rfl : block g31 4 0 0 = true)
  · exact g31B5
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g31G : graphValid g31 (boundsBefore K43) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low31 : Lower true (varsX 31) (graphGoal 31) 6 := lower_forest (g:=g31) (i:=0) (hints:=1) (before_sound K43 V43) g31G g31T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K31 := extendKnown K43 6 [(31,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V31 : Known true K31 := extend_ok (m:=31) V43 low31 (by decide +kernel)
def g47Y : Array (Bits × Bits) := #[(0xff007ffffffc01ffffffffc3ffd454a6007fff,0x2810080440884411040408802001426421084),(0xffff803ffffffe007fe1fffc3fe1ab440f801f,0x24124904889108922084890081e02b0094a529),(0xffffffc01fffffff8001ffffc03dd94a0f83e0,0x482412291122110445091200081dc049294a52),(0x1ffffffffffe0000004f27b9f07c00,0x70381c0e01c0201806001c1110452198318c63),(0x0,0x0),(0xffffffffe000000000000000033aa61bf00000,0x80c060301e03c1e07811e022233a8603ce739c),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def g47C : List ColumnInfo := [(0,32,7,8,5),(32,0,15,0,5),(2,0,45,0,4),(4,0,43,0,4),(8,32,7,0,4)]
def g47A : List (List Nat) := [[],[33]]
def g47D4 (j : Nat) : Nat := 0x5bd4910
def g47D5 (j : Nat) : Nat := 0x40880460e140fd21fe10fd10
def g47H5 (j : Nat) : Nat := 0x70
def g47D6 (j : Nat) : Nat := 0x16a09f
def g47H6 (j : Nat) : Nat := 0x3a0000f4000000388000000000001100000000000000000000000000000000000000000000
def g47L : Nat → Packing
  | 4 => (1,2,3,0,0,0,0,g47D4)
  | 5 => (3,1,3,0,0,5,0,g47D5)
  | 6 => (1,0,3,0,0,0,0,g47D6)
  | _ => emptyPacking
def g47I : Nat → Nat → Option (Nat × Nat)
  | 5 => lookupWord 1 2 0 4 0 0 g47H5
  | 6 => lookupWord 1 43 0 7 2 1 g47H6
  | _ => fun _ => none
def g47 : Forest := ⟨47,6,fun i => g47Y[i]?.getD (0,0),g47C,g47A,g47L,g47I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g47P4_0 : block g47 4 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g47B4 : block g47 4 0 1=true := g47P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g47P5_0 : block g47 5 0 3=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g47B5 : block g47 5 0 3=true := g47P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g47P6_0 : block g47 6 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g47B6 : block g47 6 0 1=true := g47P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g47T : checkedTables g47 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g47 0 0 0 = true)
  · exact (rfl : block g47 1 0 0 = true)
  · exact (rfl : block g47 2 0 0 = true)
  · exact (rfl : block g47 3 0 0 = true)
  · exact g47B4
  · exact g47B5
  · exact g47B6
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g47G : graphValid g47 (boundsBefore K31) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low47 : Lower true (varsX 47) (graphGoal 47) 7 := lower_forest (g:=g47) (i:=0) (hints:=3145729) (before_sound K31 V31) g47G g47T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K47 := extendKnown K31 7 [(47,[]),(79,[101]),(107,[48,81,98,66]),(109,[48,81,98,65,66]),(121,[48,81,98,65]),(151,[67,117,101]),(248,[80,49,98,113,64,33])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V47 : Known true K47 := extend_ok (m:=47) V31 low47 (by decide +kernel)
def g59Y : Array (Bits × Bits) := #[(0x1fff007ffffffffffffffffffffff31f73f1ff,0x40020100108084042020008080000004507492),(0xe000007fffffc001fff007ffc01ff2f236a007,0x9554564aa51529a94944d52912c942f2268b6d),(0x0,0x0),(0xffffff8007fffffe000007ffffe00df1ec1e38,0x198240cc02601300d81603204826951a40249),(0x7fffffffffff8000000013e8dc1c0,0x19e0b86f063831c18e09863c2713813a8d8b6d),(0xfffffffff80000000000000000000cea9e5e00,0x1e00c07007c03e01f00e07c0381c04aa1a5db6),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def g59C : List ColumnInfo := [(2,0,57,0,4)]
def g59A : List (List Nat) := [[],[65]]
def g59D4 (j : Nat) : Nat := 0x3f
def g59L : Nat → Packing
  | 4 => (1,0,1,0,0,0,0,g59D4)
  | _ => emptyPacking
def g59I (_ _ : Nat) : Option (Nat × Nat) := none
def g59 : Forest := ⟨59,4,fun i => g59Y[i]?.getD (0,0),g59C,g59A,g59L,g59I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g59P4_0 : block g59 4 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g59B4 : block g59 4 0 1=true := g59P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g59T : checkedTables g59 4 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g59 0 0 0 = true)
  · exact (rfl : block g59 1 0 0 = true)
  · exact (rfl : block g59 2 0 0 = true)
  · exact (rfl : block g59 3 0 0 = true)
  · exact g59B4
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g59G : graphValid g59 (boundsBefore K47) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low59 : Lower true (varsX 59) (graphGoal 59) 5 := lower_forest (g:=g59) (i:=0) (hints:=3145729) (before_sound K47 V47) g59G g59T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K59 := extendKnown K47 5 [(59,[]),(91,[101]),(155,[67,117,101]),(157,[33,67,117,101])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V59 : Known true K59 := extend_ok (m:=59) V47 low59 (by decide +kernel)
def g103Y : Array (Bits × Bits) := #[(0xfc00ffffffff003fffffffc3feea3a53000fff,0x8a220882222228882208888802201a13249249),(0xffff003fffffffc00ffffffc3ed0c5f603f03f,0x10449104444441124411110080d005c4492492),(0xffffffc00ffffffff003ffffc13eeca103ffc0,0x208822288888822088a22200090ee020924924),(0x0,0x0),(0x0,0x0),(0xffffffffffc0000012793dcfc0000,0xc0f03c0f00f00c0300c03c11112283d81c71c7),(0xfffffffff000000000000000039d530dfc0000,0x300c0300f00f03c0f03c022229d5005e38e38),(0x0,0x0),(0x0,0x0)]
def g103C : List ColumnInfo := [(0,32,7,64,5)]
def g103A : List (List Nat) := [[],[101],[33],[33,101],[16],[16,101],[16,32],[16,32,101],[32,16],[32,16,101],[32],[32,101]]
def g103D5 (j : Nat) : Nat := 0x3f
def g103L : Nat → Packing
  | 5 => (1,0,1,0,0,0,0,g103D5)
  | _ => emptyPacking
def g103I (_ _ : Nat) : Option (Nat × Nat) := none
def g103 : Forest := ⟨103,5,fun i => g103Y[i]?.getD (0,0),g103C,g103A,g103L,g103I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g103P5_0 : block g103 5 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g103B5 : block g103 5 0 1=true := g103P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g103T : checkedTables g103 5 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g103 0 0 0 = true)
  · exact (rfl : block g103 1 0 0 = true)
  · exact (rfl : block g103 2 0 0 = true)
  · exact (rfl : block g103 3 0 0 = true)
  · exact (rfl : block g103 4 0 0 = true)
  · exact g103B5
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g103G : graphValid g103 (boundsBefore K59) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low103 : Lower true (varsX 103) (graphGoal 103) 6 := lower_forest (g:=g103) (i:=0) (hints:=90177537) (before_sound K59 V59) g103G g103T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K103 := extendKnown K59 6 [(103,[]),(110,[48,81,98]),(167,[118])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V103 : Known true K103 := extend_ok (m:=103) V59 low103 (by decide +kernel)
def g171Y : Array (Bits × Bits) := #[(0xfffffffffff001ffe03fffffffffdb2e3300ff,0x2104208424214420408410910001030a235555),(0xff800ffffffffe00003fffff80ffd495b2000f,0x4a694929494a094a8b28a5222648d49590aaaa),(0x0,0x0),(0xfffff001ffffffffffc007ffff003eacc50ff0,0xc418c31818c11831230c604448c1c24c48888),(0x0,0x0),(0x1fffffffffffff800000027d3fcff00,0x700e01c00e00600c00010038081023d0303333),(0x0,0x0),(0xfffffffe000000000000000000019d530df000,0x80700e01f00f81f01c3e07c070e19c030dcccc),(0x0,0x0)]
def g171C : List ColumnInfo := []
def g171A : List (List Nat) := [[],[80,113]]
def g171D4 (j : Nat) : Nat := 0x1f
def g171L : Nat → Packing
  | 4 => (1,0,1,0,0,0,0,g171D4)
  | _ => emptyPacking
def g171I (_ _ : Nat) : Option (Nat × Nat) := none
def g171 : Forest := ⟨171,4,fun i => g171Y[i]?.getD (0,0),g171C,g171A,g171L,g171I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g171P4_0 : block g171 4 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g171B4 : block g171 4 0 1=true := g171P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g171T : checkedTables g171 4 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g171 0 0 0 = true)
  · exact (rfl : block g171 1 0 0 = true)
  · exact (rfl : block g171 2 0 0 = true)
  · exact (rfl : block g171 3 0 0 = true)
  · exact g171B4
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g171G : graphValid g171 (boundsBefore K103) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low171 : Lower true (varsX 171) (graphGoal 171) 5 := lower_forest (g:=g171) (i:=0) (hints:=1345323009) (before_sound K103 V103) g171G g171T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K171 := extendKnown K103 5 [(171,[]),(173,[33]),(179,[67,117]),(181,[33,67,117]),(217,[48,97,33,66,84]),(241,[64,16,33,115,99])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V171 : Known true K171 := extend_ok (m:=171) V103 low171 (by decide +kernel)
def g185Y : Array (Bits × Bits) := #[(0xff803ff0fffff007ffff0fffffe47a840003ff,0x21488422212425120902248802603284a5294a),(0x0,0x0),(0x0,0x0),(0xffffc000fffffff803fffffc3f8189fc007c1f,0xa0121440a414824521408108180895918c631),(0xffffffff007ffffffc000fffc07dd9120f83e0,0x4c1209804c09804060584120080dc9025294a5),(0x7ffffffffff000004f27e9f07c00,0x701c0e08700e0180806001c1104f20a06318c6),(0x0,0x0),(0xffffffffff80000000000000033aa61bff8000,0x8060300080700e0703808e02233006198c6318),(0x0,0x0)]
def g185C : List ColumnInfo := [(1,0,184,0,4),(8,0,177,0,4),(16,0,169,0,4),(32,0,153,0,4),(128,0,57,0,4)]
def g185A : List (List Nat) := [[],[67,117],[48,84],[48,80,64,116],[64,48,115,83],[64,115],[80,116],[80,115,67,64],[112,67,83,48],[112,83]]
def g185D4 (j : Nat) : Nat := 0x5dd4530
def g185D5 (j : Nat) : Nat := 0x41030fd30fd10
def g185H5 (j : Nat) : Nat := 0x1
def g185D6 (j : Nat) : Nat := 0x23440bf
def g185H6 (j : Nat) : Nat := 0x4b0086000000ee000027007100c20000c3c500000000300000fa
def g185L : Nat → Packing
  | 4 => (1,2,3,0,0,0,0,g185D4)
  | 5 => (2,1,3,0,0,3,0,g185D5)
  | 6 => (1,0,3,0,0,0,0,g185D6)
  | _ => emptyPacking
def g185I : Nat → Nat → Option (Nat × Nat)
  | 5 => lookupWord 1 2 0 4 0 0 g185H5
  | 6 => lookupWord 2 37 0 8 1 3 g185H6
  | _ => fun _ => none
def g185 : Forest := ⟨185,6,fun i => g185Y[i]?.getD (0,0),g185C,g185A,g185L,g185I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g185P4_0 : block g185 4 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g185B4 : block g185 4 0 1=true := g185P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g185P5_0 : block g185 5 0 2=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g185B5 : block g185 5 0 2=true := g185P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g185P6_0 : block g185 6 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g185B6 : block g185 6 0 1=true := g185P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g185T : checkedTables g185 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g185 0 0 0 = true)
  · exact (rfl : block g185 1 0 0 = true)
  · exact (rfl : block g185 2 0 0 = true)
  · exact (rfl : block g185 3 0 0 = true)
  · exact g185B4
  · exact g185B5
  · exact g185B6
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g185G : graphValid g185 (boundsBefore K171) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low185 : Lower true (varsX 185) (graphGoal 185) 7 := lower_forest (g:=g185) (i:=0) (hints:=1076887555) (before_sound K171 V171) g185G g185T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K185 := extendKnown K171 7 [(185,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V185 : Known true K185 := extend_ok (m:=185) V171 low185 (by decide +kernel)
def g233Y : Array (Bits × Bits) := #[(0x3ff01fffff8007fe03ff80ffe03ff501d70007,0xa2265294a94a9484aa492a944a944501d75b6d),(0x0,0x0),(0x0,0x0),(0xc0001ffffffff80003fffffffffff07f4d01ff,0x8408021021021081082002080003072002492),(0x0,0x0),(0xffffe007fffffffffc0000ffffc00fcbb2fe38,0x8000c00c00c010000c040100010c09809249),(0x7ffffffffffffff00000009b4fc0fc0,0x330b1b0630630621231048c6132601847c4924),(0xfffffff800000000000000000000675462f000,0x3c0c1c07c07c07c1c3e070f81c386354626db6),(0x0,0x0)]
def g233C : List ColumnInfo := [(1,0,232,0,5)]
def g233A : List (List Nat) := [[],[112,83]]
def g233D5 (j : Nat) : Nat := 0x3f
def g233L : Nat → Packing
  | 5 => (1,0,1,0,0,0,0,g233D5)
  | _ => emptyPacking
def g233I (_ _ : Nat) : Option (Nat × Nat) := none
def g233 : Forest := ⟨233,5,fun i => g233Y[i]?.getD (0,0),g233C,g233A,g233L,g233I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g233P5_0 : block g233 5 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g233B5 : block g233 5 0 1=true := g233P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g233T : checkedTables g233 5 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g233 0 0 0 = true)
  · exact (rfl : block g233 1 0 0 = true)
  · exact (rfl : block g233 2 0 0 = true)
  · exact (rfl : block g233 3 0 0 = true)
  · exact (rfl : block g233 4 0 0 = true)
  · exact g233B5
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g233G : graphValid g233 (boundsBefore K185) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low233 : Lower true (varsX 233) (graphGoal 233) 6 := lower_forest (g:=g233) (i:=0) (hints:=1395654659) (before_sound K185 V185) g233G g233T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K233 := extendKnown K185 6 [(233,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V233 : Known true K233 := extend_ok (m:=233) V185 low233 (by decide +kernel)
def g63Y : Array (Bits × Bits) := #[(0xffffffffe000fffffff9cda159007f400fffff,0x80000800400200000009802000002b08421084),(0xc001ffffffff0007ffe6511b26e99ac1f0001f,0x8949124844822511226411126c110d294a529),(0x1fffffffffff8001c905e7bee8401f003e0,0x11292249089044822490104e592e8425294a52),(0xfffe000000000000000373e4967744be007c00,0x230038e011c08e0470251c092754406318c63),(0x45e9b455735000f8000,0x23c1c3f011e08f0478045e9b45571437bdef7b),(0x33aa5dc49789be000000,0x3c01fc001e00f0078031aa1d448289b9ce739c),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def g63C : List ColumnInfo := [(16,0,47,0,7)]
def g63A : List (List Nat) := [[],[33]]
def g63D7 (j : Nat) : Nat := 0x7f
def g63L : Nat → Packing
  | 7 => (1,0,1,0,0,0,0,g63D7)
  | _ => emptyPacking
def g63I (_ _ : Nat) : Option (Nat × Nat) := none
def g63 : Forest := ⟨63,7,fun i => g63Y[i]?.getD (0,0),g63C,g63A,g63L,g63I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63P7_0 : block g63 7 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g63B7 : block g63 7 0 1=true := g63P7_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63T : checkedTables g63 7 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g63 0 0 0 = true)
  · exact (rfl : block g63 1 0 0 = true)
  · exact (rfl : block g63 2 0 0 = true)
  · exact (rfl : block g63 3 0 0 = true)
  · exact (rfl : block g63 4 0 0 = true)
  · exact (rfl : block g63 5 0 0 = true)
  · exact (rfl : block g63 6 0 0 = true)
  · exact g63B7
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63G : graphValid g63 (boundsBefore K233) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low63 : Lower true (varsX 63) (graphGoal 63) 8 := lower_forest (g:=g63) (i:=0) (hints:=3145729) (before_sound K233 V233) g63G g63T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K63 := extendKnown K233 8 [(63,[]),(95,[101]),(159,[67,117,101])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V63 : Known true K63 := extend_ok (m:=63) V233 low63 (by decide +kernel)
def g111Y : Array (Bits × Bits) := #[(0xffffffffe0ffd88ea4a341cb00000000ffffff,0x1104022042000884840140ca24242424242424),(0x7ffe0fffff07d4ba025cbc8d000000ff0000ff,0x220824448010141a005c1c0549494949494949),(0x80000ffffff82c2063f6a272000000ff00ff00,0x445048890000a02063a2a23092929292929292),(0xfffff000000023538125d93400ffff00ff0000,0x60000e042101030124991003030303030303),(0x0,0x0),(0x245d5e0b16d0ff00ff00000000,0x78080f008422458160306c01c1c1c1c1c1c1c),(0x13a4dd980e26ffff0000000000,0x78010f00108412a4c8980026e0e0e0e0e0e0e0),(0x0,0x0),(0x0,0x0)]
def g111C : List ColumnInfo := [(2,0,109,0,7),(4,0,107,0,7),(32,0,79,0,7),(64,0,47,0,7),(0,2,104,5,6),(0,4,104,3,6),(0,32,7,72,6),(0,64,7,40,6),(8,0,103,0,6),(1,2,104,4,5),(1,4,104,2,5),(2,4,104,1,5),(6,0,105,0,5),(8,32,7,64,5),(8,64,7,32,5),(32,64,7,8,5),(96,0,15,0,5),(3,0,104,0,4),(3,4,104,0,4)]
def g111A : List (List Nat) := [[],[101],[33],[33,101],[48,81,98],[48,81,98,33],[48,97,82,33],[48,97,82]]
def g111D5 (j : Nat) : Nat := 0x29be1543d8910
def g111D6 (j : Nat) : Nat := 0x188162058c1a9c3809faed21c21bb553624437721ec4886ed43d8910
def g111H6 (j : Nat) : Nat := 0xd
def g111D7 (j : Nat) : Nat := 0x8a00c082100c88208191040c806450420a8a0910822382442083850d122070c0c140143071234308345078f10512255265177733154882c0f44400ff55121ff55210ff90e10ff55110ff90d10ff50d10bf58e30bf58e109f59640bd58430bbd8910
def g111H7 (j : Nat) : Nat := 0x6400780000000000ca000000000007820800000000342000000000e3000000000
def g111D8 (j : Nat) : Nat := 0x70c084b3491c08e23091423c328d2460602a33c93470e238a3491a38a180e28d2481c20400ca3492081c68e200a1c18e211216d1448d3a9808a2a09001fd41fe90ff903fa81fe30fe987f0c3fc21fd10
def g111H8 (j : Nat) : Nat := 0xb0541000000cd2000007e700000000000042003c4800000d180000050382000000815a1d02d00001f1e83041a06000002c9000000000006c20000000043000000000000000000007cc0000000042a258006400
def g111D9 (j : Nat) : Nat := 0x1882013f
def g111H9 (j : Nat) : Nat := 0x1a040065520b8596b603910863e080000000000000050b84830004c0e10015c418f10000345d70e018afa000191b9080000181c0218780
def g111L : Nat → Packing
  | 5 => (1,4,5,0,0,0,0,g111D5)
  | 6 => (4,3,5,0,0,6,0,g111D6)
  | 7 => (11,2,5,0,0,9,0,g111D7)
  | 8 => (9,1,5,0,0,9,0,g111D8)
  | 9 => (1,0,5,0,0,0,0,g111D9)
  | _ => emptyPacking
def g111I : Nat → Nat → Option (Nat × Nat)
  | 6 => lookupWord 1 2 0 4 0 0 g111H6
  | 7 => lookupWord 1 29 0 9 2 3 g111H7
  | 8 => lookupWord 5 59 3 11 4 3 g111H8
  | 9 => lookupWord 6 37 5 11 4 3 g111H9
  | _ => fun _ => none
def g111 : Forest := ⟨111,9,fun i => g111Y[i]?.getD (0,0),g111C,g111A,g111L,g111I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g111P5_0 : block g111 5 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g111B5 : block g111 5 0 1=true := g111P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g111P6_0 : block g111 6 0 4=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g111B6 : block g111 6 0 4=true := g111P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g111P7_0 : block g111 7 0 3=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g111P7_3 : block g111 7 3 2=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g111P7_5 : block g111 7 5 6=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g111B7 : block g111 7 0 11=true := (@block_merge g111 7 0 3 8 g111P7_0 (@block_merge g111 7 3 2 6 g111P7_3 g111P7_5))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g111P8_0 : block g111 8 0 9=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g111B8 : block g111 8 0 9=true := g111P8_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g111P9_0 : block g111 9 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g111B9 : block g111 9 0 1=true := g111P9_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g111T : checkedTables g111 9 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g111 0 0 0 = true)
  · exact (rfl : block g111 1 0 0 = true)
  · exact (rfl : block g111 2 0 0 = true)
  · exact (rfl : block g111 3 0 0 = true)
  · exact (rfl : block g111 4 0 0 = true)
  · exact g111B5
  · exact g111B6
  · exact g111B7
  · exact g111B8
  · exact g111B9
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g111G : graphValid g111 (boundsBefore K63) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low111 : Lower true (varsX 111) (graphGoal 111) 10 := lower_forest (g:=g111) (i:=0) (hints:=53477377) (before_sound K63 V63) g111G g111T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K111 := extendKnown K63 10 [(111,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V111 : Known true K111 := extend_ok (m:=111) V63 low111 (by decide +kernel)
def g119Y : Array (Bits × Bits) := #[(0xffffffff8003ffffffb7cb446a25ba8003ffff,0x40810008000000b0414400201a09249249),(0xffffffffc001fff8d2a9995d65980fc003f,0x44a4891211208944480d2a0195064192492492),(0xfffffffffffe00078209aeedb2340fc0fc0,0x89491224224112089240009a6ad92064924924),(0x0,0x0),(0xfff00000000000000046e7e05ccfc00003f000,0x118e1c38447223911c46a6a05ccfc036db6db6),(0x48bd2f1bac4e7f000000,0x1e001fc007803c01e048ad0a1ba40e071c71c7),(0xe754b7112b657f000000,0xe00fe0007803c01e00a750b5000b6178e38e38),(0x0,0x0),(0x0,0x0)]
def g119C : List ColumnInfo := [(0,32,23,64,6)]
def g119A : List (List Nat) := [[],[101],[33],[33,101]]
def g119D6 (j : Nat) : Nat := 0x7f
def g119L : Nat → Packing
  | 6 => (1,0,1,0,0,0,0,g119D6)
  | _ => emptyPacking
def g119I (_ _ : Nat) : Option (Nat × Nat) := none
def g119 : Forest := ⟨119,6,fun i => g119Y[i]?.getD (0,0),g119C,g119A,g119L,g119I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g119P6_0 : block g119 6 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g119B6 : block g119 6 0 1=true := g119P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g119T : checkedTables g119 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g119 0 0 0 = true)
  · exact (rfl : block g119 1 0 0 = true)
  · exact (rfl : block g119 2 0 0 = true)
  · exact (rfl : block g119 3 0 0 = true)
  · exact (rfl : block g119 4 0 0 = true)
  · exact (rfl : block g119 5 0 0 = true)
  · exact g119B6
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g119G : graphValid g119 (boundsBefore K111) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low119 : Lower true (varsX 119) (graphGoal 119) 7 := lower_forest (g:=g119) (i:=0) (hints:=90177537) (before_sound K111 V111) g119G g119T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K119 := extendKnown K111 7 [(119,[]),(238,[80,49,98,16,116])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V119 : Known true K119 := extend_ok (m:=119) V111 low119 (by decide +kernel)
def g123Y : Array (Bits × Bits) := #[(0xffffffffffffffffffebc1ba3a28d2c0007fff,0x84202000108080000029001a02089214a5294a),(0x3ffff000ffffc003ffe4fa00b3364bc000001f,0x2949449aa52912592504fa00b13649eb5ad6b5),(0x0,0x0),(0xc0000000fffffffc001c3d44b9c0bd01ff83e0,0xd802c0032009009901140b9002502108421),(0xffffffff00000000000359e6144f4d80007c00,0x318e0930c63c24e24e0259e414474dab5ad6b5),(0x4569b47773c3e0f8000,0x1f001c007c00700700444930275180c6318c6),(0x33aa5dc49781bff00000,0x3e000e00f80038038023aa0c448280b18c6318),(0x0,0x0),(0x0,0x0)]
def g123C : List ColumnInfo := [(2,0,121,0,7)]
def g123A : List (List Nat) := [[],[101],[65],[65,101]]
def g123D7 (j : Nat) : Nat := 0x7f
def g123L : Nat → Packing
  | 7 => (1,0,1,0,0,0,0,g123D7)
  | _ => emptyPacking
def g123I (_ _ : Nat) : Option (Nat × Nat) := none
def g123 : Forest := ⟨123,7,fun i => g123Y[i]?.getD (0,0),g123C,g123A,g123L,g123I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g123P7_0 : block g123 7 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g123B7 : block g123 7 0 1=true := g123P7_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g123T : checkedTables g123 7 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g123 0 0 0 = true)
  · exact (rfl : block g123 1 0 0 = true)
  · exact (rfl : block g123 2 0 0 = true)
  · exact (rfl : block g123 3 0 0 = true)
  · exact (rfl : block g123 4 0 0 = true)
  · exact (rfl : block g123 5 0 0 = true)
  · exact (rfl : block g123 6 0 0 = true)
  · exact g123B7
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g123G : graphValid g123 (boundsBefore K119) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low123 : Lower true (varsX 123) (graphGoal 123) 8 := lower_forest (g:=g123) (i:=0) (hints:=53477377) (before_sound K119 V119) g123G g123T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K123 := extendKnown K119 8 [(123,[]),(125,[33])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V123 : Known true K123 := extend_ok (m:=123) V119 low123 (by decide +kernel)
def g175Y : Array (Bits × Bits) := #[(0xfffffffffc00fffff6e15c16603db00003ffff,0x208000440802000002600c10200d8249249249),(0xffc00fffffff003ff52d43a89f08f000fc003f,0x4108a488908822888505432895003492492492),(0xfffffffffc00b0891aeeae64000fc0fc0,0x8a11491121104411280890864ae24924924924),(0xfffff0000000000008d479059993603f03f000,0xc218e01c21c8721c080710599926c30c30c30),(0x0,0x0),(0x917a6d155cf0fff000000,0xf002001e0020080209178290400d01c71c71c7),(0x0,0x0),(0x4ea977125e06fc0000000,0x3c0fe003c0f03c04e8156125e06e38e38e38),(0x0,0x0)]
def g175C : List ColumnInfo := [(128,0,47,0,7)]
def g175A : List (List Nat) := [[],[33]]
def g175D7 (j : Nat) : Nat := 0x7f
def g175L : Nat → Packing
  | 7 => (1,0,1,0,0,0,0,g175D7)
  | _ => emptyPacking
def g175I (_ _ : Nat) : Option (Nat × Nat) := none
def g175 : Forest := ⟨175,7,fun i => g175Y[i]?.getD (0,0),g175C,g175A,g175L,g175I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g175P7_0 : block g175 7 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g175B7 : block g175 7 0 1=true := g175P7_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g175T : checkedTables g175 7 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g175 0 0 0 = true)
  · exact (rfl : block g175 1 0 0 = true)
  · exact (rfl : block g175 2 0 0 = true)
  · exact (rfl : block g175 3 0 0 = true)
  · exact (rfl : block g175 4 0 0 = true)
  · exact (rfl : block g175 5 0 0 = true)
  · exact (rfl : block g175 6 0 0 = true)
  · exact g175B7
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g175G : graphValid g175 (boundsBefore K123) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low175 : Lower true (varsX 175) (graphGoal 175) 8 := lower_forest (g:=g175) (i:=0) (hints:=1345323009) (before_sound K123 V123) g175G g175T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K175 := extendKnown K123 8 [(175,[]),(183,[67,117])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V175 : Known true K175 := extend_ok (m:=175) V123 low175 (by decide +kernel)
def g187Y : Array (Bits × Bits) := #[(0xfffffffffffffffffff9c1ba3aa8d240007fff,0x84202000108080000039001a02081214a5294a),(0x3ffff000ffffc003ffe6da003732cbc000001f,0x2949449aa52912592506da003532c9eb5ad6b5),(0x0,0x0),(0xc0000000fffffffc001c1d443dc1bd000f83e0,0x300d882cc0322092098019443d81a52318c631),(0xffffffff00000000000379e6904e4d81f07c00,0x18e0130063c04e04e0251e090464d0a5294a5),(0x4569b47773c3e0f8000,0x1f001c007c00700700444930276180c6318c6),(0x0,0x0),(0x33aa5dc49781bff00000,0x3e000e00f80038038031aa0c448180b18c6318),(0x0,0x0)]
def g187C : List ColumnInfo := [(2,0,185,0,7)]
def g187A : List (List Nat) := [[],[67,117]]
def g187D7 (j : Nat) : Nat := 0x7f
def g187L : Nat → Packing
  | 7 => (1,0,1,0,0,0,0,g187D7)
  | _ => emptyPacking
def g187I (_ _ : Nat) : Option (Nat × Nat) := none
def g187 : Forest := ⟨187,7,fun i => g187Y[i]?.getD (0,0),g187C,g187A,g187L,g187I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g187P7_0 : block g187 7 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g187B7 : block g187 7 0 1=true := g187P7_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g187T : checkedTables g187 7 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g187 0 0 0 = true)
  · exact (rfl : block g187 1 0 0 = true)
  · exact (rfl : block g187 2 0 0 = true)
  · exact (rfl : block g187 3 0 0 = true)
  · exact (rfl : block g187 4 0 0 = true)
  · exact (rfl : block g187 5 0 0 = true)
  · exact (rfl : block g187 6 0 0 = true)
  · exact g187B7
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g187G : graphValid g187 (boundsBefore K175) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low187 : Lower true (varsX 187) (graphGoal 187) 8 := lower_forest (g:=g187) (i:=0) (hints:=1076887553) (before_sound K175 V175) g187G g187T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K187 := extendKnown K175 8 [(187,[]),(189,[33])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V187 : Known true K187 := extend_ok (m:=187) V175 low187 (by decide +kernel)
def g190Y : Array (Bits × Bits) := #[(0x0,0x0),(0xfffffffffffffffffffbb5a7dcc059e200003f,0x4892492449249222224ba5a694405882555555),(0xffffffffffffffffffffd22569999d7400003f,0x91249248924924444484520169998574aaaaaa),(0xffff000003fffff000070bd66f34e0b2000fc0,0x238e00ee380388808e703564a14e0b2cf3cf3),(0xfffffffffc0000000000ef14349776f103f000,0xe3c0038f000e3f008f00ce14348552f13cf3cf),(0x48afbb7e9c20efc0fc0,0xfc0003f0000fc000f00088a935e9020030c30c),(0x0,0x0),(0xe754a985f269dfff000,0xfc0003f0000f000e31428812240cc30c30),(0x0,0x0)]
def g190C : List ColumnInfo := [(0,2,184,4,5)]
def g190A : List (List Nat) := [[],[67,117],[33],[33,67,117]]
def g190D5 (j : Nat) : Nat := 0x7f
def g190L : Nat → Packing
  | 5 => (1,0,1,0,0,0,0,g190D5)
  | _ => emptyPacking
def g190I (_ _ : Nat) : Option (Nat × Nat) := none
def g190 : Forest := ⟨190,5,fun i => g190Y[i]?.getD (0,0),g190C,g190A,g190L,g190I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g190P5_0 : block g190 5 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g190B5 : block g190 5 0 1=true := g190P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g190T : checkedTables g190 5 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g190 0 0 0 = true)
  · exact (rfl : block g190 1 0 0 = true)
  · exact (rfl : block g190 2 0 0 = true)
  · exact (rfl : block g190 3 0 0 = true)
  · exact (rfl : block g190 4 0 0 = true)
  · exact g190B5
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g190G : graphValid g190 (boundsBefore K187) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low190 : Lower true (varsX 190) (graphGoal 190) 6 := lower_forest (g:=g190) (i:=0) (hints:=1077367072) (before_sound K187 V187) g190G g190T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K190 := extendKnown K187 6 [(190,[]),(246,[67,99,117])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V190 : Known true K190 := extend_ok (m:=190) V187 low190 (by decide +kernel)
def g219Y : Array (Bits × Bits) := #[(0xfffffffffffffffffffd9c1a7723879c007fff,0x40422010840422004405900050218290842108),(0xffe0003ffffe0003fffe6da026374cae00001f,0x928446a52948445888a26da026164c2f7bdef7),(0x0,0x0),(0x3ffffffffc0001c1f41f5c317a0f83e0,0x1b080b0601908091013001940718316a5294a5),(0xffffffc0000000000002379fc2c4fe21f07c00,0x1c008c0031e008e011c2251b82443420318c63),(0x0,0x0),(0x2456978ff62520f8000,0xe010f0383e010f021e02446978e74211ad6b5a),(0x73aa5b8895b2bf00000,0x1f003fc001f003e0051aa438894b0bce739c),(0x0,0x0)]
def g219C : List ColumnInfo := [(2,0,217,0,5),(64,0,155,0,5),(128,0,91,0,5),(8,64,147,0,4),(16,128,75,0,4)]
def g219A : List (List Nat) := [[],[67,118]]
def g219D5 (j : Nat) : Nat := 0x1f610
def g219D6 (j : Nat) : Nat := 0x222317f
def g219H6 (j : Nat) : Nat := 0xe
def g219L : Nat → Packing
  | 5 => (1,1,3,0,0,0,0,g219D5)
  | 6 => (1,0,3,0,0,0,0,g219D6)
  | _ => emptyPacking
def g219I : Nat → Nat → Option (Nat × Nat)
  | 6 => lookupWord 1 2 0 4 0 0 g219H6
  | _ => fun _ => none
def g219 : Forest := ⟨219,6,fun i => g219Y[i]?.getD (0,0),g219C,g219A,g219L,g219I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g219P5_0 : block g219 5 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g219B5 : block g219 5 0 1=true := g219P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g219P6_0 : block g219 6 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g219B6 : block g219 6 0 1=true := g219P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g219T : checkedTables g219 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g219 0 0 0 = true)
  · exact (rfl : block g219 1 0 0 = true)
  · exact (rfl : block g219 2 0 0 = true)
  · exact (rfl : block g219 3 0 0 = true)
  · exact (rfl : block g219 4 0 0 = true)
  · exact g219B5
  · exact g219B6
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g219G : graphValid g219 (boundsBefore K190) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low219 : Lower true (varsX 219) (graphGoal 219) 7 := lower_forest (g:=g219) (i:=0) (hints:=1124073473) (before_sound K190 V190) g219G g219T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K219 := extendKnown K190 7 [(219,[]),(221,[33])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V219 : Known true K219 := extend_ok (m:=219) V190 low219 (by decide +kernel)
def g231Y : Array (Bits × Bits) := #[(0xfffffffff000ffffff300ad36b06fbc0000fff,0x8882222221121101103002c209065b09249249),(0xffffffffffff000fff6a7c6985d0bc8003f03f,0x110444444220222220487c018480a492492492),(0xfffffffffff0009b463ee678034003ffc0,0x22288888844044044283003c62780064924924),(0x0,0x0),(0x0,0x0),(0xffff00000000000000c5b3c45cefc43ffc0000,0x30000f0004004004842340446684071c71c7),(0xc9ad2b1b8c4a40fc0000,0xc3c0f0f00878878878498c2b1b884a78e38e38),(0x6654b7112b657f000000,0xfc00ff000f80f80f806254b711096178e38e38),(0x0,0x0)]
def g231C : List ColumnInfo := [(0,32,7,192,6)]
def g231A : List (List Nat) := [[],[118],[33],[33,118],[16],[16,118],[16,32],[16,32,118],[32,16],[32,16,118],[32],[32,118]]
def g231D6 (j : Nat) : Nat := 0x7f
def g231L : Nat → Packing
  | 6 => (1,0,1,0,0,0,0,g231D6)
  | _ => emptyPacking
def g231I (_ _ : Nat) : Option (Nat × Nat) := none
def g231 : Forest := ⟨231,6,fun i => g231Y[i]?.getD (0,0),g231C,g231A,g231L,g231I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g231P6_0 : block g231 6 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g231B6 : block g231 6 0 1=true := g231P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g231T : checkedTables g231 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g231 0 0 0 = true)
  · exact (rfl : block g231 1 0 0 = true)
  · exact (rfl : block g231 2 0 0 = true)
  · exact (rfl : block g231 3 0 0 = true)
  · exact (rfl : block g231 4 0 0 = true)
  · exact (rfl : block g231 5 0 0 = true)
  · exact g231B6
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g231G : graphValid g231 (boundsBefore K219) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low231 : Lower true (varsX 231) (graphGoal 231) 7 := lower_forest (g:=g231) (i:=0) (hints:=1432354817) (before_sound K219 V219) g231G g231T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K231 := extendKnown K219 7 [(231,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V231 : Known true K231 := extend_ok (m:=231) V219 low231 (by decide +kernel)
def g235Y : Array (Bits × Bits) := #[(0xe001ffffffffffffffde9421f8dca2c00003ff,0x4244848242488480480e900110dc229294a529),(0x1ffffffffc003fff08ee7e22b2a4000001f,0x849929149491091891300ee6e223086d6b5ad6),(0x0,0x0),(0xfffe0000fffffffc000c0b9abbb1d1000fffe0,0x81030181802101101800a12aa00d108421084),(0x0,0x0),(0xffffffff0000000000237964166e4dbff07c00,0x20001c00200202616010680806318c63),(0x24569b45573c01ff8000,0x10e1c1c0e0e021c21c241489451724318c6318),(0x13aa5dc49781be000000,0x1f01fe00ff003e03e0118a1dc49781b9ce739c),(0x0,0x0)]
def g235C : List ColumnInfo := [(128,0,107,0,7)]
def g235A : List (List Nat) := [[]]
def g235D7 (j : Nat) : Nat := 0x7f
def g235L : Nat → Packing
  | 7 => (1,0,1,0,0,0,0,g235D7)
  | _ => emptyPacking
def g235I (_ _ : Nat) : Option (Nat × Nat) := none
def g235 : Forest := ⟨235,7,fun i => g235Y[i]?.getD (0,0),g235C,g235A,g235L,g235I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g235P7_0 : block g235 7 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g235B7 : block g235 7 0 1=true := g235P7_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g235T : checkedTables g235 7 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g235 0 0 0 = true)
  · exact (rfl : block g235 1 0 0 = true)
  · exact (rfl : block g235 2 0 0 = true)
  · exact (rfl : block g235 3 0 0 = true)
  · exact (rfl : block g235 4 0 0 = true)
  · exact (rfl : block g235 5 0 0 = true)
  · exact (rfl : block g235 6 0 0 = true)
  · exact g235B7
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g235G : graphValid g235 (boundsBefore K231) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low235 : Lower true (varsX 235) (graphGoal 235) 8 := lower_forest (g:=g235) (i:=0) (hints:=1395654657) (before_sound K231 V231) g235G g235T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K235 := extendKnown K231 8 [(235,[]),(237,[33])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V235 : Known true K235 := extend_ok (m:=235) V231 low235 (by decide +kernel)
def g243Y : Array (Bits × Bits) := #[(0xfffffffffffffffffffb887ecf2a94d40003ff,0x80921012421111004402882cc02894c094a529),(0x3fffffffff8001fffd1e832eaee0b400001f,0x3524a4a494a2222c88a516832e8660356b5ad6),(0x0,0x0),(0x0,0x0),(0xffc00007fffffffe00049371b7c5055a007fe0,0x2600c6c018c4044811340351374501106318c6),(0xfffffff8000000000006659e6255fe21ff8000,0x3800070000f8007001c0241262559420318c63),(0x6456958fe62520f8000,0xc038f8071f0047811e06416918aa6253ce739c),(0x33aa5b8895b2bf07c00,0x3f0007e0007801e00318a488884a0b8c6318),(0x0,0x0)]
def g243C : List ColumnInfo := [(0,2,240,1,5),(0,64,147,32,5),(2,0,241,0,5),(64,0,179,0,5)]
def g243A : List (List Nat) := [[],[80,97,116]]
def g243D6 (j : Nat) : Nat := 0xe413f
def g243L : Nat → Packing
  | 6 => (1,0,2,0,0,0,0,g243D6)
  | _ => emptyPacking
def g243I (_ _ : Nat) : Option (Nat × Nat) := none
def g243 : Forest := ⟨243,6,fun i => g243Y[i]?.getD (0,0),g243C,g243A,g243L,g243I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g243P6_0 : block g243 6 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g243B6 : block g243 6 0 1=true := g243P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g243T : checkedTables g243 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g243 0 0 0 = true)
  · exact (rfl : block g243 1 0 0 = true)
  · exact (rfl : block g243 2 0 0 = true)
  · exact (rfl : block g243 3 0 0 = true)
  · exact (rfl : block g243 4 0 0 = true)
  · exact (rfl : block g243 5 0 0 = true)
  · exact g243B6
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g243G : graphValid g243 (boundsBefore K235) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low243 : Lower true (varsX 243) (graphGoal 243) 7 := lower_forest (g:=g243) (i:=0) (hints:=1163919361) (before_sound K235 V235) g243G g243T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K243 := extendKnown K235 7 [(243,[]),(245,[33])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V243 : Known true K243 := extend_ok (m:=243) V235 low243 (by decide +kernel)
def g249Y : Array (Bits × Bits) := #[(0xffffff807fffffff724991e865340000000fff,0x20a481294922505022491068653228a28a28a2),(0x0,0x0),(0x0,0x0),(0x3fffffffff00ff46a47d1387240000fff03f,0x5080a001004020044804d1082051451451451),(0xffc000007fffff00b49c8bfa10c8003f000fc0,0x46012c02024800029094899200c8d34d34d34d),(0xffffffff80000000894b0497ecd3ffc003f000,0x8003000007004040908008364c06186186186),(0x9175782c5b400fc0fc0000,0x7031c04c638098989075302c19028a28a28a28),(0x4e937660389bf03f000000,0x803e00707c00e0e04603766018130c30c30c30),(0x0,0x0)]
def g249C : List ColumnInfo := [(1,0,248,0,7),(64,0,185,0,7),(128,0,121,0,7),(0,16,104,129,6),(16,0,233,0,6),(8,0,241,0,5),(32,0,217,0,5)]
def g249A : List (List Nat) := [[],[112,83]]
def g249D5 (j : Nat) : Nat := 0x4bf7458e31
def g249D6 (j : Nat) : Nat := 0x10420806284506c85b2c0bf58e31efd9131afd9131af59031be58031
def g249H6 (j : Nat) : Nat := 0x2
def g249D7 (j : Nat) : Nat := 0x190e2a5474365a891d90ea6147888807f8c7fa63fc31
def g249H7 (j : Nat) : Nat := 0x62000000000031c400730000000090000000000000000000005800
def g249D8 (j : Nat) : Nat := 0x468817f
def g249H8 (j : Nat) : Nat := 0x29ecc3500
def g249L : Nat → Packing
  | 5 => (1,3,3,0,0,0,0,g249D5)
  | 6 => (5,2,3,0,0,6,0,g249D6)
  | 7 => (3,1,3,0,0,7,0,g249D7)
  | 8 => (1,0,3,0,0,0,0,g249D8)
  | _ => emptyPacking
def g249I : Nat → Nat → Option (Nat × Nat)
  | 6 => lookupWord 1 2 0 4 0 0 g249H6
  | 7 => lookupWord 1 31 0 8 3 1 g249H7
  | 8 => lookupWord 1 7 0 7 2 1 g249H8
  | _ => fun _ => none
def g249 : Forest := ⟨249,8,fun i => g249Y[i]?.getD (0,0),g249C,g249A,g249L,g249I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g249P5_0 : block g249 5 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g249B5 : block g249 5 0 1=true := g249P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g249P6_0 : block g249 6 0 3=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g249P6_3 : block g249 6 3 2=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g249B6 : block g249 6 0 5=true := (@block_merge g249 6 0 3 2 g249P6_0 g249P6_3)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g249P7_0 : block g249 7 0 3=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g249B7 : block g249 7 0 3=true := g249P7_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g249P8_0 : block g249 8 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g249B8 : block g249 8 0 1=true := g249P8_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g249T : checkedTables g249 8 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g249 0 0 0 = true)
  · exact (rfl : block g249 1 0 0 = true)
  · exact (rfl : block g249 2 0 0 = true)
  · exact (rfl : block g249 3 0 0 = true)
  · exact (rfl : block g249 4 0 0 = true)
  · exact g249B5
  · exact g249B6
  · exact g249B7
  · exact g249B8
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g249G : graphValid g249 (boundsBefore K243) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low249 : Lower true (varsX 249) (graphGoal 249) 9 := lower_forest (g:=g249) (i:=0) (hints:=1127219203) (before_sound K243 V243) g249G g249T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K249 := extendKnown K243 9 [(249,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V249 : Known true K249 := extend_ok (m:=249) V243 low249 (by decide +kernel)
def g127Y : Array (Bits × Bits) := #[(0xc3c54d164159a3984033e000000000ffffffff,0x414014005180984000802424242424242424),(0xfcaa2209ae685a46c131ad000000ff000000ff,0x4ca82200a6285a468131214949494949494949),(0x350e052b8b92683b0fc45c000000ff0000ff00,0x3106052b098220210ec45c9292929292929292),(0x8203bfa0007d066b6fe0a00ffff0000ff0000,0x298a00025062947a0a0303030303030303),(0x6e75e8bd6aa6761a2240600000000ff000000,0x6a61e8bd6aa6761a22406dbdbdbdbdbdbdbdb),(0x8b9a4e4bcb285c13844f5ff00ff0000000000,0x8a984649c9081002804e51c1c1c1c1c1c1c1c),(0x6754920534ad14b5cf8813ffff000000000000,0x67541201202d0495438010e0e0e0e0e0e0e0e0),(0x0,0x0),(0x0,0x0)]
def g127C : List ColumnInfo := [(16,0,111,0,10)]
def g127A : List (List Nat) := [[],[101],[33],[33,101]]
def g127D10 (j : Nat) : Nat := 0xff
def g127L : Nat → Packing
  | 10 => (1,0,1,0,0,0,0,g127D10)
  | _ => emptyPacking
def g127I (_ _ : Nat) : Option (Nat × Nat) := none
def g127 : Forest := ⟨127,10,fun i => g127Y[i]?.getD (0,0),g127C,g127A,g127L,g127I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P10_0 : block g127 10 0 1=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g127B10 : block g127 10 0 1=true := g127P10_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127T : checkedTables g127 10 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g127 0 0 0 = true)
  · exact (rfl : block g127 1 0 0 = true)
  · exact (rfl : block g127 2 0 0 = true)
  · exact (rfl : block g127 3 0 0 = true)
  · exact (rfl : block g127 4 0 0 = true)
  · exact (rfl : block g127 5 0 0 = true)
  · exact (rfl : block g127 6 0 0 = true)
  · exact (rfl : block g127 7 0 0 = true)
  · exact (rfl : block g127 8 0 0 = true)
  · exact (rfl : block g127 9 0 0 = true)
  · exact g127B10
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127G : graphValid g127 (boundsBefore K249) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low127 : Lower true (varsX 127) (graphGoal 127) 11 := lower_forest (g:=g127) (i:=0) (hints:=53477377) (before_sound K249 V249) g127G g127T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K127 := extendKnown K249 11 [(127,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V127 : Known true K127 := extend_ok (m:=127) V249 low127 (by decide +kernel)
def g191Y : Array (Bits × Bits) := #[(0xc3814d164155b398403be000000000ffffffff,0x2014014005080984008802424242424242424),(0xf8ae2208aac94e46c531ad000000ff000000ff,0x48ac2200a2894e468131214949494949494949),(0x350a052b8f12783f0f445c000000ff0000ff00,0x3502052b0d0230210e445c9292929292929292),(0x8203bfa1407d466b67e0a0000ff0000ff0000,0x3b8a1407546696720ac3c3c3c3c3c3c3c3),(0x6e75e8bc2aa6361a2a40600ff0000ff000000,0x4a20c8ac2aa6361a0a4061b1b1b1b1b1b1b1b),(0x8b9a4e4bcb285c13844f5ff00ff0000000000,0x8a9846488b081012804e51c1c1c1c1c1c1c1c),(0x0,0x0),(0x6754920534ad14b5cf8813ffff000000000000,0x6354120134051494470810e0e0e0e0e0e0e0e0),(0x0,0x0)]
def g191C : List ColumnInfo := [(2,0,189,0,8),(4,0,187,0,8),(8,0,183,0,8),(16,0,175,0,8),(32,0,159,0,8),(128,0,63,0,8),(0,32,23,136,7),(0,128,15,48,7),(6,0,185,0,7),(40,0,151,0,7),(144,0,47,0,7),(0,2,184,5,6),(0,4,184,3,6),(1,0,190,0,6),(8,32,23,128,6),(8,128,7,48,6),(16,32,7,136,6),(24,0,167,0,6),(32,128,15,16,6),(160,0,31,0,6),(1,2,184,4,5),(1,4,184,2,5),(4,2,184,1,5),(10,0,181,0,5),(18,0,173,0,5),(34,0,157,0,5),(136,0,23,0,5),(136,32,23,0,5),(3,4,184,0,4)]
def g191A : List (List Nat) := [[],[67,117],[33],[33,67,117]]
def g191D5 (j : Nat) : Nat := 0x33c163648804c510
def g191D6 (j : Nat) : Nat := 0x16405c80b901000000d142c29cfd82a4878c00ccec22c6382639cd63608704c739ac7c12e318667dd38350130ab7caac7b9221bd1632013144339f07b92a0884f8648804c510
def g191H6 (j : Nat) : Nat := 0xa
def g191D7 (j : Nat) : Nat := 0x860564021190111040c100000001030208000000005a40800307001000c10416902019010304164c11a0f07002a4a20a881c107930b843440ce4c2c00d1453930830222882c3448fa3884a047d9e8789dc759c86c9ac699a0669945f9785a95c559505092c4991844904398d02e8ac278781282c098009fd80dd1319fd841c131ddd631c131ddd635c630dbf745d130f9f7450d309fd84dc530bef825c530bdf844c530bdf8350130f9d4350130bdd848c130bdf835d6109fd84dce109ff845ce10b7f8558e10ddf7358e109fd8750e10ddd7350e10bdf83542109fd84dcd109ff845cd10b7f8558d10ddf7358d10ded65dc910ded63dc910ded43dc910bf7844c510fd5634c510bdf8354110def7254110def724c110bf583841109bd841c1319ed821c1319ef825c6309ef825cd10bf0804c510
def g191H7 (j : Nat) : Nat := 0x1d7d010fc80005c000000005cd0000000002f00
def g191D8 (j : Nat) : Nat := 0x1b091863518444140502385c5a1402a0305031a442470820c89206909860c5a2092073418b444433219140482978034349060130c2a4830039a15141807058a2c322829200d06014382070b2484814385212640d18686c9215171a42a9250448a93c8362c8285c30c1c283912468e1c29092a058c1c290922d40c3058100aa48d1c301005724228a8848a939b13201842ce0a3058702032a39240c161c305080401124ae58e50491183860a1018b503c712a0a0856394122070c141e44520690343860a101a2904070c141e4447070e18284068a414200c0167048d904222828b1010685a250854a0721a248d4886ad03852c30a6ad3006f43e37c076ce87ca38a700dcbb2b5b69bd0195f1e613bd5706c8d6fa8d45a734c493720224c197d2ec9ba352652bad5327647e874fd9bd2fe520850e817e2ac44859060003feba461ffdd130ffae8987ff714c3feb8a61ff50530ffc80987fd404c3febac21ff59610ffae7087fd63843fea1c21ff54210ffa61087fd65443feb1a21ff50d10ffaa0887fd30442ffb82a37f1c151bfee898dfd744c7eeb1a637fdc131bf8e098dfd71942ffb8aa17fdd230bfae9187dd638c2feb8c617fdd130bfae8987dd434c2ffb8a61f74c530fbc60985ff73842feb9c217fdcd10bfae6887ef72443fa98a21fd84110afeeab1cfd76942efb9aa17bdc910
def g191H8 (j : Nat) : Nat := 0x40662551b00080001dd8fc45000000b01000b47000000000912000f0b000d1721a000708fa2000000000000904992000000f0365cf1ce0926154690e04cb1f313000a20618b0d00040a000988e1600030cb24000c05000c0f319911d15000000b22e96000495802a07b1455300082171092300071e000120860401b0d
def g191D9 (j : Nat) : Nat := 0x35051298a20f414d8b4144a224a9124202ae7a951048ca8aa4a9504a044a9504a02aa7d152848c7d541220e31b55240c38ce2955240f8cb452a4cfc63288f05a18003fd65ff58ffd43ff547fd31ff943fd50ff8c3fd30ff843fd10
def g191H9 (j : Nat) : Nat := 0x351fab206484987c00006c095e9263319221d8886b40000b1ea3db0c800004a4000000000000000002e865aec4e474002498003d7fc040019a5297c2c002229430000000001d29cc7087d9a2b982769a51658f81be354b800000000113a12792206000000026b44098717b03482988c0000022798c14140000000000000000018b4001c38e5bcac00000205445c00366741e47bc12a8c0030bd19c000050001c20c3d093471a7e25400000089c0010a2c69a8be45c59ca8000444a8100c808aca9445004156802628481201a3
def g191D10 (j : Nat) : Nat := 0x52501ff
def g191H10 (j : Nat) : Nat := 0x19300000028000000000000000000000000000000000028565b57b1a36a0000000000000071f4300000000000000000112324006980000342c20c188000002d54100000000000007dc0000000000000000028400003540000000000000000000000000c9dd9002114a
def g191L : Nat → Packing
  | 5 => (1,5,5,0,0,0,0,g191D5)
  | 6 => (8,4,5,0,0,7,0,g191D6)
  | 7 => (38,3,5,0,0,10,0,g191D7)
  | 8 => (50,2,5,0,0,11,0,g191D8)
  | 9 => (11,1,5,0,0,9,0,g191D9)
  | 10 => (1,0,5,0,0,0,0,g191D10)
  | _ => emptyPacking
def g191I : Nat → Nat → Option (Nat × Nat)
  | 6 => lookupWord 1 2 0 4 0 0 g191H6
  | 7 => lookupWord 2 23 0 7 3 0 g191H7
  | 8 => lookupWord 12 79 4 12 6 2 g191H8
  | 9 => lookupWord 22 127 5 12 6 2 g191H9
  | 10 => lookupWord 6 89 3 10 4 2 g191H10
  | _ => fun _ => none
def g191 : Forest := ⟨191,10,fun i => g191Y[i]?.getD (0,0),g191C,g191A,g191L,g191I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g191P5_0 : block g191 5 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g191B5 : block g191 5 0 1=true := g191P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g191P6_0 : block g191 6 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g191P6_1 : block g191 6 1 7=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g191B6 : block g191 6 0 8=true := (@block_merge g191 6 0 1 7 g191P6_0 g191P6_1)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g191P7_0 : block g191 7 0 5=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g191P7_5 : block g191 7 5 33=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g191B7 : block g191 7 0 38=true := (@block_merge g191 7 0 5 33 g191P7_0 g191P7_5)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g191P8_0 : block g191 8 0 4=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g191P8_4 : block g191 8 4 26=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g191P8_30 : block g191 8 30 20=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g191B8 : block g191 8 0 50=true := (@block_merge g191 8 0 4 46 g191P8_0 (@block_merge g191 8 4 26 20 g191P8_4 g191P8_30))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g191P9_0 : block g191 9 0 11=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g191B9 : block g191 9 0 11=true := g191P9_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g191P10_0 : block g191 10 0 1=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g191B10 : block g191 10 0 1=true := g191P10_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g191T : checkedTables g191 10 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g191 0 0 0 = true)
  · exact (rfl : block g191 1 0 0 = true)
  · exact (rfl : block g191 2 0 0 = true)
  · exact (rfl : block g191 3 0 0 = true)
  · exact (rfl : block g191 4 0 0 = true)
  · exact g191B5
  · exact g191B6
  · exact g191B7
  · exact g191B8
  · exact g191B9
  · exact g191B10
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g191G : graphValid g191 (boundsBefore K127) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low191 : Lower true (varsX 191) (graphGoal 191) 11 := lower_forest (g:=g191) (i:=0) (hints:=1076887553) (before_sound K127 V127) g191G g191T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K191 := extendKnown K127 11 [(191,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V191 : Known true K191 := extend_ok (m:=191) V127 low191 (by decide +kernel)
def g223Y : Array (Bits × Bits) := #[(0x7229e142490588d80be52f8000000fffffffff,0x40280002090400c00384261008040201008040),(0x17c402858c525f2abca45c80001ff0000001ff,0x1784028184524a2a9c2048a552a954aa552a95),(0xa140e4f4c39bd577e2089200001ff00003fe00,0xa040e474428995156008904aa552a954aa552a),(0x4173738026ea3bb251af9803fe00007fc0000,0x173520024aa33b2410598cc6633198cc6633),(0xdceb9c83b6cbae047043c87fc0000ff8000000,0x94419c81a243ac043043c803c1e0f0783c1e0f),(0x0,0x0),(0x1734d2ff37241445ccdee0003fe00000000000,0x1720c2df35241444c8cea073399cce673399cc),(0xea924f2334f833ded60c247fc0000000000000,0x6a92432214b813dac60c247c3e1f0f87c3e1f0),(0x0,0x0)]
def g223C : List ColumnInfo := [(0,64,151,8,8),(0,128,79,16,8),(64,0,159,0,8),(128,0,95,0,8),(2,0,221,0,7),(4,0,219,0,7),(8,64,151,0,7),(16,128,79,0,7),(6,0,217,0,5)]
def g223A : List (List Nat) := [[],[67,118],[33],[33,67,118]]
def g223D6 (j : Nat) : Nat := 0x50816a809ee871c910de7711c910fe12148110
def g223D7 (j : Nat) : Nat := 0x240c2040155045902005902024048045902144084073cb1c04a296847e6c665a4e3c2a1e00bfee5085fd72843fd104217fdc910fdee4885fd72443f639221fd48510ff440887f920443fb082217bdc910
def g223H7 (j : Nat) : Nat := 0x5000000a00003100d200000000000000
def g223D8 (j : Nat) : Nat := 0x1272bd903567225ec34e4525ec3484803fd21ff843fd10
def g223H8 (j : Nat) : Nat := 0x188000000000000000000000000000000000000000050c0000000000040000000000000000000000000000000000000006000000000000000002020018500000000000000000000d0000000000000000000000000000000000000000000000000000000030700000000000000000000000000018900000000000000b104000000000000000000000052800003a40000000000000000000098c0000000
def g223D9 (j : Nat) : Nat := 0x64a8ec37f
def g223H9 (j : Nat) : Nat := 0x680000f9000000006100000000000000c200000000000000000080000000000000000000000000
def g223L : Nat → Packing
  | 6 => (3,3,4,0,0,5,0,g223D6)
  | 7 => (12,2,4,0,0,8,0,g223D7)
  | 8 => (3,1,4,0,0,7,0,g223D8)
  | 9 => (1,0,4,0,0,0,0,g223D9)
  | _ => emptyPacking
def g223I : Nat → Nat → Option (Nat × Nat)
  | 7 => lookupWord 1 17 0 8 2 2 g223H7
  | 8 => lookupWord 3 127 0 10 4 2 g223H8
  | 9 => lookupWord 1 43 0 8 2 2 g223H9
  | _ => fun _ => none
def g223 : Forest := ⟨223,9,fun i => g223Y[i]?.getD (0,0),g223C,g223A,g223L,g223I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g223P6_0 : block g223 6 0 3=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g223B6 : block g223 6 0 3=true := g223P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g223P7_0 : block g223 7 0 1=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g223P7_1 : block g223 7 1 11=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g223B7 : block g223 7 0 12=true := (@block_merge g223 7 0 1 11 g223P7_0 g223P7_1)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g223P8_0 : block g223 8 0 3=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g223B8 : block g223 8 0 3=true := g223P8_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g223P9_0 : block g223 9 0 1=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g223B9 : block g223 9 0 1=true := g223P9_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g223T : checkedTables g223 9 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g223 0 0 0 = true)
  · exact (rfl : block g223 1 0 0 = true)
  · exact (rfl : block g223 2 0 0 = true)
  · exact (rfl : block g223 3 0 0 = true)
  · exact (rfl : block g223 4 0 0 = true)
  · exact (rfl : block g223 5 0 0 = true)
  · exact g223B6
  · exact g223B7
  · exact g223B8
  · exact g223B9
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g223G : graphValid g223 (boundsBefore K191) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low223 : Lower true (varsX 223) (graphGoal 223) 10 := lower_forest (g:=g223) (i:=0) (hints:=1124073473) (before_sound K191 V191) g223G g223T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K223 := extendKnown K191 10 [(223,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V223 : Known true K223 := extend_ok (m:=223) V191 low223 (by decide +kernel)
def g239Y : Array (Bits × Bits) := #[(0xf4246312e9762228439f440000000000ffffff,0x4242212a07202084380042121212121212121),(0xc98922e842db58b2385d5a00000000ff0000ff,0x10000a8428948b2385d524a4a4a4a4a4a4a4a),(0x2a9fc1401b053fdbd200a800000000ff00ff00,0xaa9bc140190435418000a89494949494949494),(0x1400993f3005d502897abb0000ffff00ff0000,0x100089051005d002885a8a1818181818181818),(0x0,0x0),(0x3732c8bc6a86245a4a0a6ffff00ff00000000,0x143208ac200224400a0200707070707070707),(0x45cd6e4bcb085e13a405500ffff0000000000,0x41c56602cb005a1320055e0e0e0e0e0e0e0e0),(0x33aa420534af14b5cf8c13ff00000000000000,0x32a8420534af14b1cf0c13f8f8f8f8f8f8f8f8),(0x0,0x0)]
def g239C : List ColumnInfo := [(128,0,111,0,10)]
def g239A : List (List Nat) := [[],[33]]
def g239D10 (j : Nat) : Nat := 0xff
def g239L : Nat → Packing
  | 10 => (1,0,1,0,0,0,0,g239D10)
  | _ => emptyPacking
def g239I (_ _ : Nat) : Option (Nat × Nat) := none
def g239 : Forest := ⟨239,10,fun i => g239Y[i]?.getD (0,0),g239C,g239A,g239L,g239I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g239P10_0 : block g239 10 0 1=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g239B10 : block g239 10 0 1=true := g239P10_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g239T : checkedTables g239 10 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g239 0 0 0 = true)
  · exact (rfl : block g239 1 0 0 = true)
  · exact (rfl : block g239 2 0 0 = true)
  · exact (rfl : block g239 3 0 0 = true)
  · exact (rfl : block g239 4 0 0 = true)
  · exact (rfl : block g239 5 0 0 = true)
  · exact (rfl : block g239 6 0 0 = true)
  · exact (rfl : block g239 7 0 0 = true)
  · exact (rfl : block g239 8 0 0 = true)
  · exact (rfl : block g239 9 0 0 = true)
  · exact g239B10
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g239G : graphValid g239 (boundsBefore K223) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low239 : Lower true (varsX 239) (graphGoal 239) 11 := lower_forest (g:=g239) (i:=0) (hints:=1395654657) (before_sound K223 V223) g239G g239T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K239 := extendKnown K223 11 [(239,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V239 : Known true K239 := extend_ok (m:=239) V223 low239 (by decide +kernel)
def g247Y : Array (Bits × Bits) := #[(0xfad98ed04d134bc442c250d300000000ffffff,0x4904c009030a04424210c021212121212121),(0xf9112704d6aaf0131cf1f325000000ff0000ff,0x4010030454a8f0131ca1c3014a4a4a4a4a4a4a),(0x7a4a81aa2b024fc5719a4e4000000ff00ff00,0x97a4a81aa21004e80118242494949494949494),(0x0,0x0),(0x4a602b54b0c83ab31338e3b0000ff00ff0000,0xe4860230420081a331318e3b1e1e1e1e1e1e1e),(0x44a75ca74619cc5893d0d18ffff0000000000,0x48348a542090c581110c1807070707070707),(0x48b9a6913c9e72a08eca5cc00ff0000000000,0x4838a6103c9672a08eca1c4f8f8f8f8f8f8f8),(0x2754927a84d3e2baf803a80ff00ff00000000,0x2314905a84d2e080e803080e0e0e0e0e0e0e0),(0x0,0x0)]
def g247C : List ColumnInfo := [(0,64,151,32,8),(64,0,183,0,8),(0,32,23,192,7),(2,0,245,0,7),(4,0,243,0,7),(16,0,231,0,7),(32,0,151,0,7),(128,0,119,0,7),(0,2,240,5,6),(0,4,240,3,6),(0,128,7,48,6),(1,0,246,0,6),(64,128,7,48,6),(1,2,240,4,5),(1,4,240,2,5),(2,4,240,1,5),(6,0,241,0,5),(3,4,240,0,4)]
def g247A : List (List Nat) := [[],[33]]
def g247D7 (j : Nat) : Nat := 0xc3802a02feb9c217bdc910
def g247D8 (j : Nat) : Nat := 0xa1843e70e286014d2c386040d149206103b278a18052cc1c61030a13ac36014b2871850838603891038602111a40fc571985400ff4c7fd21ff8c3fd30ff843fd10
def g247H8 (j : Nat) : Nat := 0xe00007
def g247D9 (j : Nat) : Nat := 0x2c3948311804ff
def g247H9 (j : Nat) : Nat := 0xb0000000000038000015e332000000090000000000000000a4000001000000000000007d00
def g247L : Nat → Packing
  | 7 => (2,2,5,0,0,5,0,g247D7)
  | 8 => (6,1,5,0,0,9,0,g247D8)
  | 9 => (1,0,5,0,0,0,0,g247D9)
  | _ => emptyPacking
def g247I : Nat → Nat → Option (Nat × Nat)
  | 8 => lookupWord 1 5 0 5 1 0 g247H8
  | 9 => lookupWord 2 37 0 8 3 1 g247H9
  | _ => fun _ => none
def g247 : Forest := ⟨247,9,fun i => g247Y[i]?.getD (0,0),g247C,g247A,g247L,g247I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g247P7_0 : block g247 7 0 1=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g247P7_1 : block g247 7 1 1=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g247B7 : block g247 7 0 2=true := (@block_merge g247 7 0 1 1 g247P7_0 g247P7_1)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g247P8_0 : block g247 8 0 6=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g247B8 : block g247 8 0 6=true := g247P8_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g247P9_0 : block g247 9 0 1=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g247B9 : block g247 9 0 1=true := g247P9_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g247T : checkedTables g247 9 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g247 0 0 0 = true)
  · exact (rfl : block g247 1 0 0 = true)
  · exact (rfl : block g247 2 0 0 = true)
  · exact (rfl : block g247 3 0 0 = true)
  · exact (rfl : block g247 4 0 0 = true)
  · exact (rfl : block g247 5 0 0 = true)
  · exact (rfl : block g247 6 0 0 = true)
  · exact g247B7
  · exact g247B8
  · exact g247B9
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g247G : graphValid g247 (boundsBefore K239) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low247 : Lower true (varsX 247) (graphGoal 247) 10 := lower_forest (g:=g247) (i:=0) (hints:=1163919361) (before_sound K239 V239) g247G g247T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K247 := extendKnown K239 10 [(247,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V247 : Known true K247 := extend_ok (m:=247) V239 low247 (by decide +kernel)
def g251Y : Array (Bits × Bits) := #[(0xffdd06a91099d48a9a43332c000000001fffff,0x1406000098c4829a42002444891224489122),(0xffc84181c926533d23f3a7ab0000000000007f,0x4a484181c926133d21b1a78bbb76eddbb76edd),(0x0,0x0),(0x159516e6b006b9c95d0c1000007ffe03f80,0x130151510a0100280495d04122448912244891),(0x38632b3a1407d5640cfe900003f8001fc000,0x9c28212b3a0003456408f6801a3468d1a3468d),(0x6a65e8bc2aa6263a0248efffc000fe00000,0xe002860a81c20242620020880c183060c18306),(0x8b9a4e4bcb285c13a447501fc07f0000000,0x828a4643cb085812a0434d1a3468d1a3468),(0x6754920534ad14b5cf8813fe03f800000000,0x4550900434ac1091c70813e1c3870e1c3870),(0x0,0x0)]
def g251C : List ColumnInfo := [(2,0,249,0,9),(0,2,248,1,8),(16,0,235,0,8),(64,0,187,0,8),(128,0,123,0,8),(1,0,248,0,7),(1,2,248,0,7),(8,0,243,0,7),(32,0,219,0,7),(144,0,107,0,7),(0,16,104,129,6),(0,64,147,40,6),(0,128,75,48,6),(2,16,104,129,6),(16,2,232,1,6),(18,0,233,0,6),(1,16,104,128,5),(3,16,104,128,5),(8,2,240,1,5),(8,64,147,32,5),(10,0,241,0,5),(16,128,75,32,5),(17,0,232,0,5),(17,2,232,0,5),(32,64,147,8,5),(32,128,75,16,5),(64,2,184,1,5),(72,0,179,0,5),(80,0,171,0,5),(96,0,155,0,5),(128,2,104,1,5),(128,16,104,1,5),(160,0,91,0,5),(192,0,59,0,5),(9,2,240,0,4),(40,64,147,0,4),(48,128,75,0,4),(65,2,184,0,4),(74,0,177,0,4),(104,0,147,0,4),(129,2,104,0,4),(131,16,104,0,4)]
def g251A : List (List Nat) := [[]]
def g251D6 (j : Nat) : Nat := 0x2c4040b10100010c1000e081e0810000386041922c20000000000000000000000000043040000ba5bad162ae55aa14aa24fa7132914721906803c1d4e46a3117cb85928910823e1d8e06a32178b05226118803a1a0b85022090300c00a3fcb307baa8517f985d87550aa7f28bb0eaa161fe1b755cd428bf4c0eab9a8587f861d57350b0ff0dbaa86a145fa60755c142cb7c10eab82855f193e057010b66b092a4a498dd964a5494931dcbc2286a926337698215424c76af0aa1a8498e5de177250931f932a4a4a1263f2554549424c6bcf24aa6e690e5de17735092193fcab05322c166f92596525832bf0bb9a84b047be61721c940b56cb0e4a128172d951c942502b592eb1284a065b217825d1209bbcab05324215e592a1172842aef2ac22e508579e49845ca10cbac3acb2942176792596528432eb0f2a4a5086cd6125494a10bb2c94a9294213b79461952843b4ae7a1485084dde558650a109bb4c10aa1421977855cd428432ef0ab9285087c99525250a10f92aa2a4a14218f5865cc428432eb0ab98850867c5cd8010a10
def g251D7 (j : Nat) : Nat := (if j<1 then 0x772d0931bf58590931bf58490931fd54390931fe55290931bf78550931f778550931bf58550931f748550931fb65450931fb55450931fd54350931df77250931fe65250931fe55250931bf58510931bf78259121bf58695121df654dcd21df554dcd21bf78250d21bf78458921ef56458921bf586d0921df773d0921bf58650921df77350921fe56250921bf7844c921aff8259560afd8599160afd8299160ddd54dcd60aff8558960e7d6594960ddf7394960ddf7354960ddf7390960b7f8550960ddf73509609fd82dd950b7d8695150def7258950b7f86549509fd82dd9409ff825d940bef825d540bec825d540bbf8459540bbd849c940def729c940b7f855c940afd861c940b7d851c940ded721c9409fe87989409fd8798940bbd8498940bf980989409ff87589409fc87589409fe87949409fd8794940bbd8494940bf98094940bbd8490940def7290940bf98090940f3f8550940f3c8550940faf7250940fac7250940fae6250940fad6250940fae5250940fad5250940b7f8550940def7250940fb94258140faf4290930b7f8550930afd8610930b7d8510930bf98010930bed829d120d7f855d120d7c855d1209ff825d120def825d120b7f855d120bef825d1209fd8799120bf980991209fd8795120bf98095120bfb80589209fd87d0920bf980d0920b7f8550920feb8250120fe88250120fbb4250120fb94250120bf78459610bf78259610bf58599210bf58299210bf78559210ef56559210bf78259210bf58695210bf58295210bf78655210bf58655210f756555210bf78255210df6545ce10df5545ce10df5865ca10df5855ca10df5655ca10df6845ca10df5845ca10df6645ca10df5645ca10df6545ca10df5545ca10bf58598a10bf58498a10bf78558a10ef56558a10bf78458a10ef56458a10df57258a10bf58694a10f756594a10bf58494a10f765494a10df57394a10bf78654a10bf58654a10bf78454a10f755454a10df57354a10df57254a10bf586d0a10bf585d0a10fb554d0a10df573d0a10df572d0a10bf58690a10bf58590a10bf58490a10df57390a10fe56290a10fe55290a10bf78650a10bf58650a10bf78550a10f778550a10bf58550a10f748550a10fb65450a10fb55450a10df57350a10df57250a10fe66250a10fe56250a10fe65250a10fe55250a10bf58610a10bf58510a10df57310a1097f855ca64b6f8259652d3d7495252b6d82952529bf845d95297f855d94297e871d542f2e5494942f2d5454942df3815c042dd543dc931fa74290931b778550931af58610931b758510931bf18010931be78255121af78650d21b778550921d3f74951509ef825d54097f855d32097f855d1209f58798a109f58794a109f58790a10fa74290a10b778550a109f58710a10af58610a10b758510a10bf18010a10 else (if j<2 then 0x4184104986131010186080000010c1008e0d1010088080050c1c0a0c02402011c1a18343040000008e080010c107028200860804304021820004304860d0c1a18201101218243040000b44a183814284e11c0c48818e004e92221c31c00f8013082749e00613a4f00309f0020e86e0fc0109603e009c460b020e182913060f884823e0b0c2f1305860c8e15246184e211f0448c30a48e26084426181a16030c1e030c10638013c309c0c30507e06183e06182005248e180015432388000511c3246008f81130181081580238648c011f0221230380238814c091c3a84d3c69b34c1a54d2468f3461a24d0c683340a9f94fb27cd3d79db4e7a7313779b44d8a6953329964c525f92db961caae539284936495248b23f91848864372038fa47723891b58d3465e3111798ac4502251119880c3a61b50b9855429212b07d82e413608f04180bc045ff2fd87e4bf0df68f937c6bdf9ea8f4579fbcc1e54f2478abc19dcaed6763bae1d64eac7533a5dcfee79739b991cbce4f71bb87dc0edef6ebb721b72daa6cdb60dac4d536993445a04cf3676b37999ecb764fb21d8bac4e61fb0e5842c095f8af89794bb25d1ae516f8b5b5a1ac89626b0457aab995aeabf5582a85524a8c53ea9b94aca3e517a8814109f04ec270133e9874b3251525a91547ea3b91888ac445a1cd0b68314112028ff67e33e59eccf5a79e3cc1e24f067743b71da0ec475c3ab1d1ce707293919be4dc26db3619aacd386963439a04cf66753379980cb464b31e18d8c4e62130d97e8be85e52ef9740b825b22d61698b4059a2c59614afe5702ac1548a8653d29714a0a3251328693f89de4e0268932c9784ad24f126092445f21a902c7d43d21d88e406f034e1920c0c5c42af14709904622070fc075c37e1950be857028812307c836015c09603a812c0420009fd84dc1659fd82dc1659ff825c2649fd80dd5649fd80dc964cfd65dc1649fd82dc1649ff825c2549fd80dd9549ff805d954d7d65dc154cff76551439fd80dd562aff8059562aff8059162cfd65dc1629fd84dc1629ff805da52b7d8695252aff8650e52d7d655c252d7e545c2529fd80dd9529ff805d952aff8650d52dbf7450d529ff805da42aff8650e429fd80dd9429ff805d942d7d86dd542d7d83dd542d7d80dd5429fd80dd542d7d76dd542d7d761d542d7f7559142bbd8095142aff865cd42d7f755cd42d7c755cd42aff8650d42d7f7550d42f6f7558942f6c7558942fad5458942d7f7558942bbf8458942d7f755c142d7c755c142df9835c042df581dd1329fe8795132bef8255132dbf74d0932b7f8550932dbf7450932bf58295131bf78255131fd55450d31df654dc931df554dc931bf58494931f765494931fd54394931bf78454931f755454931fd54354931df77254931bf585d0931fb554d0931df else 0x40184010004010004010004010004880184010004010004010004010004880205430402000800006082c08030c0200080c1e070018101000200080200080a200820080028460700180400100400131016230826031820031821082051010382007288151018460c2a25082a2034404260d101060225a0d003a0d002600882000201000581010582070581c0060a040c0834461840a61a08361820000f6250e02200482384486250c3a182010c10511e0418043041e486240442182010c10002182430490c4a187430486090c100001860a1d8610001201020e084c86141e86150c9010500210130416081c102c307040e0850150e83400e86086683400f0581c00743040608004060e082c06100400161b80102f0d43e00805040e08186e00586e00586e004c3040200080200080a081c10080020580c32180400102c02000c16082c103838604000c1f0c141c10383860400c828b0436180b0186084608641c06182c06182c06182c06182016010c182082161807c00c1786e006010004231105c0c3042204160300800403a18205804001a181610310c102c06010008860701860982084582101e0c14180e100440402182010c100000000900e0416182007820c461081a61840))
def g251H7 (j : Nat) : Nat := 0x249b6f61002c500000fafc2000a910c00ba3d3540c4519580004ac8b92a000017fa6f7800001110b12e0025a2525cd5659983cde2c006bf65f306ad384115b240000032000d9c00277971b4000008f00387003e3120260a8421c860
def g251D8 (j : Nat) : Nat := (if j<1 then 0x3168c373090c0d2fb8bdb2f30bb92e58b772da0b452cb8b172bc0ad92ae8a9729f0a6d2958a3f28b0a1d28189eb27509b5267898b258094d24d891f24108e923488b7228088521a885320d082520587ff1f907cd1ef87af1e6077d1da87471ca070d1bd86e31b206b11a68687199064d18b861317f05d516b859715e055514c850713904c1129849711f046110f841b10003dd0ee83970dd034d0cd83130bf02e50b382af0a40275097823f088020107881c3069018d05d815304f011903d80df02f00a50238077019004d00b80170001ff59154ffaa8a1fff7558bfeaa2c5ffdc162ffac9297fd4394bfeb22a5ff50d52ffac4a97fd6490bfea1c85ff5d942ffac8a17fd7350bfea1a85ff58942ffae0a17fe544cbfeaa265ff54932ffe84997fd424cbfeaa2c1ff94960ffaa4b07fe42583fea12c1ff59150ffac4a87ff76503febb281ffdd540ffaeaa07fd65503feb2281ff55140ffee4a07fe72503feb9281ff1c940ffcc4a07fd62503ff29281ff54940ffc84a07fd42503ff2a261ff55130ffca4987fd524c3ffa1261ff90930ffa84987fc424c3feb2641ff5d920ffaea907fd65483ff3a241ff5d120ffcc8907fd64483ff2a241ff55120ffac4907fd52483ffa1241ff50920bfee8b2dff72596ffb82cb7f5d664bfae5325fd70992ffbaac9bf59564bfee4b25ff70592febb4a97f5ca54bfae12a5ff76552febb2a9df59554bfee4aa5ff70552ffba2a77fdc953bfaeba1dfd72d0effbaa877fdc943bfaeb315fd7498afeb84c57fdd562dfacab15ff7458b7eb22c57fdc162bfaed2977d6594afeba4a5df95252bfae1295ff7654afebb2a57fdd152efaa8a95ff7054afebb6857f5d742f7aa9a15fd70d0afebb4857f5d642bfae9217ed6290bf6a94857f5c242bfeeca15fd7650affbaa85dfdd542bfaeaa177c7550bdf2a285ef55142fdcc4a17ed6250bf729285fb54942bfee0a15fd7610afeba8857f5c042bfaeb195fd748caffbaa657fdd132feca898ff5544c7fb29263fd54931fee8498ff6424c7faa1263fd10931feaca90ff664487fab2243fd95121feaa890ff553487fba1a43fd50d21feac490ff552487fba1243fd50921fea6490efd655837f322c1bf58960bfeeca85fd76543beb2aa17fdd150efca8a85ff72543bea92a17f5db40bfaeba05fd72d03dea16817fdd940bfaeca05ff75502febaa817fdc940f7e84a07bd42503fcb0281fe54140bfaed905fd75c82feba6417fdd920bfaec905ff75482febaa417fdd120bfae8907f950483fca0241fd59610fecc9087f564843fb2a421fd55210fecc5087f562843fb29421fd54a10fee85087f642843faa1421fd10a109feeca1ddd7398bd7a14855fdd5429faec2157d7510aeeb98857e5c0429faed197d5434c6fbb92637ddcd21bbee6b05dd73d02fab9c217d5ca10 else (if j<2 then 0x8e1816100781128c38382e0248c8b810e9230206050282418160038c1380910e1860504020100e04191120b803292362860402c189e0248c11898030362040583e0138a18140805808c4e3a4e0061009803a26181e00e8988140806043380308c405838281e006248f801636185028201810ce0119027800e923228c8c6021898a181408060427800e8c48602e024918a40160a0693803238605028201602189918d88078580463600593878d8985804628d8ce021898a2607804e260249186300f80923228e8c83e0218c0c320f8086302860502016023118e920f80184028460058d8810142789878580320e8c544838c08880e062712222808c4488898a0e021607122230523a1c4c3240c908e870d12287a421c344a38c908e87130c28523a1c4c3240c1e9087130c8e321a423c4c30a1e148691130c8e3a4c31186930c461c02191c3248a1a8884870c26303a189c3138a930c461a4c311868626930c1a2a409e183c3248c870c464c206a22109e183c324101a0e8886850c46389a421c324868d0c870432522c34124148827800f0c1232303e043248c8a1a30930c2628c432489881814090605810c46426e02443098a18140805810c463a683e00c43098c93810c1840286050402016021c3099214100806043380310c48ca6e043118a160e07810c1892386858381e024c30c901814080580870c2640c060503820121e0430994181408044787810c4110c8c26e0098443100e9a1180470c3030c94863223800c864630581e043248c8c18140805800f0c3040605020181604311901607810c9232314068581e024c30c901814080580870c304098605020160430c101814080605804644411060502010191e0431223800c864628c8c0988e004110310908e86930a2a3a1a442a48a908e870a92286a3a22121c2a40e1a908e8884870a3882421c2a4a38c908e870a92286a4222121c2a38e1a908e8884870a386a3a221a142a40e1a908886850a8e386a22121a423c28e20908886850a8e38f864461888a2787080e2228ce309e18403e4e0118c302793802906309e18a8403e0103236178d9211800e409e18403888a3227860f81921044409e18c83888a918614130c2a3e18783448a144c0c9220ce1c206c30a33883186101b0c387618285248b860a2592202da5167d59b965f593163158495fb57715c956c959b5631579559954f54d151d54094df53114a9522946b513142950393f34f613c14eb938b4de135d4cf93274c412fd4bb92d74ad129149f925b491122d48591fb47911c946c919b461116d453913744610fd43890cb42d109d421906f416104540b901f4020ff53f88fc73ed0f9d3e08f6b3d40f313c48efb3b60eb13a68e8339b0e5938e8e2b3870e0937e8de73750dc13688d8335b0d5134d8d1733e0ce13338ca73260c71 else 0x18083106205854221c10b0886181a18e89870880188c240c01006418c0c1689030106481438d85c1a2060a3616108906041438605a2418889030032402a240c005120a8640461a2418c90088886484622241a105120a190780100e8831121a011a30b03001687041430e8583a1c0c041051016150300870430403c0c005410c140e870300110438e85824140c00c8e8705030080185038d858221c140c00611050300805032321c140c0140c8c401807030030303c0c012898b0d80883221410088621432260110d8086302128e85c321e00c10870300324230390064022430a3a1700870c28403e043080f0d80191a19143600a220e88868411810c404222140a0c00388910300883220402c0a0c020218590870300363028403c020430a1087010c4628b0521c004430c87002c150c2a1c0200b05430c87002c150c28b054004430b00802c150c2a1c00b05430a888700802c150c3a2401006430a5022188489810c3928d85a1e0430c1887010c4226308a11160430a864645810c291224004430a890040190c2914021c3098a87003b0c2628640224308370026870c2c0114306448700470c2c4e01091898112424620403e044a3108d81123a2620281e044918a0e078031128c302a1e044898a181180861246306028191c4e0100e160e0781128c403a4c1e006100a140a0804330780264040503824181600ca312180b80924e28c02e024898a11803292262e3600e898818140805808c4e3880e11862226381a1c48889891222461c4a188898816062248244e00c0d880e0a062781123238401808009c4910e0a27811230283e021848c898c160b8781123230c09846003848c))
def g251H8 (j : Nat) : Nat := 0xb7008080012cbf6f80000d9a2b0000001c874d9b5c499d9290fb3350002935a58d40811a59a46f741b8e060784c15ad1f00f0065f692a544c6c3774fcc075a023698400000012c000011cc56f02fe3482ad433644c88432b09e304510894b144860f50c87f82b8e3000529493170e7020afe158000c057b948bb89d65390b000102a53fb14485147a0003c164068c6e198840116cff50a00838bde92676892ec24048c0f00010cdc3a02fb0ef61f40b488a4030b5870e6c33ca9748c204493c55c36a4f63a0598ec6ad40480015e0e40762309912028a02b8001168c4af4b59dd81ce010004a09954ae91138003047c3e21901c812f0312723aa184ac50c040b53110862667c9d114d2d33849abc43161c61fabbbc45113279fa1fd7bc71d0600d649befd536fac8073ef637389655180b024e2b57c7b67992e3b5a146cf43069be71b48b3073084f51a000c64b3778360e877f3430c0fc5ba7af8d318a000c2a6a45c8b507000423b87800026180021f0d0de498002049c80c75411dc35f060764001e04868624800281e211c5b00006160002588000001f0a36e4a194fca7bf2762f09406eba6f00c0001ceff3e8aba8c2a413321aa58a766e16d9a7a19d01756ba87640ce56f42fb3197c4f7868d2ef00b06b26430ba885629647ea66936712c5cd8b7df42c117e29d7dc40000000955d0801079c82e2b0182cba19158064a030100c54111309c2604070dc00030e010080b198884a180c8041e00000440a550a02812220687c0422070000006180a006030880c1404028404e0e048180023
def g251D9 (j : Nat) : Nat := 0x10880f181c0462480f1a1a3802048e2038c8d0d0401240d0e649c6920e008246880e763039301192203a3124450e62188124460e221892229910049c68700487244078d0ccc01238d1004c46920e007246880e6e303930119234c980f1a1c9802091a049888d0e4c00e4831a203c38d2602324c8d080c106271a1c9110039a20080270c3892240802003c312447101c1000c661a9212880f00883928c3121c119310219192203141e00886464861c00686344971844380451c90e188101e0434446486221890c1800f0e4861484392144c89836e7d8aa8b472764c38fd11e013bd6f0ccd7728d49e860ed195292448710a40cc12c11000ff597fe64ff593fe54ff553fd53ffd0ffd43ff98bfd62ff94bfd52ffd0bfe42ff50bfc42ff8cbfd32ff583fd50ffd03fd40ff4c3ff20ff483f531fd487f610
def g251H9 (j : Nat) : Nat := 0x19ddbc1d18c40007cb0c2f57d54e70b5d000000d7f0aec25772c639c99aa11760d8cf41eedeb46d3cd66696ba7d2813f20b7865247088713d5000810d4f622dd304b28af1401c62737e48cf7c0003ba91643e9765378856a40524a0000778774f4240f764184d6dda3523acd932943c5b4872dd145fd658d70e72d000373f81dbb73000061300000000000082b000000000758b927ad162080000000000000000000000fb9c34ac000000000000069b3d80950009180000002c3968641467000ba2b2100067a000fb5000ab019a4bd54d08e251020dc18a9439caf25f0002b2335bc8a8960200000042c76c01dfd999c26e947d38b77800ec521b5297d0983d618060000000005d2ddf00061fa5e00000008812e00005c000000401e36fca24a000d6f582da100000063d4440d4000953b15f98269e078934b3000891c75000b3a000c6a00049401a000a040003ce97b42f0c674efab379a99790e11eb69e0f33000d7d02ab5900004900060aa8f00000000000059f000000255000a656b7f5a0cc50c96bf095be4b40031a5000e40219ca6fdab3b98b0003b10000000000000000c70006976a8b9e1ac000edc01200004c000adb4604b80000000267500009d7b562485050000000005311bf0058f00381d68928480811309b09680028100184112018b146828b051810004040030612587000208d020420002003031b
def g251D10 (j : Nat) : Nat := 0x30648027f
def g251H10 (j : Nat) : Nat := 0xb400142000074c01e55766d494a9a4bc0131932d8d20031001242d41a5d7147aaaea6000002b001005580133cf011
def g251L : Nat → Packing
  | 6 => (48,4,6,0,0,9,0,g251D6)
  | 7 => (276,3,6,0,0,13,0,g251D7)
  | 8 => (225,2,6,0,0,14,0,g251D8)
  | 9 => (28,1,6,0,0,11,0,g251D9)
  | 10 => (1,0,6,0,0,0,0,g251D10)
  | _ => emptyPacking
def g251I : Nat → Nat → Option (Nat × Nat)
  | 7 => lookupWord 12 67 5 10 6 0 g251H7
  | 8 => lookupWord 69 307 9 13 9 0 g251H8
  | 9 => lookupWord 56 307 7 12 8 0 g251H9
  | 10 => lookupWord 7 41 3 9 5 0 g251H10
  | _ => fun _ => none
def g251 : Forest := ⟨251,10,fun i => g251Y[i]?.getD (0,0),g251C,g251A,g251L,g251I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P6_0 : block g251 6 0 48=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g251B6 : block g251 6 0 48=true := g251P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P7_0 : block g251 7 0 32=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P7_32 : block g251 7 32 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P7_128 : block g251 7 128 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P7_224 : block g251 7 224 52=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g251B7 : block g251 7 0 276=true := (@block_merge g251 7 0 128 148 (@block_merge g251 7 0 32 96 g251P7_0 g251P7_32) (@block_merge g251 7 128 96 52 g251P7_128 g251P7_224))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P8_0 : block g251 8 0 16=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P8_16 : block g251 8 16 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P8_112 : block g251 8 112 44=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P8_156 : block g251 8 156 69=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g251B8 : block g251 8 0 225=true := (@block_merge g251 8 0 112 113 (@block_merge g251 8 0 16 96 g251P8_0 g251P8_16) (@block_merge g251 8 112 44 69 g251P8_112 g251P8_156))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P9_0 : block g251 9 0 3=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P9_3 : block g251 9 3 25=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g251B9 : block g251 9 0 28=true := (@block_merge g251 9 0 3 25 g251P9_0 g251P9_3)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P10_0 : block g251 10 0 1=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g251B10 : block g251 10 0 1=true := g251P10_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251T : checkedTables g251 10 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g251 0 0 0 = true)
  · exact (rfl : block g251 1 0 0 = true)
  · exact (rfl : block g251 2 0 0 = true)
  · exact (rfl : block g251 3 0 0 = true)
  · exact (rfl : block g251 4 0 0 = true)
  · exact (rfl : block g251 5 0 0 = true)
  · exact g251B6
  · exact g251B7
  · exact g251B8
  · exact g251B9
  · exact g251B10
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251G : graphValid g251 (boundsBefore K247) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low251 : Lower true (varsX 251) (graphGoal 251) 11 := lower_forest (g:=g251) (i:=0) (hints:=1127219201) (before_sound K247 V247) g251G g251T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K251 := extendKnown K247 11 [(251,[]),(253,[33])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V251 : Known true K251 := extend_ok (m:=251) V247 low251 (by decide +kernel)
def g254Y : Array (Bits × Bits) := #[(0x0,0x0),(0x1d47107660ae0d7962d67a0000000000003ff,0x1545003640ae0d6962d632555555555555555),(0x788cef0c22e54e2166c974b0000000000003ff,0x7888af0c02e50e2160c0149aaaaaaaaaaaaaaa),(0xa7718744802f99c2ebe8a2d00000003ffffc00,0xa5510544002899c06ac8a0830cc330cc330cc3),(0xf1cd883b88b2c10e5394d9900000ffc0000000,0xe1cd88338882c10a43945190fc3f0fc3f0fc3f),(0x4c9b30805dcbae384956437fffff00000ffc00,0x8a308008c3240801044370300c0300c0300c),(0x6a64d6ea9e8415f7a432190003ff003ff00000,0x4a24c22a960400378432180cc330cc330cc330),(0x952a4f3b5578326d10e5b80ffc00ffc0000000,0x14204708553812651061a80f03c0f03c0f03c0),(0x0,0x0)]
def g254C : List ColumnInfo := [(0,2,248,4,8)]
def g254A : List (List Nat) := [[],[99],[33],[33,99]]
def g254D8 (j : Nat) : Nat := 0xff
def g254L : Nat → Packing
  | 8 => (1,0,1,0,0,0,0,g254D8)
  | _ => emptyPacking
def g254I (_ _ : Nat) : Option (Nat × Nat) := none
def g254 : Forest := ⟨254,8,fun i => g254Y[i]?.getD (0,0),g254C,g254A,g254L,g254I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g254P8_0 : block g254 8 0 1=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g254B8 : block g254 8 0 1=true := g254P8_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g254T : checkedTables g254 8 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g254 0 0 0 = true)
  · exact (rfl : block g254 1 0 0 = true)
  · exact (rfl : block g254 2 0 0 = true)
  · exact (rfl : block g254 3 0 0 = true)
  · exact (rfl : block g254 4 0 0 = true)
  · exact (rfl : block g254 5 0 0 = true)
  · exact (rfl : block g254 6 0 0 = true)
  · exact (rfl : block g254 7 0 0 = true)
  · exact g254B8
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g254G : graphValid g254 (boundsBefore K251) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low254 : Lower true (varsX 254) (graphGoal 254) 9 := lower_forest (g:=g254) (i:=0) (hints:=1127698720) (before_sound K251 V251) g254G g254T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K254 := extendKnown K251 9 [(254,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V254 : Known true K254 := extend_ok (m:=254) V251 low254 (by decide +kernel)
def g255Y : Array (Bits × Bits) := #[(0x36a04032000000000000000000ffffffffffff,0x4a04002204204204204204204204204204204),(0x640558b5000000000000000fff000000000fff,0x600518b14a94a94a94a94a94a94a94a94a94a9),(0x924a3507000000000000000fff000000fff000,0x924a2504952952952952952952952952952952),(0xa3c61ed0000000000ffffff000000fff000000,0xa3461a90183183183183183183183183183183),(0xea499c68000000fff000000000fff000000000,0xea091c6807b07b07b07b07b07b07b07b07b07b),(0xc0346709ffffff000000fff000000000000000,0x4020440901c01c01c01c01c01c01c01c01c01c),(0x410aa0c6000fff000fff000000000000000000,0x8a046e60e60e60e60e60e60e60e60e60e60),(0xc79a998fff000fff000000000000000000000,0x450a190f80f80f80f80f80f80f80f80f80f80),(0x0,0x0)]
def g255C : List ColumnInfo := [(2,0,253,0,11),(4,0,251,0,11),(16,0,239,0,11),(64,0,191,0,11),(128,0,127,0,11),(8,0,247,0,10),(32,0,223,0,10),(0,2,248,5,9),(0,4,248,3,9),(0,64,151,40,9),(0,128,79,48,9),(1,0,254,0,9),(0,16,110,129,8),(0,32,23,200,8),(1,2,248,4,8),(1,4,248,2,8),(8,64,151,32,8),(18,0,237,0,8),(32,64,151,8,8),(32,128,79,16,8),(66,0,189,0,8),(80,0,175,0,8),(160,0,95,0,8),(1,16,110,128,7),(8,32,23,192,7),(10,0,245,0,7),(16,32,7,200,7),(17,0,238,0,7),(40,0,151,0,7),(40,64,151,0,7),(48,0,79,0,7),(48,128,79,0,7),(64,32,23,136,7),(17,2,232,4,6),(24,32,7,192,6)]
def g255A : List (List Nat) := [[],[33]]
def g255D7 (j : Nat) : Nat := 0x6c5f80c6c3593e0be0fc0f8946c6900361dc3f4ca9aa0a06e1ba6e0d5354140
def g255D8 (j : Nat) : Nat := 0x18237442744d109d0a47713c2f07c3e1a8d1f4561346f019b158f12782f059bd1b45f118e2549f0746f03c4a6c6213c3d008cb18cac387e0945f07c4f0ec6c387f07c3233c43370e1bc0f0ec59351b17c1f03c3f124d46c654bc153746f0fc48398c2246c6cc9f06c5e0bc4c388f07c42630e2745f070ef109d13c2f060ef1090171b32685b1b42f03c41fc1f10606384a35c4f07c3f0a471b4032bc3f07c2860651fc1f0fc2f10591bc3f0bc4234591786327c2f07c4c386a18c9f07c2f130e188cf10d2c384337c1f0d0ef10971b82327c1b1bc4c386e0bc1f10d00845918c9e0bc1f03c4b147617c1f13c38385713c3f0647f085234c9f0bc1f105234c8f0fc2f105234c9f0bc1f10582880e7c278a72a6e869c65060e5d659453e4e84b048244a3fe3d038e34c30a2d229024e2201de19c1641180e00a8070038000be7e8d8550130fc7e155350130f7469c984c550d2fe1f9654d409af6839654d40da7e5b8354d40b6de9d854c540be5e8d854c540be5e95834c540f4ee1d5354140fc6e0d5354140fe460d3154140b8fe995354140be5e8d8550530fc5e155350530f96e4d6054130ba7e9953501309b56839654d31f5469c984c550b5c69c984c550ed4263834c550ed4261834c550b95e99834c550b95e99534c550ba5e99834c540be4e81834c540ba5e99534c540b8e69b8554140b8ee995354140fc4e4d4154130b5469c984c550b94e99834c550bd0e89834c550b94e99534c550
def g255H8 (j : Nat) : Nat := 0x7c06
def g255D9 (j : Nat) : Nat := (if j<1 then 0x1d1787c1e17101c181a8c85e0f0b89c3e00f46e0f0b880e480d46e0f0c1dc48c0d46e0f0f840ee206070df041dc44e8bc1e17101c5214298e24f0785c4a30e17e0f03891d178dc1e17101c191b87c149838302d0387c2e0f1030330f85c1e07128a303785c3e07128a37048fc2e270d1a32348fc1e1f0b88350385c1e1f1030311c81c2e270f828d1c1bc1e07138545190dc1e1f113029458bc1e1f111a321b85c1e1f111a321b85c1e1f111a370387c10692b840e1f8049e083785c4070fc00b86f87c1a31281c40878346e1f101c303b83c48e89c10770b881d168dc3e083b89851a8c85e1f0785c4070e0ec370b83c4151386e170788283b87c2e0f105e677227889bf6de1edfb673aebd53691b4039aaca9e43b16f872c125fa2f59779b9a5be2d55665b14d792b1b548a81d2d6905446a00cef270133b9844b0e4eb2308f1467629f11c874c2920ad01a7ef3e89ebaf0f7653a15c80dfb6dfb5c5a6acf065131997fabc15be2d0161aad1546291d4049cf4c9a5392248cd451a19d0327e63d51d94e526ed35419d4c845fd2e51638ab651f271929c8d642f1f98eb86e433f1818b1c51624610086cc2ee14d08d03781320660198003f7f0aa0261fbd8550130f3fc1ac0a879f60d60542f7b27c2a817bf9361540bdecaf06a06ef61783502f7f2ac1a81bbf8560d40edfc3aa6a07e7e0d53503f6b0a98a81fbb8354140fdcc1aa0a05efe4d50503e7aa6a82817bf9055130fafc2aa6987ede15414c3f6b0aa0a61fd7854c530feac2a62987d7e4d504c2fbf26a8261bbf8550130ddec2a80987e754d404c3f72a0a02612fd90e1953bdac9f0aa0ded65783507f2f06a9a837b79055131fabc2aa698f2fe5d54582d7f20aa2c1f70984c550b3fcb306a87cde0d41543e6b06a0aa1f57834c550faac1a62a87ec26141543f6726a0aa1fd0984c550b3fcb2a6a86ede0d41543e6aa6a0aa1bd7834c550faaa9a62a85af65b85502b7f2ec2a819bf8761540bcfc9b0aa06e761783502b7f2ec1a816bf9660d40bddc8306a05afe5953503f2b0a98a81f95834c540fcaa9a62a06afe156050357b0ab0281dbb8754140f9dc2aa0a07e6e0d50503f3106a8281f395354140fd898aa0a07ae5815050377308a84616df9654d30ddbc2a82986ed615414c3f2aa6a0a61bd7854c530deac2a62987e5551314c2ef32b28261f5b9354130f3cb02a0987ec505504c3fa262a8261eb96050130d6bc370a98db5e59534c6d7720aa2c12f4984c560cdcc3b09286dc61531942cf72cc1aa176b9260d50fa9cc262a87d426131543ea70698aa1f51834c550b3dcb2a6a87cce5541543e62a6a0aa1f53954c550fa8a9a62a855e65e50542cf32d282a15b99794140fc898aa0a07ac505604c3da262b0261f314154130fa898aa0987944c560d435a30c98ca1b51854c650 else 0xa2439309d101f0e46d1186c14e8e8dc370785c48714070790f85c1e22361c1d2387c1e2160422d1b83c0e1f118a171d8d45e0f0f884d108fc06303383c3e251442470787c0a2f109a171c36532914383c0e1f1044172ab884a37068bc3508e0c229728dc1e0713869b251e9f637078745e2230424d1b81c1e1f1042581c36532970781c3e2161184e0a37c12c43b885d1f871bc17049bc48717480c05f83c4474746e1f0781c4e107464c707890e4e8a8fc2a6389c18727470c70785c487074647b0f85c1e2438301d228dc1e170f8885870fc1e1077890e0c0d42e0c6d1b0ee227474420e851be0c391bc44e93c3a170637c0e227470db1b83c3077113038270dc1e161789c01011c1e270e1c58168bc1e270c9b0e188a91a370787c4470e5e0b93783c44747470cf0b87c426a3860bc4b07c129f00b0385f83c44747452070f83c20c710b23b0f0c49e0f0a8bc4e0108dc331783c3e243874ea3d8bc1e1f111b0e230c45e170787c4870e1d47f0b83c3e22361c470f83c428a605e0f0f88514c0a9323f0b83c3e2234724c1b8345e17138020211bc1e1b17890e191bc3e0f121c9d1b85c1e1f121c18188bc3e0f0b881d870e1506e0b8346e214042401383c3a312b80171c2dc0e0d1819c3108ec5e0d1b81c3e205c70df058dc3e07102e38128bc3e005ca6330f040ce0d1781c42911c3e0f038817110d82e09268dc0a2f10747a7d8dc1e1f11190e218dc1e1f121c8c199a45c117119216370787c4871743e0707890e4c0c9fa1f0383c4872607a370383c3ac0846e0f0f8858108b82e0f0387c40d8c0ee0f0f81c40d96070df0787c062f109a3d181dc110f0f88581c37c107710ba2f0437c30771230341493c1e051b89c21f8385e1f111b0e191185e0f0f888d870fc1e24393a270787c2e22361c322511c2e0f13870e4691c10c7121c)
def g255H9 (j : Nat) : Nat := 0x1b002898110700281c281900152b2cda0029d78508a800064000000005614e834140000034ed100146b0c05b5f4c57800d3c000000015400c0000b719ff5ac20000092310004
def g255D10 (j : Nat) : Nat := (if j<1 then 0x3048ba10c0de360e1c2e20714098381863c3030f0386e28be0c361e2601582130d81890b843a2a360e1e208870e8c8b838788221c388e1c760e22e8c8d838785881c361608ee2070c8d01871d83883a3038061c760e1620e8f0684be2f8381883a4086160e209070d8385881c3a2e0e162070e8b8385881c3a2e2e061e0e109870e8783841d883032160e187620c0c218387850d888a1c462e061e08543610711830d8588201c303600c61e0e162071180190d838635881c406e160e06261a28f85838189868a1a3c361e0e16222870f0d8086a18385881c422e0e161e260068e8a810d838785883044c4362e0e1e2070f0d838785881c361e0e162070c0d8c09818b8386423a360e061e20c0c3f8381878830360e1e0620d8a301d83878188363c10c6310e0e1a2e207128705802e378388ba1c48fe00b8de0e1a36207121a16048d83878188b04c2e16209070b838785890a1c306860de0e1c2e207118385881c3a28ec2e1e0e162070f8d0b8387881c302e360e1e162070e17838189843a305a361e0e16260429086a58583881c341e0e24e870b07258583881c360e1c362070b830d87881c2e0e0620e8983810d882028c61e160e0620d830d87881c2e0c361e2070a30808f878583888a44362e1e0e2070d0d878583881c3074360e261cc0d1a1d858389870c390c16360e1e2070e8f878583882dcc2db5694b235842b9557ca9b53e2965474a134f4272534c9834a824c521c8ef46822b511c86f42c21050347fb3ea1ea4f1c7633a21c94e0c6eb3681ad4d2c67732a18e4c4460b2fa1754b7459f2be1564a7c51b27c136497449b23c116486c4171fe0f847843a71c60dd46ac32f1840b845742a3144099449c22f10a07d43b41b70ce06142d415309e04a42240f7070032414c08b038015406c0170003ffe1530ffd854c3ff54130ff7854c6ff60e50f7f83543df60d50bff83543df54d50ff531543bf58150fbf85503ef61540fbf83503ef60d40fbd53503ef54140bfd858c3ef55230ff9508c2ffe1530bfd854c3ef55130fdd534c3bf58130f7f504c3fe94130f7d504c3fe54130fbd404c36fe1d54bbf80552bfe1953fb785507ede0d41fb553507f5e1531ef7864c7ed55131fd5534c7af55160ef781583bd4c560f7531d439f58350df987943be61a50fb984943fc4c6509fd87942bf61a50b7d85942ef61250f7b83543de60d50f75315439f58150f7953543fc4c550fb541543f54c550f7a505436fe1d40bbf85502ef61540f9f83503e720d40fb531503af58140fba50503ee54140afd868c2df61630bbd848c3be58230f79508c3ed50530fd5314c3be58130f79504c3b5e1931eb541583b54c560f3541d43d54c750e7960d42be61a50b7985943ec50650fd131943dc4c550f3541543d54c550fb141543f44c550f9531503d44c550 else 0x1871783818984303a407c2c5e1e0e062610c0e950b87838588301c3a40c802360e1e162070c13838785881c30306c360e161e06222901e3b85828b8987801a4e1a2e0e062610e8c1187838189841a3a3c322e0e1e162070c111a878389841c3a386e062c160a361e210921e3e8a308d838781882e5606360e1e222908e368d828b8781882e4060de1c160e0622e902e1b808b0436b183868d881c660e1e142e207068e3e1b078381883a2e40360e1e162070c0f87838189841a3a38461e0e06261068e9187178381883a303e185e0e062610e8f8385881c3a2e0e162070e8a38210a8d838785881c4a360e1e16242870e160a8d8387818984)
def g255H10 (j : Nat) : Nat := 0x2808000018c800000000b400000003a001638000000000000051400000000000001428000000021800000000000000000000000000000000000000011800000000000004ad00000000000da8f64000000000018b000000000000000000000000000000000000000000000000000000000000000000000000000000000000000c800c4800000000000002d580000104611800000000000001dc000000000000000029b7000000000000093c0025100095800000000000000000010f40000000000000000000000000002c49b0000000017a48f000000f240000000181c89800472000a68000000000038600000000000a9000000000000000000000000029600000000000000000000000000000000000000113000000000000002bb00000000367000000000000000000000000000000000000000000000000000000000000000000000000000000000039380000000000000000000005260000000000087d9864942a0000000000000000000000d817911e6ce001089b78000000000000000000000000000001b8800000c3800000000000001700000000000000000000000000001458000000000000032e000000000000000000000192800000000000002280003a00062e0000000000000000000000a66000000000000000000000000000000000000000000000000000000000000000000000000000000000000057000000000000efc000000000000050f00059717860000000000000000000000014a00000000000000000000000006e56d00000000000001f08006db001ed80000000000000000000000007440000030180000000000000000000000a100000000000000000001b50000000038dc86000000000000000000000046000000000000000000000000000000000000345c2a00000355000680db800000000000000000002f800001670000003a40000023100000000000001a240000000000000566000000003ea00000000000000002608000000020f80000084000000000e30000004a74680000000000000000000003a5800000000000003bcb6800000000000002a90011afee9588680000000000000000488875d5c00000e08003816e3c28000000000001100045c21c
def g255D11 (j : Nat) : Nat := 0x5c383022423a3c08b043438510710605c5830e0440d0890d042c3890870e2e34181121858440283121c0307c70118741890e10520583830a2403a38b8a1a0c287120101a0c287022181c5868b061c2890088a1a0c28712018205828d160c3811088d14741890c68c3a0c2890c68b0e14181106d8f25b82a99ae347d9bf6054a430ce240600c000ffaa7ff943fea87fe30ffa61ef553fa98efd60efea1fe943bea87f950f7a81ed507ea98f7950
def g255H11 (j : Nat) : Nat := 0x4a000000000000005d7e79d280030300000000288898eef2071a60b8074dc192b8d380000f7730969ad2a67c003658000000000041c70c000e93a7cb5299dc4c686171ea2000826f668b000953d4f2f411f3c44a6c38a8926da570006b705c002900018fc0054502b9052410b29a0000040c77aeca11b84000d5204c2f468a006ee42667757e8f9d60e00000414c44e080052d0a000270421087ab12b73ac3e8acd05b111d2928c03781b73c006df105003f4049c3810156c3105040104201140
def g255D12 (j : Nat) : Nat := 0x185043084007ff
def g255H12 (j : Nat) : Nat := 0xc700000000001a0000000000a4260200e0003b00003c0000000000000083000000000000000000c90000580000ef000000dd15f15e0002
def g255L : Nat → Packing
  | 7 => (2,5,6,0,0,7,0,g255D7)
  | 8 => (34,4,6,0,0,12,0,g255D8)
  | 9 => (114,3,6,0,0,13,0,g255D9)
  | 10 => (97,2,6,0,0,13,0,g255D10)
  | 11 => (16,1,6,0,0,10,0,g255D11)
  | 12 => (1,0,6,0,0,0,0,g255D12)
  | _ => emptyPacking
def g255I : Nat → Nat → Option (Nat × Nat)
  | 8 => lookupWord 1 3 0 5 1 0 g255H8
  | 9 => lookupWord 8 53 4 10 6 0 g255H9
  | 10 => lookupWord 28 587 2 11 7 0 g255H10
  | 11 => lookupWord 24 127 6 11 7 0 g255H11
  | 12 => lookupWord 4 59 2 8 4 0 g255H12
  | _ => fun _ => none
def g255 : Forest := ⟨255,12,fun i => g255Y[i]?.getD (0,0),g255C,g255A,g255L,g255I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P7_0 : block g255 7 0 2=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g255B7 : block g255 7 0 2=true := g255P7_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P8_0 : block g255 8 0 4=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P8_4 : block g255 8 4 13=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P8_17 : block g255 8 17 15=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P8_32 : block g255 8 32 2=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g255B8 : block g255 8 0 34=true := (@block_merge g255 8 0 17 17 (@block_merge g255 8 0 4 13 g255P8_0 g255P8_4) (@block_merge g255 8 17 15 2 g255P8_17 g255P8_32))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P9_0 : block g255 9 0 3=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P9_3 : block g255 9 3 25=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P9_28 : block g255 9 28 57=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P9_85 : block g255 9 85 27=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P9_112 : block g255 9 112 2=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g255B9 : block g255 9 0 114=true := (@block_merge g255 9 0 28 86 (@block_merge g255 9 0 3 25 g255P9_0 g255P9_3) (@block_merge g255 9 28 57 29 g255P9_28 (@block_merge g255 9 85 27 2 g255P9_85 g255P9_112)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P10_0 : block g255 10 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P10_1 : block g255 10 1 16=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P10_17 : block g255 10 17 50=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P10_67 : block g255 10 67 27=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P10_94 : block g255 10 94 3=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g255B10 : block g255 10 0 97=true := (@block_merge g255 10 0 17 80 (@block_merge g255 10 0 1 16 g255P10_0 g255P10_1) (@block_merge g255 10 17 50 30 g255P10_17 (@block_merge g255 10 67 27 3 g255P10_67 g255P10_94)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P11_0 : block g255 11 0 3=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P11_3 : block g255 11 3 8=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P11_11 : block g255 11 11 5=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g255B11 : block g255 11 0 16=true := (@block_merge g255 11 0 3 13 g255P11_0 (@block_merge g255 11 3 8 5 g255P11_3 g255P11_11))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P12_0 : block g255 12 0 1=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g255B12 : block g255 12 0 1=true := g255P12_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255T : checkedTables g255 12 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g255 0 0 0 = true)
  · exact (rfl : block g255 1 0 0 = true)
  · exact (rfl : block g255 2 0 0 = true)
  · exact (rfl : block g255 3 0 0 = true)
  · exact (rfl : block g255 4 0 0 = true)
  · exact (rfl : block g255 5 0 0 = true)
  · exact (rfl : block g255 6 0 0 = true)
  · exact g255B7
  · exact g255B8
  · exact g255B9
  · exact g255B10
  · exact g255B11
  · exact g255B12
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255G : graphValid g255 (boundsBefore K254) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255R : Impossible true graph 12 eightInputs.toFinset := by
  rw [show graph = targetOf g255 by decide +kernel]
  exact root_index (g:=g255) (top:=12) (i:=0) (before_sound K254 V254) g255G g255T (by decide) (by decide +kernel)
def mo255Y : Array (Bits × Bits) := #[(0x36a04032000000000000000000ffffffffffff,0x4a04002204204204204204204204204204204),(0x640558b5000000000000000fff000000000fff,0x600518b14a94a94a94a94a94a94a94a94a94a9),(0x924a3507000000000000000fff000000fff000,0x924a2504952952952952952952952952952952),(0xa3c61ed0000000000ffffff000000fff000000,0xa3461a90183183183183183183183183183183),(0xea499c68000000fff000000000fff000000000,0xea091c6807b07b07b07b07b07b07b07b07b07b),(0xc0346709ffffff000000fff000000000000000,0x4020440901c01c01c01c01c01c01c01c01c01c),(0x410aa0c6000fff000fff000000000000000000,0x8a046e60e60e60e60e60e60e60e60e60e60),(0xc79a998fff000fff000000000000000000000,0x450a190f80f80f80f80f80f80f80f80f80f80),(0x0,0x0)]
def mo255C : List ColumnInfo := [(2,0,253,0,11),(4,0,251,0,11),(16,0,239,0,11),(64,0,191,0,11),(128,0,127,0,11),(8,0,247,0,10),(32,0,223,0,10),(144,0,111,0,10),(0,2,248,5,9),(0,4,248,3,9),(0,64,151,40,9),(0,128,79,48,9),(1,0,254,0,9),(6,0,249,0,9),(1,2,248,4,8),(1,4,248,2,8),(2,4,248,1,8),(4,2,248,1,8),(8,64,151,32,8),(16,128,79,32,8),(18,0,237,0,8),(20,0,235,0,8),(32,64,151,8,8),(32,128,79,16,8),(66,0,189,0,8),(68,0,187,0,8),(72,0,183,0,8),(80,0,175,0,8),(96,0,159,0,8),(130,0,125,0,8),(132,0,123,0,8),(160,0,95,0,8),(192,0,63,0,8),(3,4,248,0,7),(5,2,248,0,7),(7,0,248,0,7),(40,64,151,0,7),(48,128,79,0,7),(70,0,185,0,7),(104,0,151,0,7)]
def mo255A : List (List Nat) := [[],[33]]
def mo255D5 (j : Nat) : Nat := 0x80977b0db2a0965cd9154d50
def mo255D6 (j : Nat) : Nat := 0x6305097365b66c4a85cd5354224bbb85c12cb9b22a9aa1425cdb2a0965cd9154d50
def mo255H6 (j : Nat) : Nat := 0x9
def mo255D7 (j : Nat) : Nat := 0xc17fc1fc0ec72241685fb1c2ab54295449f4e2652c9348235148742204fc7b3c1d4e46f361a4cc6330174b4572a1449c4b24114843f1e0e46c331803c0083bdc46e8852418150e92f329976595420143a53cca65d955508050e56d32d975519120143b3e1c22a1a1640535064e7710ba5959320141e25da66956564c805068cf710ba6556320141d25db66cd9558c805078976a56558d5320141c2bdb66d1a914c80507c935956354d9220141933dc42e976654804c64d770cba5d99520131a33dc42e9955cc804c70d72e9b3655732013183bdc42e9955cc804c68be301a82999550d21c53db7694a0650835431cd695b12819420d50ca5db66c4a85cd53542997325b62a17354d50ca5dcb2a0965cd5354239772ca82597354d508b5ccb2a173645535434972e0965cd9154d50e25ca8259736455354309f2e0a66859550d50d25c986d88354d715428b770c986988350550da1db66108354d41542bc670ca95514154130af19c42a5534c5504c37c4551b12814354130c7e1966c8a0645434431f8655b22819150d10c7e0956c8a0645434433e8591b22819150d10cfa1546c8a06454344316b6ddb46a45320910c7a9b46c1a914c82443f905956354d2148110a25cc96d8a85cd5354229772ca82597354d50
def mo255H7 (j : Nat) : Nat := 0x994007400c9d
def mo255D8 (j : Nat) : Nat := (if j<2 then (if j<1 then 0x2fac5cae6a9aa0985f99b42614354130deb152d2a86a8261f962d9a550d504c3bcc4c328a1aa0987f19a56514354130fe3152aa286a8261fc66e15450d504c3f8c4c2a8a1aa0987f19b15514354130deb34ad0a86a8261fc6551a150d504c379c54aa8a1aa0987f19b35514354130fe32a8c9a86a8261bd62a55350d504c3f8cca2a6a1aa0987f195450d9154130fe32a8a1b02a8261fc665143545504c3f8caa286a8aa0984fd9b32a541541309ef36a54282a8261bce2a554505504c379c542a8a0aa0984fb9b42a53154130deb152a9a62a82617d66d5434c5504c3f8caa28698aa0987f195450d2154130aeb972b9aa6a82617d66d4a050d504c3f8caa140a1aa0985fd1b12814354130bf336052a86a0261fc66d543541404c3f8ca9a86a82809869bca76819561030a77972d2b08b8061acf2a5a5611500c3c9e5bb4ac22a0186b3da76958454030e67b2ed2b08a8061ece6d5845c1500c3d2eb2b08b1aa68862fda82999550d10c5f9505332aa1a214ef2e585551434431fa5432cc8a868863f4a86559150d10c7e9504ab22a1a21aed2a164645434435da542a8c8a868867f1962819150d10cfe32a50322a1a219fc254a0645434437d8b2140c8a86886fb1542819150d10f4bacab1aa6c12215bb6e4a654c82443f26b2ac6a99048865edb76a45320910cddb6cd48a6412219eb6d1a914c824433f4d835229904887e556558d5350510cfe172d00a6a0a21bec6d1a014d41443f2ab2ac6a9a42885d5db724d5354110bcbb6c49aa6a82215d72e57354d50443f8caa286a8260887e596558d5348110fbc2ecbaa42902217f86dd6548520443f70bb2ca90a40885fe1b65512148110ff42c8aa24290221f785d97348520443ef0baae690a40885fe1b758d2148110fdc2cab1a42902217f86dd5348520442ff0db2a690a40887ee0b654d2148110fec2caa9a4290221ff05cd5348520443fe0b1aa690a40885fe1b714d2148110bfc36c29a42902217f86d05348520442ff0db28690a40885fe1b550d2148110ff42c8a1a4290221fe855143485204425d6d9140c8b0829d3e9b22a19014d41a2fb6e51b2a4028349f6d8a36548050699eda146ca900a0d1ddb72959320141a5bb6c52b26402834e76d0a564c805061deda35229900a0e17da76545320141c4fb4cca8a6402838cf655a414c805070eed3b2629900a0e2dda664c5320141c73b48c98a6402838de655a014c805071ecc9b4029900a0d1edb714d9220141a5db6c29b24402834eb6d053648805069f4d80a6c9100a0e7e1a26859014d21c4f9504b328a9aa1a976998420d5354352edb150b9aa6a86a5ca82597354d50c4f9504b322a9aa18cf695a42614354313e5414ccaa86a85e59b620d535c1509fc36450322a1a217786dc5348520442f70db0a690a40885fa1b414d2148110 else 0x1c5fb505332aa1a434fe2c198655434869fc583304aa8690dbb8b06616450d21b77160cc2a8a1a438bf2a096645535c353e5414cc9aa8a8733cb86959420d50ea796ed2b2841aa19cf69da56508354399ec3b4aca106a853bcb86859420d50c77b50d0b2841aa19cf695a165083542adedb940ca106a8673da52819420d50af6b625032841aa18bf699a12617354333e5412cca2a6a8727ca82599454d50dcbb0ed3106a9aa1b976998420d535435aed8950b9aa6a86e5db62a17354d50dcb9504b2e6a9aa18df2a1976455354333e5412cc8aa6a8637ca86519154d50b6b970b9b22a9aa1ad72a17364553543b2e4b2e6c8aa6a85b5cb85cd9054d50e67b68d2930a1aa1ccf695a4261435431ded23424c286a8637da56809850d50ce7b4ad2130a1aa1acf695a42614354333e5414ccaa86a8727ca82999550d50a6f970d0b2aa1aa199f299a16554354359eda150caa86a86a7ca82999550d50a6fb6a4c32aa1aa19cf6e8985514354399eda930aa286a85b3cb86555450d50e67930aa306a1aa18df661a5241435431be4c34a48286a863f5986849050d50c7e930d0920a1aa19dd655a12414354379aaa34248286a85d5db720d5360550bcbb6c41aa6c0aa15d72e57354d81542dae5c2e6a9b02a8673ca95514360550c7b93051b0cb8aa18bf261a620d715431de4c34841ae2a8735c9820d535c550bcbb6c41aa6b8aa10ff2e4a850d515431ee4c146c3282a85b9cb36198450550ae7b664c2a8a0aa17c72cd86551415429eed993041a82a862fc986988350550c77930d2106a0aa13cf6d5a420d4154355ed330841a82a86e3da65508350550bcbb6c41aa6a0aa1ec76108354d415431dedbb484c262a863bdb3690984c550c77b4ed213098aa14ef6d09861d315429deda130baa62a853bdb4261834c550a77b684c2e698aa15cf6d09854d31542dae5c2e6a9a62a85d5db720d5348550bcbb6c41aa690aa16d72e17354d2154379cdab4841ae0a86e78a6685535c150beb166c32a2b82a179e6d88354570542f9cda106a8ae0a84fb9b42a1315c1508f7972d2106b82a17976d88354d7054379c542a8a0ac0a853dcb36599161540c5f9504b322a9a818ef2a5a1615435025deda950c8a86a063bca86599150d40c77950cab22a1a818ef2a095645435025de5d30ac8a86a06b3da56149050d40cf6b2ad0920a1a81aed615a124143502dce59b4cc2a82a07e1d6558d535054087fb66d293098a817976d89354d5050317e53342cc2a8986f99b46809550d309f3b60d210aa1a615f66c095645434c378eda34a48286986d9da75909050d30de3b4ab2120a1a61bc769554241434c37cab234248286986f95546849050d30c5f9525330ab8a618bf2a4a6615414c31de4c34842a82985dd9b72814358130beb36a50286b02617f46c4a050d604c) else (if j<3 then 0xf9dac2b28c8900a1f5b5975919120143ee6b2ab2322402875ed6e5546448050fadacbaa8c8900a1f6b5965519120143ee6b2aaa32240287cf9619926448050f9f2c2b24c8900a1f3e4856499120143ef4ac8c932240287de9551926448050f1be5d32ac0100a1f3b5546458020143a5fb6c51b2a402e34ef6d0a3654805c717e5b352a9900b8d2fdb92995320171c5fb52532a6402e3c9f2999554c805c796e53326a9900b8f35d6564d5320171e6bb2ab1aa6402e3e975956354c805c79ceaa326a1900a8f3f0a86859014d41ef6348d0b2029a83f875956354d4250793e5b346ca900a0e37da668d9520141a6fb6c51b2a402834bf6d8a3654805069deda146ca900a0f2dcb66959320141c7bb4cd2b26402834f76d8a564c805069eedd2cac9900a0d3dcba5959320141e5bb4cb2b2640283cd76956564c805079cedd2a8c9900a0f39db65519320141e73b4caa32640283ce76955464c805079ceb2aa8c9900a0d1fdb72959320141a5fb6c52b26402834ef6d0a564c805079ced9aa8c9900a0e37dba6556320141c6f974caac640283c9f6d99558c805079aed9b2ab1900a0f27d955956320141e5bacac9ac640283ce75519358c8050717e5b352a9900a0d2fdb92995320141c5fb52532a6402838df6999554c8050793e5332aa9900a0e37da95955320141c7bb4cc9aa640283cb72999354c805079aeb2b26a9900a0f39d5464d5320141c7bb52b1aa640283cd76556354c80507d2eb2ac6a9900a0e2fdb66a45320141c77b68d48a6402838df6999514c805071eed332629900a0f3adb65519220141e75acaaa32440283ceb6cd5464880507976b2ac6c9100a0f3ad5458d9220141a7db6ca9b2440283cbb2d953648805079b6b2aa6c9100a0f3ad5454d9220141e79ac6a9b24402834fb6d853648805069be5d2ecca90098f17da75d99520131e4f96cd1b2a402634ef2e976650804c78de5bb4aca10098e3bda76959420131a77b6e52b28402634ef6e975650804c69de5d2eaca10098f33da55d59420131c77b4ad1b28402638df2e995590804c799eda32ab210098e37dba6557320131c6f974caae640263c5f6dd955cc804c79aed9b2ab990098c3fcba6557320131a7bb66caae640263c5f655755cc804c71dedd328b990098e3bcba6517320131e37aeaca2e640263ce76cd945cc804c79aed9b2ab190098e3bdba6515320131c77b4eca2a640263ce76517354c804c71bedd32aa190098e37cba6554320131e67b68caa86402630ff6e99550c804c61fe5d32aa190098f33d955514320131e3daeab9b24402634fb6dd53648804c79e6b9aa6c910098d3edb550d9220131e75aa8a1b2440263cb7660965cd53487d2eb2b08b1aa690d3f8ba6119014d21e77348c232029a43df8689a1640534869fc58330cb28690d3f8b06a19550d2 else (if j<4 then 0x78c72c6cc66c60c5ac54c4ec48c42c3cc36c30c2ac24c1ec18c12c0cc06c00bfabf4beebe8be2bdcbd6bd0bcabc4bbebb8bb2bacba6ba0b9ab94b8eb88b82b7cb76b70b6ab64b5eb58b52b4cb46b40b3ab34b2eb28b22b1cb16b10b0ab04afeaf8af2aecae6ae0adaad4aceac8ac2abcab6ab0aaaaa4a9ea98a92a8ca86a80a7aa74a6ea68a62a5ca56a50a4aa44a3ea38a32a2ca26a20a1aa14a0ea08a029fc9f69f09ea9e49de9d89d29cc9c69c09ba9b49ae9a89a299c99699098a98497e97897296c96696095a95494e94894293c93693092a92491e91891290c9069008fa8f48ee8e88e28dc8d68d08ca8c48be8b88b28ac8a68a089a89488e88888287c87687086a86485e85885284c84684083a83482e82882281c81681080a8047fe7f87f27ec7e67e07da7d47ce7c87c27bc7b67b07aa7a479e79879278c78678077a77476e76876275c75675074a74473e73873272c72672071a71470e7087026fc6f66f06ea6e46de6d86d26cc6c66c06ba6b46ae6a86a269c69669068a68467e67867266c66666065a65464e64864263c63663062a62461e61861260c6066005fa5f45ee5e85e25dc5d65d05ca5c45be5b85b25ac5a65a059a59458e58858257c57657056a56455e55855254c54654053a53452e52852251c51651050a5044fe4f84f24ec4e64e04da4d44ce4c84c24bc4b64b04aa4a449e49849248c48648047a47446e46843640f4094033fd3cb39936734b34533f3393072d52a329d26b2392071d51a318716b14f1120eb0da0d40b809105403801c000bcbb6a51b2c402e77a76d0a3658805cf17e4334848302a9f2dc865cc9060553c5f92c50322c2a87c9f259a52418550f17e4b3424830aa1cf9db32819155143977b68d010ac0a878df6e1a52418150f1be5c34a48302a1e37d866949060543ce7b68d2920c0a870ff2e1a52418150e1fedd10a48302a1e37da52149060543ce7b4ab2120c0a879cf695542418150f1f6c334448302a1e3ed856889060543c7d90ad1120c0a879eb591a22418150f3d6aa34448302a1f27cb668d9520143e6bb66caac640287c3f2a1976588050e9be5c34cca900a1d37cba6199520143e2f950cbb2a40287c9f2e1966548050f93e5432cca900a1f17d976199520143ea7b2ed232a40287d8f659a46548050f87ecbb2cc2900a1f17d976558520143e4fb2ccab0a40287ccf2e1956508050f8decbb0aca100a1f33d956159420143ea7b2ecaac84028736f2e9975508050f2ded4b2eaa100a1f4bd976595420143ea7b2ecaaa840287d8f659955508050f97a5b30ac8900a1d3f5b02159120143e76b0aaa32240287cbd2e1966448050f8facbb0cc8900a1f374b86559120143e6eb0ccab2240287dcd6d1956448050f8facbb0ac8900a1f2f5966159120143e6eb2ac2b2240287cdd65485644805 else 0x199c1be26c01323782f00180001830e3782f00260c38de0bc009830e2182f00250cf0010000143163782f00250c58de0bc00943162282f0020043a63782f00260c38de0bc009830e3782f00260c38860bc008838e3782f002588b0016c78481224b8e1417f83f0363a24150bec7b861c24040e8f70c214985fa387f0dc08c9911d1c5d11a002d11a002d11a002e16e10e0ae04dfedf8df2decde6de0ddadd4dcedc8dc2dbcdb6db0daada4d9ed98d92d8cd86d80d7ad74d6ed68d62d5cd56d50d4ad44d3ed38d32d2cd26d20d1ad14d0ed08d02cfccf6cf0ceace4cdecd8cd2ccccc6cc0cbacb4caeca8ca2c9cc96c90c8ac84c7ec)))
def mo255H8 (j : Nat) : Nat := 0x3caba162129e94b9d11ee062b923b41621d580ca5486f0d22552c001871863010908948a0000032909459a266d3204b12000003a813800282d2279400089c180000004f80032f81d7400d001a478f00000100c41000c160016c0001c28030050800c31c1
def mo255D9 (j : Nat) : Nat := (if j<7 then (if j<3 then (if j<1 then 0x985cd50adf2a19754d50adf2a19454d50d9f2599454d50ed76108354d50bd72a17354d50f972597354d50adf2a17354d50adf2a19154d50d9f2599154d50cdf6949850d50cef6909850d50cdf2a19550d50d9f2999550d50adf2a19550d50dcf2615450d50cef2615450d50af728d8660550a7f69c8360550abf6988360550aef6908360550bd728d8654550b5f69c8354550b9f6988354550bcf6908354550dcf26154505508ff690984c550cef690984c5509ef690984c5508ff2a5874c550bf628d865c150bbe698835c150bee690835c150bfc684835c150f9e299535c150fd620d535c150fd658d535c150fce55141581508ff6819850c50af728d9661540cbf6609654d40f975956354d40cef2a58550d40aef2a19150d40b6f69c9050d40baf6989050d40bcf6949050d40bed6849050d408ff68c9854540aef6a05350540b6f69c5350540baf6985350540bee68053505408ff694984c5408ff2a5854c540de764d4314140cbf65c9661530cbf2599461530cbf2599161530cbf2999855130bf66809550d30be76908550d30b7769c9050d30bb76989050d30bd76949050d30bf56849050d308ff69098545308ff2a58454530fd65cd5354130fd66954354130fe66514354130fe65514354130bde6954354130fce5514354130fd654d4354130fd650d5154130fce5514154130fd65513154130fd654d3154130fc75514354130de765143141308ff6a19550130de76554350130fe650d6050130fe650d5050130e6f29d9561030cef65d9561030aef6a57561030aef2a57561030ecf6557561030e6f69d845c030cbf65d8654030cdf65d8554030cef65d8454030ecf6958454030adf6a15454030e9f6195454030ecf6115454030cfd65d8154030edd5518154030ebe6197054030ede6157054030eee6117054030efc6057054030cbf6199550030cdf6558550030cef6558450030cfd65581500308ff2a5855cd10cbf6609654d10f975956354d10cef6a19414d10ded6859414d10c7f65d8414d10cbf6598414d10cef6518414d10cfe6119014d108ff2a58550d10afd2a19150d10bfc2819150d10a7f69c5360910abf6985360910aef6905360910afe68053609109fb6a45320910b7b69c5320910bbb6985320910beb6905320910bfa6805320910b7d69c5350510bbd6985350510bed6905350510bfc6805350510b7d69c5348510bbd6985348510bed6905348510bfc6805348510b7e69c5348110bbe6985348110bee6905348110ff85d92148110ff85d52148110ff85952148110ff85912148110ff85512148110ff85cd2148110ff858d2148110ff854d2148110ff814d2148110ff850d2148110ced5519120143ce75519320141ceb5519220141b5769c8354d50b976988354d50ad72a17354d508ef690984c550fc65514354130 else (if j<2 then 0x3cdf6999520143cdf68d9520143cdf6556520143c7f65d6320143cdf6556320143cfd5959120143cfd58d9120143cfd54d9120143d3f65d9620143c7f65d8620143cdf6199520143dcf6919520143d5f65d9520143d9f65995201438ff6a48520143cdf6548520143d6f65d9420143dcf6559420143d6f65d6420143dcf6556420143dcf6555420143cfd6199120143cfd6159120143cfd2159120143ded5919120143ded5519120143d7d65d9120143dbd6599120143ddd6559120143ded6519120143df96499120143c7f65d8020143cbf6598020143cdf6558020143cfd6458020143f975956354d718ff6a55320171cdf6555320171cf764d53201718ff6a55420161cdf6555420161cef65154201618ff6a54320161cef6514320161cf764d43201618ff680985cd518ff6809850d51cef6516420151cf764d7320151cf764d63201518ff6a54320151cef6514320151cf764d4320151cbf6609654d41f975956354d41cfe6a19014d41cfe2a19014d41dee6919014d41dfc6859014d41b6f69c5350941baf6985350941bee6805350941cdf6999520141cdf68d9520141cdf28d9520141cdf6556520141cf76999320141cf76959320141cf72959320141cf75959320141cef5519320141c7f65d6320141cdf6556320141cf764d63201418ff6a55320141cdf6555320141cf764d53201418ff6a45320141a7f69c5320141abf6985320141cdf6545320141aef6905320141cf764c5320141afe6805320141cfb5959220141cfb58d9220141cfb54d9220141cfb14d92201418ff6909854931cdf69d9520131cdf6999520131cdf5d99520131cdf6919520131cdf68d95201318ff68d9520131cdf6557520131cdf6556520131cef69d9420131cef6999420131cef5d99420131cef6959420131cef2959420131cef5d59420131cef5959420131cef68d9420131cdf6556420131cef65164201318ff6a55420131cdf6555420131cef6515420131cdf6557320131cef6517320131c7f65d6320131cdf6556320131cef6516320131cef6515320131cdf6554320131cfb5d99220131cfb5d59220131cfb5959220131cfb5919220131cfb5519220131cfb5cd9220131cfb58d9220131cfb54d9220131cfb50d92201318ff2a5855cd21cbf6609654d21f975956354d21cef6a19414d21c7f65d8414d21cbf6598414d21cef6518414d21cfe6a19014d21cfe6119014d21dfc6859014d21afe2819850d218ff2a58550d21f975956354d708ff68c98545708ff694984c5708ff69098545608ff690984c560cf761c9361950af728d8661150bd728d8655150bcf2a16455150adf2a19355150cbf61d9620d50cef61d9420d50dcf6959420d50cbf6598420d50d9f6595420d50dcf6515420d50cfd61d9120d50cfd6119120d50ddd5519120d50cbf698 else 0x99150d10dfd6559150d10dfd2559150d10fed5919150d10fed5519150d10e7f5d97560910aff69d6560910ebf5d96560910aff6995460910eef5915460910e7f5d97360910e7f5d57360910aff69d6360910ebf5956360910aff69d5360910aff6995360910ebf2995360910edf5955360910ef75cd5360910ef758d5360910aff69c5360910aff6985360910aff6905360910aff6994360910aff6954360910eef5914360910eef5514360910f7b5d97520910bfb69d6520910fbb5d96520910bfb6995420910feb5915420910f7b5d97320910f7b5d57320910bfb69d6320910fbb5956320910bfb69d5320910bfb6995320910fbb2995320910fdb5955320910ff35cd5320910ff358d5320910bfb69c5320910bfb6985320910bfb6905320910bfb6994320910bfb6954320910feb5914320910feb5514320910fed6995450510fed5955450510fed68d5450510fbd5956350510fed5516350510bfd6995350510fbd2995350510fdd5955350510fed5515350510ff558d5350510bfd6985350510f7d5d5734c510bfd69d534c510ff55cd534c510bfd695434c510fed551434c510f7d5d97548510bfd69d6548510fbd5d96548510bfd6995448510fed5915448510f7d5d97348510f7d5d57348510bfd69d6348510fbd5956348510bfd69d5348510bfd6995348510fbd2995348510fdd5955348510ff55cd5348510ff558d5348510bfd69c5348510bfd6985348510bfd6905348510bfd6994348510bfd6954348510fed5914348510fed55143485109ff2a573581109ff2a54358110bf728d9654110fcf5915454110b7f69c9354110bbf6989354110bef69093541109ff2a57354110f9f2995354110fd724d5354110fd758d53541109ff2a54354110bdf6954354110fcf5514354110fde55160541109ff6a45350110b7f69c5350110bbf6985350110bef6905350110bfe6805350110def6554350110dbf299954c1109ff6a5544c110fe7591434c110fe7551434c110ff650d604c110fde551504c110fde54d504c110ff650d504c110f7e5d97548110bfe69d6548110fbe5d96548110bfe6995448110fee5915448110f7e5d97348110f7e5d57348110bfe69d6348110fbe5956348110bfe69d5348110bfe6995348110fbe2995348110fde5955348110ff65cd5348110ff658d5348110bfe69c5348110bfe6985348110bfe6905348110bfe6994348110bfe6954348110fee5914348110fee5514348110fd75cd5348550fde54d215c150fd75cd5354110fde54d70541109f768c9055163abf2818721953cbf2189061153eb72197360553cbf2189060553cef6499161053aef2819161053cef6459061053efa2899160053cfe6499160053cbf2599161543cbf2599061543cbf25890615439ef69190215439df69490605439fb688906054)) else (if j<5 then (if j<4 then 0x30efe61d8154130fde5518154130fde54d8154130ff650d8154130bfe2a57154130bfe2a17154130fde54d7154130fde2615154130fde65d5154130fde61d5154130fde6515154130fde6115154130fde5cd5154130fde50d5154130bfe2a15154130fde6155154130fde5d55154130fde5515154130ff650d5154130bfe2a54154130bfe2a14154130fee6514154130fee5514154130fde54d4154130ff62613154130ff665d3154130ff661d3154130ff65d53154130ff66513154130ff66113154130ff65513154130bfe2a53154130fde5513154130ff664d3154130ff65cd3154130ff650d3154130fde5512154130fde54d2154130ff650d2154130cff6919854130cff6a58454130cff2a58454130edf6a15454130aff6a15454130edf6155454130cff61193541309ff2a57354130edf6115354130fd75cd5354130df76a54354130df72a54354130fd76954354130fe76514354130fe75514354130ff628143541309ff2a54354130bdf6954354130fcf5514354130df764d4354130fd754d4354130fde54d7054130df76a54314130cff6a19550130aff6a19550130ebf2998550130cff65585501309ff6a55350130fe72a54350130fe76994350130fe76594350130fe76194350130fe76954350130fe72954350130fe76554350130fe72554350130fe76154350130fe72154350130fe75954350130def6554350130eef6154350130fe758d4350130fe754d4350130fe750d6050130fde54d5050130fee50d5050130aff6a15050130fe750d5050130edf6819461430eef69d9561030eef65d9561030eef6819561030aff6819561030cff6619055030ebf6199055030edf6159055030eef6119055030efd6815460430eef695845c030ebf65d8654030edf65d8554030ebf6199454030edf6159454030eef2a58454030eef69d8454030eef65d8454030edf6958454030eef6518454030edf6a15454030efd65d8154030efd6518154030ebf6199550030edf6558550030eef6958450030eef6558450030efd6558150030cff6619655110eef6616455110cff6619355110e7f5d5835cd10ebf5958458d10cff6619754d10dbf65c9654d10cff6619454d10dbf2599454d10cff6598454d10ebf2598454d10edf5958454d10cff65d8354d10ef76617354d10fb72597354d10fd75957354d10ef760d7354d10ef76116354d10dbf2599054d10def6819414d10cff6598414d10dfe6919014d10aff6949850d10cff6619650d10cff2619650d10cff6a19550d10cff2a19550d10dbf2999550d10cff6619550d10cff2619550d10cff6609550d10cff2609550d10aff2a58550d10cff6558550d10eef6616450d10eef2616450d10eef6a15450d10eef6615450d10eef2615450d10eef6155450d10cff6558350d10eef5518350d10dfd65 else 0x5c9661530ebf2999461530ebf2599461530cff65d9161530ebf2599161530cff6519161530dbf65c9661530ebf61c9661530dbf2599461530dbf25991615309ff6819421530ebf2999561130cff6599161130cff6559161130cff2559161130ebf2998561130cff6859855130dbf2999855130ebf2999855130aff2a19155130cff6619155130bf72a19650d30bf72a19550d30fb72999550d30bf76809550d30fb72998550d30fe76a15450d30fe76155450d30fe76855450d30fe76815450d30bf72a19150d30df76599150d30df76559150d30df72559150d30fe75919150d30fe75519150d30bf76949050d30fe75909050d30fe75509050d30cff6a19550d30aff6a19550d30eef6a15450d30fe768d5450d30b7f69c9050d30bdf6949050d30bfd6849050d30aff2a17660530e7f61d7660530ebf2998560530aff69c8560530aff6908560530aff6a17560530aff2a17560530aff2a16460530aff6a15460530aff2a15460530fe75914360530fe755143605309ff694985c530cff261865c530cff2a5855c530ebf299855c530cff261855c5309ff6909858530cff2618758530cff2a58458530cff2618458530df72a54358530df72614358530cff69c9854530cff69098545309ff69098545309ff2a58754530cff2618754530cff2618554530cff2617554530cff2a584545309ff2a58454530cff2618454530aff6a15454530cff26154545309ff2a57354530cff2617354530df72a54354530df72614354530fe755143545309ff2a54354530cff26143545309ff6949850530cff2618650530cff2a58550530ebf2998550530cff2618550530cff2608550530bef6908550530eef6a15450530def2615450530eef6155450530bf72a1764c530f7761d764c530ef761d854c530fb7299854c530bf769c854c530bf7690854c530bf76a1754c530bf72a1754c530bf72a1644c530bf76a1544c530bf72a1544c530aff6a1544c530ef7615734c530f775d5734c530bf769d534c530bf7695434c530fe7551434c530ebf2998548530aff6a15448530fe75914348530fe75514348530ebf299855c130ff66854358130ff650d8158130bfe2a17158130bfe2a14158130ff661d3158130ff66113158130ff650d2158130df72a54358130ff62814358130bfe6909854130dfe2619454130dfe2a58454130efe2618454130fde6a15454130fde2615454130fde68d5454130fde6855454130fde5519354130bfe2a57354130fde65d5354130fde61d5354130fde6515354130fde6115354130ff66a54354130ff62a54354130ff62614354130ff66954354130ff66854354130bfe6a54354130bfe2a54354130fde6954354130fee6514354130ff664d4354130dfe2619154130fde5519154130fde54d9154130ff650d9154130efe26181541) else (if j<6 then 0x150bf728d865c150bbf698835c150bef690835c150f9f299535c150fd720d535c150fd758d535c150fde681535c150fde6855458150fde5518158150bfe2a17158150fde61d5158150fde6115158150bfe2a14158150fee6114158150fde5512158150aff6819850c50cff6619050c50eef6119050c50ef760d9050c50ebf2999361540cff6599161540cff64d9161540cff24d9161540bf728d96615409ff6819321540dbf2999854d40dbf6609654d40aff2a19154d40cff6619154d40dbf2599154d40dbf2599054d40cff6859814d40dfe6859014d40bef6949850d40bef2a19650d40bef2a19550d40def2619550d40faf2999550d40bef6809550d40eef2a58550d40eef6558550d40eef68d8550d40eef6858550d40def2a58550d40eef2618550d40bef2a19150d40def6599150d40def6559150d40def2559150d40eef6159150d40eef6159050d40bef6949050d40def6549050d40eef6149050d40aff6988560540aff68c8560540aff6a16560540aff2a16560540aff6988360540aff6948360540aff6a16360540aff2a16360540aff6a15360540aff2a15360540aff6a05360540b7f69c5360540bbf6985360540bef6905360540bfe6805360540eef6194360540eef61543605409ff69498585409ff68c9858540cff2a58558540cff2618558540cff2618358540def2a54358540def2614358540cff6989854540cff68c9854540cff28c98545409ff68c98545409ff2a58654540cff2618654540cff2618554540cff26165545409ff2a58354540cff2618354540cff2608354540cff2616354540cff2615354540def2a54354540def2614354540eef6154354540eef6998550540eef68d8550540eef28d8550540eef6198550540bef6988550540bef68c8550540bef6a16550540bef2a16550540eef6156550540eef6198350540eef6158350540bef6988350540bef6948350540eef6148350540bef6a16350540bef2a16350540eef6156350540faf5956350540bef6a15350540bef2a15350540bef6995350540faf2995350540eef6155350540fcf5955350540fe758d5350540bef6a05350540bef6985350540cff698984c540cff694984c540cff294984c5409ff694984c5409ff2a5864c540cff261864c540cff2a5854c5409ff2a5854c540cff261854c540cff260854c540cff261654c540cff261834c540cff261634c540cff261534c540def261434c540eef615434c540aff6a05348540b7f69c5348540bbf6985348540bef6905348540bfe6805348540eef6154348540def2a54358140bf728d9654140bbf6989354140bef6909354140bdf6948354140edf6a15354140f9f2995354140fd724d5354140fd758d5354140def6a54354140def2a54354140fcf6954354140fcf54d4354140def6a54314140ebf6 else 0x6949850d50def6909850d50edf6949850d50eef6909850d50cff6609850d50ddf2a19550d50ddf6859550d50ddf2819550d50cff2a19550d50edf2a19550d50ddf6619550d50ddf2619550d50f9f2999550d50aff2a19550d50cff2619550d50def2a58450d50eef2618450d50fcf6558450d50fcf6615450d50fcf2615450d50fcf6855450d50def2615450d50eef2615450d50fcf6555450d50cff2618350d50ddf6558350d50eef6118350d50fcf5518350d50ddf2615350d50fcf6115350d50aff2a19150d50cff6619150d50cff2619150d50ddf6559150d50fcf5519150d50cff2619050d50ddf6559050d50fcf5519050d50cff6609050d50cff2609050d50bdf6949050d50ddf6549050d50fcf5509050d50bfd6849050d50bf728d8660550aff2a17660550aff2a16460550fcf5915460550ebf2998360550aff6908360550b7f69c8360550bbf6988360550bef69083605509ff2a57360550aff2a17360550f9f2995360550fd720d5360550fd75cd5360550fd758d53605509ff2a54360550aff6a14360550aff2a14360550bdf6954360550eef6114360550fcf55143605509ff68c985c550cff261865c550bf728d865c550cff261835c550cff260835c550bbf698835c550bef690835c550ddf261535c550f9f299535c550fd720d535c550fd758d535c5509ff6909858550cff2618758550cff2618458550ddf2615458550bdf2a17654550bdf2a16454550f9f2998354550bdf6908354550bdf2a17354550bdf6a14354550bdf2a14354550fcf61143545509ff2a54354550aff2a14354550bdf6954354550fcf55143545509ff68c9850550cff2618650550bf728d8650550eef6198450550fcf6995450550fcf6195450550fcf68d5450550def2615450550fcf5955450550cff2618350550eef6118350550fcf5518350550cff2608350550bbf6988350550bef6908350550eef6108350550fcf5508350550fcf5516350550ddf2615350550f9f2995350550fcf6115350550fd720d5350550fd758d5350550fcf5515350550cff69c984c550cff690984c5509ff690984c550def690984c5509ff2a5874c550cff261874c550cff261754c5509ff2a5844c550cff261844c550ddf261544c550cff261544c550cff261834c550aff2a1734c550cff261734c550ddf261534c550fd75cd534c550aff2a1434c550cff261434c550bdf695434c550fcf551434c550bf728d8648550fcf5915448550b7f69c8348550bbf6988348550bef6908348550aff2a17348550f9f2995348550fd720d5348550fd758d5348550aff2a14348550bdf6954348550fcf5514348550fbe299835c150fde685535c150fde54d815c150bfe2a1615c150fde619515c150fde60d515c150fde20d515c150fde58d515c150bfe2a1315c150fde54d315c))) else (if j<11 then (if j<9 then (if j<8 then 0x141aff6985320141eef6119355131aff2a19255131aff2a19055131eef6a15450d31cff69c9854931cff6909854931cff2617554931cff26154549319ff2a57354931cff26173549319ff2a54354931cff2614354931f775d5734c931bf769d534c931bf7695434c931fe7551434c931cff69d9520131cff6919520131cff68d9520131cff6557520131cff6999420131cff6959420131cff2959420131cff5959420131cff68d9420131cff6a55420131cff6555420131cff6557320131e7f5d57320131cff6516320131aff69d5320131cff6515320131ef75cd5320131aff6954320131cff6554320131eef5514320131cff6619655121eef6598455121eef5958455121eef6616455121cff6619355121eef6119355121e7f5d5835cd21ebf5958458d21eef6115458d21cff6619754d21dbf65c9654d21cff6619454d21dbf2599454d21cff6598454d21ebf2598454d21edf5958454d21eef6115454d21cff65d8354d21ef76617354d21fb72597354d21fd75957354d21ef760d7354d21ef76116354d21dbf2599054d21def6819414d21cff6598414d21dfe6919014d21cff6619650d21cff6a19550d21dbf2999550d21cff6619550d21cff6609550d21aff2a58550d21cff6558550d21eef6616450d21eef6a15450d21eef6615450d21eef6155450d21cff6558350d21eef5518350d21aff2a19154d70dbf2599154d70dbf2599054d709ff68c9858570cff6989854570cff68c9854570cff28c9854570cff2616354570cff698984c570cff694984c570cff261654c570cff261634c570cff261534c570aff2a19155160cff684985cd60cff6849850d60aff2a19150d60cff2619150d60cff2619050d60b7f69c9050d60bdf6949050d60bfd6849050d60cff69c9854560cff6909854560cff69c984c560cff690984c560aff2a17348560aff2a14348560df761c9361950bf728d9661150bf728d8661150bdf2a19655150bdf2a19355150edf2a19355150f9f2999355150bdf2a19155150ddf6599155150fcf5919155150ddf64d9155150dbf65c9660d50ebf61c9660d50dbf2599460d50ebf2598460d50f9f2595460d50dbf2599160d50dbf61d9620d50def69d9420d50def61d9420d50def6859420d50def6819420d50def2819420d50ddf6959420d50dbf6598420d50dfd61d9120d50dfd6119120d50cff684985cd50dbf698985cd50cff261835cd50bdf2a19754d50f9f61c9654d50bdf2a19454d50edf2a19454d50ddf2a58454d50f9f2598454d50fd728d8454d50fd761c8354d50fd76108354d50bdf2a17354d50fd761d6354d50fd76116354d50bdf2a19154d50ddf65d9154d50ddf6519154d50fd75cd9154d50fd75cd9054d50dbf2999850d50ebf2999850d50cff6949850d50cff6849850d50cff6809850d50ddf else 0xf65d9620143e7f65d8620143d7f65d8620143ddf6999520143ddf6199520143ddf68d9520143def6919520143edf2a19520143ddf6599520143edf6199520143fcf6919520143aff6a19520143d7f65d9520143dbf6599520143e7f65d8520143ebf2998520143ebf6598520143edf6558520143edf6548520143aff68085201439ff6a48520143ddf6548520143ddf6556520143def6559420143eef6159420143f6f65d6420143fcf6556420143bef6a55420143f6f65d5420143faf6595420143def6555420143fcf6555420143eef6155420143d7f65d6320143ddf6556320143ddf6555320143dfd6199120143dfd6159120143dfd2159120143dfd5959120143dfd58d9120143dfd54d9120143cff6199120143cff6159120143cff2159120143def5919120143def5519120143dfd6599120143efd6199120143dfd6559120143efd6159120143efd2159120143fed5919120143fed5519120143cff6558020143eef5518020143d7f65d8020143dbf6598020143ddf6558020143dfd6458020143dbf2599254d71dbf2599054d71cff6999520171cff68d9520171cff28d9520171cff6999320171cff6959320171cff5959320171cff6556320171ebf5956320171cff64d6320171cff6a55320171aff6995320171ebf2995320171edf5955320171cff64d5320171ef758d5320171aff680985cd61aff6809850d61cff2619050d61cff69d9520161cff6919520161cff6959420161cff68d9420161cff6a55420161cff69d9320161cff6919320161cff6a54320161cff688985cd51cff680985cd51cff6889850d51cff6809850d51aff6809850d51cff2619550d51eef2615450d51aff2a19250d51cff2619250d51aff2a19050d51cff2619050d51aff2a14354951bdf6954354951fcf5514354951cff6999420151cff6959420151cff5959420151cff68d9420151cff28d9420151cff69d9320151cff6959320151cff5d59320151cff6919320151cff5519320151cff64d7320151cff6516320151cff6515320151cff6a54320151aff6954320151eef5514320151cff64d4320151faf2999355141def6599255141def64d9255141def6599055141def64d9055141dbf2599254d41dbf2599054d41dfe6899014d41cff2a19014d41def6919014d41faf5956350941bef6995350941faf2995350941fcf5955350941fe758d5350941bef6985350941cff6999520141cff68d9520141cff28d9520141cff6556520141eef6995420141eef5955420141eef68d5420141cff6999320141cff6959320141cff2959320141cff5959320141cff6556320141ebf5956320141eef5516320141cff64d6320141cff6a55320141aff6995320141ebf2995320141cff6555320141edf5955320141eef5515320141cff64d5320141ef758d532) else (if j<10 then 0x24b2470489490a51ff23d347828ebd1c4a36d468e8c9918a22e945908ab1148226f44b088c9108a1eb4380867d0bca1584278849508720ed41a282d504ca07d40ae812901ea03040147f90fe41fb13f347de4fa71f323e367c10f769ed63d607a3cf399e4d3c4e7818ef29dc43b4675f4eae1d363a2073a8e621cad3904715ce1d9c1037de6f10dd19b8236cc6d14d949b0335b06af0d501a7034946890cff19d833786680cc2196d329864c0c8298e9319a62c4c4a98603074603cbf717dc2f805e90bbf17622e825c58b7d16d92d665a34b38964b2c4a5838afb95d62b6a5664abc15572a625490a8414e229785258a381454286650209f113c627544e389b4133d264c4c0097212b9251c49c892d923f245048308fa91e3237a46ac8cc918222e04528899910d22004354857909820da411c8108ffb1fb43ee47ce8f811eca3cfc78c8ef81da43aec7548e971d0039b872e0e451c4837e46ee8dbc1b4a35fc6ac8d381a3834006720cbe194432186350c4e185030085ee0bbb17342df85b60b5a167c2c9c5858af415ba2adc5488a7514bc29085158a0f13f0275c4dd899a12fc258849b891b11f42378461089c10e2219042188180ff81fbc3e207a30f041dac3a787330e1a1bb036806b40d3019f0330063f0c3c17a42e185a20b0c15942a205230a041398260049f08f21160216841107ea0fa01e3839c06ec0d401a1831805f80b8016482b2054a0a60145827e04d8096812402220402076c0dd019902f00548098811a01f2037406080a0011201c8026002b0000dbf2599160d54dbf2599060d54dbf2589060d54ebf2998360554eef5918260554cff6189060554def59090605549ff68c9060554cff60c9060554bf728d9660154ebf2998360154eef5918160154cff68d9520173ebf2a19620173fb728d9620173ebf2199161153ebf2199061153ebf2189061153ef75cd8260553cff61c90605539ff6909060553cff6109060553df75cc9060553ebf65c8660153ebf2199460153ebf2199160153ef75cd8160153eef6859061053efe6859460053efe6519160053efe6499160053cff6519160053ebf2999161543ebf2599161543cff6499161543aff2819161543ebf2999061543ebf2599061543cff6459061543ebf2589061543edf6949061543aff6849061543cff6409061543dbf2599161543dbf2599061543dbf2589061543def6919021543bef2819355143eef2a19155143def6499155143bef2819155143eef2a19055143def6459055143ebf2998560543aff6808560543bef2a55460543eef5918260543eef5518260543cff61890605439ff6949060543cff6149060543cff2149060543def5909060543def5509060543ebf2998560143bef2a55460143eef5918160143eef5518160143cff68d9520143ebf2a19620143d7 else 0x5c6ab8c9717ae2c5c52b899711ae205c3ab86970bae145c22b839705ae085c0ab8096ffadfc5bf2b7d96f9adf05bdab7a96f3ade45bc2b7796edadd85baab7496e7adcc5b92b7196e1adc05b7ab6e96dbadb45b62b6b96d5ada85b4ab6896cfad9c5b32b6596c9ad905b1ab6296c3ad845b02b5f96bdad785aeab5c96b7ad6c5ad2b5996b1ad605abab5696abad545aa2b5396a5ad485a8ab50969fad3c5a72b4d9699ad305a5ab4a9693ad245a42b47968dad185a2ab449687ad0c5a12b419681ad0059fab3e967bacf459e2b3b9675ace859cab38966facdc59b2b359669acd0599ab329663acc45982b2f965dacb8596ab2c9657acac5952b299651aca0593ab26964bac945922b239645ac88590ab20963fac7c58f2b1d9639ac7058dab1a9633ac6458c2b17962dac5858aab149627ac4c5892b119621ac40587ab0e961bac345862b0b9615ac28584ab08960fac1c5832b059609ac10581ab029603ac045802aff95fdabf857eaafc95f7abec57d2af995f1abe057baaf695ebabd457a2af395e5abc8578aaf095dfabbc5772aed95d9abb0575aaea95d3aba45742ae795cdab98572aae495c7ab8c5712ae195c1ab8056faade95bbab7456e2adb95b5ab6856caad895afab5c56b2ad595a9ab50569aad295a3ab445682acf959dab38566aacc9597ab2c5652ac99591ab20563aac6958bab145622ac39585ab08560aac0957faafc55f2abd9579aaf055daaba9573aae455c2ab7956daad855aaab49567aacc5592ab19561aac0557aaae955baab45562aab9555aaa8554aaa8954faa9c5532aa59549aa90551aaa29543aa845502a9f953daa7854eaa9c9537aa6c54d2a999531aa6054baa96952baa5454a2a939525aa48548aa90951faa3c5472a8d9519aa30545aa8a9513aa245442a87950daa18542aa849507aa0c5412a819501aa0053faa7e94fba9f453e2a7b94f5a9e853caa7894efa9dc53b2a7594e9a9d0539aa7294e3a9c45382a6f94dda9b8536aa6c94d7a9ac5352a6994d1a9a0533aa6694cba9945322a6394c5a988530aa6094bfa97c52f2a5d94b9a97052daa5a94b3a96452c2a5794ada95852aaa5494a7a94c5292a5194a1a940527aa4e949ba9345262a4b9495a928524aa48948fa91c5232a459489a910521aa429483a9045202a3f947da8f851eaa3c9477a8ec51d2a399471a8e051baa36946ba8d451a2a339465a8c8518aa30945fa8bc5172a2d9459a8b0515aa2a9453a8a45142a27944da898512aa249447a88c5112a219441a88050faa1e943ba87450e2a1b9435a86850caa18942fa85c50b2a159429a850509aa129423a8445082a0f941da838506aa0c9412a813500c9fd13f3a7b74f369e253b927564e569c2936fa6cd4d769a91346a6804cbe990d30ea5ed4b9896ad2cca5784aae94d928824f449b092f1)) else (if j<13 then (if j<12 then 0x9a4db498692ad249a47b48c6912d219a41b48068fad1e9a3bb47468e2d1b9a35b46868cad189a2fb45c68b2d159a29b450689ad129a23b4446882d0f9a1db438686ad0c9a17b42c6852d099a11b420683ad069a0bb4146822d039a05b408680ad0099ffb3fc67f2cfd99f9b3f067dacfa99f3b3e467c2cf799edb3d867aacf499e7b3cc6792cf199e1b3c0677acee99dbb3b46762ceb99d5b3a8674ace899cfb39c6732ce599c9b390671ace299c3b3846702cdf99bdb37866eacdc99b7b36c66d2cd999b1b36066bacd699abb35466a2cd399a5b348668acd0999fb33c6672ccd9999b330665acca9993b3246642cc7998db318662acc49987b30c6612cc19981b30065facbe997bb2f465e2cbb9975b2e865cacb8996fb2dc65b2cb59969b2d0659acb29963b2c46582caf995db2b8656acac9957b2ac6552ca99951b2a0653aca6994bb2946522ca39945b288650aca0993fb27c64f2c9d9939b27064dac9a9933b26464c2c97992db25864aac949927b24c6492c919921b240647ac8e991bb2346462c8b9915b228644ac88990fb21c6432c859909b210641ac829903b2046402c7f98fdb1f863eac7c98f7b1ec63d2c7998f1b1e063bac7698ebb1d463a2c7398e5b1c8638ac7098dfb1bc6372c6d98d9b1b0635ac6a98d3b1a46342c6798cdb198632ac6498c7b18c6312c6198c1b18062fac5e98bbb17462e2c5b98b5b16862cac5898afb15c62b2c5598a9b150629ac5298a3b1446282c4f989db138626ac4c9897b12c6252c499891b120623ac46988bb1146222c439885b108620ac40987fb0fc61f2c3d9879b0f061dac3a9873b0e461c2c37986db0d861aac349867b0cc6192c319861b0c0617ac2e985bb0b46162c2b9855b0a8614ac28984fb09c6132c259849b090611ac229843b0846102c1f983db07860eac1c9837b06c60d2c199831b06060bac16982bb05460a2c139825b048608ac10981fb03c6072c0d9819b030605ac0a9813b0246042c07980db018602ac049807b00c6012c019801b0005ffabfe97fbaff45fe2bfb97f5afe85fcabf897efafdc5fb2bf597e9afd05f9abf297e3afc45f82bef97ddafb85f6abec97d7afac5f52be997d1afa05f3abe697cbaf945f22be397c5af885f0abe097bfaf7c5ef2bdd97b9af705edabda97b3af645ec2bd797adaf585eaabd497a7af4c5e92bd197a1af405e7abce979baf345e62bcb9795af285e4abc8978faf1c5e32bc59789af105e1abc29783af045e02bbf977daef85deabbc9777aeec5dd2bb99771aee05dbabb6976baed45da2bb39765aec85d8abb0975faebc5d72bad9759aeb05d5abaa9753aea45d42ba7974dae985d2aba49747ae8c5d12ba19741ae805cfab9e973bae745ce2b9b9735ae685ccab98972fae5c5cb2b959729ae505c9ab929723ae445c82b8f971dae38 else 0x302541c603c0e23064c1c5c480f0388cc1c5c480f23048c1c50280901803007878387224c6c3b07d005c40c604f40c385c40c6c1f40c385c40c643b40c1c502809014030078783870280900c01e1f4043872480f0394621445a1c763d8e705c0b0dc71a8fa3ac1b01c3b1c6b12c270ec1a385f07c0d1c3358c6d1c3c3f0e358c651c503c0e23065100f0388c09347140f0388cd1c403c8c12347101400c01c85c7c920e1c0a02403006c7d010e1e0f8382471c57150f43824b1c483e0e2162431c583e0e31c24100c324c8b1c27160f838c7090483d0f8390eb1c24182443ec071e0e151641a2131ec0838609221b01c7838545d0fb002483851942483e0ef0fc1f00c7200f03956518c7140902001000a7d1c683e0e014a491c503c0eb0d472905448924148583e0e51c7c17c3f07c0c3f12c394720d751c20300530cc1300cb1b0530cc130312c3f0e91c8c3f0ec171291c511d5709495204350540a2a8571c8015435054071d4b180550d415004252c6a4a0fa160e10886490f616c7150f4398a616c7140f0398962192614c71c0550d41101c752c6a4a0fa228571c503c0e62985b1c56480f03985b1c503c0e614c795c56480f62185b1c50284343d0e61747194a50e0f83a85d1c652a89526885214350540a1647294a50c40a220fa17471c0a024030074715c66118260588b0c545f84e0b80e046418060158460d81644609646f138163991185301805a0e81a44601a84a041aa44552406a1283a0405a2070198460d8101591180a0180300421d1c8e1c0ff0fc1a008cd1c603cc9f0fc1e0488d1c8c2005c0f0207f081406c130206b081723c20201b04c0f020170818c6f13c3f0b80504c5c208317c3f0b8037f41c20731bc4f0b8036b41c207c232108c6317c4f0fc2e0341c20831b81c3b42c44531b81c3b42c445e070e51f1110c6e0742c444c3b410b0ed042c3b41090fc342c0311c403c0311c403c0311c403719c570e00925c7a207715c3801c79268819c5711c370a00926881dc67160071e49a206715c38024971e8819c670e00925c7a206719c470dc280249a207711c2801c3926881849a02887144719c38024971e881bc3821a461e0f17c36978061e0f17c3697808320961c6f07c00942413c1f03c7090422bc3f07c005e24b1c7f13c3c87c1c920e1a0f83865f0fc1093c031c8d6c9ad7b5ac6b52d699ad1b5a06b3ad669acbb5946b22d639ac5b5886b0ad609abfb57c6af2d5d9ab9b5706adad5a9ab3b5646ac2d579aadb5586aaad549aa7b54c6a92d519aa1b5406a7ad4e9a9bb5346a62d4b9a95b5286a4ad489a8fb51c6a32d459a89b5106a1ad429a83b5046a02d3f9a7db4f869ead3c9a77b4ec69d2d399a71b4e069bad369a6bb4d469a2d339a65b4c8698ad309a5fb4bc6972d2d9a59b4b0695ad2a9a53b4a46942d27) else (if j<14 then 0xe038743070280900403e010ce1c703d0ab06c3e0387430703d0ab06c3e0387430700c0a43ca513093141202cc6e0b80c30805f093140a31b80e1f0c210c03e08e1ec51417c24c631412e0187c3088200f43380e1ec61817c24c5048c6e03874388715c38260ce038719c670e09e020ce1c6825c3e020ce1c54220c02780e1dc61803c921171e21140f70dc164a0ce01c71d08615c470dc270580648870580833c2648570d92e020f71c503d85711c27059270f8083098300b024040080129c703ec3b050ce00a4b1c7032c4b0ac1a02c3a48703dc670dc164b808307711c1833806905711c1e020c690570dc46938083c503e0ce01a4100f70dc16920ce00683185e01a7648503dc670dc164bc4e020c200cb12c1a029216c4b0780432a41403a938043ec716c32938043ec7141403d0a426c3b0692e00c7430a03ec1a0292f0d0cb1c703ec6b12c1a4bc3e010c200cb0ac1a0117a486b0e9aa483432c3e029aa90503ec3e010ca90503ec3b0680a490cb1c7827c2e020c690570e096920c71f801a09615c470dc2833806488825c483380690570da48260ce01c719c660192f0e09831c71e09711c370a0ce01a41c0970f80831a415c670d8064a09831c71c0d0280600f81d1c8e1d846098eb0c445f80e3464100560e46f138063860168314d46e028e181ab1d46e028e1405a0cc7e0146a38601805611836098819890158371e46e01881d886342f0f81d1f8023050340a01803d1f812387090c3e078032b8745c7028030072185f8783870280900c0125f8783878380171f21890500740c85c783a241a1663d8e705c0d0dc79148c3f0ed0740b0f473147c3f0eb0cc5d1c5324c8b0e470905f0e2423c8ed1c563d8e705c09161671c763d8e70dc170252914c7218f63a529144a3e8eb06c045945b1c7a3e8e05945b1c5a3e8e4314952152514c7218f021c3704c094a4571c8049c39162271c594a45889c71217f07c0d1d24140f03ac7890403c0e232c78905a3e8eb1c24102571e240c16f0fc1f02c7890171ec785c240c17b1e240c0f232c08904b128e09034900ff0fc1f000ed1c7f07c051d24100ff0fc1f022403b471c27d1c203c0ef0fc1f022423347202543149523c3892471d094222491c4c8496d1342d06c3c38c52321d0f42d0097d070e1f21d1342d034125b0e1f21d134350b40d070e1f2105ac3d030e3146c84d232cc5d030e1b21328c5d030e1721348c5d030e154a5274043a47141400f21f072471e0e1f24c87c4f0fc1d020e1fc4f0f21f072483860280900c01b1f404387b0f473171710c5d1f170cc551f170cc508b47c5c4d1e172903d1e17290325b4429e17110f31ec0d0e0e4586028090200300400d1e8620c5f07c0b0f8715896218160387b0c6e0780e1c64101252545f0fc1f03071c0f22bc3f06c0c1c8c1f1203c0e2 else 0x25f4008c8b01170c57e04215f81a003e0f16089f324c8214c130097b1f43264992347931241697b1dc30e4b9264c4904b11c4b00d1340532705f1012c1ac0094cc231734306b11c03386c1b05f13c3f0ac0704c820c0344d00dc3b07870dc3b06c0e1c4b06c0e1d271187890203fc3f0740133871bc312740e1c4c140c615c3705c0e1d921c0f03985705c0649c383387240cb06c0e1ec3a48603282b06c045e921ac3a6a920c0c821857078769060320870dc1e1da4180f021c383387690603c0ef07c0a904c61c7b0ec1b0187a90570dc17038729050920f838a461c503c0ef0fc1f004c61c703c0ef07c06484ce1c70300902001003872907a480f03a85e1cc6180f03bc3f07c0132a421c803c0ef0fc1f02921328722c304ea40ec3a1ca40ca543d0e118a4a16871dc3704c0e1da41408704c06900f70f871d9203c0861787718670d87690369608f0fc1885856918721a503fc3f0587138603fc169387138503fc3f0787138503fc3f05a4139871bc313f871384a480f03ac3b06c0494703c0eb06c0e1d241a9203c0eb0ec1b03871e9203c08b1ac3b04c0e1c8090c3e078732917180a0240143003e03871d0a01805e038703c603d0ae0387430543f80b1e24110fe0024b1c403d0c4278031e241809006c7e0224140f4338031e24140f43380092c7140a00f4785ca2140a0180300421d1c8e1c0ca902b1e970ac3a582024030050ce02a4b1c7a581403d0ae00c7430703f802910cb1c56078763ac31381e0387190401805611836059118176264560012e1e4665086424691587e005919c1e09911013e0311c404c1f80c47101307e0311c40403dc570dc183380e1c703dc170f80833871a0c03d08e1dc5140fb16c3b0780e1d0c1c0f719c370780833871c0f705c3e020ce1c64200f83380e1dc6180f70dc183380e1c682bc36978061e0f180fb0ec1e0b80431171c0fb0ec1e010ce1c603ec6b0ec1))))
def mo255H9 (j : Nat) : Nat := (if j<1 then 0x4084c3b2f4000000000000000000000000000010010470870003432a2180000000000865000000004085e3400092ff57fd03400000010cf00038db0000000a354000000379094065af000000000000000000000000348bf2e3c3b0000000e658000501487b443516221c9c5392778eaf1d94f50246b8c00000000000f8526c00004a0a92d00000000000000000006016e40000003906b304000244916300006a00000000e02fa880000000000318b000000000016a80000000659000000000003342c9591a40000002875000000000000000000000755000000000005024492a537665c68756511e80000002d26f5b400075619600003ac9000000033680000000000000000000010564654000000000059540000000000c8f400000000000001c6300024fb0000000000000000030ac2e38000b50c000c5bd8500000000410c00041230f80000000b1e044e0294000000000000000000000000000000000000000000d81000107400000000000000000000000033870000000a13c0002073096000000000000000001f833230000000000000000000000000000000054a400000000000000000a3ac0000000000c2c6871116b8e800000000000386c32cc4c00000000000a8e00011a50000000c32aca882fa5310e440000000000e170941c3f498d5b69d1de37799b0000c52000000020a400000000000000000a6400000000000b0a301500000000000000c00143100000000000000000000063591760002010000008f069dd8c000000096a5cf100001856350000f2a8482d6c8000000000000000000002b803398000000000000018f7000000022d00000002c88000000049b4000000000000038ec000000050fac5900000009078000000000061a00000002d2a00000000001d2c86f4000000000000020395283d4500000007bcc0000002ab60003c9486b40002e24000b4d40000000000f51b0664b36c67de13c7d000000000010b20002d36048f8900000000000000000000000002430000169e0001509d0bccf6f34fd8e00000000001a9700000000000000000000000037780001d9f73b4000a508000000000012b4000000000035b8000000119d0000000f8ed0160000c376e0b4222a9a587000000000000a100016540000000b1cc000000118300000000000000000105f0000000000000000000000000000000000000010c5e1fc00003840000002c7700010140002038d61800000000000001514c0875bb646c000000000f0000000d64557a00000000000000c1a8000000000000000000000000c0966f6e59d689000000000000000000000000052f00038990003947044a021103322061115012330021100602090523010060003203220073101105001102302000002010000320001221031004000b011431030011110103011006124 else (if j<2 then 0x65cb09c00000004160000000000000024020000000000000000000008e2800046b01b79668000c5444d7951000000000000000000f6a80000001788e2d8000d5c000054d00000003ac0000206c78e4000000000000039930000000a0f40001227571000000035ae1ab0000000f201c98000113f0000000000000000004b3000000031172e5000281d8576434227c0000000cc4a6780000000000000302ba110000fb38c79554b5070001c6159b80001587d7952ac000c0b00000000000000285d20fed40000000003b8cde000000000035a0000203a000000053f0d0bd6a000000000000000000000000053800000002d1fe2b800000000000000000000000000024ff000000000000000000000000000000000000000000000000080900001062503b66308300008ccb214000a01cc23429cec30000000000000026b80000000000063c0009420000000188a945c00000000000000ab7000092e0000000000000000000000000000a2e40000000000000040186cc6f20000000000000005f40008416ce40002d7b00000000001968000154c0000000e07c000000000016d80000308000a47b67033e40002396ab8d0a8000000000005d000016d00006018000f31917cc0b40000002d66452400053f8000562a9a2000000000000000000000238e1770000000000000000000000000000a2889881468000941000082380000000000000000000000000000000000000000036780000000000000000000002ee400000000006a54000000005b1081dbe49dfc6ef6fec0c00014c9000284d0000000000000000028a39b840000000000868f15a0000599a9bc000f488884b3d30cec11800000000000000000000000000000000dfc000809800000020dc00000007b3c000926e417000186f000195c000163c00000000000000000007ef43800062bd157000182724f0000f24d55bd4280000000ce90002451000091013c000000000000000000d26800086e80000000000000114a3981159d54c00000000000000000000000000000002648cc0e192113000000004ed457fe2c000000000004cf813d0640000699ad0a038000000000035d59bc22f3916932016a145400000015550000000b3bc0007152c4200031b50000000000215ff06cebe14ebc030000000f37f14e00020c70000000000299c40d80000000000000000084e000000015970000000000000000000002363530000000000000000000000994000000000000000000000000000000000000000000000000000000003433000000088eb04000000000000000000000060d40006e0585ef464000101393e000006522a456c6a94000e367e96000000022d6da4f433d4f000000000000000000000000000000000000000000a6c6bb746e2eccb4e4000000000072dea94000000000000005 else 0x2ee700016b97490000b4a000000000000002266000293700000007388000000000000021730001c4732e8000000000045408fae23746d660000041c00000000000000000035f8000000245500000000000000000000000000000000000000000000000000000000dab7cd1000000000000006048000000000089dbc4b000000000000007028000000000004828490000cf30000000000000000000000003989033400062040008494956649c0000002584a48400000012cb0003441b188000312986b0000000000051c0003691000000084f40003e3c00000028b03bb4000225c000000000051f18bb0002aa70000000e34892bb29913295e0000000055e0000000000000000000000000000b5a6d0f229209e50f000000004e70000000552000043c8000260800080bb118000000000000000000000d0680005444000552c0000000))
def mo255D10 (j : Nat) : Nat := (if j<9 then (if j<4 then (if j<2 then (if j<1 then 0xab9a42887fd58d21443feaa690a21ff45348510ffaa1a428877f5d970443bfae6b82217fd9758110f7ebb2c0887bf59160443dfac6b02217fd9754110bfecb2a0887df55150443efaa6a8221ff97054110ffcb02a0885ff65940442ffb2aa0221fbd4350110bfecba60885ff65930442ffb2a982217fd944c110feea1a60887fe58130443ff2a098221ff97648110ffcbaa40887fe59520443ff2c890221ff95448110ffcb9a40887fe58d20443ff2a690221ff85348110ffca1a40884ff654805da7fb26402ed3fd93201759feca100b2cff654805927fb26402c97bc90591549fec9900aa4ff654805cedfb2c402e73fd9420163d7ec390ca9ebf2198454fdb90cb9aa7f5d655cd53d7e43302a9ebf2198054e7fb28402a7bbd9161053ddec830829efe6518014f7f322c00a7afc96615439feca900a1eef5508050ebfb2e402876fd9620143bbeca900a1dfd6448050e7fb2a402e33fd93201719feca900b0cff650805867fb26402c33fc985cd519fe4c286a8cff650805467fb26402a35fd9714d41b7ecb0a6a0def65053506fdb2429a837f99014d419feca900a0eef550805067fb26402837bd9421531ddec22a898cff261524c67fb2a402633fd9420131ddec22a890d7f65c53486dfb2c29a437bd9414d21bfcc80a690cff261515c27f93098ae13fc985cd609fe4c286b04ff261515827f93098ac1cfd765c160bee49b0ca87cf59154542bfb2e41aa16fd9620d50bdeca106a85fd644835427f930b9aa1e7c9654d50fae41aa6a87d75cd53543ebac6a9aa13fc9850d50bbecaa86a87cf55143543e7aa8a0aa13fc984c550fbca9ae0a87de54570543ef2a8b02a1f7951581509fecc286286ef611431437bb06a18a13fd9814d40afecb8a6a05bf65853502f7b2829a817f59114d40bfcc80a6a06ef615435027f930a8a81bbd85505409fe4c262a06bf259854c27fb30aa261f9d6450d30fceaa286984ff261514c3fb286b0261fd93158130fbcaa2a0987de54d504c3fb286a8261f795154130fec98aa0984ff661504c3f3a86a0261b7d9761430dbeca30a186bf619750c36fb0aba861bbd9761030ddecab08186ef5d5840c27fb30aa061afd8655030dbec2aa8186ef611540c37eaeac0861bf55460430d7ec32e0186df615700c377b08b8061bf5815c030cfec3aa0186bf619500c36fb0aa8061bbd8454030dfac0aa01867f61d400c35fb0ca0061b7d8550030ddec2280186fd605400c2bfb2e29a216fd9614d10bdeca0a6885fe64053443f6aa8a0a211fd972016497ecb100b9c7f65c8058fcbacab1aa71fd972014397ecb100a1cdf6548050e7eb22402872fd96201718fecb900b0c7f65c805065fb2c4028337d95201419eec9900a0cfb648805063fb2e402632fd96201319beca90098cef650804c67db2440263fe12148110 else 0xaa86986ff615434c3f7aa8a1a61fdd6350d30feea9a86986ff61d814c37fb0cc0a61bfd8560530dfe42b02986ff611814c3fba86c0a617fc985c530dfec32e2986ff615714c2ff930b0a61bfd8758530dfec22c2987f750d614c2ff930a8a61bfd8554530dfec22a2987f750d514c2ff930a0a61bfd8650530dfec2a82987ef551414c3fbb0e98a61fdd864c530feebb262987f7615314c3fb90a98a61fdd754c530feeb2a62987f7611314c3fbac898a61fdd544c530dfec3a62986ff615314c37fb0898a61fdd734c530feeb1a62987f754d314c3fba8698a61bfd8748530dfec3242986ff615214c37fb0890a61fdd4348530dfec32e09877f5d9704c37fb0ab8261dfd735c130ffcc3ac0987fe611604c3ff302b0261ff97158130ffca0ac0987fe485604c37fb0eb0261bfd8458130feea1ac0987fe5c1604c3ff130a8261ff99754130ffcc3aa0987fe5d5504c3ff328a8261ff98454130ffcaa2a0987fe64d504c3ff2e6a8261ff94354130ffcc8aa0987fe605504c3ff2e2a8261ff95154130ffca0aa0987fe4c5504c3ff242a82617fd9754130dfec2aa0986ff611504c3efaa8a82617fd9354130fbea9aa0987f750d504c3ff2e0a82617fd9714130bfeca0a0986ff610504c3fba8628261bfd8650130bfecaa80986ff615404c3f7a86a0261ff96050130ffca8280986ff655840c37fb30aa061bfd7560430dfeaa302186ff619700c37fb0ab80617fd9754030dfec22a0187df551500c3ff2e0a8061bfd8650030bfecaa80186ff615400c37faecc2a21dfd765d510dfec2aea885ff65d65443dfaecb2a21bfd8559510dfeb2b08886ff615644437fb30aa2217fd9655110dfec2aa8887ef591544437faecc1a21bfd7560d10dfeb2b06886ff591834437faa8c1a21bfc985cd10efebb2e6886ff61573443bfaeab9a21bfd835cd10bfecbac6886ff61d634437fb0ab1a21efd6558d10dfec22c6886ff60d634437fb30a9a217fd9754d10bfecb2a6887bf259534437fb0aa9a21f7d6554d10dfec22a6886ff60d53443fbae6a9a21fdd6354d10bfecb8a6885ff65853442ffb2829a21bfd8414d10bfec80a6886ff661434437f930a1a217fd9650d10bfecaa86886ff61543443f7ac8a1a21fbd5450d10dfec1a86887fd645434437faecc1221bfd7560910dfeb2b04886ff591824437faa8c1221bfd7360910dfeb1b04886ff54d824437f8a6c1221bfd4360910ff6bb104887fb5d482443fdaca41221fed6420910ff6aa104887fb5cc82443fdac641221fed5320910ff629904887fb50c82443feacaa0a21ff56350510ffaa9a82887fd14d41443feaec98a21ff5754c510ffab2a62887fd59131443feaa898a21ff5734c510ffab1a62887fd54d31443fea8698a21ff57648510ffabaa42887fd59521443feac890a21ff55448510ff) else (if j<3 then 0xa6a87df61153543efae6a9aa1f7d9154d50fbec82a6a87df5d553543efaa8a9aa17fd9850d50dfecc286a85ff261435437f930a1aa17fd9550d50fbecaa86a87ef61143543f7aa8a1aa1f7d5350d50dfec3b02a86ff619815437fb08c0aa1f7d5460550dfec1b02a86ff20d81543efaa6c0aa17fc985c550dfec32e2a87df54d71542ff930b0aa1bfd8758550fbeaa2c2a87df61d51543efb0ca8aa1f7d7654550fbec22a2a87df59151543efb06a8aa1f7c8354550fbeb9aa2a87df58d51543efa86a8aa1f7d7554550fbeb2aa2a87df55151543efaa6a8aa17fc9850550dfec3282a87ef61141543f7aa8a0aa1f7d5350550bfe4c262a86ff61d31543efaa898aa1f7d534c550dfec3a42a86ff61921543efaa890aa1f7d5348550ffcc32e0a87fe60d70543ff106b82a1ff9635c150ffcc0ae0a87fe58570543ff262b82a1ff9215c150dfec32e0a87df54d70543ff30eb02a1ff98458150ffcc0ac0a87fe5c560543ff282b02a1ff92158150dfec3ac0a87df55160543ff2e0b02a1bfd9850c50dfea1b02286ff659855037fb26c2a81bfc9361540dfec8b0aa06ff61985502ffb2c42a817fd9321540bfecc2caa05ff261655037fb0ab2a81bfd8660d40dfec2b06a06ff21583502ffb2c41a817fd9520d40dfec2906a05ff66163502ff930b1a81bfd8558d40f7eb2ac6a05ff661535037fb30a9a817fc9854d40bfecb2a6a07bf259535037fb0aa9a81f7d6554d40feeb1aa6a05ff66053502ffb2c29a817fd9014d40fde4c286a07ef65943503f7b0ca1a81fbd9550d40fde4aa86a07ef61543503f790aa1a81fbd6550d40fdeb1a86a07ef54d43503f7b22a1a81fbd9050d40fde48286a06ff619815037fb0ac0a81bfc8560540dfec1b02a06ff20d81503f7a86c0a817fc9858540dfec2ac2a07ef50d61502ff930a8a81bfd8554540fdea1aa2a07ef61941503f7b0aa0a81fbc8550540fdeb2a82a07ef60d41503f7906a0a81fbd6350540fdea9a82a07ef14d41502ff93098a81bfd854c540fdea1a62a06ff619215037fb0a90a81fbd4348540dfec2ac0a07bf58d60503f7a86b02817fd9654140fbea9aa0a07ef50d50503ff2c0a82817fd9614140bfec98a0a07ef50c505037fb0ec32617fc985d930efec3aec986ff65d854c37fb28c2a61bfd9161530dfec3b0a987bf259854c2ffb2e42a617fd9421530bfecc2ea985ff261754c37fb0abaa61bfd9661130dfecab08986ff255844c37facac2261bfd9161130dfec3308986ff615844c37f90ac22617fc9859130bfecc2a8986ff661544c2ff930aa261bfd8555130dfec2ae69877f5d5734c37fb0eb1a61bfd8458d30bfecbaa6986ff611534c3fbae6a9a61fdd9650d30feec3286987f7655434c3fb92aa1a61fdd8550d30fee42a86987f7595434c3fbb22a1a61fdc9050d30bfec else 0xa8dff26164546ffb2841aa37fc985cd51dfec3ac6a8eff66143546ff930a1aa3bfc9850d51bfecaa86a8fef55143547efaeca92a3f7d6454951fbeb9aa4a8fdf58d52547efa86a92a3f7d7554951fbeb2aa4a8fdf55152547efaa6a92a3ff5635c551dfebb100a8eff5d4805477faca402a3bfd6420151dfeaa100a8eff5cc805477fac6402a3bfd5320151dfea1900a8eff61565507f7b2caa283fbd6555141fdec9aa8a0fef64954507f7b20aa283bfd8558d41f7eb2ac6a0fef551635077fb30a9a837fd9654d41f7e4b2a6a0eff61553507efacaa9a83fbd5454d41feeb1aa6a0dff65853506ffb2029a83fbd5458941fdeaa2a4a0fef59542507f7ac6a1283fbd5350941fde29a84a0eff594805077fac640283bfd5320141dfe29900a0dff261764c6ffb2e42a637fd9421531bfe4c2ea98eff615754c77facac22637fc9859131dfecc2a898dff261544c77fb0aaa263bfd855cd31efebaae698eff61d634c77fb08b1a637fd9754d31dfec22a698ff75cd534c6ffb2aa1a63bfd8550d31fdeaa28698fef551424c7fbaec99263fdd754c931feeb2a6498ff7591324c7fbaa899263fdd734c931feeb1a6498ff754d324c7fba8699263ff57554531ffaaa2a298ffd5cd514c7fea86a8a63bfd7620131dfeba90098eff594804c77fac840263bfd5420131dfeb990098eff58c804c77faa640263bfd4320131dfebb30a90f7f5d9754877fb0abaa437fd9759521f7ebb2ca90eff615654877facac2243bfd8559121dfecc2a890dff659544877fb0aaa243fbd6455121dfebb30690eff5d5834877facac1a43bfd6460d21dfeaa30690f7f5d9734877fb0ab9a43dfd755cd21dfec1ae690dff65d634877fb0eb1a43bfd8558d21f7eb2ac690eff611634877fb06b1a43bfd9854d21bfecbaa690dff65953487df92ca9a43bfd8554d21fbeb2aa690eff611534877fb06a9a43fdd7354d21feeb1aa690dff65c53486ffb2c29a437fd9414d21dfec20a690dff640534877fb30a1a437fd9650d21bfecaa8690eff61543487f7ac8a1a43fbd5450d21dfec1a8690dff658835c2ff930b1ae1efd6558d70efeb9ac6b85ff659535c3df92ca9ae1f7d6554d70feeb1aa6b877f58d715c2ff930b0ae1dfd7358570bfe4c262b877f5d9315c3bfae698ae1dfd7648570efeb9a42b86ff261735837f930a1ac17fc985c560f7eb1ae2b05ff26141583f7aa8a0ac1efd6350560dfec3a42b07bf5d921583dfac890ac1efd6348560efeb9ae0b07bf58d705837fb0ec32a17fc985d950dfec3308a85ff26164543efb2caa2a1f7d8655150fbec9aa8a87df64554543efacaaa2a1bfd8760d50f7e4b306a86ff61183543efaa8c1aa1bfd8720d50bfeca106a86ff61083543efaa841aa17fc985cd50dfec3ac6a87df55163543efb2ea9aa1f7d8754d50fbeca2)) else (if j<6 then (if j<5 then 0x7ff611214c3ffac890a61ffd5448530ffeb9a42987ff58d214c3ffaa690a61ffd4348530ffec32e0987ff615704c3ffacab8261ffd635c130ffea9ae0987ff61d604c3ffb08b0261ffd7058130ffe4c2a0987ff65d504c3ffb0ea8261ffd7554130ffeca2a0987ff611504c3ffaa8a8261ffd9354130ffeb9aa0987ff50d504c3ffae0a8261ffd8414130ffecb280987ff619404c3ffb2aa0261ffc9550130ffec2a80987ff215404c3ffacaa0261ffd6350130ffea9a80987ff581404c3ffaa0a0261ffd9055030ffecbaa0187ff651500c3ffb2aa0061ffd7559510ffecb2a8887ff59554443ffb26aa221ffd9055110ffeb2ae6887ff5d563443ffaa8b1a21ffd7358d10ffecbaa6887ff5d553443ffb28a9a21ffd5454d10ffeb9aa6887ff64153443ffb2ca1a21ffd9550d10ffe4aa86887ff59543443ffac6a1a21ffd5350d10ffec8286887ff59570443ff926b8221ffd635c110ffebaac0887ff55160443ffae6b0221ffd4358110ffecbaa0887ff65950443ffaeaa8221ffd6554110ffeca2a0887ff59150443ffaa8a8221ffd9354110ffe49aa0887ff58d50443ffaa6a8221ffd4354110ffecb280887ff65540443ff92aa0221ffd6550110ffec9a80887ff24d40443ffac6a0221ffd5350110ffe29a80887ff65d30443ffb2c98221ffd764c110ffecaa60887ff25530443ffaea98221ffd654c110ffeca260887ff59130443ffaa898221ffd734c110ffeb1a60887ff54d30443ffa8698221ffd5348570ffebb242a87ff5cd21543ffaa6b8221ffd7654110ffeb9aa0885ff24186553df92cc1aa97fc9060d54dfec3302aa7ef591815537fb06c0aa9bfd8260554bfe48302aa6ff61980553f7ac8c02a9bfd8360154dfec0b00aa6ff594805cfdfb2c402e77fd9120173bfe482eab1dff2415458eff920b9ac77fc9061d53bfe48308a9dff2417354f7fb0ec0aa7bfd8460553feeb9b02a9eff6098154eff920c0aa7bfd8760153dfec2300a9ff75cd8054f7fb02c02a7bfd9460053dfec8b0029dff2418650f7fb22c2a87bfd9061543dfe4830aa1fbf2598550eff920c2a877fd9121543bfec810aa1fef64d5450ff7b22aa287fbd9055143dfec3302a1eff6158150f7f90ac0a87fbd6460543fdeaa302a1eff6098150eff920c0a87bfd8660143dfec2b00a1eff2158050ff7ac8c0287fbd5460143dfec0b00a1eff5948050f7fac640287bfd5320143efecb900a1fbf6588050f7fb0c402877fd9520143fbeca900a1eff6148050f7f90a40287fbd9420143fdeb2100a1fef5508050effb2240287ff59120143dfec0100a1fbf595635c6ffb2ca9ae3efc9654d71fbeb2aa6b8ff758d535c7bfac6b92e3bfd6520171dfeb1900b8eff54c805c77f930b9ac3bfc9850d61dfeba900b0eff550805877fae6402c3bfd4320161bfe4c2ec else 0xf61981543ffaecc0aa1ffd7560550ffeb2b02a87ff61181543ffac8c0aa1ffd5460550ffec1b02a87ff20d81543ffae6c0aa1ffd6360550ffea9b02a87ff50d81543ffb0cb8aa1ffd835c550ffe41ae2a87ff58d71543ffb0eb0aa1ffd8458550ffec22a2a87ff60d51543ffa86a8aa1ffd8650550ffeb2a82a87ff60d41543ff906a0aa1ffd6350550ffea9a82a87ff61d31543ffaea98aa1ffd844c550ffeaa262a87ff60d31543ffae698aa1ffd434c550ffec3a42a87ff61921543ffaea90aa1ffd6548550ffec2242a87ff59121543ffaa890aa1ffd8348550ffe41a42a87ff58d21543ffaa690aa1ffd4348550ffec32e0a87ff60d70543ff906b82a1ffd635c150ffec3ac0a87ff61160543ffae0b02a1ffd9050c50ffecb30aa07ff61985503ffb26c2a81ffc9361540ffec8b0aa07ff61565503ffb2cc1a81ffd8660d40ffecab06a07ff25583503ffb0ac1a81ffc8560d40ffeb2b06a07ff64583503ffb0a41a81ffd8558d40ffec1ac6a07ff66153503ffb0aa9a81ffd8354d40ffec8aa6a07ff64153503ffb0cc0a81ffd8560540ffe42b02a07ff59581503ffb06c0a81ffc8360540ffeb1b02a07ff54d81503ff8a6c0a81ffd8558540ffec1ac2a07ff61951503ffb0aa8a81ffd6554540ffec1aa2a07ff20d51503ffac6a8a81ffd5354540ffec3262a07ff61531503ff90a98a81ffd654c540ffec1a62a07ff58d31503ffaa698a81ffd8648540ffec2a42a07ff21521503ffaca90a81ffd8348540ffe41a42a07ff58d21503ffaa690a81ffc5348540ffec2ac0a07ff60d60503ffb2ca8281ffd8654140ffeb2aa0a07ff64d50503ff926a8281ffd8354140ffe41aa0a07ff58d50503ffaa6a8281ffd6054140ffec18a0a07ff61d864c3ffb2ec2a61ffd8761530ffeca30a987ff645854c3ffb0abaa61ffd8759530ffecb308987ff619844c3ffb2ac2261ffc9561130ffec2b08987ff215844c3ffacac2261ffd9161130ffecc2a8987ff615544c3ffb26aa261ffd9155130ffec82a8987ff615734c3ff920b9a61ffd8758d30ffec22c6987ff61d534c3ffb08a9a61ffd9550d30ffec2a86987ff645434c3ff920a1a61ffd8760530ffec3302987ff5d9814c3ffb0ac0a61ffc8560530ffebab02987ff595814c3ffb08c0a61ffd6460530ffeaa302987ff5cd814c3ffac6c0a61ffd5360530ffea1b02987ff619714c3ffb0ab8a61ffd655c530ffeb1ae2987ff54d714c3ffb0eb0a61ffd8458530ffec3aa2987ff615514c3ffaeaa8a61ffd8454530ffeaa2a2987ff5cd514c3ffa86a8a61ffd8650530ffec2a82987ff215414c3ffacaa0a61ffd6350530ffea9a82987ff61d314c3ffb0a98a61ffd754c530ffec2262987ff551314c3ffb0e90a61ffd8648530ffebb242987ff615214c3ff90a90a61ffd7548530ffeb2a4298) else (if j<7 then 0xc80e46070d437ce1b900da106bd0354c1a610d0e067803348195f0c918639c315618780c27060b42fac17ac0bbc85cf42e1416aa0b2e058382ba415840a9b053c4295814670a1584fbc27541353098704b2424f6123f08fd046b022aa1110085c8423c2082100e07db83da41e480edf07440390c1bea0d9e06a80342c197a0c78061e02fb817520b49058202ad814e20a2c04f3826ac12ba092a04728228010a4080403e401e540ed60738038701b480d2c065a030f017880ae00510024f010d407f203c601ce00da4067e030c017100abc04f80252010f807b00384019800b7004ec021000d50051001bc00660000ffec8b06aa7ff64183553ff920c1aa9ffc9360554ffecb300aa7ff64d80553ff926c02a9ffd9160154ffecb100b9fff6455458fffb20aa2c7ffc905cd63ffec8b08a9fff6418454fff920c22a7ffd9760153ffeca300a9fff6458054fffb22c2a87ffd9061543ffe4830aa1fff6198150fff92ac0a87ffd8560543ffe42b02a1fff5958150fffac6c0a87ffd5360543ffec1302a1fff6598050fffb0cc0287ffd9560143ffe4ab00a1fff6158050fff90ac0287ffd6560143ffeb1b00a1fff54d8050fffb22c0287ffd8160143ffecb100a1fff6188050fffb2a40287ffd8520143ffe42900a1fff5948050fffac640287ffd5320143ffec0100a1fff649535c7ffb20a9ae3ffd9255161ffec82a8b0fff64943587ffb20a1ac3ffc9850d51ffecaa86a8fff64943547ffb20a1aa3ffd635c951ffea1aa4a8fff64953507ffb20a9a83ffd6554941ffeb1aa4a0fff54d52507ffb26aa263ffd9255131ffec82a898fff655434c7ffb24a1a63ffd9050d31ffeb2ae498fff58d724c7ffaa6b9263ffd7554931ffeaa2a498fff5cd524c7ffa86a9263ffd6550931ffeb1a8498fff54d424c7ffaea99263ffd544c931ffebaaca90fff65954487ffacaaa243ffd9355121ffec82a890fff59573487ffaeab1a43ffd5458d21ffeb9ac690fff65d53487ffaeaa9a43ffd9454d21ffeaa2a690fff5cd53487ffb20a9a43ffd9650d21ffecaa8690fff25543487ffacaa1a43ffd6350d21ffea9a8690fff64143487ffb22a9ae1ffd9054d70ffeb1aa2b87ff595315c3ffac698ae1ffd534c570ffeb2a42b87ff20d215c3ffac690ae1ffd9155160ffec82a8b07ff24173583ffb22a1ac1ffd9050d60ffe48286b07ff5d521583ffaa890ac1ffd7348560ffea1a42b07ff61d86543ffb2cc22a1ffd8661150ffeb2b08a87ff64d84543ff926c22a1ffd9161150ffecbb06a87ff61d83543ffaeac1aa1ffd9460d50ffec2306a87ff55183543ffb22c1aa1ffd8720d50ffec2106a87ff60d73543ffb0eb1aa1ffd8458d50ffec22a6a87ff66143543ff930a1aa1ffd9550d50ffec1a86a87ff64543543ffb20a1aa1ffc9050d50ffec3b02a87f else (if j<8 then 0x3949eea4a9522da8fed4736a3565188a8b0d450ea23950eca85e54232a0dd50312802d3f7a9f6f4f90a7b713d2e9e404f02276d93ad09d1a4e662724138729be24dca26d8536269abc4d32a67f13338994e4c77262c930b698164bdfa5d592e1096c34b31a57e92ba095a64ab52547129c094b64a38a50d527e093bd49aa24c1925949285492024811237e918c489f243c121209042480323f711f1c8f49478223ab51cd08e2346ef236891a848ceb462f2304117968b86459c22c1515928a844524227e9137c898244a7a2495119c889b4434220450faa877e439821bd10d5e86614317217390b248556428d2135509208439420320e99068c83014150a0971042e81db40cb2058d023c80b54038200acffba7faa3fae1fc5cfdc87e963f289f830fb7c7d553e839f308f8fa7c4a3df99ee94f6d27b003d591e96cf42c79da3cd39e5f4f25e78ea3c571e1a4f03677c43bad9dca0eda2768c3b239d79ceb0e755d3a879d34ce91c744939fd9ce24e66472f639541c968e40671a338a19c3f8e14e704737f39be40de966f0f37699ba14dc806de936c49b558da226cde363f1b078d7b26b8b35a31ab98d50c6a1434de9a574d24268ca343e1a070cfae679233a699c68cd74665132f8996d4cae06519325c99188c82863cf31c518cf0c5dc62a031369887cc3c6619e30a81839cc0fc601e2fe817e2cbe325ecb2f3a17898bbc25db72eb017448b9525c522e0696f20b7065b472d8116b3cb5025a2a2cf296680b28058fb2c5b16230b06a57de2bd595d74ae3056dc2b3e15894ab9c55802a8715300a8e4540029c714c94a59c525c290714700a28a50ee286214268a0bc500727ca93cd49dbc4e992713937409af24d10266a1326098944c0525ed92e5896b44b1e257592ae094b04a1c24e292600928848ed244f9218c903c47d923c111cf48e0246b323299185c8b92458422a4113e8896a445e220390ee486b2430b215e90998844241ca20b09044c818a4080201d8ffd87f743f751f938fb647d043e341ee58f63c7aca3d201e648f21078a23bdf1dc40ed5475fc3ab01d280e808739e399c1c9e0e424718838911c188dff86f4e37501b8e8dba86d2636601b0d8d7a06b5835701a9e8d404699c34891a1d8d0206786337519980cbf4655e327319200c81063a2319e18b58c4bc61f830d2184f8c18c60602feb17dc0be145e922f04175b0ba305cc42e1416e30b6285a8a2d12166b0b26858982c0715ee8ae3c56162ac615450a914541229cd14c88a530522028e614550a20050ac281a13f809f184f382769139b09be84d6a268b132c098b84bf625c812ca895884a7024fc1260091ec483623f111d608d9c465622ef1155089b8445221ed10dd0861c42a82118106e0823840a4200d0fdb07dc43e6a1ede0f4c879503c1e1dd30ecb8756c3a2c1c else 0x27d8e3ec59f620fb0a7d823ebf9f5f0faf27d763eb99f5c0fada7d6a3eb39f590fac27d5e3ead9f560faaa7d523ea79f530fa927d463ea19f500fa7a7d3a3e9b9f4d0fa627d2e3e959f4a0fa4a7d223e8f9f470fa327d163e899f440fa1a7d0a3e839f410fa027cfe3e7d9f3e0f9ea7cf23e779f3b0f9d27ce63e719f380f9ba7cda3e6b9f350f9a27cce3e659f320f98a7cc23e5f9f2f0f9727cb63e599f2c0f95a7caa3e539f290f9427c9e3e4d9f260f92a7c923e479f230f9127c863e419f200f8fa7c7a3e3b9f1d0f8e27c6e3e359f1a0f8ca7c623e2f9f170f8b27c563e299f140f89a7c4a3e239f110f8827c3e3e1d9f0e0f86a7c323e179f0b0f8527c263e119f080f83a7c1a3e0b9f050f8227c0e3e059f020f80a7c023dff9eff0f7f27bf63df99efc0f7da7bea3df39ef90f7c27bde3ded9ef60f7aa7bd23de79ef30f7927bc63de19ef00f77a7bba3ddb9eed0f7627bae3dd59eea0f74a7ba23dcf9ee70f7327b963dc99ee40f71a7b8a3dc39ee10f7027b7e3dbd9ede0f6ea7b723db79edb0f6817b19bd801eb52f5647a9d3d41de9a8f4987a2e3d0a5e7a4f38479a43cbe9e57cf25578f63c679e2e8f12f78753c295e0c0f01b77eb3be21de86ef07776ebb9f5dc82edf376d2bb5c9da12ecb276293af81d736eb5f7588bab9dd4eaea2774f5ba705d2e6e91c74703a225d064e7ff73d439d45cde2e6a3731d39769cb4ee559727839265c896e3f471e0b8e39c692e2e9715fb8935c410e1cc70ccb84c1c1c4e0b8703538101bff6dfb66fbd37cf9be16deb46f2eb7819bb94dda06ea93747db9a2dc836e2cb70bdb80adbc96dc236cfdb606dabe6d3cb6919b3ded9b36cb736481b1c8d8966c243600dafa0d79d6bac35c05ad66d6776b1db57b5ab3ed55a6a8635365a94cd4586a09b4f39a6eed33b697fb4ac5a4fcd23068feb4729a32ed152688fb4345a118d050680a33f619f38cf69679b33b599cfece2866e4336799ac4cd38667e332b998c0cc3665f8b2ed59704cb466580b2af194eeca2064edb265992a2c90c6463b222d90b0c81c63de31e018e88c6ed634b3198d8c3cc5e262dc316158ab6c5166256b11598822c3c361ad30c0d857cc25560ff3070982e8c138607e302b980d2c0365ffd2fef97ee0bf345f80afaf17cb8be295ef22f6a17ac6bd275e712f25178b0bc015de2aee017664baf65d58ae98d7472b9f45ce0ae6157292b9165c71ae2317058b7f05bd5add096e1eb6d35b472d9496c3eb5c85abd2d4d569e0b4bd5a40ad0a967eeb3b259b6acca165d8b2b95935ac89963c2b1a558b4ac46d61acb09a582aac0655f84af7457932bbcd5d80ae7b571fab7c55b46ad5e5683ab32d591eac4a55fe2aeb956c0aaf755622a94953f6a9a454ab2a3fd513ea84853f429ed54ee0a719536ea99f54c5ea5ea52ce295)))) else (if j<13 then (if j<11 then (if j<10 then 0xe0e240ac0e1f044224e38388e095f810f8771c4e38480bc3e0f021f0e2390cbe0c3f810e638907e0f021f0e638906a5f051fc0472142d472297c147f011d47120ec682f0f830fe035e250e2394c4e2707810f8709076fb2f830fe011e1c24204bc1e023d1d47120fc1e023d1c850b51c703707808f4751c483f07808f4711c483085becb847061ec71211c1844858e2416969a42a581e0ea38f4be1a141ea40751c7a321787574903c8e0e228d57e1a490a0f0751c8e1a481e85070946e383d0a16070bc70783848210b880f070905e383c1c241125c307a141c251934854b03c1d471b868507a901d47190bc30791d480e1b868507a901d47183f81c070ca5c225f07104622e84cc0168af81256238e4622e84a12e0701c42bf0ca5c1c41188ba13303802bf0f8252c471c8ca12297c3c09962247870c0fc1e081c17141e120761c40b83f0613070bc1e071c48270c1f820705c5078382d87130bc30783b0e2e17860807e1c5c003c2587102f83c004c1e2f0f05800785c5c003c2d8713878007e1c4e1e001f87138780060270e2f0c2f800983c50b71f0012078b85e1f1f000f170bc4e1e001e2e17860c04f1f00300387c724a20580ca4063a0311018280be405da02e1016a80b24057a02b1015280a64051a0281013a809a404ba02510122808e4045a0221010a8082403fa01f100f280764039a01c100da806a4033a019100c2805e402da016100aa80524027a0131009280464021a0101007a803a401ba00d10062802e4015a00a1004a8022400fa0071003280164009a0041001a800a4003a001100027ffe3ffd9ffe0ffea7ff23ff79ffb0ffd27fe63ff19ff80ffba7fda3feb9ff50ffa27fce3fe59ff20ff8a7fc23fdf9fef0ff727fb63fd99fec0ff5a7faa3fd39fe90ff427f9e3fcd9fe60ff2a7f923fc79fe30ff127f863fc19fe00fefa7f7a3fbb9fdd0fee27f6e3fb59fda0feca7f623faf9fd70feb27f563fa99fd40fe9a7f4a3fa39fd10fe827f3e3f9d9fce0fe6a7f323f979fcb0fe527f263f919fc80fe3a7f1a3f8b9fc50fe227f0e3f859fc20fe0a7f023f7f9fbf0fdf27ef63f799fbc0fdda7eea3f739fb90fdc27ede3f6d9fb60fdaa7ed23f679fb30fd927ec63f619fb00fd7a7eba3f5b9fad0fd627eae3f559faa0fd4a7ea23f4f9fa70fd327e963f499fa40fd1a7e8a3f439fa10fd027e7e3f3d9f9e0fcea7e723f379f9b0fcd27e663f319f980fcba7e5a3f2b9f950fca27e4e3f259f920fc8a7e423f1f9f8f0fc727e363f199f8c0fc5a7e2a3f139f890fc427e1e3f0d9f860fc2a7e123f079f830fc127e063f019f800fbfa7dfa3efb9f7d0fbe27dee3ef59f7a0fbca7de23eef9f770fbb27dd63ee99f740fb9a7dca3ee39f710fb827dbe3edd9f6e0fb6a7db23ed79f6b0fb527da63ed19f680fb3a7d9a3ecb9f650fb2 else 0xd1ca52118944521e068f0e908e52c091e1d211487818731caf21188842c095a1d2118964421604c84387484825118878163c3a423e058f0e908984c16001f8161838c8415cac524311a0b84c1e088b8107e001c73198ac38031e23101d8ac38031e2310198ac461b0a0111880ec662c018f11880cc561c0222c7880cc661c018f11880cc66230d850088c4076230a00c388c4068044620c5118cc38031e2310181e0ec389040783b0e24103fc307a901d87181ec70709c40783b0e24101e0ec389040b93e0e24270bc35203c1c25143fc307a901d87189fc1e013b0e128b8e0f638384e270780c74b8905e0f028e241383c08bd1c482f0781470b89058bd078f62120b17e0f038e24141e0e638904e0c4b8705710946e1f0625c0828946e1f0625c0834158e3b0591c38bf0624c0e3c1a0a57078187138825c2f0c1ea4c383870b85b870f5221e1c3f0f824fe01384a37049fc02761c48361787c127f009d871f0bc324704c3871814050bf0f000fc38e0a8bf0f000fc38c0be3e001e241707809203d8e282f8f8007890504f0e48a2a385c604f0f01245151c60a0280b86e1e001ec72017c3e3e01480f1b8252e19148da2098e1aca607004a2291b45872493c12970c8ba2128e52e19148d87108d94c470ca5c1c01148d872414c602f0f000fc38e17e18594b8043c3c7050198bc3c003f0e3894afc48709222370c0c919211d1c302f8741e3c9042302f0bc3e3e01480f1c280a03617878007b1c80370ccb8123a386c76038652e112c8c45c6938ec015c95c7231171a463b01c42bf0ca44622e349e1e00ae52e39188b8d201405e1c8782170761c80525f874090f070e0e201208e0e0f8147120e090470707c0a3890705f0643c707090605f0643c707090687f00970e4b11d243d0f83c0e39142c32304bc1e011c48370f83c0291144a370781c7228585e27078024138e2212060a0482387c1e04928e172783c0e389040bf0781c7120bc3e0f018e240b8c27e0f038e241412080301419c3e0f0249472892480670f83c01251c887c384bc3e0f004847204bc390f048f0e1817c3a070643c79203880783b87c1e051d48172181c310f068e0e0b8e0f0770687c0638907e0b028621e3838483f051fc04751c483707808f4711c48301783c047a3a8e241c120822f0f83c02911b0e4f0f8252e01188a131cb5c1257008c45c38e492470f8252e01144a414b864622e1c44370f8252e01188b871e1f0e02f0f83c0839908055180bc3a0487820ec392c6a070e43c183c3870501a8bc3a048783870713c1e071c4e20241003e1f078124a390c3e0f008e24161f0e0299787c1e00908e482f8740e0c878f2407100f0750f83c0638907a1f058021e38384839941e0e0370f83c01231c90b83c1dc1e071c48383c1c05e1f0780246390170330387c1108938) else (if j<12 then 0x4923d1c85a3920f81b0e02c18907e0ac7a0438b61c4a0ac78448464283c1d4761a58642a4b86460783a8e57222c4387c398e57c28e0f070918e20942d9287e158f0e1e2d8507b1c1c57190a0f0751d8696184b0f8751d482a181e0ea3a9051015e0ac561c0622c72b438a21e03024b239906865150b4341a068e57489241c015b022163948723603025763948686511094241204069132130562b0e030e0e51e22406e1881a3a44c832150681a3a44ca8e1c83802b6044347290f4542d0d06812b23a8e91244b8061e054247320f01104398f11320d0361c043f0e3231e22423208c461c0985010e14a22506d190163c44c8340d870112c38c8c788908a44f0f8380a395c721e0302472915c686016868340d1cae91208b83c044b02472b8f464350d06812923a8e9124964620e0302212931cac4c3e8741408698e8e4b910ca2212874241204345648949722e130580c0958a445190d4340a3834c748910ca221284824080d226425228441a09028e320f8320e022443c08858e57262f84226088441c015b02212917a18be230982c0e00c8421286824095d1c91321017c210f0580c0990741a06868e1231d223a12868240a3922641f0780126058e571a2f8421e0b0181320e12c1e0302c72292cbe405f0982c011b024a2d1188c1e870380290208a6524428e0320d02c748d14823114884321607005729239425a1903c348d1d1c322b8747508841c0604a421a39587c19070043c0820c821a3934341a04c891a3a387c030f0247320a56294208d8312c488b81c04848e65190d4341a04a491a3a389e1e052347470b06634158ac3a08818f0e260ac581b0e821f63c38882b1608c461c0985410e438a8331a0ac5a086d8f0e218ac38431e462b1986c78448c58331a08c461c0985410d438a623098708918a068240e04098731476330d8f08918a2170359a4c662b0d8f418714c561b1e11211442d262b0f89c26e5061c4885acd263315b6c7a0c38962b0d8f08908ac661b1e11211442d66330f89c26d5061c4b1184c38448456371387c2a0c398a3b1986c784484562b0f030ea3c4466330f0311a3c386c0b0e2347870a21c0c3a8ec6888d81e14461c64160ac3c09918f0e888e456230d85818714a224313030e88990582b0f026488b1e1c3b180b812970d8f118710c461b0b030e88990761e06230e320ac602b0f025263c461c43198ac363d061c331586c7a0c38562b1186c2a0c386633158f41870ac561b1e830e158cc363d061c2b1988c3615061c331184c3a0c38524d058b0e118cc363d061c2b0f032123c38ae360642478715c525917030e6395a423e04acc7909485c095a1c52908a45c095a1d21290c4521e058f0e25c847229118642c0c3a42522302c7874844c09921d21130b83c003f020e6395c8c260b000fc0b0c1c64221c46c else 0x580b4763150f8751c4e241542146370f8347470e1202a3e8e8e144a49246048380200328e272a1e894450503404043a8e27284b0fc0e021c47120f0f8723182c061d1c48443d1f0e4730e8e241d25466350d86c190d061cc72a43446250984c1205061ca42a88c4a1d0984c152485874123438c492168943a148682c6871292a331a86c360c86830e639546a1c86830e638c0c2515c0bc3e0d02434726421d82d0503474b43880e95d1343a0a0506a4a3c38a25f1385c190d0048386282818731e24971c3089a0a061cc7920e8fa0c398e2414184b02f1387c2e0c92434029174442509054140c86802787168a034168683a0a0642c7871543a089242c7870c4a2370e43c10751c7908520b4140d028e96871214a1d05034090a0d49478714250a60f02a490d008f0e2424c660c87870e63d00890b1184c187500483c4186c1e15021c241d88c260c8586248750086b0480bc390d018d0e22208f61b0448c7a043888843a8027120a126330d832163c3a80444188c1a043848330d822490d018f0e1e434140d0386c78725c845d110942415050321a009e1c5a2a8c86a1a0e828190d018f0e2e208f6360d86c1095018f0e2a20c46130587408709084bc411ec3a0438483c411f466350d87416084a80c787180d82d0d074163c392e40360b444250905414b438945a1105405220e1d4d21148641d018f0ea68f4063d361c250503404024a1f0e4b51c9c0e021f0e6195c8e92211288a1d0503404020d49472b9605c1e07009287c388e57241e0e60b0286c7920e0f0730580c7a1c9076230842c1a183a483b0442c7a183a4833058021a1b1c1d241d81430733648280e8281a02018e978910894450503404050d8f24241e0ea1f0780c7120ec16050c1e0e63c9070783925c4e1f0b83c02ba14a61b05812442b1cae3c908dc3e0f018e571d8e242f95c4078390ac360b004b2463920f0730d82c02341648c7241e0e63890ca283c1cc461305805713908561b0580926395c70783982c06389068bb1186c292419822142838a6230d852482b0442460713168921586c1108398e57242ec46130580210709088b44a0c4642b0d82c0828858e0e322ec46130442c00709088bc5a2506604141ccd230643c090700409243e1c056395cca22128482a0a0680802bc3e1c27328683a0a0680800343e1d2463966512f0f83c01243e1cc7270844c110b0241c0100af0f8709cc0bf1385c1e043e1c24200bc3e0f021f0e1231c88b4490b8361e0583806003c1cc72b9a05c190cac460783896c7241e0e1231c487c398f2410255687d198f0e1a8281a0201250f8751d2c48970643c0907004002c3e1ca4a39943a0a06808041c3e1ca4a39586c1e07009287c388e852683406183c1d47520e96492188d43a0d0224850783a8e631b87c1e044a1f0e82d1c912f0f83c)) else (if j<15 then (if j<14 then 0x671a18894450503404050f0e642a1f0ea0b0680c061e1cc84958a50f47c391d4361d058340601188b873e1e8f8723a8340c399080611783c061e1cac392491c1e00970e641e1e8f8723982c0c39908e0f00ad87290a49247078187338c89442050067c3990722e0701872b1486249238643e0f00c98721128840a030e67189248e0f030e641b0380c3928ce2e07018732090f87225114340a030e64248781c061cc8290f0380c3990524920a5c3e0f008d87229381c011b0e4a2d0c5247a3b87c1e01188b87251e8ee1f0780453241c80d23182c083990687c388bc1e041cc83a3d82c032239862483908f471160e64161e8f872388bc3e0f00c9072a1e8f8723a0e641a1f0e22c1cce641a1f0e61c1cb4641a1e8f872398707320ea18931b87c183a3876330d82c02923d1c458393122923e0e8e168cc6a2b158321a090f0f0e2a8ac5a1b0d8321a091b0f0e2a8b4390e1e82c6870f466350d86c190d070e45871546a1c870f4162c387a350e434122a1e1c395b8321295030e3062828190c3b0e641d1f418721cc829288bc3e0c8681871d154542d0d074140d02438787169222d0e832143c3876331583218741e803b198b21e1f061d07a0112183d018d0e16208f62b0d834083c3886330d83218741e803c860f4062c3858823d8cc360d020f0e22208f60b0e8107870f10630860f408731472511b87c190d030e0e21144602d0d074140d024387871612a350e834090a1e1c40368c86c3d05250e1d148541d030f0ea68e92a021e9b0e168281a02021f0ea1e1cc84e07010f871170e5629100f075068087320d0622b0f0241c01021f0ec3948bc1e07010e87838c987210b43a0d021d0f071910e4e07000f0730f0e641c8c0f0730f0e52188a0f0761cc82c3e1c8732088f475058340604918e41249143e0f028e241f83c08915c8f431b872461f0780c72b8e8f4770d87c1e04918e428787c19271187c260a38987c39874160d018124a195d8e5f1385c1e009c506014ac46e1f07804b63920c2492383c01231c7e1c9087c1e051cae3830924802f0f83c09251cbe54311288a0a068080a389cae5707814752088f4770d87c1e02928e423d1dc1e051d48342611018051d4ea41d42c6e0f0d8347470f0f8750583406051d48443d1f0e4750e82c1a030186a4a3990f47c391d41a02168ea4249248e0f028e24189248e190f83c09251c844a21028041c928e652018492401787c1e0490ca4c3d1288a0a0680808709e8e54311288a0a06808013d1cae50170781c04488e571e194140d01000363c492e4c311288a0a06808063d0e48560f0241c010224430631cae543e1c894450d028063c90987c3b03801231cae386d18c16051c48343e1cc16051c48323d82c012a398624a3901247a380ad6a3b18787a3e1c8e60b018624a3921287a3e1c8ee1b else 0x48412491c1e005e8e241e1f0ea0b0680c061d1d48492491c1e051c48306d18c16051c48343e1cc16030c49471d1ec16023986251251c80a31586c1508951d47221f0e4630580c3a3890887c39874160d0181439225d8e5f1385c1e009c587a3e1c8e61d0583406050e48c7321e8f8723a8340a18918e4c5a1f0e61b0580c7a2a5c9128309248e0f0048c7221e8f8723982c012b1e48485a1e8f8723b875212b1e8a50589248e1f078124a385c98650e8281a020034c745c58a47a384ec7120a8c61b0580c70b890787c3986c1601158f240b928f60b011cc7138d0f47c391cc360b008b2463950f8723182c06385c48428588c3613051c241c2ec461305808f4709c887c3918c16005d8e24221e8f8750d82c04731c48492491c321f078124a390894470d07c1e04928e4124900622f0f83c0064928e523112884301787c1e04928e512491c1e00328e271d1e8ee1f078024a38f0f8770f83c022c908e443f03808711c48343d1e8ea0d021d47121121a2b1686c360d052f0e639521a231284c26090e830e521496a2b1686c360d06430e639545a1d06430e638c97a2312874261305492161d048b0e364297435128421a0c39484d1287425248682458710172511787c19083a8e40750b4140c3a8f1749108fa1d042ea4a3c38725f1385c190d004838628a85a0a061cc745c58912d06430e63890690b1586c163d021c172242c461b098340870908304418217a031e1c24202cc561b06434063c388883058f408709060bb1184c190b0c49408713210b859a40610d021cc524491061b0680c78705c8885004f0e120b1047b0d83401231e1c405a20c561b058f400bc3890bc4188c361306810e12134562d0d874160d0242168731cb8823e88c3a1506801787090a2511787c190d001d4722421442d0503404b51e1c922b87c190d008f0e182985c1a5b83214311e1c4d0e834090a928f0e1c9640e270f8521e0c901c4c860c05a1a0e8281a031d170e2c4b43a0d00492163c388a250a8340908921c38360d4542d0d074163a2e1c50360c85a22118742415061c922e80c7a6c384a02929b0e1186c16045e8ea4181e0e60b0148c38bd1c84b03c1d4762c5c68ba9e8ea4118ac310b062e0ea38e2160c5c1d47520cc360b0043470745c76003a8ecd8b8b0642b0e8281a02021f0ea3a48b07f0f83c0072928e172182c0a1b1d2f24181e0e60b018f43920ec461085820ea1c907608858f4307490660b0042c7a183a483b02860e66c905a0a06808045d0d8f24214b0f8770781431231c80783a874160d01809763c90a47f0f83c04b2390d472187168331e430e1b83c0c3990447a3b86c3e0f00c987204a8f477078187320ec5e0a8786c14761c787c3a82c1a0301878732120c2370780c3c39487249208bc1e061cc83d188b43e0f030e521c9248e0f030e) else (if j<16 then 0x891100bc38731c97111a1c2463c4442570f008ea3a44682d0e828141d1cae8e20388580b0701478729084751c489113878041c912347470e4ae1e011d47488c83488928e8e150691e1d1cae8e180b81c044b86472b8f4140b1c068e8925c7a0a07014363a3a483933078120c4886c7c015c98850d038063a3a483c428781c015d8e241c9849c09068f80138f1041d050224a3a38712c421d81c00908e3e0c4b4123c4642344785411248456189300c788c8464e1711cc461b0b001288c40a4731301118809066189300c788c8466360e86c3096018f1190928e6331184c3c004a23102622c3a0892422b198612c031e23211d0ac363c38af111a1c2463c444e1c398f112b8ac7888921c202e12c1c031e18a41c2c0f84c1586c105a918f8086170942b1184c10be0218a424270960b1f010c520e1609c1586a4c031e1e403c17096330525c30931f010c2e17096230d84c1c043148483e12c30be0218a41c260f84b1986c1490498f808616202bc158ac340b1cad0e2487802591f1a641a8a85a1a0e03472ba3882b13300c7296346c691b00c72b9486a221284828080d1c64220ac5618730347870e1b80d1d1c64150a83a3e04ca8e18ac4cc051f1a521a8a85a1a0cad814751c8476018647c69906106058f0e320b036187cc98163c38722c1188c381308398129438a0db1f030e320b0361894c98163c387c690f00472915c602d0d0701a3a38ae3c488b8023e34ae35190c52e1e068e8e1c984b23600a4c7c69588a1e058e1a4725c6a2212874241404345647129722e00ad8d290d464350c358163a387a22128482a1e04c88e210883416011c641a244cc031c8657c68f172b1308842c014b1a445f018d320884a1a0b02574719070b90f018d320a83a189302c7470c84a1a0b0264470c12c06358e57162e43c0634c8284898462290f004b63e3490b9308c452210b00c325634a04600a445c6994604815078163d191c39188a442190b00572923f1a8e2d0dc3c0d1d1c29489980a395b1a31301180219928f8d1e8683c09928e8e1b00c323e34c8295a2452236021c4523e349a321a8683296068e8e2018c3e0f030f0b2b0e492450f83c0c3a5c7c0e030e524b8b0ca0d010e524b8c270660483802061ca517270380c3c5cc82893038061e1ca4171c48c3c0e00ad878b8e8f61b0601078745c72494b8340c3a5c6865050e524b8a0e2512787c1a061d2e4486834061a1e1c971e4341a070d0f0e4b8f4561d010f0e4b8c45a1d010f0e4b8c1244a2307c1e051cae422511c1e060e8e241c9383e0a4a8e961a4285a1505250e4b0e490770525474b0c250a23f0781a011e1ca4264285a0d028e9287258806a2e8a85a0b1e1c962280c74b439242b1e809287258542d128540494392c3a1703802395d243506810f8721525474b1043a0b0680c04bb1e else (if j<17 then 0x39097a0d018e27162e50a231284c2a0b05802727164f2744b87c1e041a0ac7260d0560f1387c28bc498062283613078389248e0f00358712130c0770d80c3e0c930e3f0d87c1e04930e30941e0ee1f078124c391c1e009f0e203c1c492470f83c012c9049872618052b11b86516061c9c412491c1e061c483305802783889061b051c8512c920e423d86c1602390b24838949075058387a029062803a874160b0d4987a01312491410b43a0d030ec626834061a1d482a961d402321787c15221c9a331a86c3201470ec13092130792787c10a04b0f4026144ca0b0680c061e1d48413e874160d01804e2330d49872e2492279390b43a0d030ec62a834061a1d482a968741a01190aa4439112285198d4361d0582c0c3938b0bc26108560b030f0c5213098430d82c0c3c3148405c1e0e84c21878786290952f0c9e87270a125213f0e4e15874160d018187520e25c2a909fc3e0f009c24c395c327e1c9c20941f43a0b0680c0520398624c3980f0721683405229470970c9ea4439386a0d018687520aa587c384a85e1f0780a41221cb079180bc3e0e1d804e23864ec393c4892498d056193f0e4e2303872925c426604821dc394a2e3e3b83801261d87171c4981c3b0c2e521848c3c0e1cad1719870083c862e283e12c56085f000ac3c30907c258cc360e00158786121707c25821261e030f0c25128ee0e028e57191c24a3a98407c25820bc031c490c202780638921e283e12c105e018e2486101307c258380638921842468e24470891a38911c244448c787084ae1e012347470d43a0a0434c7474587e1e01072448d1d1c392b878048d1d1c32251dc3e0c9301471c9849c09070147138f10c0c384847151cc561c002fc288c402c4a39890088c40483239870063c4620171d1cc461b0a011188058861c0048c788c8464731587008885e20c7211cc56230a001688c40862b0e001688b1e423b0e001790890561d1e230e4b0a0b84b0700c7862907854258ac360e018f0c4b930b84b1184c1c0431484425838063c314833158696c031e1e342a12c360e018f0c4b910b84b1184c1c043148403e12c3c025e18a41c1f0961b05498063c30801a470e8e320a8e60e020e641429104730587808399084823982c3326020e38958a91e1a020ea11cacc561b054307c00951c4d0c3491c39591c311703802961cac3051210ea0897008732108348e1cc88e14998120e00a414c39588c46070187320b4348e1d1c64148781c061cc82c412108a1e010e641c8781c061cc829308a14237070ec325101422f0ca446c3a887a2c004b1143c846a2d0e011143c84662b0f011183c8466330f010788c84661e022307908b8083b162321142e0f84b1586c1056030f0c281f096330d820ac061e18485c1f09608498780c3c3090bc2410c50903f018763430a4751c4 else 0x524349a484230f05404b92a0869350d404bc392c44349b408725c532085104461d0b0257c012a03011b03002b958710e06005710364f1261c9c2f078027c3c94522e1e484f274946075058240c3a906275058687520a500750e82c161a928187268ac5a1b0c8051c398480a12b0f4027c9462650583406030f0ea4209941a030d0ea4189f43a0b0680c02711586a4c39716a2b1686c3a0b04c2c0c3938b84c2182c00be1e1892209e4ec3c5c402f0f82c0c39222e39249181c051c99241c9248c0e028e4c920e4924607004ca3c9070783892482651e48383c1c49241328f241c1e0e24923064ca3c9084b83a82c12809d8e383a82c12809d8e325e82c71389446250d874261100485130940f25926804c920c4fa0b0680c02709d8e413e82c1a03009cc71)))))
def mo255H10 (j : Nat) : Nat := (if j<7 then (if j<3 then (if j<1 then 0x90b90000326b14bd0000d1501560c0d4000001240000000000002dcf000000000000ad0b000000000000000000000074000000000000516f000000000000000000000000000000007010c977000000000000e0c0426c8be40000f0bebdb0e02b000073e7921b0000210800000000000000000000540f00000000000012a60000000000000000000000000ba5000002ba000000000000000000000000000000001b3d9504ad4da29a00000000000000000000000000000000c3eb0000000000000000000000000000000000000000e34a00006489648e00000000935800000000000022c3000000000000000061a30000000000000000c51c0000000000000000000000003be5000090aa00000000000093190000b28e0000000000007b100000000000000000000000000000000000000000000000004d4c0000000000000000a4730000000074060000000000001a8b000000000000000000000000c3f200000000cc6834310000000000000000000000000000b0bb00000000a3a40000eb6ff1187226420254c0000000000000224265210000c49500006497440700000000000000000000000010b86be38066b569e37c0000000000000000000000000000000000000000000000000000f2fd000000000000233f0000000000000000000000005c142559000000000000000064d100000000000000000000000034ec00000000f5810d5600000000000000000000000000000000000000000000c1dc00001a690000000060480000005bb4f30000f1bc0000000000006332419700000000f40800000000000000000000d3781975e339639935c6313800000000e59a0000d57600000000000094ac953d15910000000042721c2d0000000000000000c1c8000000000000000032a000000000414500000000000000000000000013a2042344d700000000000000000000c017000032f4000000000000000000000000000000000000000000000000000000000000625d000014a6000000000000000000000000000000000000000000000000541f000000000000000000000000789f0000000075a0001002300004500120000211200504010200812100320022200400100020020030042101003003001010000012310032302100030011110232112200000121000211341010020040104213001001610010000030030001031302000000003200000200100102110132000010000315001030314111120301021200000111020000110003000000110000000010200003100000101302000002211120030630001200000000000100001031021021013003000102200350202000203103043332100000001000000110022012000210200120003014000021340003032111001002010000211000003e0005011210020171000 else (if j<2 then 0xb5a7f03000000000bdccec8922864db4000000008403d3f30000000000000000255400000000000000000000000000000000698b000000000000000000000000000000000000000000000000000000000000000080f70000000010373287000000000000815e0000317e0000000000004bee00000000000000000000000000000000000000000000000000000000896e91870000000000000000c17b0000a3b6000000008165000000000000000000000000000000009b4b00007918000000000000637f00000000fba3a1400000fbdbe441c4a80000f2c6000094bcc204725a921644867409f10f000000000000000032f0720d000041fa0000000000000000000000000000000000000000000000000000000000000000000000000c550000ad59000000000000000000000000000000000000000000000000000054720000b1ec717c52a40000000000000000000000000000f2ac00000000cd090000000000000000000000000000000084e600000000000000000000000000000000d851bb760000e0d2c0810000000000000000000000000000735600000000000024140000e266000000000000000000000000129b00000000000000000000c9ff00000000707b25966ae165cc0000732731ba000000000000000000008c23103e000000000000000000000000000000000000000000000000000000000000000000000000000004d900000000f1950000000000000000000000000000623b0000c48300000292000034f400000000000073ff0000538f000000000000000000000000e3acf48f00000000354d0000000000000000000090ef000000000000d46300000000310b00000000000000000000936d0000000000000000000060fdcb740000000000002040000000000000000000000000000000000000000000000000000000000000c3b9000065c10000000083520000000094df00000000000000000000a4b803070000c2de0000000095789163da5c006300000000f1f311c60000000073970d5f000043010000000000000000000000000000a5820000000000000000000000000000000000000000c39e00000000011d00000000000070010000000000008b070000000000000000000000000000c06d000063aa00000000738300000000000000000000000063cac4dc00000000e4480000000000000807382f92bf1816daab00000000f53c80c82b4e0000e40d558583dde48094fd00000000b28000000000b1e7000000000000000000000000000000005190000000002220b0ca0000000000000000741000000000300b00000000000024af0000f28c000000000000000000000000e1b70000000000000000000000e700003981000000000000000000000000c2da000000000000000005a300003361515f00000 else 0x136000000000000000000000000330300000000000000000000000000009141f315f53800424347736ad1f9000053c100000000e59b0000000000000000c08e246b000000000000000000000000000000002bea000000000000000085480000b2f7000000000000125975b3112200000000000000000000000000000000000000000000e2890000000000000000c1f6188c00000b0e0000000000000000000000000000000000000000000000000000225b344600000000603f0000000050980000000000000000000000000000000000000000c82b0000a0544451000000000000000000000000fbb3000000003c7900002284c51d000000000000000000000000b29c000011440000000000000000000000000000a35b00000d5b9885138a517553443bb858529a7500000000d0887c1c000000000000dbf5000000000000000060920000e5bf000000000000000000000000c00900000000000000000000000000000000000000000000000000000000000000000000000000000000c4c6000000000000000000000000000000004d0e00000000651e00000000000000000000000000000000000000000000948b0000000064b4000000000000000000000000000048860000000000000000000000000000a3ed0000c0f9704a00005aad0000e18f782e00000000390400009a6e316d0000000000000000000000000000e99300000000000000000000000000000000000000006594000001690000fb0ae3d4000025530000000000000000000000000000e55e52b800000000000000001477000000000000b1ee00000000891de01b00000000000200000000211b00003105000000000000000000000000158b00008ac4d1610000b18d000000000000000000000000000000000000000000000000000000000000000051fd22a7911444d8000000000000000000000000000000000000e47900005bb10000000000005588bb7800000000c023288b60ad0000000000000000e168d5000000cbdc00000000b526000000000b5100000000000000000000dd26000000003b480000d02600000000d4c900000000000000000000000000009adc0000000000000000000000000000000000000000725f00000000f11700000000000000000000000000000000b4c100000000c39c0000000000009d60892400000000000045491ab1000000000000000000000000611ae087000000000000000019db251080d6921c00000000000000000000000044fb0000000070d8532a00000000000000000000456200000000000000001049e0560000000000000000000055aa00000000000000009110000000000000000000009a02000000000000000000000000c065000000000000858f00000000000020c3914900000000000000000000842d0000000000000)) else (if j<5 then (if j<4 then 0x444300000000000000000000b19d000000000000a1f500000000e08c00000000000082370000000000000000000083660000000000000000000000000000000000000000e11f00000000000000000000000060d9000000000000000000000000000000000000000030590000000000000000000000000000000000000000e23a0000b989000000000000000000000000227d00000000000000000000000000000000000000005bf7957e00000000000003b8138874d00000000000000000441c0000000000000000303ba42700000000556d710a243e0000c349122ee2e9000000000000000000000000000000000000b5af0000a4f5250b00000000d4a45da4000041bd0000603c000000000000000000000000000000000000000000000000000000000000000000003b0f000000000000d97f434cf3b4000091cff4440000000000000000009d00000000aaa2423e242a0000b04b0000000000001b9c0000000000000000000000000000000040470000049dc01f83d25c780000000000000000000000000000000002fb40c500000000000000009536f11c6b3b000000000000000000000000000000000b81000075310000dceac0b10000000052bc0000d4f900000000f03900000000c25400000000dc2100000000598800000000000000000000956c00000000000000000000000000009487000000000000702f0000a3205428a49c000000001a74a103d38701d700000000000000000000037e0000a3c0000000000000e45c00000000514a00000000a5c97314a2f9000000000000000000000000000081d93d9b0000f3420000a207f08b72180000e4b3000000005213fd9900000000000000000000e2ee0af70000718100000000000093fe0000000000000984f23371e90000000000000000000000000000c264000000000000000082a5000000000000cd626aa89aaa54e700000000000000007b6d829763bb00000000e185000000006c22000000003485000000000000000000000000a0b60000c850000000000000832d00000177000000000000520534e522bd0000a56fdc9000000000e1db0000e492751849fb0000000000000000c0d10000000000000000cd8c00000000000000000000000000000000450cad54047800000000000000004498612b000000000000000000000000000000000000000000000000a94b0000000000000000e97d628101fe000011c7d35e03260000000000000000000000003572b44d00000000000072830000000000000000000000000000000000000000000002b9cc05000000000000000000000000000000000000000090990000312afa5300000000000000000000000003a7000000004 else 0x721a00000000659900000000000061c50000000000000000000000000000000000000000000083e8000000000000000000000000349900000000000000000000000000000000012f000000000000000000000000ac5600000000000000000000f4e2000000000000e2620000000040750000000074e0000000000000000000000000283600000000218cb0e10000000090bc5b6ab9f9000000000000000000000000843675631ab5000000000000f5b20000000000000000b06725980000000000000000358c95020000000000000000000035120000d07d00000000000000000000000000000000d46d000000000000000000000000000000000000f1bb00005b46adae0000b474aa15da0300000000000000008a09f1e56386000000000000940bb02ce18232d5435a0000000000000000000000000000b30855614128000000000000000000000000000093940000000000000000c30c52cb00007310559c838501c4000000000000000000000000346f000000000000000000000000000000000000807e01a430bf0000036c525100000000000000009ab4cb40604673c70000c3790000000000000000a47500000000a421000000000000000000000000000000000000000000000000e16400000000000000000000000000000000324e00000000000000000000c384000000006248196600000000000000000000000000000000000000000000000000000000b1c0c2320000e4710000d1a20000000000000000000000000000000070c40000000011f281e4000060130000000000000000000000000000f0cd000014580000000000000000000000000000000000000000000000000000faf300000000000000000000000000002db60130f55c8815000051b600000000a00d000000000000f3e20000000000000000000009e48bb593a60000f14e342200000000383b99ee00001494000000000000000000000000e2222036000000000000000000000000000000000000000030ee000000000000000063ce000000000000000042d90000623873500000000000000000b13f000000006005e0a5000000000000000000000000c5c7000000000000000000000000c133a5580000000000000000f51a000033cf92c50000000000000000000000005064218e1b4fd203b38da21504a50000000082090000c16e000075a5a1200000000000000000000000000000901800000000506a000000000000000000000000000000000000000000000000aa78000000009aae0000000000000000000000009922547d000000000000000000000000000090a6000099ef00000000000000000000000000000000539100000000e0450000b0cc0000218654660000c0950241f4b7000000000000000000000000745284de0000000000000000aa6500000) else (if j<6 then 0xbbb60000b2be8869d5b00000000000000000509c0000117f315400007bca000000006003000000000000d9780000000000005d0f0000ea9a000000000000f4a96255452e0000000013d00000000044b0000000000000e2bb000000000000c3f900000000000082d8c490dd61000000000000000000001a5e0000000000000000000000000000000000000000000000000b3c00000000000000000000000000000000000000000000e3950000932b0000d501306f23ad00000126000000000000000000000000e1b50000000000000000000000000000000000000000718a931804bb62ea000000000000000093630000537a93240524e9030000a31a00000000157c000000000000fa66000000000000000000000000c337000092100000000080fe000000000000000020a40000000000000000000000001132000000000000000000000000c35521eb000023382aa6952bb1b303cb000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000094e175c8000000000000000000009162000000000000000000000000000000000000a9ebf2cc259200000b430000d26fe143d996000000000000000000006c1600005ce000000000000000000000000000003022c4c50000000000000000c3df000000003be1000000008400319b00000000000000000000000000008a720000000000000000c32e00000000f04f0000000035110000000000000000000040a800000000000000000000bb3a000041f80000000000000000000074b6e14bb55a000000000000493360f5217d2d58000000000000000000000000000000003dc0000062b00000000015bc000000000000000020eb0000000011d5000000001273000000002920000000003263052d000000000000f135000000000000000000006309000040340000e2300000b357000000000000403d0000000000000000000000000000000000000000000000000000999200000000000000005021dae40000000000000000000000000000000040b319830000000000000000b1010000000000000000000000000000a25700000000000003d3f15d000000000000000000000000bdb3000000000000000000003078000000000000727800000000000000000000000000007381e2e044ea00000000000000000000f0da00000000000000000000000000000000000012f5d0f24a6b91ad0000000000000000b39a000000000000000000000000000000000000000000000000691fe57194ce00007a5d00000000000000000000000000000000000000000000a2e600005a6c0000c5ab0000000000000000000000000000000000002b45b146dbf0000000000000000000000000000000000000000000000000e9fe0 else 0xd2240000000000003b4a3d5e65b90000000000000000153b0000000000000000094041a1000000002513000000000000244f0000d243000000000000000000006c7a0000000000002493000000000000000000000000f4eb00000000000000000000b31c000000000000000000000000a1120000e24600000000000000003c1e00000000000000000000d2e80000e888000000001ba80000000000000000000084450000000000004dc4000000005166000000000000000022230000944c2016030e64810000c595732f00000000000000000000000000000000000000000000e5cd000000000000c97600000000000000000000000000000000000000000000424700000000326a00000000cc2e000060ea00000000000081d27b3f73c500000000f3fc00000000000010df000000000000047e000000000000000000000000205dd5470000783a00000000000003c21994c24f000000000000000001df00000000815c00000000000000008244000000000000024c341600003d5a00000000000000000000982c00000000b3ef000000003b39000000000000000020a100000000000000000000000000008a5a84ba00000000b3cc00000b9a00000000f04da4c462e200000000e1ab0000000079350000a4c8000092a9000000000000b2c0000000000000000000000000000040cf515aeb6c1c6e00000000b3c3000000000000147a8568ab79000000000000754f00006aa410b40000000062cd0aac0000796b0000000000007c2f00000000000000000000000000000000c377000041ce0000000000000000d0a20000000000000adec1bff30a000065841076d3ec906c000049e1000000000000f5c400000000d1ef228d0000a464000000000000000000005c119b91096a9240c21f4c48439f0000000000000000000073410000000000000000000000000000000000000af10000a5290000000000000000000000000000000000000000b0a7f88700002c070000935c0000000000000000000000000000000000000000000000002ae600004236647c0000000000000000000000000000000003f40000b01c00000000555700000000000000000000000000000000000000000000000013f8433e0000a9700000000065450000000000000000000022e50000000000001079bb86c9910000000000000000000000000000253500000000000000000000000000000000000000000ada00000000ebf3f4500000dc08000000000000703a000034b200000000000000000000000000000000d5a60000000065b1e317b43800003a600000000000000000000015650000f26800000c120000000000000000000000000000f19800000000fd63e3530000000062f30000745a0000000000000000d57d00000000000000000))) else (if j<11 then (if j<9 then (if j<8 then 0x99f0000003da0000e1a80000000000000000d25200000000000009f60000000000000000000000000000206b0000000072f100008465041e0000013400000000000000000000000000000000e3a8c39300000000a5080000a0c1000000000000d917c2af000000000000000000000000d38c2d10000018a0345705220000000000000000000082d000000000000045870000000000000000000000000000000051a500000000007c000000000000334d000000000000c1d0000052c1245f000000000bb400000000000000000000000000000000b419f3340000000000000000639200000000000075077033000000000000000000000000c5790000000000c9000000000000659722850000000000000000000000002043000000000000000000000000000000000000000000002a5900000000000053216469000000000000000000000000000000000000000000006c030000000074530000000000000000b1da3b7a00000000000000000000000000003bb9c46700003a5b00000000000000000000330f000000000000000000000000000000000000718b99050000000040db00000000000044f6000000000000000000000000d5ca0000000000000000000000000000d1e80000549f0000000093bc0000000000000000000000000000d09400000000db52a0f4c51f0000000000000000000000000000000000000000000000000000abfe000000000000549b0000429000000000000011e11147a544c1090000452821b4da64000000000000b2fa00000000000014f2000000002411000000000000000000009020dd57000005860000000000000000000083890000000000006031000000000000000081520000443000000000402a000000000000000000000000000080dc000000000000000000000000000000000000000029f8610073220000000000000000000071cddbdd754103de000021ac000072dd63a00000a2df000000003c5009ed0000429d0000000012b210a0427100000000000000000000a96c000000000000000020629d6500000000027c000000008973000000000000000055030000000000f3000000000000000000000000e5890000000045a900000000000002db0000000004320000b4240000000000000000000000000000207200000000000000000000000000000000b30d00000000000000000000000000003aa70000000041fb00000000000000000000d412000000000000000000000000d00821dd000005b50000229500000000819a000000000000000000000000cbe70000000054d40000000000000000000072350000000000000000523c0000d055f1de0000000000000000000000000000c1e2000000000000000000000000000094b5a9ddf04400000000000094040000936400000 else 0x42eb0000000000000000c34e000073a1c159032300000000118400000000000000000000000000000000000000000000000000000000236e00000000000000000000000000000000000000000000000000000000000000000000207fab444d5c00000000000000000000e4a700000000401a000033af00000000dc200000000000000000000000000000000000000000a3c80000553300000000000000000000000000000000f0b50000000000002997814f000000000000947b00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000b16b848200000000000023e400000000000000de00000000000000004249000000000000fbed0000000000000000000093fd000000000000a81700000000000000000000000000000000000009fc34cb000000000000000000000000b33d051443c900000000000080f81258416a159e0000832800000000000000000000832900000261aab8000000000000000000000000000000000000000052a1d26d0000e4b1000000000000000000000000000000000000b10c0000d3e50000000000000000000000000000000000000000000000000000000000000000000042940000000000000000e2c200000000000000000000000000000000000000000000000000000000000000000000a0e40000e17000000000c9d9aba6000049de00000000000000000000000000000000bce70000000000000000000000000000e972000000000000000000000000000000000000000000000000928200000000087c000000000000000003e300000000000000000000000000000000ca5f0000b57700000000000000000000000000000000000000003980b47f0000000030abf3130000342e0000000000000000000000000000000000003c8d00004b90000000000000000062d6ab770000000025b600000000000000000000000000000000da54c15b00000000000000000000000000000000c3690000b0ba6c690000000000000000000000001178943300000000000030140000000000000000000000000000c5900000000000000000713b000000000000000000000000000072d30000000000000000000000000000000084f01496000000000000000000000000000000000000000091f7c2d20000b4840000c20b000095a1f1930000c15300000000655500000000000021b282c7a3540000000000000000e245a2e3000000000228000000000000000000000000000000000000000000009aa50000000092a3000000000000212304aa9a97000000000000c084000000000000000000000000902de42f00000000000043be000000000000000000000000000000000000000092670000857b000000000000000070f10000000000000) else (if j<10 then 0x44a00000000000000000000000073a90000d42b000000000000d1d3a48d000083e90000000000000000a42000000000000000000000000000000000000095700000ac171b4900000000000000000000c52c0000000084f195adb096000000000000000000000000000000000000948a11577c9d000000000000000000000000d995000000005024c97a0000000010af00006102553900000000000073fb0000457a00009b4c50d500000000453e000000000000000000000000b5cf84e964d3000000000000000000000000e5400000000000000000000000000000000000006c0e000000000000ab03000000000000a21100000000000000000000b3350000000000000000000000000000613c00003137e3ee0000000000000000b439211521190000000000000000000000000000000000000000000000000000100400000000309791a00000824d0000000000000000836500000000334b000000000000000000000000000093db93a311390000baff0000000000000000d0e60000509e000000000000558000000000c288c3d900000000000041ed40dd00e80000828a0000000000000000150d00000000c221e16c0000220a00004b4200000000b527000059f200000000c1730000055d0000d0fa0000000000000000000000000000000000000000000050ff0000000000000000000015a2000065090000000000004a6300000000000000000000fd0d399000000000c18900000000000000000000845500005c18705100000000000000000000000000000000000000000000e5ac3426000000000000000000000000000000000000000000000000000000000000000000000000c20e34fa000000000000000000008bc70000000000000000000000005035000000000000000083750d8d00000000000000009d0c0000000000000000ed550000e00000000000458a00000000245400000000608db4ff0000000000000000c12513fa9575430b000000000000000000000000000000000000000000000000000082b3a92300000000282a000000000000000000000000000000000000000000000000035f000000000000000000000000000000000000000000000000000000000000f37200000000000000000000000062ff0000000000000000f0ec00000000000000000000000000000000000024e4000000000000000000000000000061889b47000000005229b4be000000000000000000008934000000000000000000000000000000000000000000000000000072960000000000000000827600000000629800000000000000000000e5b80000017600007bce000074a3000000000000000083ae000071b0000000000000e08f00000000000041420000554c0000000000000000000000000000000000000000000000009442000000000 else 0x41fc00000000758d000062cf000000008d12000000000000e39b0000000000000b94000000000000754600000000000000000000000084db000000009b06000000000000000000000000a1920000000000000000c98fc012000000000000853a000000000000000021830000000000000000a3d64a6a000000001ce20000346a0000000071b10000000000000000000048b30bfc340ef10e322d0000fc1500000b6e000000000000000000000000a4cf0000000000000000000000000000000000000000000000000000000094fc30b7000000000000000053c600000000000000002172a55f0000998d00000000c3ea00000000000000000000f06e00000000e3a5c121000000000000000000000000883200000000000000007a550000000000000000122570a900000000000000000000f05a00000000000000000000000071800000000000000000c413000000000000000030b0000000000000b13ad0bd000000000000000000003073536be1cc2b80000000000000000000000000000000000000f20f0000000030d0000000000000000000000000b02900000000000000000000000000000000000052b6000000000000546c00000000d2080000123f000000000000000065a8e00e21d600004be200002418333100000000b25c000000000000000000000000000000000000000000000000831100000000000049250000000050800201b304000071ff000012e10000e0a3844900005a73000000000000000000000000e50e00000000cb501bcb00000000000000000000944ec3ab3291cba9000000000000000000000000c4dd000000000000000000007c0b0000000000000000000000000000b2ab000000000000000000001bf400000000000002ce000000000000d10400006058422b000000000000000000002bf8f26900000000e4401979551b0000000031290000a86a000000000000000000000000000075c5000000000000045b00000000000021990000000000000000d1f059f4000070282ae0000000000000000000000000084f00000000000000000000000000000000e506214d7987000000000000000063c400000000000000000000589e0000000000000000000000000000000000000a6800000000000000000000d974000000007ab03373557ffb53000005ba510d00000000803200000000000000000000000000000000dc2c00000000cabe00000000e31b63dc0000000000000000a351000084ab000000000000e9e900000000000000000000d348000000000000000000000000000000000000000030910000000045660000201e10f679f70000000000000000e1f10000000000000000000000004093dbf90000000092ec000000009015000000000000ba570000352500000000bc1d00007971000000000000a)) else (if j<13 then (if j<12 then 0x107000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000c9f10000786e0000492100000000000000005a010000000041c9000000000000c415000000000000c4f700000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000cb8200000000000000007b380000000080e90000000000000000000000000000000011e3000000000000000000000000000000000000d19125c284a0000000000000000000000000000000000000000000000000e4ed442c00004c72c1d813b232ad000000004564721d0000000000000000000000000000000000000000000000000000000000000000000064600000000000000000000000000000f5830000115800001bdf000000000000000000000000000000000000000065160000000000001c67f22cc2f600000000000000000000c98500000000aae2a4da0000000000000000f27b0000000000009250427500000000000000000000b3f100000000000000006da60000e05c00000000000000000000b470448c0000000000000000000000000000000000000000e19e00000000000033b184a20000000000000000000000000000000000000000000000000000949a000000000000000000000000c9670000000000000000000000000000000000001af20000000000000000d4cc000000000000000000000000000000000000a11e000020cb0000928f00000000000030c70000000000000000e42500000000643d0000000000000000000000000901000000000000f1b90000354e0000f2b150edd00c033b12d400000000000021c3e00ad405000000000000887800000000f863000051e60000000000000000000000000000e2c800000000000000000000000000000000000000000000000000000000aaa90000a371936700000000823d0000220000000000000000000000000000000000000000000000000000006ae500000000d9e6000000000000000000000000000000000000ba6f000000006b7500000000694c99430000c37b000025190000000023d5000000000000000000000000000075b73d110000e196207a637000000000757392ed0000000014ae0000000000000000f5be000000000000000000000000000061a70000000042d70000000042dc000000000000000000000000dbe800000000000000000000000000000000da0800000000000000005a79622700009461000000000000db7200000000f1310000000000000000000000000000841d0000119f00000000000000000000556a00000000845d0000000000000000000000000000843f70ce0000000000001306000000000000000000000000000081d10000000072930000741700000000000000000 else 0x4bf0000112d0000000000000000000000000000a39d00003505000000000000c46e00000000cd64000043cd0000e04100000000000000000000000000000000a550839682140000000035150000c43a00000000000043baa2fe0000000000000000000014f800000000949ec34500000000d4d28488b3d8aaa3d09a82a273f0000000000000abfd0000f330c4e824b900000000d53200000000000000000000000069e7000024020000a530000000000000000000000000000000000000000000006d9a71c10000685c000052340000000000000bef00000000000000000000000000000000b889000013d70000ea520000ea6df36ff9dac13ec1af7a0000000000000000000000000000000000000000000000000000000000baf40000000000000000000000000000000000000000000000007c0400000000daaf00000000556eb2b50000000000000000000000000000291e0000096f2456000081160000d3b3000000000000d4ef51790000424a0000000000000000000000000000000000000000000091f4708500004520bd4ef34654e3688a3052237dd300f56b00000000000000002bece86cb3f50000000060d300000000098e000000000000ba7ae5a420600000000000000000412c000000002071732c00003b6bcb4142a872aa353f73f678180000c4350000100f0000000000000000000000000000000084c3f5930000000098291174000060830000521ea05000000000000000000000000000000000000000000000c59f00000000000032b4634000002086000049fd0000000000000000000000000986c45961ae00003b9bbadd0000eadf000074cd92ca0000726e000000000000ada90000000000000000000013029b3e00000000c082c274547600000000000000000000758e000000000000000000000000e40a00000000000000000000000000000000000003e004ad000000000000a4344adbb17100000000219400000000000000000000c5ce0000000000000000d0b2000062c472f8a22a6070000000000000000093809160d253000000000000000000000000000011aa4090f04c00000000000000000000000000000000e0e5207700000000a55bec8f00000000000000000000000041a6e0ac000000000000000022790000000000000000000000000000017a000000000000000000000000838b000000000000000004470000000000000113000000000000000000000000000000000000b0190000000000000000000000000000000000000000000000000000000025cb000000000000e83000000000000000000000d2311b7300000000000071cb00000000000090fc00000000000000000000000000000000000000009359000000000000b34f000000000000000094c7a54b000000000000000000000000000041271) else (if j<14 then 0x140c8bfb700700000000000000000000000000009a9b0000a0270000000000000000735d000000000000000000000000c4a100000000000083600000a574000000000000f49100000000000000000000d26000000000000000000000000000000000624b0000000000008a960000826543bd000000000000000000000000000000000000000000000000000000000000000000000000000080890000000000007c0f000000002069000000000000016700000000000055c370e395340000000000004894d27e000040570000000000008567f50f00000000a0c600000000cdb200000000a068000000002316f4370000c376b13d000000000000894750e000000000000000000000000000000000236253050000043bb25eb1ca0000000000004462a2b700000000f5b400000000a33c00000000e5420000b5bb000013b7609f0000308a33f7827020250000000000000000000000000000000000000000000000000000bbc8000000000000827a0000db0505373219000000000000000000000000e97e0000000000000000000000000000904e205335ae00000000615600000000531200000000f29f00000000000063d1b1c2797b000000000000396500000000a14c00000000854300000000000000000000000000000000d5bd0000000000003a8000000000d374000000000000251700000000000000005bded0386106827f3382000000000000000000000000f9faa44b0000829e0000000000006ab20000f22f00000000000012ef000000002bfa40f09b282a5880e20000000000000000000003e60000b43c00006390a34300000000000000000000105fe429297c6aa174d50000000000007db5514800000000000000000000000064d6000000008206e38e431e521700001c3a0000d3e1000000000000321272ae00004061a54a0000000000000000a4c200000000755600000000f09b000000002325000000000000445e901dc33361e00000000000000000533a000000000000000000000000000053980000000000000000d12e0000000001550000000000000000098c0000000000000000000000000000000000000000eae38b7100000000000000007c1fc1d4d0ae0000f31f000065510000e9e00000000000000000000000000000000000000000d3b0000000000c1a000000000000000082560000ca77000000000000000000000000000000004368505ed5232401e19c000000000000000082f2000000000000000000000000000000000000000000004b700000c98200000000000032c9b151000024ca00000000000053bf000000000000d0fb00000000000000000000b1eab1110000000000000000000000000000000000000000000000000000000000000000000072fc0000000000000000a9f300000000bc1b000000005 else 0xb28b00000000000071be202e0000000000009552d41ae96d000000009277c5c00000000063b50000000000000000000000000000000000000000eb7f3b93ca76b9690000d52fa1b882e400000000000000000000000000000000752a00000000baf021a90000d2e7598aac570000000000000000000000000000000000000000786b0000000000000000a4fee299000080d7150a0000000000000000000000000000000000000000000000000000e0c20000520cf33600000000b4685d5d00000000841b00000000231de00600000000301100000000000000000000000000009c100000000062d154ee000099f500000000000000001239000000004ad68b4d0000996800000000000000000000859d0))))
def mo255D11 (j : Nat) : Nat := (if j<2 then (if j<1 then 0x7ff55161ffd73587ff50d61ffd72587ff5d951ffd75547ff59551ffd64547ff55151ffc83547ff5cd51ffd63547ff54d51ffd43547ff5c951ffd62547ff54951ffd65507ff58d41ffd53507ff14d41ffd62507ff54941ffd764c7ff21531ffd754c7ff59531ffd644c7ff55131ffd734c7ff58d31ffd534c7ff50d31ffd724c7ff58931ffd524c7ff50931ffd324c7ff5d921ffd75487ff59521ffd64487ff55121ffd73487ff58d21ffd53487ff14d21ffd43487ff59570ffc835c3ff58d70ffd535c3ff58570ffd515c3ff4c570ffd215c3ff5d560ffd54583ff5cd60ffd43583ff5c560ffd51583ff50560ffd31583ff48560ffd70583ff61d50ffd86543ff5d950ffd75543ff59550ffd84543ff59150ffd54543ff60d50ffc83543ff5cd50ffd63543ff54d50ffd43543ff60550ffd71543ff58550ffd51543ff50550ffd31543ff48550ffd70543ff58150ffd43143ff61940ffd85503ff21540ffd65503ff60d40ffc83503ff58d40ffd53503ff14d40ffd81503ff58540ffd51503ff4c540ffd21503ff58140ffd50503ff14140ffd874c3ff61930ffd764c3ff61530ffc854c3ff5d530ffd654c3ff61130ffd644c3ff55130ffd734c3ff58d30ffd534c3ff50d30ffd814c3ff5c530ffd614c3ff54530ffd414c3ff4c530ffd214c3ff5c130ffd604c3ff54130ffc504c3ff50130ffd750c3ff55030ffd700c3ff54030ffd400c3ff5d910ffd75443ff59510ffd64443ff55110ffd73443ff58d10ffd53443ff14d10ffd43443ff5c110ffd60443ff54110ffd40443ff4c110bfc805db7f5d975bfc805d6ff61d65efd76596ff20165bfc80592ff61954fbd64552ff20154dfd765cf7f5d573bfc805ceff61d63efd6558eff20163bfd8754eff61953efc8654fdf59553fdd7354ff758d53bfc8054eff61c53bfd8614eff61053bfd8114eff60053bfd8650eff61543fbd6450fef55143bfc8050f7f5c971bfc805c6ff61d61efd62586ff20161bfd87546ff61951f7d52547fd5c551ff561546ff20151bfd86506ff61541fbd54507ef50941bfc80506ff61d31bfd864c6ff61531bfd844c7f74c931ff5614c7fd54531bfc804c6ff61d21bfd86486ff61521bfd84486ff60d21dfd765c37f5cd70dfd715c2ff61d60efd76583bf59160efd63583bf58560bfd87542ff61950f7d54543df54d50f7d51543fe5c150ff960542ff61c50bfd86142ff61050bfd83142ff60450bfd86502ff61540fbd43503ef50540bfd874c2ff61930bfd854c2ff61130fdd434c3f74c530ff9604c3fe54130bfd870c2ff61830bfd850c2ff61030bfd810c2ff61d10bfd86442ff61510bfd84442ff60d10bfd82443fb20910ff541443fd4c510ff521443fe481109fd8714ebf61853bbd8414efd60453bf98014e7f61c30afd860c2df61430bbd840c2fd60430 else 0x5b0c3f070038182d1ca1701c00f0ec70612200b07003c903894705c0170fc70e241c5c170c5b043c1b1c389c1c016871214282420151b0f07021c9120f0e0545c3c1c00725030c87041c38685c3c1c047171b07004b1c5850b090803c3c1c0c724242824201a170f07011c90f0ec3c1c0471b0d0304871c386c143c0c724145c18170f07031c90812030fc1c00e05471727043f0038171c5870b06c00fc70e241c170f07003c38911c8064012c30fc105c70e2414070c385d1c447010e16c71211191814070c3b1c447060501c30e47111c1914070c3b1c4470605c341c70e1b0c231c84481c30e4711151416070f1c38447c3c7410e10030f1c444051fc3c212c10bc00605246b045f002b1c18148c4c306c1c0120525230c5c4b1c1814887c3c117c012c70605230f044b003c3814948c1c00f160ec7051f0f0700483c3b1c148c4c305c1c00f0e24230f04204b1c14847999532726334c2897c52e925b74b2895d52ab253b4a40940527724d349709285245247748b89115215240f47f08f551db238b46c88ce518922ef45a08ab5147226f44a088c510921f743b087050d1218b42d08515091210b41c082d5045206340788064ffb1fd73f887e54fbb1f5b3e607c14f751ec73d4879f4f311e473c4077d4ee71da33af87564e991d0b39d07314e4d1c7338907084df71bc337306dd4da71b2b36006b64d5b1a9b34e86964d191a1b33f06734cd9199b32f06564c9d191331f06354c57188b30d86154c1918132fe05f24bd717872ec05d14b9316ff2dc05b14b4f167b2cb058a4b0315e32b685634ab315432a3853d4a6714af29105174a21141728084f849df139b26d84d44995130f25d04af4951127f24b848e490911f723b046c48c7116f2288449487d10e32170425483b104f207040747f50faf1ef83d3478b0ee31d683a047270e171be837446d90d931ae835746a10d271a1833c466d0cc71958324463b0c5b187830745fd0bdf17882e845c30b7316b82d045950b0f15d02b0454f0a7f14a828e450909fb13b826f44d3098b12e825744a3092b122823f447308cf1160226443f085b108820b440b07ff0fd01f343db079f0f101d943a507330e301bf437106c70d501a24339065b0c8818a430705f30bb016e42cb057b0ac8153429104ff09c0130424d048308b810d420d03ff07d00f041cd037f06c80d34195030305c80b14151027b04b80904111020303c807240db019f030005b40ab012f021803a406500a701080194021001f0000ffd75597ff61954ffd65553ff60d54ffd81553ff60154ffd655cfff20173ffd7558fff55163ffd7358fff61d53ffd7554fff61153ffd5454fff5cd53ffd8154fff60153ffd8650fff61543ffc8550fff59543ffd6350fff54d43ffd8150fff60143ffc8050fff59571ffd635c7ff54d71ffd7558) else (if j<3 then 0xe206119150f0485921c38916854546c3c121870e244a1919170c87061c389868540c30e874d1d19150f07003c39921c916854546c3c1c00f0e87291b0c3d921c386120f0e4685c3c1c057472b07031c904200c0b43c1c04724203c390f0f07031c9080f0e05c1c057c724207c3c2c397f0d2f0700911cb1727c1c0c72418483c391a170f07011c91b0cc1c0472418943c39970f0700911c90f460e05c3c1c057124728310f07031c906170f0e43c1c0c724203c38170f0700911c8468541c3c121c70e207518155f0f04851c38918c121c70e24185f0f04871c9038714864685c321c1470e2500170f04871c90388868540c3c70e4d1c491a170f07015c3c391ca43c1c00f0ec7241c5c18170f07003c3b1c90a57c70f0e24144a191a170f07003c391ca4bc18f0bc08e4724209707023e391c9070b4657c392850f470e245f1c3c38905c3850fa4470e182119150e060083062285911cc1f160885458180c34bc15f88a147385c21150e06007306231d9284c08464581801bc188a164472c845822151606030f059622851cd210846818012c3c18857a1473021190e06006b06231d9284b21170883818043c1c78864a13086015c230e054a231d1a8514c2112864681800845c3c188a147351916070c395d1c848464543810ec76421211916070c3b1c847464581c30e47211d1916070c3b1c847030f24870e140f07002c1c9060ac30f870e1f18330700591c48606c1c0471712182f1c3c389c50f24870e103307005a1c48603c1c0250724182b0c083c3894603c1c007121718170f0700901c5c70a8505c30f870e1c302c1b0700491c58805c1c0c71612182c171c3c389c60cc303c1c0244717203307005b1c486c1c0c724100f07031c905c3c1c0244717180f07031c9050b05c70f0e2418330c4b070018142d1c90c4317c1c00605c70a2424230f0700481494812c3110605c70e1c24230f045f004b1c1814a0cc1c0128716183024200f0f0700921c943c1c0072414170f07001c909470a8505c30f870e1f0c001c5c845170ac380870f181844491c38500c7161221142f1e00903c505c31711470e1858471c48385c300c71121170c5c451c38503c7110e24142c2a1b0f1e003c705110e87161518170c461c386161410c3800725a2230e001c448450ac380870f170c5c451c3851211c7160e140c471c903850685c311470e1b0e031c4484503c70e112414171c38904450b0a8505c3c7800f20170e045d1c3868116c7120e1518170e071c3860605c381470e1819170f1e0438652c1c04307171914170f07001c5c7c30021c1070e171f0700591c485c1c0164712170700491c585c105c0c712161800871c483858605c3c1c04717181707005b1c4860f0e25c3c1c0471c3c38170f07031c908c340c121c70e1b0f07011c5c5c1c043c7241414 else (if j<4 then 0x4724190f07011c5c9061f83c1c04717241f07011c9c483c147c025241a0f07005d1c9061741c76227145f07031c9c5c1c08724110f0f0700921c605c1c0872414149f07021c9061a43c1c08724190f07021c9051246854140c3628720491a170f07021c712468505c3c14fc04e872841160472014a1e885c910084643811d5a64a28728750e04430d921e885c910811f4b80a247242042049602891c9071810814b80a247242060420602891c90786851811a447211c805e0402891c9078100c32447a2171e04005d0f1e889071b8100a247241842051f0c928894717c7110e241604030c911e885c78127c7a22414410e06005f1e8890810088180c324a247207a15170c5c451c8481911c72421145e1514005b0c18471c84a10084543c11c9464a287284021190f046a51928a1ca100843c114c364a287244023054b0d168a1d1894645031411648721221514511b0c461c84820814380a247241f1c38449045f1008811f804bc324a2472c5c17049f1e889071b8180a24724199440220496030c92891ca1046810580c35712a2472a06010f1e889061710438180c7a22420420416030e88911c81e86460085c3114721246400471c9084600c3c71124211a19185616030c451c84986460112c3800511c721282119150e0239911e349168e45800ec34b5f478d285c21150e023b1d92349084645808e64478d205a3916003b0d951e349120846808ec357478d2421190e023b1d9234817c3800e43c7648d20270e015c214b1d191634a12084645808ec3478d24703d143b0701714a1c5ca0f0ec352c1c087451724683d190c382f062f0169921cc240f430ec3c1c0648717286119162d0f0485921c38a854521c3c1870e17204a19170c87065e1c389868540c3970e874d207c3c0c397d2f07011c90a250f030e65c1c04724243c14392f07011c9080f0ec1c0472418761a160f0486911c38903c121c70e2418521a160c8706911c38921c1c70e24161a160d031c3a9134886854b83c1c00f0ea44729170f07011c5c643c1c0c724148030185f07011c9080cc3c1c02447171c310f07005f1c907160f0e4586c3c1c047246c3307011c9060f0ec347c1c02425205c3c390f0f07031c909170f0e06c1c0c72420330f0700911c5c727c1c0c724143c390f07005f1c9080f0ec3c1c024471e1915070f04871c3881d8545c321c117470e246304871c389060640c317c121c7240e245215161b0c87051c389c3c121c7240e1a1a15030f1c393478545c30fc1c00e4717250f07003c3b1c907c18fc08e4724183c3919150f0701921c90f0e4546c3c1c087203c3b0f070119921c81c0f0a45430ec1c05c64872c3c3919170f07021c80f0ec3c1c064458720683c29190c3b070169921cb240f430ec3c1c06487243c3b0f054b011a1d149464541c321c1870 else 0x1cc117c0471f241e1f0700909451c84c1c02425190e1f0f0700909471645414087c362252059161f0f0700947c112c0871727184b0d3f07013a1c5c85f274bc1c047241c9d949707011c9071a4bc1c)))
def mo255H11 (j : Nat) : Nat := (if j<2 then (if j<1 then 0x458191407b735fb18a0000c9ced017b1aaa40a0000545ac16580a6e3be3238dd118543d1f34b1bc3a12b99c4c6e18990aa2107e49d334a190084fea8cbd9dd74360baf90103083b0d86b979890431c14b94122b15744ad28b6a0c4e09bdafce91849d111efda54a35023b3950d1b7f30d3a8bc752c000092cc905d3b5561cfcc4a324869152546e24313cc8282b511e4151327b536c4dd61c1c085c484b192f03d0000a4ee1adbf0b000000000d0290837f05733d40000cb8600000000414882ce03ca00002c59000071c230ec94e370b540ba54a45a28b026ec553b472431c27b334db3f90000dc4dd494334b044494ff0000e1a79249613c000085061cfd423200009337000000006176b9738447e26d41dccca4a29a72f31348f9023c5ca394a0520a0732f872d51328f11d12c0e4c1000000e24a37a45d41c012463413753b2141125033f131a67155d4f6f30db08b12ab94e40117922b806ee5240323b3baba29d0c81cf7fcd8d43ca01cb30bd3eb41882460912d915964d9aa33b8c3843b52c7d38e7906037e70972c4f5082c52063f8736de2bc99d9940c2a1b24b8c41ac0d953c75afe62bbac906c5319877917fd0f4540d3e211808148432d8200306f0083209c0900417170050d8a7005bc00007028be0459c1422d0b8220040d2ac180cc0908c88004b00ec14114003a4b1000052403363c6707cc70711d33885000183641800c55070000bc5608c1e0500000c420012c0044a0743502066454061b8e10144708c0f5f4b2040000c0ad164198a891508040740d0006e15801264510c8a802c000304000426090a13c41b0007f0a0100017500c940248f0106b00805008530004c004461602e04e5400cdc0644508c041444601c210002f06001004a10a42b13446004190100002025028130044701004084060600100404014010440c0940a00c0901028058000c8000d0000080c000050c01507c340a94904c0203c00000870fcad000041a43600800010330340a0246e0140100c0b2441c0242d0c8cc3d8770580023c0e02ced070083606505c090243b0000203004000190001000401140450005601c1a040001409303c1204c0114c080204500c38004060100b1580a034000a82e03802024010d40009197004100ec01054170300100410074120000d0000a02c0311c4100002024190b00410c58014491840c008300000b0280101c1c02c080040200806020040847406408014031dc0a0140c00001090011e82205c02050340540b00802040330445300428004060700501c002580b0000207406094000044e0003c00c2700800018090340002001020130000500854014090681c1140003c0000c040082b0180902007004062c81e0ec0d094050740300c7202409020250180000401000360000100803004010542000405000120681c else 0x8ce46aaa74615843d8c2a84225410f2a38fbb9fd0a0000813b2336341b9230822cf1806518232a80fba538bb902d0771a24501d4c87958bc9749cfc206c3fa325351ece9dc024a607ab03100005269e4269879e0a300000000836e8d0d3125224ebd019bf70000415c21f491d84c5d00008291cc600545e039420a1b93440ee2f4396ac172a0be00001d03412959d093d710e022ddb3582a2a701200007442f1e11182e8b7a15f7b7d634e23190000b41d10fec38b790b903a92ed82459c9e197091f1a0c72011b3d583b79446117debfb150ce32dc37ae462c91421e4a39833c32d122339985222c6c2f9e354b04f00003a323b2a73ac04bba3700000fa45145bf2bf0000a0c10000e38f38b9b4a26c0bd345d91b32cf31c7d13a98c0119afb2da1b08b31f09d590ea42f015dc08e6392aae2936000008affa231953d928cca444138307300adb517e10e849e2ca293f3d90564870352352d8d131418b37cc14f5152752892fba240d007617ca315cbb45244ccd973adfb9a33e8eb4d43d0a15144252c06db5053ef81e9b8c439de0bf208ffb1366d21e39e130a62986251eb8c7202345f6186b38879913d08e29531f7ec51c3bf6047226a0000514aa2eed8ef00006513c2b90c730062502d42d8824cf16c6d2c40e5f09945096019b2fd0000a2191406410cc4f054017c010a1943e09a77000033ff5b57ec937405a9d2416b84456a3f1d3b252a74cf8277d2860000990f00002b4af1bbb00f2371dcfe94f72279a105d39903c90000d8fb553f747cf275c100bad4688d4a2f133bb3af603510d5db021397d257d22742a62965935e1283d0b695160000245e91188c052b4b45077a1abcad51e2c37f0b1650bcbd20c1b6b1ae523fe448dc9b841ce2e20b48e1ff934214b1d423f8bee2acb31211afb210abfde8c8452e9bf162a22303a134a0c92a3adad5e11a8051627338f662ca517a738610db0b8b5a4370e903df997ef027740800000000d28e726edbb72154e01343c20000521afc54022045411531fb98821c5c56c40d20cf000090042c0ff07e0317591a8461cbacf2c1a435a1c914203af20000351df8c179cb3b8fb2f173d14886d16aa102e04a40df4217ed36a264ed16809edcda51b7535d21e60000717ebb924112a1c3424fc486741994ebd022a18c0000ed2f58adc46970acb5033b5fcbee60018cdd33320132d2ece5239c92f2d424bea329a4f80178f1404322720e000051939021cbad32e0605962aaf3fb225263deecffa2da00006d00c3fe6d065130e1f9c078d5333b9e51eb0c9d131fbbf9a2967cd1b4410b88b170806900001207c271c3660a1110282c508c630000a3f2f4dbd384cadfb46ea3b51216a1e07a2df1ba792be485550859dbb81983d99a7ec30f9a82814b902a6177942c0000000072b5d1e73c074064939de0) else (if j<3 then 0x7bf0f508afa2b3315623c1380db3a0bc240000401bd077d912d2b40000c3d65374000072a1fba882c9644ed1268324e16232e1d43a0000bbfa8a3030c61404447d013ec15e74c20000498ab4e994e1609ae1df628d014244d2e0606afbb8f325372ba588c5221fe4c4a10d54829b9ce4370333c4efb0d182142ad23c0a62763470ab3f8095d31800007b87904bc353e90904fcd2853041347742720000b476fc912b6104cd7109b183625cdb49000098f1208a3369f36f0000b1fddc5faba410e6312fc1150c8c3499538dd25623088af1f07c131de093d9c8d48f92f001ade16ea17fe0a425190124325520303496997543e5b8f45cb2d22e112b10d6a235f266f297d005b3edc9740000000014f95969ab81e0dcb29ea4227b9f44e203250000521d522603dd118e5cd49a31f330000000003c0cc1681061e51bd1d580f800009143419ea196000010a800380000302ce3ec943f31e59878f14daa25d978597c439b4ba7295900007391c4dfa2fa0000cb95e04e91da7bab49d7f1f0b21840ca5c0262d782adf91c0464305bc97f70f0f23be824cc5e78c2d9888947c429a198a377742b84656281a02f6014c0066af9a4d44402bba62c61817b41be11470d15336440fd608f13859379b4ca8187fd0ce5290310c0fa205cd160c1cab03c13c824f4f3c441b5c10a6361d12c895763d2bb597034b8c751f84421820392c2e9e15270811c297201d490761a3ba3b9f5150ba0a3c6d19cc0f6222212d13976143d52f58290b5446390397721d7db71727f81a594bf7cfcc5277044807d64883175e4bc828f40e8ecc4dc13f4d6b03e351a2d2d6247f1fe2bff340970d474d5e81a5ca85b2ed33440559535524df90d3375e113d50eac14c393e4a84439c53a99c791a303562412225a53f4dcbd73e4e3d3118df02b6caeda47b2997146335790b7b300237de526c4cef51243cf949140ee210b287310de2368448b09d67498a259e19933db432e13110000935aab8deadd03f6b33ff4ba3bf8407200001321e2396452d46dac94408d20870049000009110000c0a04af3820f3c11c1d30000497aaad8642df4aee0b9e4dc504c0af8c16dd1cd714ca43340c0a4958cf971c8c98551a480cd052bf06303c51234bbef333a70c502088331254214defc5af359a96b427c2351c907fb17cc20e349047311e39ca6f2e7e1a9c1b8c9838b6839cc02a5d0ab51499b9b24a6596c73b4cb91d26f700da39a32f7f1694200d26343c0143ea4bdbbfea4ac6174e1d6620164b20000c2bdc8f0000084d73288938c337229011cacd301fb77040040082c008179e2a7e13fd4cb3265f03253070000219decdbb1010000312e98fd531b6b85eb7902b15b60b8c9000040ea18fa63cb7a2b3d2e0000000000001980e4f5719022cb000063f5d34fe410948129827417e3fca4 else (if j<4 then 0x6cf05638cc545651677c100000722d920484b4d343abb60000f26b2af5a489000022fe00000493009f484430ef34c723780000dbf6f521c1d2c2dec05af25d1ad9fca3000012fc30026d47835c900910ae0000fc49449078b4100e34ead28b73aac0b184a399cad344c2685c2e1bbb741e185572d390c3f438225e0000d15bb341a091a3b8f1ed4908a48d0000000012c5226781c5000000000000910391197c9520bf0171b4800161238200004237845ca01f00008b0022e5000094d8a068305e2d324079f9664c9848f2d28a00002d30a8fec0ed2020f53c92ea211439dad0f2aa66e0a7fca09457d2059a35dc0ea9cdd2e4db6b20539b83a5057920a8f90c8ee21eb2cd42efe829a1dbccaa89043396e4435cf6c40b2450bba914c90000d0fc1314c4f1522121f67b8058bb68f7e3a221dd93b2e416606f91cb2bb0a09688b311e8f346e4a0952590e3938a250478165945242e0000000032e6f2ebdd02d440a3a313e10af7b478b434e12848c6091ef376f9d40000f83830bdb8b202b7547bbbbc000082be797b4c4b4d40c4e5531e2ae1ab01e0802302533cf30454aa90b842bac389609cc07051b2d0e780d200002ca57459cc4ec44fa29c8432a23324d0f0541428d47ea184694211ea000023624145f30c41c4e2243bf5dada74ed9bb1e4f2a03ff818c02423cdc91652f27a8064b7b4a5ca2e0000a06a0000bc57b0afa1970000c1bde365616f43ea0403349a51bce31aa0ddd90c0000c4673c58600aa3a8050f000011f50000b0e1d2a9e1ce387a7b786215badc1b2b00000000818100002c99528011bf00007453d1500000b25868aebb3012a360f3baf4d3a582878278cbaa18b1496e439c120ba53972949144f45561d1d229437390501c035c523c8fba262387fbb80000023c0c08e1d9e0039407e430032bf4e7c2e81458e90359a8446878bf9919000040f17b8244fb58ca3139944984e053a43ca1b015e0a9a32fca7563e6529f7367f08cda39221120cc2968d33522d9012a0000e0eb825f0000329211ac1a13000043e3000060f441a0dd046c9fdd0e00007228a094a2135164187b840f0a3440255ad75381d2b852f68b96239ff0662a3c61abb4a92306e46c28fc6a4124a1908984f372d03d352ca73ba2c01aebb2634c54b00000e340019462af4d14325b22e36bf3c293eb8ab9d3fb2cd46b430ef241816300a2f3a7549f94c3fba335300123018f739561b1a89323abf24b8afd501eb33888bdf284c098c547553e1067f4749166900cf36ac13720c2a23600900000b35b2ca9e2095c0de8b8b1271b89bc5b183cbcfbeb7263a6e32cd9210000406bf2dcd081d1f292b072c41d090000b4a7a48e64e8a50bf3dce44b2c04236b6121747a750272a0c81f41ee7989c06d0000a27d3532dbfcd106228914b6b23d5472147f296d43 else 0xe1a814fa30e40000dad3314ea3ae02542828a21b1b84815ab065ebb5cc4c2492451f0133e45150482c9ae52f211b026053b60c8d6971f363402ed50aa0430000708651ccd1fa119fb262db9dd29b000000006223aad6f50040741817b967c2747bf00000e4b3f9b4c0a18a0b50ce00da227e20b40ba1d13d33ce226cd497d18b30751c9cb3f7422fc3bbe1c68a46000000000d05c4e6133dc96f74d1f3bd03208944f108c110ccab82610000b305c07fdc16f48a04146bb31522885000003a3ea2b200003347942753eed4c5b4ecd49b61117afa21b9046662a454ab83e9fb7303160000ea1281de0946700be03b0092546fba4238b0f49c8b1a71d042d62bf44242422ab46334af0c968cfac20d0000bc124383d212212050f9a3fdb8b588ba0000223a64da251c31047040d4d3a2db24b52aef63a9292c79139411c131744d4af02483238000bb10f7218512dfa1a1c1b480cbe01dd3b02cf830b3acafb4fdb0a5f45400361313c1fb2016eb942510b479342af05f0000391d223e4173b29da2ff0d3e7071c2ae0000b11ed4cc4c6a6943b088600060b2f9864a2463bc251e9a3613f00af6e0d7f04202c8fbba82e9e153904d90374424990a644c0a7dc11fb20c14c0b27a0000d19b0000544a00001b8e391f4b7ed2c3e534d51450ff3023000081fc2046c85ec87cc3da81b3e84880d0519592d2713528f843b1c3098355a018233ee3e77116cc094058d4751084fbae0033432672b6e06c0471441f53)))
def mo255D12 (j : Nat) : Nat := 0xc141c18081207202c3822e01f0e385070601c8e9070c160c0369038e161c1809438c182c38300b871c3038300d47483c3070604748343825e0128e18290182c3830038c5c305030cea20e4060a04047488870c14080871d10e182c186511071c30502021c7443801d0e38d1430587060170e3860a0e0c08e9070a1a1c1811c6865e0c02c3c7470c4860b0e0c00e3060b0e0c08e343830090f1d1c29018281010e0888e8499d52ce3e44582af79d3b77672c2565a944ba898f79c631e560940e316620c22800ffaedff5d7feb2ffd64ffaa9ff5cffeb1ffd53ff8a7ff50ffeb8ffd61ffaa3ff507fe98ffd21ffae1ff583fea87fc50ffa81ff4c3fe187fd10
def mo255H12 (j : Nat) : Nat := (if j<1 then 0x38b8000000000034707c0c000000000022d6e4400000000000000c3c80aa00000002060000000000051818920002477000000000000003198ad1000000000000002498000000280088c80007bf80000000000000000000000007840000e8000000000000000309c1a4c00034978350000000145c00000000000000000000000000038e0000000043f0000b0a641a00000000002c1ec92749bac38000a360000000000044600006108000539d0ca136d31f7055ebf0000c190000000c11c000c45400000031280002c050002c260001cbd00000000003ad300000003384000f2c00000000000000000000022f60002425537000000000000003214b17d49a40464d29230000000000000000450000000bbb5a4a00000000002cbef9f0000e3d400041cc0000000000000000001f000000014e20000000384c0009888000000248904bc000244e6c059e9a4359770f0fbba02d10f187a000000000000000001453c258000000000000000000000000000000044b8000f220d0b000000000000000003c3bf870410000130a50e80005059ca500000000000000000000000000000000000000000000000000001d0000028d00003cff00000000001d110000000000082890cc00000000000000000000000000024509bf000000000000000000000000000006850000000000100d0002f0100038b90000885000000000000000000000404c0007274000000000000000000000000a31ac8bb464000000000051280000003c5e0000cd12b6a04f0000000000361221bd312526000000000000000000a4040000000000000000044124d78aec0000003ad23155863000000000000e80000000000000012b805800000000433c6970e4c010000000000000060af72b00000000000697a3580680003c400000000000140b00000000000000712c0000000000000000000000000000000f2c80ce2193867032c0360184000e1880000000000000149e0003adbb0d0a7f00010750000c4193d8c7fc3bc000ea18000000000000000000003d2d2158000f2198a800012f700012bd4bffc0ae07f4b600034230000000000308fd8460ad000380c000000000000000000000000143df2f00000000000242340700000007be8000000000004a400000000000002476000000000000000000000000000000024d40000000000000034186dc3bb1d24000105ba0e2a4558b400098999100002efba1680000002cdd0000000000000000700000000420a1d00000001ebec4ac00040c70b30c2c2820001d1ebc4c000a3644c2743c000000048200000000003a060000000b25f4cce91889f5139696b4168f8f46f8ab001010001130131311430005204120320023a42020528012060001120008300812390023030107e30000503211000824200212 else 0x92280000003cba00000000a040000000000a4580004bc448100032514252507000000000002f90000000000000000000000000000e3eb914000000022b00000298000000285900009220000000000000013548da2c4442e62348c08254000b1b000000020370000000a326280c9e400000000000002480d1e60bbc48f02a0000000110c00000000000000a7800000000000000000000031e0000621fc5200038c70000000b3a4000000142c3af30eb000000000003040000000000000000000000000000cc3000000004fb5c5c000c15c000000000000000002150000f312cfd2bd0000000283f0000000000000000000000000000000000042840000000000000310900000000000000000000074680003bcc4de000012c000000043df0320003c2f0000000000000000000000001cc30002903b2400004854000000004c60480000002ca7000000000000000003824f0382ad000146e83b4000123a06d72890460000000405000000030b7bbc80000000000e43aa83501beaa0003b08b20c00000000000000000c38c00000000000000000000000031720ea5a4800000000000000000e2fe27da82c000000365491f4000000381d0003f0600000002334c1b0003c71000000000000000000000000000000000000000aef00028a4b3b86d4349c85d00000000000000000000000000000000000d2c4000809ea7e00034a053c4000134c0000002c7e000000000000001c404f900002fd7c16eabb4840000000000000000000000000000000000000041a800000000001a500000000000900e4c8c2d08fe00000000000b0f0000000a399650000000000000005024000000312000030930000000000000041ac0000003b02f9ec000730400000036f5000007b5110c1700000000000000b395f1400000000001c490003c72c120000742943e60c000000000000000000c37c000d086ef0eab044d00024c5a40952a18de8650000000000040f33d20af4a5400083b0000000000000000000000d1d00000000000000e26651c0000c040000ce4000000072a4000a28c0000000000e43500243cc0000000000000000000000000003491000070d0000000000391f20220cf00000009c240005a12d1200010220001884592c000000000000000000001051)
def mo255D13 (j : Nat) : Nat := 0x30401c4ff
def mo255H13 (j : Nat) : Nat := 0x294000000000000000000000000000000000000000000000000000000000000e90000000000000000000000000000ea00000000000000000000000000000000000708000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000048ae1eaa00000000000000000000000000000000000000000000000000000000000000000000000000000000000014580000000000000000000000000000000000000004da0000000001d000000000000000000000001e6800000000000000000000000000000000000000000000000000000040400000000000000000000e78ae0000044000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000114800000000000000000000005600000000001a20000000000438000000000000a0800000000000000000000000000000001eb00000000000000000135000000000000000000000000000144800000014980000000000000000000000000000000000000000000000000000000000000000000000000000000000000018600000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000059c00000000000000000001f580000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000028000000000000000000000000000000000000000000000000830000000000000000c
def mo255L : Nat → Packing
  | 5 => (1,8,6,0,0,0,0,mo255D5)
  | 6 => (3,7,6,0,0,4,0,mo255D6)
  | 7 => (44,6,6,0,0,9,0,mo255D7)
  | 8 => (448,5,6,0,0,12,0,mo255D8)
  | 9 => (1488,4,6,0,0,15,0,mo255D9)
  | 10 => (1352,3,6,0,0,17,0,mo255D10)
  | 11 => (304,2,6,0,0,15,0,mo255D11)
  | 12 => (24,1,6,0,0,11,0,mo255D12)
  | 13 => (1,0,6,0,0,0,0,mo255D13)
  | _ => emptyPacking
def mo255I : Nat → Nat → Option (Nat × Nat)
  | 6 => lookupWord 1 2 0 4 0 0 mo255H6
  | 7 => lookupWord 1 11 0 7 2 1 mo255H7
  | 8 => lookupWord 12 67 6 11 6 1 mo255H8
  | 9 => lookupWord 131 1319 4 14 9 1 mo255H9
  | 10 => lookupWord 485 7187 4 16 11 1 mo255H10
  | 11 => lookupWord 468 2027 10 16 11 1 mo255H11
  | 12 => lookupWord 102 1031 4 14 9 1 mo255H12
  | 13 => lookupWord 7 487 1 10 5 1 mo255H13
  | _ => fun _ => none
def mo255 : Forest := ⟨1279,13,fun i => mo255Y[i]?.getD (0,0),mo255C,mo255A,mo255L,mo255I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo255P5_0 : CutRow mo255 5 0 1 := mixedCut (pos:=387310938923054611101387267) (neg:=124470386497759865407878509901850) (data:=fun _ => 0x439a1010) rfl (by decide +kernel)
theorem mo255B5 : CutRow mo255 5 0 1 := mo255P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo255P6_0 : CutRow mo255 6 0 3 := mixedCut (pos:=387310938923054611101387267) (neg:=124470386497759865407878509901850) (data:=fun _ => 0x439b0120432a1010439a1010) rfl (by decide +kernel)
theorem mo255B6 : CutRow mo255 6 0 3 := mo255P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo255P7_0 : CutRow mo255 7 0 2 := by
  apply checkedRow
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo255P7_2 : CutRow mo255 7 2 42 := mixedCut (pos:=387310938923054611101387267) (neg:=124470386497759865407878509901850) (data:=fun _ => 0x439b0120419a1010419a1010419a1060858b2630439b0120439b0120422310104223101043271010439b5120429b014043231010432310104323101043271010439a101034a210704193401041934060439b012043934010439a101043934010439a1010432a1010432310104123101043931010439b0120439601205489015154890151459710648684552086845520858b36308684551086145510639752207295717684273263) rfl (by decide +kernel)
theorem mo255B7 : CutRow mo255 7 0 44 := (@joinRow mo255 7 0 2 42 mo255P7_0 mo255P7_2)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo255P8_0 : CutRow mo255 8 0 34 := by
  apply checkedRow
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo255P8_34 : CutRow mo255 8 34 96 := mixedCut (pos:=387310938923054611101387267) (neg:=124470386497759865407878509901850) (data:=fun _ => 0x347910603409106014791060547910503409108054091050147910505479105010ab24105472105086735065867350541479106054791050547910501479106054091050543940405479105054324040543240403489017154721070344931515489016134890171544931518673506586735054867350544397101014791060547910504197108634091080540910605409106043951010419a1010439340104393401043934010439a401034394060439a1010439a1010419a1010419a1010419a1080419a1080419a1080419a1080419a10808684553186845531858b36418684552186145521439a101053273220832732706397522063975220639752203679528183273270858b2641360952718327327076295287936b274370957330867350658327327545793250457932604579325045793260457932504679a2504679a250467952604679525045793260457932604572325045723250542732855427328546795260467952604579326045793260457232607495a37586145510) rfl (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo255P8_130 : CutRow mo255 8 130 96 := mixedCut (pos:=387310938923054611101387267) (neg:=124470386497759865407878509901850) (data:=fun _ => 0x439b01204393401043934010419a101043934010419a10104123101043234010419a1010419a1010419a101043934010419a1010419a10104197101041971010419a101041971070419a10704193407041934070439340104393401043934010439a4010439340104393101043931010439310104393101043943120439a1010439b3120439601204394312043943120439b0120439b3120439b31204394312043960120439431204394312043960120439b0120439b0120439b3120439b3120439b012043980120439b012043943120439b012076295287936b2743709673303439406034324060343240603432406034324060344931714193401010ab242134493161439a101043251010439a101043251010439b0120439b0120439b0120439b012041951010419510704195107043960120439601204327101043934010439a101034091070439010103489018141971010419710104197101041971010419710704197107043971010439b0120439b0120147910601479106041971086) rfl (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo255P8_226 : CutRow mo255 8 226 96 := mixedCut (pos:=387310938923054611101387267) (neg:=124470386497759865407878509901850) (data:=fun _ => 0x429b0120429b0120429b012042231010439b0120429b0160429b0160429b0160429b0160429b0160429b0170429b0160429b0160429b0160429b0160429b0170432310104323101043231010439b0120439b0120439b0120439b0120439b0120439b0120439b0120439b0120432310104323101043231010432310104323101043231010439a10104327101043231010439b0120439b0120439b0120439b012043231010439b0120439b0120439b012043231010432310104323101043271010439a101043231010439b0160439b0170439b0160439b0170439b0160432a101083283260858b265236195262858b26308684554234a21080432a101086845542858b36528684553286145532432a1010419a1010419a10104393401043934010439a4010439b31204396012043943120419340104193401041934080439b012043934010419a10104393401043934010439b01204393401043934010432310104323401043231010432a1010432310104323401043971010419a1010419a1010) rfl (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo255P8_322 : CutRow mo255 8 322 96 := mixedCut (pos:=387310938923054611101387267) (neg:=124470386497759865407878509901850) (data:=fun _ => 0x419a1010419a1010419a1010419a1010419a1010419a1010419a1010419a1010419a1010419a1010419a1010419a1010419a1010419a1010419a1010419a1010419a106041934070419a1060419a1060419a1060419a1060419a1060419a1060419a1060419a1060419a1060419a1060419a1060419a1060419a1060419a1070419a1060419a1060419a1060419a1060419a1060419a1060419a1060419a1060419a101041971070439310104393101043971010439b01204397101043931010439710104397101043931010439b012043271010858b264136095261832832704223101042231010422310104223101042231010439b0120439b0120439b0120439b0120439b0120439b0120439b0120439b0120439b0120439b0120439b0120439b0120439b0120439b0120439b0120439b01204223101042231010422310104223101042231010439b0120439b012043271010429b012043271010422310104223101043271010439b0120439b0120439b0120439b01204327101042231010) rfl (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo255P8_418 : CutRow mo255 8 418 30 := mixedCut (pos:=387310938923054611101387267) (neg:=124470386497759865407878509901850) (data:=fun _ => 0x439a1010439a101043251010439b012010ab2421419a1010439b0120432710104396012041231010412310104123101041231010419a1010439b31204123101041231010412310108684654286846542858b46528684653286146532419a1010419a1010419a1010419a1010419a1010419a1010419a1010) rfl (by decide +kernel)
theorem mo255B8 : CutRow mo255 8 0 448 := (@joinRow mo255 8 0 226 222 (@joinRow mo255 8 0 34 192 mo255P8_0 (@joinRow mo255 8 34 96 96 mo255P8_34 mo255P8_130)) (@joinRow mo255 8 226 96 126 mo255P8_226 (@joinRow mo255 8 322 96 30 mo255P8_322 mo255P8_418)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo255P9_0 : CutRow mo255 9 0 8 := by
  apply checkedRow
  apply cellsBlock (ar:=8) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo255P9_8 : CutRow mo255 9 8 96 := by
  apply checkedRow
  apply cellsBlock (ar:=9) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo255P9_104 : CutRow mo255 9 104 96 := by
  apply checkedRow
  apply cellsBlock (ar:=9) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo255P9_200 : CutRow mo255 9 200 96 := by
  apply checkedRow
  apply cellsBlock (ar:=9) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo255P9_296 : CutRow mo255 9 296 35 := by
  apply checkedRow
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo255P9_331 : CutRow mo255 9 331 4 := by
  apply checkedRow
  apply cellsBlock (ar:=10) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo255P9_335 : CutRow mo255 9 335 96 := mixedCut (pos:=387310938923054611101387267) (neg:=124470386497759865407878509901850) (data:=fun _ => 0x63975220639752205397322053973220532732207095a380861455325397322053973220532732206397522063975220539732205327322053273220532732205327329063975220729573307295733072957320722573308613553253973220539732205397322053973220539732206097a2206097a220639752206397522053973220539732205327322053273220532732905327329063975220639752205397322053973220532732207095a380861455327095734086845553936b276386145573936b2794936b2764858b365370957340936b2754936b2753936b2753858b3663868455838614557386145572539032306390523063905230539032303609529286145543539732305397323079289583684155736848557385892642970973835898269435793272357932823579327235793282357932720679a2720679a272367952823679527235793282357932823572327235723272532732975327329736795282367952823579328235793282357232827095a38786145532) rfl (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo255P9_431 : CutRow mo255 9 431 96 := mixedCut (pos:=387310938923054611101387267) (neg:=124470386497759865407878509901850) (data:=fun _ => 0x439340104393401043934010439340104393401043934080439340804395101043951010439510104395101043951080439a1010439a1010439a1010439a1010439a1010439a101053973230439a101053273230439a1010439a1010439a1010439a1010439a10105327328053273280439a1010439a10105397323053903230439a101036095282419a1010439a1010419a1010439a1010419a101053273230439a1010419a1010439a1010419a1010419a1010439a4010439a1010419a1010439a1010439a1010419a1010439a4010439a1010439a10108684554286845542858a36528684553286145532439a1010439a1010439a1010439a1010439a1010439a1010439a1010439a1010439a1010439a1010439a1010439a1010439a1010439a1010439a1010439a1010439a1010439a1010439a1010439a1010439a1010439a101053973220539732205397322053973220539732206097a2206097a2206397522063975220539732205397322053273220532732205327329053273290) rfl (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo255P9_527 : CutRow mo255 9 527 96 := mixedCut (pos:=387310938923054611101387267) (neg:=124470386497759865407878509901850) (data:=fun _ => 0x10a424103432406054890171343240603432406034324060343240603472108034324060343240603432406054324060344931713489018134190171348901715489017158982684544931613489017134890171341901713489017134890171344931715489017134890171348901713489017185892642971973735868366443971010439710104393401043934010439340104393401043971010439710104393401010ab2421439710104197101010ab242110ab242110ab2421147910704197101010ab242110ab24214397101010ab24219479807043971010439510104395101043931010439310104397101043901010439010104390101043901010439010104390101043901010439010104390101043901010439010104390101043931010439010104390101010ab242154091080340910804393101010ab242143951010439a1010439a101043951010439510104395101043951010439510104395101043951070419a80104393401043934010439340104393401043934010) rfl (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo255P9_623 : CutRow mo255 9 623 96 := mixedCut (pos:=387310938923054611101387267) (neg:=124470386497759865407878509901850) (data:=fun _ => 0x4327101043271010432710104327101043271010432710104327101043271010432710104327101043274010432710104397101043271010439710104327101043980120439710104327101043271010439b0120439801204398012043980120439b01204398012043980120439801204398012043980120439801204398012043980120439801204398012043980120439801204398012043980120439801204398012043980120439801204398012043980120439801205398323053983230792895836841556342978010348901713479107034791080348901813489017134890171684855634197101014791070340910803409109034791090343940905479107010ab24105479107054721070547910703479108034394060547910705409107054791070347910701479107010ab2410347910703489017134791080147910805479107034091070347910702709739334394060343940605439406010a8241034a91070547910705479107034791070343940703479108094798070) rfl (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo255P9_719 : CutRow mo255 9 719 96 := mixedCut (pos:=387310938923054611101387267) (neg:=124470386497759865407878509901850) (data:=fun _ => 0x439b0120439b012043980120439b0120439b012043960120439601205391323063915230639152305391323036195292861455434195101043934010439340104393401043934010439340104393401043934010439340104395101041951010439340104393401043951010439710104397101043971010439a10104397101043971010439710104397101043971010439710104390101043971010439a101043971010439a101043971010439710104397101043971010432710104327101043971010439710104397101010ab2421439710104397101043971010432710104390101043980120439801204398012043980120439801204398012041971010419710104197101043971010439710104397101043971010419710104197101041971090439a1010439a101043971010439a1010439a1010439a1010439a1010439a101043971010439a101043971010439710104397101043971010439710104297801043971010439710104397101043971010439710104397101043971010) rfl (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo255P9_815 : CutRow mo255 9 815 96 := mixedCut (pos:=387310938923054611101387267) (neg:=124470386497759865407878509901850) (data:=fun _ => 0x4395101043951010439510104395101043934010439510104395101043951010439510104395101043951010439601204396012043960120439601204396012043951010419510104195101041951010439a1010439a1010439a1010439a1010439a1010439a1010439a1010439a101043971010439a10104395101043951010439510104395101034591090439a1010439510104395101043951010439510104395101043951010439510104395101043251010432510104325101043251010432510104325101043251010432510104325101043251010432510104325101043251010439510104325101043254010439601204396012043960120439601204396012043960120439601204396012043960120439601204396012043960120439601204396012043960120439601204396012043960120439601204396012043960120439601204396012043960120439601204396012043960120439b0120439b0120439b01204325101043960120439b0120439601204396012043960120) rfl (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo255P9_911 : CutRow mo255 9 911 96 := mixedCut (pos:=387310938923054611101387267) (neg:=124470386497759865407878509901850) (data:=fun _ => 0x4394312043943120439431204394312043943120439831204394012043943120439b31204394312043943120439601204394312043943120439431204394312043943120439431204394312043943120439b3120439b3120439431204394312043943120439b3120439b3120439431204396312043943120439b312043983120439b0120439b31204394312043943120409b0120439b31204394312043943120936b276386145563936b2794936b2764858b365370967340936b2754936b2753936b2753858b366386845573861455633439407034324070343940703439408034324070343240703432407034324070344931813449317110ab242110ab242110ab242110ab242110ab242110ab24213439407034324070343940703439408034324070343240703449318134493171861455624397101043971010439710104397101043951010439a101043971010439a10104395101043931010439510104395101043251010432710104325101043931010439510103609528243951010) rfl (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo255P9_1007 : CutRow mo255 9 1007 96 := mixedCut (pos:=387310938923054611101387267) (neg:=124470386497759865407878509901850) (data:=fun _ => 0x4393401043934010419a1010419a101041971010439340104323401041934010419a1010419a1010439340104393401043934010419a1010419a101043934010419510104393401043934010439340104323401043934010419a101043934010419710104393401043931010439340104393401043934010439b312043980120409b0120439431204394312041971010439340104393401041971010419a10104393401041934010419340104193409043934010439a4010439a40104393401043974010439a401043934010439340104393401043934010439a4010439340104393401043934010439340104393401043974010439a4010439340104395401043934010439340104393401043943120439310104393101043943120439431204393401043943120439431204394312043934010439340104393101043934010432340104323401043234010432340104323401043234010432340104323401043934010432a4010432340104323401043943120439b31204394312043963120) rfl (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo255P9_1103 : CutRow mo255 9 1103 96 := mixedCut (pos:=387310938923054611101387267) (neg:=124470386497759865407878509901850) (data:=fun _ => 0x53913230639852303619528286845553432a10105328323086845553858b3663439a1010432a101086845543432a101086145543432a10107226734086145543432a1010422a801042978010429a8010432a1010432a1010432a1010432a1010429b7120429b7120429b7120429b7120429b7120422a1010419ab010409b0120439b5120409b012041971010419a6010419a6010419a6090432a1010432a1010439b5120439b512070967340868455534393401043934010439340104393401043934010419a1010439340104323401043234010432340104323401043934010439740104393401043931010439340104393401043934010439340104393401043943120439340104193401043934010439340104393408043934080439b01204393401043971010439340104393401043934010419a1010439340104393401043934010439340104393401043934010439340104393401043234010432340104323401043234010439340104393401043971010419a1010409b012043934010) rfl (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo255P9_1199 : CutRow mo255 9 1199 96 := mixedCut (pos:=387310938923054611101387267) (neg:=124470386497759865407878509901850) (data:=fun _ => 0x43960120432b01204398012036896282858b2663858b265363985230539832305328323053283230532832906398523042231010422310104223101042231010429b0120429b0120429b0120439b0120439b0120439b0120439b012042231010429b0120429b0120439b012043271010429b0120429b012042231010429b0120429b0120439b0120429b0120429b0120439b0120439a1010439b0120432a1010439a1010439a1010439a1010439a1010439b0120439a1010439b0120439a10107296733072967330722673306831557343231010432310104323101043231010439b0120439b0120439b0120439b0120439b0120432510104323101043231010439b0120439b0120439b0120439b0120439b0120439b012043231010439b0120432a10105398323053983230432a1010432a101053283230729673406398523063985230432a101053983230432a1010532832305398323053283230532832305328323072967340432a10105328328053283280729673305328328053983230) rfl (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo255P9_1295 : CutRow mo255 9 1295 96 := mixedCut (pos:=387310938923054611101387267) (neg:=124470386497759865407878509901850) (data:=fun _ => 0x419a1010419a1010419a1010419a1010419a1010419a1010419a1010419a1010419a1010419a1080419a1080419a1080419a1080419a1080419a1080439b0120439b0120439b0120439b0120439b0120419a1080419a1080419a1080419a1080419a1080419a1080419a1080419710104197101041971010419710104197101041971090429a80104297801043931010439310104393101043971010439710104397101043931010439b01204397101043971010439b0120439b0120439b012043971010439b0120419ab01043976010439710104393101043931010439510104395101043951010439710104397101043971010439a10106097a230439a10104397401043974010439a1010439a1010439a4010439a10104327101043971010439a1010432a4010432a40104325101043251010432510104325101043251010432710104327101043271010432710104327101043271010432510104325101043271010439b0120439b012043271010439b0120432b0120432b012043960120) rfl (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo255P9_1391 : CutRow mo255 9 1391 96 := mixedCut (pos:=387310938923054611101387267) (neg:=124470386497759865407878509901850) (data:=fun _ => 0x43971010419a1010432a1010432a1010429b0120429b012043271010429b0120439510104395101043251010439a1010439a1010439a1010432a101043971010419a1010432a1010439b012043251010439b0120439b012043971010439710104397101043271010439510103459107036095272858b265253903230432a1010432a1010432a101010ab2421439710104397101043271010419a1010419a1010439b012041971010432a101043971010419a101043934010419a1010432a1010432a1010429b01204395101043251010439b012043943120439b01208684554386145543868465534123101086846553858b4663868465438614654343971010439710104398012043980120419a1010419a1010419a1010419a1010419a1010419a1010419a1010419a1010419a1010419a1010419a1010419a1010419a1010419a1010419a1010419a1010419a1010419a1010419a1010419a1010419a101041934010419a1010419a1010419a1010419a1010419a1010419a1010419a1010) rfl (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo255P9_1487 : CutRow mo255 9 1487 1 := mixedCut (pos:=387310938923054611101387267) (neg:=124470386497759865407878509901850) (data:=fun _ => 0x432a1010) rfl (by decide +kernel)
theorem mo255B9 : CutRow mo255 9 0 1488 := (@joinRow mo255 9 0 623 865 (@joinRow mo255 9 0 296 327 (@joinRow mo255 9 0 104 192 (@joinRow mo255 9 0 8 96 mo255P9_0 mo255P9_8) (@joinRow mo255 9 104 96 96 mo255P9_104 mo255P9_200)) (@joinRow mo255 9 296 39 288 (@joinRow mo255 9 296 35 4 mo255P9_296 mo255P9_331) (@joinRow mo255 9 335 96 192 mo255P9_335 (@joinRow mo255 9 431 96 96 mo255P9_431 mo255P9_527)))) (@joinRow mo255 9 623 480 385 (@joinRow mo255 9 623 192 288 (@joinRow mo255 9 623 96 96 mo255P9_623 mo255P9_719) (@joinRow mo255 9 815 96 192 mo255P9_815 (@joinRow mo255 9 911 96 96 mo255P9_911 mo255P9_1007))) (@joinRow mo255 9 1103 192 193 (@joinRow mo255 9 1103 96 96 mo255P9_1103 mo255P9_1199) (@joinRow mo255 9 1295 96 97 mo255P9_1295 (@joinRow mo255 9 1391 96 1 mo255P9_1391 mo255P9_1487)))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo255P10_0 : CutRow mo255 10 0 21 := by
  apply checkedRow
  apply cellsBlock (ar:=8) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo255P10_21 : CutRow mo255 10 21 96 := by
  apply checkedRow
  apply cellsBlock (ar:=9) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo255P10_117 : CutRow mo255 10 117 46 := by
  apply checkedRow
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo255P10_163 : CutRow mo255 10 163 96 := by
  apply checkedRow
  apply cellsBlock (ar:=10) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo255P10_259 : CutRow mo255 10 259 96 := by
  apply checkedRow
  apply cellsBlock (ar:=10) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo255P10_355 : CutRow mo255 10 355 96 := by
  apply checkedRow
  apply cellsBlock (ar:=10) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo255P10_451 : CutRow mo255 10 451 96 := by
  apply checkedRow
  apply cellsBlock (ar:=10) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo255P10_547 : CutRow mo255 10 547 96 := by
  apply checkedRow
  apply cellsBlock (ar:=10) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo255P10_643 : CutRow mo255 10 643 96 := by
  apply checkedRow
  apply cellsBlock (ar:=10) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo255P10_739 : CutRow mo255 10 739 96 := by
  apply checkedRow
  apply cellsBlock (ar:=10) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo255P10_835 : CutRow mo255 10 835 52 := by
  apply checkedRow
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo255P10_887 : CutRow mo255 10 887 6 := by
  apply checkedRow
  apply cellsBlock (ar:=11) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo255P10_893 : CutRow mo255 10 893 96 := mixedCut (pos:=387310938923054611101387267) (neg:=124470386497759865407878509901850) (data:=fun _ => 0x429780104297801010ab242110ab242110ab242110ab242110ab242110ab242110ab242110ab242110ab242110ab242110ab242110ab242110ab242110ab24214397101043901010439010104390101043901010439010104390101043901010439010104390101010ab242110ab24214395101043934010439340104395101053973230539732305397323053273230539032306097a23063975230639752306097a230532732305327323053273230532732307295734053273230868455538684555385863663784b5975754b097575480975868455536097a230968495536097a2307095a340861455537095a34086845553858b2663936b2774858b2663936b2774858b2663851b3663858b266385892663936b2774936b2774936b27748586366353903230539032305390323053903230539032308684555363905230532032306390523072907340729073407290734072907340729073407290734072907340729073409682955385892663729073407290734072907340654b0865) rfl (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo255P10_989 : CutRow mo255 10 989 96 := mixedCut (pos:=387310938923054611101387267) (neg:=124470386497759865407878509901850) (data:=fun _ => 0x439340104393401043934010439340104393401043934010439340104393401010ab24214395101043971010439710104397101043971010439710104397101043971010439710104397101043971010439710104397101043971010439710104397101043971010439710104397101043271010439010104397101043971010439710104397101043971010439710104397101043971010439801204197101043971010439710104397101043971010439710104397101043971010439710104397101043971010439710104397101043971010439710104297801042978010429780104297801042978010439801204398012043980120439801204398012043980120439801204398012043980120439801204398012043980120439801204398012043980120439801204398012043980120439801204398012072917340729173407291734072917340729173407291734072917340729173409682955385892663729173407291734072917340654b0865429780104297801042978010) rfl (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo255P10_1085 : CutRow mo255 10 1085 96 := mixedCut (pos:=387310938923054611101387267) (neg:=124470386497759865407878509901850) (data:=fun _ => 0x4394312043234010432340104323401043943120439431204394312043943120439431204394312043943120439431204394312043943120439431204394312043943120858b3663936b2774858b3663936b2774858b3663851b3663858b366385893663936b2774936b2774936b27748586366310ab242110ab242110ab242110ab242110ab242110ab242110ab2421439710104395101043951010439510104395101043951010439510104395101043951010439510104395101043951010439510104395101043951010439510104395101043951010439510104395101043951010432510104393101043951010439510104395101043951010439510104395101043951010439510104395101043956010439560104325401043254010432540104325401043254010432540104325401043960120439601204396012043960120439601204396012043960120539132305391323053913230539132305391323086845553639152305321323063915230439560104395601043934010) rfl (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo255P10_1181 : CutRow mo255 10 1181 96 := mixedCut (pos:=387310938923054611101387267) (neg:=124470386497759865407878509901850) (data:=fun _ => 0x432b3120432b3120432b3120432b3120784b5975754b097575480975729673406546086553983230539832305398323053283230539132306098a23063985230639852306098a230532832305328323053283230532832307296734053283230868455538684555385863663784b5975754b09757548097586845553422a801042978010429b7120429b7120429b7120429b71206098a2309684a5536098a230432a601043956010439a6010439b512043956010419a60107096a340861455537096a3408684555343934010439340104393401043934010439340104393401043934010439340104393401043934010439340104393401043934010439340104393401043934010439340104393401043934010439340104393401043934010439340104393401043943120439340104193401043934010439340104393401043934010439340104393401043934010439340104393401043934010439340104393401043934010439340104394312043943120439431204394312043943120) rfl (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo255P10_1277 : CutRow mo255 10 1277 75 := mixedCut (pos:=387310938923054611101387267) (neg:=124470386497759865407878509901850) (data:=fun _ => 0x432a101043971010419a1010432a101043951010439510104395101043951010439a1010432a101043951010439a1010432a101043971010419a1010439710104397101043971010432a101043971010419a1010439b0120439b0120439b0120439b0120439b0120439b0120439b0120868455534397101043971010439710104397101043971010439710104397101043971010439710104397101043980120419a1010419a1010419a1010419a1010419a1010419a1010419a1010419a101041971010429a801042978010439a601043956010439a601043976010432a4010432a4010432a401043274010432a4010432a4010432b012043980120432b3120432b3120432b3120439b0120432b012043960120439b01208683555343980120429b7120429b7120429b7120) rfl (by decide +kernel)
theorem mo255B10 : CutRow mo255 10 0 1352 := (@joinRow mo255 10 0 643 709 (@joinRow mo255 10 0 259 384 (@joinRow mo255 10 0 117 142 (@joinRow mo255 10 0 21 96 mo255P10_0 mo255P10_21) (@joinRow mo255 10 117 46 96 mo255P10_117 mo255P10_163)) (@joinRow mo255 10 259 192 192 (@joinRow mo255 10 259 96 96 mo255P10_259 mo255P10_355) (@joinRow mo255 10 451 96 96 mo255P10_451 mo255P10_547))) (@joinRow mo255 10 643 250 459 (@joinRow mo255 10 643 192 58 (@joinRow mo255 10 643 96 96 mo255P10_643 mo255P10_739) (@joinRow mo255 10 835 52 6 mo255P10_835 mo255P10_887)) (@joinRow mo255 10 893 192 267 (@joinRow mo255 10 893 96 96 mo255P10_893 mo255P10_989) (@joinRow mo255 10 1085 96 171 mo255P10_1085 (@joinRow mo255 10 1181 96 75 mo255P10_1181 mo255P10_1277)))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo255P11_0 : CutRow mo255 11 0 10 := by
  apply checkedRow
  apply cellsBlock (ar:=8) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo255P11_10 : CutRow mo255 11 10 96 := by
  apply checkedRow
  apply cellsBlock (ar:=9) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo255P11_106 : CutRow mo255 11 106 14 := by
  apply checkedRow
  apply cellsBlock (ar:=9) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo255P11_120 : CutRow mo255 11 120 96 := by
  apply checkedRow
  apply cellsBlock (ar:=10) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo255P11_216 : CutRow mo255 11 216 88 := by
  apply checkedRow
  apply cellsBlock (ar:=10) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem mo255B11 : CutRow mo255 11 0 304 := (@joinRow mo255 11 0 106 198 (@joinRow mo255 11 0 10 96 mo255P11_0 mo255P11_10) (@joinRow mo255 11 106 14 184 mo255P11_106 (@joinRow mo255 11 120 96 88 mo255P11_120 mo255P11_216)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo255P12_0 : CutRow mo255 12 0 24 := by
  apply checkedRow
  apply cellsBlock (ar:=9) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem mo255B12 : CutRow mo255 12 0 24 := mo255P12_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo255P13_0 : CutRow mo255 13 0 1 := by
  apply checkedRow
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem mo255B13 : CutRow mo255 13 0 1 := mo255P13_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo255T : mixedTables mo255 13 := by
  intro k hk
  interval_cases k
  · exact (mixedEmpty mo255 0 0)
  · exact (mixedEmpty mo255 1 0)
  · exact (mixedEmpty mo255 2 0)
  · exact (mixedEmpty mo255 3 0)
  · exact (mixedEmpty mo255 4 0)
  · exact mo255B5
  · exact mo255B6
  · exact mo255B7
  · exact mo255B8
  · exact mo255B9
  · exact mo255B10
  · exact mo255B11
  · exact mo255B12
  · exact mo255B13
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo255G : graphValid mo255 (boundsBefore K254) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo255R : Impossible false graph 13 eightInputs.toFinset := by
  rw [show graph = targetOf mo255 by decide +kernel]
  exact mixedRoot (g:=mo255) (top:=13) (i:=0) (before_sound K254 (known_down V254)) mo255G mo255T (by decide) (by decide +kernel)

end Bound

open Bound in
theorem Bound : ∀ t : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 8 (fun x : Fin 8 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 3 && x 5) || (x 3 && x 6) || (x 4 && x 7) || (x 5 && x 6) || (x 5 && x 7)) t → 14 ≤ t := by
  intro t hs
  by_contra! small
  obtain ⟨C,hf,hsize,heq⟩ := hs
  exact directSplit mo255R g255R ⟨C,hf,by omega,heq⟩

end PEqualNP.Outside.L_meta_17271_aux.Pin

namespace PEqualNP.Outside.L_meta_17271_aux
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem wiresFrom_append (gs gs' : List Gate) (w : List Bool) :
    wiresFrom (gs ++ gs') w = wiresFrom gs' (wiresFrom gs w) := by
  simp [wiresFrom, List.foldl_append]

theorem wiresFrom_prefix (gs : List Gate) : ∀ w : List Bool,
    ∃ t : List Bool, wiresFrom gs w = w ++ t ∧ t.length = gs.length := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp [wiresFrom], rfl⟩
  | cons g gs ih =>
    intro w
    obtain ⟨t, ht, hl⟩ := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: t, ?_, by simp [hl]⟩
    have : wiresFrom (g :: gs) w
        = wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl
    rw [this, ht]; simp

theorem length_wiresFrom (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := wiresFrom_prefix gs w
  rw [ht]; simp [hl]

theorem getD_wiresFrom (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := wiresFrom_prefix gs w
  rw [ht, List.getD_append _ _ _ _ h]

def Ok (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2

theorem getD_snoc_ne {α : Type} (L : List α) (S d : α) (j : ℕ) (h : j ≠ L.length) :
    (L ++ [S]).getD j d = L.getD j d := by
  by_cases hj : j < L.length
  · exact List.getD_append _ _ _ _ hj
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

theorem getD_snoc_eq {α : Type} (L : List α) (S d : α) : (L ++ [S]).getD L.length d = S := by
  simp

theorem getD_snoc_len {α : Type} (L : List α) (S d : α) (k : ℕ) (h : L.length = k) :
    (L ++ [S]).getD k d = S := by
  subst h; simp

def gateSupp {n : ℕ} (L : List (Finset (Fin n))) (g : Gate) : Finset (Fin n) :=
  (g.inputs.map fun a => L.getD a ∅).foldr (· ∪ ·) ∅

theorem mem_foldr_union {n : ℕ} (l : List ℕ) (F : ℕ → Finset (Fin n)) (i : Fin n) :
    i ∈ (l.map F).foldr (· ∪ ·) ∅ ↔ ∃ a ∈ l, i ∈ F a := by
  induction l with
  | nil => simp
  | cons b l ih => simp [ih]

theorem mem_gateSupp {n : ℕ} (L : List (Finset (Fin n))) (g : Gate) (i : Fin n) :
    i ∈ gateSupp L g ↔ ∃ a ∈ g.inputs, i ∈ L.getD a ∅ :=
  mem_foldr_union _ _ _

def suppsFrom {n : ℕ} (gs : List Gate) (L : List (Finset (Fin n))) : List (Finset (Fin n)) :=
  gs.foldl (fun L g => L ++ [gateSupp L g]) L

def inputSupps (n : ℕ) : List (Finset (Fin n)) := List.ofFn fun i : Fin n => {i}

def Agree {n : ℕ} (x y : Fin n → Bool) (L : List (Finset (Fin n))) (w w' : List Bool) : Prop :=
  L.length = w.length ∧ w.length = w'.length ∧
    ∀ j : ℕ, (∀ i ∈ L.getD j ∅, x i = y i) → w.getD j false = w'.getD j false

theorem agree_wiresFrom {n : ℕ} (x y : Fin n → Bool) (gs : List Gate) :
    ∀ (L : List (Finset (Fin n))) (w w' : List Bool), Agree x y L w w' →
      Agree x y (suppsFrom gs L) (wiresFrom gs w) (wiresFrom gs w') := by
  induction gs with
  | nil => intro L w w' h; exact h
  | cons g gs ih =>
    intro L w w' h
    obtain ⟨h1, h2, h3⟩ := h
    apply ih (L ++ [gateSupp L g])
      (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
      (w' ++ [g.op.eval (g.inputs.map fun i => w'.getD i false)])
    refine ⟨by simp [h1], by simp [h2], ?_⟩
    intro j hj
    by_cases hjl : j = L.length
    · subst hjl
      rw [getD_snoc_eq] at hj
      rw [h1, getD_snoc_eq, h2, getD_snoc_eq]
      congr 1
      apply List.map_congr_left
      intro a ha
      exact h3 a (fun i hi => hj i ((mem_gateSupp L g i).2 ⟨a, ha, hi⟩))
    · rw [getD_snoc_ne _ _ _ _ hjl] at hj
      rw [getD_snoc_ne _ _ _ _ (by omega), getD_snoc_ne _ _ _ _ (by omega)]
      exact h3 j hj

theorem agree_inputs {n : ℕ} (x y : Fin n → Bool) :
    Agree x y (inputSupps n) (List.ofFn x) (List.ofFn y) := by
  refine ⟨by simp [inputSupps], by simp, ?_⟩
  intro j hj
  by_cases hjn : j < n
  · have hx : x ⟨j, hjn⟩ = y ⟨j, hjn⟩ := hj _ (by simp [inputSupps, hjn])
    simp [hjn, hx]
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]

def normGate (g : Gate) : Gate :=
  match g.op with
  | GateOp.not => ⟨GateOp.not, g.inputs.take 1⟩
  | _ => g

theorem normGate_eval (g : Gate) (F : ℕ → Bool) :
    (normGate g).op.eval ((normGate g).inputs.map F) = g.op.eval (g.inputs.map F) := by
  obtain ⟨op, inputs⟩ := g
  cases op <;> simp only [normGate]
  cases inputs <;> simp [GateOp.eval]

def NOk (g : Gate) : Prop := Ok g ∧ (g.op = GateOp.not → g.inputs.length ≤ 1)

theorem normGate_nok (g : Gate) (h : Ok g) : NOk (normGate g) := by
  obtain ⟨op, inputs⟩ := g
  obtain ⟨hop, hlen⟩ := h
  rcases hop with h | h | h
  · have : op = GateOp.and := h
    subst this; exact ⟨⟨Or.inl rfl, hlen⟩, by simp [normGate]⟩
  · have : op = GateOp.or := h
    subst this; exact ⟨⟨Or.inr (Or.inl rfl), hlen⟩, by simp [normGate]⟩
  · have : op = GateOp.not := h
    subst this
    refine ⟨⟨Or.inr (Or.inr rfl), ?_⟩, fun _ => ?_⟩ <;> simp [normGate] <;> omega

theorem wiresFrom_norm (gs : List Gate) : ∀ w : List Bool,
    wiresFrom (gs.map normGate) w = wiresFrom gs w := by
  induction gs with
  | nil => intro w; rfl
  | cons g gs ih =>
    intro w
    have s1 : wiresFrom ((g :: gs).map normGate) w = wiresFrom (gs.map normGate)
        (w ++ [(normGate g).op.eval ((normGate g).inputs.map fun i => w.getD i false)]) := rfl
    have s2 : wiresFrom (g :: gs) w
        = wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl
    rw [s1, s2, normGate_eval, ih]

abbrev Stat := Sum Bool ℕ

def statVal (w : List Bool) : Stat → Bool
  | Sum.inl c => c
  | Sum.inr j => w.getD j false

def statValid (m : ℕ) : Stat → Prop
  | Sum.inl _ => True
  | Sum.inr j => j < m

def simpNot (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none, Sum.inl true)
  | Sum.inl c :: _ => (none, Sum.inl (!c))
  | Sum.inr j :: _ => (some ⟨GateOp.not, [j]⟩, Sum.inr m)

def simpAnd (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none, Sum.inl true)
  | [Sum.inl c] => (none, Sum.inl c)
  | [Sum.inr j] => (none, Sum.inr j)
  | [Sum.inl c, Sum.inl d] => (none, Sum.inl (c && d))
  | [Sum.inl c, Sum.inr j] => (none, bif c then Sum.inr j else Sum.inl false)
  | [Sum.inr j, Sum.inl c] => (none, bif c then Sum.inr j else Sum.inl false)
  | [Sum.inr j, Sum.inr k] => (some ⟨GateOp.and, [j, k]⟩, Sum.inr m)
  | _ => (none, Sum.inl false)

def simpOr (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none, Sum.inl false)
  | [Sum.inl c] => (none, Sum.inl c)
  | [Sum.inr j] => (none, Sum.inr j)
  | [Sum.inl c, Sum.inl d] => (none, Sum.inl (c || d))
  | [Sum.inl c, Sum.inr j] => (none, bif c then Sum.inl true else Sum.inr j)
  | [Sum.inr j, Sum.inl c] => (none, bif c then Sum.inl true else Sum.inr j)
  | [Sum.inr j, Sum.inr k] => (some ⟨GateOp.or, [j, k]⟩, Sum.inr m)
  | _ => (none, Sum.inl false)

def simplify (op : GateOp) (m : ℕ) (ins : List Stat) : Option Gate × Stat :=
  match op with
  | GateOp.and => simpAnd m ins
  | GateOp.or => simpOr m ins
  | GateOp.not => simpNot m ins
  | _ => (none, Sum.inl false)

theorem simplify_ok (op : GateOp) (m : ℕ) (ins : List Stat) :
    ∀ g ∈ (simplify op m ins).1, Ok g := by
  intro g hg
  cases op <;> simp only [simplify] at hg
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpAnd] at hg <;> (subst hg; simp [Ok])
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpOr] at hg <;> (subst hg; simp [Ok])
  · rcases ins with _ | ⟨a, l⟩ <;> (try cases a) <;>
      simp [simpNot] at hg <;> (subst hg; simp [Ok])
  · simp at hg
  · simp at hg

theorem simplify_count (op : GateOp) (m : ℕ) (ins : List Stat)
    (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not) (hlen : ins.length ≤ 2)
    (hnot : op = GateOp.not → ins.length ≤ 1) (hc : ∃ c, Sum.inl c ∈ ins) :
    (simplify op m ins).1 = none := by
  obtain ⟨c, hc⟩ := hc
  rcases hop with rfl | rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp_all [simplify, simpAnd]
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp_all [simplify, simpOr]
  · have := hnot rfl
    rcases ins with _ | ⟨a, _ | ⟨b, l⟩⟩ <;> (try cases a) <;> simp_all [simplify, simpNot]

theorem simplify_sound (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not)
    (w : List Bool) (ins : List Stat) (hlen : ins.length ≤ 2)
    (hv : ∀ s ∈ ins, statValid w.length s) :
    statValid (w.length + (simplify op w.length ins).1.toList.length) (simplify op w.length ins).2 ∧
    statVal (wiresFrom (simplify op w.length ins).1.toList w) (simplify op w.length ins).2
      = op.eval (ins.map (statVal w)) := by
  rcases hop with rfl | rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [simplify, simpAnd, statValid, statVal, GateOp.eval]
    · cases a <;> simp_all [simplify, simpAnd, statValid, statVal, GateOp.eval, wiresFrom]
    · cases a <;> cases b <;> (try rename_i c e; cases c) <;> (try cases e) <;>
        simp_all [simplify, simpAnd, statValid, statVal, GateOp.eval, wiresFrom]
    · simp at hlen
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [simplify, simpOr, statValid, statVal, GateOp.eval]
    · cases a <;> simp_all [simplify, simpOr, statValid, statVal, GateOp.eval, wiresFrom]
    · cases a <;> cases b <;> (try rename_i c e; cases c) <;> (try cases e) <;>
        simp_all [simplify, simpOr, statValid, statVal, GateOp.eval, wiresFrom]
    · simp at hlen
  · rcases ins with _ | ⟨a, l⟩
    · simp [simplify, simpNot, statValid, statVal, GateOp.eval]
    · cases a <;> simp_all [simplify, simpNot, statValid, statVal, GateOp.eval, wiresFrom]

def elimStep (n : ℕ) (acc : List Stat × List Gate) (g : Gate) : List Stat × List Gate :=
  (acc.1 ++ [(simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).2],
    acc.2 ++ (simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1.toList)

def elim (n : ℕ) (gs : List Gate) (acc : List Stat × List Gate) : List Stat × List Gate :=
  gs.foldl (elimStep n) acc

theorem elim_cons (n : ℕ) (g : Gate) (gs : List Gate) (acc : List Stat × List Gate) :
    elim n (g :: gs) acc = elim n gs (elimStep n acc g) := rfl

theorem elim_append (n : ℕ) (pre post : List Gate) (acc : List Stat × List Gate) :
    elim n (pre ++ post) acc = elim n post (elim n pre acc) := by
  simp [elim, List.foldl_append]

theorem elim_fst_len (n : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (elim n gs acc).1.length = acc.1.length + gs.length := by
  induction gs with
  | nil => intro acc; rfl
  | cons g gs ih =>
    intro acc
    rw [elim_cons, ih]
    simp only [elimStep, List.length_append, List.length_cons, List.length_nil]
    omega

theorem elim_getD (n k : ℕ) (d : Stat) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    k < acc.1.length → (elim n gs acc).1.getD k d = acc.1.getD k d := by
  induction gs with
  | nil => intro acc _; rfl
  | cons g gs ih =>
    intro acc hk
    rw [elim_cons, ih (elimStep n acc g) (by simp [elimStep]; omega)]
    exact getD_snoc_ne _ _ _ _ (by omega)

theorem toList_length_le {α : Type} (o : Option α) : o.toList.length ≤ 1 := by
  cases o <;> simp

theorem elim_ok (n : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (∀ g ∈ acc.2, Ok g) → ∀ g ∈ (elim n gs acc).2, Ok g := by
  induction gs with
  | nil => intro acc h; exact h
  | cons g gs ih =>
    intro acc h
    apply ih (elimStep n acc g)
    intro g' hg'
    rcases List.mem_append.1 hg' with h1 | h1
    · exact h g' h1
    · exact simplify_ok _ _ _ g' (by simpa using h1)

theorem elim_len (n : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (elim n gs acc).2.length ≤ acc.2.length + gs.length := by
  induction gs with
  | nil => intro acc; simp [elim]
  | cons g gs ih =>
    intro acc
    have h1 := ih (elimStep n acc g)
    have h2 : (elimStep n acc g).2.length ≤ acc.2.length + 1 := by
      simp only [elimStep, List.length_append]
      have := toList_length_le (simplify g.op (n + acc.2.length)
        (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1
      omega
    rw [elim_cons, List.length_cons]; omega

theorem elim_len_lt (n k : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (∀ g ∈ gs, NOk g) → k < acc.1.length → (∃ c, acc.1.getD k (Sum.inl false) = Sum.inl c) →
    (∃ g ∈ gs, k ∈ g.inputs) → (elim n gs acc).2.length + 1 ≤ acc.2.length + gs.length := by
  induction gs with
  | nil => intro acc _ _ _ h; obtain ⟨g, hg, _⟩ := h; simp at hg
  | cons g gs ih =>
    intro acc hok hk hc hex
    rw [elim_cons, List.length_cons]
    by_cases hkg : k ∈ g.inputs
    · obtain ⟨c, hc⟩ := hc
      have hnok := hok g List.mem_cons_self
      have hnone : (simplify g.op (n + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1 = none := by
        apply simplify_count
        · exact hnok.1.1
        · simpa using hnok.1.2
        · intro h; simpa using hnok.2 h
        · exact ⟨c, List.mem_map.2 ⟨k, hkg, hc⟩⟩
      have h2 : (elimStep n acc g).2.length = acc.2.length := by
        show (acc.2 ++ (simplify g.op (n + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1.toList).length = _
        rw [hnone]; simp
      have := elim_len n gs (elimStep n acc g)
      omega
    · have hex' : ∃ g' ∈ gs, k ∈ g'.inputs := by
        obtain ⟨g', hg', hk'⟩ := hex
        rcases List.mem_cons.1 hg' with rfl | h
        · exact absurd hk' hkg
        · exact ⟨g', h, hk'⟩
      have h1 := ih (elimStep n acc g) (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
        (by simp [elimStep]; omega)
        (by
          obtain ⟨c, hc⟩ := hc
          refine ⟨c, ?_⟩
          simp only [elimStep]
          rw [getD_snoc_ne _ _ _ _ (by omega)]; exact hc)
        hex'
      have h2 : (elimStep n acc g).2.length ≤ acc.2.length + 1 := by
        simp only [elimStep, List.length_append]
        have := toList_length_le (simplify g.op (n + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1
        omega
      omega

theorem statValid_mono {m m' : ℕ} (h : m ≤ m') : ∀ s : Stat, statValid m s → statValid m' s
  | Sum.inl _, _ => trivial
  | Sum.inr _, hj => lt_of_lt_of_le hj h

theorem statVal_append (w t : List Bool) : ∀ s : Stat, statValid w.length s →
    statVal (w ++ t) s = statVal w s
  | Sum.inl _, _ => rfl
  | Sum.inr _, hj => List.getD_append _ _ _ _ hj

def Inv (n : ℕ) (y : List Bool) (w : List Bool) (acc : List Stat × List Gate) : Prop :=
  acc.1.length = w.length ∧ ∀ i : ℕ,
    statValid (n + acc.2.length) (acc.1.getD i (Sum.inl false)) ∧
    statVal (wiresFrom acc.2 y) (acc.1.getD i (Sum.inl false)) = w.getD i false

theorem inv_elim (n : ℕ) (y : List Bool) (hy : y.length = n) (gs : List Gate) :
    ∀ (w : List Bool) (acc : List Stat × List Gate), (∀ g ∈ gs, Ok g) → Inv n y w acc →
      Inv n y (wiresFrom gs w) (elim n gs acc) := by
  induction gs with
  | nil => intro w acc _ h; exact h
  | cons g gs ih =>
    intro w acc hok h
    apply ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) (elimStep n acc g)
      (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
    obtain ⟨hl, hi⟩ := h
    set w' := wiresFrom acc.2 y with hw'
    have lw' : w'.length = n + acc.2.length := by rw [hw', length_wiresFrom, hy]
    set ins := g.inputs.map fun i => acc.1.getD i (Sum.inl false) with hins
    have hgok := hok g List.mem_cons_self
    have hs := simplify_sound g.op hgok.1 w' ins (by simpa [hins] using hgok.2)
      (by
        intro s hs
        obtain ⟨a, _, rfl⟩ := List.mem_map.1 hs
        rw [lw']; exact (hi a).1)
    rw [lw'] at hs
    set r := simplify g.op (n + acc.2.length) ins with hr
    have hvals : ins.map (statVal w') = g.inputs.map fun i => w.getD i false := by
      rw [hins, List.map_map]
      apply List.map_congr_left
      intro a _
      exact (hi a).2
    have hnew : wiresFrom (acc.2 ++ r.1.toList) y = wiresFrom r.1.toList w' := by
      rw [wiresFrom_append]
    obtain ⟨t, ht, _⟩ := wiresFrom_prefix r.1.toList w'
    refine ⟨by simp [elimStep, hl], ?_⟩
    intro i
    show statValid (n + (acc.2 ++ r.1.toList).length) ((acc.1 ++ [r.2]).getD i (Sum.inl false)) ∧
      statVal (wiresFrom (acc.2 ++ r.1.toList) y) ((acc.1 ++ [r.2]).getD i (Sum.inl false)) = _
    rw [hnew, List.length_append, ← Nat.add_assoc]
    by_cases hil : i = acc.1.length
    · subst hil
      rw [getD_snoc_eq, hl, getD_snoc_eq]
      exact ⟨hs.1, by rw [hs.2, hvals]⟩
    · rw [getD_snoc_ne _ _ _ _ hil, getD_snoc_ne _ _ _ _ (by omega)]
      refine ⟨statValid_mono (by omega) _ (hi i).1, ?_⟩
      rw [ht, statVal_append _ _ _ (by rw [lw']; exact (hi i).1)]
      exact (hi i).2

def initStats (n : ℕ) (b : Bool) : List Stat :=
  List.ofFn (fun i : Fin n => Sum.inr (i : ℕ)) ++ [Sum.inl b]

theorem initStats_last (n : ℕ) (b : Bool) :
    (initStats n b).getD n (Sum.inl false) = Sum.inl b :=
  getD_snoc_len _ _ _ _ (by simp)

theorem inv_init (n : ℕ) (b : Bool) (y : Fin n → Bool) :
    Inv n (List.ofFn y) (List.ofFn y ++ [b]) (initStats n b, []) := by
  refine ⟨by simp [initStats], ?_⟩
  intro i
  have l1 : (List.ofFn (fun i : Fin n => (Sum.inr (i : ℕ) : Stat))).length = n := by simp
  have l2 : (List.ofFn y).length = n := by simp
  by_cases hin : i = n
  · subst hin
    simp only [initStats]
    rw [getD_snoc_len _ _ _ _ l1, getD_snoc_len _ _ _ _ l2]
    exact ⟨trivial, rfl⟩
  · simp only [initStats]
    rw [getD_snoc_ne _ _ _ _ (by omega), getD_snoc_ne _ _ _ _ (by omega)]
    by_cases hlt : i < n
    · simp [hlt, statValid, statVal, wiresFrom]
    · rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by omega)]
      exact ⟨trivial, rfl⟩

theorem ofFn_snoc (n : ℕ) (y : Fin n → Bool) (b : Bool) :
    List.ofFn (Fin.snoc y b : Fin (n + 1) → Bool) = List.ofFn y ++ [b] := by
  rw [List.ofFn_succ']
  simp

theorem supp_noread (n : ℕ) (gs : List Gate) : ∀ L : List (Finset (Fin (n + 1))),
    (∀ g ∈ gs, n ∉ g.inputs) → (∀ j : ℕ, j ≠ n → Fin.last n ∉ L.getD j ∅) →
    ∀ j : ℕ, j ≠ n → Fin.last n ∉ (suppsFrom gs L).getD j ∅ := by
  induction gs with
  | nil => intro L _ h; exact h
  | cons g gs ih =>
    intro L hno h
    apply ih (L ++ [gateSupp L g]) (fun g' hg' => hno g' (List.mem_cons_of_mem _ hg'))
    intro j hj
    by_cases hjl : j = L.length
    · subst hjl
      rw [getD_snoc_eq]
      intro hmem
      obtain ⟨a, ha, hia⟩ := (mem_gateSupp L g _).1 hmem
      exact h a (fun e => hno g List.mem_cons_self (e ▸ ha)) hia
    · rw [getD_snoc_ne _ _ _ _ hjl]; exact h j hj

theorem inputSupps_getD (m j : ℕ) (h : j < m) :
    (inputSupps m).getD j ∅ = {⟨j, h⟩} := by
  simp [inputSupps, h]

theorem inputSupps_noread (n : ℕ) : ∀ j : ℕ, j ≠ n →
    Fin.last n ∉ (inputSupps (n + 1)).getD j ∅ := by
  intro j hj
  by_cases hlt : j < n + 1
  · have e : (inputSupps (n + 1)).getD j ∅ = {⟨j, hlt⟩} := inputSupps_getD (n + 1) j hlt
    rw [e, Finset.mem_singleton]
    intro e'
    exact hj (by have := congrArg Fin.val e'; simpa using this.symm)
  · rw [List.getD_eq_default _ _ (by simp [inputSupps]; omega)]; simp

theorem simplify_const (op : GateOp) (m : ℕ) (ins : List Stat)
    (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not) (hlen : ins.length ≤ 2)
    (hnot : op = GateOp.not → ins.length ≤ 1) (b : Bool)
    (hand : op = GateOp.and → b = false) (hor : op = GateOp.or → b = true)
    (hc : Sum.inl b ∈ ins) : ∃ c, (simplify op m ins).2 = Sum.inl c := by
  rcases hop with rfl | rfl | rfl
  · have := hand rfl
    subst this
    rcases ins with _ | ⟨a, _ | ⟨d, _ | ⟨e, l⟩⟩⟩ <;> (try cases a) <;> (try cases d) <;>
      simp_all [simplify, simpAnd]
  · have := hor rfl
    subst this
    rcases ins with _ | ⟨a, _ | ⟨d, _ | ⟨e, l⟩⟩⟩ <;> (try cases a) <;> (try cases d) <;>
      simp_all [simplify, simpOr]
  · have := hnot rfl
    rcases ins with _ | ⟨a, _ | ⟨d, l⟩⟩ <;> (try cases a) <;> simp_all [simplify, simpNot]

theorem elimStep_none (n : ℕ) (acc : List Stat × List Gate) (g : Gate) (hg : NOk g) (k : ℕ)
    (hk : k ∈ g.inputs) (c : Bool) (hc : acc.1.getD k (Sum.inl false) = Sum.inl c) :
    (elimStep n acc g).2.length = acc.2.length := by
  have hnone : (simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1 = none := by
    apply simplify_count
    · exact hg.1.1
    · simpa using hg.1.2
    · intro h; simpa using hg.2 h
    · exact ⟨c, List.mem_map.2 ⟨k, hk, hc⟩⟩
  show (acc.2 ++ (simplify g.op (n + acc.2.length)
    (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1.toList).length = _
  rw [hnone]; simp

def fixBit (g : Gate) : Bool :=
  match g.op with
  | GateOp.or => true
  | _ => false

theorem elimStep_const (n : ℕ) (acc : List Stat × List Gate) (g : Gate) (hg : NOk g) (k : ℕ)
    (hk : k ∈ g.inputs) (hc : acc.1.getD k (Sum.inl false) = Sum.inl (fixBit g)) :
    ∃ c, (elimStep n acc g).1.getD acc.1.length (Sum.inl false) = Sum.inl c := by
  have e : (elimStep n acc g).1.getD acc.1.length (Sum.inl false)
      = (simplify g.op (n + acc.2.length)
        (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).2 := getD_snoc_eq _ _ _
  rw [e]
  apply simplify_const _ _ _ hg.1.1 (by simpa using hg.1.2) (fun h => by simpa using hg.2 h)
    (fixBit g)
  · intro h; simp [fixBit, h]
  · intro h; simp [fixBit, h]
  · exact List.mem_map.2 ⟨k, hk, hc⟩

theorem suppsFrom_append {n : ℕ} (pre post : List Gate) (L : List (Finset (Fin n))) :
    suppsFrom (pre ++ post) L = suppsFrom post (suppsFrom pre L) := by
  simp [suppsFrom, List.foldl_append]

theorem length_suppsFrom {n : ℕ} (gs : List Gate) : ∀ L : List (Finset (Fin n)),
    (suppsFrom gs L).length = L.length + gs.length := by
  induction gs with
  | nil => intro L; rfl
  | cons g gs ih =>
    intro L
    have h : suppsFrom (g :: gs) L = suppsFrom gs (L ++ [gateSupp L g]) := rfl
    rw [h, ih]
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega

theorem supp_noreadD (n : ℕ) (D : ℕ → Prop) (gs : List Gate) :
    ∀ L : List (Finset (Fin (n + 1))),
    (∀ g ∈ gs, ∀ a ∈ g.inputs, ¬ D a) → (∀ j : ℕ, ¬ D j → Fin.last n ∉ L.getD j ∅) →
    ∀ j : ℕ, ¬ D j → Fin.last n ∉ (suppsFrom gs L).getD j ∅ := by
  induction gs with
  | nil => intro L _ h; exact h
  | cons g gs ih =>
    intro L hno h
    apply ih (L ++ [gateSupp L g]) (fun g' hg' => hno g' (List.mem_cons_of_mem _ hg'))
    intro j hj
    by_cases hjl : j = L.length
    · subst hjl
      rw [getD_snoc_eq]
      intro hmem
      obtain ⟨a, ha, hia⟩ := (mem_gateSupp L g _).1 hmem
      exact h a (hno g List.mem_cons_self a ha) hia
    · rw [getD_snoc_ne _ _ _ _ hjl]; exact h j hj

def wmap (n m : ℕ) (π : Fin n → Fin m) (w : ℕ) : ℕ :=
  if h : w < n then (π ⟨w, h⟩ : ℕ) else w - n + m

def relGate (n m : ℕ) (π : Fin n → Fin m) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map (wmap n m π)⟩

def relabel (n m : ℕ) (π : Fin n → Fin m) (C : Circuit) : Circuit :=
  ⟨C.gates.map (relGate n m π), wmap n m π C.output⟩

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def Rel (n m : ℕ) (π : Fin n → Fin m) (W W' : List Bool) : Prop :=
  n ≤ W.length ∧ W'.length + n = W.length + m ∧
    ∀ w : ℕ, W'.getD (wmap n m π w) false = W.getD w false

theorem rel_step (n m : ℕ) (π : Fin n → Fin m) (W W' : List Bool) (g : Gate)
    (h : Rel n m π W W') : Rel n m π (step W g) (step W' (relGate n m π g)) := by
  obtain ⟨h1, h2, h3⟩ := h
  have hv : (relGate n m π g).op.eval
      ((relGate n m π g).inputs.map fun i => W'.getD i false)
      = g.op.eval (g.inputs.map fun i => W.getD i false) := by
    simp only [relGate, List.map_map]
    congr 1
    apply List.map_congr_left
    intro a _
    exact h3 a
  refine ⟨by simp [step]; omega, by simp [step]; omega, ?_⟩
  intro w
  simp only [step, hv]
  rcases Nat.lt_trichotomy w W.length with hw | hw | hw
  · have hlt : wmap n m π w < W'.length := by
      unfold wmap
      split
      · have := (π ⟨w, by assumption⟩).2; omega
      · omega
    rw [List.getD_append _ _ _ _ hlt, List.getD_append _ _ _ _ hw]
    exact h3 w
  · have he : wmap n m π w = W'.length := by
      unfold wmap
      split
      · omega
      · omega
    rw [he, hw, getD_snoc_eq, getD_snoc_eq]
  · have hge : W'.length + 1 ≤ wmap n m π w := by
      unfold wmap
      split
      · omega
      · omega
    rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]

theorem rel_fold (n m : ℕ) (π : Fin n → Fin m) (gs : List Gate) :
    ∀ W W' : List Bool, Rel n m π W W' →
      Rel n m π (gs.foldl step W) ((gs.map (relGate n m π)).foldl step W') := by
  induction gs with
  | nil => intro W W' h; exact h
  | cons g gs ih =>
    intro W W' h
    exact ih _ _ (rel_step n m π W W' g h)

theorem rel_init (n m : ℕ) (π : Fin n → Fin m) (x : Fin m → Bool) :
    Rel n m π (List.ofFn (x ∘ π)) (List.ofFn x) := by
  refine ⟨by simp, by simp; omega, ?_⟩
  intro w
  unfold wmap
  split
  · rename_i hw
    rw [List.getD_eq_getElem _ _ (by simp), List.getD_eq_getElem _ _ (by simpa using hw)]
    simp
  · rename_i hw
    rw [List.getD_eq_default _ _ (by simp), List.getD_eq_default _ _ (by simp; omega)]

def edge : (Fin 9 → Bool) → Bool := fun x : Fin 9 → Bool => (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 5) || (x 2 && x 6) || (x 3 && x 6) || (x 0 && x 7) || (x 2 && x 7) || (x 4 && x 7) || (x 1 && x 8) || (x 3 && x 8) || (x 4 && x 8) || (x 6 && x 8)

def TightOr (n : ℕ) (gs : List Gate) : Prop :=
  ∃ (pre : List Gate) (g : Gate) (post : List Gate),
    gs = pre ++ g :: post ∧ n ∈ g.inputs ∧ g.op = .or ∧
    (¬ ∃ g' ∈ pre, n ∈ g'.inputs) ∧ (¬ ∃ g' ∈ post, n ∈ g'.inputs) ∧
    (∀ c : Bool, (elimStep n (elim n pre (initStats n false, [])) g).1.getD
      (n + 1 + pre.length) (Sum.inl false) ≠ Sum.inl c)

theorem two_saved_or_tight (n : ℕ) (gs : List Gate) (hnok : ∀ g ∈ gs, NOk g) (o : ℕ)
    (hdep : Fin.last n ∈ (suppsFrom gs (inputSupps (n + 1))).getD o ∅)
    (hout : ∀ b c, (elim n gs (initStats n b, [])).1.getD o (Sum.inl false) ≠ Sum.inl c) :
    (elim n gs (initStats n false, [])).2.length + 2 ≤ gs.length ∨ TightOr n gs := by
  have hon : o ≠ n := by
    intro e
    apply hout false false
    rw [e, elim_getD n n _ gs _ (by simp [initStats])]
    exact initStats_last n false
  by_cases hread : ∃ g ∈ gs, n ∈ g.inputs
  swap
  · exfalso
    push Not at hread
    exact supp_noread n gs (inputSupps (n + 1)) hread (inputSupps_noread n) o hon hdep
  obtain ⟨g, hg, hng⟩ := hread
  obtain ⟨pre, post, rfl⟩ := List.append_of_mem hg
  have hgn : NOk g := hnok g hg
  have hpren : ∀ g' ∈ pre, NOk g' := fun g' h => hnok g' (List.mem_append_left _ h)
  have hpostn : ∀ g' ∈ post, NOk g' :=
    fun g' h => hnok g' (List.mem_append_right _ (List.mem_cons_of_mem _ h))
  have hsplit : ∀ b, elim n (pre ++ g :: post) (initStats n b, [])
      = elim n post (elimStep n (elim n pre (initStats n b, [])) g) :=
    fun b => by rw [elim_append, elim_cons]
  have hAn : ∀ b, (elim n pre (initStats n b, [])).1.getD n (Sum.inl false) = Sum.inl b := by
    intro b
    rw [elim_getD n n _ pre _ (by simp [initStats])]
    exact initStats_last n b
  have hAl : ∀ b, (elim n pre (initStats n b, [])).1.length = n + 1 + pre.length := by
    intro b
    rw [elim_fst_len]
    simp [initStats]
  have hA2 : ∀ b, (elim n pre (initStats n b, [])).2.length ≤ 0 + pre.length :=
    fun b => elim_len n pre (initStats n b, [])
  have hB2 := fun b => elimStep_none n (elim n pre (initStats n b, [])) g hgn n hng b (hAn b)
  have hBl : ∀ b, (elimStep n (elim n pre (initStats n b, [])) g).1.length
      = n + 1 + pre.length + 1 := by
    intro b
    simp [elimStep, hAl b]
  have hBn : ∀ b, (elimStep n (elim n pre (initStats n b, [])) g).1.getD n (Sum.inl false)
      = Sum.inl b := by
    intro b
    show ((elim n pre (initStats n b, [])).1 ++ [_]).getD n _ = _
    rw [getD_snoc_ne _ _ _ _ (by rw [hAl b]; omega)]
    exact hAn b
  have hF := fun b => elim_len n post (elimStep n (elim n pre (initStats n b, [])) g)
  have hlen : (pre ++ g :: post).length = pre.length + post.length + 1 := by
    simp only [List.length_append, List.length_cons]; omega
  by_cases h1 : ∃ g' ∈ pre, n ∈ g'.inputs
  · left
    have a1 : (elim n pre (initStats n false, [])).2.length + 1 ≤ 0 + pre.length :=
      elim_len_lt n n pre (initStats n false, []) hpren (by simp [initStats])
        ⟨false, initStats_last n false⟩ h1
    have := hF false
    have := hB2 false
    rw [hsplit, hlen]
    omega
  by_cases h2 : ∃ g' ∈ post, n ∈ g'.inputs
  · left
    have a1 := elim_len_lt n n post (elimStep n (elim n pre (initStats n false, [])) g) hpostn
      (by rw [hBl]; omega) ⟨false, hBn false⟩ h2
    have := hA2 false
    have := hB2 false
    rw [hsplit, hlen]
    omega
  by_cases hc0 : ∃ c : Bool, (elimStep n (elim n pre (initStats n false, [])) g).1.getD
      (n + 1 + pre.length) (Sum.inl false) = Sum.inl c
  swap
  · push Not at hc0
    have hor : g.op = .or := by
      by_contra hn
      have hz : fixBit g = false := by cases he : g.op <;> simp_all [fixBit]
      obtain ⟨c, hc⟩ := elimStep_const n (elim n pre (initStats n (fixBit g), [])) g hgn n hng
        (hAn (fixBit g))
      rw [hAl (fixBit g), hz] at hc
      exact hc0 c hc
    exact Or.inr ⟨pre, g, post, rfl, hng, hor, h1, h2, hc0⟩
  obtain ⟨c, hc⟩ := hc0
  left
  by_cases h3 : ∃ g' ∈ post, (n + 1 + pre.length) ∈ g'.inputs
  · have a1 := elim_len_lt n (n + 1 + pre.length) post
      (elimStep n (elim n pre (initStats n false, [])) g) hpostn
      (by rw [hBl]; omega) ⟨c, hc⟩ h3
    have := hA2 false
    have := hB2 false
    rw [hsplit, hlen]
    omega
  · exfalso
    have hom : o ≠ n + 1 + pre.length := by
      intro e
      apply hout false c
      rw [hsplit, e, elim_getD n _ _ post _ (by rw [hBl]; omega)]
      exact hc
    push Not at h1 h2 h3
    have hs : suppsFrom (pre ++ g :: post) (inputSupps (n + 1))
        = suppsFrom post (suppsFrom pre (inputSupps (n + 1))
          ++ [gateSupp (suppsFrom pre (inputSupps (n + 1))) g]) := by
      rw [suppsFrom_append]; rfl
    rw [hs] at hdep
    have hL := supp_noread n pre (inputSupps (n + 1)) h1 (inputSupps_noread n)
    have hLl : (suppsFrom pre (inputSupps (n + 1))).length = n + 1 + pre.length := by
      rw [length_suppsFrom]
      simp [inputSupps]
    refine supp_noreadD n (fun j => j = n ∨ j = n + 1 + pre.length) post _ ?_ ?_ o
      (by simp [hon, hom]) hdep
    · intro g' hg' a ha hD
      rcases hD with rfl | rfl
      · exact h2 g' hg' ha
      · exact h3 g' hg' ha
    · intro j hj
      have hj' : j ≠ n ∧ j ≠ n + 1 + pre.length := by
        constructor
        · exact fun e => hj (Or.inl e)
        · exact fun e => hj (Or.inr e)
      rw [getD_snoc_ne _ _ _ _ (by rw [hLl]; exact hj'.2)]
      exact hL j hj'.1

theorem strict_or_of_tight (n : ℕ) (f : (Fin (n+1) → Bool) → Bool)
    (C : Circuit) (ok : FanInTwo C)
    (hev : ∀ x, C.eval (List.ofFn x) = f x)
    (hdep : ∃ x, f (Function.update x (Fin.last n) (!x (Fin.last n))) ≠ f x)
    (hnc : ∀ b, ∃ y y' : Fin n → Bool, f (Fin.snoc y b) ≠ f (Fin.snoc y' b))
    (hbound : ∀ t, HasCircuitSize n (fun y => f (Fin.snoc y false)) t → C.size < t + 2) :
    TightOr n (C.gates.map normGate) := by
  set gs := C.gates.map normGate with hgs
  have hl : gs.length = C.gates.length := by simp [hgs]
  have hnok : ∀ g ∈ gs, NOk g := by
    intro g hg
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 hg
    exact normGate_nok g0 (ok g0 hg0)
  have hevg : ∀ x : Fin (n + 1) → Bool, (wiresFrom gs (List.ofFn x)).getD C.output false = f x := by
    intro x
    rw [hgs, wiresFrom_norm, ← hev x]; rfl
  have hinv : ∀ (b : Bool) (y : Fin n → Bool),
      Inv n (List.ofFn y) (wiresFrom gs (List.ofFn (Fin.snoc y b : Fin (n + 1) → Bool)))
        (elim n gs (initStats n b, [])) := by
    intro b y
    rw [ofFn_snoc]
    exact inv_elim n _ (by simp) gs _ _ (fun g hg => (hnok g hg).1) (inv_init n b y)
  have hval : ∀ (b : Bool) (y : Fin n → Bool),
      statVal (wiresFrom (elim n gs (initStats n b, [])).2 (List.ofFn y))
        ((elim n gs (initStats n b, [])).1.getD C.output (Sum.inl false)) = f (Fin.snoc y b) := by
    intro b y
    rw [((hinv b y).2 C.output).2, hevg]
  have hout : ∀ b c,
      (elim n gs (initStats n b, [])).1.getD C.output (Sum.inl false) ≠ Sum.inl c := by
    intro b c hst
    obtain ⟨y, y', hne⟩ := hnc b
    apply hne
    rw [← hval b y, ← hval b y', hst]; rfl
  have hsupp : Fin.last n ∈ (suppsFrom gs (inputSupps (n + 1))).getD C.output ∅ := by
    by_contra hns
    obtain ⟨x, hx⟩ := hdep
    apply hx
    have hag := (agree_wiresFrom (Function.update x (Fin.last n) (!x (Fin.last n))) x gs _ _ _
      (agree_inputs _ _)).2.2 C.output (by
        intro k hk
        have : k ≠ Fin.last n := fun e => hns (e ▸ hk)
        simp [Function.update_of_ne this])
    rw [← hevg, ← hevg]
    exact hag
  rcases two_saved_or_tight n gs hnok C.output hsupp hout with hs | hdone
  · cases hst : (elim n gs (initStats n false, [])).1.getD C.output (Sum.inl false) with
    | inl c => exact absurd hst (hout false c)
    | inr j =>
      have ht := hbound (elim n gs (initStats n false, [])).2.length
        ⟨⟨(elim n gs (initStats n false, [])).2, j⟩, elim_ok n gs _ (by simp), le_refl _,
          fun y => by
            have hv := hval false y
            rw [hst] at hv
            exact hv⟩
      change C.gates.length < _ at ht
      omega
  · exact hdone

def Away (k : ℕ) (w v : List Bool) :=
  w.length = v.length ∧ ∀ i, i ≠ k → w.getD i false = v.getD i false

theorem away_append (k : ℕ) (w v : List Bool) (h : Away k w v) (a : Bool) :
    Away k (w ++ [a]) (v ++ [a]) := by
  obtain ⟨hl, hv⟩ := h
  refine ⟨by simp [hl], ?_⟩
  intro i hi
  by_cases he : i = w.length
  · rw [getD_snoc_len _ _ _ _ he.symm, getD_snoc_len _ _ _ _ (hl.symm.trans he.symm)]
  · rw [getD_snoc_ne _ _ _ _ he, getD_snoc_ne _ _ _ _ (by simpa [← hl] using he)]
    exact hv i hi

theorem away_inputs (n : ℕ) (y : Fin n → Bool) (a b : Bool) :
    Away n (List.ofFn (Fin.snoc y a : Fin (n+1) → Bool)) (List.ofFn (Fin.snoc y b)) := by
  rw [ofFn_snoc, ofFn_snoc]
  refine ⟨by simp, ?_⟩
  intro j hj
  rw [getD_snoc_ne _ _ _ _ (by simpa using hj), getD_snoc_ne _ _ _ _ (by simpa using hj)]

theorem away_no_read (k : ℕ) (gs : List Gate) (hno : ¬ ∃ g ∈ gs, k ∈ g.inputs) :
    ∀ (w v : List Bool), Away k w v → Away k (wiresFrom gs w) (wiresFrom gs v) := by
  induction gs with
  | nil => exact fun _ _ h => h
  | cons g gs ih =>
    intro w v h
    have het : g.inputs.map (fun i => w.getD i false) = g.inputs.map (fun i => v.getD i false) := by
      apply List.map_congr_left
      intro i hi
      exact h.2 i (fun he => hno ⟨g, List.mem_cons_self, he ▸ hi⟩)
    apply ih (fun he => by
      obtain ⟨j, hj, hin⟩ := he
      exact hno ⟨j, List.mem_cons_of_mem _ hj, hin⟩)
    dsimp only
    rw [het]
    exact away_append k w v h _

theorem or_high (g : Gate) (hor : g.op = .or) (j : ℕ) (hj : j ∈ g.inputs)
    (w : List Bool) (hw : w.getD j false = true) :
    g.op.eval (g.inputs.map fun i => w.getD i false) = true := by
  rw [hor]
  change (g.inputs.map fun i => w.getD i false).any id = true
  apply List.any_eq_true.2
  exact ⟨true, List.mem_map.2 ⟨j,hj,hw⟩, rfl⟩

theorem shield_raw (n : ℕ) (pre post : List Gate) (g : Gate) (o : ℕ)
    (hpre : ¬ ∃ h ∈ pre, n ∈ h.inputs) (hpost : ¬ ∃ h ∈ post, n ∈ h.inputs)
    (hg : g.op = .or) (ho : o ≠ n) (j : Fin n) (hread : j.val ∈ g.inputs)
    (y : Fin n → Bool) (hy : y j = true) :
    (wiresFrom (pre ++ g :: post) (List.ofFn (Fin.snoc y false))).getD o false =
    (wiresFrom (pre ++ g :: post) (List.ofFn (Fin.snoc y true))).getD o false := by
  let w := fun b : Bool => wiresFrom pre (List.ofFn (Fin.snoc y b : Fin (n+1) → Bool))
  have high (b : Bool) : (w b).getD j.val false = true := by
    dsimp [w]
    rw [getD_wiresFrom _ _ _ (by simp <;> omega), ofFn_snoc, List.getD_append _ _ _ _ (by simp)]
    simpa using hy
  have hv (b : Bool) := or_high g hg j.val hread (w b) (high b)
  have h := away_no_read n pre hpre _ _ (away_inputs n y false true)
  have hall := away_no_read n post hpost _ _ (away_append n _ _ h true)
  rw [wiresFrom_append, wiresFrom_append]
  change (wiresFrom post (w false ++ [g.op.eval (g.inputs.map fun i => (w false).getD i false)])).getD o false =
    (wiresFrom post (w true ++ [g.op.eval (g.inputs.map fun i => (w true).getD i false)])).getD o false
  rw [hv false, hv true]
  exact hall.2 o ho

def baseEight (x : Fin 8 → Bool) :=
  (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 3 && x 5) || (x 3 && x 6) || (x 4 && x 7) || (x 5 && x 6) || (x 5 && x 7)

def ordered (x : Fin 9 → Bool) :=
  baseEight (fun j => x j.castSucc) || (x 8 && x 2) || (x 8 && x 6)

def orderNine : Fin 9 → Fin 9 := ![5, 4, 8, 1, 3, 7, 2, 6, 0]

theorem ordered_false (y : Fin 8 → Bool) : ordered (Fin.snoc y false) = baseEight y := by
  have h8 : (Fin.snoc y false : Fin 9 → Bool) 8 = false := by rfl
  simp [ordered, h8, Fin.snoc_castSucc]

theorem two_inputs_of_live_or {n : ℕ} (pre : List Gate) (g : Gate) (hg : NOk g)
    (hin : n ∈ g.inputs) (hor : g.op = .or)
    (hlive : ∀ c : Bool, (elimStep n (elim n pre (initStats n false, [])) g).1.getD
      (n+1+pre.length) (Sum.inl false) ≠ Sum.inl c) :
    ∃ j, j ≠ n ∧ j < n + 1 + pre.length ∧ (g.inputs = [n,j] ∨ g.inputs = [j,n]) := by
  let acc := elim n pre (initStats n false, [])
  have hl : acc.1.length = n + 1 + pre.length := by
    dsimp [acc]
    rw [elim_fst_len]
    simp [initStats]
  have hn : acc.1.getD n (Sum.inl false) = Sum.inl false := by
    dsimp [acc]
    rw [elim_getD n n _ pre _ (by simp [initStats])]
    exact initStats_last n false
  have hnoconst (c : Bool) : (simpOr (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).2 ≠ Sum.inl c := by
    have hh := hlive c
    change (acc.1 ++ [(simplify g.op _ _).2]).getD _ _ ≠ Sum.inl c at hh
    rw [getD_snoc_len _ _ _ _ hl, hor] at hh
    exact hh
  have le := hg.1.2
  rcases hs : g.inputs with _ | ⟨a, _ | ⟨b, _ | ⟨d, t⟩⟩⟩
  · simp [hs] at hin
  · have ha : n = a := by simpa [hs] using hin
    subst a
    exact False.elim (hnoconst false (by simp only [hs,List.map_cons,List.map_nil,hn]; rfl))
  · have hab : n = a ∨ n = b := by simpa [hs] using hin
    rcases hab with rfl | rfl
    · refine ⟨b, ?_, ?_, Or.inl rfl⟩
      · intro h
        subst b
        exact hnoconst false (by simp only [hs,List.map_cons,List.map_nil,hn]; rfl)
      · by_contra! hb
        have ez := List.getD_eq_default acc.1 (Sum.inl false) (by omega : acc.1.length ≤ b)
        exact hnoconst false (by simp only [hs,List.map_cons,List.map_nil,hn,ez]; rfl)
    · refine ⟨a, ?_, ?_, Or.inr rfl⟩
      · intro h
        subst a
        exact hnoconst false (by simp only [hs,List.map_cons,List.map_nil,hn]; rfl)
      · by_contra! ha
        have ez := List.getD_eq_default acc.1 (Sum.inl false) (by omega : acc.1.length ≤ a)
        exact hnoconst false (by simp only [hs,List.map_cons,List.map_nil,hn,ez]; rfl)
  · simp [hs] at le

set_option maxHeartbeats 2500000 in
theorem sensitive_with_input : ∀ j : Fin 8, ∃ y : Fin 8 → Bool,
    y j = true ∧ ordered (Fin.snoc y false) ≠ ordered (Fin.snoc y true) := by decide +kernel

theorem ordered_has_derived (eight : ∀ t, HasCircuitSize 8 baseEight t → 14 ≤ t)
    (C : Circuit) (ok : FanInTwo C) (sz : C.size ≤ 15) (hev : ∀ x, C.eval (List.ofFn x) = ordered x) :
    ∃ (pre : List Gate) (g : Gate) (post : List Gate) (j : ℕ),
      C.gates.map normGate = pre ++ g :: post ∧ g.op = .or ∧
      9 ≤ j ∧ j < 9 + pre.length ∧ (g.inputs = [8,j] ∨ g.inputs = [j,8]) ∧
      (¬ ∃ q ∈ pre, 8 ∈ q.inputs) ∧ (¬ ∃ q ∈ post, 8 ∈ q.inputs) := by
  have ht : TightOr 8 (C.gates.map normGate) := by
    apply strict_or_of_tight 8 ordered C ok hev
    · exact ⟨fun i => decide (i = 2), by decide⟩
    · intro b
      refine ⟨fun i => decide (i = 0 ∨ i = 1), fun _ => false, ?_⟩
      cases b <;> decide
    · intro t h
      have hfun : (fun y => ordered (Fin.snoc y false)) = baseEight := funext ordered_false
      rw [hfun] at h
      have := eight t h
      omega
  obtain ⟨pre, g, post, he, h8, ho, hp, hq, hlive⟩ := ht
  have hgmem : g ∈ C.gates.map normGate := by simp [he]
  obtain ⟨g0, hg0, he0⟩ := List.mem_map.1 hgmem
  have hg : NOk g := he0 ▸ normGate_nok g0 (ok g0 hg0)
  obtain ⟨j, hj, hlen, hh⟩ := two_inputs_of_live_or pre g hg h8 ho hlive
  refine ⟨pre, g, post, j, he, ho, ?_, hlen, hh, hp, hq⟩
  by_contra! hj'
  let i : Fin 8 := ⟨j, by omega⟩
  obtain ⟨y, hy, diff⟩ := sensitive_with_input i
  have hread : i.val ∈ g.inputs := by rcases hh with h | h <;> simp [h,i]
  have outne : C.output ≠ 8 := by
    intro eq
    let x : Fin 9 → Bool := fun v => decide (v = 0 ∨ v = 1)
    have hs := hev x
    change (wiresFrom C.gates (List.ofFn x)).getD C.output false = ordered x at hs
    rw [eq, getD_wiresFrom _ _ _ (by simp)] at hs
    exact (by decide : (List.ofFn x).getD 8 false ≠ ordered x) hs
  have hsame := shield_raw 8 pre post g C.output hp hq ho outne i hread y hy
  rw [← he, wiresFrom_norm, wiresFrom_norm] at hsame
  exact diff ((hev _).symm.trans (hsame.trans (hev _)))

end PEqualNP.Outside.L_meta_17271_aux

namespace PEqualNP.Outside.L_meta_17271_aux
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def sample (common special : Bool) : Fin 9 → Bool :=
  (Fin.snoc (fun _ : Fin 8 => common) special : Fin 9 → Bool) ∘ orderNine

theorem first_irrelevant (C : Circuit) (legal : FanInTwo C) (small : C.size ≤ 15)
    (correct : circuitFun 9 C = edge) (b : Bool) :
    (C.wires (List.ofFn (sample b false))).getD 9 false =
      (C.wires (List.ofFn (sample b true))).getD 9 false := by
  let D := relabel 9 9 orderNine C
  have dl : FanInTwo D := by
    intro g hg
    obtain ⟨h, hh, rfl⟩ := List.mem_map.1 hg
    exact ⟨(legal h hh).1, by simpa [relGate] using (legal h hh).2⟩
  have ds : D.size ≤ 15 := by simpa [D, relabel, Circuit.size] using small
  have rel (x : Fin 9 → Bool) (i : ℕ) :=
    (rel_fold 9 9 orderNine C.gates _ _ (rel_init 9 9 orderNine x)).2.2 i
  have de (x : Fin 9 → Bool) : D.eval (List.ofFn x) = ordered x := by
    change _ = _
    calc
      _ = C.eval (List.ofFn (x ∘ orderNine)) := rel x C.output
      _ = edge (x ∘ orderNine) := congrFun correct _
      _ = ordered x := (by decide +kernel : ∀ t : Fin 9 → Bool, edge (t ∘ orderNine) = ordered t) x
  obtain ⟨pre, g, post, j, eq, _, hj, bound, _, noPre, _⟩ :=
    ordered_has_derived PEqualNP.Outside.L_meta_17271_aux.Pin.Bound D dl ds de
  have pos : 0 < pre.length := by omega
  let input (c : Bool) : Fin 9 → Bool := Fin.snoc (fun _ : Fin 8 => b) c
  have samePrefix (c : Bool) :
      (D.wires (List.ofFn (input c))).getD 9 false =
        (wiresFrom pre (List.ofFn (input c))).getD 9 false := by
    change (wiresFrom D.gates _).getD _ _ = _
    rw [← wiresFrom_norm D.gates, eq, wiresFrom_append, getD_wiresFrom]
    rw [length_wiresFrom, List.length_ofFn]
    omega
  have equalOrdered :=
    (away_no_read 8 pre noPre _ _ (away_inputs 8 (fun _ => b) false true)).2 9 (by decide)
  have transfer (c : Bool) :
      (D.wires (List.ofFn (input c))).getD 9 false =
        (C.wires (List.ofFn (sample b c))).getD 9 false := rel (input c) 9
  exact (transfer false).symm.trans ((samePrefix false).trans
    (equalOrdered.trans ((samePrefix true).symm.trans (transfer true))))

end PEqualNP.Outside.L_meta_17271_aux

open PEqualNP.Outside.L_meta_17271_aux PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity in
theorem PEqualNP.Outside.L_meta_17271 : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C → ((∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = !(y 2)) ∨ (∃ j : Fin 9, (2 : Fin 9) < j ∧ ∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 2 && y j)) ∨ (∃ j : Fin 9, (2 : Fin 9) < j ∧ ∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 2 || y j))) → PEqualNP.MetaComplexity.circuitFun 9 C = (fun x : Fin 9 → Bool => (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 5) || (x 2 && x 6) || (x 3 && x 6) || (x 0 && x 7) || (x 2 && x 7) || (x 4 && x 7) || (x 1 && x 8) || (x 3 && x 8) || (x 4 && x 8) || (x 6 && x 8)) → 16 ≤ C.size := by
  intro C legal first correct
  by_contra! hs
  have same := first_irrelevant C legal (by omega) correct
  rcases first with h | ⟨j, hj, h⟩ | ⟨j, hj, h⟩
  · have eq := (h (sample false false)).symm.trans ((same false).trans (h (sample false true)))
    exact (by decide : (!(sample false false 2)) ≠ (!(sample false true 2))) eq
  · have eq := (h (sample true false)).symm.trans ((same true).trans (h (sample true true)))
    exact (by decide +kernel : ∀ k : Fin 9, 2 < k →
      (sample true false 2 && sample true false k) ≠ (sample true true 2 && sample true true k)) j hj eq
  · have eq := (h (sample false false)).symm.trans ((same false).trans (h (sample false true)))
    exact (by decide +kernel : ∀ k : Fin 9, 2 < k →
      (sample false false 2 || sample false false k) ≠ (sample false true 2 || sample false true k)) j hj eq
