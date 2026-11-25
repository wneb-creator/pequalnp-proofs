import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2373.Live1024
open PEqualNP.CircuitLowerBounds
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

def inputs : List Sig := [0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,
  0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc,
  0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,
  0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00,
  0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000,
  0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000,
  0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000,
  0xffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000,
  0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000000000000000000000000000000000000,
  0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000]
def graph : Sig := 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc8fffffffffffffffffffffffffffffffffffffffffffffffffffffaeafffff8c8fffffffffffffffffffffffffffafff8ffffffffffffffffffffffffffeaffc8fffffffffffefcfcfffffffffffaf8f8ffeefeeeffeefcccffeafaeaffeaf8c8
def sample (r : Row) (j : Fin 10) := bit r (inputs.getD j.val zero)
def edge (x : Fin 10 → Bool) : Bool :=
  (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 4 && x 9) || (x 5 && x 7) || (x 7 && x 9) || (x 9 && x 6) || (x 6 && x 8) || (x 8 && x 5)
theorem edge_table : ∀ r : Row, bit r graph = edge (sample r) := by decide +kernel
theorem graph_proper : proper graph := by unfold proper; decide +kernel
theorem input_list : List.ofFn (fun j : Fin 10 => inputs.getD j.val zero) = inputs := rfl
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



def neighbor (i : Fin 10) : Nat := [1,0,1,2,0,0,1,2,3,4].getD i.val 0
def absentRow (i : Fin 10) : Row := Fin.ofNat 1024 (1 <<< neighbor i)
def presentRow (i : Fin 10) : Row := Fin.ofNat 1024 ((1 <<< i.val) ||| (1 <<< neighbor i))

set_option maxHeartbeats 1000000 in
theorem requiredInputs :
    (∀ i : Fin 10, bit (absentRow i) graph ≠ bit (presentRow i) graph) ∧
    (∀ i j : Fin 10, i ≠ j →
      bit (absentRow i) (inputs.getD j.val zero) =
      bit (presentRow i) (inputs.getD j.val zero)) := by decide +kernel


theorem twoRoots (C : Circuit) (legal : PEqualNP.MetaComplexity.FanInTwo C)
    (computes : PEqualNP.MetaComplexity.circuitFun 10 C = edge) (small : C.size ≤ 19) :
    ∃ (u : Bool) (k : Nat), k ≤ (if u then 18 else 19) ∧ Live u graph k inputs.toFinset := by
  have goalEq : (execute C.gates inputs).getD C.output zero = graph := by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    let r : Row := ⟨j,hj⟩
    exact (table_eval C legal C.output r).trans ((congrFun computes (sample r)).trans (edge_table r).symm)
  have len : C.gates.length ≤ 19 := small
  have mode : ∃ u : Bool, (u=false → ∀ g ∈ C.gates, isNot g=false) ∧ C.gates.countP (fun g => !isNot g) ≤ (if u then 18 else 19) := by
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
  have pg : bit 0 graph = false := by decide +kernel
  rw [nrm_id pg] at out
  obtain ⟨k,S,hk,run,sub⟩ := extract C.gates inputs legal mono graph_proper
    (out.resolve_right (fun h => h graph_proper))
  have ns : inputs.all plainWord = true := by decide +kernel
  rw [nrm_map ns] at sub
  have idx (a : Sig) (ha : a ∈ inputs) : ∃ i : Fin 10, inputs.getD i.val zero = a := by
    rw [←input_list] at ha
    exact List.mem_ofFn.mp ha
  have eq : S = inputs.toFinset := by
    ext a
    constructor
    · exact fun h => List.mem_toFinset.mpr (sub a h)
    · intro ha
      obtain ⟨i,rfl⟩ := idx a (List.mem_toFinset.mp ha)
      apply raw_required run inputs (inputs.getD i.val zero) sub (absentRow i) (presentRow i)
        (requiredInputs.1 i)
      intro v hv hn
      obtain ⟨j,rfl⟩ := idx v hv
      apply requiredInputs.2 i j
      rintro rfl
      exact hn rfl
  exact ⟨u,k,hk.trans count,eq ▸ run⟩

theorem directSplit
    (m : ∀ k, k ≤ 19 → ¬Live false graph k inputs.toFinset)
    (s : ∀ k, k ≤ 18 → ¬Live true graph k inputs.toFinset) :
    ¬ PEqualNP.MetaComplexity.HasCircuitSize 10 edge 19 := by
  rintro ⟨C,legal,small,computes⟩
  obtain ⟨mode,k,hk,run⟩ := twoRoots C legal (funext computes) small
  cases mode
  · exact m k hk run
  · exact s k hk run


theorem circuit_live (C : Circuit) (legal : PEqualNP.MetaComplexity.FanInTwo C)
    (computes : PEqualNP.MetaComplexity.circuitFun 10 C = edge) (u : Bool)
    (mono : u = false → ∀ g ∈ C.gates, isNot g = false) :
    ∃ k, k ≤ C.gates.countP (fun g => !isNot g) ∧ Live u graph k inputs.toFinset := by
  have goalEq : (execute C.gates inputs).getD C.output zero = graph := by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    let r : Row := ⟨j, hj⟩
    exact (table_eval C legal C.output r).trans
      ((congrFun computes (sample r)).trans (edge_table r).symm)
  have out := get_rep (u := u) (execute C.gates inputs) C.output
  rw [goalEq] at out
  unfold Repr at out
  have pg : bit 0 graph = false := by decide +kernel
  rw [nrm_id pg] at out
  obtain ⟨k, S, hk, run, sub⟩ := extract C.gates inputs legal mono graph_proper
    (out.resolve_right (fun h => h graph_proper))
  have ns : inputs.all plainWord = true := by decide +kernel
  rw [nrm_map ns] at sub
  have idx (a : Sig) (ha : a ∈ inputs) : ∃ i : Fin 10, inputs.getD i.val zero = a := by
    rw [← input_list] at ha
    exact List.mem_ofFn.mp ha
  have eq : S = inputs.toFinset := by
    ext a
    constructor
    · exact fun h => List.mem_toFinset.mpr (sub a h)
    · intro ha
      obtain ⟨i, rfl⟩ := idx a (List.mem_toFinset.mp ha)
      apply raw_required run inputs (inputs.getD i.val zero) sub (absentRow i) (presentRow i)
        (requiredInputs.1 i)
      intro v hv hn
      obtain ⟨j, rfl⟩ := idx v hv
      apply requiredInputs.2 i j
      rintro rfl
      exact hn rfl
  exact ⟨k, hk, eq ▸ run⟩

theorem circuit_live_signed (C : Circuit) (legal : PEqualNP.MetaComplexity.FanInTwo C)
    (computes : PEqualNP.MetaComplexity.circuitFun 10 C = edge) :
    ∃ k, k ≤ C.gates.countP (fun g => !isNot g) ∧ Live true graph k inputs.toFinset :=
  circuit_live C legal computes true (by simp)

end PEqualNP.Outside.L_meta_2373.Live1024

namespace PEqualNP.Outside.L_meta_2373.Live1024

def LabelPartition {α : Type} [DecidableEq α] (roots : Finset α)
    (S : Finset Sig) (label : Sig → Finset α) : Prop :=
  (∀ v ∈ S, label v ⊆ roots) ∧
  (∀ v ∈ S, ∀ w ∈ S, v ≠ w → Disjoint (label v) (label w)) ∧
  (∀ r ∈ roots, ∃ v ∈ S, r ∈ label v)

def liftLabels {α : Type} [DecidableEq α] (A : Finset α) : Finset (Sum α Bool) :=
  A.image Sum.inl

def duplicateRoots {α : Type} [DecidableEq α] (roots A : Finset α) : Finset (Sum α Bool) :=
  liftLabels (roots \ A) ∪ {Sum.inr false, Sum.inr true}

def duplicateRaw {α : Type} (raw : α → Sig) (w : Sig) : Sum α Bool → Sig :=
  Sum.elim raw (fun _ => w)


theorem kept_append {α : Type} (save : Bool) (a : α) (xs ys : List α) :
    kept save a xs ++ ys = kept save a (xs ++ ys) := by
  cases save <;> rfl

theorem Run.substitute {R : Type} {u : Bool} {goal target : Wire R}
    {k l : Nat} {xs rest : List (Wire R)}
    (trace : Run u goal k xs) (tail : Run u target l (goal :: rest)) :
    Run u target (k + l) (xs ++ rest) := by
  induction k generalizing xs with
  | zero =>
    have perm : [goal].Perm xs := trace
    exact Run.perm (perm.append_right rest) (by simpa using tail)
  | succ k ih =>
    obtain ⟨op, ka, kb, a, b, mid, hd, perm, trace⟩ := trace
    have next := ih trace
    have next' : Run u target (k + l)
        (comb op a b :: kept ka a (kept kb b (mid ++ rest))) := by
      simpa only [List.cons_append, kept_append] using next
    have step := Run.two op hd ka kb next'
    have framed : Run u target (k + 1 + l) ((a :: b :: mid) ++ rest) := by
      simpa only [List.cons_append, Nat.add_right_comm] using step
    exact Run.perm (perm.append_right rest) framed

theorem Run.combine_traces {R : Type} {u : Bool} {a b : Wire R}
    {k l : Nat} {xs ys : List (Wire R)}
    (left : Run u a k xs) (right : Run u b l ys) (d : Nat) (hd : allowed u d) :
    Run u (comb d a b) (k + l + 1) (xs ++ ys) := by
  have finish : Run u (comb d a b) 1 [a, b] :=
    Run.two d hd false false (by simpa [kept] using (Run.stop (goal := comb d a b) (u := u)))
  have swap : ([a, b] : List (Wire R)).Perm [b, a] := List.Perm.swap _ _ _
  have reversed : Run u (comb d a b) 1 [b, a] := Run.perm swap finish
  have first : Run u (comb d a b) (l + 1) (ys ++ [a]) := Run.substitute right reversed
  have second : Run u (comb d a b) (l + 1) (a :: ys) :=
    Run.perm List.perm_append_comm first
  simpa only [Nat.add_assoc] using Run.substitute left second

def ReadOnce {α : Type} [DecidableEq α] (raw : α → Sig) (u : Bool)
    (A : Finset α) (v : Sig) : Prop :=
  A.Nonempty ∧ Run u (observe v) (A.card - 1) (A.toList.map (fun r => observe (raw r)))

theorem ReadOnce.leaf {α : Type} [DecidableEq α] (raw : α → Sig) (u : Bool) (r : α) :
    ReadOnce raw u {r} (raw r) := by
  have perm : [r].Perm ({r} : Finset α).toList := by
    apply List.perm_of_nodup_nodup_toFinset_eq (by simp) (Finset.nodup_toList _)
    simp
  refine ⟨by simp, ?_⟩
  simpa only [Finset.card_singleton, Nat.sub_self, List.map_cons, List.map_nil] using
    Run.perm (perm.map (fun q => observe (raw q))) (Run.stop (u := u) (goal := observe (raw r)))

theorem ReadOnce.combine {α : Type} [DecidableEq α] (raw : α → Sig) (u : Bool)
    {A B : Finset α} {a b : Sig} (left : ReadOnce raw u A a) (right : ReadOnce raw u B b)
    (disjoint : Disjoint A B) (d : Nat) (legal : allowed u d) :
    ReadOnce raw u (A ∪ B) (bin d a b) := by
  have nd : (A.toList ++ B.toList).Nodup := by
    simp only [List.nodup_append]
    refine ⟨Finset.nodup_toList _, Finset.nodup_toList _, ?_⟩
    intro x hx y hy eq
    subst y
    exact Finset.disjoint_left.mp disjoint (Finset.mem_toList.mp hx) (Finset.mem_toList.mp hy)
  have perm : (A.toList ++ B.toList).Perm (A ∪ B).toList := by
    apply List.perm_of_nodup_nodup_toFinset_eq nd (Finset.nodup_toList _)
    simp
  have combined := Run.combine_traces left.2 right.2 d legal
  have lifted : (A.toList.map (fun r => observe (raw r)) ++
      B.toList.map (fun r => observe (raw r))).Perm
      ((A ∪ B).toList.map (fun r => observe (raw r))) := by
    simpa only [List.map_append] using perm.map (fun r => observe (raw r))
  have ordered := Run.perm lifted combined
  have count : (A ∪ B).card - 1 = A.card - 1 + (B.card - 1) + 1 := by
    rw [Finset.card_union_of_disjoint disjoint]
    have pa := Finset.card_pos.mpr left.1
    have pb := Finset.card_pos.mpr right.1
    omega
  refine ⟨?_, ?_⟩
  · obtain ⟨r, hr⟩ := left.1
    exact ⟨r, Finset.mem_union_left _ hr⟩
  · simpa only [count, obs_bin] using ordered

theorem ReadOnce.map {α β : Type} [DecidableEq α] [DecidableEq β]
    (raw : α → Sig) (nextRaw : β → Sig) (u : Bool)
    (f : α → β) (injective : Function.Injective f)
    (same : ∀ r, nextRaw (f r) = raw r)
    {A : Finset α} {v : Sig} (trace : ReadOnce raw u A v) :
    ReadOnce nextRaw u (A.image f) v := by
  have nd : (A.toList.map f).Nodup := (Finset.nodup_toList A).map injective
  have perm : (A.toList.map f).Perm (A.image f).toList := by
    apply List.perm_of_nodup_nodup_toFinset_eq nd (Finset.nodup_toList _)
    ext r
    simp
  have count : (A.image f).card = A.card := by
    simpa using perm.length_eq.symm
  have mapped : (A.toList.map f).map (fun r => observe (nextRaw r)) =
      A.toList.map (fun r => observe (raw r)) := by
    simp only [List.map_map, Function.comp_def, same]
  have moved : Run u (observe v) (A.card - 1)
      ((A.toList.map f).map (fun r => observe (nextRaw r))) := by
    rw [mapped]
    exact trace.2
  refine ⟨?_, ?_⟩
  · obtain ⟨r, hr⟩ := trace.1
    exact ⟨f r, Finset.mem_image_of_mem f hr⟩
  · rw [count]
    exact Run.perm (perm.map (fun r => observe (nextRaw r))) moved
theorem Run.substitute_list {R : Type} {u : Bool} {target : Wire R}
    (xs : List (Wire R)) (leaves : Wire R → List (Wire R)) (cost : Wire R → Nat)
    (traces : ∀ v ∈ xs, Run u v (cost v) (leaves v))
    {rest : List (Wire R)} {k : Nat} (tail : Run u target k (xs ++ rest)) :
    Run u target ((xs.map cost).sum + k) (xs.flatMap leaves ++ rest) := by
  induction xs generalizing rest k with
  | nil => simpa using tail
  | cons v xs ih =>
    have perm : ((v :: xs) ++ rest).Perm (xs ++ v :: rest) := by
      have small : ([v] ++ xs).Perm (xs ++ [v]) := List.perm_append_comm
      simpa only [List.cons_append, List.nil_append, List.append_assoc] using
        small.append_right rest
    have shifted := Run.perm perm tail
    have expanded := ih (fun w hw => traces w (List.mem_cons_of_mem v hw)) shifted
    have permBack : (xs.flatMap leaves ++ v :: rest).Perm
        (v :: (xs.flatMap leaves ++ rest)) := by
      have small : (xs.flatMap leaves ++ [v]).Perm ([v] ++ xs.flatMap leaves) :=
        List.perm_append_comm
      simpa only [List.cons_append, List.nil_append, List.append_assoc] using
        small.append_right rest
    have atHead := Run.perm permBack expanded
    have result := Run.substitute (traces v (by simp)) atHead
    simpa only [List.map_cons, List.sum_cons, List.flatMap_cons, List.append_assoc,
      Nat.add_assoc] using result
lemma partition_flatMap_perm {α : Type} [DecidableEq α]
    (roots : Finset α) (S : Finset Sig) (label : Sig → Finset α)
    (part : LabelPartition roots S label) :
    (S.toList.flatMap fun v => (label v).toList).Perm roots.toList := by
  have pair : List.Pairwise
      (fun v w => List.Disjoint (label v).toList (label w).toList) S.toList := by
    apply List.Pairwise.imp_of_mem _ (Finset.nodup_toList S)
    intro v w hv hw hne
    apply List.disjoint_left.mpr
    intro r hrv hrw
    exact Finset.disjoint_left.mp
      (part.2.1 v (Finset.mem_toList.mp hv) w (Finset.mem_toList.mp hw) hne)
      (Finset.mem_toList.mp hrv) (Finset.mem_toList.mp hrw)
  have nodup : (S.toList.flatMap fun v => (label v).toList).Nodup :=
    List.nodup_flatMap.mpr ⟨fun v _ => Finset.nodup_toList (label v), pair⟩
  apply (List.perm_ext_iff_of_nodup nodup (Finset.nodup_toList roots)).mpr
  intro r
  constructor
  · intro hr
    obtain ⟨v, hv, hrv⟩ := List.mem_flatMap.mp hr
    exact Finset.mem_toList.mpr
      (part.1 v (Finset.mem_toList.mp hv) (Finset.mem_toList.mp hrv))
  · intro hr
    obtain ⟨v, hv, hrv⟩ := part.2.2 r (Finset.mem_toList.mp hr)
    exact List.mem_flatMap.mpr
      ⟨v, Finset.mem_toList.mpr hv, Finset.mem_toList.mpr hrv⟩

lemma partition_cost_sum {α : Type} [DecidableEq α]
    (roots : Finset α) (S : Finset Sig) (label : Sig → Finset α)
    (part : LabelPartition roots S label)
    (nonempty : ∀ v ∈ S, (label v).Nonempty) :
    (S.toList.map fun v => (label v).card - 1).sum + S.card = roots.card := by
  have cardinal : (S.toList.map fun v => (label v).card).sum = roots.card := by
    simpa only [List.length_flatMap, Finset.length_toList] using
      (partition_flatMap_perm roots S label part).length_eq
  have sumIdentity (vs : List Sig) : (∀ v ∈ vs, v ∈ S) →
      (vs.map fun v => (label v).card - 1).sum + vs.length =
        (vs.map fun v => (label v).card).sum := by
    induction vs with
    | nil => intro _; simp
    | cons v vs ih =>
      intro hv
      have positive : 0 < (label v).card :=
        Finset.card_pos.mpr (nonempty v (hv v (by simp)))
      have tail := ih (fun w hw => hv w (List.mem_cons_of_mem v hw))
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      omega
  have total := sumIdentity S.toList (fun v hv => Finset.mem_toList.mp hv)
  simpa only [Finset.length_toList] using total.trans cardinal
theorem readOnce_forest_run {α : Type} [DecidableEq α]
    (roots : Finset α) (raw : α → Sig) (u : Bool) (T : Sig)
    {k : Nat} {S : Finset Sig} (run : Live u T k S)
    (label : Sig → Finset α) (part : LabelPartition roots S label)
    (entries : ∀ v ∈ S, ReadOnce raw u (label v) v) :
    Run u (observe T) (k + roots.card - S.card)
      (roots.toList.map (fun r => observe (raw r))) := by
  classical
  let leaves (w : Wire Row) := (label (table w)).toList.map (fun r => observe (raw r))
  let cost (w : Wire Row) := (label (table w)).card - 1
  have traces : ∀ w ∈ S.toList.map observe, Run u w (cost w) (leaves w) := by
    intro w hw
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hw
    simpa only [cost, leaves, table_observe] using (entries v (Finset.mem_toList.mp hv)).2
  have trace := list_run run S.toList (Finset.nodup_toList S) (by simp)
  have expanded := Run.substitute_list (S.toList.map observe) leaves cost traces
    (rest := []) (by simpa only [List.append_nil] using trace)
  have flat : (S.toList.map observe).flatMap leaves =
      (S.toList.flatMap (fun v => (label v).toList)).map (fun r => observe (raw r)) := by
    simp only [List.flatMap_map, leaves, table_observe, List.map_flatMap]
  have expanded' : Run u (observe T)
      ((S.toList.map (fun v => (label v).card - 1)).sum + k)
      ((S.toList.flatMap (fun v => (label v).toList)).map (fun r => observe (raw r))) := by
    simpa only [List.append_nil, List.map_map, Function.comp_def, cost, table_observe, flat]
      using expanded
  have moved := Run.perm
    ((partition_flatMap_perm roots S label part).map (fun r => observe (raw r))) expanded'
  have count := partition_cost_sum roots S label part (fun v hv => (entries v hv).1)
  have costEq : (S.toList.map (fun v => (label v).card - 1)).sum + k =
      k + roots.card - S.card := by omega
  simpa only [costEq] using moved

theorem readOnce_forest_exclusion_state {α : Type} [DecidableEq α]
    (roots : Finset α) (raw : α → Sig) (u : Bool) (T : Sig) (depth : Nat)
    (blocked : ∀ n, n + 1 ≤ roots.card + depth →
      ¬ Run u (observe T) n (roots.toList.map (fun r => observe (raw r))))
    {k : Nat} {S : Finset Sig} (run : Live u T k S) (cap : k + 1 ≤ S.card + depth)
    (label : Sig → Finset α) (part : LabelPartition roots S label)
    (entries : ∀ v ∈ S, ReadOnce raw u (label v) v) : False := by
  have count := partition_cost_sum roots S label part (fun v hv => (entries v hv).1)
  exact blocked (k + roots.card - S.card) (by omega)
    (readOnce_forest_run roots raw u T run label part entries)

end PEqualNP.Outside.L_meta_2373.Live1024

namespace PEqualNP.Outside.L_meta_2373.Live1024

theorem Run.substitute_indexed {ι R : Type} {u : Bool} {target : Wire R}
    (xs : List ι) (value : ι → Wire R) (leaves : ι → List (Wire R)) (cost : ι → Nat)
    (traces : ∀ i ∈ xs, Run u (value i) (cost i) (leaves i))
    {rest : List (Wire R)} {k : Nat} (tail : Run u target k (xs.map value ++ rest)) :
    Run u target ((xs.map cost).sum + k) (xs.flatMap leaves ++ rest) := by
  induction xs generalizing rest k with
  | nil => simpa using tail
  | cons i xs ih =>
    have perm : ((i :: xs).map value ++ rest).Perm (xs.map value ++ value i :: rest) := by
      have small : ([value i] ++ xs.map value).Perm (xs.map value ++ [value i]) :=
        List.perm_append_comm
      simpa only [List.map_cons, List.cons_append, List.nil_append, List.append_assoc] using
        small.append_right rest
    have shifted := Run.perm perm tail
    have expanded := ih (fun j hj => traces j (List.mem_cons_of_mem i hj)) shifted
    have permBack : (xs.flatMap leaves ++ value i :: rest).Perm
        (value i :: (xs.flatMap leaves ++ rest)) := by
      have small : (xs.flatMap leaves ++ [value i]).Perm ([value i] ++ xs.flatMap leaves) :=
        List.perm_append_comm
      simpa only [List.cons_append, List.nil_append, List.append_assoc] using
        small.append_right rest
    have atHead := Run.perm permBack expanded
    have result := Run.substitute (traces i (by simp)) atHead
    simpa only [List.map_cons, List.sum_cons, List.flatMap_cons, List.append_assoc,
      Nat.add_assoc] using result

theorem readOnce_indexed_forest_run {α : Type} [DecidableEq α]
    (roots : Finset α) (raw : α → Sig) (u : Bool) (T : Sig)
    {k : Nat} {S : Finset Sig} (value : Sig → Sig)
    (run : Run u (observe T) k (S.toList.map (fun v => observe (value v))))
    (label : Sig → Finset α) (part : LabelPartition roots S label)
    (entries : ∀ v ∈ S, ReadOnce raw u (label v) (value v)) :
    Run u (observe T) (k + roots.card - S.card)
      (roots.toList.map (fun r => observe (raw r))) := by
  classical
  let leaves (v : Sig) := (label v).toList.map (fun r => observe (raw r))
  let cost (v : Sig) := (label v).card - 1
  have traces : ∀ v ∈ S.toList, Run u (observe (value v)) (cost v) (leaves v) := by
    intro v hv
    exact (entries v (Finset.mem_toList.mp hv)).2
  have expanded := Run.substitute_indexed S.toList (fun v => observe (value v)) leaves cost traces
    (rest := []) (by simpa only [List.append_nil] using run)
  have flat : S.toList.flatMap leaves =
      (S.toList.flatMap (fun v => (label v).toList)).map (fun r => observe (raw r)) := by
    simp only [leaves, List.map_flatMap]
  have expanded' : Run u (observe T)
      ((S.toList.map (fun v => (label v).card - 1)).sum + k)
      ((S.toList.flatMap (fun v => (label v).toList)).map (fun r => observe (raw r))) := by
    simpa only [List.append_nil, cost, flat] using expanded
  have moved := Run.perm
    ((partition_flatMap_perm roots S label part).map (fun r => observe (raw r))) expanded'
  have count := partition_cost_sum roots S label part (fun v hv => (entries v hv).1)
  have costEq : (S.toList.map (fun v => (label v).card - 1)).sum + k =
      k + roots.card - S.card := by omega
  simpa only [costEq] using moved

theorem readOnce_indexed_forest_exclusion_state {α : Type} [DecidableEq α]
    (roots : Finset α) (raw : α → Sig) (u : Bool) (T : Sig) (depth : Nat)
    (blocked : ∀ n, n + 1 ≤ roots.card + depth →
      ¬ Run u (observe T) n (roots.toList.map (fun r => observe (raw r))))
    {k : Nat} {S : Finset Sig} (value : Sig → Sig)
    (run : Run u (observe T) k (S.toList.map (fun v => observe (value v))))
    (cap : k + 1 ≤ S.card + depth)
    (label : Sig → Finset α) (part : LabelPartition roots S label)
    (entries : ∀ v ∈ S, ReadOnce raw u (label v) (value v)) : False := by
  have count := partition_cost_sum roots S label part (fun v hv => (entries v hv).1)
  exact blocked (k + roots.card - S.card) (by omega)
    (readOnce_indexed_forest_run roots raw u T value run label part entries)

end PEqualNP.Outside.L_meta_2373.Live1024

namespace PEqualNP.Outside.L_meta_2373.Live1024

theorem first_copy_run {u : Bool} {T a b : Sig} {k d : Nat} {U : Finset Sig}
    (tail : Live u T k (insert (bin d a b) U)) (hd : allowed u d)
    (hb : b ∈ U) (fresh : bin d a b ∉ U) :
    Run u (observe T) (k + 1)
      ((insert (bin d a b) U).toList.map
        (fun v => observe (if v = bin d a b then a else v))) := by
  classical
  let z := bin d a b
  let value : Sig → Sig := fun v => if v = z then a else v
  let rest := (U.erase b).toList
  let vs := z :: b :: rest
  have bz : b ≠ z := by
    intro h
    exact fresh (Eq.mp (congrArg (fun v : Sig => v ∈ U) h) hb)
  have zr : z ∉ rest := by
    simpa only [rest, Finset.mem_toList, Finset.mem_erase, not_and] using
      (fun _ h => fresh h)
  have br : b ∉ rest := by simp [rest]
  have restnd : rest.Nodup := Finset.nodup_toList _
  have nd : vs.Nodup := by simp [vs, Ne.symm bz, zr, br, restnd]
  have eqv : vs.toFinset = insert z U := by
    simp [vs, rest, Finset.insert_erase hb]
  have progress := list_run tail vs nd eqv
  have finish : Run u (observe T) (k + 1)
      (observe a :: observe b :: rest.map observe) :=
    Run.two d hd false true (by simpa [vs, kept, z, obs_bin] using progress)
  have untouched (v : Sig) (hv : v ∈ U) : value v = v := by
    have vz : v ≠ z := by
      intro h
      exact fresh (Eq.mp (congrArg (fun v : Sig => v ∈ U) h) hv)
    simp [value, vz]
  have mappedRest : rest.map (fun v => observe (value v)) = rest.map observe := by
    apply List.map_congr_left
    intro v hv
    rw [untouched v (Finset.mem_erase.mp (Finset.mem_toList.mp hv)).2]
  have source : Run u (observe T) (k + 1)
      (vs.map (fun v => observe (value v))) := by
    simpa only [vs, List.map_cons, show value z = a by simp [value],
      untouched b hb, mappedRest] using finish
  have perm : vs.Perm (insert z U).toList := by
    apply List.perm_of_nodup_nodup_toFinset_eq nd (Finset.nodup_toList _)
    simpa using eqv
  exact Run.perm (perm.map (fun v => observe (value v))) source

end PEqualNP.Outside.L_meta_2373.Live1024

namespace PEqualNP.Outside.L_meta_2373.Live1024

def copyInputLabels {α : Type} [DecidableEq α] (label : Sig → Finset α)
    (a z v : Sig) : Finset (Sum α Bool) :=
  if v = z then {Sum.inr true}
  else if v = a then {Sum.inr false} else liftLabels (label v)

theorem copy_input_partition {α : Type} [DecidableEq α]
    (roots : Finset α) (S : Finset Sig) (label : Sig → Finset α)
    (a z : Sig) (part : LabelPartition roots S label)
    (ha : a ∈ S) (fresh : z ∉ S) :
    LabelPartition (duplicateRoots roots (label a)) (insert z S)
      (copyInputLabels label a z) := by
  classical
  let next := copyInputLabels label a z
  have anz : a ≠ z := by rintro rfl; exact fresh ha
  have leftMem (v : Sig) (r : α) : Sum.inl r ∈ next v ↔
      v ≠ z ∧ v ≠ a ∧ r ∈ label v := by
    by_cases vz : v = z <;> by_cases va : v = a <;>
      simp [next, copyInputLabels, liftLabels, vz, va, anz]
  have falseMem (v : Sig) : Sum.inr false ∈ next v ↔ v ≠ z ∧ v = a := by
    by_cases vz : v = z <;> by_cases va : v = a <;>
      simp [next, copyInputLabels, liftLabels, vz, va, anz]
  have trueMem (v : Sig) : Sum.inr true ∈ next v ↔ v = z := by
    by_cases vz : v = z <;> by_cases va : v = a <;>
      simp [next, copyInputLabels, liftLabels, vz, va, anz]
  change LabelPartition (duplicateRoots roots (label a)) (insert z S) next
  refine ⟨?_, ?_, ?_⟩
  · intro v hv q hq
    cases q with
    | inl r =>
      obtain ⟨vz, va, hr⟩ := (leftMem v r).mp hq
      have hvS := (Finset.mem_insert.mp hv).resolve_left vz
      have rRoot := part.1 v hvS hr
      have notA : r ∉ label a := fun h =>
        Finset.disjoint_left.mp (part.2.1 v hvS a ha va) hr h
      simp [duplicateRoots, liftLabels, rRoot, notA]
    | inr bit => cases bit <;> simp [duplicateRoots]
  · intro v hv w hw hne
    apply Finset.disjoint_left.mpr
    intro q hqv hqw
    cases q with
    | inl r =>
      obtain ⟨vz, _, hrv⟩ := (leftMem v r).mp hqv
      obtain ⟨wz, _, hrw⟩ := (leftMem w r).mp hqw
      exact Finset.disjoint_left.mp
        (part.2.1 v ((Finset.mem_insert.mp hv).resolve_left vz)
          w ((Finset.mem_insert.mp hw).resolve_left wz) hne) hrv hrw
    | inr bit =>
      cases bit with
      | false => exact hne (((falseMem v).mp hqv).2.trans ((falseMem w).mp hqw).2.symm)
      | true => exact hne (((trueMem v).mp hqv).trans ((trueMem w).mp hqw).symm)
  · intro q hq
    cases q with
    | inl r =>
      have hr : r ∈ roots ∧ r ∉ label a := by
        simpa [duplicateRoots, liftLabels] using hq
      obtain ⟨v, hv, hrv⟩ := part.2.2 r hr.1
      have vz : v ≠ z := by rintro rfl; exact fresh hv
      have va : v ≠ a := by rintro rfl; exact hr.2 hrv
      exact ⟨v, Finset.mem_insert_of_mem hv, (leftMem v r).mpr ⟨vz, va, hrv⟩⟩
    | inr bit =>
      cases bit with
      | false => exact ⟨a, Finset.mem_insert_of_mem ha, (falseMem a).mpr ⟨anz, rfl⟩⟩
      | true => exact ⟨z, Finset.mem_insert_self _ _, (trueMem z).mpr rfl⟩

end PEqualNP.Outside.L_meta_2373.Live1024

namespace PEqualNP.Outside.L_meta_2373.Live1024

theorem copy_input_readOnce {α : Type} [DecidableEq α]
    (raw : α → Sig) (u : Bool) (S : Finset Sig) (label : Sig → Finset α) (a z : Sig)
    (fresh : z ∉ S) (entries : ∀ v ∈ S, ReadOnce raw u (label v) v) :
    ∀ v ∈ insert z S,
      ReadOnce (duplicateRaw raw a) u (copyInputLabels label a z v)
        (if v = z then a else v) := by
  intro v hv
  by_cases hvz : v = z
  · subst v
    simpa [copyInputLabels, duplicateRaw] using
      ReadOnce.leaf (duplicateRaw raw a) u (Sum.inr true)
  · have hvS : v ∈ S := (Finset.mem_insert.mp hv).resolve_left hvz
    by_cases hva : v = a
    · subst v
      simpa [copyInputLabels, hvz, duplicateRaw] using
        ReadOnce.leaf (duplicateRaw raw a) u (Sum.inr false)
    · have mapped := ReadOnce.map raw (duplicateRaw raw a) u Sum.inl
        (by intro x y h; cases h; rfl) (by intro r; rfl) (entries v hvS)
      simpa [copyInputLabels, hvz, hva, liftLabels] using mapped

theorem first_copy_forest_exclusion {α : Type} [DecidableEq α]
    (roots : Finset α) (raw : α → Sig) (u : Bool) (T : Sig) (depth : Nat)
    {k d : Nat} {U : Finset Sig} {a b : Sig}
    (tail : Live u T k (insert (bin d a b) U)) (hd : allowed u d)
    (ha : a ∈ U) (hb : b ∈ U) (fresh : bin d a b ∉ U)
    (cap : k + 1 ≤ U.card + depth)
    (label : Sig → Finset α) (part : LabelPartition roots U label)
    (entries : ∀ v ∈ U, ReadOnce raw u (label v) v)
    (blocked : ∀ n, n + 1 ≤ (duplicateRoots roots (label a)).card + depth →
      ¬ Run u (observe T) n
        ((duplicateRoots roots (label a)).toList.map
          (fun r => observe (duplicateRaw raw a r)))) : False := by
  have part2 := copy_input_partition roots U label a (bin d a b) part ha fresh
  have entries2 := copy_input_readOnce raw u U label a (bin d a b) fresh entries
  have run := first_copy_run tail hd hb fresh
  apply readOnce_indexed_forest_exclusion_state
    (duplicateRoots roots (label a)) (duplicateRaw raw a) u T depth blocked
    (fun v => if v = bin d a b then a else v) run ?_
    (copyInputLabels label a (bin d a b)) part2 entries2
  rw [Finset.card_insert_of_notMem fresh]
  omega

end PEqualNP.Outside.L_meta_2373.Live1024

namespace PEqualNP.Outside.L_meta_2373.Live1024

def compressLabels {α : Type} [DecidableEq α] (label : Sig → Finset α)
    (z v : Sig) : Finset (Sum α Bool) :=
  if v = z then {Sum.inr false} else liftLabels (label v)

def compressRoots {α : Type} [DecidableEq α] (roots A : Finset α) :
    Finset (Sum α Bool) := liftLabels (roots \ A) ∪ {Sum.inr false}

theorem compress_partition {α : Type} [DecidableEq α]
    (roots : Finset α) (S : Finset Sig) (label : Sig → Finset α)
    (z : Sig) (part : LabelPartition roots S label) (hz : z ∈ S) :
    LabelPartition (compressRoots roots (label z)) S (compressLabels label z) := by
  classical
  let next := compressLabels label z
  have leftMem (v : Sig) (r : α) :
      Sum.inl r ∈ next v ↔ v ≠ z ∧ r ∈ label v := by
    by_cases vz : v = z <;> simp [next, compressLabels, liftLabels, vz]
  have falseMem (v : Sig) : Sum.inr false ∈ next v ↔ v = z := by
    by_cases vz : v = z <;> simp [next, compressLabels, liftLabels, vz]
  have trueNotMem (v : Sig) : Sum.inr true ∉ next v := by
    by_cases vz : v = z <;> simp [next, compressLabels, liftLabels, vz]
  change LabelPartition (compressRoots roots (label z)) S next
  refine ⟨?_, ?_, ?_⟩
  · intro v hv q hq
    cases q with
    | inl r =>
      obtain ⟨vz, hr⟩ := (leftMem v r).mp hq
      have rRoot := part.1 v hv hr
      have notZ : r ∉ label z := fun h =>
        Finset.disjoint_left.mp (part.2.1 v hv z hz vz) hr h
      simp [compressRoots, liftLabels, rRoot, notZ]
    | inr bit =>
      cases bit with
      | false => simp [compressRoots]
      | true => exact False.elim (trueNotMem v hq)
  · intro v hv w hw hne
    apply Finset.disjoint_left.mpr
    intro q hqv hqw
    cases q with
    | inl r =>
      exact Finset.disjoint_left.mp (part.2.1 v hv w hw hne)
        ((leftMem v r).mp hqv).2 ((leftMem w r).mp hqw).2
    | inr bit =>
      cases bit with
      | false => exact hne (((falseMem v).mp hqv).trans ((falseMem w).mp hqw).symm)
      | true => exact trueNotMem v hqv
  · intro q hq
    cases q with
    | inl r =>
      have hr : r ∈ roots ∧ r ∉ label z := by
        simpa [compressRoots, liftLabels] using hq
      obtain ⟨v, hv, hrv⟩ := part.2.2 r hr.1
      have vz : v ≠ z := by rintro rfl; exact hr.2 hrv
      exact ⟨v, hv, (leftMem v r).mpr ⟨vz, hrv⟩⟩
    | inr bit =>
      cases bit with
      | false => exact ⟨z, hz, (falseMem z).mpr rfl⟩
      | true => simpa [compressRoots, liftLabels] using hq

end PEqualNP.Outside.L_meta_2373.Live1024

namespace PEqualNP.Outside.L_meta_2373.Live1024

theorem compress_wire_readOnce {α : Type} [DecidableEq α]
    (raw : α → Sig) (u : Bool) (S : Finset Sig) (label : Sig → Finset α) (z : Sig)
    (entries : ∀ v ∈ S, ReadOnce raw u (label v) v) :
    ∀ v ∈ S, ReadOnce (duplicateRaw raw z) u (compressLabels label z v) v := by
  intro v hv
  by_cases hvz : v = z
  · subst v
    simpa [compressLabels, duplicateRaw] using
      ReadOnce.leaf (duplicateRaw raw z) u (Sum.inr false)
  · have mapped := ReadOnce.map raw (duplicateRaw raw z) u Sum.inl
      (by intro x y h; cases h; rfl) (by intro r; rfl) (entries v hv)
    simpa [compressLabels, hvz, liftLabels] using mapped

theorem compressed_wire_forest_exclusion {α : Type} [DecidableEq α]
    (roots : Finset α) (raw : α → Sig) (u : Bool) (T : Sig) (depth : Nat)
    {k : Nat} {S : Finset Sig} (run : Live u T k S) (cap : k + 1 ≤ S.card + depth)
    (label : Sig → Finset α) (part : LabelPartition roots S label)
    (entries : ∀ v ∈ S, ReadOnce raw u (label v) v)
    (z : Sig) (hz : z ∈ S)
    (blocked : ∀ n, n + 1 ≤ (compressRoots roots (label z)).card + depth →
      ¬ Run u (observe T) n
        ((compressRoots roots (label z)).toList.map
          (fun r => observe (duplicateRaw raw z r)))) : False := by
  have part2 := compress_partition roots S label z part hz
  have entries2 := compress_wire_readOnce raw u S label z entries
  exact readOnce_forest_exclusion_state
    (compressRoots roots (label z)) (duplicateRaw raw z) u T depth blocked
    run cap (compressLabels label z) part2 entries2

end PEqualNP.Outside.L_meta_2373.Live1024

namespace PEqualNP.Outside.L_meta_2373.Live1024

def ColumnSupport {α Ω : Type} (raw : α → Sig) (col : Sig → Set Ω)
    (A : Finset α) (v : Sig) : Prop :=
  ∀ o ∈ col v, ∃ r ∈ A, o ∈ col (raw r)

def ColumnAdmissible {α Ω : Type} [DecidableEq α]
    (roots : Finset α) (raw : α → Sig) (col : Sig → Set Ω) (need : Set Ω)
    (A : Finset α) (v : Sig) : Prop :=
  ∀ o ∈ need, (∀ r ∈ roots, r ∉ A → o ∉ col (raw r)) → o ∈ col v

abbrev BudgetRunCut {α : Type} [DecidableEq α]
    (roots : Finset α) (raw : α → Sig) (u : Bool) (T : Sig) (depth : Nat) : Prop :=
  ∀ n, n + 1 ≤ roots.card + depth →
    ¬ Run u (observe T) n (roots.toList.map (fun r => observe (raw r)))

abbrev PrunedGateClosed {α Ω : Type} [DecidableEq α]
    (roots : Finset α) (raw : α → Sig) (col : Sig → Set Ω) (need : Set Ω)
    (Cert : Finset α → Sig → Prop) (u : Bool) (T : Sig) (depth : Nat) : Prop :=
  ∀ A B a b d, Disjoint A B → allowed u d → a ≠ b → bin d a b ≠ a →
    bin d a b ≠ b → proper (bin d a b) → Cert A a → Cert B b →
    ColumnAdmissible roots raw col need (A ∪ B) (bin d a b) →
    Cert (A ∪ B) (bin d a b) ∨
      BudgetRunCut (compressRoots roots (A ∪ B)) (duplicateRaw raw (bin d a b)) u T depth

abbrev PrunedBridge {α Ω : Type} [DecidableEq α]
    (roots : Finset α) (raw : α → Sig) (col : Sig → Set Ω) (need : Set Ω)
    (Cert : Finset α → Sig → Prop) (Cert2 : Finset (Sum α Bool) → Sig → Prop)
    (u : Bool) (T : Sig) (depth : Nat) (A : Finset α) (w : Sig) : Prop :=
  ∀ B v, Cert B v → Disjoint A B →
    ColumnAdmissible (duplicateRoots roots A) (duplicateRaw raw w) col need
      (liftLabels B) v →
    Cert2 (liftLabels B) v ∨
      BudgetRunCut (compressRoots (duplicateRoots roots A) (liftLabels B))
        (duplicateRaw (duplicateRaw raw w) v) u T depth

def PrunedNode {Ω : Type} (col : Sig → Set Ω) (need : Set Ω) (u : Bool) (T : Sig)
    (depth : Nat) (α : Type) [DecidableEq α] (roots : Finset α) (raw : α → Sig)
    (Cert : Finset α → Sig → Prop) : Prop :=
  (∀ r ∈ roots, Cert {r} (raw r)) ∧
  PrunedGateClosed roots raw col need Cert u T depth ∧
  ¬ Cert roots T ∧
  match depth with
  | 0 => True
  | n + 1 =>
    ∀ A w, A ⊆ roots → proper w → Cert A w →
      BudgetRunCut (duplicateRoots roots A) (duplicateRaw raw w) u T n ∨
      ∃ Cert2 : Finset (Sum α Bool) → Sig → Prop,
        PrunedBridge roots raw col need Cert Cert2 u T n A w ∧
        PrunedNode col need u T n (Sum α Bool)
          (duplicateRoots roots A) (duplicateRaw raw w) Cert2

end PEqualNP.Outside.L_meta_2373.Live1024

namespace PEqualNP.Outside.L_meta_2373.Live1024

def successorOps (u : Bool) : List Nat := if u then [0, 1, 2, 3] else [0, 1]

lemma successorOps_complete {u : Bool} {d : Nat} (h : allowed u d) :
    d ∈ successorOps u := by
  cases u <;> simp [successorOps, allowed] at * <;> omega

def successorGuard (ws : List Sig) (cap : Nat) (a b : Sig) (d : Nat) (ka kb : Bool) : Bool :=
  decide (a ≠ b) && decide (bin d a b ∉ ws) &&
    decide (bin d a b ≠ zero) && decide (bin d a b ≠ one) &&
    decide ((childTwo ws a b d ka kb).length ≤ cap)

def successorLists (u : Bool) (ws : List Sig) (cap : Nat) : List (List Sig) :=
  ws.flatMap fun a => ws.flatMap fun b => (successorOps u).flatMap fun d =>
    [false, true].flatMap fun ka => [false, true].filterMap fun kb =>
      if successorGuard ws cap a b d ka kb then some (childTwo ws a b d ka kb) else none

lemma successorLists_complete {u ws cap a b d ka kb}
    (ha : a ∈ ws) (hb : b ∈ ws) (hd : allowed u d) (hab : a ≠ b)
    (fresh : bin d a b ∉ ws) (hp : proper (bin d a b))
    (sz : (childTwo ws a b d ka kb).length ≤ cap) :
    childTwo ws a b d ka kb ∈ successorLists u ws cap := by
  have guard : successorGuard ws cap a b d ka kb = true := by
    simp [successorGuard, hab, fresh, hp.1, hp.2, sz]
  unfold successorLists
  apply List.mem_flatMap.mpr
  refine ⟨a, ha, ?_⟩
  apply List.mem_flatMap.mpr
  refine ⟨b, hb, ?_⟩
  apply List.mem_flatMap.mpr
  refine ⟨d, successorOps_complete hd, ?_⟩
  apply List.mem_flatMap.mpr
  refine ⟨ka, by cases ka <;> simp, ?_⟩
  apply List.mem_filterMap.mpr
  exact ⟨kb, by cases kb <;> simp, by simp [guard]⟩

def rowSeparates (u : Bool) (r s : Row) (w : Sig) : Bool :=
  if u then bit r w != bit s w else bit r w && !(bit s w)

lemma live_rowSeparates {u T k S r s} (h : Live u T k S)
    (sep : rowSeparates u r s T = true) : ∃ w ∈ S, rowSeparates u r s w = true := by
  cases u with
  | true =>
    have diff : bit r T ≠ bit s T := by simpa [rowSeparates] using sep
    obtain ⟨w, hw, hd⟩ := live_row_difference h diff
    exact ⟨w, hw, by simpa [rowSeparates] using hd⟩
  | false =>
    have bits : bit r T = true ∧ bit s T = false := by simpa [rowSeparates] using sep
    obtain ⟨w, hw, yes, no⟩ := mono_row_difference h rfl bits.1 bits.2
    exact ⟨w, hw, by simp [rowSeparates, yes, no]⟩

def rowReject (u : Bool) (T : Sig) (ws : List Sig) (pair : Row × Row) : Bool :=
  rowSeparates u pair.1 pair.2 T && ws.all (fun w => !(rowSeparates u pair.1 pair.2 w))

lemma rowReject_sound {u T ws pair} (check : rowReject u T ws pair = true) :
    ∀ k, ¬ Live u T k ws.toFinset := by
  intro k run
  have both := Bool.and_eq_true_iff.mp check
  obtain ⟨w, hw, hsep⟩ := live_rowSeparates run both.1
  have hn := List.all_eq_true.mp both.2 w (List.mem_toFinset.mp hw)
  simp [hsep] at hn

def successorCheck (u : Bool) (T : Sig) (ws : List Sig) (cap : Nat)
    (known : List (Finset Sig)) (rows : List (Row × Row)) : Bool :=
  (successorLists u ws cap).all fun child =>
    decide (child.toFinset ∈ known) || rows.any (rowReject u T child)

lemma successorCheck_sound {u T ws cap known rows} (nd : ws.Nodup) (out : T ∉ ws)
    (knownSound : ∀ S ∈ known, Impossible u T (cap - 1) S)
    (check : successorCheck u T ws cap known rows = true) :
    Impossible u T cap ws.toFinset := by
  apply enum_step nd out
  intro a ha b hb d hd ka kb hab fresh hp sz
  have mem := successorLists_complete ha hb hd hab fresh hp sz
  have done := List.all_eq_true.mp check _ mem
  rcases Bool.or_eq_true_iff.mp done with hit | cut
  · exact knownSound _ (of_decide_eq_true hit)
  · obtain ⟨pair, hpair, good⟩ := List.any_eq_true.mp cut
    exact fun k _ => rowReject_sound good k

end PEqualNP.Outside.L_meta_2373.Live1024

namespace PEqualNP.Outside.L_meta_2373.Live1024

def pairColumn (u : Bool) (v : Sig) : Set (Row × Row) :=
  {p | rowSeparates u p.1 p.2 v = true}

def columnReject {α : Type} [DecidableEq α] (u : Bool) (T : Sig)
    (roots : List α) (raw : α → Sig) (A : Finset α) (v : Sig)
    (rows : List (Row × Row)) : Bool :=
  rows.any fun p => rowSeparates u p.1 p.2 T && !(rowSeparates u p.1 p.2 v) &&
    roots.all (fun r => decide (r ∈ A) || !(rowSeparates u p.1 p.2 (raw r)))

theorem columnReject_sound {α : Type} [DecidableEq α] {u T}
    {roots : List α} {raw : α → Sig} {A : Finset α} {v : Sig} {rows}
    (check : columnReject u T roots raw A v rows = true) :
    ¬ ColumnAdmissible roots.toFinset raw (pairColumn u) (pairColumn u T) A v := by
  obtain ⟨p, _, h⟩ := List.any_eq_true.mp check
  have both := Bool.and_eq_true_iff.mp h
  have bits := Bool.and_eq_true_iff.mp both.1
  intro adm
  have value := adm p bits.1 (by
    intro r hr hn
    have test := List.all_eq_true.mp both.2 r (List.mem_toFinset.mp hr)
    rcases Bool.or_eq_true_iff.mp test with inside | outside
    · exact False.elim (hn (of_decide_eq_true inside))
    · intro col
      simp only [pairColumn, Set.mem_ofPred_eq] at col
      simp [col] at outside)
  simp only [pairColumn, Set.mem_ofPred_eq] at value
  simp [value] at bits

abbrev Entry (α : Type) := Finset α × Sig

def entryCert {α : Type} (entries : List (Entry α)) (A : Finset α) (v : Sig) : Prop :=
  (A, v) ∈ entries

def entryGateCheck {α : Type} [DecidableEq α]
    (u : Bool) (T : Sig) (roots : List α) (raw : α → Sig)
    (entries cuts : List (Entry α)) (rows : List (Row × Row)) : Bool :=
  entries.all fun e => entries.all fun f => (successorOps u).all fun d =>
    let z := bin d e.2 f.2
    if Disjoint e.1 f.1 ∧ e.2 ≠ f.2 ∧ z ≠ e.2 ∧ z ≠ f.2 ∧ z ≠ zero ∧ z ≠ one then
      decide ((e.1 ∪ f.1, z) ∈ entries) || decide ((e.1 ∪ f.1, z) ∈ cuts) ||
        columnReject u T roots raw (e.1 ∪ f.1) z rows
    else true

theorem entryGateCheck_sound {α : Type} [DecidableEq α]
    {u T depth} {roots : List α} {raw : α → Sig}
    {entries cuts : List (Entry α)} {rows : List (Row × Row)}
    (cutSound : ∀ A v, (A, v) ∈ cuts →
      BudgetRunCut (compressRoots roots.toFinset A) (duplicateRaw raw v) u T depth)
    (check : entryGateCheck u T roots raw entries cuts rows = true) :
    PrunedGateClosed roots.toFinset raw (pairColumn u) (pairColumn u T)
      (entryCert entries) u T depth := by
  intro A B a b d disjoint legal distinct freshA freshB hp left right adm
  have outer := List.all_eq_true.mp check (A, a) left
  have inner := List.all_eq_true.mp outer (B, b) right
  have gate := List.all_eq_true.mp inner d (successorOps_complete legal)
  have guard : Disjoint A B ∧ a ≠ b ∧ bin d a b ≠ a ∧ bin d a b ≠ b ∧
      bin d a b ≠ zero ∧ bin d a b ≠ one := ⟨disjoint, distinct, freshA, freshB, hp⟩
  dsimp only at gate
  rw [if_pos guard] at gate
  rcases Bool.or_eq_true_iff.mp gate with keptOrCut | rejected
  · rcases Bool.or_eq_true_iff.mp keptOrCut with kept | cut
    · apply Or.inl
      change (A ∪ B, bin d a b) ∈ entries
      exact of_decide_eq_true kept
    · exact Or.inr (cutSound _ _ (of_decide_eq_true cut))
  · exact False.elim (columnReject_sound rejected adm)

end PEqualNP.Outside.L_meta_2373.Live1024

namespace PEqualNP.Outside.L_meta_2373.Live1024

theorem budgetRunCut_of_list {α : Type} [DecidableEq α]
    (roots : Finset α) (raw : α → Sig) (labels : List α) (ws : List Sig)
    (nd : labels.Nodup) (basis : labels.toFinset = roots)
    (values : labels.map raw = ws) (u : Bool) (T : Sig) (depth cap : Nat)
    (size : roots.card + depth ≤ cap + 1)
    (blocked : ∀ k, k ≤ cap → ¬ Run u (observe T) k (ws.map observe)) :
    BudgetRunCut roots raw u T depth := by
  have perm : roots.toList.Perm labels := by
    apply List.perm_of_nodup_nodup_toFinset_eq (Finset.nodup_toList roots) nd
    simpa using basis.symm
  intro k bound run
  have transferred := Run.perm (perm.map (fun r => observe (raw r))) run
  have target : labels.map (fun r => observe (raw r)) = ws.map observe := by
    rw [← values, List.map_map]
    rfl
  rw [target] at transferred
  exact blocked k (by omega) transferred

def entryLeafCheck {α : Type} [DecidableEq α] (roots : List α) (raw : α → Sig)
    (entries : List (Entry α)) : Bool :=
  roots.all (fun r => decide (({r}, raw r) ∈ entries))

theorem entryLeafCheck_sound {α : Type} [DecidableEq α]
    {roots : List α} {raw : α → Sig} {entries : List (Entry α)}
    (check : entryLeafCheck roots raw entries = true) :
    ∀ r ∈ roots.toFinset, entryCert entries {r} (raw r) := by
  intro r hr
  change ({r}, raw r) ∈ entries
  exact of_decide_eq_true (List.all_eq_true.mp check r (List.mem_toFinset.mp hr))

def entryBridgeCheck {α : Type} [DecidableEq α]
    (u : Bool) (T : Sig) (roots : List (Sum α Bool)) (raw : Sum α Bool → Sig)
    (A : Finset α) (entries : List (Entry α))
    (nextEntries cuts : List (Entry (Sum α Bool))) (rows : List (Row × Row)) : Bool :=
  entries.all fun e => if Disjoint A e.1 then
    decide ((liftLabels e.1, e.2) ∈ nextEntries) ||
      decide ((liftLabels e.1, e.2) ∈ cuts) ||
      columnReject u T roots raw (liftLabels e.1) e.2 rows
    else true

theorem entryBridgeCheck_sound {α : Type} [DecidableEq α]
    {roots : Finset α} {raw : α → Sig} {u T depth} {A : Finset α} {w : Sig}
    {nextRoots : List (Sum α Bool)} {entries : List (Entry α)}
    {nextEntries cuts : List (Entry (Sum α Bool))} {rows}
    (basis : nextRoots.toFinset = duplicateRoots roots A)
    (cutSound : ∀ B v, (B, v) ∈ cuts →
      BudgetRunCut (compressRoots nextRoots.toFinset B) (duplicateRaw (duplicateRaw raw w) v)
        u T depth)
    (check : entryBridgeCheck u T nextRoots (duplicateRaw raw w) A entries
      nextEntries cuts rows = true) :
    PrunedBridge roots raw (pairColumn u) (pairColumn u T) (entryCert entries)
      (entryCert nextEntries) u T depth A w := by
  intro B v member disjoint adm
  have result := List.all_eq_true.mp check (B, v) member
  dsimp only at result
  rw [if_pos disjoint] at result
  rcases Bool.or_eq_true_iff.mp result with keptOrCut | rejected
  · rcases Bool.or_eq_true_iff.mp keptOrCut with kept | cut
    · apply Or.inl
      change (liftLabels B, v) ∈ nextEntries
      exact of_decide_eq_true kept
    · apply Or.inr
      simpa only [basis] using cutSound (liftLabels B) v (of_decide_eq_true cut)
  · apply False.elim
    apply columnReject_sound rejected
    simpa only [basis] using adm

theorem prunedNode_zero_of_checks {α : Type} [DecidableEq α]
    (roots : List α) (raw : α → Sig) (u : Bool) (T : Sig)
    (entries cuts : List (Entry α)) (rows : List (Row × Row))
    (cutSound : ∀ A v, (A, v) ∈ cuts →
      BudgetRunCut (compressRoots roots.toFinset A) (duplicateRaw raw v) u T 0)
    (leaves : entryLeafCheck roots raw entries = true)
    (closed : entryGateCheck u T roots raw entries cuts rows = true)
    (missing : (roots.toFinset, T) ∉ entries) :
    PrunedNode (pairColumn u) (pairColumn u T) u T 0 α roots.toFinset raw
      (entryCert entries) :=
  ⟨entryLeafCheck_sound leaves, entryGateCheck_sound cutSound closed, missing, trivial⟩

end PEqualNP.Outside.L_meta_2373.Live1024

namespace PEqualNP.Outside.L_meta_2373.Live1024

theorem initial_raw_state {α Ω : Type} [DecidableEq α]
    (roots : Finset α) (raw : α → Sig) (col : Sig → Set Ω)
    (Cert : Finset α → Sig → Prop) (u : Bool)
    (distinct : Set.InjOn raw (↑roots : Set α))
    (initial : ∀ r ∈ roots, Cert {r} (raw r)) :
    ∃ label : Sig → Finset α,
      LabelPartition roots (roots.image raw) label ∧
      (∀ v ∈ roots.image raw, Cert (label v) v) ∧
      (∀ v ∈ roots.image raw, ReadOnce raw u (label v) v) ∧
      (∀ v ∈ roots.image raw, ColumnSupport raw col (label v) v) := by
  classical
  let label (v : Sig) := roots.filter (fun r => raw r = v)
  have leaf (r : α) (hr : r ∈ roots) : label (raw r) = {r} := by
    ext q
    simp only [label, Finset.mem_filter, Finset.mem_singleton]
    constructor
    · rintro ⟨hq, he⟩
      exact distinct hq hr he
    · rintro rfl
      exact ⟨hr, rfl⟩
  have part : LabelPartition roots (roots.image raw) label := by
    refine ⟨?_, ?_, ?_⟩
    · intro v hv r hr
      exact (Finset.mem_filter.mp hr).1
    · intro v hv w hw hne
      apply Finset.disjoint_left.mpr
      intro r hrv hrw
      have ev := (Finset.mem_filter.mp hrv).2
      have ew := (Finset.mem_filter.mp hrw).2
      exact hne (ev.symm.trans ew)
    · intro r hr
      exact ⟨raw r, Finset.mem_image_of_mem raw hr, Finset.mem_filter.mpr ⟨hr, rfl⟩⟩
  refine ⟨label, part, ?_, ?_, ?_⟩
  · intro v hv
    obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hv
    simpa only [leaf r hr] using initial r hr
  · intro v hv
    obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hv
    simpa only [leaf r hr] using ReadOnce.leaf raw u r
  · intro v hv o ho
    obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hv
    exact ⟨r, Finset.mem_filter.mpr ⟨hr, rfl⟩, ho⟩

end PEqualNP.Outside.L_meta_2373.Live1024

namespace PEqualNP.Outside.L_meta_2373.Live1024

theorem pairColumn_bits (i : Row) (d : Nat) (a b : Sig) :
    bit i (bin d a b) =
      (if d = 0 then bit i a && bit i b else if d = 1 then bit i a || bit i b else
        if d = 2 then bit i a && !(bit i b) else !(bit i a) && bit i b) := by
  unfold bin
  split_ifs <;> simp [bit]

theorem pairColumn_gate (u : Bool) (d : Nat) (a b : Sig) (legal : allowed u d) :
    pairColumn u (bin d a b) ⊆ pairColumn u a ∪ pairColumn u b := by
  intro p hp
  change rowSeparates u p.1 p.2 a = true ∨ rowSeparates u p.1 p.2 b = true
  change rowSeparates u p.1 p.2 (bin d a b) = true at hp
  have bound : d < 4 := by rcases legal with h | h <;> omega
  interval_cases d <;> cases u <;> simp [allowed] at legal
  all_goals
    cases ha : bit p.1 a <;> cases hb : bit p.1 b <;>
      cases hc : bit p.2 a <;> cases he : bit p.2 b <;>
      simp [rowSeparates, pairColumn_bits, ha, hb, hc, he] at hp ⊢

theorem pairColumn_cover (u : Bool) (T : Sig) (k : Nat) (S : Finset Sig)
    (run : Live u T k S) :
    ∀ p ∈ pairColumn u T, ∃ v ∈ S, p ∈ pairColumn u v := by
  intro p hp
  exact live_rowSeparates run hp

end PEqualNP.Outside.L_meta_2373.Live1024

namespace PEqualNP.Outside.L_meta_2373.Live1024

theorem compress_indexed_readOnce {α : Type} [DecidableEq α]
    (raw : α → Sig) (u : Bool) (S : Finset Sig)
    (value : Sig → Sig) (label : Sig → Finset α) (z : Sig)
    (entries : ∀ v ∈ S, ReadOnce raw u (label v) (value v)) :
    ∀ v ∈ S, ReadOnce (duplicateRaw raw (value z)) u
      (compressLabels label z v) (value v) := by
  intro v hv
  by_cases hvz : v = z
  · subst v
    simpa [compressLabels, duplicateRaw] using
      ReadOnce.leaf (duplicateRaw raw (value z)) u (Sum.inr false)
  · have mapped := ReadOnce.map raw (duplicateRaw raw (value z)) u Sum.inl
      (by intro x y h; cases h; rfl) (by intro r; rfl) (entries v hv)
    simpa [compressLabels, hvz, liftLabels] using mapped

theorem compressed_indexed_forest_exclusion {α : Type} [DecidableEq α]
    (roots : Finset α) (raw : α → Sig) (u : Bool) (T : Sig) (depth : Nat)
    {k : Nat} {S : Finset Sig} (value : Sig → Sig)
    (run : Run u (observe T) k (S.toList.map (fun v => observe (value v))))
    (cap : k + 1 ≤ S.card + depth)
    (label : Sig → Finset α) (part : LabelPartition roots S label)
    (entries : ∀ v ∈ S, ReadOnce raw u (label v) (value v))
    (z : Sig) (hz : z ∈ S)
    (blocked : ∀ n, n + 1 ≤ (compressRoots roots (label z)).card + depth →
      ¬ Run u (observe T) n
        ((compressRoots roots (label z)).toList.map
          (fun r => observe (duplicateRaw raw (value z) r)))) : False := by
  have part2 := compress_partition roots S label z part hz
  have entries2 := compress_indexed_readOnce raw u S value label z entries
  exact readOnce_indexed_forest_exclusion_state
    (compressRoots roots (label z)) (duplicateRaw raw (value z)) u T depth blocked
    value run cap (compressLabels label z) part2 entries2

end PEqualNP.Outside.L_meta_2373.Live1024

namespace PEqualNP.Outside.L_meta_2373.Live1024

theorem live_all_proper {u target k S} (h : Live u target k S) : ∀ a ∈ S, proper a := by
  induction h using Live.ind with
  | stop hp => simpa using hp
  | binary hd ha hb hab hf _ ih =>
    simp only [Finset.forall_mem_insert]
    exact ⟨ha,hb,fun a h => ih a (Finset.mem_insert_of_mem h)⟩

theorem live_card_bound {u target k S} (h : Live u target k S) : S.card ≤ k+1 := by
  induction h using Live.ind with
  | stop hp => simp
  | @binary k U a b d hd ha hb hab hf _ ih =>
    have hu : bin d a b ∉ U := fun hm => hf (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hm))
    rw [Finset.card_insert_of_notMem hu] at ih
    have h1 := Finset.card_insert_le (a := a) (s := insert b U)
    have h2 := Finset.card_insert_le (a := b) (s := U)
    omega

theorem partition_admissible {α Ω : Type} [DecidableEq α]
    (roots : Finset α) (raw : α → Sig) (col : Sig → Set Ω) (need : Set Ω)
    {S : Finset Sig} {label : Sig → Finset α}
    (part : LabelPartition roots S label)
    (supports : ∀ v ∈ S, ColumnSupport raw col (label v) v)
    (cover : ∀ o ∈ need, ∃ v ∈ S, o ∈ col v) :
    ∀ v ∈ S, ColumnAdmissible roots raw col need (label v) v := by
  intro v hv o ho outside
  obtain ⟨w, hw, how⟩ := cover o ho
  by_cases h : w = v
  · simpa only [h] using how
  obtain ⟨r, hr, hor⟩ := supports w hw o how
  have rRoot := part.1 w hw hr
  have notV : r ∉ label v := fun hrv =>
    Finset.disjoint_left.mp (part.2.1 w hw v hv h) hr hrv
  exact False.elim (outside r rRoot notV hor)

theorem liftLabels_disjoint {α : Type} [DecidableEq α] {A B : Finset α}
    (h : Disjoint A B) : Disjoint (liftLabels A) (liftLabels B) := by
  apply Finset.disjoint_left.mpr
  intro r hr hs
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hr
  have hb : a ∈ B := by simpa [liftLabels] using hs
  exact Finset.disjoint_left.mp h ha hb

theorem duplicate_admissible {α Ω : Type} [DecidableEq α]
    (roots : Finset α) (raw : α → Sig) (col : Sig → Set Ω) (need : Set Ω)
    {S : Finset Sig} {label : Sig → Finset α}
    (part : LabelPartition roots S label)
    (supports : ∀ v ∈ S, ColumnSupport raw col (label v) v)
    (cover : ∀ o ∈ need, ∃ v ∈ S, o ∈ col v)
    (w : Sig) (hw : w ∈ S) (v : Sig) (hv : v ∈ S) (hne : v ≠ w) :
    ColumnAdmissible (duplicateRoots roots (label w)) (duplicateRaw raw w) col need
      (liftLabels (label v)) v := by
  intro o ho outside
  obtain ⟨q, hq, hoq⟩ := cover o ho
  by_cases hqv : q = v
  · simpa only [hqv] using hoq
  by_cases hqw : q = w
  · subst q
    exact False.elim (outside (Sum.inr false) (by simp [duplicateRoots])
      (by simp [liftLabels]) (by simpa [duplicateRaw] using hoq))
  obtain ⟨r, hr, hor⟩ := supports q hq o hoq
  have rRoot := part.1 q hq hr
  have notA : r ∉ label w := fun hrw =>
    Finset.disjoint_left.mp (part.2.1 q hq w hw hqw) hr hrw
  have notB : r ∉ label v := fun hrv =>
    Finset.disjoint_left.mp (part.2.1 q hq v hv hqv) hr hrv
  have hnew : Sum.inl r ∈ duplicateRoots roots (label w) := by
    simp [duplicateRoots, liftLabels, rRoot, notA]
  have hout : Sum.inl r ∉ liftLabels (label v) := by simp [liftLabels, notB]
  exact False.elim (outside (Sum.inl r) hnew hout hor)

def sharingLabels {α : Type} [DecidableEq α] (label : Sig → Finset α)
    (a b z v : Sig) : Finset (Sum α Bool) :=
  if v = z then insert (Sum.inr true) (liftLabels (label b))
  else if v = a then {Sum.inr false} else liftLabels (label v)

theorem liftLabels_subset_duplicate {α : Type} [DecidableEq α]
    {roots A B : Finset α} (sub : B ⊆ roots) (disjoint : Disjoint A B) :
    liftLabels B ⊆ duplicateRoots roots A := by
  intro q hq
  obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hq
  have rRoot := sub hr
  have notA : r ∉ A := fun h => Finset.disjoint_left.mp disjoint h hr
  simp [duplicateRoots, liftLabels, rRoot, notA]

theorem sharing_partition {α : Type} [DecidableEq α]
    (roots : Finset α) (U : Finset Sig) (a b z : Sig) (label : Sig → Finset α)
    (hab : a ≠ b) (fresh : z ∉ insert a (insert b U)) (ha : a ∈ U) (hb : b ∉ U)
    (part : LabelPartition roots (insert a (insert b U)) label) :
    LabelPartition (duplicateRoots roots (label a)) (insert z U)
      (sharingLabels label a b z) := by
  classical
  let next := sharingLabels label a b z
  have memA : a ∈ insert a (insert b U) := by simp
  have memB : b ∈ insert a (insert b U) := by simp
  have memU (v : Sig) (hv : v ∈ U) : v ∈ insert a (insert b U) := by simp [hv]
  have notU : z ∉ U := fun hz => fresh (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hz))
  have anz : a ≠ z := by
    intro h
    exact fresh (Finset.mem_insert.mpr (Or.inl h.symm))
  have nextZ : next z = insert (Sum.inr true) (liftLabels (label b)) := by
    simp [next, sharingLabels]
  have nextA : next a = {Sum.inr false} := by simp [next, sharingLabels, anz]
  have nextU (v : Sig) (hv : v ∈ U) (hne : v ≠ a) : next v = liftLabels (label v) := by
    have hnz : v ≠ z := by rintro rfl; exact notU hv
    simp [next, sharingLabels, hnz, hne]
  have bne (v : Sig) (hv : v ∈ U) : b ≠ v := by rintro rfl; exact hb hv
  have disjointZ (v : Sig) (hv : v ∈ U) : Disjoint (next z) (next v) := by
    by_cases h : v = a
    · subst v
      rw [nextZ, nextA]
      apply Finset.disjoint_left.mpr
      intro q hq hqa
      have eq := Finset.mem_singleton.mp hqa
      subst q
      simpa [liftLabels] using hq
    · rw [nextZ, nextU v hv h]
      apply Finset.disjoint_left.mpr
      intro q hq hqv
      rcases Finset.mem_insert.mp hq with rfl | hq
      · simpa [liftLabels] using hqv
      · exact Finset.disjoint_left.mp
          (liftLabels_disjoint (part.2.1 b memB v (memU v hv) (bne v hv))) hq hqv
  have disjointA (v : Sig) (hv : v ∈ U) (hne : v ≠ a) :
      Disjoint (next a) (next v) := by
    rw [nextA, nextU v hv hne]
    apply Finset.disjoint_left.mpr
    intro q hq hqv
    have eq := Finset.mem_singleton.mp hq
    subst q
    simpa [liftLabels] using hqv
  change LabelPartition (duplicateRoots roots (label a)) (insert z U) next
  refine ⟨?_, ?_, ?_⟩
  · intro v hv
    rcases Finset.mem_insert.mp hv with rfl | hv
    · rw [nextZ]
      intro q hq
      rcases Finset.mem_insert.mp hq with rfl | hq
      · simp [duplicateRoots]
      · exact liftLabels_subset_duplicate (part.1 b memB) (part.2.1 a memA b memB hab) hq
    · by_cases h : v = a
      · subst v
        rw [nextA]
        intro q hq
        have eq := Finset.mem_singleton.mp hq
        subst q
        simp [duplicateRoots]
      · rw [nextU v hv h]
        exact liftLabels_subset_duplicate (part.1 v (memU v hv))
          (part.2.1 a memA v (memU v hv) (Ne.symm h))
  · intro v hv w hw hne
    by_cases hvz : v = z
    · subst v
      have hwU : w ∈ U := (Finset.mem_insert.mp hw).resolve_left (Ne.symm hne)
      exact disjointZ w hwU
    · have hvU : v ∈ U := (Finset.mem_insert.mp hv).resolve_left hvz
      by_cases hwz : w = z
      · subst w
        exact (disjointZ v hvU).symm
      · have hwU : w ∈ U := (Finset.mem_insert.mp hw).resolve_left hwz
        by_cases hva : v = a
        · subst v
          exact disjointA w hwU (Ne.symm hne)
        · by_cases hwa : w = a
          · subst w
            exact (disjointA v hvU hva).symm
          · rw [nextU v hvU hva, nextU w hwU hwa]
            exact liftLabels_disjoint (part.2.1 v (memU v hvU) w (memU w hwU) hne)
  · intro q hq
    rcases Finset.mem_union.mp hq with hq | hq
    · obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hq
      have rRoot := (Finset.mem_sdiff.mp hr).1
      have notA := (Finset.mem_sdiff.mp hr).2
      obtain ⟨v, hv, hrv⟩ := part.2.2 r rRoot
      rcases Finset.mem_insert.mp hv with rfl | hv
      · exact False.elim (notA hrv)
      rcases Finset.mem_insert.mp hv with rfl | hv
      · refine ⟨z, by simp, ?_⟩
        rw [nextZ]
        exact Finset.mem_insert_of_mem (Finset.mem_image_of_mem Sum.inl hrv)
      · have hna : v ≠ a := by rintro rfl; exact notA hrv
        refine ⟨v, Finset.mem_insert_of_mem hv, ?_⟩
        rw [nextU v hv hna]
        exact Finset.mem_image_of_mem Sum.inl hrv
    · simp only [Finset.mem_insert, Finset.mem_singleton] at hq
      rcases hq with rfl | rfl
      · exact ⟨a, Finset.mem_insert_of_mem ha, nextA.symm ▸ (by simp)⟩
      · exact ⟨z, by simp, nextZ.symm ▸ (by simp)⟩

theorem sharing_support {α Ω : Type} [DecidableEq α]
    (raw : α → Sig) (col : Sig → Set Ω) (u : Bool)
    (gateCol : ∀ d a b, allowed u d → col (bin d a b) ⊆ col a ∪ col b)
    (U : Finset Sig) (a b : Sig) (d : Nat) (hd : allowed u d)
    (fresh : bin d a b ∉ insert a (insert b U))
    (label : Sig → Finset α)
    (supports : ∀ v ∈ insert a (insert b U), ColumnSupport raw col (label v) v) :
    ∀ v ∈ insert (bin d a b) U,
      ColumnSupport (duplicateRaw raw a) col (sharingLabels label a b (bin d a b) v) v := by
  classical
  intro v hv
  rcases Finset.mem_insert.mp hv with rfl | hv
  · simp only [sharingLabels, if_pos rfl]
    intro o ho
    rcases gateCol d a b hd ho with ho | ho
    · exact ⟨Sum.inr true, by simp, ho⟩
    · obtain ⟨r, hr, hor⟩ := supports b (by simp) o ho
      exact ⟨Sum.inl r, Finset.mem_insert_of_mem (Finset.mem_image_of_mem Sum.inl hr), hor⟩
  · have hnz : v ≠ bin d a b := by
      rintro rfl
      exact fresh (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hv))
    by_cases hva : v = a
    · subst v
      simp only [sharingLabels, if_neg hnz, if_pos rfl]
      intro o ho
      exact ⟨Sum.inr false, by simp, ho⟩
    · simp only [sharingLabels, if_neg hnz, if_neg hva]
      intro o ho
      obtain ⟨r, hr, hor⟩ := supports v (by simp [hv]) o ho
      exact ⟨Sum.inl r, Finset.mem_image_of_mem Sum.inl hr, hor⟩

theorem merge_partition_frame {α Ω : Type} [DecidableEq α]
    (roots : Finset α) (raw : α → Sig) (col : Sig → Set Ω) (u : Bool)
    (gateCol : ∀ d a b, allowed u d → col (bin d a b) ⊆ col a ∪ col b)
    (U : Finset Sig) (a b : Sig) (d : Nat) (hd : allowed u d) (hab : a ≠ b)
    (hfresh : bin d a b ∉ insert a (insert b U)) (ha : a ∉ U) (hb : b ∉ U)
    (label : Sig → Finset α) (part : LabelPartition roots (insert a (insert b U)) label)
    (supports : ∀ v ∈ insert a (insert b U), ColumnSupport raw col (label v) v) :
    ∃ next : Sig → Finset α, LabelPartition roots (insert (bin d a b) U) next ∧
      (∀ v ∈ insert (bin d a b) U, ColumnSupport raw col (next v) v) ∧
      next (bin d a b) = label a ∪ label b ∧ (∀ v ∈ U, next v = label v) := by
  classical
  let z := bin d a b
  have fresh : z ∉ U :=
    fun h => hfresh (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem h))
  have memA : a ∈ insert a (insert b U) := by simp
  have memB : b ∈ insert a (insert b U) := by simp
  have memU (v : Sig) (hv : v ∈ U) : v ∈ insert a (insert b U) := by simp [hv]
  have differentA (v : Sig) (hv : v ∈ U) : a ≠ v := by
    rintro rfl
    exact ha hv
  have differentB (v : Sig) (hv : v ∈ U) : b ≠ v := by
    rintro rfl
    exact hb hv
  let next := Function.update label z (label a ∪ label b)
  have nextZ : next z = label a ∪ label b := by simp [next]
  have nextU (v : Sig) (hv : v ∈ U) : next v = label v := by
    have ne : v ≠ z := by rintro rfl; exact fresh hv
    simp [next, ne]
  have partNext : LabelPartition roots (insert z U) next := by
    refine ⟨?_, ?_, ?_⟩
    · intro v hv
      rcases Finset.mem_insert.mp hv with rfl | hv
      · rw [nextZ]
        exact Finset.union_subset (part.1 a memA) (part.1 b memB)
      · rw [nextU v hv]
        exact part.1 v (memU v hv)
    · intro v hv w hw hne
      rcases Finset.mem_insert.mp hv with rfl | hv <;>
        rcases Finset.mem_insert.mp hw with rfl | hw
      · exact False.elim (hne rfl)
      · rw [nextZ, nextU w hw]
        exact Finset.disjoint_union_left.mpr
          ⟨part.2.1 a memA w (memU w hw) (differentA w hw),
           part.2.1 b memB w (memU w hw) (differentB w hw)⟩
      · rw [nextU v hv, nextZ]
        exact Finset.disjoint_union_right.mpr
          ⟨part.2.1 v (memU v hv) a memA (differentA v hv).symm,
           part.2.1 v (memU v hv) b memB (differentB v hv).symm⟩
      · rw [nextU v hv, nextU w hw]
        exact part.2.1 v (memU v hv) w (memU w hw) hne
    · intro r hr
      obtain ⟨v, hv, hrv⟩ := part.2.2 r hr
      rcases Finset.mem_insert.mp hv with rfl | hv
      · exact ⟨z, by simp, nextZ.symm ▸ Finset.mem_union_left _ hrv⟩
      rcases Finset.mem_insert.mp hv with rfl | hv
      · exact ⟨z, by simp, nextZ.symm ▸ Finset.mem_union_right _ hrv⟩
      exact ⟨v, by simp [hv], (nextU v hv).symm ▸ hrv⟩
  have supportsNext : ∀ v ∈ insert z U, ColumnSupport raw col (next v) v := by
    intro v hv
    rcases Finset.mem_insert.mp hv with rfl | hv
    · rw [nextZ]
      intro o ho
      rcases gateCol d a b hd ho with ho | ho
      · obtain ⟨r, hr, hor⟩ := supports a memA o ho
        exact ⟨r, Finset.mem_union_left _ hr, hor⟩
      · obtain ⟨r, hr, hor⟩ := supports b memB o ho
        exact ⟨r, Finset.mem_union_right _ hr, hor⟩
    · simpa only [nextU v hv] using supports v (memU v hv)
  exact ⟨next, partNext, supportsNext, nextZ, nextU⟩


def doubleSharingLabels {α : Type} [DecidableEq α] (label : Sig → Finset α)
    (a b z v : Sig) : Finset (Sum (Sum α Bool) Bool) :=
  if v = z then {Sum.inl (Sum.inr true), Sum.inr true}
  else if v = a then {Sum.inl (Sum.inr false)}
  else if v = b then {Sum.inr false}
  else liftLabels (liftLabels (label v))

lemma double_sharing_partition {α : Type} [DecidableEq α]
    (roots : Finset α) (U : Finset Sig) (a b z : Sig) (label : Sig → Finset α)
    (hab : a ≠ b) (fresh : z ∉ insert a (insert b U)) (ha : a ∈ U) (hb : b ∈ U)
    (part : LabelPartition roots (insert a (insert b U)) label) :
    LabelPartition (duplicateRoots (duplicateRoots roots (label a)) (liftLabels (label b)))
      (insert z U) (doubleSharingLabels label a b z) := by
  classical
  let next := doubleSharingLabels label a b z
  have memA : a ∈ insert a (insert b U) := by simp
  have memB : b ∈ insert a (insert b U) := by simp
  have memU (v : Sig) (hv : v ∈ U) : v ∈ insert a (insert b U) := by simp [hv]
  have notU : z ∉ U := fun hz => fresh (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hz))
  have anz : a ≠ z := by intro h; exact fresh (h ▸ memA)
  have bnz : b ≠ z := by intro h; exact fresh (h ▸ memB)
  have nextZ : next z = {Sum.inl (Sum.inr true), Sum.inr true} := by
    simp [next, doubleSharingLabels]
  have nextA : next a = {Sum.inl (Sum.inr false)} := by
    simp [next, doubleSharingLabels, anz]
  have nextB : next b = {Sum.inr false} := by
    simp [next, doubleSharingLabels, bnz, hab.symm]
  have nextU (v : Sig) (hv : v ∈ U) (hna : v ≠ a) (hnb : v ≠ b) :
      next v = liftLabels (liftLabels (label v)) := by
    have hnz : v ≠ z := by rintro rfl; exact notU hv
    simp [next, doubleSharingLabels, hnz, hna, hnb]
  have disjointZ (v : Sig) (hv : v ∈ U) : Disjoint (next z) (next v) := by
    by_cases hna : v = a
    · subst v; rw [nextZ, nextA]; simp
    by_cases hnb : v = b
    · subst v; rw [nextZ, nextB]; simp
    rw [nextZ, nextU v hv hna hnb]
    simp [liftLabels, Finset.disjoint_left]
  have disjointA (v : Sig) (hv : v ∈ U) (hna : v ≠ a) : Disjoint (next a) (next v) := by
    by_cases hnb : v = b
    · subst v; rw [nextA, nextB]; simp
    rw [nextA, nextU v hv hna hnb]
    simp [liftLabels, Finset.disjoint_left]
  have disjointB (v : Sig) (hv : v ∈ U) (hna : v ≠ a) (hnb : v ≠ b) :
      Disjoint (next b) (next v) := by
    rw [nextB, nextU v hv hna hnb]
    simp [liftLabels, Finset.disjoint_left]
  change LabelPartition _ (insert z U) next
  refine ⟨?_, ?_, ?_⟩
  · intro v hv
    rcases Finset.mem_insert.mp hv with rfl | hv
    · rw [nextZ]
      intro q hq
      simp only [Finset.mem_insert, Finset.mem_singleton] at hq
      rcases hq with rfl | rfl <;> simp [duplicateRoots, liftLabels]
    by_cases hna : v = a
    · subst v; rw [nextA]; simp [duplicateRoots, liftLabels]
    by_cases hnb : v = b
    · subst v; rw [nextB]; simp [duplicateRoots]
    rw [nextU v hv hna hnb]
    exact liftLabels_subset_duplicate
      (liftLabels_subset_duplicate (part.1 v (memU v hv))
        (part.2.1 a memA v (memU v hv) (Ne.symm hna)))
      (liftLabels_disjoint (part.2.1 b memB v (memU v hv) (Ne.symm hnb)))
  · intro v hv w hw hne
    by_cases hvz : v = z
    · subst v
      exact disjointZ w ((Finset.mem_insert.mp hw).resolve_left hne.symm)
    have hvU : v ∈ U := (Finset.mem_insert.mp hv).resolve_left hvz
    by_cases hwz : w = z
    · subst w; exact (disjointZ v hvU).symm
    have hwU : w ∈ U := (Finset.mem_insert.mp hw).resolve_left hwz
    by_cases hva : v = a
    · subst v; exact disjointA w hwU hne.symm
    by_cases hwa : w = a
    · subst w; exact (disjointA v hvU hva).symm
    by_cases hvb : v = b
    · subst v; exact disjointB w hwU hwa hne.symm
    by_cases hwb : w = b
    · subst w; exact (disjointB v hvU hva hvb).symm
    rw [nextU v hvU hva hvb, nextU w hwU hwa hwb]
    exact liftLabels_disjoint (liftLabels_disjoint
      (part.2.1 v (memU v hvU) w (memU w hwU) hne))
  · intro q hq
    rcases Finset.mem_union.mp hq with hq | hq
    · obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hq
      have pRoot := (Finset.mem_sdiff.mp hp).1
      have notB := (Finset.mem_sdiff.mp hp).2
      rcases Finset.mem_union.mp pRoot with pRoot | pRoot
      · obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp pRoot
        have rRoot := (Finset.mem_sdiff.mp hr).1
        have notA := (Finset.mem_sdiff.mp hr).2
        have rnotB : r ∉ label b := by simpa [liftLabels] using notB
        obtain ⟨v, hv, hrv⟩ := part.2.2 r rRoot
        have hna : v ≠ a := by rintro rfl; exact notA hrv
        have hnb : v ≠ b := by rintro rfl; exact rnotB hrv
        have hvU : v ∈ U := by simpa [hna, hnb] using hv
        refine ⟨v, Finset.mem_insert_of_mem hvU, ?_⟩
        rw [nextU v hvU hna hnb]
        exact Finset.mem_image_of_mem Sum.inl (Finset.mem_image_of_mem Sum.inl hrv)
      · simp only [Finset.mem_insert, Finset.mem_singleton] at pRoot
        rcases pRoot with rfl | rfl
        · exact ⟨a, Finset.mem_insert_of_mem ha, nextA.symm ▸ (by simp)⟩
        · exact ⟨z, by simp, nextZ.symm ▸ (by simp)⟩
    · simp only [Finset.mem_insert, Finset.mem_singleton] at hq
      rcases hq with rfl | rfl
      · exact ⟨b, Finset.mem_insert_of_mem hb, nextB.symm ▸ (by simp)⟩
      · exact ⟨z, by simp, nextZ.symm ▸ (by simp)⟩

lemma double_sharing_support {α Ω : Type} [DecidableEq α]
    (raw : α → Sig) (col : Sig → Set Ω) (u : Bool)
    (gateCol : ∀ d a b, allowed u d → col (bin d a b) ⊆ col a ∪ col b)
    (U : Finset Sig) (a b : Sig) (d : Nat) (hd : allowed u d)
    (fresh : bin d a b ∉ insert a (insert b U))
    (label : Sig → Finset α)
    (supports : ∀ v ∈ insert a (insert b U), ColumnSupport raw col (label v) v) :
    ∀ v ∈ insert (bin d a b) U,
      ColumnSupport (duplicateRaw (duplicateRaw raw a) b) col
        (doubleSharingLabels label a b (bin d a b) v) v := by
  classical
  intro v hv
  rcases Finset.mem_insert.mp hv with rfl | hv
  · simp only [doubleSharingLabels, if_pos rfl]
    intro o ho
    rcases gateCol d a b hd ho with ho | ho
    · exact ⟨Sum.inl (Sum.inr true), by simp, ho⟩
    · exact ⟨Sum.inr true, by simp, ho⟩
  have hnz : v ≠ bin d a b := by
    rintro rfl
    exact fresh (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hv))
  by_cases hva : v = a
  · subst v
    simp only [doubleSharingLabels, if_neg hnz, if_pos rfl]
    intro o ho
    exact ⟨Sum.inl (Sum.inr false), by simp, ho⟩
  by_cases hvb : v = b
  · subst v
    simp only [doubleSharingLabels, if_neg hnz, if_neg hva, if_pos rfl]
    intro o ho
    exact ⟨Sum.inr false, by simp, ho⟩
  simp only [doubleSharingLabels, if_neg hnz, if_neg hva, if_neg hvb]
  intro o ho
  obtain ⟨r, hr, hor⟩ := supports v (by simp [hv]) o ho
  exact ⟨Sum.inl (Sum.inl r),
    Finset.mem_image_of_mem Sum.inl (Finset.mem_image_of_mem Sum.inl hr), hor⟩

theorem first_copy_run_general {u : Bool} {T a b : Sig} {k d : Nat} {U : Finset Sig}
    (tail : Live u T k (insert (bin d a b) U)) (hd : allowed u d)
    (fresh : bin d a b ∉ insert b U) :
    Run u (observe T) (k + 1)
      ((insert (bin d a b) (insert b U)).toList.map
        (fun v => observe (if v = bin d a b then a else v))) := by
  classical
  have freshU : bin d a b ∉ U := fun h => fresh (Finset.mem_insert_of_mem h)
  by_cases hb : b ∈ U
  · simpa only [Finset.insert_eq_of_mem hb] using first_copy_run tail hd hb freshU
  · let z := bin d a b
    let value : Sig → Sig := fun v => if v = z then a else v
    have zb : z ≠ b := fun h => fresh (Finset.mem_insert.mpr (Or.inl h))
    have zr : z ∉ U.toList := fun h => freshU (Finset.mem_toList.mp h)
    have br : b ∉ U.toList := fun h => hb (Finset.mem_toList.mp h)
    have nd : (z :: b :: U.toList).Nodup := by
      simp [zb, zr, br, Finset.nodup_toList]
    have progress := list_run tail (z :: U.toList)
      (List.nodup_cons.mpr ⟨zr, Finset.nodup_toList U⟩) (by simp [z])
    have finish : Run u (observe T) (k + 1)
        (observe a :: observe b :: U.toList.map observe) :=
      Run.two d hd false false (by simpa [kept, z, obs_bin] using progress)
    have untouched (v : Sig) (hv : v ∈ U) : value v = v := by
      have vz : v ≠ z := fun h =>
        freshU (Eq.mp (congrArg (fun v : Sig => v ∈ U) h) hv)
      simp [value, vz]
    have mappedRest : U.toList.map (fun v => observe (value v)) = U.toList.map observe := by
      apply List.map_congr_left
      intro v hv
      rw [untouched v (Finset.mem_toList.mp hv)]
    have source : Run u (observe T) (k + 1)
        ((z :: b :: U.toList).map (fun v => observe (value v))) := by
      simpa only [List.map_cons, show value z = a by simp [value],
        show value b = b by simp [value, Ne.symm zb], mappedRest] using finish
    have perm : (z :: b :: U.toList).Perm (insert z (insert b U)).toList := by
      apply List.perm_of_nodup_nodup_toFinset_eq nd (Finset.nodup_toList _)
      simp
    exact Run.perm (perm.map (fun v => observe (value v))) source

end PEqualNP.Outside.L_meta_2373.Live1024

namespace PEqualNP.Outside.L_meta_2373.Live1024

theorem pruned_bridge_live_copy {α Ω : Type} [DecidableEq α]
    (roots : Finset α) (raw : α → Sig) (col : Sig → Set Ω) (need : Set Ω)
    (Cert : Finset α → Sig → Prop) (Cert2 : Finset (Sum α Bool) → Sig → Prop)
    (u : Bool) (T : Sig) (depth : Nat)
    (rowCover : ∀ k S, Live u T k S → ∀ o ∈ need, ∃ v ∈ S, o ∈ col v)
    (U : Finset Sig) (a b : Sig) (d k : Nat) (label : Sig → Finset α)
    (hd : allowed u d) (pa : proper a) (pb : proper b) (hab : a ≠ b)
    (fresh : bin d a b ∉ insert a (insert b U)) (ha : a ∈ U)
    (tail : Live u T k (insert (bin d a b) U))
    (cap : k + 2 ≤ (insert a (insert b U)).card + (depth + 1))
    (part : LabelPartition roots (insert a (insert b U)) label)
    (entries : ∀ v ∈ insert a (insert b U), Cert (label v) v)
    (traces : ∀ v ∈ insert a (insert b U), ReadOnce raw u (label v) v)
    (supports : ∀ v ∈ insert a (insert b U), ColumnSupport raw col (label v) v)
    (bridge : PrunedBridge roots raw col need Cert Cert2 u T depth (label a) a) :
    ∀ v ∈ insert a (insert b U), v ≠ a → Cert2 (liftLabels (label v)) v := by
  intro v hv hne
  have memA : a ∈ insert a (insert b U) := by simp
  have preRun : Live u T (k + 1) (insert a (insert b U)) :=
    Live.binary hd pa pb hab fresh tail
  have adm := duplicate_admissible roots raw col need part supports
    (rowCover (k + 1) _ preRun) a memA v hv hne
  rcases bridge (label v) v (entries v hv) (part.2.1 a memA v hv (Ne.symm hne)) adm with found | cut
  · exact found
  · exfalso
    have part2 := copy_input_partition roots (insert a (insert b U)) label a (bin d a b)
      part memA fresh
    have traces2 := copy_input_readOnce raw u (insert a (insert b U)) label a (bin d a b)
      fresh traces
    have source := first_copy_run_general tail hd
      (fun h => fresh (Finset.mem_insert_of_mem h))
    have same : insert a (insert b U) = insert b U :=
      Finset.insert_eq_of_mem (Finset.mem_insert_of_mem ha)
    have source2 : Run u (observe T) (k + 1)
        ((insert (bin d a b) (insert a (insert b U))).toList.map
          (fun w => observe (if w = bin d a b then a else w))) := by
      simpa only [same] using source
    have vz : v ≠ bin d a b := by
      intro h
      exact fresh (Eq.mp (congrArg (fun w : Sig => w ∈ insert a (insert b U)) h) hv)
    have cap2 : k + 1 + 1 ≤ (insert (bin d a b) (insert a (insert b U))).card + depth := by
      rw [Finset.card_insert_of_notMem fresh]
      omega
    apply compressed_indexed_forest_exclusion
      (duplicateRoots roots (label a)) (duplicateRaw raw a) u T depth
      (fun w => if w = bin d a b then a else w) source2 cap2
      (copyInputLabels label a (bin d a b)) part2 traces2 v
      (Finset.mem_insert_of_mem hv)
    simpa [BudgetRunCut, copyInputLabels, vz, hne] using cut

end PEqualNP.Outside.L_meta_2373.Live1024

namespace PEqualNP.Outside.L_meta_2373.Live1024

theorem pruned_closed_live {α Ω : Type} [DecidableEq α]
    (roots : Finset α) (raw : α → Sig) (col : Sig → Set Ω) (need : Set Ω)
    (Cert : Finset α → Sig → Prop) (u : Bool) (T : Sig) (depth : Nat)
    (rowCover : ∀ k S, Live u T k S → ∀ o ∈ need, ∃ v ∈ S, o ∈ col v)
    (closed : PrunedGateClosed roots raw col need Cert u T depth)
    {k : Nat} {S : Finset Sig} (run : Live u T k S) (cap : k + 1 ≤ S.card + depth)
    (label : Sig → Finset α) (part : LabelPartition roots S label)
    (traces : ∀ v ∈ S, ReadOnce raw u (label v) v)
    (supports : ∀ v ∈ S, ColumnSupport raw col (label v) v)
    (A B : Finset α) (a b : Sig) (d : Nat)
    (disjoint : Disjoint A B) (hd : allowed u d) (hab : a ≠ b)
    (hza : bin d a b ≠ a) (hzb : bin d a b ≠ b)
    (ca : Cert A a) (cb : Cert B b) (hz : bin d a b ∈ S)
    (labels : label (bin d a b) = A ∪ B) : Cert (A ∪ B) (bin d a b) := by
  have admissible := partition_admissible roots raw col need part supports
    (rowCover k S run) (bin d a b) hz
  rw [labels] at admissible
  rcases closed A B a b d disjoint hd hab hza hzb
    (live_all_proper run _ hz) ca cb admissible with found | cut
  · exact found
  · exfalso
    apply compressed_wire_forest_exclusion roots raw u T depth run cap
      label part traces (bin d a b) hz
    simpa only [labels] using cut

theorem pruned_merge_transfer {α Ω : Type} [DecidableEq α]
    (roots : Finset α) (raw : α → Sig) (col : Sig → Set Ω) (need : Set Ω)
    (Cert : Finset α → Sig → Prop) (u : Bool) (T : Sig) (depth : Nat)
    (gateCol : ∀ d a b, allowed u d → col (bin d a b) ⊆ col a ∪ col b)
    (rowCover : ∀ k S, Live u T k S → ∀ o ∈ need, ∃ v ∈ S, o ∈ col v)
    (closed : PrunedGateClosed roots raw col need Cert u T depth)
    (U : Finset Sig) (a b : Sig) (d k : Nat) (label : Sig → Finset α)
    (hd : allowed u d) (hab : a ≠ b)
    (fresh : bin d a b ∉ insert a (insert b U)) (ha : a ∉ U) (hb : b ∉ U)
    (tail : Live u T k (insert (bin d a b) U))
    (cap : k + 1 ≤ (insert (bin d a b) U).card + depth)
    (part : LabelPartition roots (insert a (insert b U)) label)
    (entries : ∀ v ∈ insert a (insert b U), Cert (label v) v)
    (traces : ∀ v ∈ insert a (insert b U), ReadOnce raw u (label v) v)
    (supports : ∀ v ∈ insert a (insert b U), ColumnSupport raw col (label v) v) :
    ∃ next : Sig → Finset α,
      LabelPartition roots (insert (bin d a b) U) next ∧
      (∀ v ∈ insert (bin d a b) U, Cert (next v) v) ∧
      (∀ v ∈ insert (bin d a b) U, ReadOnce raw u (next v) v) ∧
      (∀ v ∈ insert (bin d a b) U, ColumnSupport raw col (next v) v) := by
  obtain ⟨next, pn, sn, nz, nu⟩ := merge_partition_frame roots raw col u gateCol
    U a b d hd hab fresh ha hb label part supports
  have ma : a ∈ insert a (insert b U) := by simp
  have mb : b ∈ insert a (insert b U) := by simp
  have disjoint := part.2.1 a ma b mb hab
  have tn : ∀ v ∈ insert (bin d a b) U, ReadOnce raw u (next v) v := by
    intro v hv
    rcases Finset.mem_insert.mp hv with eq | old
    · subst v
      rw [nz]
      exact ReadOnce.combine raw u (traces a ma) (traces b mb) disjoint d hd
    · rw [nu v old]
      exact traces v (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem old))
  have za : bin d a b ≠ a := fun eq => fresh (by simp [eq])
  have zb : bin d a b ≠ b := fun eq => fresh (by simp [eq])
  have generated := pruned_closed_live roots raw col need Cert u T depth rowCover closed
    tail cap next pn tn sn (label a) (label b) a b d disjoint hd hab za zb
    (entries a ma) (entries b mb) (by simp) nz
  refine ⟨next, pn, ?_, tn, sn⟩
  intro v hv
  rcases Finset.mem_insert.mp hv with eq | old
  · subst v
    simpa only [nz] using generated
  · rw [nu v old]
    exact entries v (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem old))

end PEqualNP.Outside.L_meta_2373.Live1024

namespace PEqualNP.Outside.L_meta_2373.Live1024

theorem sharing_readOnce {α : Type} [DecidableEq α]
    (raw : α → Sig) (u : Bool) (U : Finset Sig) (a b : Sig) (d : Nat)
    (hd : allowed u d) (fresh : bin d a b ∉ insert a (insert b U))
    (label : Sig → Finset α)
    (entries : ∀ v ∈ insert a (insert b U), ReadOnce raw u (label v) v) :
    ∀ v ∈ insert (bin d a b) U, ReadOnce (duplicateRaw raw a) u
      (sharingLabels label a b (bin d a b) v) v := by
  intro v hv
  by_cases vz : v = bin d a b
  · subst v
    have left : ReadOnce (duplicateRaw raw a) u {Sum.inr true} a :=
      ReadOnce.leaf (duplicateRaw raw a) u (Sum.inr true)
    have right := ReadOnce.map raw (duplicateRaw raw a) u Sum.inl
      (by intro x y h; cases h; rfl) (by intro r; rfl) (entries b (by simp))
    have disjoint : Disjoint ({Sum.inr true} : Finset (Sum α Bool)) (liftLabels (label b)) := by
      simp [liftLabels]
    simpa [sharingLabels, liftLabels, Finset.singleton_union] using
      ReadOnce.combine (duplicateRaw raw a) u left right disjoint d hd
  · have hvU : v ∈ U := (Finset.mem_insert.mp hv).resolve_left vz
    by_cases va : v = a
    · subst v
      simpa [sharingLabels, vz, duplicateRaw] using
        ReadOnce.leaf (duplicateRaw raw a) u (Sum.inr false)
    · have mapped := ReadOnce.map raw (duplicateRaw raw a) u Sum.inl
        (by intro x y h; cases h; rfl) (by intro r; rfl) (entries v (by simp [hvU]))
      simpa [sharingLabels, vz, va, liftLabels] using mapped

theorem double_sharing_readOnce {α : Type} [DecidableEq α]
    (raw : α → Sig) (u : Bool) (U : Finset Sig) (a b : Sig) (d : Nat)
    (hd : allowed u d) (fresh : bin d a b ∉ insert a (insert b U))
    (label : Sig → Finset α)
    (entries : ∀ v ∈ insert a (insert b U), ReadOnce raw u (label v) v) :
    ∀ v ∈ insert (bin d a b) U, ReadOnce (duplicateRaw (duplicateRaw raw a) b) u
      (doubleSharingLabels label a b (bin d a b) v) v := by
  let next := duplicateRaw (duplicateRaw raw a) b
  intro v hv
  by_cases vz : v = bin d a b
  · subst v
    have left : ReadOnce next u {Sum.inl (Sum.inr true)} a :=
      ReadOnce.leaf next u (Sum.inl (Sum.inr true))
    have right : ReadOnce next u {Sum.inr true} b :=
      ReadOnce.leaf next u (Sum.inr true)
    have disjoint : Disjoint ({Sum.inl (Sum.inr true)} : Finset (Sum (Sum α Bool) Bool))
        {Sum.inr true} := by simp
    simpa [doubleSharingLabels, next, Finset.singleton_union] using
      ReadOnce.combine next u left right disjoint d hd
  · have hvU : v ∈ U := (Finset.mem_insert.mp hv).resolve_left vz
    by_cases va : v = a
    · subst v
      simpa [doubleSharingLabels, vz, next, duplicateRaw] using
        ReadOnce.leaf next u (Sum.inl (Sum.inr false))
    · by_cases vb : v = b
      · subst v
        simpa [doubleSharingLabels, vz, va, next, duplicateRaw] using
          ReadOnce.leaf next u (Sum.inr false)
      · have first := ReadOnce.map raw (duplicateRaw raw a) u Sum.inl
          (by intro x y h; cases h; rfl) (by intro r; rfl) (entries v (by simp [hvU]))
        have second := ReadOnce.map (duplicateRaw raw a) next u Sum.inl
          (by intro x y h; cases h; rfl) (by intro r; rfl) first
        simpa [doubleSharingLabels, vz, va, vb, next, liftLabels] using second

end PEqualNP.Outside.L_meta_2373.Live1024

namespace PEqualNP.Outside.L_meta_2373.Live1024

theorem pruned_double_transfer {α Ω : Type} [DecidableEq α]
    (roots : Finset α) (raw : α → Sig) (col : Sig → Set Ω) (need : Set Ω)
    (Cert2 : Finset (Sum α Bool) → Sig → Prop)
    (Cert3 : Finset (Sum (Sum α Bool) Bool) → Sig → Prop)
    (u : Bool) (T : Sig) (depth : Nat)
    (gateCol : ∀ d a b, allowed u d → col (bin d a b) ⊆ col a ∪ col b)
    (rowCover : ∀ k S, Live u T k S → ∀ o ∈ need, ∃ v ∈ S, o ∈ col v)
    (U : Finset Sig) (a b : Sig) (d k : Nat) (label : Sig → Finset α)
    (hd : allowed u d) (hab : a ≠ b)
    (fresh : bin d a b ∉ insert a (insert b U)) (ha : a ∈ U) (hb : b ∈ U)
    (tail : Live u T k (insert (bin d a b) U))
    (cap : k + 1 ≤ (insert (bin d a b) U).card + depth)
    (part : LabelPartition roots (insert a (insert b U)) label)
    (entries2 : ∀ v ∈ insert a (insert b U), v ≠ a → Cert2 (liftLabels (label v)) v)
    (traces : ∀ v ∈ insert a (insert b U), ReadOnce raw u (label v) v)
    (supports : ∀ v ∈ insert a (insert b U), ColumnSupport raw col (label v) v)
    (initial3 : ∀ r ∈ duplicateRoots (duplicateRoots roots (label a)) (liftLabels (label b)),
      Cert3 {r} (duplicateRaw (duplicateRaw raw a) b r))
    (closed3 : PrunedGateClosed
      (duplicateRoots (duplicateRoots roots (label a)) (liftLabels (label b)))
      (duplicateRaw (duplicateRaw raw a) b) col need Cert3 u T depth)
    (bridge2 : PrunedBridge (duplicateRoots roots (label a)) (duplicateRaw raw a)
      col need Cert2 Cert3 u T depth (liftLabels (label b)) b) :
    LabelPartition
      (duplicateRoots (duplicateRoots roots (label a)) (liftLabels (label b)))
      (insert (bin d a b) U) (doubleSharingLabels label a b (bin d a b)) ∧
    (∀ v ∈ insert (bin d a b) U, Cert3 (doubleSharingLabels label a b (bin d a b) v) v) ∧
    (∀ v ∈ insert (bin d a b) U, ReadOnce (duplicateRaw (duplicateRaw raw a) b) u
      (doubleSharingLabels label a b (bin d a b) v) v) ∧
    (∀ v ∈ insert (bin d a b) U, ColumnSupport (duplicateRaw (duplicateRaw raw a) b) col
      (doubleSharingLabels label a b (bin d a b) v) v) := by
  have pn := double_sharing_partition roots U a b (bin d a b) label hab fresh ha hb part
  have tn := double_sharing_readOnce raw u U a b d hd fresh label traces
  have sn := double_sharing_support raw col u gateCol U a b d hd fresh label supports
  have admissible := partition_admissible _ _ col need pn sn (rowCover k _ tail)
  have za : bin d a b ≠ a := fun eq => fresh (by simp [eq])
  have zb : bin d a b ≠ b := fun eq => fresh (by simp [eq])
  have ca : Cert3 {Sum.inl (Sum.inr true)} a :=
    initial3 _ (by simp [duplicateRoots, liftLabels])
  have cb : Cert3 {Sum.inr true} b :=
    initial3 _ (by simp [duplicateRoots])
  have generated := pruned_closed_live _ _ col need Cert3 u T depth rowCover closed3
    tail cap _ pn tn sn {Sum.inl (Sum.inr true)} {Sum.inr true} a b d
    (by simp) hd hab za zb ca cb (by simp)
    (by simp [doubleSharingLabels, Finset.singleton_union])
  refine ⟨pn, ?_, tn, sn⟩
  intro v hv
  by_cases vz : v = bin d a b
  · subst v
    simpa [doubleSharingLabels, Finset.singleton_union] using generated
  have vu : v ∈ U := (Finset.mem_insert.mp hv).resolve_left vz
  by_cases va : v = a
  · subst v
    have leaf := initial3 (Sum.inl (Sum.inr false)) (by simp [duplicateRoots, liftLabels])
    simpa [doubleSharingLabels, vz, duplicateRaw] using leaf
  by_cases vb : v = b
  · subst v
    have leaf := initial3 (Sum.inr false) (by simp [duplicateRoots])
    simpa [doubleSharingLabels, vz, va, duplicateRaw] using leaf
  have old : v ∈ insert a (insert b U) := by simp [vu]
  have adm := admissible v hv
  simp only [doubleSharingLabels, if_neg vz, if_neg va, if_neg vb] at adm
  rcases bridge2 (liftLabels (label v)) v (entries2 v old va)
    (liftLabels_disjoint (part.2.1 b (by simp) v old (Ne.symm vb))) adm with found | cut
  · simpa [doubleSharingLabels, vz, va, vb] using found
  · exfalso
    apply compressed_wire_forest_exclusion _ _ u T depth tail cap _ pn tn v hv
    simpa only [doubleSharingLabels, if_neg vz, if_neg va, if_neg vb] using cut

end PEqualNP.Outside.L_meta_2373.Live1024

namespace PEqualNP.Outside.L_meta_2373.Live1024

theorem pruned_single_transfer {α Ω : Type} [DecidableEq α]
    (roots : Finset α) (raw : α → Sig) (col : Sig → Set Ω) (need : Set Ω)
    (Cert : Finset α → Sig → Prop) (Cert2 : Finset (Sum α Bool) → Sig → Prop)
    (u : Bool) (T : Sig) (depth : Nat)
    (gateCol : ∀ d a b, allowed u d → col (bin d a b) ⊆ col a ∪ col b)
    (rowCover : ∀ k S, Live u T k S → ∀ o ∈ need, ∃ v ∈ S, o ∈ col v)
    (U : Finset Sig) (a b : Sig) (d k : Nat) (label : Sig → Finset α)
    (hd : allowed u d) (pa : proper a) (pb : proper b) (hab : a ≠ b)
    (fresh : bin d a b ∉ insert a (insert b U)) (ha : a ∈ U) (hb : b ∉ U)
    (tail : Live u T k (insert (bin d a b) U))
    (cap : k + 1 ≤ (insert (bin d a b) U).card + depth)
    (part : LabelPartition roots (insert a (insert b U)) label)
    (entries : ∀ v ∈ insert a (insert b U), Cert (label v) v)
    (traces : ∀ v ∈ insert a (insert b U), ReadOnce raw u (label v) v)
    (supports : ∀ v ∈ insert a (insert b U), ColumnSupport raw col (label v) v)
    (bridge : PrunedBridge roots raw col need Cert Cert2 u T depth (label a) a)
    (initial : ∀ r ∈ duplicateRoots roots (label a), Cert2 {r} (duplicateRaw raw a r))
    (closed : PrunedGateClosed (duplicateRoots roots (label a)) (duplicateRaw raw a)
      col need Cert2 u T depth) :
    ∃ next : Sig → Finset (Sum α Bool),
      LabelPartition (duplicateRoots roots (label a)) (insert (bin d a b) U) next ∧
      (∀ v ∈ insert (bin d a b) U, Cert2 (next v) v) ∧
      (∀ v ∈ insert (bin d a b) U, ReadOnce (duplicateRaw raw a) u (next v) v) ∧
      (∀ v ∈ insert (bin d a b) U, ColumnSupport (duplicateRaw raw a) col (next v) v) := by
  let next := sharingLabels label a b (bin d a b)
  have pn := sharing_partition roots U a b (bin d a b) label hab fresh ha hb part
  have tn := sharing_readOnce raw u U a b d hd fresh label traces
  have sn := sharing_support raw col u gateCol U a b d hd fresh label supports
  have notU : bin d a b ∉ U := fun h => fresh (by simp [h])
  have oldEq : insert a (insert b U) = insert b U :=
    Finset.insert_eq_of_mem (Finset.mem_insert_of_mem ha)
  have oldCap : k + 2 ≤ (insert a (insert b U)).card + (depth + 1) := by
    rw [oldEq, Finset.card_insert_of_notMem hb]
    rw [Finset.card_insert_of_notMem notU] at cap
    omega
  have lifted := pruned_bridge_live_copy roots raw col need Cert Cert2 u T depth rowCover
    U a b d k label hd pa pb hab fresh ha tail oldCap part entries traces supports bridge
  have leaf (t : Bool) : Cert2 {Sum.inr t} a := by
    simpa [duplicateRaw] using initial (Sum.inr t) (by cases t <;> simp [duplicateRoots])
  have disjoint : Disjoint ({Sum.inr true} : Finset (Sum α Bool)) (liftLabels (label b)) := by
    simp [liftLabels]
  have nz : next (bin d a b) = {Sum.inr true} ∪ liftLabels (label b) := by
    simp [next, sharingLabels, Finset.singleton_union]
  have za : bin d a b ≠ a := fun h => fresh (by simp [h])
  have zb : bin d a b ≠ b := fun h => fresh (by simp [h])
  have generated := pruned_closed_live
    (duplicateRoots roots (label a)) (duplicateRaw raw a) col need Cert2 u T depth
    rowCover closed tail cap next pn tn sn {Sum.inr true} (liftLabels (label b)) a b d
    disjoint hd hab za zb (leaf true) (lifted b (by simp) hab.symm) (by simp) nz
  refine ⟨next, pn, ?_, tn, sn⟩
  intro v hv
  rcases Finset.mem_insert.mp hv with vz | hv
  · subst v
    simpa only [nz] using generated
  · have vz : v ≠ bin d a b := by intro h; subst v; exact notU hv
    by_cases va : v = a
    · subst v
      simpa [next, sharingLabels, vz] using leaf false
    · simpa [next, sharingLabels, vz, va] using lifted v (by simp [hv]) va

end PEqualNP.Outside.L_meta_2373.Live1024

namespace PEqualNP.Outside.L_meta_2373.Live1024

theorem PrunedNode.initial {α Ω : Type} [DecidableEq α]
    {col : Sig → Set Ω} {need : Set Ω} {u : Bool} {T : Sig}
    {depth : Nat} {roots : Finset α} {raw : α → Sig} {Cert : Finset α → Sig → Prop}
    (node : PrunedNode col need u T depth α roots raw Cert) :
    ∀ r ∈ roots, Cert {r} (raw r) := by
  cases depth <;> exact node.1

theorem PrunedNode.closed {α Ω : Type} [DecidableEq α]
    {col : Sig → Set Ω} {need : Set Ω} {u : Bool} {T : Sig}
    {depth : Nat} {roots : Finset α} {raw : α → Sig} {Cert : Finset α → Sig → Prop}
    (node : PrunedNode col need u T depth α roots raw Cert) :
    PrunedGateClosed roots raw col need Cert u T depth := by
  cases depth <;> exact node.2.1

theorem PrunedNode.missing {α Ω : Type} [DecidableEq α]
    {col : Sig → Set Ω} {need : Set Ω} {u : Bool} {T : Sig}
    {depth : Nat} {roots : Finset α} {raw : α → Sig} {Cert : Finset α → Sig → Prop}
    (node : PrunedNode col need u T depth α roots raw Cert) : ¬ Cert roots T := by
  cases depth <;> exact node.2.2.1

theorem PrunedNode.copies {α Ω : Type} [DecidableEq α]
    {col : Sig → Set Ω} {need : Set Ω} {u : Bool} {T : Sig}
    {depth : Nat} {roots : Finset α} {raw : α → Sig} {Cert : Finset α → Sig → Prop}
    (node : PrunedNode col need u T (depth + 1) α roots raw Cert) :
    ∀ A w, A ⊆ roots → proper w → Cert A w →
      BudgetRunCut (duplicateRoots roots A) (duplicateRaw raw w) u T depth ∨
      ∃ Cert2 : Finset (Sum α Bool) → Sig → Prop,
        PrunedBridge roots raw col need Cert Cert2 u T depth A w ∧
        PrunedNode col need u T depth (Sum α Bool)
          (duplicateRoots roots A) (duplicateRaw raw w) Cert2 := node.2.2.2

theorem pruned_node_exclusion_state {Ω : Type}
    (col : Sig → Set Ω) (need : Set Ω) (u : Bool) (T : Sig)
    (gateCol : ∀ d a b, allowed u d → col (bin d a b) ⊆ col a ∪ col b)
    (rowCover : ∀ k S, Live u T k S → ∀ o ∈ need, ∃ v ∈ S, o ∈ col v)
    (k : Nat) :
    ∀ (α : Type) [DecidableEq α] (roots : Finset α) (raw : α → Sig)
      (Cert : Finset α → Sig → Prop) (depth : Nat),
      PrunedNode col need u T depth α roots raw Cert →
      ∀ (S : Finset Sig), Live u T k S → k + 1 ≤ S.card + depth →
      ∀ (label : Sig → Finset α), LabelPartition roots S label →
      (∀ v ∈ S, Cert (label v) v) →
      (∀ v ∈ S, ReadOnce raw u (label v) v) →
      (∀ v ∈ S, ColumnSupport raw col (label v) v) → False := by
  induction k with
  | zero =>
    intro α inst roots raw Cert depth node S run cap label part entries traces supports
    obtain ⟨rfl, hp⟩ := run
    have labels : label T = roots := by
      apply Finset.Subset.antisymm (part.1 T (by simp))
      intro r hr
      obtain ⟨v, hv, hrv⟩ := part.2.2 r hr
      have eq : v = T := by simpa using hv
      simpa only [eq] using hrv
    exact node.missing (labels ▸ entries T (by simp))
  | succ k ih =>
    intro α inst roots raw Cert depth node S run cap label part entries traces supports
    have retained : ∀ (U : Finset Sig) (a b : Sig) (d : Nat),
        allowed u d → proper a → proper b → a ≠ b →
        bin d a b ∉ insert a (insert b U) → a ∈ U →
        Live u T k (insert (bin d a b) U) →
        k + 2 ≤ (insert a (insert b U)).card + depth →
        LabelPartition roots (insert a (insert b U)) label →
        (∀ v ∈ insert a (insert b U), Cert (label v) v) →
        (∀ v ∈ insert a (insert b U), ReadOnce raw u (label v) v) →
        (∀ v ∈ insert a (insert b U), ColumnSupport raw col (label v) v) → False := by
      intro U a b d hd pa pb hab fresh ha tail cap part entries traces supports
      have notU : bin d a b ∉ U := fun h =>
        fresh (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem h))
      have ma : a ∈ insert a (insert b U) := by simp
      have mb : b ∈ insert a (insert b U) := by simp
      have oldEq : insert a (insert b U) = insert b U :=
        Finset.insert_eq_of_mem (Finset.mem_insert_of_mem ha)
      have bound := live_card_bound tail
      rw [Finset.card_insert_of_notMem notU] at bound
      have oldBound : (insert a (insert b U)).card ≤ U.card + 1 := by
        rw [oldEq]
        exact Finset.card_insert_le b U
      cases depth with
      | zero => omega
      | succ n =>
        have children := node.copies
        rcases children (label a) a (part.1 a ma) pa (entries a ma) with cut | next
        · by_cases hb : b ∈ U
          · have oldU : insert a (insert b U) = U := by simp [ha, hb]
            apply first_copy_forest_exclusion roots raw u T n tail hd ha hb notU
              (by rw [oldU] at cap; omega) label
              (by simpa only [oldU] using part)
              (by simpa only [oldU] using traces) cut
          · have pn := sharing_partition roots U a b (bin d a b) label hab fresh ha hb part
            have tn := sharing_readOnce raw u U a b d hd fresh label traces
            apply readOnce_forest_exclusion_state _ _ u T n cut tail ?_
              (sharingLabels label a b (bin d a b)) pn tn
            rw [Finset.card_insert_of_notMem notU]
            rw [oldEq, Finset.card_insert_of_notMem hb] at cap
            omega
        · obtain ⟨Cert2, bridge1, node2⟩ := next
          have lifted := pruned_bridge_live_copy roots raw col need Cert Cert2 u T n
            rowCover U a b d k label hd pa pb hab fresh ha tail cap part entries traces supports bridge1
          by_cases hb : b ∈ U
          · have oldU : insert a (insert b U) = U := by simp [ha, hb]
            rw [oldU] at cap
            cases n with
            | zero => omega
            | succ m =>
              have certB := lifted b mb hab.symm
              have subB : liftLabels (label b) ⊆ duplicateRoots roots (label a) :=
                liftLabels_subset_duplicate (part.1 b mb) (part.2.1 a ma b mb hab)
              rcases node2.copies (liftLabels (label b)) b subB pb certB with cut | next
              · have pn := double_sharing_partition roots U a b (bin d a b) label hab fresh ha hb part
                have tn := double_sharing_readOnce raw u U a b d hd fresh label traces
                apply readOnce_forest_exclusion_state _ _ u T m cut tail ?_
                  (doubleSharingLabels label a b (bin d a b)) pn tn
                rw [Finset.card_insert_of_notMem notU]
                omega
              · obtain ⟨Cert3, bridge2, node3⟩ := next
                have cap3 : k + 1 ≤ (insert (bin d a b) U).card + m := by
                  rw [Finset.card_insert_of_notMem notU]
                  omega
                obtain ⟨pn, en, tn, sn⟩ := pruned_double_transfer roots raw col need Cert2 Cert3
                  u T m gateCol rowCover U a b d k label hd hab fresh ha hb tail cap3
                  part lifted traces supports node3.initial node3.closed bridge2
                exact ih (Sum (Sum α Bool) Bool)
                  (duplicateRoots (duplicateRoots roots (label a)) (liftLabels (label b)))
                  (duplicateRaw (duplicateRaw raw a) b) Cert3 m node3 _ tail cap3
                  (doubleSharingLabels label a b (bin d a b)) pn en tn sn
          · have cap2 : k + 1 ≤ (insert (bin d a b) U).card + n := by
              rw [Finset.card_insert_of_notMem notU]
              rw [oldEq, Finset.card_insert_of_notMem hb] at cap
              omega
            obtain ⟨nextLabel, pn, en, tn, sn⟩ := pruned_single_transfer roots raw col need Cert Cert2
              u T n gateCol rowCover U a b d k label hd pa pb hab fresh ha hb tail cap2
              part entries traces supports bridge1 node2.initial node2.closed
            exact ih (Sum α Bool) (duplicateRoots roots (label a))
              (duplicateRaw raw a) Cert2 n node2 _ tail cap2
              nextLabel pn en tn sn
    obtain ⟨U, a, b, d, hd, rfl, pa, pb, hab, fresh, tail⟩ := run
    by_cases ha : a ∈ U
    · exact retained U a b d hd pa pb hab fresh ha tail cap part entries traces supports
    by_cases hb : b ∈ U
    · have swapped : bin (flipOp d) b a = bin d a b := (bin_flip hd a b).symm
      apply retained U b a (flipOp d) (flip_flip hd).1 pb pa hab.symm
        (by simpa only [swapped, Finset.insert_comm] using fresh) hb
        (by simpa only [swapped] using tail)
        (by simpa only [Finset.insert_comm] using cap)
        (by simpa only [Finset.insert_comm] using part)
        (by simpa only [Finset.insert_comm] using entries)
        (by simpa only [Finset.insert_comm] using traces)
        (by simpa only [Finset.insert_comm] using supports)
    · have notU : bin d a b ∉ U := fun h =>
        fresh (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem h))
      have notB : a ∉ insert b U := by simp [hab, ha]
      have cap2 : k + 1 ≤ (insert (bin d a b) U).card + depth := by
        rw [Finset.card_insert_of_notMem notU]
        rw [Finset.card_insert_of_notMem notB, Finset.card_insert_of_notMem hb] at cap
        omega
      obtain ⟨next, pn, en, tn, sn⟩ := pruned_merge_transfer roots raw col need Cert
        u T depth gateCol rowCover node.closed U a b d k label hd hab fresh ha hb
        tail cap2 part entries traces supports
      exact ih α roots raw Cert depth node _ tail cap2 next pn en tn sn

end PEqualNP.Outside.L_meta_2373.Live1024

namespace PEqualNP.Outside.L_meta_2373.RectangleRun

open Live1024

lemma run_length_le {R : Type} {u goal k} {roots : List (Wire R)}
    (h : Run u goal k roots) : roots.length ≤ k + 1 := by
  induction h using Run.ind with
  | stop => simp
  | perm p _ ih => simpa only [← p.length_eq] using ih
  | two op hd ka kb h ih =>
    cases ka <;> cases kb <;> simp [kept] at ih ⊢ <;> omega

lemma run_tight_measure {R : Type} (M : Wire R → Int)
    (subadd : ∀ d, allowed false d → ∀ a b, M (comb d a b) ≤ M a + M b)
    {goal k roots} (h : Run false goal k roots) (tight : roots.length = k + 1) :
    M goal ≤ (roots.map M).sum := by
  induction h using Run.ind with
  | stop => simp
  | perm p h ih =>
    have bound := ih (p.length_eq.trans tight)
    simpa only [(p.map M).sum_eq] using bound
  | @two s a b rest op hd ka kb h ih =>
    have len := run_length_le h
    have keeps : ka = false ∧ kb = false := by
      cases ka <;> cases kb <;> simp [kept] at len tight ⊢ <;> omega
    obtain ⟨rfl, rfl⟩ := keeps
    simp only [kept, Bool.false_eq_true, ite_false] at h ih
    have tailtight : (comb op a b :: rest).length = s + 1 := by
      simp only [List.length_cons] at tight ⊢
      omega
    have bound := ih tailtight
    calc
      M goal ≤ M (comb op a b) + (rest.map M).sum := by simpa using bound
      _ ≤ (M a + M b) + (rest.map M).sum := by
        have h := subadd op hd a b
        omega
      _ = ((a :: b :: rest).map M).sum := by simp [Int.add_assoc]

def rect {p q : Nat} (weight : Fin p → Fin q → Int)
    (S : Finset (Fin p)) (T : Finset (Fin q)) : Int := ∑ r ∈ S, ∑ c ∈ T, weight r c

def Bounds {R : Type} {p q : Nat} (P : Fin p → R) (N : Fin q → R)
    (weight : Fin p → Fin q → Int) (v : Wire R) (cap : Int) : Prop :=
  ∀ (S : Finset (Fin p)) (T : Finset (Fin q)),
    (∀ r ∈ S, v (P r) = true) → (∀ c ∈ T, v (N c) = false) → rect weight S T ≤ cap

lemma rect_union_left {p q : Nat} (weight : Fin p → Fin q → Int)
    (S U : Finset (Fin p)) (T : Finset (Fin q)) (h : Disjoint S U) :
    rect weight (S ∪ U) T = rect weight S T + rect weight U T := by
  exact Finset.sum_union h

lemma rect_union_right {p q : Nat} (weight : Fin p → Fin q → Int)
    (S : Finset (Fin p)) (T U : Finset (Fin q)) (h : Disjoint T U) :
    rect weight S (T ∪ U) = rect weight S T + rect weight S U := by
  simp only [rect, Finset.sum_union h, Finset.sum_add_distrib]

lemma bounds_and {R : Type} {p q : Nat} {P : Fin p → R} {N : Fin q → R}
    {weight : Fin p → Fin q → Int} {a b : Wire R} {ca cb : Int}
    (ha : Bounds P N weight a ca) (hb : Bounds P N weight b cb) :
    Bounds P N weight (combine false a b) (ca + cb) := by
  intro S T hs ht
  let T0 := T.filter (fun c => a (N c) = false)
  let T1 := T.filter (fun c => a (N c) = true)
  have part : T0 ∪ T1 = T := by
    ext c
    simp only [T0, T1, Finset.mem_union, Finset.mem_filter]
    cases a (N c) <;> simp
  have disj : Disjoint T0 T1 := by
    apply Finset.disjoint_left.mpr
    intro c hc hd
    have h0 := (Finset.mem_filter.mp hc).2
    have h1 := (Finset.mem_filter.mp hd).2
    exact Bool.false_ne_true (h0.symm.trans h1)
  have left := ha S T0
    (fun r hr => (Bool.and_eq_true_iff.mp (hs r hr)).1)
    (fun c hc => (Finset.mem_filter.mp hc).2)
  have right := hb S T1
    (fun r hr => (Bool.and_eq_true_iff.mp (hs r hr)).2)
    (fun c hc => by
      obtain ⟨hc, ah⟩ := Finset.mem_filter.mp hc
      have h := ht c hc
      change (a (N c) && b (N c)) = false at h
      simpa only [ah, Bool.true_and] using h)
  rw [← part, rect_union_right weight S T0 T1 disj]
  exact add_le_add left right

lemma bounds_or {R : Type} {p q : Nat} {P : Fin p → R} {N : Fin q → R}
    {weight : Fin p → Fin q → Int} {a b : Wire R} {ca cb : Int}
    (ha : Bounds P N weight a ca) (hb : Bounds P N weight b cb) :
    Bounds P N weight (combine true a b) (ca + cb) := by
  intro S T hs ht
  let S0 := S.filter (fun r => a (P r) = true)
  let S1 := S.filter (fun r => a (P r) = false)
  have part : S0 ∪ S1 = S := by
    ext r
    simp only [S0, S1, Finset.mem_union, Finset.mem_filter]
    cases a (P r) <;> simp
  have disj : Disjoint S0 S1 := by
    apply Finset.disjoint_left.mpr
    intro r hr hd
    have h0 := (Finset.mem_filter.mp hr).2
    have h1 := (Finset.mem_filter.mp hd).2
    exact Bool.false_ne_true (h1.symm.trans h0)
  have left := ha S0 T
    (fun r hr => (Finset.mem_filter.mp hr).2)
    (fun c hc => (Bool.or_eq_false_iff.mp (ht c hc)).1)
  have right := hb S1 T
    (fun r hr => by
      obtain ⟨hr, ah⟩ := Finset.mem_filter.mp hr
      have h := hs r hr
      change (a (P r) || b (P r)) = true at h
      simpa only [ah, Bool.false_or] using h)
    (fun c hc => (Bool.or_eq_false_iff.mp (ht c hc)).2)
  rw [← part, rect_union_left weight S0 S1 T disj]
  exact add_le_add left right

noncomputable def score {R : Type} {p q : Nat} (P : Fin p → R) (N : Fin q → R)
    (weight : Fin p → Fin q → Int) (v : Wire R)
    (st : Finset (Fin p) × Finset (Fin q)) : Int := by
  classical
  exact if (∀ r ∈ st.1, v (P r) = true) ∧ (∀ c ∈ st.2, v (N c) = false)
    then rect weight st.1 st.2 else 0

noncomputable def measure {R : Type} {p q : Nat} (P : Fin p → R) (N : Fin q → R)
    (weight : Fin p → Fin q → Int) (v : Wire R) : Int := by
  classical
  exact Finset.univ.sup' Finset.univ_nonempty (score P N weight v)

lemma bounds_measure {R : Type} {p q : Nat} (P : Fin p → R) (N : Fin q → R)
    (weight : Fin p → Fin q → Int) (v : Wire R) :
    Bounds P N weight v (measure P N weight v) := by
  classical
  intro S T hs ht
  have bound := Finset.le_sup' (f := score P N weight v) (Finset.mem_univ (S,T))
  have valid : (∀ r ∈ S, v (P r) = true) ∧ (∀ c ∈ T, v (N c) = false) := ⟨hs, ht⟩
  simpa only [score, if_pos valid, measure] using bound

lemma measure_le {R : Type} {p q : Nat} {P : Fin p → R} {N : Fin q → R}
    {weight : Fin p → Fin q → Int} {v : Wire R} {cap : Int}
    (h : Bounds P N weight v cap) : measure P N weight v ≤ cap := by
  classical
  have nonneg : 0 ≤ cap := by simpa [rect] using h ∅ ∅ (by simp) (by simp)
  apply (Finset.sup'_le_iff Finset.univ_nonempty (score P N weight v)).mpr
  intro st _
  unfold score
  split_ifs with valid
  · exact h st.1 st.2 valid.1 valid.2
  · exact nonneg

lemma measure_subadditive {R : Type} {p q : Nat} (P : Fin p → R) (N : Fin q → R)
    (weight : Fin p → Fin q → Int) (d : Nat) (hd : allowed false d) (a b : Wire R) :
    measure P N weight (comb d a b) ≤ measure P N weight a + measure P N weight b := by
  have small : d < 2 := by simpa [allowed] using hd
  have cases : d = 0 ∨ d = 1 := by omega
  rcases cases with rfl | rfl
  · exact measure_le (by simpa [comb] using bounds_and (bounds_measure P N weight a) (bounds_measure P N weight b))
  · exact measure_le (by simpa [comb] using bounds_or (bounds_measure P N weight a) (bounds_measure P N weight b))

lemma tight_run_bound {R : Type} {p q : Nat} (P : Fin p → R) (N : Fin q → R)
    (weight : Fin p → Fin q → Int) {goal k roots} (h : Run false goal k roots)
    (tight : roots.length = k + 1) :
    Bounds P N weight goal ((roots.map (measure P N weight)).sum) := by
  intro S T hs ht
  exact (bounds_measure P N weight goal S T hs ht).trans
    (run_tight_measure (measure P N weight) (measure_subadditive P N weight) h tight)

lemma tight_run_uniform {R : Type} {p q : Nat} (P : Fin p → R) (N : Fin q → R)
    (weight : Fin p → Fin q → Int) {goal k roots cap} (h : Run false goal k roots)
    (tight : roots.length = k + 1) (leaves : ∀ v ∈ roots, Bounds P N weight v cap)
    (positive : ∀ r, goal (P r) = true) (negative : ∀ c, goal (N c) = false) :
    rect weight Finset.univ Finset.univ ≤ (roots.length : Int) * cap := by
  have bound := tight_run_bound P N weight h tight Finset.univ Finset.univ
    (fun r _ => positive r) (fun c _ => negative c)
  have leafsum : (roots.map (measure P N weight)).sum ≤ (roots.length : Int) * cap := by
    clear h tight bound
    induction roots with
    | nil => simp
    | cons a rest ih =>
      have one := measure_le (leaves a (by simp))
      have tail := ih (fun v hv => leaves v (by simp [hv]))
      simpa [Int.add_mul, Int.add_comm, Int.add_left_comm, Int.add_assoc] using add_le_add one tail
  exact bound.trans leafsum

end PEqualNP.Outside.L_meta_2373.RectangleRun

namespace PEqualNP.Outside.L_meta_2373.RectangleRun

open Live1024

lemma map_sum_le {α : Type} (xs : List α) (f g : α → Int)
    (h : ∀ a ∈ xs, f a ≤ g a) : (xs.map f).sum ≤ (xs.map g).sum := by
  induction xs with
  | nil => simp
  | cons a rest ih =>
    have one := h a (by simp)
    have tail := ih (fun v hv => h v (by simp [hv]))
    simpa only [List.map_cons, List.sum_cons] using add_le_add one tail

lemma tight_run_indexed {R α : Type} {p q : Nat} (P : Fin p → R) (N : Fin q → R)
    (weight : Fin p → Fin q → Int) (raw : α → Wire R) (caps : α → Int)
    (labels : List α) {goal k} (trace : Run false goal k (labels.map raw))
    (tight : labels.length = k + 1)
    (leaves : ∀ i ∈ labels, Bounds P N weight (raw i) (caps i)) :
    Bounds P N weight goal (labels.map caps).sum := by
  intro S T hs ht
  have bound := tight_run_bound P N weight trace (by simpa using tight) S T hs ht
  have leafsum : ((labels.map raw).map (measure P N weight)).sum ≤ (labels.map caps).sum := by
    rw [List.map_map]
    apply map_sum_le
    intro i hi
    exact measure_le (leaves i hi)
  exact bound.trans leafsum

end PEqualNP.Outside.L_meta_2373.RectangleRun

namespace PEqualNP.Outside.L_meta_2373.Live1024.RectangleFixture0Children

def signal : Fin 13 → Sig := ![0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc, 0xf8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8, 0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00, 0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000, 0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000, 0xfffffffffaaafaaafffffffffaaafaaafffffffffaaafaaafffffffffaaafaaafffffffffaaafaaafffffffffaaafaaafffffffffaaafaaafffffffffaaafaaafffffffffaaafaaafffffffffaaafaaafffffffffaaafaaafffffffffaaafaaafffffffffaaafaaafffffffffaaafaaafffffffffaaafaaafffffffffaaafaaa, 0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000, 0xffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000, 0xfffffffffffffffffffffffffffffffffaaafaaafaaafaaafaaafaaafaaafaaafffffffffffffffffffffffffffffffffaaafaaafaaafaaafaaafaaafaaafaaafffffffffffffffffffffffffffffffffaaafaaafaaafaaafaaafaaafaaafaaafffffffffffffffffffffffffffffffffaaafaaafaaafaaafaaafaaafaaafaaa, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000000000000000000000000000000000000, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000ffffffffffffffff0000000000000000, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 0xfffffffffaaafaaafffffffffaaafaaafaaafaaafaaafaaafaaafaaafaaafaaafffffffffaaafaaafffffffffaaafaaafaaafaaafaaafaaafaaafaaafaaafaaafffffffffaaafaaafffffffffaaafaaafaaafaaafaaafaaafaaafaaafaaafaaafffffffffaaafaaafffffffffaaafaaafaaafaaafaaafaaafaaafaaafaaafaaa]
def baseRaw (i : Fin 12) : Sig := signal i.castSucc
def baseRoots : Finset (Fin 12) := Finset.univ
def support : Fin 13 → Finset (Fin 12) := ![{0}, {1}, {2}, {3}, {4}, {5}, {6}, {7}, {8}, {9}, {10}, {11}, {5, 8}]
def copiedRoots (i : Fin 13) := duplicateRoots baseRoots (support i)
def copiedRaw (i : Fin 13) := duplicateRaw baseRaw (signal i)
def signalIndex (i : Fin 13) : Sum (Fin 12) Bool → Fin 13 := Sum.elim Fin.castSucc (fun _ => i)
def rootLabels : Fin 13 → List (Sum (Fin 12) Bool) := ![[(Sum.inl 1), (Sum.inl 2), (Sum.inl 3), (Sum.inl 4), (Sum.inl 5), (Sum.inl 6), (Sum.inl 7), (Sum.inl 8), (Sum.inl 9), (Sum.inl 10), (Sum.inl 11), (Sum.inr false), (Sum.inr true)], [(Sum.inl 0), (Sum.inl 2), (Sum.inl 3), (Sum.inl 4), (Sum.inl 5), (Sum.inl 6), (Sum.inl 7), (Sum.inl 8), (Sum.inl 9), (Sum.inl 10), (Sum.inl 11), (Sum.inr false), (Sum.inr true)], [(Sum.inl 0), (Sum.inl 1), (Sum.inl 3), (Sum.inl 4), (Sum.inl 5), (Sum.inl 6), (Sum.inl 7), (Sum.inl 8), (Sum.inl 9), (Sum.inl 10), (Sum.inl 11), (Sum.inr false), (Sum.inr true)], [(Sum.inl 0), (Sum.inl 1), (Sum.inl 2), (Sum.inl 4), (Sum.inl 5), (Sum.inl 6), (Sum.inl 7), (Sum.inl 8), (Sum.inl 9), (Sum.inl 10), (Sum.inl 11), (Sum.inr false), (Sum.inr true)], [(Sum.inl 0), (Sum.inl 1), (Sum.inl 2), (Sum.inl 3), (Sum.inl 5), (Sum.inl 6), (Sum.inl 7), (Sum.inl 8), (Sum.inl 9), (Sum.inl 10), (Sum.inl 11), (Sum.inr false), (Sum.inr true)], [(Sum.inl 0), (Sum.inl 1), (Sum.inl 2), (Sum.inl 3), (Sum.inl 4), (Sum.inl 6), (Sum.inl 7), (Sum.inl 8), (Sum.inl 9), (Sum.inl 10), (Sum.inl 11), (Sum.inr false), (Sum.inr true)], [(Sum.inl 0), (Sum.inl 1), (Sum.inl 2), (Sum.inl 3), (Sum.inl 4), (Sum.inl 5), (Sum.inl 7), (Sum.inl 8), (Sum.inl 9), (Sum.inl 10), (Sum.inl 11), (Sum.inr false), (Sum.inr true)], [(Sum.inl 0), (Sum.inl 1), (Sum.inl 2), (Sum.inl 3), (Sum.inl 4), (Sum.inl 5), (Sum.inl 6), (Sum.inl 8), (Sum.inl 9), (Sum.inl 10), (Sum.inl 11), (Sum.inr false), (Sum.inr true)], [(Sum.inl 0), (Sum.inl 1), (Sum.inl 2), (Sum.inl 3), (Sum.inl 4), (Sum.inl 5), (Sum.inl 6), (Sum.inl 7), (Sum.inl 9), (Sum.inl 10), (Sum.inl 11), (Sum.inr false), (Sum.inr true)], [(Sum.inl 0), (Sum.inl 1), (Sum.inl 2), (Sum.inl 3), (Sum.inl 4), (Sum.inl 5), (Sum.inl 6), (Sum.inl 7), (Sum.inl 8), (Sum.inl 10), (Sum.inl 11), (Sum.inr false), (Sum.inr true)], [(Sum.inl 0), (Sum.inl 1), (Sum.inl 2), (Sum.inl 3), (Sum.inl 4), (Sum.inl 5), (Sum.inl 6), (Sum.inl 7), (Sum.inl 8), (Sum.inl 9), (Sum.inl 11), (Sum.inr false), (Sum.inr true)], [(Sum.inl 0), (Sum.inl 1), (Sum.inl 2), (Sum.inl 3), (Sum.inl 4), (Sum.inl 5), (Sum.inl 6), (Sum.inl 7), (Sum.inl 8), (Sum.inl 9), (Sum.inl 10), (Sum.inr false), (Sum.inr true)], [(Sum.inl 0), (Sum.inl 1), (Sum.inl 2), (Sum.inl 3), (Sum.inl 4), (Sum.inl 6), (Sum.inl 7), (Sum.inl 9), (Sum.inl 10), (Sum.inl 11), (Sum.inr false), (Sum.inr true)]]

def positiveRows : Fin 15 → Row := fun r => Fin.ofNat 1024 (![3, 6, 12, 24, 17, 33, 66, 132, 264, 528, 160, 640, 576, 320, 288] r)
def negativeRows : Fin 15 → Row := fun r => Fin.ofNat 1024 (![50, 69, 104, 116, 138, 201, 208, 276, 385, 402, 521, 548, 554, 770, 773] r)
def positiveSample : Fin 15 → Fin 13 → Bool := ![![true, true, false, false, false, true, false, false, true, false, false, false, true], ![true, true, false, false, false, false, false, false, false, false, false, false, false], ![false, true, true, false, false, true, false, false, true, false, false, false, true], ![false, false, true, true, false, false, false, false, false, false, false, false, false], ![false, false, false, true, false, true, false, false, true, false, false, false, true], ![false, false, false, false, true, true, false, false, true, false, false, false, true], ![true, false, false, false, false, false, true, false, false, false, true, false, false], ![false, true, false, false, false, false, false, true, true, false, false, false, false], ![false, false, true, false, false, false, false, false, false, true, true, false, false], ![false, false, false, true, false, false, false, false, false, false, false, true, false], ![false, false, false, false, true, true, false, true, true, false, false, false, true], ![false, false, false, false, false, false, false, true, true, false, false, true, false], ![false, false, false, false, false, false, true, false, false, false, true, true, false], ![false, false, false, false, false, false, true, false, false, true, true, false, false], ![false, false, false, false, true, true, false, false, false, true, true, false, false]]
def negativeSample : Fin 15 → Fin 13 → Bool := ![![true, false, false, true, true, true, false, false, false, false, false, false, false], ![false, true, false, false, false, true, true, false, true, false, true, false, true], ![false, false, true, false, true, true, true, false, false, false, true, false, false], ![false, true, false, true, true, true, true, false, false, false, true, false, false], ![true, false, true, false, false, false, false, true, true, false, false, false, false], ![false, false, true, false, false, true, true, true, true, false, true, false, true], ![false, false, false, true, false, false, true, true, true, false, true, false, false], ![false, true, false, true, false, false, false, false, false, true, true, false, false], ![false, false, false, false, false, true, false, true, true, true, true, false, true], ![true, false, false, true, false, false, false, true, true, true, true, false, false], ![false, false, true, false, false, true, false, false, true, false, false, true, true], ![false, true, false, false, true, true, false, false, false, false, false, true, false], ![true, false, true, false, true, true, false, false, false, false, false, true, false], ![true, false, false, false, false, false, false, false, false, true, true, true, false], ![false, true, false, false, false, true, false, false, true, true, true, true, true]]
def weight : Fin 15 → Fin 15 → Int := ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, -3, 0, 0, 0, 0, 3, 0, 0, 3, 0, 0], ![0, 0, 0, 5, 3, 0, 0, 0, 0, -5, 0, 0, 3, 0, 5], ![0, 0, 2, 5, 0, 4, 0, 0, 0, 5, 6, 0, 0, 0, -10], ![0, 2, 0, 0, 0, 4, 0, 0, 0, 0, -6, 0, 0, 0, 6], ![0, 4, 0, 0, 0, 2, 0, 0, 0, -6, 0, 0, 0, 0, 6], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 3, -3, 0], ![0, 0, 0, 4, 3, 0, 0, 0, 0, 3, 0, 0, -4, 0, 4], ![0, 0, 0, -5, 0, 5, 0, 0, 0, 5, 0, 0, 5, 0, 5], ![0, -2, -2, 4, 0, -4, 0, 0, 0, 4, 6, 0, 0, 0, 6], ![0, 0, 0, 4, 0, 6, 0, 0, 0, 6, 0, 0, 4, -2, -6], ![0, 0, 0, -4, 0, 4, 0, 0, 0, 4, 0, 0, 4, 2, 2], ![0, 2, 2, 4, 0, 0, 0, 0, 0, -4, 0, 0, 3, 3, 0], ![0, 4, 0, 5, 0, 1, 0, 0, 0, 3, 0, 0, -5, 3, 0], ![0, -4, 0, 5, 0, -6, 0, 0, 0, 6, 0, 0, 5, 2, 4]]
def costs : Fin 13 → Int := ![0, 6, 10, 12, 12, 12, 6, 8, 16, 10, 16, 8, 20]
def positions : Fin 13 → Fin 7 → Fin 15 := ![![0, 1, 6, 0, 0, 0, 0], ![0, 1, 2, 7, 0, 0, 0], ![2, 3, 8, 2, 2, 2, 2], ![3, 4, 9, 3, 3, 3, 3], ![5, 10, 14, 5, 5, 5, 5], ![0, 2, 4, 5, 10, 14, 0], ![6, 12, 13, 6, 6, 6, 6], ![7, 10, 11, 7, 7, 7, 7], ![0, 2, 4, 5, 7, 10, 11], ![8, 13, 14, 8, 8, 8, 8], ![6, 8, 12, 13, 14, 6, 6], ![9, 11, 12, 9, 9, 9, 9], ![0, 2, 4, 5, 10, 0, 0]]

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
lemma positive_inputs : ∀ r i, observe (signal i) (positiveRows r) = positiveSample r i := by decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
lemma negative_inputs : ∀ r i, observe (signal i) (negativeRows r) = negativeSample r i := by decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
lemma positive_graph : ∀ r, observe graph (positiveRows r) = true := by decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
lemma negative_graph : ∀ r, observe graph (negativeRows r) = false := by decide +kernel

def rect (S T : Finset (Fin 15)) : Int := ∑ r ∈ S, ∑ c ∈ T, weight r c

def negativeSet (i : Fin 13) : Finset (Fin 15) :=
  Finset.univ.filter (fun c => negativeSample c i = false)

def selected (i : Fin 13) (keep : Fin 7 → Bool) : Finset (Fin 15) :=
  (Finset.univ.filter (fun k => keep k = true)).image (positions i)

def maxRect (i : Fin 13) (S : Finset (Fin 15)) : Int :=
  ∑ c ∈ negativeSet i, max (∑ r ∈ S, weight r c) 0

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
lemma positions_cover : ∀ (i : Fin 13) (r : Fin 15),
    positiveSample r i = true ↔ ∃ k : Fin 7, positions i k = r := by decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
lemma finite_rectangle_bound : ∀ (i : Fin 13) (keep : Fin 7 → Bool),
    maxRect i (selected i keep) ≤ costs i := by
  intro i
  fin_cases i <;> decide +kernel

lemma selected_covers (i : Fin 13) (S : Finset (Fin 15))
    (hs : ∀ r ∈ S, positiveSample r i = true) :
    selected i (fun k => decide (positions i k ∈ S)) = S := by
  ext r
  simp only [selected, Finset.mem_image, Finset.mem_filter, Finset.mem_univ,
    true_and, decide_eq_true_eq]
  constructor
  · rintro ⟨k, hk, rfl⟩
    exact hk
  · intro hr
    obtain ⟨k, hk⟩ := (positions_cover i r).mp (hs r hr)
    exact ⟨k, by simpa only [hk] using hr, hk⟩

lemma leaf_bound (i : Fin 13) (S T : Finset (Fin 15))
    (hs : ∀ r ∈ S, positiveSample r i = true)
    (ht : ∀ c ∈ T, negativeSample c i = false) : rect S T ≤ costs i := by
  have sub : T ⊆ negativeSet i := by
    intro c hc
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ c, ht c hc⟩
  calc
    rect S T = ∑ c ∈ T, ∑ r ∈ S, weight r c := by
      unfold rect
      rw [Finset.sum_comm]
    _ ≤ ∑ c ∈ T, max (∑ r ∈ S, weight r c) 0 :=
      Finset.sum_le_sum (fun _ _ => le_max_left _ _)
    _ ≤ maxRect i S := by
      exact Finset.sum_le_sum_of_subset_of_nonneg sub (fun _ _ _ => le_max_right _ _)
    _ ≤ costs i := by
      rw [← selected_covers i S hs]
      exact finite_rectangle_bound i _

lemma raw_bound (i : Fin 13) : RectangleRun.Bounds
    positiveRows negativeRows weight (observe (signal i)) (costs i) := by
  intro S T hs ht
  apply leaf_bound i S T
  · intro r hr
    rw [← positive_inputs]
    exact hs r hr
  · intro c hc
    rw [← negative_inputs]
    exact ht c hc


set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
lemma full_weight : rect Finset.univ Finset.univ = 135 := by decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
lemma child_facts : ∀ i, (rootLabels i).Nodup ∧ (rootLabels i).toFinset = copiedRoots i ∧
    ((rootLabels i).map (fun r => costs (signalIndex i r))).sum < 135 := by
  decide +kernel

lemma copied_raw (i : Fin 13) (r : Sum (Fin 12) Bool) :
    copiedRaw i r = signal (signalIndex i r) := by cases r <;> rfl

lemma all_budget_cuts (i : Fin 13) :
    BudgetRunCut (duplicateRoots baseRoots (support i))
      (duplicateRaw baseRaw (signal i)) false graph 0 := by
  intro k cap trace
  change Run false (observe graph) k ((copiedRoots i).toList.map (fun r => observe (copiedRaw i r))) at trace
  have facts := child_facts i
  have perm : (copiedRoots i).toList.Perm (rootLabels i) := by
    apply List.perm_of_nodup_nodup_toFinset_eq (Finset.nodup_toList _) facts.1
    simpa using facts.2.1.symm
  have ordered := Run.perm (perm.map (fun r => observe (copiedRaw i r))) trace
  have lengths : (copiedRoots i).card = (rootLabels i).length := by simpa using perm.length_eq
  have lower := RectangleRun.run_length_le ordered
  simp only [List.length_map] at lower
  have tight : (rootLabels i).length = k + 1 := by
    change k + 1 ≤ (copiedRoots i).card + 0 at cap
    omega
  have bounds := RectangleRun.tight_run_indexed positiveRows negativeRows weight
    (fun r => observe (copiedRaw i r)) (fun r => costs (signalIndex i r))
    (rootLabels i) ordered tight (fun r _ => by simpa only [copied_raw] using raw_bound (signalIndex i r))
  have bound := bounds Finset.univ Finset.univ
    (fun r _ => positive_graph r) (fun r _ => negative_graph r)
  change rect Finset.univ Finset.univ ≤ _ at bound
  rw [full_weight] at bound
  have strict := facts.2.2
  omega

def entries : List (Finset (Fin 12) × Sig) := List.ofFn (fun i : Fin 13 => (support i, signal i))

lemma entry_cuts {A : Finset (Fin 12)} {w : Sig} (entry : (A, w) ∈ entries) :
    BudgetRunCut (duplicateRoots baseRoots A) (duplicateRaw baseRaw w) false graph 0 := by
  obtain ⟨i, hi⟩ := List.mem_ofFn.mp entry
  have parts := Prod.mk.inj hi
  simpa only [parts.1, parts.2] using all_budget_cuts i

end PEqualNP.Outside.L_meta_2373.Live1024.RectangleFixture0Children

namespace PEqualNP.Outside.L_meta_2373.Live1024.PrunedCopyFixture0

def rootLabels0 : List (Fin 12) := [0,1,2,3,4,5,6,7,8,9,10,11]
def roots0 : Finset (Fin 12) := rootLabels0.toFinset
def nodeRaw0 : Fin 12 → Sig := RectangleFixture0Children.baseRaw
def entries0 : List (Entry (Fin 12)) := RectangleFixture0Children.entries
def cuts0 : List (Entry (Fin 12)) := []
def rows0 : List (Row × Row) :=
  [(17,116),(6,773),(24,104),(12,773),(528,116),(640,773),
   (132,201),(17,402),(33,201),(288,116),(6,116),(640,385),
   (6,50),(24,208),(66,201),(320,385),(24,138),(264,201)]

theorem roots_eq : roots0 = RectangleFixture0Children.baseRoots := by decide +kernel

theorem cutsSound0 : ∀ A v, (A,v) ∈ cuts0 →
    BudgetRunCut (compressRoots roots0 A) (duplicateRaw nodeRaw0 v) false graph 1 := by
  intro A v h
  simp [cuts0] at h

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem checkedLeaves0 : entryLeafCheck rootLabels0 nodeRaw0 entries0 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem checkedGates0 :
    entryGateCheck false graph rootLabels0 nodeRaw0 entries0 cuts0 rows0 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem checkedMissing0 : (roots0, graph) ∉ entries0 := by decide +kernel

theorem completedPrunedNode :
    PrunedNode (pairColumn false) (pairColumn false graph) false graph 1
      (Fin 12) roots0 nodeRaw0 (entryCert entries0) := by
  refine ⟨entryLeafCheck_sound checkedLeaves0,
    entryGateCheck_sound cutsSound0 checkedGates0, checkedMissing0, ?_⟩
  intro A w sub hp member
  apply Or.inl
  simpa only [roots_eq, nodeRaw0] using RectangleFixture0Children.entry_cuts member

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem raw_distinct : Set.InjOn nodeRaw0 (↑roots0 : Set (Fin 12)) := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem raw_card : (roots0.image nodeRaw0).card = 12 := by decide +kernel

theorem initial_certificate : ∃ label : Sig → Finset (Fin 12),
    LabelPartition roots0 (roots0.image nodeRaw0) label ∧
    (∀ v ∈ roots0.image nodeRaw0, entryCert entries0 (label v) v) ∧
    (∀ v ∈ roots0.image nodeRaw0, ReadOnce nodeRaw0 false (label v) v) ∧
    (∀ v ∈ roots0.image nodeRaw0, ColumnSupport nodeRaw0 (pairColumn false) (label v) v) :=
  initial_raw_state roots0 nodeRaw0 (pairColumn false) (entryCert entries0) false
    raw_distinct (entryLeafCheck_sound checkedLeaves0)

theorem completed_live_exclusion : Impossible false graph 12 (roots0.image nodeRaw0) := by
  intro k bound run
  obtain ⟨label, part, entries, traces, supports⟩ := initial_certificate
  have cap : k + 1 ≤ (roots0.image nodeRaw0).card + 1 := by
    rw [raw_card]
    omega
  exact pruned_node_exclusion_state (pairColumn false) (pairColumn false graph) false graph
    (pairColumn_gate false) (pairColumn_cover false graph) k
    (Fin 12) roots0 nodeRaw0 (entryCert entries0) 1 completedPrunedNode
    (roots0.image nodeRaw0) run cap label part entries traces supports

end PEqualNP.Outside.L_meta_2373.Live1024.PrunedCopyFixture0
