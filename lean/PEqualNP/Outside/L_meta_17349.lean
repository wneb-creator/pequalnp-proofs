import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_17349_aux.EightVertex
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
def graph : Sig := 0xffffffffffffffffffffffe8ffffeae8ffffffe8ffecffe8ffffffe8eeeceae8ffffffffffffffffffffffe8ffffeae8ffffffe8ffecffe8ffffffe8eeeceae8
def sample (r : Row) (j : Fin 9) := bit r (inputs.getD j.val zero)
def edge (x : Fin 9 → Bool) : Bool :=
  (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 3 && x 6) || (x 4 && x 5) || (x 4 && x 7) || (x 6 && x 7)
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
  (x 0 &&& x 1) ||| (x 0 &&& x 2) ||| (x 0 &&& x 3) ||| (x 1 &&& x 2) ||| (x 1 &&& x 4) ||| (x 3 &&& x 5) ||| (x 3 &&& x 6) ||| (x 4 &&& x 5) ||| (x 4 &&& x 7) ||| (x 6 &&& x 7)
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
  (x 0 &&& x 1) ||| (x 0 &&& x 2) ||| (x 0 &&& x 3) ||| (x 1 &&& x 2) ||| (x 1 &&& x 4) ||| (x 3 &&& x 5) ||| (x 3 &&& x 6) ||| (x 4 &&& x 5) ||| (x 4 &&& x 7) ||| (x 6 &&& x 7)
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
def eightEdge (x : Fin 8 → Bool) := (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 3 && x 6) || (x 4 && x 5) || (x 4 && x 7) || (x 6 && x 7)

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
def neighbor8459 (i : Fin 8) : Nat := [1,0,0,0,1,3,3,4].getD i.val 0
def absentRow8459 (i : Fin 8) : Row := Fin.ofNat 512 (1 <<< neighbor8459 i)
def presentRow8459 (i : Fin 8) : Row := Fin.ofNat 512 ((1 <<< i.val) ||| (1 <<< neighbor8459 i))

set_option maxHeartbeats 1000000 in
theorem requiredInputs :
    (∀ i : Fin 8, bit (absentRow8459 i) graph ≠ bit (presentRow8459 i) graph) ∧
    (∀ i j : Fin 8, i ≠ j →
      bit (absentRow8459 i) (eightInputs.getD j.val zero) =
      bit (presentRow8459 i) (eightInputs.getD j.val zero)) := by decide +kernel


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
      apply raw_required run eightInputs (eightInputs.getD i.val zero) sub (absentRow8459 i) (presentRow8459 i)
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
def g7Y : Array (Bits × Bits) := #[(0xcf67b3d9ecf67b3d9ecf67b3d9ecf67b3d9ecf,0xa8542a150a8542a150a8542a150a8542a150a),(0x73b9dcee773b9dcee773b9dcee773b9dcee773,0xa150a8542a150a8542a150a8542a150a8542a1),(0xbcde6f379bcde6f379bcde6f379bcde6f379bc,0x542a150a8542a150a8542a150a8542a150a854),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
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
def K7 := extendKnown [] 4 [(7,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V7 : Known true K7 := extend_ok (m:=7) baseKnown low7 (by decide +kernel)
def g15Y : Array (Bits × Bits) := #[(0x7e3cf3f1e79f8f3cfc79e7e3cf3f1e79f8f3cf,0x5040228201141008a08045040228201141008a),(0x99cf4cce7a6673d3339e999cf4cce7a6673d33,0xa964854b242a592152c90a964854b242a5921),(0xe1f38f0f9c787ce3c3e71e1f38f0f9c787ce3c,0xa52985294c294a614a530a52985294c294a614),(0x603f0301f8180fc0c07e0603f0301f8180fc0,0x7bfd03dfe81eff40f7fa07bfd03dfe81eff40),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
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
def K15 := extendKnown K7 5 [(15,[]),(23,[67,16])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V15 : Known true K15 := extend_ok (m:=15) V7 low15 (by decide +kernel)
def g27Y : Array (Bits × Bits) := #[(0xf8fce7c7e73e3f39f1f9cf8fce7c7e73e3f39f,0x5248a29245149228a49145248a29245149228a),(0x9f1f3cf8f9e7c7cf3e3e79f1f3cf8f9e7c7cf3,0x8926144930a24985124c28926144930a249851),(0x0,0x0),(0xe0e3c7071e3838f1c1c78e0e3c7071e3838f1c,0xa5b7452dba296dd14b6e8a5b7452dba296dd14),(0x703f8381fc1c0fe0e07f0703f8381fc1c0fe0,0x6d9e836cf41b67a0db3d06d9e836cf41b67a0),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def g27C : List ColumnInfo := []
def g27A : List (List Nat) := [[],[16,67]]
def g27D3 (j : Nat) : Nat := 0xf
def g27L : Nat → Packing
  | 3 => (1,0,1,0,0,0,0,g27D3)
  | _ => emptyPacking
def g27I (_ _ : Nat) : Option (Nat × Nat) := none
def g27 : Forest := ⟨27,3,fun i => g27Y[i]?.getD (0,0),g27C,g27A,g27L,g27I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g27P3_0 : block g27 3 0 1=true := by
  apply cellsBlock (ar:=4) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g27B3 : block g27 3 0 1=true := g27P3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g27T : checkedTables g27 3 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g27 0 0 0 = true)
  · exact (rfl : block g27 1 0 0 = true)
  · exact (rfl : block g27 2 0 0 = true)
  · exact g27B3
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g27G : graphValid g27 (boundsBefore K15) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low27 : Lower true (varsX 27) (graphGoal 27) 4 := lower_forest (g:=g27) (i:=0) (hints:=65537) (before_sound K15 V15) g27G g27T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K27 := extendKnown K15 4 [(27,[]),(43,[84,49]),(45,[84,49,33]),(51,[65,81,16,48]),(54,[65,81,49,16,32]),(57,[81,33,48]),(58,[16,65,80,49,32]),(75,[100,84,49]),(77,[100,84,49,33]),(120,[48,96,81,32]),(147,[116,100,65,81,16,48]),(150,[116,100,65,81,49,16,32]),(184,[116,64,65,96,81,32]),(201,[65,113,100,81,33,48]),(210,[65,116,64,97,80,49,32]),(216,[113,96,81,32]),(232,[49,116,48,96,81,32]),(240,[49,64,115,96,81,32])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V27 : Known true K27 := extend_ok (m:=27) V15 low27 (by decide +kernel)
def g31Y : Array (Bits × Bits) := #[(0xc7e9b879e38fd370f3c71fa6e1e78e3f4dc3cf,0x924128114924825022924904a045249209408a),(0x38f64fa67c71ec9f4cf8e3d93e99f1c7b27d33,0x492405242492480a4849249014909249202921),(0x3f1871c7807e30e38f00fc61c71e01f8c38e3c,0x249850c2924930a185249261430a4924c28614),(0xc01f81f803803f03f007007e07e00e00fc0fc0,0x6dbe81e816db7d03d02db6fa07a05b6df40f40),(0x1ffe001c003ffc0038007ff8007000fff000,0xb6dbfa001b6db7f40036db6fe8006db6dfd000),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def g31C : List ColumnInfo := [(16,0,15,0,5)]
def g31A : List (List Nat) := [[],[16,67]]
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
theorem g31G : graphValid g31 (boundsBefore K27) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low31 : Lower true (varsX 31) (graphGoal 31) 6 := lower_forest (g:=g31) (i:=0) (hints:=65537) (before_sound K27 V27) g31G g31T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K31 := extendKnown K27 6 [(31,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V31 : Known true K31 := extend_ok (m:=31) V27 low31 (by decide +kernel)
def g47Y : Array (Bits × Bits) := #[(0xc1f07fe10f3cf07c1ff843cf3c1f07fe10f3cf,0x884210810a08a210842042822884210810a08a),(0xc00f83e633d33003e0f98cf4cc00f83e633d33,0x5294a526219214a52949886485294a52621921),(0xffc183ce3c003ff060f38f000ffc183ce3c,0x25294a581461494a52960518525294a5814614),(0x3ff0001fc0fc0ffc0007f03f03ff0001fc0fc0,0x6318c7480f4018c631d203d006318c7480f40),(0x0,0x0),(0x3e00001fff000f800007ffc003e00001fff000,0x39ce738b7f000e739ce2dfc0039ce738b7f000),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def g47C : List ColumnInfo := [(4,0,43,0,4),(2,0,45,0,4),(0,32,7,8,5),(40,0,7,0,4),(8,0,7,0,4)]
def g47A : List (List Nat) := [[],[33]]
def g47D4 (j : Nat) : Nat := 0x5bd4910
def g47D5 (j : Nat) : Nat := 0x209908600f140fd21fe10fd10
def g47H5 (j : Nat) : Nat := 0x700
def g47D6 (j : Nat) : Nat := 0x13808bf
def g47H6 (j : Nat) : Nat := 0x84e8001125000000070000000000
def g47L : Nat → Packing
  | 4 => (1,2,3,0,0,0,0,g47D4)
  | 5 => (3,1,3,0,0,5,0,g47D5)
  | 6 => (1,0,3,0,0,0,0,g47D6)
  | _ => emptyPacking
def g47I : Nat → Nat → Option (Nat × Nat)
  | 5 => lookupWord 1 2 0 6 1 1 g47H5
  | 6 => lookupWord 3 23 5 7 2 1 g47H6
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
def K47 := extendKnown K31 7 [(47,[]),(55,[67,16]),(79,[101]),(151,[117,101,67,16])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V47 : Known true K47 := extend_ok (m:=47) V31 low47 (by decide +kernel)
def g59Y : Array (Bits × Bits) := #[(0xc0007fe61339f0001ff984ce7c0007fe61339f,0x94a529461228a5294a51848a294a529461228a),(0xc00f83e863cf3003e0fa18f3cc00f83e863cf3,0x6318c628618518c6318a186146318c62861851),(0x0,0x0),(0x1f07c107cf1c07c1f041f3c701f07c107cf1c,0xa5294b048d14294a52c123450a5294b048d14),(0x3e0f801f80fe0f83e007e03f83e0f801f80fe0,0xc6318d5007a0318c635401e80c6318d5007a0),(0x3ff0001fff000ffc0007ffc003ff0001fff000,0x318c630ab7000c6318c2adc00318c630ab7000),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def g59C : List ColumnInfo := [(2,0,57,0,4),(1,0,58,0,4),(8,0,51,0,4),(16,0,43,0,4),(32,0,27,0,4)]
def g59A : List (List Nat) := [[],[49,84],[16,67],[16,64,48,83],[48,16,81,65],[48,81],[64,83],[64,81,49,48],[80,49,65,16],[80,65]]
def g59D4 (j : Nat) : Nat := 0x5dd4530
def g59D5 (j : Nat) : Nat := 0x1030fd30fd10
def g59H5 (j : Nat) : Nat := 0x30000
def g59D6 (j : Nat) : Nat := 0x23408bf
def g59H6 (j : Nat) : Nat := 0x12652d040000874a916002100d8127003
def g59L : Nat → Packing
  | 4 => (1,2,3,0,0,0,0,g59D4)
  | 5 => (2,1,3,0,0,3,0,g59D5)
  | 6 => (1,0,3,0,0,0,0,g59D6)
  | _ => emptyPacking
def g59I : Nat → Nat → Option (Nat × Nat)
  | 5 => lookupWord 1 2 0 9 1 4 g59H5
  | 6 => lookupWord 3 13 4 9 1 4 g59H6
  | _ => fun _ => none
def g59 : Forest := ⟨59,6,fun i => g59Y[i]?.getD (0,0),g59C,g59A,g59L,g59I⟩
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
theorem g59P5_0 : block g59 5 0 2=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g59B5 : block g59 5 0 2=true := g59P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g59P6_0 : block g59 6 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g59B6 : block g59 6 0 1=true := g59P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g59T : checkedTables g59 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g59 0 0 0 = true)
  · exact (rfl : block g59 1 0 0 = true)
  · exact (rfl : block g59 2 0 0 = true)
  · exact (rfl : block g59 3 0 0 = true)
  · exact g59B4
  · exact g59B5
  · exact g59B6
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g59G : graphValid g59 (boundsBefore K47) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low59 : Lower true (varsX 59) (graphGoal 59) 7 := lower_forest (g:=g59) (i:=0) (hints:=3211265) (before_sound K47 V47) g59G g59T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K59 := extendKnown K47 7 [(59,[]),(248,[83,81,48,112,97,32])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V59 : Known true K59 := extend_ok (m:=59) V47 low59 (by decide +kernel)
def g61Y : Array (Bits × Bits) := #[(0xf0c27ff807f8613ffc03fc309ffe01fe184fff,0x50c24a52aaa86125295554309294aaaa18494a),(0x0,0x0),(0xfb0c7398007d8639cc003ec31ce6001f618e73,0xab0c318d55558618c6aaaac30c635555618631),(0xc0f9ce07f8607ce703fc303e7381fe181f39c,0x2c0914a11116048a50888b0245284445812294),(0xff01f078007f80f83c003fc07c1e001fe03e0,0x3ea01f01999f500f80cccfa807c06667d403e0),(0xfffe007f807fff003fc03fff801fe01fffc00,0xc156e0066660ab7003333055b80199982adc00),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def g61C : List ColumnInfo := []
def g61A : List (List Nat) := [[],[80,66]]
def g61D4 (j : Nat) : Nat := 0x1f
def g61L : Nat → Packing
  | 4 => (1,0,1,0,0,0,0,g61D4)
  | _ => emptyPacking
def g61I (_ _ : Nat) : Option (Nat × Nat) := none
def g61 : Forest := ⟨61,4,fun i => g61Y[i]?.getD (0,0),g61C,g61A,g61L,g61I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g61P4_0 : block g61 4 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g61B4 : block g61 4 0 1=true := g61P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g61T : checkedTables g61 4 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g61 0 0 0 = true)
  · exact (rfl : block g61 1 0 0 = true)
  · exact (rfl : block g61 2 0 0 = true)
  · exact (rfl : block g61 3 0 0 = true)
  · exact g61B4
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g61G : graphValid g61 (boundsBefore K59) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low61 : Lower true (varsX 61) (graphGoal 61) 5 := lower_forest (g:=g61) (i:=0) (hints:=3473410) (before_sound K59 V59) g61G g61T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K61 := extendKnown K59 5 [(61,[]),(62,[67,16]),(91,[100,66,82,33,16,48]),(122,[64,83,96,32,16]),(155,[116,100,84,33,49]),(203,[84,117,100,33]),(205,[84,117,100]),(217,[117,48,96,32]),(218,[83,117,48,67,96,32,16])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V61 : Known true K61 := extend_ok (m:=61) V59 low61 (by decide +kernel)
def g107Y : Array (Bits × Bits) := #[(0x7f03f59327f03f59327f03f59327f03f59327f,0x4a49251224a49251224a49251224a49251224a),(0x730079e3c730079e3c730079e3c730079e3c73,0x31b6d8e1c31b6d8e1c31b6d8e1c31b6d8e1c31),(0x0,0x0),(0x9cff8e7cf9cff8e7cf9cff8e7cf9cff8e7cf9c,0x14249048914249048914249048914249048914),(0x0,0x0),(0xe01c0f80fe01c0f80fe01c0f80fe01c0f80fe0,0xe0db6f806e0db6f806e0db6f806e0db6f806e0),(0xe00fff000e00fff000e00fff000e00fff000,0xdb6fb7000db6fb7000db6fb7000db6fb7000),(0x0,0x0),(0x0,0x0)]
def g107C : List ColumnInfo := [(32,0,75,0,4)]
def g107A : List (List Nat) := [[],[101]]
def g107D4 (j : Nat) : Nat := 0x3f
def g107L : Nat → Packing
  | 4 => (1,0,1,0,0,0,0,g107D4)
  | _ => emptyPacking
def g107I (_ _ : Nat) : Option (Nat × Nat) := none
def g107 : Forest := ⟨107,4,fun i => g107Y[i]?.getD (0,0),g107C,g107A,g107L,g107I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g107P4_0 : block g107 4 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g107B4 : block g107 4 0 1=true := g107P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g107T : checkedTables g107 4 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g107 0 0 0 = true)
  · exact (rfl : block g107 1 0 0 = true)
  · exact (rfl : block g107 2 0 0 = true)
  · exact (rfl : block g107 3 0 0 = true)
  · exact g107B4
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g107G : graphValid g107 (boundsBefore K61) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low107 : Lower true (varsX 107) (graphGoal 107) 5 := lower_forest (g:=g107) (i:=0) (hints:=53477377) (before_sound K61 V61) g107G g107T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K107 := extendKnown K61 5 [(107,[]),(109,[33]),(121,[65,33,80]),(182,[118,67,16,32]),(186,[118,48,49,64,81,32]),(233,[96,113,65,33,80])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V107 : Known true K107 := extend_ok (m:=107) V61 low107 (by decide +kernel)
def g199Y : Array (Bits × Bits) := #[(0xc003ffc30f3cf000fff0c3cf3c003ffc30f3cf,0x892492430a28a2492490c28a2892492430a28a),(0xc0fc0fcc33cf303f03f30cf3cc0fc0fcc33cf3,0x5249248c218614924923086185249248c21861),(0xfff0303cf3c03ffc0c0f3cf00fff0303cf3c,0x2492493014514924924c051452492493014514),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0x3f00003fc0fc0fc0000ff03f03f00003fc0fc0,0x71c71ea80fc01c71c7aa03f0071c71ea80fc0),(0x3f00003fff000fc0000fffc003f00003fff000,0x38e38e157f000e38e3855fc0038e38e157f000),(0x0,0x0)]
def g199C : List ColumnInfo := [(0,64,7,128,5)]
def g199A : List (List Nat) := [[],[118],[33],[33,118],[16],[16,118],[16,32],[16,32,118],[32,16],[32,16,118],[32],[32,118]]
def g199D5 (j : Nat) : Nat := 0x3f
def g199L : Nat → Packing
  | 5 => (1,0,1,0,0,0,0,g199D5)
  | _ => emptyPacking
def g199I (_ _ : Nat) : Option (Nat × Nat) := none
def g199 : Forest := ⟨199,5,fun i => g199Y[i]?.getD (0,0),g199C,g199A,g199L,g199I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g199P5_0 : block g199 5 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g199B5 : block g199 5 0 1=true := g199P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g199T : checkedTables g199 5 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g199 0 0 0 = true)
  · exact (rfl : block g199 1 0 0 = true)
  · exact (rfl : block g199 2 0 0 = true)
  · exact (rfl : block g199 3 0 0 = true)
  · exact (rfl : block g199 4 0 0 = true)
  · exact g199B5
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g199G : graphValid g199 (boundsBefore K107) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low199 : Lower true (varsX 199) (graphGoal 199) 6 := lower_forest (g:=g199) (i:=0) (hints:=1728053249) (before_sound K107 V107) g199G g199T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K199 := extendKnown K107 6 [(199,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V199 : Known true K199 := extend_ok (m:=199) V107 low199 (by decide +kernel)
def g63Y : Array (Bits × Bits) := #[(0x3ffc1810f4dc3cf00003f03ffc1810f4dc3cf,0x28a281810a09408a28a28a28a281810a09408a),(0xfc0fc20633b27d33000fc0fc0fc20633b27d33,0x45144206212029214514514514420621202921),(0xfff02c183cc38e3c000000fff02c183cc38e3c,0x92492c1814c2861492492492492c1814c28614),(0x301fc0fc0fc003f03f0000301fc0fc0fc0,0x1451701480f40f401451451451701480f40f40),(0x3fe000fff000fc0fc000003fe000fff000,0x1861b94000dfd0001861861861b94000dfd000),(0x3fffff000000fff00000003fffff000000,0xe38e06ab7f000000e38e38e38e06ab7f000000),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def g63C : List ColumnInfo := [(2,0,61,0,5),(1,0,62,0,5),(4,0,59,0,7),(8,0,55,0,7),(16,0,47,0,7),(0,32,7,24,6),(32,0,31,0,6)]
def g63A : List (List Nat) := [[],[16,67]]
def g63D5 (j : Nat) : Nat := 0x4ef7258610
def g63D6 (j : Nat) : Nat := 0x81102100400410802f3185b400bf58610fbd8910fcc4210bbd8910b758c10bb58810
def g63H6 (j : Nat) : Nat := 0x500
def g63D7 (j : Nat) : Nat := 0x196f2804756bca101d972e8407888807f843fa21fc10
def g63H7 (j : Nat) : Nat := 0x1000000000000001d4034803824c0000028401e40000
def g63D8 (j : Nat) : Nat := 0x5d1a17f
def g63H8 (j : Nat) : Nat := 0x2290001e73000000000
def g63L : Nat → Packing
  | 5 => (1,3,3,0,0,0,0,g63D5)
  | 6 => (6,2,3,0,0,6,0,g63D6)
  | 7 => (3,1,3,0,0,7,0,g63D7)
  | 8 => (1,0,3,0,0,0,0,g63D8)
  | _ => emptyPacking
def g63I : Nat → Nat → Option (Nat × Nat)
  | 6 => lookupWord 1 2 0 6 1 1 g63H6
  | 7 => lookupWord 2 23 5 8 3 1 g63H7
  | 8 => lookupWord 1 11 0 7 2 1 g63H8
  | _ => fun _ => none
def g63 : Forest := ⟨63,8,fun i => g63Y[i]?.getD (0,0),g63C,g63A,g63L,g63I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63P5_0 : block g63 5 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g63B5 : block g63 5 0 1=true := g63P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63P6_0 : block g63 6 0 4=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63P6_4 : block g63 6 4 2=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g63B6 : block g63 6 0 6=true := (@block_merge g63 6 0 4 2 g63P6_0 g63P6_4)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63P7_0 : block g63 7 0 3=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g63B7 : block g63 7 0 3=true := g63P7_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63P8_0 : block g63 8 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g63B8 : block g63 8 0 1=true := g63P8_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63T : checkedTables g63 8 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g63 0 0 0 = true)
  · exact (rfl : block g63 1 0 0 = true)
  · exact (rfl : block g63 2 0 0 = true)
  · exact (rfl : block g63 3 0 0 = true)
  · exact (rfl : block g63 4 0 0 = true)
  · exact g63B5
  · exact g63B6
  · exact g63B7
  · exact g63B8
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63G : graphValid g63 (boundsBefore K199) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low63 : Lower true (varsX 63) (graphGoal 63) 9 := lower_forest (g:=g63) (i:=0) (hints:=3211265) (before_sound K199 V199) g63G g63T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K63 := extendKnown K199 9 [(63,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V63 : Known true K63 := extend_ok (m:=63) V199 low63 (by decide +kernel)
def g95Y : Array (Bits × Bits) := #[(0x3e0ffc8e043d370f3c00f83ff23810f4dc3cf,0x21084208a0428250229084210822810a09408a),(0x7c1f07c1398cec9f4cc1f07c1f04e633b27d33,0x94a529401188480a484a5294a5004621202921),(0x1ff831c60f30e38f00007fe0c7183cc38e3c,0x4a5294b1460530a18525294a52c51814c28614),(0x83e0003e07f03f03f03e0f8000f81fc0fc0fc0,0x8c6318e405203d03d006318c63901480f40f40),(0x7c00003ff8003ffc0001f00000ffe000fff000,0x6b5ad6bfe80037f40035ad6b5affa000dfd000),(0x0,0x0),(0x8000003fffffc000003e000000ffffff000000,0x739ce71bfadfc0000039ce739c6feb7f000000),(0x0,0x0),(0x0,0x0)]
def g95C : List ColumnInfo := [(16,0,79,0,7)]
def g95A : List (List Nat) := [[]]
def g95D7 (j : Nat) : Nat := 0x7f
def g95L : Nat → Packing
  | 7 => (1,0,1,0,0,0,0,g95D7)
  | _ => emptyPacking
def g95I (_ _ : Nat) : Option (Nat × Nat) := none
def g95 : Forest := ⟨95,7,fun i => g95Y[i]?.getD (0,0),g95C,g95A,g95L,g95I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g95P7_0 : block g95 7 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g95B7 : block g95 7 0 1=true := g95P7_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g95T : checkedTables g95 7 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g95 0 0 0 = true)
  · exact (rfl : block g95 1 0 0 = true)
  · exact (rfl : block g95 2 0 0 = true)
  · exact (rfl : block g95 3 0 0 = true)
  · exact (rfl : block g95 4 0 0 = true)
  · exact (rfl : block g95 5 0 0 = true)
  · exact (rfl : block g95 6 0 0 = true)
  · exact g95B7
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g95G : graphValid g95 (boundsBefore K63) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low95 : Lower true (varsX 95) (graphGoal 95) 8 := lower_forest (g:=g95) (i:=0) (hints:=50397185) (before_sound K63 V63) g95G g95T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K95 := extendKnown K63 8 [(95,[]),(159,[118,67,16])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V95 : Known true K95 := extend_ok (m:=95) V63 low95 (by decide +kernel)
def g111Y : Array (Bits × Bits) := #[(0x3e0ffc8f087843cf3c00f83ff23c21e10f3cf,0x10842108a0850428228842108422821410a08a),(0x1f07d3331998cf4cc0007c1f4ccc66633d33,0xa5294a5213109886485294a529484c42621921),(0x1ff823cc1e60f38f00007fe08f307983ce3c,0x4a5294a14c0a60518525294a52853029814614),(0xffe0003c0fe07f03f03fff8000f03f81fc0fc0,0x8c6318c00a405203d006318c63002901480f40),(0x0,0x0),(0x7c00003ff0007ffc0001f00000ffc001fff000,0x739ce73ff0002dfc0039ce739cffc000b7f000),(0x8000003fffff8000003e000000fffffe000000,0x739ce73ff5bf80000039ce739cffd6fe000000),(0x0,0x0),(0x0,0x0)]
def g111C : List ColumnInfo := [(64,0,47,0,7)]
def g111A : List (List Nat) := [[],[101],[33],[33,101]]
def g111D7 (j : Nat) : Nat := 0x7f
def g111L : Nat → Packing
  | 7 => (1,0,1,0,0,0,0,g111D7)
  | _ => emptyPacking
def g111I (_ _ : Nat) : Option (Nat × Nat) := none
def g111 : Forest := ⟨111,7,fun i => g111Y[i]?.getD (0,0),g111C,g111A,g111L,g111I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g111P7_0 : block g111 7 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g111B7 : block g111 7 0 1=true := g111P7_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g111T : checkedTables g111 7 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g111 0 0 0 = true)
  · exact (rfl : block g111 1 0 0 = true)
  · exact (rfl : block g111 2 0 0 = true)
  · exact (rfl : block g111 3 0 0 = true)
  · exact (rfl : block g111 4 0 0 = true)
  · exact (rfl : block g111 5 0 0 = true)
  · exact (rfl : block g111 6 0 0 = true)
  · exact g111B7
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g111G : graphValid g111 (boundsBefore K95) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low111 : Lower true (varsX 111) (graphGoal 111) 8 := lower_forest (g:=g111) (i:=0) (hints:=53477377) (before_sound K95 V95) g111G g111T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K111 := extendKnown K95 8 [(111,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V111 : Known true K111 := extend_ok (m:=111) V95 low111 (by decide +kernel)
def g123Y : Array (Bits × Bits) := #[(0xffd8b909984ce7c00003ff62e42661339f,0x318c6318a9091848a298c6318c62a42461228a),(0x1f07e131f1a18f3cc0007c1f84c7c6863cf3,0xc6318c6110b0a186146318c6318442c2861851),(0x0,0x0),(0x83e0f801ce3e41f3c73e0f83e00738f907cf1c,0x8c6318c0042441234506318c63001091048d14),(0x7c1f003e0fc07e03f801f07c00f83f01f80fe0,0x18c631940f405401e80c6318c6503d015007a0),(0x7fe0003ff0007ffc0001ff8000ffc001fff000,0x6318c62bf0002adc00318c6318afc000ab7000),(0x8000003fffff8000003e000000fffffe000000,0x739ce73ffbdb80000039ce739cffef6e000000),(0x0,0x0),(0x0,0x0)]
def g123C : List ColumnInfo := [(64,0,59,0,7)]
def g123A : List (List Nat) := [[],[80,65]]
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
theorem g123G : graphValid g123 (boundsBefore K111) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low123 : Lower true (varsX 123) (graphGoal 123) 8 := lower_forest (g:=g123) (i:=0) (hints:=53542913) (before_sound K111 V111) g123G g123T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K123 := extendKnown K111 8 [(123,[]),(187,[118,67,16]),(249,[80,65,113,33,96]),(250,[80,67,49,112,97,32])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V123 : Known true K123 := extend_ok (m:=123) V111 low123 (by decide +kernel)
def g125Y : Array (Bits × Bits) := #[(0xc0007fe62c9930c27ff8000ffcc59326184fff,0x94a52946289120c24a5294a528c5122418494a),(0x0,0x0),(0xc00003f84f1e3b0c739800007f09e3c7618e73,0x6b5ad6b8470e1b0c318d6b5ad708e1c3618631),(0x3e0ffc0073e7cc0f9ce7c1ff800e7cf981f39c,0x210842002448c0914a0421084004891812294),(0x1f0001f83f80ff01f003e0003f07f01fe03e0,0xe739cf503f80ea01f01ce739ea07f01d403e0),(0x1ff801ffc000fffe0003ff003ff8001fffc00,0x318c630afc000156e006318c615f80002adc00),(0x3e00001ffffff0000007c00003fffffe000000,0x3def7bdffdbb70000007bdef7bffb76e000000),(0x0,0x0),(0x0,0x0)]
def g125C : List ColumnInfo := [(4,0,121,0,5),(0,4,120,1,5),(1,4,120,0,4),(0,16,77,32,5),(16,0,109,0,5),(64,0,61,0,5),(32,16,77,0,4)]
def g125A : List (List Nat) := [[],[80,66]]
def g125D5 (j : Nat) : Nat := 0x17e52
def g125D6 (j : Nat) : Nat := 0x1ac6881ff
def g125H6 (j : Nat) : Nat := 0x1c
def g125L : Nat → Packing
  | 5 => (1,1,3,0,0,0,0,g125D5)
  | 6 => (1,0,3,0,0,0,0,g125D6)
  | _ => emptyPacking
def g125I : Nat → Nat → Option (Nat × Nat)
  | 6 => lookupWord 1 2 0 6 1 1 g125H6
  | _ => fun _ => none
def g125 : Forest := ⟨125,6,fun i => g125Y[i]?.getD (0,0),g125C,g125A,g125L,g125I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g125P5_0 : block g125 5 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g125B5 : block g125 5 0 1=true := g125P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g125P6_0 : block g125 6 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g125B6 : block g125 6 0 1=true := g125P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g125T : checkedTables g125 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g125 0 0 0 = true)
  · exact (rfl : block g125 1 0 0 = true)
  · exact (rfl : block g125 2 0 0 = true)
  · exact (rfl : block g125 3 0 0 = true)
  · exact (rfl : block g125 4 0 0 = true)
  · exact g125B5
  · exact g125B6
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g125G : graphValid g125 (boundsBefore K123) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low125 : Lower true (varsX 125) (graphGoal 125) 7 := lower_forest (g:=g125) (i:=0) (hints:=53805058) (before_sound K123 V123) g125G g125T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K125 := extendKnown K123 7 [(125,[]),(190,[118,67,16]),(235,[101,116,33]),(237,[101,116]),(243,[84,101,67,115,16,32]),(246,[84,101,67,115,16])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V125 : Known true K125 := extend_ok (m:=125) V123 low125 (by decide +kernel)
def g126Y : Array (Bits × Bits) := #[(0x0,0x0),(0xc0007fe4587330867ff8000ffc8b0e6610cfff,0x9294a5245023208649525294a48a046410c92a),(0xc00003f89e4c3b18727800007f13c987630e4f,0x6d6b5ad88e4c1b18322dad6b5b11c983630645),(0x3e0f8000e78fcc1f9c67c1f0001cf1f983f38c,0x6318c60050a8c151c60c6318c00a15182a38c),(0x1f07c1f07f00fe01f803e0f83e0fe01fc03f0,0xc6318d207d00e4016818c631a40fa01c802d0),(0x1ff801ff8000fffe0003ff003ff0001fffc00,0x318c630df80001aae006318c61bf0000355c00),(0x3e00001ffffff0000007c00003fffffe000000,0x39ce739ffaf57000000739ce73ff5eae000000),(0x0,0x0),(0x0,0x0)]
def g126C : List ColumnInfo := [(4,0,122,0,5),(0,4,120,2,5),(64,0,62,0,5),(0,64,54,8,5)]
def g126A : List (List Nat) := [[],[49,98,84]]
def g126D6 (j : Nat) : Nat := 0xe413f
def g126L : Nat → Packing
  | 6 => (1,0,2,0,0,0,0,g126D6)
  | _ => emptyPacking
def g126I (_ _ : Nat) : Option (Nat × Nat) := none
def g126 : Forest := ⟨126,6,fun i => g126Y[i]?.getD (0,0),g126C,g126A,g126L,g126I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126P6_0 : block g126 6 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g126B6 : block g126 6 0 1=true := g126P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126T : checkedTables g126 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g126 0 0 0 = true)
  · exact (rfl : block g126 1 0 0 = true)
  · exact (rfl : block g126 2 0 0 = true)
  · exact (rfl : block g126 3 0 0 = true)
  · exact (rfl : block g126 4 0 0 = true)
  · exact (rfl : block g126 5 0 0 = true)
  · exact g126B6
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126G : graphValid g126 (boundsBefore K125) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low126 : Lower true (varsX 126) (graphGoal 126) 7 := lower_forest (g:=g126) (i:=0) (hints:=53563680) (before_sound K125 V125) g126G g126T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K126 := extendKnown K125 7 [(126,[]),(189,[118,67,16]),(221,[83,117,99,67,16]),(222,[117,99])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V126 : Known true K126 := extend_ok (m:=126) V125 low126 (by decide +kernel)
def g207Y : Array (Bits × Bits) := #[(0xc0fff01879e10f3cf000fc0fff01879e10f3cf,0x4924901811410a08a24924924901811410a08a),(0x3f03f461a66633d3300003f03f461a66633d33,0x92492461242621921492492492461242621921),(0x3ffc0981c7983ce3c00003ffc0981c7983ce3c,0x24924980c29814614924924924980c29814614),(0xc0000e01f81fc0fc003ffc0000e01f81fc0fc0,0x30c30e01e81480f40c30c30c30e01e81480f40),(0x0,0x0),(0x0,0x0),(0xffe001fff000fff000000ffe001fff000,0xc71c7154000b7f0001c71c71c7154000b7f000),(0xfffffe000000fc0000000fffffe000000,0x38e38eabffe000000e38e38e38eabffe000000),(0x0,0x0)]
def g207C : List ColumnInfo := [(128,0,79,0,7)]
def g207A : List (List Nat) := [[],[33]]
def g207D7 (j : Nat) : Nat := 0x7f
def g207L : Nat → Packing
  | 7 => (1,0,1,0,0,0,0,g207D7)
  | _ => emptyPacking
def g207I (_ _ : Nat) : Option (Nat × Nat) := none
def g207 : Forest := ⟨207,7,fun i => g207Y[i]?.getD (0,0),g207C,g207A,g207L,g207I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g207P7_0 : block g207 7 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g207B7 : block g207 7 0 1=true := g207P7_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g207T : checkedTables g207 7 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g207 0 0 0 = true)
  · exact (rfl : block g207 1 0 0 = true)
  · exact (rfl : block g207 2 0 0 = true)
  · exact (rfl : block g207 3 0 0 = true)
  · exact (rfl : block g207 4 0 0 = true)
  · exact (rfl : block g207 5 0 0 = true)
  · exact (rfl : block g207 6 0 0 = true)
  · exact g207B7
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g207G : graphValid g207 (boundsBefore K126) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low207 : Lower true (varsX 207) (graphGoal 207) 8 := lower_forest (g:=g207) (i:=0) (hints:=1660944385) (before_sound K126 V126) g207G g207T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K207 := extendKnown K126 8 [(207,[]),(215,[118,67,16])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V207 : Known true K207 := extend_ok (m:=207) V126 low207 (by decide +kernel)
def g219Y : Array (Bits × Bits) := #[(0xffe0c0cfc84ce7c00003ff83033f21339f,0x318c6320c0c54848a298c6318c83031521228a),(0x1f07cb09098f8f3cc0007c1f2c24263e3cf3,0x4a52948b090885861465294a522c2422161851),(0x0,0x0),(0x3e0f80c0e0e71f3c7000f83e0303839c7cf1c,0xc6318c4c0e0a2123452318c631303828848d14),(0x7c1f00300ff07e03f801f07c00c03fc1f80fe0,0x94a5297004a07a01e80a5294a5c01281e807a0),(0x0,0x0),(0x83e0003ff0007ffc003e0f8000ffc001fff000,0x18c631b2a0005edc000c6318c6ca80017b7000),(0xfc00003fffff8000003ff00000fffffe000000,0x6318c60d5b5f800000318c6318356d7e000000),(0x0,0x0)]
def g219C : List ColumnInfo := [(3,0,216,0,4),(1,0,218,0,5),(9,0,210,0,4),(16,0,203,0,5),(64,0,155,0,5),(128,0,91,0,5),(18,0,201,0,4),(72,0,147,0,4),(144,0,75,0,4),(192,0,27,0,4)]
def g219A : List (List Nat) := [[],[49,100],[16,67,118],[16,64,48,115,99],[48,16,97,65,116],[48,97,116],[64,115],[64,113,49,96],[96,49,113,64],[96,113],[112,65,99],[112,97,67]]
def g219D5 (j : Nat) : Nat := 0xbdd8530
def g219D6 (j : Nat) : Nat := 0x82006c3faa1fd30
def g219H6 (j : Nat) : Nat := 0x20
def g219D7 (j : Nat) : Nat := 0x98765432012bf
def g219H7 (j : Nat) : Nat := 0xd70000000000a80160c2a2401e1000000464000000086000000
def g219L : Nat → Packing
  | 5 => (1,2,4,0,0,0,0,g219D5)
  | 6 => (2,1,4,0,0,4,0,g219D6)
  | 7 => (1,0,4,0,0,0,0,g219D7)
  | _ => emptyPacking
def g219I : Nat → Nat → Option (Nat × Nat)
  | 6 => lookupWord 1 2 0 9 1 4 g219H6
  | 7 => lookupWord 3 23 5 9 1 4 g219H7
  | _ => fun _ => none
def g219 : Forest := ⟨219,7,fun i => g219Y[i]?.getD (0,0),g219C,g219A,g219L,g219I⟩
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
theorem g219P6_0 : block g219 6 0 2=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g219B6 : block g219 6 0 2=true := g219P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g219P7_0 : block g219 7 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g219B7 : block g219 7 0 1=true := g219P7_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g219T : checkedTables g219 7 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g219 0 0 0 = true)
  · exact (rfl : block g219 1 0 0 = true)
  · exact (rfl : block g219 2 0 0 = true)
  · exact (rfl : block g219 3 0 0 = true)
  · exact (rfl : block g219 4 0 0 = true)
  · exact g219B5
  · exact g219B6
  · exact g219B7
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g219G : graphValid g219 (boundsBefore K207) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low219 : Lower true (varsX 219) (graphGoal 219) 8 := lower_forest (g:=g219) (i:=0) (hints:=1124139009) (before_sound K207 V207) g219G g219T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K219 := extendKnown K207 8 [(219,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V219 : Known true K219 := extend_ok (m:=219) V207 low219 (by decide +kernel)
def g238Y : Array (Bits × Bits) := #[(0x0,0x0),(0x3f311867eb3333f00003f311867eb3333f,0x5555553118654a3232a5555553118654a3232a),(0x3fc26187f3c3c3f00003fc26187f3c3c3f,0xaaaaaac26182b1c1c15aaaaaac26182b1c1c15),(0x3ffc00381f99cfcfcc03ffc00381f99cfcfcc,0x30c30c03815180a8a8c30c30c03815180a8a8c),(0x0,0x0),(0xfc0fc01fe1f00ff0000fc0fc01fe1f00ff0,0xcf3cf3fc00ae1f00570cf3cf3fc00ae1f00570),(0xfff000fffe001fff000fff000fffe001fff000,0xc30c3a854001f570000c30c3a854001f57000),(0xfc0000ffffffe000000fc0000ffffffe000000,0xf3cf3c57abffe000000f3cf3c57abffe000000),(0x0,0x0)]
def g238C : List ColumnInfo := [(0,2,232,4,5)]
def g238A : List (List Nat) := [[],[99,117],[33],[33,99,117]]
def g238D5 (j : Nat) : Nat := 0x7f
def g238L : Nat → Packing
  | 5 => (1,0,1,0,0,0,0,g238D5)
  | _ => emptyPacking
def g238I (_ _ : Nat) : Option (Nat × Nat) := none
def g238 : Forest := ⟨238,5,fun i => g238Y[i]?.getD (0,0),g238C,g238A,g238L,g238I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g238P5_0 : block g238 5 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g238B5 : block g238 5 0 1=true := g238P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g238T : checkedTables g238 5 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g238 0 0 0 = true)
  · exact (rfl : block g238 1 0 0 = true)
  · exact (rfl : block g238 2 0 0 = true)
  · exact (rfl : block g238 3 0 0 = true)
  · exact (rfl : block g238 4 0 0 = true)
  · exact g238B5
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g238G : graphValid g238 (boundsBefore K219) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low238 : Lower true (varsX 238) (graphGoal 238) 6 := lower_forest (g:=g238) (i:=0) (hints:=1664110880) (before_sound K219 V219) g238G g238T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K238 := extendKnown K219 6 [(238,[]),(245,[118,67,16])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V238 : Known true K238 := extend_ok (m:=238) V219 low238 (by decide +kernel)
def g127Y : Array (Bits × Bits) := #[(0xe780000007f01fff8c23c8e043c1810f4dc3cf,0x45142850a142850a0c2288a04281810a09408a),(0x99800003f80fe03f904cc1398cc20633b27d33,0x90a142850a1428509048401188420621202921),(0x1e000000000fffc0608f31c60f2c183cc38e3c,0xa4a952a54a952a560853146052c1814c28614),(0xe07f01fc07f0000000f03e07f0301fc0fc0fc0,0xa003060c183060c18000240520301480f40f40),(0xfe03f80000007f003ff8003fe000fff000,0xe1c3870e1c3874a003fe800394000dfd000),(0xfffc000000007fffc000003fffff000000,0x70e1c3870e1c3835ffc0000006ab7f000000),(0x7f0000000000007fffffffffc00000000000,0x7cf9f3e7cf9f3e7fffdbfadfc00000000000),(0x0,0x0),(0x0,0x0)]
def g127C : List ColumnInfo := [(4,0,123,0,8),(2,4,120,1,5),(2,16,77,32,5),(8,64,55,0,7),(16,0,111,0,8),(32,0,95,0,8),(64,0,63,0,9),(2,0,125,0,7),(1,0,126,0,7),(48,0,79,0,7),(0,96,7,24,6),(7,0,120,0,4),(3,4,120,0,4),(73,0,54,0,4),(9,64,54,0,4),(18,0,109,0,5),(20,0,107,0,5),(24,32,7,0,4),(76,0,51,0,4),(36,0,91,0,5),(96,0,31,0,6),(40,64,23,0,5),(72,32,7,16,5),(69,0,58,0,4),(24,96,7,0,4),(34,16,77,0,4)]
def g127A : List (List Nat) := [[]]
def g127D6 (j : Nat) : Nat := 0x1ca0f0c100001ca080000000069010000000000000000000000000348080068c100040108002000c001000000ba5bad162a9d127d389948e3b1788c2e0aff783a9c8de6c34998c6602e968ae54289389648228f67537980b4421e0d84e18090300c00a7cc8502b84c74ef926057098e9f720c0ae131e3b98f825c241cd6a1f04b84831fb985c0704c71f6ebc0242b053b65e6350a20d7531f00a1441ba943e01428829db2f31c43107395957188620e7331ae310c41ae965602218835d4c6c04431053de457498d20e3ab2ee2a8a416f19598f108433d105c02e68853be497498d10ad7ca2ebb92215af94617724429df20b2ee48853b65663dc910a76c84c7b922156f9550f724423df30ba8e48856be51751c910c7743aca392211ef985d072442bcf22ba0e48847be61731c910af5c82e6392218ee8798c724438dacbb92a28866be137254510bd8ca10098a217e192201314431df0bb92c0884fc2613150110f70b2c4310221ee26388620443dc2ca90a40887b898d2148110a6ecaf0cb98218bd855d2630431bb0ab9cc60853b656635c810
def g127D7 (j : Nat) : Nat := (if j<1 then 0xe8788550bfb8048550afd8598c10cfe635ca40cfe635c6409ff874c6409fd874c640ddd734c640df5714c6409fd81dcd40afd8098d409fd83dc940cfe63dc940dbd43dc940bbf8350940dbf7350940ebe6350940bfb804c940cfe63dc540bbf8350540ebe63505409fe874c5409fc874c540cff7158140ebd4158140ddd855cc10bf9809c530bef825c530bfb805c5309fd8790530bdd8390530fdb804c530fd8804c5309fd8788530bdd8388530bdf83501309ff835d220ff13148110afd8598e20cfd7498e20b7f8550e20ded7350a20eee6350a20fad4350a20efa6348110cfd655c620cfe635c620e7d6554620bbf84546209ff874c6209fd874c620ddd734c620bf78150110eed6588620bed8488620ded7388620eee6388620ef96548110ff13188110aff80595209fd83dd1209ff835d120efa6388110afd8598d20cff7498d20cfd7498d20afd8098d20b7f8550d20ded535c810cfd65dc520cfe63dc520e7d6554520bbf8454520df77154520eed6548520eee6348520aff8059710afd8598f10cfd7498f10afd8098f10cfd655cb10cfe635cb10ef56548710ef66348710aff8558310cfd7458310bf78154310ddd734c310fd5314c3109ff835d210ef96588110afd8598e10cfd7498e10b7f8550e10cfd655ca10cfe635ca10cfd655c610cfe635c610e7d6554610bbf84546109fd874c610ddd734c610df5714c610bfb804c610efa6350210ef96548210efa6348210fd5314c110def724c110ff153c4210bbf845d510aff80595109fd83dd1109ff835d110ff12150110def825cd10ff13150110dec825cd109ff805cd10dfb805cd10afd8598d10cff7498d10cfd7498d10afd8098d10b7f8550d10cfd65dc9109fd83dc910cfe63dc910ded75dc910eed65dc910ded74dc910ded73dc910eee63dc910ded85dc910fe87250110ded84dc910ded83dc910feb7250110ded53dc910ded43dc910cfd655c910cfe635c910efa6350110ded751c910eed651c910ded741c910ded731c910eee631c910e7d6554510bbf8454510def7254510def7250510def724c510bfb804c510fd5434c510fe7724c510fe4724c510ff3804c510ff0804c510ef56588510bf58388510ef66388510ef56548510ef66348510aff8558110cfd7458110ef96050110def7254110bf78154110efa6390110ff13190110def7250110cfd845c263def744c9209ee871c910cee63dc910ced65dc9109ef825cd109ef825d110ef263c4210ef165c42108fd8798e109f7815d120be98088620fe22188110de57188620beb8050a208fd8798e20fe12148110cbd655d010cdf865cc109ef825c630cdd655cc108fd8798c108fd8798e40afb8048560cbd7498c10cdd7398c109fb805cd21be7814ca219ef825c241a7f8059551ced655c810cee635c810cef7258110 else (if j<2 then 0x8101a3e60c0c1820b0d0b00101001c00700100198c2004d90280044011263660e00165640a9016405998c2a405998c26366650c00210164040018d9820293021c3c0870a92942a4068e9a1c30bc0082c082a3880a20108068c1800420180060018007022020c400b021c2a6a3a50c281000a405944428807982c2630791958c3e6a30aa7983038887636612221f91958c50a06480ea7983030b48e60c2e2398301e6480c42a7979a900460a06c04810002c079848f6563888715988e203c3e6880c3b91961e2050aa6480c1b25203c3068e99211c40d23480e8f982a3e60c0f27979b102c50a89230f91958e221c563668887129a8c29ed4f1275d3989c14db26cd3609a94cf265d3289894c125fd2f09714b5259d2b89594a7252d28093949724ad24091548523dd1e08e546f234d1908bd459228d130891447221d10887543921bd0d085d429210d08083d41d20dd06082540f204d0188053ff1fecfe87f13f31f8cfb07cd3d91ebcf587a13cb1e3cf107793b91d9cec875d3ad1d4ce987453a11cfce7072d38f1c6ce2870937f1bccdd06d53651afcd686a534b1a2cd00675331197cca064932118ccc58629313184cc085f92f5177cba85d12e7172cb905c12dd16ccb5059d2cb163cb185852bf15dcad05652b1154caa054529d14cca4852128f145ca28511285141ca004fd27b13ac9c04d526712fc9784ad255129c94049924311dc8c8459227111c88843d21b10ac840411207101c7f83f11f50f6c7a83c51dd0ebc7503a51cf0e5c72038d1c10dfc6e836d1b30d5c6a034519f0cdc65832518d0c2c61030517f0bdc5e82f11730b8c5a82c915f0adc55029d1490a1c50027913909ac4c825d12b093c488239117087c430215109082c4001f90f7079c3b01cd0df06ac3281850bb059c2b0149097046c2100f1071034c1780ad04f025c108075035016c08803500f002c000df5714c620cfd825c263cfe815c263cfd815c2639fd81dcd429fd80dcd42afd8098d42cfe63dc542cfe63dc142dbd43dc1429fd80dd132cfe635c8109ff805ce41afd8098e41cfe635ca41dbd435ca41cfe635c241dbd435c241cfd655c8109fd80dcd41afd8098d419fd83dc941cfe63dc941dbf7350941ebe63509419fd83dc141cfe63dc1419fd80dd1319ff805d131bfb805c931bf8805c931bf78150931bf5819c131dfb709c131bef825c131bbd841c131bed821c131df9701c131aff80596219ff805ce21afd8598e21cfd7498e21afd8098e21ded744ca21ddd7354c10cfd655c221cfe635c221aff80595219fd83dd1219ff835d121dbd7454c10afd8598d21cff7498d21cfd7498d21afd8098d21b7f8550d21def7350921eee6350921e7d6554521bbf8454521cfd65dc121cfe63dc121aff8050560cff7588560afd8488560cff7548560cfd7498c109f else 0x10580482650a0980342040008180c20008405941020004003060b10101941800594100180c2000c18200021c280040c182000400203060b9b0c2e601a0c3100c107080b0c1e6c30b9b0c2e6c309830c2850ac00c0c182c0040c0040a605230c003001030608180c2a6a3a50c00000300104870a1c1a4c00b00163058c102801028220200180c2c3050855142b100f0060000306080c18207040c10401000f101030608065040000600104040022010603080800043011c1660e080c1c2e6c3080c3420306010010210c208030a0c5820306010c04210c3024308180c20b010855142b004031a0f00304061011104650e0010001443a4c0131b0f0030306080c180430107080b0020000008004041c0040c18206030a001c00404707001c005998d943000a487c00c005a40a1e2028806142920300048040020010220102941072308208c206030a00115450a0c0c683020c0020018004510e921c4c6c3870c0c18040040708080c20208040800600108230a9a8c26663650c0c0040c18206030808100a3e60c0))
def g127H7 (j : Nat) : Nat := 0x98000000b24df2c6f0011c24f8c089ab00000000cf001d600000003c300000528640026a00299c25410024747fc583a516879b580007a45a39400b9c0035c000b6a8675e36b8660000085000003c6001440018200000003920031e000003215514000003801004081001800105
def g127D8 (j : Nat) : Nat := (if j<1 then 0x93704da93660d793576d42349ad07b3a2cc632aac8bb1a4c46b0acc0fafdebd8aee6b972deeb672d20b292c52af22b5aab42a46a76296aa3f289ca0127969c3269e98fa5a694e24d891e24428f523588b3a260879217683ea0708041fcc7d79f0c7ab1e5a7821d9a74e9cbe7109bd46d29adc6981a0e664994e634983a5f3176c5bc166657e159854714bc505938c4c7929448d11e24641130437907e3fd0f783c28eaa3880db23548cf231a0bec2df8b482b68a42267092e230086020007bc1d706ee199061216205361358484102038c0c7829408d01aa05280dc01f0001ff5d130ffa62a07fd53043fe98a21ff50510ffaa2887fd50443fea1a21ff54d10ffae6887fd74443febaa21ff4c610ffa83087fd51843fea1c21ff54e10ffa61887fd50c43fea9e21ff4c120ffa80907fd50483fe98a41ff50520ffaa2907fd43483fea9a41ff4c620ffa83107fd51883fe99283ff50e20ffaa7107fd404c3fe90a61ff88530ffee898ffd414c3feba263ff90530ffae2987ff724c7ff38a61ff5c931ffa8498ffd424c3fea0a63ffdc131ffae4987fe704c7feb8263ff1c131ffa80887fd418c3fe90a81ff4c940ffaa710fff72503ffb9a81ff4c640ffa60887fd21543ff10aa1ff4c521ffa8290ffd53487fea1a43ff54521f7a82a06fe63486feb9a437fdc121ff240886fd425837f20ac1bf50560dfc42b06fd21583fd102217f5ca50bfae3285ff72542ffb8aa17fdcd21bfae890dff74486feb9c81bf98e40bfae5205fd719037eb2a437f5c221bfee6a06fe63503dea1a81fb4ca21bfee4a07bd425037f31c437fdc540dfac0885fd744c2feb9c43bf58140bfae9185fd728c2feb8c617f5d221bfee8987f9404437eb2c437fdc930bfee098fdd324c7ee992617fdc530bfee498fdd434c6feba2637fdd131fba62985fd708c6feb94637f5d231dfacb105fd74882feb9c41bf98e20dfaca085ff70507f6a14417f5c620f7a84a0dff725077f31a83fb88620dfaca905ff74482feba2417fdcd20bfae6906fe63482ffb9a837f5c241fda64905ff71482feb9483ef50e41dfcc720fed214837eb02417f5ce41bfee0a8dff725477eb2e217f5d310bfae7886fe63c42feba0217f5cb10fea63887f521c437eb06217f5cc10bfae128efd65842feba4217f5ce10dfcc7085fd72946ffb82657f5ca10bfae3085ff714cbf6a12657f5d132ff281087f920843fd202217fdd132dfaca885ff74442ffb82857f5d110bfee6885ff7150afeb9a21bf98d10f7a86a16fe6350affb9221fbdc910bfee6a15fd72443f6392217fdc152bfee2a97f6314437f31821fd4c510fec42887f521443f6a12437f5c810fe621084ff70596f6b90215f5d640b7ae9284ff75582beba8215f5d631b7ee8a8dbd740433eb2aa3775cc10afeeaa1cfd7098e7ebacc77bdc910 else (if j<2 then 0xc13210021e28a888e4408e3c90607044cc0878a2a240462e38820501004416686a48141420280233230e48c8f26223c0207879808004a44242050504121e6022101214566080804316209523c466480a00e000e686a52021d4e6029040218529c8951c8811c80a28202cd0d001205050410608cd0f0120c1200f98b0c1f320065860a14543080800c1a4051410143cc8061063303480851404029119a1a40448002a4108cd0c7043008d0e233032c48a0a10066050c0872428acc10143163a91e2334348087288d4c74b0240ea41e6109010c1828a0808687470041514544471e0481ca0a53912a3812239324180180b30f1d4e5cc924011828a08081e6029e008281660e24601403c9079860140340931d1c888366909c353923a5472200ea41e6169244004429079920719220022428a08091e61638a0a0821203991902a2c48e8e4401c001923c4664710893941e6002e2010e4ca479840c02301cd90589272e6882d0011cc098f9918b024c4471e40d98388160452e311c0162800324388cc8c70004b661464692586668a280a020529c8960238f208523c066480838e282840400087cc8c98a2a240471e40ea730f00084240e4661680087146ca0404407cc8c8cc2d0011228a882d1e08e20815991e505900e00e20a005b30a920438e511c0531e40ca41e602001084840a0b9810400311882628a888e0479038b11985200230a0b98104190c0902c1e6400440c14504079800b04043882c505cc082431900092a7300099618c1c50580304668690112a7301482010c0b320100455290266162a980084668634046a644715483cc2d2021a4e5200f30c88a2012a4181009010fcc4051410123cc2c792401e618086141410400306e64648a8b12023911c74a6016647006931d1c8890060a28202079858140480cb931e617223912439011991c41c0e6161e5c98f30b911c79210b03181f30a8b00a9210b038030088cd1451728588cc8c1011e28a888e0488e3ca18203e646366182c14840366182d008a7324041c60c2c1e602804071c388cd8f282c80701252483c0a0516071e50590407cc4c42c2f008148822c2f00818529065e40a28164021f008cc40acc0b24303803904410a2d8f0471c782c794088c01f312284e4478238c37281c8083e011989159a243c00861b94564078140e54529c80f00da45e5c98e3e69045b336bbda5767a599764dd8c961357ed5e6d7655c856c1598560155dd50952dd4574fdd3974d4d2f34a8525d47bd173444d0b34114fd73da4ed13954e0336c4d5f346ccc93134bfb2ea4b652c14aa528a49bb256c91722dc88120bc7b31d4c6f31a84633171458f152c4dd11f44010e843330bbc28f084c1c1054c0e5016c016ff13f64fc13e88f8a3dd6f5a3cdef26bc3aeefbb50ebc3a90e8539a6e4e38d8e1e37d2dd else 0x662c94124230c74c091c410a884d18523880d2c0291a6160e0080e3c01e2010714524806440719323141600710391168d325090011028aa6469600c8d30c40345188078690620322234d181880e346863c4020e3461490c880e311108d346069420224a884d185234a3a61a1d188153230a2838818a8a0e991a51930b188c44018101490044c8c5014b00616980a38028f04920080458514903c01c08b46992840500814553234b0064d18087470061f1a182029200e6630514900c01c10f469800188391108d346069420280515109a30a4696011181048620517186208628d8c3104317324050c4043e324862e62c941241e46190343c6490c5cc2d00d862e64006189992961a1e18d98581404a18c423040480087864108c10120190c7871810f061c611983c31330b02809431b343101e616806c3173252c91007862080412007cc2061e22302490c6022c12088292469800c111072a283a6469600e001440d32305104109a2960e8e20e985c01a1d18c045c686290088a44686280a08a3234c2c1810f0071e09240105154c8d2c01808b46992840500814900a58028c021c466120871516247472200e28282088f34010309199b18b10166100500aa728c872100ca520b111a18c806294e223248642514910431630c402218b14582cc200c7403c9085818acc0442024b0b92204925b30a400462c0c08011985492028a08091e6163a907986240432907992021630600306874724410291c08f262481e48b0798420023c9079a20b103294b1d1c88030514101e6182c128801cb0404007cd2518f023a3932220c30466462410d291e618249ca0f34418800919840))
def g127H8 (j : Nat) : Nat := 0x22e09fee72332400f156848641d22d498cd5a07000000000000038fd1b6e8c00069d097ae81000000251e000000000256800000000000004c1000688cde0000f2f6015c3800025e399a89e0000005104001a590000002d7f2b90006a6a9fc00000019570a8e49f4060d8001a7517880000006c73080000001c380005b3a9f6e358328000db1ac3774840400000000003d4000cfc7191c3048fa4be4e2b148e70a022d80000016c40200001522e16041000000005800078c000127900053c8000907568cbb62120000000000000000000000000000000000000000000000002e1e0000000000c694ae54800000000005659b92cfa00000059418d34a50005a880000000002b494260000000000001cb10004400000000d0900039d46e5e4418a25c26df0048a4c001c998300000001e0b000000000000000022c288c00023d0a2bdc02eea0b8a989e600064a6abe457508c830002198edd700c8ee5dfc6bc220002a0800034eebdc00000000000000012be53090561240000003ad8000000000734e56fefa0001a869760000002218001aeb73b7170000e3d71073a0828000004440a4e24e24668001cba0000002968000cb300000004d166a00000021084c827c0000001ac600000018a4c3900d881adb2e3e216829101ace6f4b9bf4000a62736000b1920000004ae893c000000606ac4e00000060985f341e0005b3c0adcb5e18d43800102c114c01285faadb81b9fad540000005bd8000411d43b3b252d6e353ff28e47520f711000000165f06bfa6000187750fc1bc00000000000035ce000000194488b6da00032a0001833f1e000100e0000004c2c9a88190007828000000061718c00168d0000000001a21036c37b0f60000004a540012a90005a7c000000000000350a000f47310a854000f380000001653253800161a0003850000000000627000000000044d80000000009128000000000517412bdac000921800215800000050df964000f0ea15c00044d000119c00000000023030f00000004b2b418000000000000000000068614f800040049ba1e9489f1264151a08dc000001000010081801000000c00010180000000080207010000a0d000003e020103c0008020000e030380000020000c1405008240201000240202008040c000280002050100c0c02048000202
def g127D9 (j : Nat) : Nat := 0xaa411e69648c02c82caa403269648cb2072d52262899038081d84489899440e008b1c828958c0474072262448c03022921c89a55a40c03012c82899168c18072482899168e01c82262442e30601c908f2262651238072852265a50a40c18072c89969640e01c80caa403269648cb1c830aa412269648c02c72ca9a59028e004720a1831cb8095882060c72895a02080cc1e68cb80910828798912380220898c1e590b8160c828d1e69569038082432a91e69640630082c52840e68e50a40018081ce2889a59022e30072899038042a59038051a52a40e0207cfd8db005b8b1151a7f4c2919142073c6720d097d2b8504931051d4324558870b40e415018000ff483fd10ff54ffd43ff54bfd42ff4cbfe51ff547fe41ff507fe31ff4c7fe10ff487ff10ff943fd50ff903fd40ff8c3fd30ff883fc10ff886fd65bf98efd60
def g127H9 (j : Nat) : Nat := 0x67be775b60d7000c5400000049e0000000009c200000006600018200028600000072eda550a9632c847279a0002dc3815b1000eb8000000c65d59000b78000000271000302ead2a6606000000000346ad800083344774c67600002c000e1b1b53640001da475bbc58afae000000837000000fcb000000000000000d5bbc51388b70110913ba000fd6e490008620006ced8343a0000008a0000000000205d502d4f6fe80000a8571a000295000000000000000e990008a78af00005ee27000ed20000000000007b0cdb000d8b7a87b9d24dc0e13000b690cf000000655000000d930007d100000043d00041900000000000000000034e000e09458625000000f790000000000aa33b910a570000000000bdd48c08290aab944ba146ae0709c000a29e6e000e97f4500001eb8f0848cca611c39d5f8d00000000054a6328b303e00016be4f00043600055c00008829fa87d5600000000000070b47ee9487a6acc21c92ea4dd341d32ae28c39052712f3f000b3400000000d000bc462f000c420740002355043be4701a954d9229a244b00007c000000000000168896789bd9000000260e5100000000040e00000000015a0000c6a0c000801fcdc9da7300056c69812d42bd1648e0000000004b4dbf2153c153cb0097fc1cfa3318000b6d0230000000000009c7000f53e3000091fe03167340000000000000dca000000e1700000000000000000065d614320000000e2600068cd7db0f0c909b000c411316b20000001d05bb000000000000000000b4300000000000000000000000015f000000000020540201008000a07000180603018000c08000003801050100202010000e0c038080c00008001e05000182809070081400030000203008000404030241005
def g127D10 (j : Nat) : Nat := 0x24c520c037f
def g127H10 (j : Nat) : Nat := 0x1133a00000000025e21a0005900226250000282000000000000001800f500000000000000000022002b600f38b000000000000005b80000620035800000500000d4618005e6d0000000713c4649c000058000000000000000000608000
def g127L : Nat → Packing
  | 6 => (48,4,5,0,0,9,0,g127D6)
  | 7 => (272,3,5,0,0,13,0,g127D7)
  | 8 => (221,2,5,0,0,14,0,g127D8)
  | 9 => (28,1,5,0,0,11,0,g127D9)
  | 10 => (1,0,5,0,0,0,0,g127D10)
  | _ => emptyPacking
def g127I : Nat → Nat → Option (Nat × Nat)
  | 7 => lookupWord 12 79 7 10 6 0 g127H7
  | 8 => lookupWord 68 479 9 13 9 0 g127H8
  | 9 => lookupWord 56 389 9 12 8 0 g127H9
  | 10 => lookupWord 7 79 7 9 5 0 g127H10
  | _ => fun _ => none
def g127 : Forest := ⟨127,10,fun i => g127Y[i]?.getD (0,0),g127C,g127A,g127L,g127I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P6_0 : block g127 6 0 48=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g127B6 : block g127 6 0 48=true := g127P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P7_0 : block g127 7 0 31=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P7_31 : block g127 7 31 48=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P7_79 : block g127 7 79 48=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P7_127 : block g127 7 127 48=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P7_175 : block g127 7 175 48=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P7_223 : block g127 7 223 48=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P7_271 : block g127 7 271 1=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g127B7 : block g127 7 0 272=true := (@block_merge g127 7 0 127 145 (@block_merge g127 7 0 31 96 g127P7_0 (@block_merge g127 7 31 48 48 g127P7_31 g127P7_79)) (@block_merge g127 7 127 96 49 (@block_merge g127 7 127 48 48 g127P7_127 g127P7_175) (@block_merge g127 7 223 48 1 g127P7_223 g127P7_271)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P8_0 : block g127 8 0 16=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P8_16 : block g127 8 16 48=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P8_64 : block g127 8 64 48=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P8_112 : block g127 8 112 40=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P8_152 : block g127 8 152 48=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P8_200 : block g127 8 200 21=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g127B8 : block g127 8 0 221=true := (@block_merge g127 8 0 112 109 (@block_merge g127 8 0 16 96 g127P8_0 (@block_merge g127 8 16 48 48 g127P8_16 g127P8_64)) (@block_merge g127 8 112 40 69 g127P8_112 (@block_merge g127 8 152 48 21 g127P8_152 g127P8_200)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P9_0 : block g127 9 0 3=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P9_3 : block g127 9 3 25=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g127B9 : block g127 9 0 28=true := (@block_merge g127 9 0 3 25 g127P9_0 g127P9_3)
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
  · exact g127B6
  · exact g127B7
  · exact g127B8
  · exact g127B9
  · exact g127B10
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127G : graphValid g127 (boundsBefore K238) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low127 : Lower true (varsX 127) (graphGoal 127) 11 := lower_forest (g:=g127) (i:=0) (hints:=53542913) (before_sound K238 V238) g127G g127T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K127 := extendKnown K238 11 [(127,[]),(191,[118,67,16])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V127 : Known true K127 := extend_ok (m:=127) V238 low127 (by decide +kernel)
def g223Y : Array (Bits × Bits) := #[(0xf3c0000003f80fffd00c00c3cf23810f4dc3cf,0x228a142850a14285100c00c08a22810a09408a),(0x4cc00001fc07f01fc230210d3304e633b27d33,0x48512244891224488230210921004621202921),(0x8f0000000007ffe024c0c60e3cc7183cc38e3c,0x8524c993264c993264c0c60614c51814c28614),(0xf00000fe03f800000700f80fc0f81fc0fc0fc0,0xd030e1c3870e1c384700f80f40901480f40f40),(0x7f01fc0000003800fff000ffe000fff000,0x68d1a3468d1a3780094a000ffa000dfd000),(0x0,0x0),(0x3f80fe000000003fff000000ffffff000000,0x70e1c3870e1c3b8aa0000006feb7f000000),(0x3fff00000000003fffffffff000000000000,0x3870e1c3870e1c07556b5fff000000000000),(0x0,0x0)]
def g223C : List ColumnInfo := [(13,0,210,0,4),(2,4,216,1,5),(4,0,219,0,8),(1,0,222,0,7),(64,0,159,0,8),(8,0,215,0,8),(1,8,150,64,5),(2,16,77,128,5),(128,0,95,0,8),(16,0,207,0,8),(72,0,151,0,7),(7,0,216,0,4),(3,4,216,0,4),(2,0,221,0,7),(0,128,15,80,7),(68,0,155,0,5),(80,0,15,0,5),(144,0,79,0,7),(0,64,23,136,7),(16,64,7,136,6),(8,128,7,80,6),(64,128,15,16,6),(136,64,23,0,5),(73,0,150,0,4),(24,0,199,0,6),(18,0,205,0,5),(192,0,31,0,6),(130,16,77,0,4)]
def g223A : List (List Nat) := [[],[16,67,118]]
def g223D6 (j : Nat) : Nat := 0x7202e8040000000000000e01080ce500b884008206b2806c425901009880ce511c80b88100b882b120c200d882310042008002c4deae96eb458ab956a852a65087cb3d8096439e0c04818060019cd63e09718c3752a9c028510573e4d75dc910ae7c9b0bb922156f9558f724423df30ba8e488573e4d751c9108f7cc2e6392215eb905cc7244339f07b92a0884fc2613150110cf8caf0e880215f397615100433e70ec2a200867ce1d6544010ef0c2ae488021de1655c9100433c725c3a200867824b8744010cf1c3f04880219e38720910042bc530b9220085782617244010
def g223D7 (j : Nat) : Nat := 0x2341010209a0109041c08043640590164070811009680c006650162130810006405901030810022a42c2041c18d06901640418100010b0810f650a94164650806505901001c165040a804380c2c2830a941a9041f080c3a98d099014200042e0c2000c88081c18046002c1e8e4e907e5060b1c33a2a4044e4c5830c2e0c20b62830d880794300042fa01baba41f9480be806eae907e201e5265b4a0925212334588950f217410814f91eb3d0794ef1d73a8734e51bf3706c4d51a3338654c51832f05c4b31632b8554a914b2885049d12f2484748b1071f83c4750df1b83045f0b71302143b06b0b813425027000fe872501109fd81dcd40dbd54dc940bfb804c9409fc874c540ddd635ca30ddd635c630ff16544010aff8655220fad5450a20ded7350a20ff18544010bbf84586209ff8754620ded7388620ded655c810ddd655cc10aff8655120b7f8558d20bbf8458520df77158520bdf8354120aff8655210bbf8458610bfb8054610ff165c4210bdf835d510ff13148110b7f8558d10ded75dc910def724c110ded85dc910ded65dc910ded83dc910ded63dc910ded43dc910ff13150110ded751c910ded731c910def7258110bf78158110bdf8354110def7254110def7250110bf78150110feb7250110ddd63dc532ded73dc910fe221881109ef825cd10fe121481109f7815d120be98088620df38744010beb8050a209ef825c630fe38244010fe08244010df172440109ee871c910de172440109f38744010
def g223H7 (j : Nat) : Nat := 0x59c00f1d8510800c4800b3000001960000b00208d10d4cd400034ab14d4f93a86e4129d57893020a70d01f440000171c0000001
def g223D8 (j : Nat) : Nat := (if j<1 then 0x12428644049103821200a61c20e48e10482290e1828d190809948c03221c51038212121d28b0c48e104820712180902072a4a0808d0c42a180c8a4641c7009418602281d200310382120b2430b0648e10482060a0d1012400d0c0d28a2071304049171c6831604410389ca440460e34181442881c4e50b0630e104c4ca0a041a2247082410305020838352592085028104381d124708241038902092860658e104820712182a2020cb084a894440460848a0ba20c6241288928140834448e10195690f8808d4a0cb1c209040e24322039418d300068a044c814042022ca639228c152312ca17420c38e104824584181a90e50424c43800630e104c4ca0a306928908b1c20989941460107109162070424242820c2c3811a0cd9c054830e287440c088207042424382029431438412081c48104940062c40e08484870a180a228168c9a728b8734816042d1934e5170e68e2070424243a2024435a1000da3487c8046e2065160d13455278a19030395282f1031c951282f10318683d01b5690f880e52b8ead1934e5170c80c4f2811b8818e2f406d5a4383c407294000e80dab487ca3419514951c4185bbe5cdee2b6ecb5e5a4ecd5633b08d7beb9b5abac4d582a53507a72d2f293547fa2b50b67fb3d49e04e5e6dd353998cc3e5cd2b694dc9764692128f8471e32f16e898440218508481c3fe9f5cf857a3bc25db2eb072b3829b98d956b2b4819b6c8162c304d7aab975b02cdd638ad754929a5464a104f026dd30e942477a2a90ae8043ea1e90ebe70c3591a40cce63e30396ecb1653827292108b64391f68e6869c31017e0b1450e27311387a436418209b03e01820750148003fea0c41ff59410ffa60887fd40443fea8221ff58110ffa86887fd63443feb9a21ff59510ffaea887fd41843fea8c21ff58610ffaa9087fd65843fea0241ff54120ffac0907fd31483fea0a41ff54520ffac2907fd43483ffb9a81ff58d20ffaa8907ff72503feb2a41ff54620ffa64a07fd61883fe98a81ff55220ffacb107fd404c3fea0a61ff90530ffa84987fa40442feba261f74c930bfee2985ff744c2feb8c61f74c530bfae5187dd638c2feba4417f5d230bfae7107ed42882feb8c417fdc540f7a84a07fa20443fca02217fdc940bfee8905fd74483dea1a817fdcd20bfae6905ff73503deaa281fb4c920bfee2905fd71902feb94817f5ce40bfee2a87ed21482ffb92a1fe48110bfae3285fd72942feba4217fdc560bfae7085fd72842ffb92c17f5c660bfae5305fd73042feb90217fdc132bfee2997ed424cbeeb1a657f5d132bfee8995ff7054affb8aa57f5c610ff281087f920842ffb9a217f5cd10bfee4887ef72442feb9221fb1c910bfee4987ee21882eeb982177dcd50b7ae93057d75983f9884217bdc910afaea087f110042f6b90215fdd563 else 0x6438153085340c40e24924c5844801a181881c4c21a0c524961171a0c61c2210d062984b0830714b081c902c20c38c440030848d24842251888b88641871a204240c6883949b06345200d404242438e689034820702a610849281490851c05442100018418732054c214080249210a6c40e523610c1c0984b0854a1c22c902868429050243c2141090e1923492108480a484200043128314d881ca40c2183090e19006a0212121e11068903490850e194c5103995314400343298a286000948c8a34e522430b1470824100820e6089c31103141861038212121c3002040e0848101521c810389090f90145160ca9c1c6011a0c50620708241c4e48a041a2298ae2d0c50a3841208182a90e41208c40820e0d490006a50d0818d3b429860451038212121c2810cb6103307082410305038a487299520c308c3441c8161c0830d3510f380a91a0c38c38212d)
def g223H8 (j : Nat) : Nat := 0x1126a7000d2a00000224770000000000006e4003d80008f7c13045cc00000387000eab9a8b400179c8a6130000025bff4843a8df5000c1c4b20f1ef000000006eceeb8009108c04d37f8ca86e7600238d96d3a0216801b5db8db2b800474972d2800000000505b30000020d03250a67c000002b60000030d41369f570000001880071798e003008d51a6d80c875e000bc896c8b0008a000000000000007d1a1e0004938377800000000000f48000007fb84518d2bc5e00394e1c2ac000cc7b000000072a8a0911181804060003020000030000000001000004010901
def g223D9 (j : Nat) : Nat := 0x1a4834692a588858338a44588620d60344a26218724d0e855328c04800d0e850aa4508c04b10d50b89544320d5515220c63684cb89528320da154ca8831cd9139462e24490ca3519132658870c930da14a4b88a14328218da142a91400ca392c4da240691a508330e481c6a3689290022c334e4b108ca24a6518b34334e4b1a8232892994b0cd3483844a82451aaa470a20650cd46374387f8f19bf34863cba15c2764747e0db16822830036000ff597fd63ff50ffd52ff4cbfe60ff583fe50ff543fe40ff503fe30ff4c3fe20ff483fe10ff443fc10
def g223H9 (j : Nat) : Nat := 0x90ce300251412d5ee363fee5000eba13899ea4b9e4364362eef61447061b849136b2200052f421a00b5e9ec718c9143926602660681eb6ee83e31e2b6cfede2c9d46d65000000813ccae1111dc57000650f33000000e23007c17567656e90a0190f1b9d6a000d6c000e1c0d7ae90dc86dee6000204610bdb11663df5bf5595294f000e0e26974373741946b03228930bf407daab1605e5dc4c871442000000b284d053a4d4d4a20395c000354fd23bb0001b51e2b61000f12000cee000000c092cbe2a00000054e00082d23bd6f0c4f536be2cc0dd6b6d2e00000055922cdea000d58551d5f745ba833eb1f03c860d1a015929520602163808b47c0a73452794d2e7b24944535c0d35a3f14480edf681c1c000c1400000402000010062406080805220102050210170b05040004041e003b041503050d
def g223D10 (j : Nat) : Nat := 0x8a90449443ff
def g223H10 (j : Nat) : Nat := 0x6952c00003890038c003c1fb9471a18a0016380b64bb40000083baf0f20148e4400716cde9a7000000000000016c11800c430483800002e70000000265000005aa6208000310e009
def g223L : Nat → Packing
  | 6 => (23,4,5,0,0,9,0,g223D6)
  | 7 => (62,3,5,0,0,11,0,g223D7)
  | 8 => (114,2,5,0,0,13,0,g223D8)
  | 9 => (18,1,5,0,0,11,0,g223D9)
  | 10 => (1,0,5,0,0,0,0,g223D10)
  | _ => emptyPacking
def g223I : Nat → Nat → Option (Nat × Nat)
  | 7 => lookupWord 7 37 6 10 5 1 g223H7
  | 8 => lookupWord 23 149 8 11 6 1 g223H8
  | 9 => lookupWord 39 181 8 12 7 1 g223H9
  | 10 => lookupWord 8 53 6 10 5 1 g223H10
  | _ => fun _ => none
def g223 : Forest := ⟨223,10,fun i => g223Y[i]?.getD (0,0),g223C,g223A,g223L,g223I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g223P6_0 : block g223 6 0 6=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g223P6_6 : block g223 6 6 17=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g223B6 : block g223 6 0 23=true := (@block_merge g223 6 0 6 17 g223P6_0 g223P6_6)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g223P7_0 : block g223 7 0 2=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g223P7_2 : block g223 7 2 12=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g223P7_14 : block g223 7 14 48=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g223B7 : block g223 7 0 62=true := (@block_merge g223 7 0 2 60 g223P7_0 (@block_merge g223 7 2 12 48 g223P7_2 g223P7_14))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g223P8_0 : block g223 8 0 10=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g223P8_10 : block g223 8 10 48=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g223P8_58 : block g223 8 58 17=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g223P8_75 : block g223 8 75 39=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g223B8 : block g223 8 0 114=true := (@block_merge g223 8 0 58 56 (@block_merge g223 8 0 10 48 g223P8_0 g223P8_10) (@block_merge g223 8 58 17 39 g223P8_58 g223P8_75))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g223P9_0 : block g223 9 0 18=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g223B9 : block g223 9 0 18=true := g223P9_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g223P10_0 : block g223 10 0 1=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g223B10 : block g223 10 0 1=true := g223P10_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g223T : checkedTables g223 10 := by
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
  · exact g223B10
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g223G : graphValid g223 (boundsBefore K127) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low223 : Lower true (varsX 223) (graphGoal 223) 11 := lower_forest (g:=g223) (i:=0) (hints:=1124139009) (before_sound K127 V127) g223G g223T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K223 := extendKnown K127 11 [(223,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V223 : Known true K223 := extend_ok (m:=223) V127 low223 (by decide +kernel)
def g239Y : Array (Bits × Bits) := #[(0xf000000ff00ffff0c01810f3cf23c21e10f3cf,0xa212121212121210c01810a08a22821410a08a),(0x300000000ff00ff30460633d334ccc66633d33,0x14a4a4a4a4a4a4a30460621921484c42621921),(0xc00000000ffff00c098183ce3c8f307983ce3c,0x494949494949494c0981814614853029814614),(0xffffff00000000e01fc0fc0f03f81fc0fc0,0x1818181818181800e01480f40002901480f40),(0x0,0x0),(0xff00000000ff001fff000ffc001fff000,0xe7e7e7e7e7e7e7ff000b7f000ffc000b7f000),(0xffff0000000000ffffe000000fffffe000000,0x7070707070707aa154000000ffd6fe000000),(0xff000000000000fffffffffff000000000000,0xf8f8f8f8f8f8f855eabffffff000000000000),(0x0,0x0)]
def g239C : List ColumnInfo := [(1,2,232,4,5),(32,0,207,0,8),(0,128,47,64,8),(192,0,47,0,7),(40,0,199,0,6),(2,0,237,0,7),(4,0,235,0,7),(0,32,199,8,7),(3,4,232,0,4),(8,32,199,0,6),(64,0,47,0,7),(0,2,232,5,6),(2,4,232,1,5),(6,0,233,0,5)]
def g239A : List (List Nat) := [[],[33]]
def g239D6 (j : Nat) : Nat := 0x309bd8790e10dae43dc910
def g239D7 (j : Nat) : Nat := 0x250470421e50a6942cc40b3cb1004cd521303c03df21a437f5ce10f7c87087be43442deb84877bdc910
def g239H7 (j : Nat) : Nat := 0x1901c
def g239D8 (j : Nat) : Nat := 0x1e64899802ac969272880cc2aca332690106320b3480839c93944c062ca52093944c062ca54f44b5450cd2805469c401b8b33d90c4800ff4c7fd21ff8c3fd30ff843fd10ef90fbd40
def g239H8 (j : Nat) : Nat := 0xc1846c024800000294000000cc0000029002680000000000
def g239D9 (j : Nat) : Nat := 0x47428ca3ff
def g239H9 (j : Nat) : Nat := 0x7200005b801d95000000678000007829000b00000000000050cab1800022
def g239L : Nat → Packing
  | 6 => (2,3,4,0,0,3,0,g239D6)
  | 7 => (6,2,4,0,0,7,0,g239D7)
  | 8 => (8,1,4,0,0,9,0,g239D8)
  | 9 => (1,0,4,0,0,0,0,g239D9)
  | _ => emptyPacking
def g239I : Nat → Nat → Option (Nat × Nat)
  | 7 => lookupWord 1 5 0 6 1 1 g239H7
  | 8 => lookupWord 2 23 5 8 3 1 g239H8
  | 9 => lookupWord 3 31 5 8 3 1 g239H9
  | _ => fun _ => none
def g239 : Forest := ⟨239,9,fun i => g239Y[i]?.getD (0,0),g239C,g239A,g239L,g239I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g239P6_0 : block g239 6 0 2=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g239B6 : block g239 6 0 2=true := g239P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g239P7_0 : block g239 7 0 2=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g239P7_2 : block g239 7 2 4=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g239B7 : block g239 7 0 6=true := (@block_merge g239 7 0 2 4 g239P7_0 g239P7_2)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g239P8_0 : block g239 8 0 2=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g239P8_2 : block g239 8 2 6=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g239B8 : block g239 8 0 8=true := (@block_merge g239 8 0 2 6 g239P8_0 g239P8_2)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g239P9_0 : block g239 9 0 1=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g239B9 : block g239 9 0 1=true := g239P9_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g239T : checkedTables g239 9 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g239 0 0 0 = true)
  · exact (rfl : block g239 1 0 0 = true)
  · exact (rfl : block g239 2 0 0 = true)
  · exact (rfl : block g239 3 0 0 = true)
  · exact (rfl : block g239 4 0 0 = true)
  · exact (rfl : block g239 5 0 0 = true)
  · exact g239B6
  · exact g239B7
  · exact g239B8
  · exact g239B9
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g239G : graphValid g239 (boundsBefore K223) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low239 : Lower true (varsX 239) (graphGoal 239) 10 := lower_forest (g:=g239) (i:=0) (hints:=1664090113) (before_sound K223 V223) g239G g239T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K239 := extendKnown K223 10 [(239,[]),(247,[118,67,16])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V239 : Known true K239 := extend_ok (m:=239) V223 low239 (by decide +kernel)
def g251Y : Array (Bits × Bits) := #[(0xcf80000000001fff990622619f62e42661339f,0x45264c993264c993190622418a62a42461228a),(0x79800000000fe03fe0584c721384c7c6863cf3,0x28d8b162c58b162c60584c32118442c2861851),(0x0,0x0),(0x8e0001fc07f01fc000600f9c1c0738f907cf1c,0x8a112244891224488060091c14001091048d14),(0xf000fe03f80fe0000180701fe0f83f01f80fe0,0xd003060c183060c18180000940503d015007a0),(0x3fff000007e007fe000ffc001fff000,0x6cd9b366cd9b367e0076e000afc000ab7000),(0x7f01fc000000007fff800000fffffe000000,0xe1c3870e1c3875595000000ffef6e000000),(0x7ffe00000000007fffffffff000000000000,0x70e1c3870e1c382a6afff6bf000000000000),(0x0,0x0)]
def g251C : List ColumnInfo := [(32,0,219,0,8),(1,0,250,0,8),(3,0,248,0,7),(8,1,240,2,5),(16,2,232,1,5),(8,64,51,128,5),(64,0,187,0,8),(16,128,43,64,5),(128,0,123,0,8),(8,0,243,0,7),(48,0,203,0,5),(16,0,235,0,7),(41,0,210,0,4),(11,0,240,0,4),(160,0,91,0,5),(19,0,232,0,4),(65,0,186,0,5),(0,1,240,10,6),(2,1,240,8,5),(192,0,59,0,7),(104,0,147,0,4),(200,0,51,0,4),(208,0,43,0,4),(129,0,122,0,5),(34,0,217,0,5)]
def g251A : List (List Nat) := [[],[16,67,118],[96,113],[112,97,67]]
def g251D5 (j : Nat) : Nat := 0x318e98e1c844c832
def g251D6 (j : Nat) : Nat := 0x380101c008060b00560040b0020000016004c008000000000005801f3ede7e1dbccc6b7b1998a84756f69635d4e3f39332d27211b150f008dfca30f31e415b791603744ca37d303a2e09966ddd3815c132cda3a702b82655cd94e1d320cb39f29c3a6419673653874c832ce7c3f0899065d8f97e11320cbb1f0fc22641946fe5183dd520ae7cbb08990659cf87611320caf1d304226419763e1c844c8328dfca30ea1e415ce985d1320cbb1f08ba26419567e4d7590d408dfca305bb2614f79654f714c2aef2ab16e29856de5132dc5308dfca30ea1c6559d93dd24348331f0fc226419663e1c844c832
def g251H6 (j : Nat) : Nat := 0x40
def g251D7 (j : Nat) : Nat := (if j<1 then 0xb08000041022c100241000b0980120058416261083028268041a2420a4b0800c8b08022c20000002840c30ca20a8810307041c105822c2c105801110400000000000601080a00b082010004401110420100010490800104001043010c2b030c000040000000000400000103040080708042060708189c10a24103043c0c20f0308001a1982600598101812c2020810668820e0810e4b820e08100001820400005241000400d0008007040c1000002812b0c080070400006007050403162d802608b081fa0179b8013880f8490c4b0a89100000e807e605e00403e2e127876f8de5b736b6d0d85af3576a8d35a133b668cb591317620c157d2f75d8b856f2db5b0b255f2b7560aa551297520a254127f4f89e53b2734e09b53125f4a89352323f4708c51722b4408750b213418814fb1f33d87a4f31e33c0774eb1d33a0724e11bf3706b4d319f328634c317b2e05b4b515f2b0544a71432804e495123228434851031f83e4790eb1c83846b0d3198314610bf1782d4550a71402744d0971001d4350430600b415027000ddd7350f20fb96450120dbe435c242bed829cd42bf9809cd42bfb805c5429fd83dc1429ff845ce32dbc845ce329fd8750e32dbd7450e32ded7350a32df5435c632dbd82dd132dbf80dd132dbd80dd132dbf845d132bbe871d132dfb7354120faf7490932bfb8454120dbf7450932faf7450932dbf74dc132dbc74dc1329fd84dc132bbf845c132dbf745c132dbc745c132bf7815c132bbf844c920b7d85cc920fcf844c832b7f8558920fcd844c832dbf7490d20aff8654d209fd82dd160bbf844c9609fd83dd1509fd82dd1509fd84dcd509ff845cd209fd82dcd50bbf844c950def724c950dbf74591209fd83dd5409ff835d5409fd83dd120dbd64dcd40bbd8690d40dbf7590d40dbd7590d409ff835d520bbd8290d40b7d85cc940bbf844c940f9e434c940fad424c9409fd8750b30ded7250b309ff845d520f9c844cb30ddd744cb30fcd424cb309fd84dd9309fd82dd9309fd84dd5309ff845d5309fd83dd5209fd82dd1309ff845d920dbd7459130bdf8359130dbf7455130bbf844c930f9f844c930f9c844c930ddf744c930fcd624c930fcd424c930df564dc530df554dc530df553dc530df543dc530df562dc530df542dc530df532dc530bfb8458130bfb8454130f795354130bfb8550130fb96450130df9744c3209ff845cf20dbf845cf20df9754c320dbc845cf209fd8798f209fd8790f20ddd7390f209fd8750f20fba4350120f9f844cb3097f855db20beb824c32097f855d9209f7815d1309f7815d530bad8290e42d9f7390d409ef825d54097d85dd9409bd84dcd509bf845cd209f7815cd20dcd744c832f8c844c832f8f844c832dcf874c832f8e43909329be871d1329fb805c6429bf845cf209cf874c832 else 0x10e89080490)
def g251H7 (j : Nat) : Nat := 0x1c348c00000140c0000001f26ec8800001a4f85000b100020cf15001e5c0040ce0e00280b0bc3400387000001e0800396000e1809789000e0000000728000002050000000078462000030030c0000
def g251D8 (j : Nat) : Nat := (if j<1 then 0x982c2822c7101828714261411648f0044589443080a003e6062e141244060e1448b0410083286050e0e14116380121e10282cc700161026704600401c222cc6101c30506807c20504a0e20286192d0038444a101c30500451212038c162422018507122c2cb0880193a334997890611c7c2042c1a982387101432018282022204b4003466932f1612078b06a610a1c2e8cd2e484c4450612c28b120d4c21810fc00c8c11860044444a11998b064410acf40b4c0c8821c3cb400c8821831501081280e3940a2c4c2823080e1828c1626141246800825161183880c0028985048669828906086141c005082418e203000a1c48b04100832c38b924410a303c2050598c0038b07088b31d98c16982c2050486621300160e102224880e1828b190a09030583840888c1c4060a804840404194203860a2c8a2424080e1829184324c1243880a1800c07088c9825880e524c008887101c30518101110248d16888c0128470e202860888657242202e360070814120620120c10a2f407cc17004078b095cf46697271611c684d1982cbc00c4e12b407cc17009082c1e2c25f3084b466c00e5c126ecd73db86db92d85699b42d972c5960aaf0d6feb2d56daa5d46e9e54c9a5751de8ab425a054f4e75537a9ac4cbe6372dd9534a124c5232908479e3991a38b644f220b0ea867c20e0990077ef3e49ec4f1676539f9c9ce106ecb689abad2d67b32c5902c3c5f82ee5704b525912b59514a4c50e275d34096948b236115e85c4161ff0f987a33b61cf0e0a6d53481980c445f22dd95a0a7e50f26c12688aa4171f38e6c6ba3181628a384922120f1073832016708d83901300450007fd43483ff21a41ff54d20ffca6907fd63483ff39a85ff5cd42ffcc6907fd7150bfeaa241ff59120ffa87907fd438cbff21e41ff98f20ffac9907fd32483feb1241ffdd132ffa64987fd424c3ff99241ff5d132ffac4987fd434c3fea9a61ff50932ffaa8987ff704cbfeb2261ff5c132ffa85987fd52483feaa661ff4c940ffe64a07fd42583fe992c1ff4c950ffe64a87fe43543fea1aa1ff50950bfae7215ff73542ffba2a17fdd940bfaeca05ff75502febaa81ef59140bfee6a07be43502ffb9281ef50940bfee4b05ff74582febb6617f5d730bfae9985fd700cafeb96617f5d032fba65985ff764c2ffbaa617f5d530bfee8985fd744c2ffb8265fb50932fdc84997bc744caffb92617f5d132f7ee8997df324c2ffba265f74c930feee2985fd708cbfcb0261fe54130ff280985fd76c82febae417f5d320bfae3195fd73c83fca8241fb50a32bfae7197f930c82ffbb2417f5d920bfeea905fd75482ffba2417f5d120bfae9195ff7050affb9a417f5cd20bfee2a15ff7350afeb84857f5c642f7c87215ff72543fca0241f34c832b7ee8995f5718cbe7994657ddc530 else 0x111904318445a08229118a03058230c222d3411488c510444d2460b4228c1410c222d441146c93011121186202304422300288228a122e0892050917085922d011822875046088383c900a208c30589230450e994118228916803403c4c2220458e3e10106226182c49182320182831e1c426840418e3d042230455015342230464030589107a0840488a841841c700502e10122420183c1a222847182c4c11028607044282c30541046180208310626570418a44bc80cba00f2018a403200a260831c80b0c160831880b0c150118239121043200e0861c4060aac202800419400890130a9c11e9e8402c8098d0a092cc642501c5661a007160e1028244a662e00585046662d30580241918504a18cf32b92a07008504a101c30522ac6098504a192402b85046182c1e681081412060556001c282397062c8c2a7047a6805971322102824960e26141163160)
def g251H8 (j : Nat) : Nat := 0x29112f2000b0da8134f723b72c08c80000000006f14001dc600070b28260000f30002b86000ad380023bc000f310001479a10703800389332c0001038000000a2a8000849243f4a80000ae00089180028e1e538368001c9760ca10000000000000005080011692d8aba309b46ec798003011279c33800303de030000000000000a0d60ac9c2adf072c6cc00162f02e13bd6dca74c128000c5dffcbf0a2be4e40d10004846688000697d58400043e0003f7089e07c06bc019c9c000a3ba0e0000631e2dd91c7b0000c38a0640011a4a1a44f1475d65bdf49f70c12ea31b2061edfce7e988b988edaf09352fb8001e6b0007874ccb617e0fc0178d000000060fc416000431917babe0000d0272aec5a7ac182ac00016f20002fee4bf9e20d7bcc204ec7550173ee652000b2e8000c2aac459f1b89482000000003400162801c90dcc5a0009bdb83c447f66329000332a0000000000ddc866bda1f2d4120000006943c5404a111000206a00051e8001c900001b880030b54169618001c25ebe5327987cb3646b206b1a3df473919e908401e45410a1518a2a1c0f28ec00dee6c414bac5f88e69b3c6828620000000000104c9599260000000a5600000024020000005050bbf48f58a820040a000000a0e0800806020f0240a1f048201a0d0102c0e000701402050080c02000881024000f0000e030683c0200010002806008080604
def g251D9 (j : Nat) : Nat := 0xba261400c98a12732d426898032284a202a261602c326284bcc0a2680b262849a079858040cb26284b5cb2601c309304940b2600d3182049ccc2c9a260c0081289a079838022c12733c9a268032c204a2e81668090812330112e898c08904aafa7c8d1f86c1744e0f62e87810800ff90bfd42ff8cbfd32ff0cbfd60ff543fd40ffcc3fd30ffc83fd20
def g251H9 (j : Nat) : Nat := 0x4442496e564039c2000096a4b7a9aeca4db3000508bb18da1e1d0002c160650f91012ca7430016d03909926f00019400018dda368000064e1352f4464000cd01237ef8450a6c21fa0d800000000028767b4c4d2d30001c0c8d63220c82cc6000884b5436bdf54433c025c8ee3cde727a3a36825d160003bd74e701c709ba6c00000070bcbc63d6886779dc95e39c2ef33f019bd53139048000794000003d5cc0002a98bc86af4df000536000121bb248d7c96d10e50c00019570cda1dc5a640b864192488cda83d000050b8838000c30489295c000e656ab5b6dc2170f497f0114ac4f120a5cb264e81bb98a8d37f1a38b545ba9a0a00078cc00046690d6f7c001a119f2f0044c353c8b170f942c248b0fe001d99cb3620cf3f8d5756228d6b724405ac2bc291cab5e1927d06487aa68815e7764b80a648171c95cb817000600c0003ae21a34ce48106e218f6ec00094ec1ae08157d70b32de23000120260a8050000000922ab89c8460d40821500006c9c78f10c001c2a02c1cb4001d70f65b36af48a700207030a0815410f140a01040100141b06001f531d060c340309440004e00a5f00042e00040f10001e013e0b2a0a0430000010
def g251D10 (j : Nat) : Nat := 0x4d06008237f
def g251H10 (j : Nat) : Nat := 0x54883281b134133d2f61d25f2d045bc55b400000369e3914020180016400b44000000a00122001c800000002540000084d84000000000065970d900000000101470c00cd0420c0
def g251L : Nat → Packing
  | 5 => (1,5,5,0,0,0,0,g251D5)
  | 6 => (28,4,5,0,0,8,0,g251D6)
  | 7 => (126,3,5,0,0,11,0,g251D7)
  | 8 => (115,2,5,0,0,13,0,g251D8)
  | 9 => (12,1,5,0,0,10,0,g251D9)
  | 10 => (1,0,5,0,0,0,0,g251D10)
  | _ => emptyPacking
def g251I : Nat → Nat → Option (Nat × Nat)
  | 6 => lookupWord 1 2 0 7 1 2 g251H6
  | 7 => lookupWord 7 53 6 11 5 2 g251H7
  | 8 => lookupWord 51 281 9 13 7 2 g251H8
  | 9 => lookupWord 51 239 8 13 7 2 g251H9
  | 10 => lookupWord 8 53 6 10 4 2 g251H10
  | _ => fun _ => none
def g251 : Forest := ⟨251,10,fun i => g251Y[i]?.getD (0,0),g251C,g251A,g251L,g251I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P5_0 : block g251 5 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g251B5 : block g251 5 0 1=true := g251P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P6_0 : block g251 6 0 2=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P6_2 : block g251 6 2 26=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g251B6 : block g251 6 0 28=true := (@block_merge g251 6 0 2 26 g251P6_0 g251P6_2)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P7_0 : block g251 7 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P7_1 : block g251 7 1 20=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P7_21 : block g251 7 21 48=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P7_69 : block g251 7 69 48=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P7_117 : block g251 7 117 9=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g251B7 : block g251 7 0 126=true := (@block_merge g251 7 0 21 105 (@block_merge g251 7 0 1 20 g251P7_0 g251P7_1) (@block_merge g251 7 21 48 57 g251P7_21 (@block_merge g251 7 69 48 9 g251P7_69 g251P7_117)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P8_0 : block g251 8 0 5=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P8_5 : block g251 8 5 48=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P8_53 : block g251 8 53 19=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P8_72 : block g251 8 72 43=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g251B8 : block g251 8 0 115=true := (@block_merge g251 8 0 53 62 (@block_merge g251 8 0 5 48 g251P8_0 g251P8_5) (@block_merge g251 8 53 19 43 g251P8_53 g251P8_72))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P9_0 : block g251 9 0 12=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g251B9 : block g251 9 0 12=true := g251P9_0
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
  · exact g251B5
  · exact g251B6
  · exact g251B7
  · exact g251B8
  · exact g251B9
  · exact g251B10
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251G : graphValid g251 (boundsBefore K239) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low251 : Lower true (varsX 251) (graphGoal 251) 11 := lower_forest (g:=g251) (i:=0) (hints:=1127284737) (before_sound K239 V239) g251G g251T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K251 := extendKnown K239 11 [(251,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V251 : Known true K251 := extend_ok (m:=251) V239 low251 (by decide +kernel)
def g253Y : Array (Bits × Bits) := #[(0xf0000000000ffff3106226067cc59326184fff,0xa4a4a4a4a4a4a4a31062240628c5122418494a),(0x0,0x0),(0x3000000000000ffc2584c7984f09e3c7618e73,0x1b5b5b5b5b5b5b5c2584c3984708e1c3618631),(0xc0000ff00ffff0000600f9e0700e7cf981f39c,0x4212121212121210060091e050004891812294),(0xff00ff0000000380701ff83f07f01fe03e0,0x707070707070703800015502a07f01d403e0),(0xffff0000fc007fe0003ff8001fffc00,0xd8d8d8d8d8d8d8fc0076e00015f80002adc00),(0xff00ff00000000ffff8000003fffffe000000,0x1e1e1e1e1e1e1eab950000003ffb76e000000),(0xffff0000000000ffffffffffc000000000000,0xe0e0e0e0e0e0e0546affeaafc000000000000),(0x0,0x0)]
def g253C : List ColumnInfo := [(4,0,249,0,8),(0,4,248,1,8),(8,0,245,0,6),(64,0,189,0,7),(176,0,77,0,4),(16,0,237,0,7),(1,4,248,0,7),(0,16,77,160,6),(32,16,77,128,5),(16,128,45,64,5),(32,0,221,0,7),(128,0,125,0,7),(1,0,248,0,7),(48,0,205,0,5),(208,0,45,0,4),(64,128,45,16,5)]
def g253A : List (List Nat) := [[],[116,101]]
def g253D7 (j : Nat) : Nat := 0xc410151020000c2080031c02c700b1c02f1cb05aa909e36484805ff72552febac85ef59242bfeeaa15fd7550bdeaa2857f5d632bfeea994ff7654e7ebb4656fdd132
def g253D8 (j : Nat) : Nat := 0xdbd1510d5664605a16e38acc8c095a1c2194f68c0a4b4453d991812b48eaa122cc8c0b4ac65129168c0a58d28396cc8c0a58d4941cb68c0ac1d4230e5541c07000ff553fd63ff54ffd43ff90bfd42ff8cbfd32
def g253H8 (j : Nat) : Nat := 0x74c95cc84e1800028800755d4677c00244e018820
def g253D9 (j : Nat) : Nat := 0x1674ad82047f
def g253H9 (j : Nat) : Nat := 0x1ba0864348f5000000b934002d0012dcbae7a16c0e0
def g253L : Nat → Packing
  | 7 => (11,2,4,0,0,7,0,g253D7)
  | 8 => (8,1,4,0,0,9,0,g253D8)
  | 9 => (1,0,4,0,0,0,0,g253D9)
  | _ => emptyPacking
def g253I : Nat → Nat → Option (Nat × Nat)
  | 8 => lookupWord 4 17 5 9 4 1 g253H8
  | 9 => lookupWord 4 19 5 8 3 1 g253H9
  | _ => fun _ => none
def g253 : Forest := ⟨253,9,fun i => g253Y[i]?.getD (0,0),g253C,g253A,g253L,g253I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g253P7_0 : block g253 7 0 3=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g253P7_3 : block g253 7 3 8=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g253B7 : block g253 7 0 11=true := (@block_merge g253 7 0 3 8 g253P7_0 g253P7_3)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g253P8_0 : block g253 8 0 8=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g253B8 : block g253 8 0 8=true := g253P8_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g253P9_0 : block g253 9 0 1=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g253B9 : block g253 9 0 1=true := g253P9_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g253T : checkedTables g253 9 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g253 0 0 0 = true)
  · exact (rfl : block g253 1 0 0 = true)
  · exact (rfl : block g253 2 0 0 = true)
  · exact (rfl : block g253 3 0 0 = true)
  · exact (rfl : block g253 4 0 0 = true)
  · exact (rfl : block g253 5 0 0 = true)
  · exact (rfl : block g253 6 0 0 = true)
  · exact g253B7
  · exact g253B8
  · exact g253B9
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g253G : graphValid g253 (boundsBefore K251) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low253 : Lower true (varsX 253) (graphGoal 253) 10 := lower_forest (g:=g253) (i:=0) (hints:=1127546882) (before_sound K251 V251) g253G g253T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K253 := extendKnown K251 10 [(253,[]),(254,[118,67,16])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V253 : Known true K253 := extend_ok (m:=253) V251 low253 (by decide +kernel)
def g255Y : Array (Bits × Bits) := #[(0xc3100c20878061e78c23c8e043c1810f4dc3cf,0x83100c20850060450c2288a04281810a09408a),(0xcc02304319908699904cc1398cc20633b27d33,0xc023043109084909048401188420621202921),(0x3024c08c1e63071e608f31c60f2c183cc38e3c,0x7024c08c0a63030a60853146052c1814c28614),(0x7000fe07c07e000f03e07f0301fc0fc0fc0,0x4007000a407c07a00000240520301480f40f40),(0x3800f0007ff8007f003ff8003fe000fff000,0xc0380000004a50004a003fe800394000dfd000),(0x3fc000ffff8000007fffc000003fffff000000,0x3fc000f5bf80000035ffc0000006ab7f000000),(0x3fffff00000000007fffffffffc00000000000,0xaab8aa00000000007fffdbfadfc00000000000),(0x3fffffffffffffff8000000000000000000000,0x154755ffffb5afff8000000000000000000000),(0x0,0x0)]
def g255C : List ColumnInfo := [(4,0,251,0,11),(3,0,248,0,7),(3,4,248,0,7),(32,0,223,0,11),(2,16,77,160,6),(17,2,232,4,5),(1,8,150,96,6),(0,4,248,3,9),(16,0,239,0,10),(8,0,247,0,10),(2,0,253,0,10),(1,0,254,0,10),(64,0,191,0,11),(128,0,127,0,11),(32,16,77,130,6),(24,32,199,0,6),(0,1,240,14,7),(16,2,232,5,6),(8,1,240,6,6),(7,0,248,0,7),(56,0,199,0,6),(34,16,77,128,5),(0,8,150,97,7),(9,0,246,0,7),(18,0,237,0,7),(2,1,240,12,6),(33,0,222,0,7),(11,4,240,0,4)]
def g255A : List (List Nat) := [[],[16,67,118]]
def g255D7 (j : Nat) : Nat := 0x2809f1e0580fc036790a950d3150110
def g255D8 (j : Nat) : Nat := 0x18ed2101409e3f060b97aa1c0b4ea2042780f8060300409e380f806c37e783c00edbe9543e0910ce7261434c540adbe9543e09109fc2a53150110fe450d3150110
def g255H8 (j : Nat) : Nat := 0x700
def g255D9 (j : Nat) : Nat := 0x8c534ea70018132c801ede381048bca69e0246bb6b7b2b3828012ab243aac58ded0414e3ab491bb437b0338c0f21081f80005aa72ce63edeca9e004cb1023b2a627803b2fb41082909eccbede3041f82a4132c2e23b78da89ed0dec0c0f03c816e000aacb33b7b38c22a782a85b2c9ed0dec0ce303a9c8e0820700cbaa381b80a7b01123b78f2ea8aed0dec0ce303e00017a8cb2e5fa85843b32f24717e01949ece3198c0fb7b38013ab24432c58b0a12a80410e0185c10538c4ed0dec0ce30316a8c9e0cb2fb437b0338c0c5f278002ab2c2cdece3e017aac94b1c605b802a27b38f2c868e00a89ec16e3cb212c2f82245aabb38c8ed0dec0ce30316a9e000cacb30045b805c4ed0dec0c0f03a80700cacb1633b5b7b1b3818055a85039acb140ed3edcdecccc1a9a8e0cacb361c1fb3b78da1a72b2c9ed0dec0cc9e00010e3c8ab2c4b8c4641a6a0078080f0eeaedeca8c9e0cb2699a8626aa5d23fa2e21ca0d1f99e01cc9af19998217296514d94013691f1038f40e28d10bf8a609c88306b85003c8250138003eff2aa1a21fb94350110dbfc2b00a1df7e4d8050e7fb23c1a8177f9560d40f9fcaa86a07e7e0d43502f7f22a1a813fd93e05409ff4c262a04ff26131503f3a8698a813fd91e1130bbfcab08985f7e4d844c36ff2ac2261ff39150110defc9b08984ffe45844c27fb29c0a617fb9060530defc2262986f7611314c3fb72098a613ff9460d10dfdc8306884ff661434436fb21c2a8777f9550d10df6a1f04884ff6478050ffe262a022137f9561130
def g255H9 (j : Nat) : Nat := 0xcc000311c489800
def g255D10 (j : Nat) : Nat := 0xdab762c1e5f02008a8b14c6ae49ea700596485dbb319753802149640a0ba4210c1b71c896a8ad84b484058082a31b71cb906850983629db8e44b5456d5b810192fa8b14d98e5c934da80480baa2db31cb925962260be0daa156cc72e49850b5303b36e382a5460952cd0650b6dd9224e0d5aca15b766029224ab20b12d42b6ec90a706396584d5b14e028236e39651109b766390ab4e096517d42b6ec512706396517085b50adbb1449c0531cb376ecc65d568938259214b6d2eab46013b31cb2c896dbb31820e5e568538259a48813dbb31a8022e569c0614dbb2449c1ab590076ecc7a25699646ced4b96706dacac13fe564527e2e95b3b145909f1181cf3144dc6b07c07c003ff60143fff83503ff60d40fff81503ff60540ffd31503ff61130ffd814c3ff50530ffd43443dfe1543bff8050effe0d40fbd43502ffe0540bff844c2ff61130bff814c3f74c530bfd83443fe50110b7f8550efbe0910
def g255H10 (j : Nat) : Nat := 0x670c10000000000078a000000000000000000000000a0000000032547c0000061e8788b719000000cc38b38e5800009319423000000422203efa8d0018800000082fe38000000000018a000000001d0d0160800000000001055ad80000115f6480068a01bcd00060666e44000f1356400000001842c3d1d00004180022c0830e00180
def g255D11 (j : Nat) : Nat := 0x52db2320982aac9b2aa60b6320b217b6aa20b2324b253b6c8e8a4180a2cab47e4200ffa87ff503fe987fd10
def g255H11 (j : Nat) : Nat := 0x64a3d4e0018432b760001242ee2002a900187044487330600355734000000000800a9b1000000b4c00652c3715a3000c112416600eb45f24010000a
def g255D12 (j : Nat) : Nat := 0x1ac1a12052c8ff
def g255H12 (j : Nat) : Nat := 0x1500980530003c80618800000
def g255L : Nat → Packing
  | 7 => (1,5,5,0,0,0,0,g255D7)
  | 8 => (5,4,5,0,0,8,0,g255D8)
  | 9 => (34,3,5,0,0,12,0,g255D9)
  | 10 => (23,2,5,0,0,11,0,g255D10)
  | 11 => (4,1,5,0,0,8,0,g255D11)
  | 12 => (1,0,5,0,0,0,0,g255D12)
  | _ => emptyPacking
def g255I : Nat → Nat → Option (Nat × Nat)
  | 8 => lookupWord 1 2 0 6 1 1 g255H8
  | 9 => lookupWord 2 7 3 8 3 1 g255H9
  | 10 => lookupWord 11 89 7 11 6 1 g255H10
  | 11 => lookupWord 8 43 6 10 5 1 g255H11
  | 12 => lookupWord 2 13 4 7 2 1 g255H12
  | _ => fun _ => none
def g255 : Forest := ⟨255,12,fun i => g255Y[i]?.getD (0,0),g255C,g255A,g255L,g255I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P7_0 : block g255 7 0 1=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g255B7 : block g255 7 0 1=true := g255P7_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P8_0 : block g255 8 0 4=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P8_4 : block g255 8 4 1=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g255B8 : block g255 8 0 5=true := (@block_merge g255 8 0 4 1 g255P8_0 g255P8_4)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P9_0 : block g255 9 0 1=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P9_1 : block g255 9 1 32=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P9_33 : block g255 9 33 1=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g255B9 : block g255 9 0 34=true := (@block_merge g255 9 0 1 33 g255P9_0 (@block_merge g255 9 1 32 1 g255P9_1 g255P9_33))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P10_0 : block g255 10 0 2=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P10_2 : block g255 10 2 11=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P10_13 : block g255 10 13 10=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g255B10 : block g255 10 0 23=true := (@block_merge g255 10 0 2 21 g255P10_0 (@block_merge g255 10 2 11 10 g255P10_2 g255P10_13))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P11_0 : block g255 11 0 4=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g255B11 : block g255 11 0 4=true := g255P11_0
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
theorem g255G : graphValid g255 (boundsBefore K253) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255R : Impossible true graph 12 eightInputs.toFinset := by
  rw [show graph = targetOf g255 by decide +kernel]
  exact root_index (g:=g255) (top:=12) (i:=0) (before_sound K253 V253) g255G g255T (by decide) (by decide +kernel)
def mo255Y : Array (Bits × Bits) := #[(0x6043d370f3c0000000000000000ffe003fffff,0x604282502288510a2144288510a2144288510a),(0x818cec9f4cc00000000000007ff001ffc007ff,0x8188480a485282504a0941282504a094128250),(0x60f30e38f00000000000000000001fffff800,0x60530a185252ca594b29652ca594b29652ca5),(0x7f03f03f0000000ffe003ff800ffe00000000,0x5203d03d00608c1182304608c1182304608c1),(0xf8003ffc000007ff001ffc007ff00000000000,0x500037f40000380700e01c0380700e01c03807),(0xffffc00000000000001fffff80000000000000,0xaadfc0000039c738e71ce39c738e71ce39c738),(0x3ff800ffe0000000000000000000,0x1f03e07c0f81f03e07c0f81f03e),(0x3fffff0000000000000000000000,0x3e07c0f81f03e07c0f81f03e07c0),(0x0,0x0)]
def mo255C : List ColumnInfo := [(7,0,248,0,7),(8,1,240,6,6),(8,0,247,0,10),(2,4,248,1,8),(32,0,223,0,11),(64,0,191,0,11),(128,0,127,0,11),(4,0,251,0,11),(0,1,240,14,7),(2,16,77,160,6),(10,4,240,1,5),(162,16,77,0,4),(1,8,150,96,6),(3,4,248,0,7),(1,0,254,0,10),(10,1,240,4,5),(34,0,221,0,7),(16,160,7,72,6),(130,0,125,0,7),(65,0,190,0,7),(8,32,199,16,7),(8,64,55,128,8),(24,32,199,0,6),(136,64,55,0,7),(0,96,7,152,7),(16,128,47,64,8),(14,1,240,0,4),(0,160,7,88,7),(16,0,239,0,10),(23,0,232,0,4),(97,8,150,0,4),(2,0,253,0,10),(56,128,7,64,5),(80,128,47,0,7),(16,2,232,5,6),(129,0,126,0,7),(40,0,215,0,8),(12,0,243,0,7),(33,0,222,0,7),(104,0,151,0,7),(18,0,237,0,7),(18,128,45,64,5),(9,64,54,128,5),(8,96,7,144,6),(9,0,246,0,7),(192,0,63,0,9),(24,96,7,128,5),(66,0,189,0,7),(12,1,240,2,5),(176,0,79,0,7),(48,0,207,0,8),(56,64,7,128,5),(8,160,7,80,6),(36,0,219,0,8),(67,4,184,0,4),(129,4,120,2,5),(65,4,184,2,5),(20,0,235,0,7),(6,1,240,8,5),(33,4,216,2,5),(128,96,7,24,6),(45,0,210,0,4),(73,0,182,0,5),(12,64,51,128,5),(5,2,232,16,5),(21,2,232,0,4),(20,128,43,64,5),(132,0,123,0,8),(11,4,240,0,4),(68,0,187,0,8),(130,4,120,1,5),(34,4,216,1,5),(18,4,232,1,5)]
def mo255A : List (List Nat) := [[],[16,67,118]]
def mo255D6 (j : Nat) : Nat := 0xc307c36c6436454a62a022183e1b5321b22a53150110
def mo255D7 (j : Nat) : Nat := 0x3f0df85fc21000007d821a0028000a624a321a01e9d080029f8718936889150110a7e1c524da2245404431f46d9b32a53150110c7d1b56cca94c5404431f86d9b22a53150110c7e1b56c8a94c540443fc0315432093150110a3e0c86c8a94c5404421f872ca92093150110
def mo255H7 (j : Nat) : Nat := 0x540000c005c0000000
def mo255D8 (j : Nat) : Nat := 0x3c006002e1c4784c0d0be1be17e1103400f608640d0034000e00002c200380078260e1102002de0802444087820090c025000240d0034000c030026000300a00b009408100280250203800b870010fdef63d2f33c6f03baed3aeea3a2e7396e438ae137ede372db366d835ad534ed2342cf336cc32ac931ec6312c3306c02fabd2eeba2e2b72d6b42cab12beae2b2ab2a6a829aa528ea22829f2468a1da6c192571263f0de2d08a1502a003f705b2e690a408853f5b520c9160940c7bb4cc990640a818f76959320c815029f6db106c9102a053edb520d9220540c7bb4cd193098a818f7695a3261315031f6d33444c262a063eda5688984c540fe32caa9a86a0221fca2d54320940443fc4b9a8641280887f895350c8250110dfa2e6d1922a0221bf458da3245404437e8a9b4648a80886fd1b768c9150110dfa36cd1922a02217f86d843485204437e8bb34648a80886fd1b568c9150110ff82a6a1a4290221bf4595a324540443fe0b9a8690a40887f60b550d2148110afe36c49922a02215fc6d49324540442ff0daa8690a40885fe1b650d2148110dfc2ecd1122a0221fd859553485204437f0b2b4448a80885fe1b654d2148110dfc2e6d1122a0221bf858da2245404437f0a9b4448a80885fe1b754d2148110cfe36c54a62a02219fc5d8a94c5404433f8da95298a808867f1652a53150110ff82e6b1a42902219fc58ca94c5404433f8a995298a808867f1432a53150110fdc2cab1a42902219fc2a5734c540443fc8bb28698a80885fe1b758d2148110fbc2eab9a4290221f785d97348520443fa8baa62a8260887f50b550d3148110ff22c8a1a6290221fe4551434c520442ff0dbaca90a40887f61755952148110a7eb6c41922c12817f86d443485204433f05490498a80887f10b550d3150110cfc36454a62a02219f46cca94c5404437d0a1b4448a808867e0936889150110cfc32ad1122a02219f8659a2245404437c8d1a8648a808847f1ba24c9150110df2368d1922a02219f4655a3245404433e8cb34648a80887f81432093150110
def mo255H8 (j : Nat) : Nat := 0x84e12509000b050706c600714000709b
def mo255D9 (j : Nat) : Nat := (if j<4 then (if j<2 then (if j<1 then 0x325c140bfc285825c140ee7615434c540fc7295434c5408ff2a5854c5408ff2a1964c540cfb688984c540cf768c984c540cdf26165545408ff2a196545408ff68c98545408ff68c9858540cef261435c5408ff68c985c540ef35cd43608109df694985c540deb50d9220540afb6a15320910bfc6844348110cfb20d9220540cfb60d9220540afb6a04320910cfb6199220540cfb61d9220540de764d4320540dcf6554320540daf6594320540d6f65d4320540afb6a14320910ff450d3148110ff85d92148110ff85952148110ff85cd2148110ff858d2148110ff854d2148110ff850d2148110ff810d2148110edb5955360810cf764c8320540afb6995360810eb72999760c10cf765d9660c10af76a57660c10e7765d7660c108ff6a48320540af76a57560c10e7765d7560c10cdf6558320540af76a56560c10af769d6560c10eb76596560c10ed76556560c10ed75d56560c10cf765d9460c10cbf6598320540ed72959460c10cf76559460c10af769c9460c10af76989460c10af76949460c10abf6a0965cc10cef6a5845cc10eaf259845cc10e6f5d9845cc10c7f65d8320540e6f5d5845cc10ee768d845cc10eb7259835cc10e775d9835cc10e775d5835cc10de76919320540cef6a58458c10cf76159320540cef65d8458c10cf76199320540cf761d9320540eaf5958458c10cf765d8358c10bfa6804320910eb75958358c109ef6919320540ee76117358c10cbf61d9620540ded50c91609409fb6a44320910cfd20c9160940cef6a58454c10cfd60c9160940cef65d8454c10cfd6149160940cef6598454c10cfd6189160940ecf5958454c10ee768d8454c10cf765d8354c10cf76598354c10cfd61c9160940ed75958354c10bee6809150d40b6f69c9150d40dcf2559150d40cdf2959850c10adf6a09550c10cdf6609550c10afb69d5360810cf765d8350c10cf76598350c10dcf2559250d40cf76558350c10ed72558350c10cf76617350c10ee76117350c10cf76615350c10ee76115350c10cf765d8310c10cf76598310c10cf76558310c10fc75955350d40fc72557350d40dcf6589550d40dcf2609550d40af728d8620550cdf261754c9508ff690984c9508ff68c98509508ff6849850d50afb69843608108ff690984c9608ff68c98509608ff6849850d608ff690984c9708ff68c98509708ff6849850d70cbf6598120143afb69d6560810edb5d56560810ebb2997360810e7b5d97360810e7b5d57360810afb69d6360810cdf2159120143ebb5956360810cdf2159220143afb6a17620910ed72157360943acf6909361410a9f6989361410a5f69c9361410fe450d31501109fc2a53150110bf86889150110bf468c9150110fd45453154130fc654d43541408df694985c540c9f65885201438df694985c5608df2a58550c10 else 0xef75cd6360910fbe5916050110aff6995360910edf5955360910aff6994360910aff6954360910edf2954360910fe754d4350110fcf2954350110ddf5d59550110aff6944360910fd750d5354110efb5d98520910bdf69d5354110bfb69d6520910efb61d6520910fdb5d56520910efb5d98320910efb5d58320910efb5958320910edf5d58354110edf5d58454110fbb2997320910f7b5d97320910efb6157320910f7b5d57320910efb6117320910efb60d7320910f5f5cd7554110bfb69d6320910efb61d6320910efb6156320910fbb5956320910efb6116320910efb60d6320910ff35cd6320910efb6a15320910f5f5d17554110bfb69d5320910efb61d5320910bfb6995320910efb6195320910fdb5955320910efb6115320910efb60d5320910efb6a14320910ebf6116458110bfb6994320910bfb6944320910bfb6954320910fdb2954320910efb6154320910efb60d4320910ff35cd4320910ff354d4320910ef754d4360910aff69d5360910dfd5cc9160940efb6194320910df769d9320540df764d7320540dfb5cd9220540ffc5cd3150110fee5cd4350110fd72557350d10fe75cd4350110cfb6159220540ecf2156460143afb6944360810afb6a16520910ef354d4360810ef35cd6360810cfb2899810d10afb6a17320910cdf6609550d10bfc6849350110cfb2899850d10cdf2959850d10cfb6509260d10cfb6549260d10fce2954350110cfb6589260d10e7b61d7320910fe65cd4350110cfb65c9260d10cdf6609550d20fe654d4350110efa61c8250110efa6188250110cf76613150130efa6148250110cdf2959850130afb6954360810fd65453154130ef66113154130fd65d53154130fd66953154130fd654d3154130bf668c9154130fd65d53254130fea50c8250110dfc6589150110fd654d3254130dfc6549150110fd55453154130bfc68c9150110b7e69c8158130dfc24c9150110fd5551514c530ef5611514c530fd5595514c530fec50c9150110afb6994360810ef5611614c530ed7295844c5309fe2a53150110fe650d3150110dfc2a53150110cf72a5844c5308ff69098545308ff6909858530ff464d3150110afb6a163209108ff690985c530c7f65d8420530c7f65d8620530ff450d3150110cdf6609550d30ff82093150110a7f69c9161130cdf2559161130afd28592611308ff6a5844c110cdf2559261130ef5615314c110fe650d3154140df5651314c110bde2a15154140bfa6888154140bf668c8154140ff44c5604c110bee6909154140ff44c5504c110ff44c5404c1109fe2a53254140fce54d4254140fce5d54254140bde2a15254140bfc2858254140edb2954360810bde2a15354140adf2a15154140fc754d4354140fe650d315c140bfa688815c140bf668c815c140bbe698815c1409fe2a5) else (if j<3 then 0xd6548110fde5d5504c110ff5551314c110ff5591314c110ff55d1314c110ff55d5314c110ff55d9314c110cff551984c110cff5d1984c110cff5d5984c110efb5d15360810aff69c8460930cff2a5845c930cff2a58458930cff2a58454930bf769c844c930f775d5744c930bf769d544c930fd75d5544c930aff69c8460530aff6948460530ffc50d3150110cff6199420530cff6159420530def5519420530ffc54d3150110ffc58d3150110ffc5953150110cff2a58458530ffc5d93150110f775c5734c530bf769c944c530bf7694944c530efb5915360810ef75d9844c530fde5955150110bfb6984320910bf7694844c530f775d5744c530bf769d544c530fd75d5544c530fee50d6150110fd7595514c530ff52a1514c530ffc54c9150110ffc58c9150110ffc5cc9150110efb5d94360810bfe6908158130fd75d53154130ffc5949150110fde5d58254130ffc5d89150110ffa50c8250110ffa54c8250110fde5d58154130fde5d48154130bfe6908154130ffa58c8250110ffa5cc8250110ffa5508250110ffa5908250110ffa5d08250110ffa5948250110ffa5d48250110fed5c54150130fed5454150130ffa5d88250110e7f5d57460d20aff69d5460d20edf5d55460d20ebf5958458d20cff6598454d20edf5958454d20fee54d4350110ddf65c9550d20ddf6589550d20ddf6449550d20ddf6409550d20fcf2556450d20fcf5d55450d20fd72557350d20fe75517350d20fd75955350d20fe75915350d20f7b5d5744c920bfb69d544c920fdb5d5544c920f9f5916554520f9f58d6554520bdf6995454520fcf50d5454520fdd5955150520ddf595954c520fd7295434c520fe7591434c520fe7551434c520fdd595514c520bfb69d6548520fdb5d56548520fbb2997348520f7b5d97348520f7b5d57348520bfb69d6348520fbb5956348520ff35cd6348520bfb69d5348520bfb6995348520fdb5955348520bfb6994348520bfb6954348520fdb2954348520ff35cd4348520ff354d4348520bfb6984348520bfb6944348520f5f5d17554120f5f5cd7554120bdf69d5354120fd750d5354120ddf5d59550120fcf2954350120fe75cd4350120fe754d4350120fde5d55050120fde5d5504c120aff69c9460d10aff6949460d10fee58d4350110fee5954350110efb5d89260d10fee5d94350110efb5d49260d10fde5955350110efb289845cd10ebf5958458d10efb2898458d10cff6598454d10edf5958454d10efb2898454d10bfe6995350110fbe5956350110cff6617650d10ddf6609550d10bfe6949350110ddf6589550d10ddf6409550d10bfe6989350110fd75955350d10fe75915350d10fde5d55050110aff69d6560910edf5d56560910ebf2997360910e7f5d97360910e7f5d57360910aff69d6360910ebf595636091 else 0xc64c6c969926a242e46b88ad90fd213e41307ec0f6f1e643b7c7510e701c3a37286b08d2419e432a863c0c3017e62e545960ac314e028a04f0098d124822ec434080a0f6e1de839907000d70196830905d50b30159829484aa08820f601bd0306055008d00e00162021e02f003a0000bf769c844c530aff6984360910ef75cd4360910efb5d16360810efb5d56360810aff6984360810ef754d4360810ef75cd4360810edf2954360810aff6954360810aff6994360810edf5955360810aff6995360810aff69d5360810ef75cd6360810ebf5956360810aff69d6360810e7f5d57360810e7f5d97360810ebf2997360810edf5d56560810aff69d6560810ef75d98350c10cff5d99850c10ef75918354c10ef75d18354c10aff6988360940aff6948360940ef75d98354c10eef5d98454c10dfd5d89160940eef6998454c10dfd5949160940eef69d8454c10eef5918454c10eef5d18454c10dfd58c9160940dfd54c9160940edf5958454c109ff68c985c940cff60c985c940def261435c9409ff68c9858940cff60c9858940def26143589409ff68c9854940cff60c9854940def2614354940bef6988350940bef6948350940faf5956350940bef6995350940fcf5955350940cff5d4984c940cff5d0984c940cff550984c940aff6988360540aff6948360540cff6598454c10ef75d18358c10df758d9320540df754d9320540ef75d58358c10eef5d58458c10df76999320540eef6958458c10df75d99320540df76959320540eef69d8458c10df75959320540ebf5958458c10eef695845cc10ef75d99460c10ef76597560c10ef75d99560c10aff6988320540aff6948320540efb5d95360810ffc50d3148110ffc54d3148110ffc58d3148110ffc5cd3148110ffc5513148110ffc5913148110ffc5d13148110dfb5d99220540ffc5953148110dfb5959220540ffc5d53148110ffc5d93148110bfe6944348110dfb58d9220540dfb54d9220540bfe6984348110bfe69c43481109ff68c985c540ff654d4348110ff65cd4348110cff4c0985c540fee55143481109ff68c9858540cff60c9858540fee5914348110cff4c09858540def26143585409ff68c9854540fde2954348110cff4c09854540bfe6954348110ddf2616554540bfe6994348110cff698984c540cff5d8984c540cff694984c540cff594984c540bfe69d4348110cff58c984c540cff54c984c540cff50c984c540fde5955348110bfe6995348110bfe69d5348110cff261734c540fe75d9434c540ff65cd6348110fbe5956348110bfe69d6348110f7e5d57348110f7e5d97348110fbe2997348110fde5d55448110bfe6995448110bfe69d5448110fee5d16448110fbe5956448110fbe5d96448110f7e29d6448110bfe69d6448110f7e5d57448110fde5d56548110bfe69)) else (if j<6 then (if j<5 then 0x355264a4bd4962929524ca48d490291d5234a45d48a2911521ca42d48429055204a3fd47e28f951eca3cd47828ed51d4a39d47228e151bca36d46c28d551a4a33d46628c9518ca30d46028bd5174a2dd45a28b1515ca2ad45428a55144a27d44e2899512ca24d448288d5114a21d442288150fca1ed43c287550e4a1bd436286950cca18d430285d50b4a15d42a2851509ca12d42428455084a0fd41e2839506ca0cd418282d5054a09d4122821503ca06d40c28155024a03d4062809500ca00d40027fd4ff49fdd3fa27f14fdc9fad3f427e54fc49f7d3ee27d94fac9f4d3e827cd4f949f1d3e227c14f7c9eed3dc27b54f649ebd3d627a94f4c9e8d3d0279d4f349e5d3ca27914f1c9e2d3c427854f049dfd3be27794eec9dcd3b8276d4ed49d9d3b227614ebc9d6d3ac27554ea49d3d3a627494e8c9d0d3a0273d4e749cdd39a27314e5c9cad39427254e449c7d38e27194e2c9c4d388270d4e149c1d38227014dfc9bed37c26f54de49bbd37626e94dcc9b8d37026dd4db49b5d36a26d14d9c9b2d36426c54d849afd35e26b94d6c9acd35826ad4d549a9d35226a14d3c9a6d34c26954d249a3d34626894d0c9a0d340267d4cf499dd33a26714cdc99ad33426654cc4997d32e26594cac994d328264d4c94991d32226414c7c98ed31c26354c6498bd31626294c4c988d310261d4c34985d30a26114c1c982d30426054c0497fd2fe25f94bec97cd2f825ed4bd4979d2f225e14bbc976d2ec25d54ba4973d2e625c94b8c970d2e025bd4b7496dd2da25b14b5c96ad2d425a54b44967d2ce25994b2c964d2c8258d4b14961d2c225814afc95ed2bc25754ae495bd2b625694acc958d2b0255d4ab4955d2aa25514a9c952d2a425454a8494fd29e25394a6c94cd298252d4a54949d292250049b892f724fa480c8e5917d2206432c8128fc11dde397c6f28d6b198a312c5e88b83163e2aec52089c712c623a443788370f7a1cb438586bd0cb2177c2c88517085e0e7c19d827f03de05d408880810091ff3bfaa7ec4fc69f4dbe537c58f765ed93d6a7a86f3c1e59bc607846efc5dd4bb617598e961d0db9de72d4e431c5cb8877094e035bd7b7726e54dbb5b58367e6c82d869aeeb5956a9ad441a69b49668c8d0719f533ad670ccd25975b2b964f8c955906b1db6352c5dd8a2b1136180c20d8022f7a5e90bba9761ae4f5be2b64d6a02ce2594ab1a161b2bf9578eada5590aace54e0a8754f02982528aa3f54602899508c9fa13d0274d4df49a9d33526224be096492a5250d4974922120a23c146f28c15153a254441887110be213f41c281e101d9fe83f2a7cb0f721e863c3a77acec69d453a107300e471c4638286ed8dac1afa352268f8d0099ae32f864d0c7b98ba30e460d4bf1178f2e365b4cb3516172b725598a8f14ec293250ec9f413a026 else 0xc614cc82a70800cc3e1fc1c481e933e1d8f98561c328552ea104ca87a3f4380710a5f43784018267c3d1f70b4389052e168fd0e10c358501361001d8753e8448d0a0a450b84a3f438650c02c14d1fa1c2f84533e1e8fb85a1c338553347e8709a15c209753347e870c03007c0093e2286508a5d4aa87a3e07e8710029c280b01200dc3a0893e402850826543d1f03f4380710029c338401200dc3b2141127c9014e15c231970f27d040ee114ba95a3f4385508a6543d1f03f438070e02087687304240c12e255c251fa1c300e01820c07c9f16430a192ec7d870a615c2382632e1e4f8cc3805c9f003a1c5f0de17c2287044004ce0ec6587003638e0a4fe871c4ca8652aa1401a87a3e07e8700e29c338570903404687181428552e0304ca87a3e07e8712e1405b820130364fe871c1428652aa1e8f81fa1c038870ce11c100981a023438ea161401e52b47e870ca100f51fa1c228512ea6543d1f03f438750ca704aa87a3e07e8700e21c2b84632e0a06c9fd0e3a8503da704ad1fa1c36150400584199f140ce0201220c0899f1a87586018e10100091bc378501203281f87a3ee128713e1405b03f0ec7cc230e1d8330501203181b0763f6118712000c299733387c0fe0e1d42a8412ea6543d1fa1c038850d0654209550f47c0fd0e2287586c2a031c2020a1a3a9950c2554280350f47c0fd0e01c5419f0de1404d03f0f47dc250e2403499016c7d870b6180a8140182658fb0e1c0f00bb08c7d870b2100f31f61c238650aa114ca87a3f438750ca11c289550f47e870ea1942a9912ae1001a87a3f438914e610088953362d868050640588c39c358452ea54048de17c382001220110318034f982e083215b0da1c0b026140c80602a0140b02581a09880320180a80504a0720682401c480600a0100100761a0880400e2400186308655c2e1fc1c381482fe120ac0d026301400845e0680801c300600801c11415010038700a0500261723200a0681f046481500a050024190390340400e240280483201c1100801c3985b0c032c2080b0e0594710000c1199c3e07f0700e1dc31a132f87f070a65fc2199c3ee17070ce14cce1fc1c2585342e10cce1fc1c3000308664ce61f03f83807110541000c900e12470ce10cb995c3f838590a08241b84b0e298432ba1ccc8921a8bd19708030502106c0a785f0d80ccae1ff0f838c1160600841bf0d80f0ff87c1c6089028664caf85c0787fc3e0e304480f0020580581ef09037c390077c3785f0802800d82007037c39402e00800f0de17c2009d38400f017a73c3785013e1000103f0e500f50805948a9bf0ca63c280df0e5016f0a0440629b53006bc3910640c6860298000970e1d0b81642aa03c3d8451c3e0d029e1c09812e1c3011f0c027c280cd0540fc3810a1c55294a51d4a22941527ca4ed49c29) else (if j<7 then 0x980147c040c03d4da9802c003c38c02800f86f0be1006009d3800081f872c8ce85c2be1cc199f19c1003800180f45907c04c030286607b0800c0b0609e0f816806855c28c03005c000c0018630865f0f81fc1c3d8506600e0ac2b1408009f0b83419b842103c0d00608a007871404822801e1c441c02801f870450346f0de140878701e42060320180a805d080b001007c1a0c80f80801c681900c05002007c1a0bc0fc1501c511f01e0250440d14c318432a673438a0140a004c2e00c0381203e264071461ac2809b0800ec3a9f1224186b096728ad8753f614701208a06f87118330560e026c20b03a0fb870020885133e1404810007e1ccf89122c358501161dc20be1bc281033f61c040c0180280401001c5b0d6140850d7082802029839040846742183156058503f83904064648e78781a03c500002cc1e8401e67c601603f4278730667c601fe180040812a2e8402c044c199f140780c811610000a03c06408000201902da105280db0e303023361e06880c5c3119b0f0345232058068602f42001b0e0345c01e1bc280901987dc260e208c91c06003c423240c0b787020280c0038383d0c080c1a1912e8446d0c60c0799f134300f30667c4c3225cc199f104a0a501b61c4d0c006c380d100141c832e118c014002382e70808006009140c80602a0141301c00601c0a00e002581900c0500209500400c0381f0380381119e1bc2f8441a2029f0de17c220d0068014f90058020110c0c806d082540180704e07c0e00e28030050080580e00703e03080280104b80300e0bc4a80e200a81404004509019038381400908403e0d0250640710618cc80bc3f8385f0a0520cf87016280b01f0024f88618c2808339a1c540600f4398211c1003632e19c2b8480127c830ee19c2b8401e820630c6140418433860b438e61dc338470402590a0893e418770ae118cb8293e820701802407a0053e280902943bc32181060454f900b841897156a7c503343804883022a7c630c61404184d0e2c00807a1c3410eb643b84738e0a018e82000487f0ce71c2382806440070ae11ce386806320800121dc338473900c741000243b8670ae72018e8200048770ce15c24031c01a0890ee71c10a616ce19503d87f070d464c1003400200030c654ce61f03f8380711e10ccf87c3ee17070c6844bb86c3f8385308664c3e1f03f838070f614cce1fc1c201900c0540281400883401a0053e5185342664c3e1f03f838770b610d0999c3f83860126128cd8603161401d8753e250a30c6704a987c3e07f0700e201619930f87c0fe0e01c3a0c12e256c261fc1c31857380781561fc1c342c70c6844be1fc1c318633202f0fe0e14c2d8601361001d8753e2ac8f0c033c2809c07e1f0fb84c1c481e016e130fe0e15c3185308664c3e1fc1c3986308e144a987c3f83873 else 0x1d70ce1405e876323036b08654c1022002301d70ce1406319140ed86b0a0328c8a075c3385016c64570a0302032e1406076180b419e0e02c5e0e264230ee1405b820128224f8f21404b84a2a2003348618c299932ae130fe0e24c319c305a1cca808180f00b70987f070a684cbb86c3f8385f0de1404784938e1e410e614c2199339a1c560cc1404b07b0828220028343f0de140403513c37850100d4470ce1404384b0e2b8670a021ce5871405b84012030470ce114ab9cb0e298234200743999140589909c2b84010e72c38ac198280963ec0ec20c02c15380000086a701100000220090064540b60e154e0000021f86f0be1c04b841401800332618ca985c3e07f0700e2807a9b530058007871807e84856058481ca11c30160690340a298210741573803206a9819ce00c81a0508a8a05b4218333e228470ce701a40db0e340000210010130028f808140ab9c019036c38a02c008)))
def mo255H9 (j : Nat) : Nat := 0x1a2000105a000c0f63fe0d62a001d62660001c6f72c001212c88001583c6616c00145d440001e10001c43c72e2ee4400000021e00000000000064f47a00000000087400053b526a8c000000000a0453c031348c50000c86682000000001c3bc0274600154100b853766001216001601814e7f256e0666c00083c68b285e92476000d34e5f409424c81249928070c58a91a26462000e7987c81da36f24001a6800004b43803200182228f665f2e530454428b5823482c218e6ac4d64641a3142890156144800c3c119063020722044010024983
def mo255D10 (j : Nat) : Nat := (if j<10 then (if j<5 then (if j<2 then (if j<1 then 0xcc8086884ff660434427fb30a1a213fd9854d10df649306886fb249854437eb02a0861bed8250430ddec2282186df615410c35fb0ca08619fd87504309fecc282186fd605510c37db04a8861bbd8454430dbec2aa2186bf619510c33fb0ea88613fd9854430dfac0ae2186fb609710c377b08b8861b7d855c430d7ec32e2186fd551810c37eae8c0861bf59460430dfabab02186fd655810c37eb2ec0861bed5460830df6ba304186fb5d5820c377b08aa061b7d8555030d7ec32a81867f61d540c27fb30aa061bbd845d030dbec2ae8186bf619740c377b22c2061bbd7561030ddecab08186ef65d840c36fb0aba861afd865d430dbec8b0a186df651850c36fb2ec2861f5c855cd43df621b04086fe615404437daa6c10213fd9850130fec98aa0987de545504c3fb264a8261f795254130fbca9aa0986fe611504c3ef2eaa8261fd93158130fec992c0987f5545314c3f7286a0221fe88250110feab0a62987fc245404437bb0898a613fc98505309fe4c2a2984ff261614c3fe262a02213fd984c1109fe4c2e29857f65c814c27f930a12613fd9855130dbe4ab08986fd605311037bb0698881afd864c4409fecc262206fd605511036fb0aa8881afd86544409fecc2a2206f760d531036fb0aa9881afd8654c409fecc2a6207de54550503f7284a8281fd5314c110fbca92a0a07ee50d50503ef2a6a8281f797554140fdca12e0a07ee50d70503f3a8698a813fc984c540dbec2aa2a04ff261515027f930b0a813fc985c540bf6c9102a05f764c81503fe26290221bed4360810d7e4a30c086df659850436faecc2821b7d9361410dbe49b0a085df654815033fb0eb2821b7d8559410b7ecb102a057f65c815027f930992817f49160940fcea9a86a07e75cd4350377b0aa1a81f3c9550d40deecbb06086f7659830437baecc1821bdd9560c10deebab06086f7595830437bb28c1821bdc9460c10bf6c9106a06df615755036fb0ab9821b7d86545509fe4c2c2a86ef611730427f930b8aa1bdd835cc109fe4c264a867f61d630436fb0ab18213fc9850950bfcc8086a85fb6484354377b08b182177d9510d509fecc086a86f760d63043ebaa6a1aa13fd9854c109fe4c286a867f61d53042efb2ea9aa1afd8654c10ebebaae6a86df61553042feb2241aa17ed9220d50ddec22a6085ef65083542dfb2c41aa15fd9720d50deec1aa60875f5d5745427fb30a18216fd9621150d7ec3286085f724d865427f930b8ac177d9520560dbec2a86084ff261325837bb06a18213fc98509609fe4c286b04ff660430427f930b0ae13fc984c970dbec2886086f760c430427f930a12e13fc9850d70dbe42900a1dbf6588050f6f90ac0287b7c8560943fceb22a6a1efb5d9820437dacac1021bed7360810df6b1b04086fb60c824436fb0c42a87fe12148110 else 0x3284a87bf59563043feae2a0a41ff55150520bfecba62905ff65931482ffb2021aa17fd954c520bfec8886a86ff61163042ffb2898a41bfd8358c10bfecb2a0a07f75cd63042ffb2ea98217fd9654c10fbeb2aa6085ff64483543fba8698a41ff5614c520ffaa8a62907fb5d921483fdaca90a41fed7348520ff6b1a42907fb54d21483fda8690a41fec4348520dfec22a6086ff60d53043bfae6b8241bfd9850c10bfec8908a85ff65943042ffb2eb02417fd9550c10bfeca102b07bf59160483ef92aa1821efd6358120dfec1a86087bf58d42583ff2e0b02417fd9754120bfecb2a0907bf59142583efaeaa8241fdd7350c10feea9a86085ff64484582ffb2c21821f7d5354120bfec9902b85ff65d40482ffb2ca0241dfd734c970bfecaa80905ff654430437faecc1021bfd6560810bfec8906b87fb50d424cbdfac2b0281fed5350932ff6b1a84997fb5cd424cbf7a86a0241ff97050120ffca8280905ff65d30482ffb2c98241fed6550932bfecaa60907fb5d9424cbfbaa6a1a657fd944c120feeb9a86997ef551434cbef92aa1a657fd9550d32bfecba86996ff611534cbff2c098241ff9504c120dfec3b0c885ff66176442ffb2ea9a65bfd8458d32bfecc2ca885ff65d654437fb08b9a65f7d7559510dfec3b06886ff61983443bfaeab9a65bfd8560d10fbebaaa8995ff65d544cb7fb08c1a21bfd9760d10dfecb306886ff5d9834437fb2ac1a21bfd7560d10dfeb2b06886ff651834437f928c1a21bfd8458110bfecc2e68877f61d73443df92cb9a21dfd765cd10efebaae89977f5d573442ffb2a42265bfd845cd10bfecb908996ff60d73442ffb30b1a217fd9758d10dfeb2b08996ff5d9844caffb2021aa5efd6558d10dfec8b0021eff611634437fb24c0087bfd9560043dfec1ac6887f75cd634437fb02402877fd9854d10bfec8900a1dff6488050effb2ea9a21bfd7360810bfecb2a6886ff58d820437fb02c0287f7d6554d10dfec1300a1ff754d8050f7fb08a9a21fdd7360143fdeaa300a1fef5918050f7fb06a9a21bfd5360810fbe42b00a1eff6158050fef92ac02877fd9850d10dfecc286885ff65d604437fb0cc02877fd9650d10fdea1ac0a07bf58d605037fb0ec02877fd9550d10fbe4aa86887f754d8250fdfac8b0281ff9315c140ffc40ae0a07f75cd8250f7fb06a1a21fdd7350d10dfea1b04087df2158250ffbaa6a1a21bfd8560943bfecc086885ff65843442ffb2a21a217fd9010d10fbe4ab04a1eff5d9824437facac1221bfd7360910dfeb1b04886ff54d824437fa86c1221bfc4360910dfec3304a1ffb5d882443bfae6b8221fed6520910dfec1ae0887fb5cc82443fdac641221fed5320910ff6a1904887fb10c824437f886c1021ff9404c110fbea9aa0887d75955350f7db0a41221bed8620910bf) else (if j<3 then 0x80887fe65540443f7a86a0261bfd7660c10fdea1b04a07ef50d505037f906c1281fbd4150130fee98a80987fe5c1404c3ff2c0a0261ff95050130ffcbb280887fe61940443ff32ca0221ff98750110ffccba80886ff645840c3ff2a0a0221ff96050110ffcb8280887ef50d404437fb06c1281bfd8560940dfec3304a07df54d505037fb06a0221bfd8760940fdec8286a07ef245435037faeac1061bfd7460830dfeaa304186ff61140443f7b22a1a81fbd9250d40dfebab02186ff5d1810c37faa8c0861bfd8550110bfecaa80886ff655830437fb0ca02217fd9650110bfecba80886ff61170443ff302b8281fbd6350d40dfebab06086ff60d50443f7ae6a1a81fbd6550d40dfec22a0887df5d550443f7aeaa1a817fd9654110bfecbaa0886ff661410c3ff2e0b0221f7d7554140dfec3282186ff595830437fb0aa0861efd6358110dfec2282186ff60d60443f7b0aa1a81efd6458110bfecbaca907df5d5654837faecc2241bfd7561120dfeb2b089077f5d5744837fb28c1821bfd845d120bfecbac89077f25d64483dfaecb2241efd6559120dfec22c8907ef5d164482ffb2eaa241fbd9550d40bfecb2a8907ef5d943503efaeaaa241bfd8455120fdec3286a07ef65943503f7b0ea1a81fbd9750d40dfebb306906ff5d5834837facac1a41bfd7460d20dfeb2306906ff55183483df92cb9a41dfd765cd20efebaae6906ff61173483f7930a1a81bfd835cd20bfecbac6907f754d43503dfacab1a41bfd8458d20fdeaa286a07ef591435037fb06b1a41fdd7358d20fdeba286a05ff65d53482ffb2ca9a41f7c9550d40fbeb2aa6905ff655435037fb08a9a417fd9650d40fbeb2aa6a06ff60d53482ffb2ca9a817fc9854d40dfecc286905ff66153502ffb2ea1a41efd6558d40bfecb286905ff26163502ffb30b1a817fd9550d20fbe4aa86905ff26173502ffb2241a81bfd8450d20f7e4b2e6085ff65483503f7ac8a1a417fd9620d40fdeaa286906ff60d434837fb0ac1a81fdd7350d20fbe4ab06a06ff61983503fbaa6a1a41bfd8760d40bfecb2a8a05ff65c43482ffb2c21a417fd9510d20bfec8886905ff64043483fdaec99241fed754c920ff6b2a64907fb5d132483fdac899241fed544c920ff6b9a64907fb58d32483fdaa699241fed434c920f7eb2ac8a077f5d171482ff930b2a81dfd735c520bfecc2caa077f5d973043efb0abaa817fd9758520dfe48b0aa077f25d86503dfac8b0a41dfd755cc10dfec22e6086ff60d73043feae2b0a417fd9754520bfecb2a2907df54c81543efacaa8a41bfd8320550bfec9902a87df551514837fb0840aa17fd9420550fbeba902a85ff65d41482ffb2ca0a41bfd8620550bfecaa82906ff61c81543efaa6992a1f7d754c950dfec3a64a85ff65d63043efaa6a12a1f7d7550950dfec else (if j<4 then 0xa06ff611724c3ff2e690221bfd8458930bfe4c2a2a06ff611524c2ffb2c982217fd9854540fdea1ac2a06ff619424c3dfac8b0a81efd8658540dfec2a84987fe58d20442ff930b0a817fd9858540dfec2284987ef50d71503ff2a6902217fc985c540ffca1a40887ef50c81503ff2ec90221bfc8320540dfec3a64986ff615324c37fb0640a81bfd844c930ffc21a40885ff64c81503fbae699261fdd634c930feea9a64987f750d324c3fbb0e99261fdd864c930feebb264987f7615324c3fbaea99261fdd654c930feec2264987f7211324c3fbae899261fdd644c930feeaa264986ff61d814c37fb0cc0a61bfd8520540dfec2b02985ff65d650437fb08c0a61bfc8460530bfeca902a06ff61881503efaeab2821fec9260530bfecb902986ff61d304437fb0e40a61bfd8620530bfeca902986ff614814c2ffb2c40a817fd9420530dfec2102986ff61c815037fb2ec18217fd985c530ff649302a05ff65d30443bfb0eb8a61fbd4360540dfec22e29877f5d1714c3bfae6b8a61bfc8360540ffc98a80886ff60d815037fb08b0a61bfd8560540bfecc2a2986ff61981503ff2a2a02217fd9754530fbeb2aa2986ff61d815037fb08a8a61f7d5454530fdea1a64a07df545505037fb30a0a61bfd854c940ffcb0a80886ff61d325037fb2cc1821bfd8650530bfe4c264a07ef54d425037fb0aa0a61fbd6350940fdeb9a84a07ef20d42503f7b06a1281fbd6550940fdebaa84a07ef61542502ffb2e98a61bfd874c530bfecaa62986ff615314c3f7aeca12817fd944c530dfec2262987ef61942503f7b0ea1281fdd734c530feeb1a62987f754d314c3fba8698a61fbd4350940fdeaa284a07fd545314c3fb93098a61fdd974c530feec3a62987f7659314c3fbb0c98a61fdd764c530feecaa62987f7615314c3fbaea98a61fdd654c530feeca262987f7251314c3fbb0898a61ff97150110fee42262987f75d1314c3fbac898a61fdd544c530feeb8a62987f7585314c3ff322a0221fdd514c530ffca1a80887f7641314c37fb08b8261dfd735c130efeb8ae0987ef59142503fba62b8261bfd8458130fdeba284a07f74c5604c3ff308b0261ff98258130ffca12c0987fe54d40443ff302b0261ff88158130ffca0ac0987fe58d40442ffb2ea8261f7d7554130dfec22a0987df54d504c3efaa2a8261bfd8550940fee98aa0987fe5cd40443ff308a8261ff98350110ffc49a80887fe609504c3ff326a0221ff94254130ffc992a0987fe55140443ff122a8261ff98154130ffc40aa0987fe59140443ff282a8261ff93154130ffcba280887fe59540442ffb2ea0261bfd8650130dfec3284a05ff655404c37fb0aa0261fbd4354940bfe4c2a4a06ff611404c3f7a86b12817fc9858940fdea1ae4a05ff64d404c2ff930b9281ff97550110ffcc2a else 0x7ff5d5314c3ffb20a0a61ffd4350530ffea9a82987ff58d414c3ffae6a0a61ffd9350530ffeb2a82987ff615414c3ffaeca0a61ffd8650530ffecb282987ff5d932503ff930a0a61ffd754c940ffeb2a64a07ff5d132503ffac899281ffd544c940ffecc282987ff58d32503ffaa699281ffd434c940ffec0aa2987ff611514c3ff930a8a61ffd7660540ffec0ac2987ff59581503ffb08b0a61ffd815c530ffeb9b02a07ff58d81503ffaa6c0a81ffd845c530ffe4c2e2987ff550814c3ffae840a61ffd7520530ffeaa302987ff591814c3ffaec40a81ffd7460530ffebab02987ff5d9814c3ffaca40a81ffd544c930ffeba264987ff5d5324c3ffa86a1261ffd5350930ffeb1902a07ff54c81503ffac6a1261ffd7350930ffeaa284987ff591424c3ffae8a1261ffd8450930ffeb2a84987ff5d5424c3ffb0aa1261ffd7650930ffec1ac2a07ff619424c3ffb0ea1261ffd8454930ffec22c4987ff611724c3ffaa8c1261ffd6460930ffeba304987ff5d5824c3ffaecc1261ffd8455130ffebb260887ff611644c3ffb08ba261ffd764c540ffebab08987ff59531503ffaecc2261ffd754c110ffeb1a62a07ff54d31503ffa8698a81ffd654c110ffeba260887ff59130443ffaa898221ffd734c110ffeb1a60887ff54d30443ffaa6a0261ffd545c110ffea1ae0887ff5cd43443ffacaa1a21ffd7650d10ffec3286887ff5cd40483ffac898a41ffd4358110ffeb9a80887ff5cd82503ffae699281ffd7320540ffeb9a62a07ef54d43503ff2a098221ff98254140ffcb0260887fe50950503fea6298221ff93254140ffc48aa0a07fe60550503ff102a8281ff9325c140ffc98aa0a06ff64583103ff2ea90221ff9825c140ffcb2a40886ff60d304437facac1081bfd6360840dfea9b04206ff595811037fac6c0881bfd5360440ffcc1ae0a07ef50d70503ff2e890221bfd844c110dfecc262205ff651304437fb0e98881fdd434c540dfec2a62206ff60d31103ff306a8281bfd854c110f7e4b30e986ff245854c2ffb30baa61bfd8761130dfec3308987f760d31503ef92ac2261bfd8561130dfec2a62a06ff65d844c37fb2cc2261bfd7661130dfecab08985ff655304437faeac2261bfd6561130dfec9308986ff645844c37f922c22617fd9721130bfeca908985ff644844c2ffb30ba261dfd755d130bfecb262a06ff611744c3ff2c890221bfd8459130bfecc2a8986ff26131502ffb2eaa261f7d7555130dfecc262a06ff611544c3bfaeab9a61bfd845cd30dfec22c6985ff65d534c37fb08a9a617fd9750d30bfecaa86987df255434c37fb08a1a61fbd5450d30feeb9a86987f754d434c37fb0ec1261bfd8660930fdea1aa2a06ff615824c3efaa8a8a81bfd8460930dfe42304987df59551503ff2a890221f7d8554540bfecb2a2))) else (if j<7 then (if j<6 then 0xf5d563483ffa86a0261ffd6350130ffeb2ae0887ff58d70443ffaa6b8221ffd9050d10ffea9a86887ff58d43443ffb06a1a21ffd8550d10ffecaa86887ff65943443ffb30a1a21ffd9054d10ffec8aa6887ff5cd53443ffb06a9a21ffd6454d10ffeba2a6887ff61153443ffb28a9a21ffd7654d10ffec32a6887ff61d53443ffb2ea9a21ffd7558110ffecc2a6887ff60d63443ffae8b1a21ffd8458d10ffebaac6887ff61563443ffb0eb1a21ffd835cd10ffec22e6887ff61573443ffacac1a21ffd7560d10ffebb306887ff61d65443ffae8b0221ffd7661510ffea1a60907ff58d30483ffae698241ffd544c120ffeb2260907ff5d130483ffaca98241ffd754c120ffebb260907ff50d40483ffaa6a0241ffd6350120ffeaa280907ff59140483ffae8a0241ffd6550120ffebaa80907ff5d940483ffa86a8241ffd6354120ffeb9aa0907ff59150483ffae8a8241ffd7654120ffea1ac0907ff54d60483ffaa8b0241ffd7458120ffebaac0907ff5d943043ffa86b8241ffd535c120ffeb1ae0907ff55170483ffac8a9821ffd7454c10ffeb2ae0907ff50d31483ffaa698a41ffd7654c10ffeb1a62907ff5cd31483ffaa898a41ffd744c520ffeba2c6087ff59531483ffaea98a41ffd764c520ffea1a82907ff5d563043ffaa6a0a41ffd6350520ffeb9a82907ff55141483ffac8a0a41ffd7450520ffeb2a82907ff5d541483ffaeca0a41ffd4354520ffeb1aa2907ff5cd51483ffac8a8a41ffd7454520ffebb2a2907ff50d61483ffaa6b0a41ffd5458520ffeba2c2907ff5d561483ffa86b8a41ffd535c520ffeb1ae2907ff55171483ffacab8a41ffd9050d20ffec8a86907ff54d43483ffaecc1a81ffd6350d20ffeb9a86907ff59583503ffaa8a1a41ffd6450d20ffeba286907ff59543483ffaeaa1a41ffd835cd40ffecaa86907ff5d943483ffb2ca1a41ffd8358d40ffecba86907ff64553483ffae6a9a41ffd6454d20ffec1aa6a07ff5d153483ffb28a9a41ffd7654d20ffecbaa6907ff55163483ffae8b1a41ffd434c110ffeaa2e6907ff64154483ffb22aa241ffd9355120ffeb22a8907ff5d954483ffb2caa241ffd655d120ffeaa2c0887ff54d60443ffaeca8221ffd7454110ffeb22a0887ff5cd50443ffac6a8221ffd4354110ffebb280887ff5d540443ffacaa0221ffd7450110ffeb2280887ff55140443ffac6a0221ffd7660940ffea9a80887ff59582503ffa86a0221ffd4150130ffea8a80987ff58d82503ffaa6c1281ffd6150130ffeb8a80987ff5cd404c3ffb06b9281ffd5450130ffeb2280987ff60d62503ffae8a0261ffd6550130ffec1aa4a07ff5d5404c3ffaeca0261ffd4154130ffeb2a84a07ff505604c3ffa82b8261ffd514c530ffeb1a84a07ff54d42503ffae298a61ffd544c530ffeba26298 else 0x25bc72dce16d9cb6465b072d6e16ad8b4da5a512d06967ecb39659552c7e963acb162587c2c2b160acaff657cb2bc615d98ae5856f72b6895a5cacb0561e2aef95658aa9a54e62a6295290a90654582a1695008a7b853b629c314d94a674530f297994b34a56c528b2930148fca43251e428d2945fca2bc512e287014284a1005050280d93fe89f9e4fa427ba13d4c9e504efd276b93a749cd04e4227069379c9b964daf26c4935649a704d1226739330499404c7f26251304097984bab25ac12c1495be4a96253312914942049db24da9260092dc4952249b1245491de48c924541221c90cc484523f411e688efc4749238291b2c8d5e466b2322918908bd445ce22c7915cc8ab8453b2288113a88988449e223c110f8881c43f721e610eac871e437321a910c8885bc429a21379094c846e42202104907b483c041c920d91064482e0414f20971045c81ce40c6204390198806c40011fe38fe347ed83f551f950fc387dbc3ebd1f4e0f9b07c8c3e2f1efa8f7007b3e3d651e980f3c479783c871e2e0f04c77d03b8b1dad8ecac75e23ac11d500ea2474c63a421d068e79c7364395a1c978e3fc71bc38a91c440e188705a38111bf08dde86e9e37241b6d8dae86d0a36641b1f0d8746bb235951aa88d420699234941a2d0d0bc6786338e19b90cd0865fc32ba194a0c990647c321d18f68c730632e315318940c4086190304d17fa8bf645f482f8317a98bc8c5de62ec3173d0b93c5c2a2de516e20b6005a3c2cf316690b238589e2c2e16090afd857b42bb415bf8ad14563e2aea15558aa1454c82a4815188a84053ca29c414d40a608528628ff145d8a1a0501627cc13c689d9c4e5a26f3135c899fc4c8a260b12eb0965c4ad825411290093c0499e24ae123c891384850240211ee08e8846e42338117f08b104528225f111a08810439e21a910c408574425a20fd106b882c440f8204c100e07fc43f8c1f9b0fbd07d503e521f030f6487a503cb41e0c0ee4076243a9e1d1a0e7a0732439281c550e0d86f8437581b860da606c5c35ce1aa80d3c0690c341219bb0cc306558322418e20c5186190305417f00bd885e182ec017350b8505b902d7c168e0b31858cc2c0615c90acc855a42a9015180a76852f4290614300a0284f2c27221366099884bf02598127e09248483c23be11b408b5844c4220210bd084404138201e0fd007cb03d701e3a0ee80754839bc1c740e0006e3036301a9a0d1306740330819240c71062083008179a0b8e05aa02c7c15de0aba054502940142c09e104d10257812700908045f8223c10dc0843040c01fa00f70078803a701c640dd206be0342019780c1605e002da8163c0abe052f0275812c408da043d020180efc071e035a018b00b5c053a026d011e8085c03ba019900bc004f8021200c5004580158003800007f) else (if j<8 then 0xa2ae45571cab8b55c42ae155704ab7f55be2ade556ecab7355b82adb556d4ab6755b22ad8556bcab5b55ac2ad5556a4ab4f55a62ad25568cab4355a02acf55674ab37559a2acc5565cab2b55942ac955644ab1f558e2ac65562cab1355882ac355614ab0755822ac0555fcaafb557c2abd555e4aaef55762aba555ccaae3555eaaa2154ceaa41550b2a7d553a8a9a954bf2a575525aa9025470aa2b1512aa8745429aa0c95018a7e653e029e7d4ed4a753539929c314db8a6b65345a99094c2ea5ce52cf295f54a90a51d527e2931d4942a46c5225a909547cca3ca51c328d6d4674a305516fa8a9544e0a23150f6a87314338a15d50942840941b8a098503e2814540569ffb4fed27ebd3eea9f404f85a7af53d109e534f07a77cd3b9a9d934eb1a74e139f29cc94e4f2717d38549be64de2a6e0536849afe4d5826a1534aa9a2f4cfaa6715332a99654cac264a131fa98cd4c51261dd30a2982b4bf3a5ea12f0497434b89a5b512d5c967e4b29a58792be695d24ac4a558d2a9895174a73a53412954947f4a2ca50cd281a93d849d924df526869313497e24b1d252e92764925a488123e091c548caa459522609100486d242d12108904f480d23f591f2e8f58478ca3bb91d5e8e7a47252382d1bde8dd846d1a35e11a908d13466a2324118b68c1745f122eb516dc8b34458722b8d155c8a88452c2288d13e689b944d1225a1124888ef445d221ed10c8881643f321e9d0f028742439321bed0d8c869b433aa19290c2a85d642d8216010a3284ee425f2128908f884514210a0fd90764837d419a20bc10594828641212088503f681c640d7a05fd028081154075202d50128806440151ffe8ff807f7c3fa61fc5cfd9c7eb23f461f998fc6c7e1f3efc9f6d4fac47d193e721f2d0f9307c683e1e9f048f7ba7bad3dc39ed5cf6587afc3d701ead4f5287a6e3d1f1e810f3b279a43cb79e4d4f1f678c63c411e148f04477e33bdc1de0ceeba773c3b901dbe8eda876a43b419d938ec4675fd3ae19d624ea9e751a3a779d2e8e8ec74373a061cf34e71c736d39a39cc34e5ec72da39579c9ace49e7238390e1c7ece3a0718738b59c4d8e20c70e538699c2a0e0f0703e38099bfc8dfa26fb537ca1bdb8de906f2737809bba8dd6a6e8537259b880dbcc6db136c31b56cda2e6cdd36519b140d8226bdc35d89ae2cd6c06b26357d9ab18d5226a6b35229a82cd3ca69ce34c29a518d21868f0345d9a240d0f26849341199ff4cfc267ac33b919ce0cdf266d83354199b8cc7c661832f419730cb246558328a193ccc972647f322519054c7de63c431c518d90c64062f5315b18a18c4a2620830f1186b4c30461573093983dcc198608d302c18064bfd25fc32fcc17d64be705f122f6e97af0bd365e5c2f0e97778bb5c5d882ebb174c8b9dc5cbe2e4217114b8 else (if j<9 then 0x60990530e228505011a090347f87438842785e183b86c950588209b87248386f86257850588209b0e2428e1a86032a7e150347f8743a842e1be1895e143be1c1620826c38a0621be183be1c1620826c389257850ef870448209b0e202c030a4a7386e150347f8743a842c04e1787460990d30e1c19054140100b07b86e1409e100ca090347f87439006099e183be1c1609b0e228405c2e40c1547f874388a143ae1c8204408c38705021e120d05f8704c12c3890621704e15c3883e1c9fc14905810e1685e182b0440ca090347f87438d05f860af840348305682a1c13c38b0468402c1ea7386e1409e110347f87438d065170b83903515a1c13c38900c17e1816a7015a0838e1c13c38be181426495e102800d032711fe1d0e208d05021e120d05f8708c2fc389e12170d00d46425a0a8708f0e281be1418e190300e99a569c47f8743a8237860b2992578400d03a711fe1d0e208c08785047840669c03483a1c23c38b00e17e1416a0837e1c23c389808200b81603280e1d84a3890341705815203872387e1685e1b87a7d840802e0240ca38be1685e1a87a7d84a38200b8090328da0cda101605c98e1c0b19ad6718280d95617846661f839862d9c80e00e19820799587e0e610a001856720366597e17840321f60a0e618d69d9c80e00e1b840321f60a0e614b0899ce1b85e100060808a1f0e298667d8ea1117e1b1c45702e1c092c0300386e178416b9555ca4ae4f57262b9255c8cae4357202b8f55c74ae37571a2b8c55c5cae2b57142b8955c44ae1f570e2b8655c2cae1357082b8355c14ae0757022b8055bfcadfb56fc2b7d55be4adef56f62b7a55bccade356f02b7755bb4add756ea2b7455b9cadcb56e42b7155b84adbf56de2b6e55b6cadb356d82b6b55b54ada756d22b6855b3cad9b56cc2b6555b24ad8f56c62b6255b0cad8356c02b5f55af4ad7756ba2b5c55adcad6b56b42b5955ac4ad5f56ae2b5655aacad5356a82b5355a94ad4756a22b5055a7cad3b569c2b4d55a64ad2f56962b4a55a4cad2356902b4755a34ad17568a2b4455a1cad0b56842b4155a04acff567e2b3e559ecacf356782b3b559d4ace756722b38559bcacdb566c2b35559a4accf56662b325598cacc356602b2f55974acb7565a2b2c5595cacab56542b2955944ac9f564e2b265592cac9356482b2355914ac8756422b20558fcac7b563c2b1d558e4ac6f56362b1a558ccac6356302b17558b4ac57562a2b145589cac4b56242b1155884ac3f561e2b0e5586cac3356182b0b55854ac2756122b085583cac1b560c2b0555824ac0f56062b025580cac0356002aff557f4abf755fa2afc557dcabeb55f42af9557c4abdf55ee2af6557acabd355e82af355794abc755e22af05577cabbb55dc2aed55764abaf55d62aea5574caba355d02ae755734ab9755c else 0x2d1906784a13864701505800e1d0e2c15e140546786e111c0301600387438c46416e16844700043b872119e191c05000e1d0e1c1346786a1816003874388019194738505000e1d0e21190ba8447100e1d0e1d190611c05100e1d0e1e8606119a111c05500e1d0e24064641847014403874388e17860340f26c9805800e1c9067860c0110bb85a100d61c90541e0300f8202ce1b85e1000e1cb2638526f8605b1c0358361c9e1786a100d044ab0581ae1c9e14162601106b8718314700b61898e14162538726860c021e1411e100d61c8a1b8503420064970441ae1c9070020641507a0d1040b03e00c38b06415017860538403803834021041d0700f8030e401f0441b0608405200c388e181f03a0d070110ba8480010c38b07f8603a0d072210ba858002fc38be120d08411a1a0004b0e200b03f86e17840271c0009fc38a03c0bc7386e1409e100027f0e284002b86e17840018200e8726000018480c0b0799ce1b85027840321f60a0e3c1706199e1a036701587f87838a0441be18180519580e1fe1e0e614b609850459980e1fe1e0e6189614140458280e1fe1e0e20180581006f866578500e0387f872120e608e02c10e182ee14090440020c9fc38b0d01b0851940d1fe1d0ea1094729c06f86062850529540d1fe1d0e210d0742fe100925c2e0008327f0e280f0d021e1784064110008327f0e2c1905414e183fe17840968203600c38c02c01e1b85e1009c700d27c08c3a8730a40640be1b85e1c0c0442e6130e2c026180be1784e1c0c064970470e2c02e17866100946d180501ae1c01c38c80809e1b85e1d840802e0330e29850799c031a1e178480e1fe1e0e618c0f99c0302ce1b8480e1fe1e0e614b6b59c66585e120387f8783986283d6700c0b386e160387f87839842c2c6700b687856120387f87839862c2c6701e0ab866160387f87839842d8402c1e67386e1409e120387f87838ce182c6642ae100380d9c87f87838be178625482080160370e2219c7387062860530e1e850f011a090347f8743a86241f4081145600c3860f3860ac95837870982fc3890a285a5e82e140ce110347f8743a86300e0f385044998378709812c38aa140ca669c25f85e110347f8743a863034e182be140d20c25a0a8709b0e2e840d2a70868240d1fe1d0ea14aa703c0328240d1fe1d0ea1490442ee1439a700d20e8709b0e2b85e189925414270820eb87249505785c178626704270820370e2c28a180ca5ea7e110347f8743a852f86050992541ae1c9c20801c38a0178607c9925414270820eb870230e31190302c254a7a7386e110347f8743a853404e1787059180470e1c0505011a090347f8743a84241500803047860af8505a820ef8701026c38ea16a70468240d1fe1d0ea10903b87060990530e1a860b9030551fe1d0ea108a1602e17874)))) else (if j<15 then (if j<12 then (if j<11 then 0x80903100e1c08c3920701b060074342205100e1c08a130e301e08839e1b85e100c0028202187c38c06014c7c1102187c387e1685e182045416e10004090ee1cb00e9f083864578505b84a7102438b45415e1685e19020801600387438b49024e1685e19154081100387438b49c13e1a86455020801600387438b45415e1685e10194081100387438be1405e19154082005800e1d0e2816a7034e1915e1414a10004090ee1cca178600d1505a9f4090e22854578605902003874388a141140800e1d0e181345786a181640800e1d0e2685045020038743860141140800e1d0e1820a7115e1434e10004090ee1caa168600d150829f4090e2285a182045400e1d0e1e85a191504400e1d0e1c13a191508000e1d0e1c34059b1e1a15e15848360283b872d85082156c7848360283b872785617860821505b840020283b872c160d18685785051848360283b872c160d38685785051840020283b872c20857850d3840020283b87242580c34e1a15e141667202838a09603857850819c80a0e202580d86857850599980a0e2785a14090d1150510240387438aa1515045024038743870f01640900e1d0e1a854541406502403874388e141b4541402502403874389e1685025150d102403874389a15150450240387438704d1508102403874387e1585857868082005800e1e0e2985059868558480a00e1e0e2785024348541480a00e1e0e2785026150d202803878388a16864541140900e1d0e201345686059024038743886141180800e1e0e19858541180a00e1e0e1d8561a1504602803878388a1b85e1c2085e19030700f85e1a036659587f846720e608b07385e180d0211b460160038729a46720380386e140c87d82839842f85017860138400c0826515271028038705a0e3c0e0541e05b86e140d03c340ae8400387348401385e180d03c9b2601605000e1cc0543005834e182be16840358361cb0589126f86263850500dc09872b85e189b4541606b871f85e1a842462b0583ae1c82100461898e141666414c0b87280ea141e0bb840340f05c150ac00e1cc0c02e05f86056850af840358361cb07f860541e034340ad8410400e1cb0381c0678505a0d02c0f803872801e1b85e129c0031f1d8507c1e0340305c150ac41003872c0b00786e17840269c00103e1ca07c1e8344102c0f02600c38906415e18140a42ae120de1c2c0a30e3034e182be160d043870b30e2417e18150af848342fe1c2cc38a03c1608a9ce1b85e10016080de1cb064140881ce1895e17842080001d0347f87838f07e17e1434e120de1c2c04b0e28a1e1784e1c340b08327f0e241905786050420a80de1039a72870b30e341f06c18024140eb870230e2785e1810080330240c0eb8761008c38c057854678605b840311ca080043b87311906785e13864702e05800e1d0e else 0xc718425f072545e1b85e121c61f8767c0880890541d09d06a1a8505104a10090300228507a1d0d08a1f838015386e17840700261c8d0208619850718767c2c05008200541a86412844729c03107a1d0d87e0e254e2191bc130725ca11986865858540c6120220016a38a218852700c40008189f0b8200580c2008e1c2e0801620c8e61c600085c16848109780887c1c1f0300e264d05d85815848119c8718600a0387e0ea1cd0008606f06a12042731c21f0707c95038d8000061a06015848119c8700280e1f83a873986a1985a1584a100c61e8723816024c614850909706f86a731cc1c95288761a8661685612840240c0588d2d84a18840ba87a7c1603080501d091194189905505a16840100c0080b41e874342287e0e005561886a151708287a7d194440c2a85082870258415852168445c2ea1c0945416268441a8641685010954729c41e8787c0c342461a06616050119c8700280e1f83a873786e140ce1d84a38091d86a1985a1587a1c09239842786e140ce1d84a38091c8621484031000206e1b854138403107e1f0e02492109cc1c958000819866128445d87a1c0923915058a0008621018c121c25c87c1c1f03895024d208970b80d2540fe1c012082c10978340fe1c011d85a1584a111961e8702586239112c140800026486867062548585705611048720200c87c1c2207c0c0200e025805b8686706e1615c161c80b0de1f07c7c0c6130e0251a182e6129f03050398625f848371f46498257872a068640d25e1103c6a18970440e03c0060d9fe1c961886a151708111a7d19030941a86a101c07907a1e1f03090301661b0546f0425f0726498000061a0661605612040700280e1f83a873b86e140ca1d84a3a8d024809016266190570587184c1c2202cb61a866168521d8463a8e0249218852108240008180021819c18840530421f0707c0e2549c34a409086c1885c1414410992540321f0707c222080e0049c4c8621484c1c82400084388a1f86e14090308d182d01805612046721c60a0280d1f0210e360000005e199c8718460a0280c08438c615846718680e0019866119c80e0015866159c80e0015866158480e0016068160407203021821d866128445c870598ea3915024a6b58661584671828011f0210ea1cb06ca1c1c0c25c99800765585e199c611828000843a872a8601905a1504a111ca708203000020c6658565d846718680076558661584672001986615846720015866158480040060060808a1d9c183d812036718287e0ea1c8a1a85a109c00400199cc1c018020e140405416617870441e1c2267386e1582610010031f02287c38c6182267185e118265d950031f02287c38de17860201426495e110d0889c20900e1cde1405e181426495e10074342227100e1c0820b0e4019054140100b07b86e178401d0d08) else (if j<13 then 0x415a909ce1b85a100c02e8240f8747d0e4906a1905a14042551ca700c41e8740d1f438823ca183497266001786e1504e100903103e1d1f438a0a38625785c1004e1d9f2643b0200e058d21821210180249725487c7c1fc38b2109c2560002052181b21418050090300321f1f07f0e038d0608421c8385c13854761a0d25c95c1e001b86083850b80903303e1f1f6130e2e0d25c95c1e001506a1a840701e03107a1d0347d0e208ca111783515a1c52180825c0010852089983600020625c9ca108225600c1c08218645f842660d456871c976199ca0a0dc1e001c8605c990440bc7f0e1c2e0441e02d84c7f0e1c28e1b8420f8767e180200e266152c86064840609c25487c7f0e259c00707800406e21e108720d17864232085210828360002062188425600020505f84255198345218850060d80008181905414264952703dc7f0e242d01805612046721c60a0280e1f83a87360000005e199c8718460a0280e1f83a8734852108386f872561908c861115264168345c10972609500056198505a0d118427117834461517e109983450060008860040d0004610010340010852109c836000206218842709580008191727184409158346218852720d800081984408998344213066170505416c7f070309218852120d80008188661705a13040d0152471f26707030c21306c7c14c1c1e1b06c161505b03c7f076100c2486c1885c16150589fc7f07030a21705213048549b27f1f26707030b41899a1905a14048540927307434b21408e18950340019840040d000421984a119ca709700008208427095400081485c1615a109927f1fc1c0c2405412842721743462189c20895400081800a120421f0707c950389926854109985f84c1d0d1d86c1c9728446188661685612846729c00400020b21586a1984a119ca7095000082a8561099c7f07078661186a1985a14846729c00400020b89432c158626099c7f070530e28252170500898a109fc7f072648ec38c61a8661685612842700820800298661785e119c06587e1c08834ae1985e102261f870220d21ad0b4066101b8119c8718781e0d47c95438ee1b856102261f870220d20191103161a0525c0b870820798461e078342247c08439209c978701e81e0d47c954389e1b856138467187e1c088349e1895e1784000398342267008438ba1405e1904a109c004000209214842700c4000818a100499400406f04c1c976170e26472141bc1307254991a85c1584410172671fc1f0e0d0aa160228584c1c1e2647e1815e1584267070d40283603281d05e8601a8505104a100c008a141e874361f838994785e10996184300a0d80c8a141e4729ca1907a1e1f030921884270954000818002101bc1087c1c1f2540e264a09d17271844560d182d01584811022660d1c2c0d486c1885c149925414434a else (if j<14 then 0x80241661518c1097c7c95c1c9617840738727c0e25c9526090c81606706256158098407b1f007073106a1a840701e0310d1d86a1985a14840588261e87024082c0c05986c151bc1097c7c99c1ca61386e1682e1c09020761586a18856128420987a1c09020b09016266190570502e1c61041c7f07318621985a1584a108261e87024082c1521b0641482c0887c1c0e86684024c25c1721415c1484053042089fc7c0e26707380021819c1884053042701c27f1f03895c1ce2900309086c1885c1584410992549c0708227f1f1040e007075086214841010040c621885210824000819846709583a0d80c625d9c2081e6120e836032097671842089583a0d80c86158425c0c20a0e836032186610972560e836031d862548207a0e836031d850799c61b840320e8360325846709783a0d80c6619852559c0320e8360321866101ee140c83a0d80c8a1984c1c9502c5c130287ca12670780c729e21a101d1185c10a187c972670780c821a8425c820578702408201b255852671fc38621b85608148678702c7002052130420b022640ec1e032919e1818e14090510000d9fe1d0e020c61b8425415e1c090207c111c25c95c1e031a8505c14078a161099c7f0e2428a14144109ca180b2840c2668240f8747d0e3e850791ca728603107a1d0347d0e208c218032840025f0718a127082a121f26600c1e03240021b068109cc709503b0780ca25600a1d040441418a1e1a9c60a1f8030780c861495044148029f07f042099218952148720c1609814258287c418030780c6618990600905200a7f042099218952148720c260588061868028741011050700085c1484c1082c089903b0780cb00086213048709703895c1e03281106200a1d85c10141c002188510082c080803b0780ca060148028761b040447a1a85058828345a158605814834509505a16040091983472101b2549921f1f07f0e038909286a160d05a871831a15862720d05a871c3945c1cc110283515a1c80d014610972571fc38725d86264030030718411018400c00c1c600085c1484c109703899c1e03280021b06213042731c03895c1e032c86c1885c141cc1087c1c9fc7c140210e3486214418030780c60a086c1885c148321f0747c99254140389c2080140150a014026a727386a17842840ca0903e1d1f439021885210408030780c741a86412842551ca700c41e8740d1f43882389707095a10828340fe1c08243c25ca161b1fc38621418050970309921f1f07f0e288606c142709521f1f07f0e038a2141ba709507b1fc38786f86257850ef870588209b0e2841802030c85104030030715841040300307160e6119c60a0080c683b866718460a0080c7839856119c61a0080c7839866119c802031a0e619856720080c68398661584802031a0e619856120080c6050280911926 else 0x207e1b85e110200022438721808c1c9700050c705473078371f6189805a0e2828412840700007d17455854610e2c2c05097870820789580f8787e0e2d240910505685408020001f04584438c25f07004958020e1a86a140945400264162710e2405e1904a111ca700087c950220e2c82e1b8505811e1c016100925860630725c958020e1c00a12042549fc7c9903b0725862871f25f07142d015848118280a1f2650ec1e032c312849c60a022658487e0dc1e032c27818a12700b6118280a1f0210ec1e0334a1c09842671fc1c66101ee1b850338467203e1e1f838b01904a10a140a8247c9983b0740cb0008406f042549fc7c9903b072818c10a187303c7d86c3895c1ca2191bc1095c7c99c1c7a180b870976131f25707228602f8440a82a140947d0dc1d032c8646f04c7ca125f071c0021418c168481082c089fc7c9903b0736026198561d0e04584024800086a120425c098709fc7c9503b0731ad0b88261e0d67c1943811243225c18c1586a0b022671fc1ca41a86416850109940a820251f0220ec1d033986208970bb87004091d8661384031874389725416024a20a0e615840458700409220261584065874381102480b406612046721c80c9543890c60525d9c8708207984834909c976721c612032550e20316160561204070970308280c08438c08586015848101c25e0343895283261a06256050101c2081e80c08438c06f0425f03c7d85c3899c1c92141bc1095c7c99c1c7a16022858407b1f26707201701a8541284008a147e0e2670740cc20b85e1c20058091a850791ca72860310d1c002101bc109527f1f2640ec1ca21305c1c11c380b1b1c61097c7c95c1c609d06a1904a1009008a147d0dc1d033186c1985c148280987c1d0e06584024c21586c1a840b987c1d0e06495058093005412844729c25d0383895248646f04c7ca125f071e020c4090c0021705a120425e020309fc7c9903b0734002181bc1a848109cc709fc7c9503b073602e1b85a0b8761219c380925852142425c1be1a9cc731f257072c1421b062170580887c1c0e86584024c0910626505a14042700202d1f4370740cd21b062138421f0703a1925498024b214a7093070471f2549b2106a1905a14042551ca700c434a29c2721b0607087c1c9fc7c950389ba10d29ca4046840745e1b85413840240c47d0d2386e1684a0b87024081c00217052101bc10978080c27f1f2640ec1cec1f1f0589761050008621018c10098709727f1f03895c1cd884a7074321b86a1484e1282e1c09020900c200009921a19c189521615c158441009872020304027f1f0200ec1d7c0016e1a19c1b85857050261c8080cc0f1f6130ec1d125c110743e1b8500387434202540f05801088b41685a100202d1f0220ec1d03281b25c99e1f1f6170e1d840578520b8727c0e044))) else (if j<17 then (if j<16 then 0x20e2506a1905a148486502a08098360ea1cca1a85a702ba100f0020e2041619856111b285878351f264ae1b850599ca103003c7619856109c004001a1c2640d03c3015866159c022840300d1e1c619856111f024301c2ca1204619852101661c0d243409c160350261c62c89c07186615842658261c09289b45416a10140018367c8619856728461c0d03c70d1150500fa100e0b000e1d8367cb0009c071860880be118261587024b0202c61915616842118703491058b0200e0d02705987035150510228006158446c996098702481061c2840b6118261e0d0891f281900906217052130487087c1e0d03c08341541a8621504a101c41e878340f020c41917e11158360e86687200221b06217050521c21f078340f020c05106a1905a148407107a1e0d03c083286a1515044168346e182ee141604684034741a86416854128440907a1c09020b0b8972ae0d1386e12210b80d168545420a108206411834821b06217052130427087c1c9fc7c0c020d087850801103452849c2640b11866149c00400161c6140b47c090c0600b06c1704c1f1f03001202d0a81b67082255866178466603e1e1f838e20a8502c018345a1a8505811a12878340f0060e291961a866168561284a1e0d2428c1b05c100f00061040f000321906c1704873070340f208541786a1115a1f070340f2686c1a85c141687184a1f070340f2dad6111b609878349947c82718661022004001a1c6198447c090c0661584270010005871856111f024301985854000801667e0e1d866149c61307004001f866109cc1c010006619856109cc1c010007c1c018020e1186a1985a1584a108221e0d020a6168502d82a080921e0d020961a8621584a1182a080921e0d020b09305047078340f0060e2106a1905a1504a101c2080c000082c86616856128460a8221e0d020a209866158403187004092095070204008303c1667c809585815866721c0d0148098480e0ea1cd0958581434072158080280e0ea1cb0c98681985814140720280e0ea1cb41a86416854128440a8202507a1d0347e0e0209c410e80b86e1584e100ce1f0e08016024ce1b8585584e100c438200590d298561a1505a028038783886161508202803878387614348541680a00e1e0e201441a864168507000004086120e2c1421885c1c01800088388619850a99c0302c80f8787e0e2906a1904a101c0000845787614a21884c1c95800088387064852130700600020701905a1504a1102a080087c99020ba18866158461c0d03c703097254a7102c064976708207b856100b66603e1e1f838e41a86416854729ca1082030000220e3097619850558461d9f06411030822c160790e25d841506a1905a149ca100100008838a25c186199ca0b078020e20310641602c425c9ca1082c1c9580008838906485273070060 else 0x1000e260143c2706f06c1e0d87c16455852585a1584a1182a0987022878349f464c041050110702e0e05872712c0c919c1b058361f0584105098300c8383005a0d140fc1b0526c98058008388e1b8541384c0907e1c22c3809282541a8641685870148348105860258460822000709505a1504a111900a0d21866119c0b00c25603e1e1f838a0a104a101c41e878341f45d188380f338625785047840c00d1c090741961985a1c116120d24110a01941a8645505856850240c41e878342207d1b6120e03d40241d61984a1c210ba0d201d6198561021a1c190460d26870643005a0d1687e1985610870c20d1c090778660a870858483480c40b08582a1c196198483496140b60809a1c116120d2085c1484c1087c1c0c87d86038998549b3505a178441e8707d1946e15030a21b06217052731c21f070321f6100e85414381441a86416854729c41e8707e156100c35ad61182066870460d1c0e21b06217052130421f0787e150580c3506a1905a1504a1107a1c1f856020580c368761b8421c3083460858406582a1c118347839850799c6198727c150d00c2a0e054270304839866159c61c9f05584030943986c198407987c1c9f87c150580c3185a158402e870641683486198560809a1c196120d202207c3409c16c1c0d85414808ae1828e1c1e03d0e190e87d856119c61c170d00c249f83985e119c61e0d03c170d1082d0e87d866119c61c150ac0c260e619846700c61e0d0549f0ad082dad87e0e6119c61e0d80c9f0550e61434350e87d860799c61c2b6100c260e61985671870309f0ad84420a0b21f839856199c02e0d80c4003d0e05d843827838170541e150e87d86611870780c1e1f0540d8342e0580f1c9f83b866119ce1c1e03d08249902c2200040559c834400b8160b070b21f8398561009836031040f438170d0d03c2c87e0e619856100905d878360327d0e0542b402c87e0e6181561409836031040f4382b610e0b00f6158661041100170d000282c61984104400542b0030e25866158400400142c61985104400ad840030e24006109ce140b60b870248619856119c61c4003d0e2006416854128441e8703c08264a00b05c1307c7c0c4549b2649a1705c100005c9b26476180b60809616870642e8349a1684a700005c3403e0e2005e1904a109c8540fe1c082517066870c60d1786a129c0542b03c008388a1786612150c00f1a85023866119c8540d1c2ca1605467866121561c0d244187099865856100b61e0d0891f2e85e19846721561c0d03c8a1617e189803a150038760d9f28080b2858158461c0d85e158aca1061c6198446009285878342247cb00885c160421f078340f02186264b21004c17078371f6189805a0e2906a1905a14162728441e878340f0220e3706c159cc7307c7c0c0060e248401306c149b260160) else (if j<18 then 0x707486c181c21e0d87c402540e26e84088d10d154168508104a12028360e264913200615846718680e871c4546506a1833412842720d83a158acc2578527c1620f870700f02c90d51941a8645505a16840120d8381630862109cc1c95800081f86e16842081421f8702408242e20e871060e25c952ac80e506a1904a11150720283687281cc1b84c1c9546498024827f84e1c972600918110e41941a8645505a14840241c80a0da1ce020006198467203a1c727e210b81d1086e1a85e108205487e1c09020a4168541284e180905a0da1c9408970640b1008001866159c80e871c95e142006483e1c1c02c8020006198561203a1c78389502c1c03e00a7c7021ad6119c60a03a1c746434054148398200e1c8029f280741417e11198560d1c0741a86416852111ca700c834a61a19614956101683a008700f020b01d06a1904a13850301683490218280e871082e1895e1411e100903c0027ca81d850799c03186054348349a1e0705c1509e0d1a07619856700c05584834821e07619840781505a0d2185e119c0320da1c170d1082417610156720da1c2b42086b68781d8467015614348349619856700c836870ad8442090302ca1e0761586670176120d2827a1e0705d9c055856120d268761b856120d0c1081c150f60da1c2e0582c1c0c0b28781d85610170d20d242ca1e0761985610170542b834a0302ca1e07618156142b6120d298621985a1584a119ca7187a1e0d03c083586a1984a119ca7187022878358527cc06d850601402e0e03c098021c0229f3186a1985a159ca7187022878358427cc0509526487c7c1fc380e2186a1985a1584a109c61e8727c0c020ca1915a1684a1e0d0899c4090e2818e1416e1c83038116109f2586085840620e03c098021c48408a7cc618a125f1fc38511022000081385e138720c9f038996191726ca4168541284008000211921856101b0a600a7e02839172517610184559c8029f61602838a06f86e158405828e1c8327c0e26014300f6181b455858540967200a7d8480a0e37840738720c0e25c956149827ca270992182921414210090a88720c9f0b0d6189961615610160260e8000f298525d8406c0f8029f8720e020a6141e67186e17840319980f8787e0e328621785e109c06487e1e9f030082f86e178400409000081c19214842730703200020827d85e1784e1e0d2640f05c9b288243a8502e87004091c124150441e1702e0e26491249c61705c120d87c412641726ca6170405f078361f2651526c946686a168403401a1e0d0891c608b03c22003871186a1985a1584a108261e87024082c2f0cd04a109c00e8707e171060e8562b358421185a140b60a8261e87024ae1b852702221f87a7c0c02284298561a8621584a1182a0987a1c09020c6100b08800102c2170561a848109c21e0d87c99 else (if j<19 then 0xa1684a700c004001c3061985a1016035871d19262840580060d9f1d8502e8461c0d03c60b81102c0ea100f0018367f872a060c00d61c481119034ab0580f19866140c8640005a0e1c08001856199c6098480e872686219856100161c0d1c08003866718460a03a1c841a8641685412844729c41e8740d1f83808383901416046038380ea1c88003961a060158481016870028660383a87382461605044028720383a872585e1a1905a0083860558661584872190580c8020e29850541186584032008388a1886615840c00f1a85082840440da1c1903c01838a020006158460a03a1c741a86416854128427002000082b86e178400022438621885213070320002074c42341685412840001f4649746d0e301c464161040915320c90606686416854700007d180510e3686a140c00095058824388e1b8505a840c00f180241a86416854729c00014020aa1b84e1c0f2640c020745785044280510000f8767c24438ba1885e149c0678703c0c022842886616856128461e8767e9f2640c020c61586a18856128427187a1d9fa7c0c020d27c4102c0f420091984e1b85a738703c09030082586a1985a149c61e8767e9f03008610c41a194140941e0d4601403c012985e158408387024081d86e19840cf87024081dad0b4338110261e0381d9f87c99438913786e178702584141421885273070320002080c6050120702d0e058709e0681e1f0581e4550e6109e1b8561384434081b86e1584e1187e1c09020826786457850581002500e1c0f020b61b85e138727c282640e45c9b28192703d27c280502403898610a27c86214842702c21d0d67c99100080382e058f2178521384e1c9f02499030082a85c15844109987307c7c170d0a07484c101c21e0d87c400389725498088d41507024992c4561a006118261603a1c741a8601504e1107a1c0983a15058be1b85a738727c0903008a109464150510e00c4103c22202c2170500887c1c9fc7c9903898a10c8b032c158626707c7c142609e1b854138441f870880c2106a1905a149980907a1c090220ea10c212854119cc7307c7c1e854142806416854128441e8747e9f0320e26491350641d1f0321589c641885c149cc7087c1c9fc7c0c03a15050d41a864168501107a1d1fa7c0c838163085c1484c1087c1c9fc7c0c2640e8549b341421b062170587087c1c9fc7c0c0200e855843f06c170705b1f612150308419054128426507024168089c1b07c7c1e05215610721906c17040d307c7c9905491030b21104c1b05c1f1f05416030921985a1584a119ca720d020921d86a1984a11156729c83490580b0986a1985a14840219ca720d241cc1b05c1c1625119024861a8661685612842720d02094543d61284a1e0d4090e2185417078361f0581126c8020006198560a03a1c727f86e17870589b024 else 0x8c0081984267070047618178008606585a1002c1c0c28a7800842570707862b52d8028425499c1c70d800a10952098708801209745c86616072646286006188580c9518130018425482c1c1e004825d1721985c1e1f03899201d6198502e87464621817095066140c8360e464907586614970460e02d19208605d066140c4646291866141561d9f04416030822984c1c0100046140ba100161c0d1885e1808c1c9500060c42e0591c61c0d1a86)))))
def mo255H10 (j : Nat) : Nat := (if j<2 then (if j<1 then 0x1a968000000000000003c6651ad0a0c0000acd80000428c6f000000000000000000000000001754882f800052d40002d324db1ecc7a494000020183c6e65f4946d550000000000061878b680003c5380000000000212800000000000340971f40000634244980000000d04832e8000000000000007d780000000000035963aa040c00000000c9ee177189c8000000061280000000a37138f80000000813966962650000e46035e40000000f9983668406711eb0d9e4ff28e3d0359c1e5b800030b550a9c55000000000001c6d6cf31a3e1a0924900000000000000010edc84d000080f74bb8cc700000000000115c12f2e008000790d0000000000004337a5600000000000000187fc000601e84a6c7c5e3e80000001a724000000024160002013800000013348d191ddb91080000000000000010037c5d00000001105000000000001a1980000000843c489089e309500000000000384742d200000005d3c117a88dfc03611d2caff1f38f4800011e00001cf92d1d000026000000000088000000005d7fb30a000000059b20000000369b0000000061d74bb710e31060002a3f0000c38206cde85a953bbeb68858eec09edb6e7654000000094b2000000000002937a32400000000000a53c00000000000000000050900000000008fc874f381264000000000000000000000000000331800021cb0000812f6dc80000000000000000000000000172600000000e2340000000000040a9c5504cec14156e0000000000000002411000071db683b69f518d347200000000000e4ab452f4388000000000000003d23c47e000000065ce1826000247b38ff822200020433828db1602c400069c8229b5401ce18000a05600000c70000e2032113857000000000003c8c0000319e49588e280006959659d00e000051ca000000001da42a4000361d8000000043ee8ad65bf318230a54e5264ba1b5390c00000007415a6180006968f3bc00032cc00000000000000000000000000000000000060000000400800006000008008000000020000080000000401804000014018010060100100a00e004010010040140080200200000000006000000040060000180000000c0000000200c000040000040000000a01800001006004038060000000080300001c0000001a0000200a002000008030040000100000400c0000000800c0000000002000004012010028050000300080000000804000006018000070080040200200201000001004010030040000040000300000401001004000038010000100000000400402007002004040060000000080a00800400000000000000000020000180000001c00002004000038070000180000300000400001002000000010040000080500001001803002010008000000000180200c0140180000201c0000000e00801000 else 0x742d83f600000003cddd1bbc069287b8fc5afd81204b20000b3fbf4e8000000000000003021d8df21bc0001010ca4b000020008f6000000000000000000000000003e64a06f32d853c5d100000000000000000e5f000180740000000000000000000000000000008d651d7f286000000028d7742f41a287bd5289201553800000007bd550c400078d3abc0e2d800069324354b534ac801f80000000000000000000000166c80000000000000000000000000301ac938000000016d800009238c6fa89141700000000270919120001d44c000000000000003d238000acbc49440007df0000102fe2fc2a1a0001a6a0cc500002478000000020d9bc2244332e9d229b44ea7dc0000000000183208d13935c2df81e90228000000000000004e31000147ac00055b2abe400000004055121266ad51768fe544c867400038e3b42302d26219898000000012c780001ae822940000000aa4c0000000545600000002cbc506292360003698aa54000000000006840940bd95011780000001a0e8af08c7ba02e0000000058d00000228000000034208357478800000000002b0800000001e16c0000000120534c80000000000019680c9cc30000042aec8a0000426706efcfd5e30000000000000000000000000000d7dc450000000059c20000c090ccf720c0000c351c70146c73f80001c50b0f90001e58ee20d0bb00000001024f4f583b081640000000b9b400000000000580a00024603dfae1cc00000004982bada42980003018f102000000000000000000000000000000a6918e9685300000000000094e0000c4d0000157b000017614c780000ca5b2ae8e80108ab2ee310000592e000000000001192000000000000000000000000000000000106200100000f282000000040f40001d31586e58eab3de0002874e60b000124b06d700000000000364b29cf01d883c800028cda11f128400078c200000220cd0e9ea62a2000111b0000000026f4501000043e684af6b65981022a63d79115c39000146454ca802c62e60000000081f507c0000000117d0000000000032040000000000000000000000000000000000000000000005c4a00000007238205c00024cfd5865af9080c000000000000000000000000000000000303b000000036b7aa4d343200022bd0000ec03c69a60fcc2bf42a000000018310000000000000000001e81d2458000c3e1394c0000000043000000000000000000000000000d206284c2ff0000000101c8c00800000000000000000072092659858242f21700000000000000000003427a0ef5c18f81bd315520849000008a33a06000122f24828000e0060001adb00000001026c00010e429e8e5b680a8000e875a0fc00008adf186c98f8ccba1f21241671f150000000000000000000000000000da000041ce546400000000) else (if j<3 then 0x70b9e5c622f00000000000000000008ae200034f28000000000008db0000631800000dd0000000000000004927000006bc10480000000220800038a850c755aeec8c8ac0000000000000780000c87000000000000428c00000000001c275cf0b867000000000002dde00000000000000000000001cb0ee420000000000000000001a1fc00049898a8e000000000000000000109e8000110fe02800068910000b16e020a8b2c3dc00038357121000006dc00054db000000038f6a81000000002c4480000000e91280d963272b200000000000c4b1d40aab98000829822be0b00000000000000000000a96451446f7d957000000008134514000148ea40280000000e25000048f3839d349612135e218b9d876414dd43000199040000000000041af428800000000000cf3800000004158000120f0000a4dc0000000a4b60000c51118b0000625c0006861000000016c4f910745a0001b1180000000000289682169328090684c8000109800000002cc1581a000151a0000b14800004d880000000e7a00005dda00000003887800023eac1f800029a7d06c00008638000000000000000000101702a4000595b542400030ee513b2466a0cc0c2000000000480000211a949c81c12b84ccda01e895c8c18000e2bfe15feefea3b94c31372cb28000a01c0000000000019f800000000000baee75c872280001b4700dc000000011c2000389d000000d3c0e7b23b82300000003adae8c50000898208bb9cc000110b8000000000000001271800000001758cd864bc3a7e38a5b1000000001683400000009b7c83a000000000000000000000000000000303999c70000000252e000000005757cea80000001e46711280000001874450d80007a1800000000000000000018f025bd0001204400025224b102180000396b000185140002cea3918493c00010c6829494578bd80000000000000000009196000000000005c26e7522d7c4e8a06525214a3a02d0000000002c000000000000000000003400000c0a117500000000000651b91160000000517a00000002ab4302f23a6b2d0000719b1ba981e603680000000a5740006d38538c1202a228000000000000000000f47bb8500000000000000000000000625e6258e72d85e00000001caf0000000113ea0f1000000000000c6c00000000421440209e400000002307688e91ac0001c4fb05d0000c6680000000000000006948000000020f04598000000000000000000f119513d921800014000001add0000000012cc00000000c3d077dc9898db04bc614a6ee80000001e8d44cc11720000000245b8000000000000000000300e0003e9bb09a0001e41903b75a7827c000092e80008a9e0001a190a4c00000001330583843f20002832304e224784994dfca5f82260000000656e3ba400006a300ebb8c00000 else 0x659a85f0000e0114168a1620ca000000000000000000106a40000000000143ea483d962c481d82a83d80006a7600008d70000000000038dc9080000000020a48000b0ee0003c0b000000000002b0b000093ac4540e5701585a7ba4c0000607dc869759a52280007214000370bc580fa436349e47800023ec0000000000000000000000000000000000000684292fd08b000019a3000100940948000000000000000000d0a00000000000068a80003f0a80000001892800068ee78d205080000000708c000000069d90000a8aeaf8ba1d39acc3880007a0880680000000000053fd29270ba00004ace00000000000117200020ce00001aa324dac3e00000000000000048ce000183e3804800011fa642d8e200000000255800000000000b767068f8130000000000000000000000000072460000000000000000001f11c0000a310000000348b2140000125100000000000000000000000d0dc00008aaf17ce254a5ff3317019b4a400000004c356454000191180000000d414432c9cd))
def mo255D11 (j : Nat) : Nat := (if j<3 then (if j<1 then 0xfff20143ffd76443ff61910ffd30483ff50120ffd50483ff58120ffd7558bff5d162ffd5458bff54d62ffd4358bff5c120ffd31483ff5d952ffd7354bff58d52ffd4354bff10d52ffd41483ff54520ffd764cbff58520ffd754cbff59532ffd71483ff21132ffd744cbff59132ffd544cbff5cd32ffd634cbff54d32ffd434cbff10d20ffd43483ff54d20ffd655c3ff55170ffc835c3ff58d20ffd635c3ff54d70ffd435c3ff5cd20ffd625c3ff54970ffd425c3ff4c970ffc815c3ff58570ffd54483ff5d560ffc84583ff5d160ffd64483ff55160ffd74483ff54d60ffd43583ff5c960ffd65483ff54960ffd42583ff4c960ffc81583ff5c560ffd724c3ff5c160ffd76483ff61d50ffd410c3ff61950ffd510c3ff5d950ffd710c3ff61150ffc84543ff5d150ffd64543ff60d50ffc83543ff5cd50ffd63543ff59410ffd43543ff10d50ffd82543ff5c950ffd62543ff55030ffd42543ff4c950ffd81543ff20550ffd71543ff58550ffd740c3ff5c150ffd60543ff61d40ffd750c3ff61940ffd73043ff5d940ffd85503ff58c10ffd75503ff59540ffd74503ff59140ffd53043ff60d40ffc83503ff5cd40ffd63503ff54d40ffc43043ff50130ffd504c3ff5c940ffd62503ff54940ffd42503ff58130ffd32503ff60540ffc81503ff5c540ffd61503ff54540ffd31503ff5c140ffd704c3ff58140ffd50503ff4c530ffd414c3ff54530ffd43043ff58530ffd65103ff5c530ffd63103ff54c40ffc814c3ff60530ffd61103ff54440ffd31103ff61d30ffd324c3ff61930ffd424c3ff5d930ffd854c3ff54930ffd754c3ff59530ffd844c3ff58930ffc844c3ff5d130ffd644c3ff55130ffd734c3ff58d30ffd534c3ff50d30ffd824c3ff55140ffd76042ff61130bfd864c2ff61d30fdd324c2ff60440bfd82102ff60c40bfd85102ff61840bfd87103fe54140fdd314c3fe5c140fbd42503fe58130f7d75597fe54130efc865ceff61c30bfd87596ff61830bfd85502ff61430bfd86502ff61d40bfd840c2ff60c10f7d51543df54950bfd820c3df54d50bfd810c2ff61410f7d75542ff61950bfd87542ff61d20bfd86483fe5c160bfd85483bf58560efd62582ff61120efd63583bf59160bfd87582ff60d20dfd725c37f5cd70fed424cbfb54932fed624cbfb4c920bfd844caff61532bfd864caff61d32bfd8654bfb48520fed7258aff61d62bfd8010eff60810bfd8210eff61443bfd86442ff61843fdd5350eff61510fdd7350fdf21543bfd83442ff61543bfd8650fdf59553bfd8654eff61d53bfd82443fb20910fdd7358fbf59563bfd8758f7f5d573ff9404437f5d973ff920442ff61810bfd854c3ef50d40bf5810c2df61410bed820c2ef61030bdd83042df61430afd860c27f61c30afd86102fb60810bed8210ebf61810 else (if j<2 then 0x44101c1a008716190a80c3e200706f0c18c2a123902c39c060207c1c17c3063091c0ac0b0e60142f1c1261822158161c90e07c1d86820442b02c392050b87c1c18c2c103302c39403c3617080043c387c36170800870a060b8f308214ce1c70be1908160ac0b0e387c1c1bc20642b02c391051085f0a840cc0b0e40703386c2e11380d0061c90286f08190ac0b0e38030d85c200d0e30702f860c61006150fe1c1c852c32150e00c3f86c285a05870d861090e381c020a8370d85c220b0f0e2b0c15c2e101a020761c8c3614061fc383860061b0b840a80c040e230b86c20342a020061c1c4e1b0b840187f0e0e1c4986c28342a020061c1c489f0d84068540400c38389c2e101a190a8080187071384c30342a190e0030e0e240600c3617081f070f85c361032150e0081a032708170a80c3f87070ffadff277da6fa7bf377e35fbf0f6ebec0fd447a3af35be4a7c64f845f001de83b8e76aaeccbd85fae9754ee971d0f79e5f347e5f3caaf901f16de23fc2b78226fc0de9dbbdf742ee1cdb79b597682ec9cd879af4f5b56b13d579a94f4f9e993d231a32b427e7c2cec59be733ae60ccadb93cb2406420c7278bf712ae1dac2e383b7034dfdcbe8d7ac2f285e02bb45740ee565c4cb7eb6da2d8d5ac3b4c7680eccd5955b16d615abf25784addd5a3aaf7d5a1aa9553cea2a5406a7294cf696a527da41746d289cd0eba10540d27ea4f7d9e5f3b627334e0f9b2934f66614c4798052e425984aa3949927fa4d84962919921223f8c7768e3f1b8e34ac6358bcf15b2286447f87e50e02175426683fb05c209140958034fe11f803e7c7c14f619e813c8777f4ee45d9d3ac8749ae76dcbdb8ee70e6e04dbd0b70b6d20d855acd35286948d05d9ce330f64f2c8418dcb1356198c1b17fd2f645e3ebb21726adc05a8ab371630abdd56a0ab3151b29c4526ea2f1429a7c64e729a6930225ad4a2e924d210a3a646568ae5131220243688575083209440327f08fb59f1d3d9e7a04f229dee3b64756ce8f9cbf39067068dc69b123564696ccf49977320a6270c2297b82ec25b50b2c95f02b2054e4a71149428564f749c7933825d44a4c92711f72352454888690bf20d040687e60f751e3c3b407458e461c0237146a98cfc193830cc5e98b6a16262a1851789e112f023d0441082b0fa81dd039786fc0d6e19c831205d60afe14e827f049508220ec41b1832705b20a0811e81e6031e04e0070809c008a0003ff5d520ffd82503ff50d40ffd30443ff50110ffd50443ff5d563ffd60443ff5d163ffd70443ff61d53ffc43443ff50d10ffd7654fff54d10ffd8454fff5d153ffd6454fff5cd53ffd8254fff60553ffd8054fff61943ffd63443ff5d943ffd8550fff5cd10ffd83443ff59543ffd7350fff59510ffd6350fff54d43ffd85443ff60943ffd8050 else 0x793986c2e12040d4f830758704438f16115382a8e05f0d840a8ac1a00871a15c3035329c2261c5c1616438b0c8b0622006ac53f1fc2e1139870b8d21c78b04286428153e2a8fe1139870b854570e3c58320a8082c0d5927e3f86c2a730e3415a121c8a141a174f830591fc2e113202c3a182a3487200c1647c5d870b8544f0e25380d43c1d3e0c8fe1b0a16010d02a841ec390072101a9f1647f0d85c383040150b438e0f2705986c2e10180d8121c110e31040d4f8263f86c28730e19172121c68642a1b56a090c85c2266071fc3c38d0c85408030fe1b0b844e40b0f0e30381fc20bb0e170c2161c48143f85c261c2e1b0ca1a1c521c0f86c2e101a00871015c3617081c0c8030e0e240419c3617081c01a1c1c48540a04c3034322e0b07001870718151900b0d850686430840e0030e0e370d840c86038150061c1c480b080d1086c3800c383890c8470c2ec2a102d87203e0ec3617080d004388430184385088644187230d85c221c1b0e190a050be1b082e0ac0b0e4a1842990bc570e3054698615e1508168161c90de1032178161c602a1b08150d8640400c3838a0f83a08190ae1c60e217080d0b85430020061c1c58642a020b00c3f86c2c7029870d861090e3c32240e61b0a0d0d85508020061c1c68183f848e61c2e18428561c50083f841a61c421b4343890ce1b0b84068802a16010030e0e303215160730d85c2208061fc3838c0f83b0c9c81058280d0d860010e310e07c327036180b0501a0087161cc30570b840100d0e0e241c020aa702c0d1261b0a114161c3618871e19c36170815010030e0e24321502e1838020d8602c140187f0e0e421e174e4082c0d18e153214c3a18310e342e1c0107f0c11c386e08158716020fe160814c38610c1987140210e1437840c834070e243817c3063080d0a80e1c4818798410a642f15c39005c3070041b0c058280d01c38b076101a170c054010e200e18c205c1a150043880161b0b844e07c1a03871202c20bb0e170c0561c40390d844e61c2e180ac3890fe130e1b0c8561c38730d85c22081b0701c3890386f08210c834010e200421c2e130e170d8661c480b0d85c203604031c082b1a09c2c0d8100c80285f0c2bc20541b02019386c2e11040e0680e1c40130d85c241c1b02019005c307036180b0360403243817c3063080d0ac0806481708170d8641b0201901c0de1a080d0a80c70761b0b840000e1c3818420d4c85e2a031c1c1bc20642a0318062c0fe1b0b84c38642a1c01238c0e00b0d85c200c3e0e439205c30642a0dc207004870194031203833860ae15081c0161cb0e6100e0d0b8602a0042c38a0f83833860aa1431840e00b0e58644811c30bb0a848e61c90c8540b860e0082c14038343618002121c7a184017c284708198e61c9420830c2ec2c7205872032150e61b0b8)) else (if j<4 then 0x18104542d028061e1c4098328582e180902088b82c9c4381c1a00872026434182b1c15c1068270b2081a00871c870c0030e110a022090e270c0e0d8602c140009a1c83c3a7e0868650b05430f022340043890a8f05c2b0043860c85e2a20814030f0e210c0642c1401871e044680e2a08040061c782e158388c220868304f884320f1d61c2208871a19428610d150b40a0187871486c2619040d1827c120f1d61c422e04438f0ca142e1b4e2192f85c203105038fe1e1c7ab45a824fc7f0895c38650a11871819c2e19040d1827c5c09078eb0e11420221c80842a1853a730c85c203105038fe1e1c70c438824f82e3e16c3885090e2c2a27410581aa74fc7f0d874a8850a84871e208147c1387108c61c4218428206a7c131fc36103987428645d0e3c3615522730d854203105038fe1e1c68670c84c2615040d1827c1609078eb0e08872019070352a82c361483870e0802c01871c17430190a214fc7f0b84c38652e11871c15138354e9f8fe1b0987108ba1c6090321c06a913f1fc36170e11172121c70642b860a2652b8401c0d38828fe1e1c70642a9c0e61b0b84010341e00c3838d0ae160b864e21004160683c01871a0ac1c790d0420810870b840c8441b0e2c8b84826190421170361c48d70b05c3071042e0b045080d871882049060586c2e103887038641b0e340a9c16473080d040030e1715838c0a8730d85c20c1040e06c38a0ce1b0b844121c1a41058241e00c38221c7864160e07e1b0b8404c7038004fc38d4102e058406904421100438a178550904c32081a41108b8010e302019434190b050e208160d208445c840043900ca142b05c36103802069041e00871a86036120882810341e00c3884220e370b05422710c200683c01870b8d01c6e12098642a081a0f0061c422e071819c2c170c1c422081a0f0061c222e071c1f07031382c8e61b0b84010342a0f00438f160a032154e0730d85c24081a00871a2c080570b05c32700416068d0568400438f0c85508160587b0d8504e10188281c7f0f0e40589c17473080d0b85456008716860d85632850b4030f0e2458120ce160a8642270400d0b8d0010e384215174650a168e03201878716860dc645c848e0320187871415c30ab0b84070030e2c41a7e1c60543c444e0b30d85c24090e0d060030e088720210ac645c00c3c3870da143119c30580187871385428570884c3466382e0b0030f0e350a9c4c8670b8406a7c183ac385c6808871e074e030591cc361708020a834010e35382ec227c2e151d61c560887162c0ca703986c2e12048703834010e355a2d4e27c551f4361133870aa14690e382a9c0b61b0a0d4f8d0183ac38ad0808871e2c1ae160b864e008681615a101a00871c19160c5381606ac53f1fc2e1d32860ba121c809d389f0f0aa3e16c385d0a84871815420 else (if j<5 then 0x486c0ca0c8d50b051e41e3f0e4b844690d819a158fc38782e13c360640d60b860200e0f1f87044561686c0cd0d8620b8601c1e3f0e4ca54289c414360679009082c3617089c0000e1c52708e82c361508410f800070e2d5a2d4e2663886c247e0f0e1a0561b03390c414e21708824ba54000387161958894638582a702d1f83a661c860ba121b03444e9c0b470051f83c382e840ac36066a7142464121b0b844c87c00038718154ce182d8412a701b0201941958894638582a10411f83c382e3486c0cf128850c8502a7039848fc1e1c17158561b03416425190570b05c30082c038fc1e1c3415a121b03490a998e6102f1f83c382a34014360668ba391f83c382e151380a1b032d38168e61b0b1f83c3868154200a1b033b0b05c32123f070643840150b00a1b033a0b860a2652b8401c1e3e4100a710500871e03000642a840b0730d85c240d05078fc021c800c481b4285539038e6194f078fa107b0087202702a7e3e1bc3a1042178714324fc7f0e210c8d21c405f080d0d86b0e950c88e1c5054008610a10309c8e40d2ea783c7d2a8580439113a7e3f84c38f042178712191227e3f85c385c22348714840c8363f85c385c410e24321742c1437844e40e0f1f4ca192f00871e45424101a210b8021c40d50502c28f0220d00438941408238403884320d00438a11e160b048e0802e0d00438a1186f08210c8021c83c3a7e0c5a12083c1085c010e1c06320c86162b24140e0586c2a720f1f424021c88c40a864fc7f0e181085e1c505c1b860c6113838c3a642a1387183102a7e3f84c38f0421787141500219081882619050383c7d2aa142c021c8054649f8fe1b0e21170ae1c506400170da85628281c0b0b8483c7d32868043911227e3f870b8b82b0e21080206c7f0e17170561c490c0a84820841a170043890a8010c1b53a72388281a5e0f1f4aa1509008722354e470780d158021c404d0904c34085c87038841a0087189c8e0af08170a834010e2431840005c26158720f0e9f82960543212083c1085c010e245843c2c15089c1005c680d00438c02a120800c38f042170712190dc0e05844cc1e3ead43216010e353e181d61c22140443880ce150b868ac0840160061e1c5a7d0a3ac3844280887101b428622b860b408018787141916a7e3f8742844690e243217434544000c3c3884f860223ac3c10280887121b06a670c18c28ef0e040b09a1c6064091fc2e1c78311a438910a182a041e27e3f86c3a845c2b871a9f0c050758708c10110e2431860703436950d61c08164109a1c685c3285010f13f1fc2e1d2e111a438d0ac7f0e3c1709e1c386c2a9cc3211041e4ac0e3f8787180406c7f0d85c3844561687141b0c4170c0d8fa652a140d61d388200c38f4f80c318543844280887124342c141a111a0021c41150d06068b856008710 else 0x6400184e285628281c0b0b078fa650c8480439105a080386c2e10131c438361c5838058582a130904c30370e9f8f87012191705a1c9054102c4e61b0b844141c000e2c32014161b0b844e41c000e283618132730d8541210030700038c188193f1f47438308410a642f02c39a8610860269c42e1104974ac1c000e34629f8fa3a1c3cc208538178161cc0b86d38a100a090d85c22660e00071a854fe1d1c240c0441844170c144ca57080d83c3444014e20a010e3c00190aa102c1cc3617088283c36010e385a9f8fa3a1c114c856058728481b42855391cc329d050786a12010e393f87470903011060e198fc382f8518a706902c39424430153f1f474382f86172702b02c39c864285d3f1fc2e1d1d0e0a84418627d1c18088911a831d1c18088304902c3a7c843a7c4818088f51c3a19089f470b82f860b61238158161c127054008610a10309c8e25d4f0786a550b0087202d8227d1c2e8704708198e0560587350b864fa382c1115a101902c3824c0b8650b050de11390786a650c9780438e112730d85c2208010e204e044fe1d1c170b07884288208340ba7c2d1fc2e130e8e8705422190103120a8010c1b53a7238824bc1e1a9542a12010e400b044fe1d1c171703084209d3f86c2e1d1c110a858040c303618112730d85412100200871785c321308874fa38402e0b024188d419d85c321309874f8805c16048311c60081a20170581880c3a3890c86e05844cc1e1aad43216010e310c18112710b844125d2a00871684042730d851ea081a000714014161b0b844e034000e244c9cc3615048400834000e290c134e21708824ba541a000716450301e3f0e0c0842f0d819445424120f1f870f0421786c0cb0a9140f868fc38422e15c360659140f1f8705c5c1586c0c922a123f0e0b8b82b0d81929c508050486c2e11320d00038b200293986c2e11040001c38a0c8b40f1f87214223)))
def mo255H11 (j : Nat) : Nat := (if j<2 then (if j<1 then 0xfc46d0000639fb382b10f92c17281247f506d30a163c0014b000000005acd93247038135bd01ff06efc5c0360325d7ab15be59344f36400001452b2bc43e5e01c6202b81e23773804525fa112725a00fae92a100b9be7c150600e242d283af8fa51dde941c2990000000082e351a4f1163a87f47400000000311800002228bc6020c912ba30c2d1337421eb9be18dd366b042e29f92b3231cd2e0523d133300006ba8e973617c6380ac11f9b0f8f1000070220000f328417fc431ab5e0000d28502d4485942272badab8f000049974b0b2b0f22a10000f3ebb2e54a8eb88e6a12b138c4adb9bff289bbe0ba9b336d00009a0e78492485315d64766235f90303c270c570a66c100000000051e051e20000f42661070000000032bf51050464c9a373cecaa40000000012ed0000624483f5a251db4f4236d27b6454c136a388e3ed0000c9a974a613dc327710330352fabdb25ed27c505b025ba484d41c9c3110a871bc2c4998c7b384e3bc533013aca12db2c541db812150219211d321034222ae245bda2f60f0f31e19acda9261b0285471d212a69079b35ee14041ec60f43304d242614e938fa19e81ff8ad1031502d83399002b42c712b90264d22c12040000200004100401007000014030058010340140205e0021100b00100208c0486002e1d80000102004807800006000020000020140000c00e0580003a0060e82380100a2b00101800a010000360000280100100800c0c00900003c1a0160fc1040001a04a09c0b8200205641701f03001c07809010038260190000042884d03c0087684801a0001202e0500f001802040450008110120040001702a0040c0010000ac000010020140b817000008028060000000380f0461c4078810220401200003a004028020800d000812000074040070780240000101e0000204204c0001e0070060302301a0000b0000030200300000201433c2a823002028070020040c40100700e00800024002014508041160201100d0102840083601c0280080001a0340000500646c02010018018010010620240180906408c0f02100607c1a0040901fc0000105c0100302b04c5a80300800004c2100000e1a40700002003c008030100000201c016008118310120086a8062a2018098050a40800400013a0903a8630380001683a0340340001201e014080390000540f8051540800880b000058038001260d0010090b40900000921c02c3f0000000600784e058088140020420181687e16800c048070380001284e000048008700120000104100c000310000041f80102702c004028010000e40200001a0040001801e1d80401c0020380602101a0382300400000c000020100100002f04c0000600003a0080f8010020dc1591f01a018000660000a41901801c0200380000c0dc020180280100182a00805801802 else 0xc4960e2afaa2b0000e3da0000246b644313100000d189000089cd482fc487a48d61858492000030b760da516b4c596450a3cca3d2c20760e6000000005a6900000000a10e283e143589480000b2932c5502a500005a22f1757a98e468b131f06f348ab03bf0d80000eb812447604763c60a8b20f673a2292321e5588f80940000309a311ed2e2e26a0000d9900000d4287490001929507007b97700dc0000000082136462009cbc87cb8834343391a1ab8187f4600000e3f6f0bdfb9313fea2b59483b16900009c5a00003b37742aac18f2a40000000040ddb34741f5bb58007100000000a058a39ea18821d40000232300000000a0a50000000000008144723c2c1a21d7b0b6914d0000547e5297dc5200009126e3754c014acc009fd21f00009159924700000000000040f8f41de80ea8569a68ca4b000000002a07680300000000c43c705aaa86b8dc50230000abee9254b2bdec8ad22e201e3843e1498a0043a1f351dac820c1c0548a67f329b3f9743700005b225184540400000000f03a749e8beb0000a06bb00d22a31238aa3ae024c0a014aa30d00000e0ba42d33c40136a830970105014000064940000d47ac4196b1a43eea4393191100a0b40608b0000f3460000d08d8a91a18fc8852ad34a93c0ce6a10901509248055000090c8e15ed1a891736ad5342b9475e1a941a294111bdb646a5286809ef0c4e074e2ff43121493000072f0d0d21165f078a083c3f2d9f294a000001c3e041a7a6311798301128b31a70000fa2c0000000054a1a2ec58318092a3d9030c00000000cb3a0000730e10d4540db19823bb31e9000004135c98217bc415249c3429fa16f0b800002268907ea2a033b263f87a271c4531c7f161c2f861d9f2e1d1bd9438b0add39471fb19ebc174d37c403509c353b6831ab34f30ca62d720ec237173a5e987d17800003176c3bf30bfc16291b60000f3b872f2e15588d292600000a2faa065ead780e3000081520000b9ea1197f284000062ab748f32f40000000013b991df738d00005396000049dbd13a839722da024f88f61203691f93ddc465735f739200001c9b0000f03c00000000625940250000a307e091699e0000b42052b070f21313a216fa2193e0d2081c9a3b4c137bc1a3239c41b2c13c7481f3a8d9a4cb7b4ac67217d354b201b20da106636f6922cc46a29b9848a104b29a800470938a0953e2b250604c9aa0494f8be9544a00008c060000140ab47d2c1532e613cf21a01ac3cb8090e2628e2c075881c14c81dc5157a1e693d8000082180000418210f39124fb3e00005a960471897874880288b1c5f2b1c0050b1e40270000c461f400705df12ab1c0b4066036000000008b2e00c7b3b1723bf44ec2987427124d9aaf51c8132f81cb4059803f6c0a0000ba9a0000000033d482551479534c0000b3f) else (if j<3 then 0xf00f00004a0f1085000000004c0c84418339c01bb1b5003d8232e029000051de2246291532309acb00000000cbb100007b17d220309724958b75c40f00000000000082aa2a0bf1f0f8d45c3d51b7f02d000000008836f030a3436a896134f016f1905aa7000010a200000000e937405091309c3aac2a22ac243a5a05045e53dfc0fc916442cd91bb000020890000708f528fc0df523e11f2117e0000000000002883e9e123fb000073e3629c0000ec1600001326d146ca2ac183812013e131ccdc9c000060cb610850cd9c41c45863db6269f3e6205672cf0041b03ea2f983c8401131d01a953425e0707a94806322d1b985bb2789301ca6914fd4631b36b83d618c6064429ed2956ab4612298d07a0a2467e195f33a7073ba13f20c01b959d4a154a1f7c98b42f36c2f93e8fab3019b802abb3c3317c97d59d900008c50983cdc859976b8d3d0fd000000005b2cd3b4000042b4c076546c0000b3ab6886b117980912679282fb49b127000098923331d26df979f39de0ed8219f06280495a9d11b1f11dc06933dee3c42c1d0000b18b0000a928c270d2be03a4711a4053bbe858c860515037512e0000e0aa147010c3cbe11908b1dac469141672bb228ae4240497828c2ae63265e0a4280281d8199a239be22530026c2b52783b960c5e019fb94292ef3261947c4099f214f350c101c0481c8e435a93a9fa8acaac208a54a423aeaaa6619dd3343ab7b2b80376809521ae20d91129611c7c613066a805cc5b00009be603140000cb8ddb9213ea4bafcbefc32e48785001911434aed13eb0e07135a0bc49a534802224c10c335da308e8db9b09e14a719c41ac8b8700006b8e8a79291c434ac098d41ee04600005239911febae489138e21348525749202c0f13f10000ab940000c30600000000b0090000000000006c2760b59040f08742d950086bea9801a2a2b125734b43f3f3ef5b6173baaabbb91891ea2baa61e3a8fbcc37d4ac29a17aa2e356f23700000000711b000033d3445d82c3d473108e000000000000833c2c00843d51c1191ae45a00000000000000001373000002cb4168181594a771e10830e10a0000000049d068e0a05f9043f0abe3355193e3eca8e800000000000073852a4f01e47477335560a30000f98c3386e38b000029359141d0d5fc4250a90c4e549bc1f100009bb02456b2ea822bc368b1d6d39589e209ecb30a0000d2ad60865158ac4d5c4f382350fe0000f08441fdc2ca8a36323aa305f0cf0000000000000000025c933f520f02e9902002c2d0b2000090aec0fb0000290d318e10ef59677266e13d32765992a2fea3a3d95d8988827dec4a506ab8d1b3e7397b3c8f3311da03000031c4f97cfc47d41870be640bb1372405306cf1ef9381e0eb7a3de9cb00004322fac53c48a449eb86e9ae62f50000e9c0f8eafb5 else (if j<4 then 0xbc4a8f09600009894e0670b03d080a275d249113fcb1323a0680b2a083901e31f41f45a605139941b0b38215ce252304a9a11208272fdf1b3b23f9128c45751fc1b3d6223a2410000000093fa098fa3c9c07232cc40f13167001ad3f4d42f33af807c78fff349f04fe04ee8d7507b31c3a12392b7529113c14909ca7f5b6df387d2b67a9ffb156a8fc10b0000038a2000c271a0b0cc8600002052426c6845e4980000e34d7341943b1ab818fe091e70f90221ead6fa1f612f62b2f379a38cd1ee000071ad002c92e8892731c9920532a7441742df692fc27982c8ab3f835762de20316c969088f986c888607d5a0ca486f034f2fba1eb726fc233e390230b4166f966babe40d643f76c1720a76145c2d0f2434215822fd1097a509917393e0c3f0babc057f42328fd02963199340c42a9a2e4c851e0e5e47b9336e3a70000a3be02c47370aa540000e0e1db0e00003290b16a5832c3696231827fe361396eaca2c49600d180e86186b8e53229b37420af01aaabb411ca734e42d500004403a22da363d0eaf4100143e85fe37f5c398451b300538e6a57213b8c433245910251ed20172a0271bec3d1d20ea49d000000008c1902c688ec045531420132039ae28344423100244f2bf071b4014730ee83c50013a9a89a06e359637d50b3f1c25b854c440209e4465258448c644bfc3c39e4417ae8351c1b2409cb6031ba000060ff0000043f23c7a459d37ef933a4998489a3d732100177d1f80000e090720b942c7372cc4b08eed44d604d63ca00000000787cf006cb390000e9e74061fca7294092dbd4320000949a839892a80000000080e7e981fa5b00004b52d0ac60b4348b00000000e01d8a235436c3250000d2006c14000033e421bf3039718194076c51830f199961cd3ab5c8c44393342e7240cb2ffbe2249ff26e815f13d5f433a48234a9cb307c88917149063aa9815614227172e36cfc8bb09b0c56415a9c0bf327835c292e00000000b00321609445aa6e59b333fd2ab0f153aac028dd0000615b682c826b481b000092560000595f9a01000063200000000093b57a2690e900004a6a00005c08faab507ad1d312f722069a1472fce2c9f303686a7115a05e00000884000011a6000079b2f414000089c2f35800000000fb1f293f196224723068e478437a28078a5860b1599153ad82c05912ac5d630d9a42a4307292e21b926323785110521a14ab2044618ac383d853000011af53c36026b33d1aa8ea04ebdc4a351402e04500007b16000052870028031d88e9e9fc00000000920a0000c8dae3160000e09d8c8d61e86337198d916f4868a07f31f9f170000011a1f32d2113436ba10da02edabcc36500008151b33e5938127ac24a8c1ce16d73b0140e0000c1e7490f00000000f1f3733b6bed1c3bea340bb50000c9a70000cc53c340000 else 0xd02f63a6e440a08c249103b7f38900f5a0d7d1d1517dc0cc5a7811fa2c30fc1311fe9148d45fa24ba1962850dc4c4032907562f1443e02ce131983186a301a9052e74c1e8b8371c6904b93aaaca8c1924b6f09d3f2d2798a30d3b12b01cea0e4631b02dd50bb13f0627e429d6c2df0601234c018a28050b911b86119990c446603b3f12cf180e24cc8260401632c0000da48dc944453000c70f7d46f3bdf0000c2720103b1f63bdebac9a0c622d683d0094e32ebc2737345845c7226e294a36264a5607764a3c408121c0448e3fc8b259412711100005c5443d6305c53e9044c8954222ac353421d933843bdc44470de91632c90e41f0000846e928d921e43cb824823cd52dc308183325ca5932ab2533262a24ea2f61c5811cf2212536eb19a21d552eedaaa7b21f16c90c0130200002a776274e36764a228fca1943ab23a9c648ef16ed1a5dbe3d012682a30db2222000098f45bec332)))
def mo255D12 (j : Nat) : Nat := 0x2d0e0605841915872070085c7c9c3a181410561cb051c061f0e1785841902872c705c7c549c3a1816100a1cb1c271f240e868504028728107c3a1a1610700a1c919861585841c02872019147210085c541c7c3814340cd1c35028685071f0e040d032c721a1610087c1c38340ca1c21021f06858419870e2870085c7e181610561c38a1c021f868504870e20087e1a1610721c3888685840d191c00870e24707e1a16100a1c3888685840d150200870e24700c0a1a16101c7c0038a1c02868584070d000e261a16100c7e1c387c45712b35089651920f3b06a4bf153250414710bb1301c42301f000ffaedff597feb9ffd63ffaa7ff50ffe21ffd62ffaa5ff4cbfeb87fd60ffaa1ff503fe207fd30ff861ff483fe887fc10
def mo255H12 (j : Nat) : Nat := (if j<1 then 0x3aab00034dfbb64000000000000008fe32b0000d9dc0000001481000000000014c000010b400000000000000000292a8a200000002479b4534006020000a1d400041f0ee2f2240005bbc000000000000032ba315c000b354000000109a42e7c4600000004b34000b92800080ec00000034c5000020f0002a13b2df11363740000001621b2c626604a6ab63be4000435c0700000000000229000000000208000ab14000000000061810de0000a6d000000000028a9a3fe4be60b4000816800020c00000000000e1200001cad51c5456c370000000e1ac0000000000000000000000000000000ac140000367e1f000000000000000003464c0540007a592bb000000000000000000000fbcc0002aa1d1923282128124aa3c18f63732c92afb3940000000000000000000014d6f34630900000000000000000000072d80006a8612800000002b863180003b1e00012a652bc00000030350000044c10e86c330b45cd23e4eb000228fc090440000000081b9640000000000014cf71154c30000000000000064580005cc0000000144c000000000015210000000193400000010d2f49e6fb00026f5c3d80000aa4000c0e000093bf0360003cc10001c194c1d823000000041b40000002b110000000000240700010d40000000000000044c80000002c500003ab1c1380000000000c3a7d1200000005398000f38400024cdcf85331a950001d200000105c29c2d522908fd0003900e408926000250b000048d000092d0001a1091648dc000000000004620000000abf081ae437c1389f6471507304210ffb08da600000000000fbf7c1e0000200e45fadc00022c28b1a42c0000000a04000081e0000438800000000000000004000000000000000000a3cc14783ef39c0000003319a08000033c111fd8ac0000000000c43c000b12eea20000cd0000311d00020950000000eac312ee27382500000000000000e2280340000000a8e8000f03800000000000002f2f000202a0000cc90000000ac5000000034911a1a906ab62315d04b30e0002e320002e43117892ba3398870000000c09867b0002067202e40a000349900018ee3174211fc5a092d3ec000d3c40000001eee8488000d25800000000005074af400020a80003c176cb80000003c558275418188b2b573e800000013170000000000000000034980000000000021800000009b4800000000000001c8e0000ce0000103a00000003320000000500800014030000102000000060040602c07014050000201c0100001000000040000c0800c0200c050040100c0100c04004000000000400000060040300c0000c000180001c0300001008080080100801018000040000001008020180200401000040100000400014000040000000000030000201c020000300000010020000901c01008000000700001 else 0xedac1e822e000344f51500000000000000348c401800000000000000000f3e4ab88831e0e0001901000000000000000000000a4c00000001c520001238938f4eda29400084440b3c1bc5240000cd80000000ebb4000000000042e949bc2a84dacc40000606c000642400020ac2c16cb56480000000000000000012410000000000000090cecd3a40c00000018580000000ccd00000000000000083c52c00000002c930003523a004000a21000030440004468c610000000c89d42100000000c03724dc9c000000000000018470000000000000000000000002d2c00000000000000000000000038320001ed100000000002002000000001f800059a0000d214000225c000396784a2241cec00030bb00000000000cea0003301000261d716d4bf8b754f211a3c2e74280000000000000000043100000c9a2f7b0a2a4ceb50e73681c0000003b1d000009eb2f3cdb00000009a3800000000000002ec7000000000000000000000f1cb888000000000000000b24000000287d50a4000000000000026230000000000011b0000000000000000000000000000000064f00004cb00004e8ac6800000000002b5c0002b2c4f300000000000a1b000000000000000003cf5f17c0000003e6c105000000000fcc1980000000000e13400072868a3fa0800000000b50000000000000000000000001d0462b61070002c6951dc00000000008be80000000000b2500000002cf40002e3d6422c0300011340000000a440000f20f80d00000003027a6499f2ae5e1ec00000000000001a2c00018a2e9d00000000000000103100000006c8c00078d400000026760000000d0f666e0000465a4940000000c2f12980c6a1d343902f40000000257b14c000e088000000147652e105651a8000000340f000000000004c70058000f09c00000000000002405a3350860000000b280000fa1010c000349ff03000000000000002c801c0c00062b8000807c0000000000000333100000000000000b22c00000000000003b3252acd2f4af210ef460000c3dc000000307f000000000021310000000000000081cc0004ba800000000000000000000000000000000000000b1068e4000000000000000000000000000000032a5000091e00)
def mo255D13 (j : Nat) : Nat := 0x305081c4ff
def mo255H13 (j : Nat) : Nat := 0x125658000000000068000000000054c00000002d5728000000000000f8801678d3e5a860000000284a244400000927e594000000000000000391c0801c68000000000000c880000224000000000066246f80010009327000b78000058c002264380193800c2800000008000000000080
def mo255L : Nat → Packing
  | 6 => (2,7,7,0,0,3,0,mo255D6)
  | 7 => (9,6,7,0,0,8,0,mo255D7)
  | 8 => (74,5,7,0,0,10,0,mo255D8)
  | 9 => (613,4,7,0,0,15,0,mo255D9)
  | 10 => (1199,3,7,0,0,17,0,mo255D10)
  | 11 => (309,2,7,0,0,15,0,mo255D11)
  | 12 => (20,1,7,0,0,11,0,mo255D12)
  | 13 => (1,0,7,0,0,0,0,mo255D13)
  | _ => emptyPacking
def mo255I : Nat → Nat → Option (Nat × Nat)
  | 7 => lookupWord 1 13 0 6 1 1 mo255H7
  | 8 => lookupWord 3 13 4 9 4 1 mo255H8
  | 9 => lookupWord 23 127 7 12 7 1 mo255H9
  | 10 => lookupWord 216 1693 11 15 10 1 mo255H10
  | 11 => lookupWord 420 1931 11 16 11 1 mo255H11
  | 12 => lookupWord 113 971 10 14 9 1 mo255H12
  | 13 => lookupWord 9 83 7 10 5 1 mo255H13
  | _ => fun _ => none
def mo255 : Forest := ⟨1279,13,fun i => mo255Y[i]?.getD (0,0),mo255C,mo255A,mo255L,mo255I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo255P6_0 : CutRow mo255 6 0 2 := mixedCut (pos:=0x18090240c05012048180a03) (neg:=0x29144a146228c86230950a21c) (data:=fun _ => 0x6703152095018730) rfl (by decide +kernel)
theorem mo255B6 : CutRow mo255 6 0 2 := mo255P6_0
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
theorem mo255P7_2 : CutRow mo255 7 2 7 := mixedCut (pos:=0x18090240c05012048180a03) (neg:=0x29144a146228c86230950a21c) (data:=fun _ => 0x7012350070323507110206571302065670315209501873009108740) rfl (by decide +kernel)
theorem mo255B7 : CutRow mo255 7 0 9 := (@joinRow mo255 7 0 2 7 mo255P7_0 mo255P7_2)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo255P8_0 : CutRow mo255 8 0 14 := by
  apply checkedRow
  apply cellsBlock (ar:=8) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo255P8_14 : CutRow mo255 8 14 60 := mixedCut (pos:=0x18090240c05012048180a03) (neg:=0x29144a146228c86230950a21c) (data:=fun _ => 0x5689350713023202010612020106120711023207130232071102370713023706703154295018752511023740960485350869375503643755210a07571102075521050755280a075711020750701235071102075523050757010238471102075701023840701234017012361170323610701235007012350070123500563435007012350070123502508a35007012350250353500563436067031531670315319501874196063852701023846703153158036632871609540701234058036632711020640701235005689350056893500614347171102064711020647110206407012350070123407110232007012350) rfl (by decide +kernel)
theorem mo255B8 : CutRow mo255 8 0 74 := (@joinRow mo255 8 0 14 60 mo255P8_0 mo255P8_14)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo255P9_0 : CutRow mo255 9 0 13 := by
  apply checkedRow
  apply cellsBlock (ar:=8) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo255P9_13 : CutRow mo255 9 13 48 := by
  apply checkedRow
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo255P9_61 : CutRow mo255 9 61 48 := by
  apply checkedRow
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo255P9_109 : CutRow mo255 9 109 48 := by
  apply checkedRow
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo255P9_157 : CutRow mo255 9 157 48 := by
  apply checkedRow
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo255P9_205 : CutRow mo255 9 205 44 := by
  apply checkedRow
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo255P9_249 : CutRow mo255 9 249 9 := by
  apply checkedRow
  apply cellsBlock (ar:=10) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo255P9_258 : CutRow mo255 9 258 96 := mixedCut (pos:=0x18090240c05012048180a03) (neg:=0x29144a146228c86230950a21c) (data:=fun _ => 0x826074317110233071102330711023907110239017012382604034302114001021140010170123621701236221140010170123622114001005634372211400102114001021140010211400102114001021140010170123721701236221140010701643301703237270164330806184411701237250364370403643709301874221140010211400102114001021140010211400102114001021140010211400106303154221140010211400102114001021140010211400103930878487160954604134412114001039308794501643206041344150164320501643205016432043140010431400104314001010401221104012215086932050869320508693205086932043140010431400106041344150164320501643205016432050164320431400104314001050164390431400106061844150364320503643205016432050364320503643204314001043140010431400102114201050164320501643205016432087160954871609654314001050869380503643802114001021140010) rfl (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo255P9_354 : CutRow mo255 9 354 96 := mixedCut (pos:=0x18090240c05012048180a03) (neg:=0x29144a146228c86230950a21c) (data:=fun _ => 0x21160010211600109504974196083852960838522116001095649741201061202010612020106120231061702010612017012362501643202010612020106120201061202010612017012362201061202010611025035361170123612508a36123106170126100808240743117012361126100701701236187160954056343711261007002016171126100800561437105689371056143710561437105614371056143710561437101041291010412910561437121160010211600102116001071102330711023305130533069803885711023307110233071102330711023307110233071102330711023807110238051102380711023808260743160403431604034317110233071102330711023307110233071102320513053307110237071102370711023702804748371102320711023205180a3205180a3205180a32071102320711023207110239051305320711023205130532071102320711023207110232071102390711023907110232071102320826074416040344160403441) rfl (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo255P9_450 : CutRow mo255 9 450 96 := mixedCut (pos:=0x18090240c05012048180a03) (neg:=0x29144a146228c86230950a21c) (data:=fun _ => 0x393087852310612071102380231061202310612020106120201061202010612071102330713023302310617008067462061434820614348206143482061434820614348208067462711023200614348271102320061434820614348217012372711023209303875217012372170123721040822171102396711023962310612017012362104012212310612017012362231061201040122110403221170123622310612017012372104032211701237267031553670315539501876396063874170123726703155358036654871609760563437217012372056343825803665471102370711023961701236217012372056893720568937205689372170123621701237217012372170123621701236217012362170123621701237217012362170123621701237260413430061434820614348228067462061434820614348221140010211400102114001023106170211600102116001021160010211600102116001021160010211600102116001021140010211400108716095421160010) rfl (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo255P9_546 : CutRow mo255 9 546 67 := mixedCut (pos:=0x18090240c05012048180a03) (neg:=0x29144a146228c86230950a21c) (data:=fun _ => 0x20106120211400102114001023106170231061707110233071102390711023907110233071102330711023305130533071102330513053307110239071102330711023305180a3305180a3305180a3307110233071102330201061202116001020106120201061207110233071302330201061202310612071102320231061207110232023106120231061202310612071102320930387522310612010408221211600101040822110401221211600101040122110403221211600101040322171102330713023307110233071102330580576962114001021140010211400102114001021140010231061202010612071102380393087852010612023106120711023802310612071102380) rfl (by decide +kernel)
theorem mo255B9 : CutRow mo255 9 0 613 := (@joinRow mo255 9 0 205 408 (@joinRow mo255 9 0 61 144 (@joinRow mo255 9 0 13 48 mo255P9_0 mo255P9_13) (@joinRow mo255 9 61 48 96 mo255P9_61 (@joinRow mo255 9 109 48 48 mo255P9_109 mo255P9_157))) (@joinRow mo255 9 205 149 259 (@joinRow mo255 9 205 44 105 mo255P9_205 (@joinRow mo255 9 249 9 96 mo255P9_249 mo255P9_258)) (@joinRow mo255 9 354 96 163 mo255P9_354 (@joinRow mo255 9 450 96 67 mo255P9_450 mo255P9_546))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo255P10_0 : CutRow mo255 10 0 1 := by
  apply checkedRow
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo255P10_1 : CutRow mo255 10 1 48 := by
  apply checkedRow
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo255P10_49 : CutRow mo255 10 49 48 := by
  apply checkedRow
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo255P10_97 : CutRow mo255 10 97 48 := by
  apply checkedRow
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo255P10_145 : CutRow mo255 10 145 48 := by
  apply checkedRow
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo255P10_193 : CutRow mo255 10 193 10 := by
  apply checkedRow
  apply cellsBlock (ar:=9) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo255P10_203 : CutRow mo255 10 203 48 := by
  apply checkedRow
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo255P10_251 : CutRow mo255 10 251 48 := by
  apply checkedRow
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo255P10_299 : CutRow mo255 10 299 48 := by
  apply checkedRow
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo255P10_347 : CutRow mo255 10 347 48 := by
  apply checkedRow
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo255P10_395 : CutRow mo255 10 395 48 := by
  apply checkedRow
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo255P10_443 : CutRow mo255 10 443 48 := by
  apply checkedRow
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo255P10_491 : CutRow mo255 10 491 48 := by
  apply checkedRow
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo255P10_539 : CutRow mo255 10 539 48 := by
  apply checkedRow
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo255P10_587 : CutRow mo255 10 587 48 := by
  apply checkedRow
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo255P10_635 : CutRow mo255 10 635 48 := by
  apply checkedRow
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo255P10_683 : CutRow mo255 10 683 48 := by
  apply checkedRow
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo255P10_731 : CutRow mo255 10 731 48 := by
  apply checkedRow
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo255P10_779 : CutRow mo255 10 779 48 := by
  apply checkedRow
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo255P10_827 : CutRow mo255 10 827 48 := by
  apply checkedRow
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo255P10_875 : CutRow mo255 10 875 16 := by
  apply checkedRow
  apply cellsBlock (ar:=10) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo255P10_891 : CutRow mo255 10 891 13 := by
  apply checkedRow
  apply cellsBlock (ar:=11) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo255P10_904 : CutRow mo255 10 904 96 := mixedCut (pos:=0x18090240c05012048180a03) (neg:=0x29144a146228c86230950a21c) (data:=fun _ => 0x2010612020106120211600102116001021160010211600102116001021160010211600102116001021160010211600102116001067052553211600109502a7639608387467052553670525536705255321160010670525539505a76387160976201061202010612020106120104012212010612010401221201061202186701010401221104012211040122121867010218670102010612020106120201061202116001021160010711023302116001021160010211600107110233021160010211600102116001021160010211600107110233093038763211600102116001021160010211600102116001021160010211600102116001021160010211600101042122121160010211600102116001021160010211600102116001021160010211600102116001021160010211600106041344121160010211600109564976321160010960838742116001060413441960838749504976387160976604134416061844160413441604134416041344160413441604134411040122150169330) rfl (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo255P10_1000 : CutRow mo255 10 1000 96 := mixedCut (pos:=0x18090240c05012048180a03) (neg:=0x29144a146228c86230950a21c) (data:=fun _ => 0x711023305180a33071102330711023307110233071102330513053307110233071102330711023307110233051305330711023307110233071102330711023307110233082607441104012217110233082607441104012217110233071102330711023307110233071102330104012217110233071102330711023301040122171102330513053305180a3305130533010401221513053305130533051305330513053307110233071102330871609765180a330711023307110233071102330711023307110233071102330711023306041344160413441604134416061844160413441604134416041344187160976630315539301876396083874630315536303155363031553630315537110233093038763711023308716097610401221104532217110233093038763104212211047822110401221106082211040122110401221104012211040122110401221104032211040122110401221104012217110233010401221201761202010612071102330930387632010612020106120) rfl (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo255P10_1096 : CutRow mo255 10 1096 96 := mixedCut (pos:=0x18090240c05012048180a03) (neg:=0x29144a146228c86230950a21c) (data:=fun _ => 0x871609768716097687160976871609768716097687160976871609765036433050364330508693305036433050364330503643305036433050364330503643305036433050364330503643306041344150364330501643305016433050164330501643305016433050164330508693305086933050869330501643305016433050164330501643306061844150164330826074416040344160403441604034416040344182607441604034416040344160403441711023309303876371102330711023307110233071102330711023307110233071102330826074416040344160403441604034418260744160403441826074416040344160403441826074416040344123106120826074415137a330604034415117a33023106120231061205117a3308260744182407441231061208240744182407441950497638260744123106120824074418240744182407441711023302310612051305330711023305180a33071102330711023307110233071102330711023307110233071102330) rfl (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo255P10_1192 : CutRow mo255 10 1192 7 := mixedCut (pos:=0x18090240c05012048180a03) (neg:=0x29144a146228c86230950a21c) (data:=fun _ => 0x71102330104012211040122150169330604134415036933087160976) rfl (by decide +kernel)
theorem mo255B10 : CutRow mo255 10 0 1199 := (@joinRow mo255 10 0 539 660 (@joinRow mo255 10 0 203 336 (@joinRow mo255 10 0 97 106 (@joinRow mo255 10 0 1 96 mo255P10_0 (@joinRow mo255 10 1 48 48 mo255P10_1 mo255P10_49)) (@joinRow mo255 10 97 48 58 mo255P10_97 (@joinRow mo255 10 145 48 10 mo255P10_145 mo255P10_193))) (@joinRow mo255 10 203 144 192 (@joinRow mo255 10 203 48 96 mo255P10_203 (@joinRow mo255 10 251 48 48 mo255P10_251 mo255P10_299)) (@joinRow mo255 10 347 96 96 (@joinRow mo255 10 347 48 48 mo255P10_347 mo255P10_395) (@joinRow mo255 10 443 48 48 mo255P10_443 mo255P10_491)))) (@joinRow mo255 10 539 288 372 (@joinRow mo255 10 539 144 144 (@joinRow mo255 10 539 48 96 mo255P10_539 (@joinRow mo255 10 587 48 48 mo255P10_587 mo255P10_635)) (@joinRow mo255 10 683 48 96 mo255P10_683 (@joinRow mo255 10 731 48 48 mo255P10_731 mo255P10_779))) (@joinRow mo255 10 827 77 295 (@joinRow mo255 10 827 48 29 mo255P10_827 (@joinRow mo255 10 875 16 13 mo255P10_875 mo255P10_891)) (@joinRow mo255 10 904 192 103 (@joinRow mo255 10 904 96 96 mo255P10_904 mo255P10_1000) (@joinRow mo255 10 1096 96 7 mo255P10_1096 mo255P10_1192)))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo255P11_0 : CutRow mo255 11 0 12 := by
  apply checkedRow
  apply cellsBlock (ar:=8) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo255P11_12 : CutRow mo255 11 12 48 := by
  apply checkedRow
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo255P11_60 : CutRow mo255 11 60 41 := by
  apply checkedRow
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo255P11_101 : CutRow mo255 11 101 48 := by
  apply checkedRow
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo255P11_149 : CutRow mo255 11 149 48 := by
  apply checkedRow
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo255P11_197 : CutRow mo255 11 197 48 := by
  apply checkedRow
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo255P11_245 : CutRow mo255 11 245 48 := by
  apply checkedRow
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo255P11_293 : CutRow mo255 11 293 16 := by
  apply checkedRow
  apply cellsBlock (ar:=10) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem mo255B11 : CutRow mo255 11 0 309 := (@joinRow mo255 11 0 149 160 (@joinRow mo255 11 0 60 89 (@joinRow mo255 11 0 12 48 mo255P11_0 mo255P11_12) (@joinRow mo255 11 60 41 48 mo255P11_60 mo255P11_101)) (@joinRow mo255 11 149 96 64 (@joinRow mo255 11 149 48 48 mo255P11_149 mo255P11_197) (@joinRow mo255 11 245 48 16 mo255P11_245 mo255P11_293)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo255P12_0 : CutRow mo255 12 0 20 := by
  apply checkedRow
  apply cellsBlock (ar:=9) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem mo255B12 : CutRow mo255 12 0 20 := mo255P12_0
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
  · exact (mixedEmpty mo255 5 0)
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
theorem mo255G : graphValid mo255 (boundsBefore K253) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo255R : Impossible false graph 13 eightInputs.toFinset := by
  rw [show graph = targetOf mo255 by decide +kernel]
  exact mixedRoot (g:=mo255) (top:=13) (i:=0) (before_sound K253 (known_down V253)) mo255G mo255T (by decide) (by decide +kernel)

theorem deletion_bound : ∀ t : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 8 (fun x : Fin 8 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 3 && x 6) || (x 4 && x 5) || (x 4 && x 7) || (x 6 && x 7)) t → 14 ≤ t := by
  intro t hs
  by_contra! small
  obtain ⟨C,hf,hsize,heq⟩ := hs
  exact PEqualNP.Outside.L_meta_17349_aux.EightVertex.directSplit PEqualNP.Outside.L_meta_17349_aux.EightVertex.mo255R PEqualNP.Outside.L_meta_17349_aux.EightVertex.g255R ⟨C,hf,by omega,heq⟩

end PEqualNP.Outside.L_meta_17349_aux.EightVertex

namespace PEqualNP.Outside.L_meta_17349_aux
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

def edge : (Fin 9 → Bool) → Bool := fun x : Fin 9 → Bool => (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 5) || (x 1 && x 6) || (x 2 && x 6) || (x 1 && x 7) || (x 3 && x 7) || (x 4 && x 7) || (x 0 && x 8) || (x 2 && x 8) || (x 3 && x 8) || (x 6 && x 8)

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
  (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) ||
  (x 1 && x 4) || (x 3 && x 5) || (x 3 && x 6) || (x 4 && x 5) ||
  (x 4 && x 7) || (x 6 && x 7)

def ordered (x : Fin 9 → Bool) :=
  baseEight (fun j => x j.castSucc) || (x 8 && x 7) || (x 8 && x 0)

def orderNine : Fin 9 → Fin 9 := ![3,4,2,8,6,5,1,7,0]

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
    · exact ⟨fun i => decide (i = 7), by decide⟩
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

end PEqualNP.Outside.L_meta_17349_aux

namespace PEqualNP.Outside.L_meta_17349_aux
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
    ordered_has_derived PEqualNP.Outside.L_meta_17349_aux.EightVertex.deletion_bound D dl ds de
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

end PEqualNP.Outside.L_meta_17349_aux

open PEqualNP.Outside.L_meta_17349_aux PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity in
theorem PEqualNP.Outside.L_meta_17349 : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C → ((∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = !(y 3)) ∨ (∃ j : Fin 9, (3 : Fin 9) < j ∧ ∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 3 && y j)) ∨ (∃ j : Fin 9, (3 : Fin 9) < j ∧ ∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 3 || y j))) → PEqualNP.MetaComplexity.circuitFun 9 C = (fun x : Fin 9 → Bool => (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 5) || (x 1 && x 6) || (x 2 && x 6) || (x 1 && x 7) || (x 3 && x 7) || (x 4 && x 7) || (x 0 && x 8) || (x 2 && x 8) || (x 3 && x 8) || (x 6 && x 8)) → 16 ≤ C.size := by
  intro C legal first correct
  by_contra! hs
  have same := first_irrelevant C legal (by omega) correct
  rcases first with h | ⟨j, hj, h⟩ | ⟨j, hj, h⟩
  · have eq := (h (sample false false)).symm.trans ((same false).trans (h (sample false true)))
    exact (by decide : (!(sample false false 3)) ≠ (!(sample false true 3))) eq
  · have eq := (h (sample true false)).symm.trans ((same true).trans (h (sample true true)))
    exact (by decide +kernel : ∀ k : Fin 9, 3 < k →
      (sample true false 3 && sample true false k) ≠ (sample true true 3 && sample true true k)) j hj eq
  · have eq := (h (sample false false)).symm.trans ((same false).trans (h (sample false true)))
    exact (by decide +kernel : ∀ k : Fin 9, 3 < k →
      (sample false false 3 || sample false false k) ≠ (sample false true 3 || sample false true k)) j hj eq
