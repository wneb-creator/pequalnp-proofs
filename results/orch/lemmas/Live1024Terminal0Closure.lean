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


def LabelPartition {α : Type} [DecidableEq α] (roots : Finset α)
    (S : Finset Sig) (label : Sig → Finset α) : Prop :=
  (∀ v ∈ S, label v ⊆ roots) ∧
  (∀ v ∈ S, ∀ w ∈ S, v ≠ w → Disjoint (label v) (label w)) ∧
  (∀ r ∈ roots, ∃ v ∈ S, r ∈ label v)

def ColumnSupport {α Ω : Type} [DecidableEq α] (raw : α → Sig)
    (col : Sig → Set Ω) (A : Finset α) (v : Sig) : Prop :=
  ∀ o ∈ col v, ∃ r ∈ A, o ∈ col (raw r)

def ColumnAdmissible {α Ω : Type} [DecidableEq α] (roots : Finset α)
    (raw : α → Sig) (col : Sig → Set Ω) (need : Set Ω)
    (A : Finset α) (v : Sig) : Prop :=
  ∀ o ∈ need, (∀ r ∈ roots, r ∉ A → o ∉ col (raw r)) → o ∈ col v

theorem tight_closure_fresh_state {α Ω : Type} [DecidableEq α]
    (roots : Finset α) (raw : α → Sig) (col : Sig → Set Ω) (need : Set Ω)
    (Cert : Finset α → Sig → Prop) (u : Bool) (T : Sig)
    (gateCol : ∀ d a b, allowed u d → col (bin d a b) ⊆ col a ∪ col b)
    (rowCover : ∀ k S, Live u T k S → ∀ o ∈ need, ∃ v ∈ S, o ∈ col v)
    (closed : ∀ A B a b d, Disjoint A B → allowed u d → a ≠ b →
       bin d a b ≠ a → bin d a b ≠ b → proper (bin d a b) →
      Cert A a → Cert B b → ColumnAdmissible roots raw col need (A ∪ B) (bin d a b) →
      Cert (A ∪ B) (bin d a b))
    {k : Nat} {S : Finset Sig} (run : Live u T k S) (tight : S.card = k + 1)
    (label : Sig → Finset α) (part : LabelPartition roots S label)
    (entries : ∀ v ∈ S, Cert (label v) v)
    (supports : ∀ v ∈ S, ColumnSupport raw col (label v) v) : Cert roots T := by
  classical
  induction k generalizing S label with
  | zero =>
    obtain ⟨rfl, _⟩ := run
    have eq : label T = roots := by
      apply Finset.Subset.antisymm (part.1 T (by simp))
      intro r hr
      obtain ⟨v, hv, hrv⟩ := part.2.2 r hr
      have hvT := Finset.mem_singleton.mp hv
      subst v
      exact hrv
    simpa only [eq] using entries T (by simp)
  | succ k ih =>
    obtain ⟨U, a, b, d, hd, rfl, pa, pb, hab, hfresh, tail⟩ := run
    let z := bin d a b
    have fresh : z ∉ U :=
      fun h => hfresh (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem h))
    have bound := live_size tail
    rw [Finset.card_insert_of_notMem fresh] at bound
    have le1 := Finset.card_insert_le (a := a) (insert b U)
    have le2 := Finset.card_insert_le (a := b) U
    have ha : a ∉ U := by
      intro h
      rw [Finset.insert_eq_of_mem (Finset.mem_insert_of_mem h : a ∈ insert b U)] at tight
      omega
    have hb : b ∉ U := by
      intro h
      rw [Finset.insert_eq_of_mem h] at tight le1
      omega
    have eq : (insert z U).card = k + 1 := by
      rw [Finset.card_insert_of_notMem fresh]
      omega
    have memA : a ∈ insert a (insert b U) := by simp
    have memB : b ∈ insert a (insert b U) := by simp
    have memU (v : Sig) (hv : v ∈ U) : v ∈ insert a (insert b U) := by simp [hv]
    have differentA (v : Sig) (hv : v ∈ U) : a ≠ v := by
      rintro rfl
      exact ha hv
    have differentB (v : Sig) (hv : v ∈ U) : b ≠ v := by
      rintro rfl
      exact hb hv
    have adm : ColumnAdmissible roots raw col need (label a ∪ label b) z := by
      intro o ho outside
      obtain ⟨v, hv, hov⟩ := rowCover k (insert z U) tail o ho
      rcases Finset.mem_insert.mp hv with rfl | hv
      · exact hov
      obtain ⟨r, hr, hor⟩ := supports v (memU v hv) o hov
      have rRoot := part.1 v (memU v hv) hr
      have notA : r ∉ label a := fun hra =>
        Finset.disjoint_left.mp (part.2.1 a memA v (memU v hv) (differentA v hv)) hra hr
      have notB : r ∉ label b := fun hrb =>
        Finset.disjoint_left.mp (part.2.1 b memB v (memU v hv) (differentB v hv)) hrb hr
      exact False.elim (outside r rRoot (by simpa using And.intro notA notB) hor)
    have certZ : Cert (label a ∪ label b) z :=
      closed (label a) (label b) a b d (part.2.1 a memA b memB hab) hd hab
        (fun h => hfresh (Finset.mem_insert.mpr (Or.inl h)))
        (fun h => hfresh (Finset.mem_insert_of_mem (Finset.mem_insert.mpr (Or.inl h))))
        (live_proper tail z (Finset.mem_insert_self _ _)) (entries a memA) (entries b memB) adm
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
    have entriesNext : ∀ v ∈ insert z U, Cert (next v) v := by
      intro v hv
      rcases Finset.mem_insert.mp hv with rfl | hv
      · simpa only [nextZ] using certZ
      · simpa only [nextU v hv] using entries v (memU v hv)
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
    exact ih tail eq next partNext entriesNext supportsNext

theorem tight_closure_state {α Ω : Type} [DecidableEq α]
    (roots : Finset α) (raw : α → Sig) (col : Sig → Set Ω) (need : Set Ω)
    (Cert : Finset α → Sig → Prop) (u : Bool) (T : Sig)
    (gateCol : ∀ d a b, allowed u d → col (bin d a b) ⊆ col a ∪ col b)
    (rowCover : ∀ k S, Live u T k S → ∀ o ∈ need, ∃ v ∈ S, o ∈ col v)
    (closed : ∀ A B a b d, Disjoint A B → allowed u d → proper (bin d a b) →
      Cert A a → Cert B b → ColumnAdmissible roots raw col need (A ∪ B) (bin d a b) →
      Cert (A ∪ B) (bin d a b))
    {k : Nat} {S : Finset Sig} (run : Live u T k S) (tight : S.card = k + 1)
    (label : Sig → Finset α) (part : LabelPartition roots S label)
    (entries : ∀ v ∈ S, Cert (label v) v)
    (supports : ∀ v ∈ S, ColumnSupport raw col (label v) v) : Cert roots T := by
  exact tight_closure_fresh_state roots raw col need Cert u T gateCol rowCover
    (fun A B a b d hAB hd _ _ _ hp hA hB adm => closed A B a b d hAB hd hp hA hB adm)
    run tight label part entries supports

theorem tight_closure_raw {α Ω : Type} [DecidableEq α]
    (roots : Finset α) (raw : α → Sig) (col : Sig → Set Ω) (need : Set Ω)
    (Cert : Finset α → Sig → Prop) (u : Bool) (T : Sig)
    (distinct : Set.InjOn raw (↑roots : Set α))
    (initial : ∀ r ∈ roots, Cert {r} (raw r))
    (gateCol : ∀ d a b, allowed u d → col (bin d a b) ⊆ col a ∪ col b)
    (rowCover : ∀ k S, Live u T k S → ∀ o ∈ need, ∃ v ∈ S, o ∈ col v)
    (closed : ∀ A B a b d, Disjoint A B → allowed u d → proper (bin d a b) →
      Cert A a → Cert B b → ColumnAdmissible roots raw col need (A ∪ B) (bin d a b) →
      Cert (A ∪ B) (bin d a b))
    {k : Nat} (run : Live u T k (roots.image raw))
    (tight : (roots.image raw).card = k + 1) : Cert roots T := by
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
  have entries : ∀ v ∈ roots.image raw, Cert (label v) v := by
    intro v hv
    obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hv
    simpa only [leaf r hr] using initial r hr
  have supports : ∀ v ∈ roots.image raw, ColumnSupport raw col (label v) v := by
    intro v hv o ho
    obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hv
    exact ⟨r, Finset.mem_filter.mpr ⟨hr, rfl⟩, ho⟩
  exact tight_closure_state roots raw col need Cert u T gateCol rowCover closed
    run tight label part entries supports

theorem tight_closure_exclusion {α Ω : Type} [DecidableEq α]
    (roots : Finset α) (raw : α → Sig) (col : Sig → Set Ω) (need : Set Ω)
    (Cert : Finset α → Sig → Prop) (u : Bool) (T : Sig) (cap : Nat)
    (distinct : Set.InjOn raw (↑roots : Set α))
    (initial : ∀ r ∈ roots, Cert {r} (raw r))
    (gateCol : ∀ d a b, allowed u d → col (bin d a b) ⊆ col a ∪ col b)
    (rowCover : ∀ k S, Live u T k S → ∀ o ∈ need, ∃ v ∈ S, o ∈ col v)
    (closed : ∀ A B a b d, Disjoint A B → allowed u d → proper (bin d a b) →
      Cert A a → Cert B b → ColumnAdmissible roots raw col need (A ∪ B) (bin d a b) →
      Cert (A ∪ B) (bin d a b))
    (width : (roots.image raw).card = cap + 1) (missing : ¬ Cert roots T) :
    Impossible u T cap (roots.image raw) := by
  intro k hk run
  have bound := live_size run
  have tight : (roots.image raw).card = k + 1 := by omega
  exact missing (tight_closure_raw roots raw col need Cert u T distinct initial
    gateCol rowCover closed run tight)

theorem tight_closure_fresh_raw {α Ω : Type} [DecidableEq α]
    (roots : Finset α) (raw : α → Sig) (col : Sig → Set Ω) (need : Set Ω)
    (Cert : Finset α → Sig → Prop) (u : Bool) (T : Sig)
    (distinct : Set.InjOn raw (↑roots : Set α))
    (initial : ∀ r ∈ roots, Cert {r} (raw r))
    (gateCol : ∀ d a b, allowed u d → col (bin d a b) ⊆ col a ∪ col b)
    (rowCover : ∀ k S, Live u T k S → ∀ o ∈ need, ∃ v ∈ S, o ∈ col v)
    (closed : ∀ A B a b d, Disjoint A B → allowed u d → a ≠ b →
       bin d a b ≠ a → bin d a b ≠ b → proper (bin d a b) →
      Cert A a → Cert B b → ColumnAdmissible roots raw col need (A ∪ B) (bin d a b) →
      Cert (A ∪ B) (bin d a b))
    {k : Nat} (run : Live u T k (roots.image raw))
    (tight : (roots.image raw).card = k + 1) : Cert roots T := by
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
  have entries : ∀ v ∈ roots.image raw, Cert (label v) v := by
    intro v hv
    obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hv
    simpa only [leaf r hr] using initial r hr
  have supports : ∀ v ∈ roots.image raw, ColumnSupport raw col (label v) v := by
    intro v hv o ho
    obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hv
    exact ⟨r, Finset.mem_filter.mpr ⟨hr, rfl⟩, ho⟩
  exact tight_closure_fresh_state roots raw col need Cert u T gateCol rowCover closed
    run tight label part entries supports

theorem tight_closure_fresh_exclusion {α Ω : Type} [DecidableEq α]
    (roots : Finset α) (raw : α → Sig) (col : Sig → Set Ω) (need : Set Ω)
    (Cert : Finset α → Sig → Prop) (u : Bool) (T : Sig) (cap : Nat)
    (distinct : Set.InjOn raw (↑roots : Set α))
    (initial : ∀ r ∈ roots, Cert {r} (raw r))
    (gateCol : ∀ d a b, allowed u d → col (bin d a b) ⊆ col a ∪ col b)
    (rowCover : ∀ k S, Live u T k S → ∀ o ∈ need, ∃ v ∈ S, o ∈ col v)
    (closed : ∀ A B a b d, Disjoint A B → allowed u d → a ≠ b →
       bin d a b ≠ a → bin d a b ≠ b → proper (bin d a b) →
      Cert A a → Cert B b → ColumnAdmissible roots raw col need (A ∪ B) (bin d a b) →
      Cert (A ∪ B) (bin d a b))
    (width : (roots.image raw).card = cap + 1) (missing : ¬ Cert roots T) :
    Impossible u T cap (roots.image raw) := by
  intro k hk run
  have bound := live_size run
  have tight : (roots.image raw).card = k + 1 := by omega
  exact missing (tight_closure_fresh_raw roots raw col need Cert u T distinct initial
    gateCol rowCover closed run tight)

def separationColumn {Ω : Type} (u : Bool) (positive negative : Ω → Row)
    (v : Sig) : Set Ω := {o |
  if u then bit (positive o) v ≠ bit (negative o) v
  else bit (positive o) v = true ∧ bit (negative o) v = false}

theorem separationColumn_gate {Ω : Type} (u : Bool) (positive negative : Ω → Row)
    (d : Nat) (a b : Sig) (legal : allowed u d) :
    separationColumn u positive negative (bin d a b) ⊆
      separationColumn u positive negative a ∪ separationColumn u positive negative b := by
  intro o ho
  rcases allowed_four legal with rfl | rfl | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  all_goals try cases u
  all_goals
    cases hpa : bit (positive o) a <;> cases hna : bit (negative o) a <;>
      cases hpb : bit (positive o) b <;> cases hnb : bit (negative o) b <;>
      simp_all [separationColumn, bit_bin]

theorem separationColumn_cover {Ω : Type} (u : Bool) (positive negative : Ω → Row)
    (T : Sig) (need : Set Ω) (valid : need ⊆ separationColumn u positive negative T)
    (k : Nat) (S : Finset Sig) (run : Live u T k S) :
    ∀ o ∈ need, ∃ v ∈ S, o ∈ separationColumn u positive negative v := by
  intro o ho
  have ht := valid ho
  cases u with
  | false =>
    change bit (positive o) T = true ∧ bit (negative o) T = false at ht
    exact mono_row_difference run rfl ht.1 ht.2
  | true =>
    change bit (positive o) T ≠ bit (negative o) T at ht
    exact live_row_difference run ht



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

def liftLabels {α : Type} [DecidableEq α] (A : Finset α) : Finset (Sum α Bool) :=
  A.image Sum.inl

def duplicateRoots {α : Type} [DecidableEq α] (roots A : Finset α) :
    Finset (Sum α Bool) :=
  liftLabels (roots \ A) ∪ {Sum.inr false, Sum.inr true}

def duplicateRaw {α : Type} (raw : α → Sig) (w : Sig) : Sum α Bool → Sig :=
  Sum.elim raw (fun _ => w)

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

theorem merge_cert_state {α Ω : Type} [DecidableEq α]
    (roots : Finset α) (raw : α → Sig) (col : Sig → Set Ω) (need : Set Ω)
    (Cert : Finset α → Sig → Prop) (u : Bool)
    (gateCol : ∀ d a b, allowed u d → col (bin d a b) ⊆ col a ∪ col b)
    (closed : ∀ A B a b d, Disjoint A B → allowed u d → a ≠ b → bin d a b ≠ a →
      bin d a b ≠ b → proper (bin d a b) → Cert A a → Cert B b → ColumnAdmissible roots raw col need (A ∪ B) (bin d a b) →
      Cert (A ∪ B) (bin d a b))
    (U : Finset Sig) (a b : Sig) (d : Nat) (hd : allowed u d) (hab : a ≠ b)
    (hfresh : bin d a b ∉ insert a (insert b U)) (ha : a ∉ U) (hb : b ∉ U)
    (outputProper : proper (bin d a b))
    (cover : ∀ o ∈ need, ∃ v ∈ insert (bin d a b) U, o ∈ col v)
    (label : Sig → Finset α) (part : LabelPartition roots (insert a (insert b U)) label)
    (entries : ∀ v ∈ insert a (insert b U), Cert (label v) v)
    (supports : ∀ v ∈ insert a (insert b U), ColumnSupport raw col (label v) v) :
    ∃ next : Sig → Finset α, LabelPartition roots (insert (bin d a b) U) next ∧
      (∀ v ∈ insert (bin d a b) U, Cert (next v) v) ∧
      (∀ v ∈ insert (bin d a b) U, ColumnSupport raw col (next v) v) := by
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
  have adm : ColumnAdmissible roots raw col need (label a ∪ label b) z := by
    intro o ho outside
    obtain ⟨v, hv, hov⟩ := cover o ho
    rcases Finset.mem_insert.mp hv with rfl | hv
    · exact hov
    obtain ⟨r, hr, hor⟩ := supports v (memU v hv) o hov
    have rRoot := part.1 v (memU v hv) hr
    have notA : r ∉ label a := fun hra =>
      Finset.disjoint_left.mp (part.2.1 a memA v (memU v hv) (differentA v hv)) hra hr
    have notB : r ∉ label b := fun hrb =>
      Finset.disjoint_left.mp (part.2.1 b memB v (memU v hv) (differentB v hv)) hrb hr
    exact False.elim (outside r rRoot (by simpa using And.intro notA notB) hor)
  have certZ : Cert (label a ∪ label b) z :=
    closed (label a) (label b) a b d (part.2.1 a memA b memB hab) hd hab
      (fun h => hfresh (h.symm ▸ memA)) (fun h => hfresh (h.symm ▸ memB)) outputProper (entries a memA) (entries b memB) adm
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
  have entriesNext : ∀ v ∈ insert z U, Cert (next v) v := by
    intro v hv
    rcases Finset.mem_insert.mp hv with rfl | hv
    · simpa only [nextZ] using certZ
    · simpa only [nextU v hv] using entries v (memU v hv)
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
  exact ⟨next, partNext, entriesNext, supportsNext⟩

theorem deficit_one_first_retention {α Ω : Type} [DecidableEq α]
    (roots : Finset α) (raw : α → Sig) (col : Sig → Set Ω) (need : Set Ω)
    (Cert : Finset α → Sig → Prop) (u : Bool) (T : Sig)
    (gateCol : ∀ d a b, allowed u d → col (bin d a b) ⊆ col a ∪ col b)
    (rowCover : ∀ k S, Live u T k S → ∀ o ∈ need, ∃ v ∈ S, o ∈ col v)
    (closed : ∀ A B a b d, Disjoint A B → allowed u d → a ≠ b → bin d a b ≠ a →
      bin d a b ≠ b → proper (bin d a b) → Cert A a → Cert B b → ColumnAdmissible roots raw col need (A ∪ B) (bin d a b) →
      Cert (A ∪ B) (bin d a b))
    {k : Nat} {S : Finset Sig} (run : Live u T k S) (deficit : S.card = k)
    (label : Sig → Finset α) (part : LabelPartition roots S label)
    (entries : ∀ v ∈ S, Cert (label v) v)
    (supports : ∀ v ∈ S, ColumnSupport raw col (label v) v) :
    ∃ (j : Nat) (U : Finset Sig) (a b : Sig) (d : Nat) (labels : Sig → Finset α),
      allowed u d ∧ proper a ∧ proper b ∧ a ≠ b ∧
      bin d a b ∉ insert a (insert b U) ∧ a ∈ U ∧ b ∉ U ∧
      Live u T j (insert (bin d a b) U) ∧ (insert (bin d a b) U).card = j + 1 ∧
      LabelPartition roots (insert a (insert b U)) labels ∧
      (∀ v ∈ insert a (insert b U), Cert (labels v) v) ∧
      (∀ v ∈ insert a (insert b U), ColumnSupport raw col (labels v) v) := by
  classical
  induction k generalizing S label with
  | zero =>
    obtain ⟨rfl, _⟩ := run
    simp at deficit
  | succ k ih =>
    obtain ⟨U, a, b, d, hd, rfl, pa, pb, hab, hfresh, tail⟩ := run
    have fresh : bin d a b ∉ U :=
      fun h => hfresh (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem h))
    have bound := live_size tail
    rw [Finset.card_insert_of_notMem fresh] at bound
    by_cases ha : a ∈ U
    · by_cases hb : b ∈ U
      · rw [Finset.insert_eq_of_mem hb, Finset.insert_eq_of_mem ha] at deficit
        omega
      · have tight : (insert (bin d a b) U).card = k + 1 := by
          rw [Finset.card_insert_of_notMem fresh]
          rw [Finset.insert_eq_of_mem (Finset.mem_insert_of_mem ha),
            Finset.card_insert_of_notMem hb] at deficit
          omega
        exact ⟨k, U, a, b, d, label, hd, pa, pb, hab, hfresh, ha, hb,
          tail, tight, part, entries, supports⟩
    · by_cases hb : b ∈ U
      · have tight : (insert (bin d a b) U).card = k + 1 := by
          rw [Finset.card_insert_of_notMem fresh]
          rw [Finset.insert_eq_of_mem hb, Finset.card_insert_of_notMem ha] at deficit
          omega
        have swapped : bin (flipOp d) b a = bin d a b := (bin_flip hd a b).symm
        refine ⟨k, U, b, a, flipOp d, label, (flip_flip hd).1, pb, pa,
          hab.symm, ?_, hb, ha, ?_, ?_, ?_, ?_, ?_⟩
        · simpa only [swapped, Finset.insert_comm] using hfresh
        · simpa only [swapped] using tail
        · simpa only [swapped] using tight
        · simpa only [Finset.insert_comm] using part
        · simpa only [Finset.insert_comm] using entries
        · simpa only [Finset.insert_comm] using supports
      · have ha' : a ∉ insert b U := by simp [ha, hab]
        have nextDeficit : (insert (bin d a b) U).card = k := by
          rw [Finset.card_insert_of_notMem fresh]
          rw [Finset.card_insert_of_notMem ha', Finset.card_insert_of_notMem hb] at deficit
          omega
        obtain ⟨next, nextPart, nextEntries, nextSupports⟩ :=
          merge_cert_state roots raw col need Cert u gateCol closed U a b d hd hab hfresh
            ha hb (live_proper tail _ (Finset.mem_insert_self _ _))
            (rowCover k _ tail) label part entries supports
        exact ih tail nextDeficit next nextPart nextEntries nextSupports

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

theorem sharing_cert2 {α Ω : Type} [DecidableEq α]
    (roots : Finset α) (raw : α → Sig) (col : Sig → Set Ω) (need : Set Ω)
    (Cert0 : Finset α → Sig → Prop) (Cert2 : Finset (Sum α Bool) → Sig → Prop)
    (u : Bool) (T : Sig)
    (gateCol : ∀ d a b, allowed u d → col (bin d a b) ⊆ col a ∪ col b)
    (rowCover : ∀ k S, Live u T k S → ∀ o ∈ need, ∃ v ∈ S, o ∈ col v)
    (U : Finset Sig) (a b : Sig) (d k : Nat) (label : Sig → Finset α)
    (hd : allowed u d) (pa : proper a) (pb : proper b) (hab : a ≠ b)
    (fresh : bin d a b ∉ insert a (insert b U)) (ha : a ∈ U) (hb : b ∉ U)
    (tail : Live u T k (insert (bin d a b) U))
    (tight : (insert (bin d a b) U).card = k + 1)
    (part : LabelPartition roots (insert a (insert b U)) label)
    (entries : ∀ v ∈ insert a (insert b U), Cert0 (label v) v)
    (supports : ∀ v ∈ insert a (insert b U), ColumnSupport raw col (label v) v)
    (leaves : ∀ t : Bool, Cert2 {Sum.inr t} a)
    (closed : ∀ A B v w e, Disjoint A B → allowed u e → v ≠ w →
      bin e v w ≠ v → bin e v w ≠ w → proper (bin e v w) →
      Cert2 A v → Cert2 B w →
      ColumnAdmissible (duplicateRoots roots (label a)) (duplicateRaw raw a) col need
        (A ∪ B) (bin e v w) → Cert2 (A ∪ B) (bin e v w))
    (bridge : ∀ B v, Cert0 B v → Disjoint (label a) B →
      ColumnAdmissible (duplicateRoots roots (label a)) (duplicateRaw raw a) col need
        (liftLabels B) v → Cert2 (liftLabels B) v) :
    Cert2 (duplicateRoots roots (label a)) T := by
  classical
  let z := bin d a b
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
  have part2 := sharing_partition roots U a b z label hab fresh ha hb part
  have supports2 := sharing_support raw col u gateCol U a b d hd fresh label supports
  have admissible2 := partition_admissible (duplicateRoots roots (label a))
    (duplicateRaw raw a) col need part2 supports2 (rowCover k _ tail)
  have preRun : Live u T (k + 1) (insert a (insert b U)) :=
    Live.binary hd pa pb hab fresh tail
  have certB : Cert2 (liftLabels (label b)) b :=
    bridge (label b) b (entries b memB) (part.2.1 a memA b memB hab)
      (duplicate_admissible roots raw col need part supports
        (rowCover (k + 1) _ preRun) a memA b memB hab.symm)
  have certZ : Cert2 (next z) z := by
    rw [nextZ]
    have disjoint : Disjoint ({Sum.inr true} : Finset (Sum α Bool)) (liftLabels (label b)) := by
      apply Finset.disjoint_left.mpr
      intro q hq hqb
      have eq := Finset.mem_singleton.mp hq
      subst q
      simpa [liftLabels] using hqb
    have admissible := admissible2 z (Finset.mem_insert_self _ _)
    change ColumnAdmissible (duplicateRoots roots (label a)) (duplicateRaw raw a) col need
      (next z) z at admissible
    rw [nextZ] at admissible
    simpa only [Finset.singleton_union] using
      closed {Sum.inr true} (liftLabels (label b)) a b d disjoint hd hab
        (fun h => fresh (h.symm ▸ memA)) (fun h => fresh (h.symm ▸ memB))
        (live_proper tail z (Finset.mem_insert_self _ _)) (leaves true) certB
        (by simpa only [Finset.singleton_union] using admissible)
  have entries2 : ∀ v ∈ insert z U, Cert2 (next v) v := by
    intro v hv
    rcases Finset.mem_insert.mp hv with rfl | hv
    · exact certZ
    · by_cases h : v = a
      · subst v
        simpa only [nextA] using leaves false
      · rw [nextU v hv h]
        apply bridge (label v) v (entries v (memU v hv))
          (part.2.1 a memA v (memU v hv) (Ne.symm h))
        have adm := admissible2 v (Finset.mem_insert_of_mem hv)
        change ColumnAdmissible (duplicateRoots roots (label a)) (duplicateRaw raw a) col need
          (next v) v at adm
        simpa only [nextU v hv h] using adm
  exact tight_closure_fresh_state (duplicateRoots roots (label a))
    (duplicateRaw raw a) col need Cert2 u T gateCol rowCover closed
    tail tight next part2 entries2 supports2

def CopyCertificate {α Ω : Type} [DecidableEq α]
    (roots : Finset α) (raw : α → Sig) (col : Sig → Set Ω) (need : Set Ω)
    (Cert0 : Finset α → Sig → Prop) (u : Bool) (T : Sig) (A : Finset α) (w : Sig) : Prop :=
  ∃ Cert2 : Finset (Sum α Bool) → Sig → Prop,
    (∀ t : Bool, Cert2 {Sum.inr t} w) ∧
    (∀ B C a b d, Disjoint B C → allowed u d → a ≠ b → bin d a b ≠ a →
      bin d a b ≠ b → proper (bin d a b) → Cert2 B a → Cert2 C b →
      ColumnAdmissible (duplicateRoots roots A) (duplicateRaw raw w) col need
        (B ∪ C) (bin d a b) → Cert2 (B ∪ C) (bin d a b)) ∧
    (∀ B v, Cert0 B v → Disjoint A B →
      ColumnAdmissible (duplicateRoots roots A) (duplicateRaw raw w) col need
        (liftLabels B) v → Cert2 (liftLabels B) v) ∧
    ¬ Cert2 (duplicateRoots roots A) T

theorem deficit_one_exclusion_state {α Ω : Type} [DecidableEq α]
    (roots : Finset α) (raw : α → Sig) (col : Sig → Set Ω) (need : Set Ω)
    (Cert0 : Finset α → Sig → Prop) (u : Bool) (T : Sig)
    (gateCol : ∀ d a b, allowed u d → col (bin d a b) ⊆ col a ∪ col b)
    (rowCover : ∀ k S, Live u T k S → ∀ o ∈ need, ∃ v ∈ S, o ∈ col v)
    (closed : ∀ A B a b d, Disjoint A B → allowed u d → a ≠ b → bin d a b ≠ a →
      bin d a b ≠ b → proper (bin d a b) → Cert0 A a → Cert0 B b →
      ColumnAdmissible roots raw col need (A ∪ B) (bin d a b) → Cert0 (A ∪ B) (bin d a b))
    (copies : ∀ A w, A ⊆ roots → proper w → Cert0 A w →
      CopyCertificate roots raw col need Cert0 u T A w)
    {k : Nat} {S : Finset Sig} (run : Live u T k S) (deficit : S.card = k)
    (label : Sig → Finset α) (part : LabelPartition roots S label)
    (entries : ∀ v ∈ S, Cert0 (label v) v)
    (supports : ∀ v ∈ S, ColumnSupport raw col (label v) v) : False := by
  obtain ⟨j, U, a, b, d, labels, hd, pa, pb, hab, fresh, ha, hb,
    tail, tight, part2, entries2, supports2⟩ :=
    deficit_one_first_retention roots raw col need Cert0 u T gateCol rowCover closed
      run deficit label part entries supports
  obtain ⟨Cert2, leaves, closed2, bridge, missing⟩ :=
    copies (labels a) a (part2.1 a (by simp)) pa (entries2 a (by simp))
  exact missing (sharing_cert2 roots raw col need Cert0 Cert2 u T gateCol rowCover
    U a b d j labels hd pa pb hab fresh ha hb tail tight part2 entries2 supports2
    leaves closed2 bridge)

theorem initial_cert_state {α Ω : Type} [DecidableEq α]
    (roots : Finset α) (raw : α → Sig) (col : Sig → Set Ω)
    (Cert : Finset α → Sig → Prop)
    (distinct : Set.InjOn raw (↑roots : Set α))
    (initial : ∀ r ∈ roots, Cert {r} (raw r)) :
    ∃ label : Sig → Finset α, LabelPartition roots (roots.image raw) label ∧
      (∀ v ∈ roots.image raw, Cert (label v) v) ∧
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
  have entries : ∀ v ∈ roots.image raw, Cert (label v) v := by
    intro v hv
    obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hv
    simpa only [leaf r hr] using initial r hr
  have supports : ∀ v ∈ roots.image raw, ColumnSupport raw col (label v) v := by
    intro v hv o ho
    obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hv
    exact ⟨r, Finset.mem_filter.mpr ⟨hr, rfl⟩, ho⟩
  exact ⟨label, part, entries, supports⟩

theorem deficit_one_closure_exclusion {α Ω : Type} [DecidableEq α]
    (roots : Finset α) (raw : α → Sig) (col : Sig → Set Ω) (need : Set Ω)
    (Cert0 : Finset α → Sig → Prop) (u : Bool) (T : Sig) (cap : Nat)
    (distinct : Set.InjOn raw (↑roots : Set α))
    (initial : ∀ r ∈ roots, Cert0 {r} (raw r))
    (gateCol : ∀ d a b, allowed u d → col (bin d a b) ⊆ col a ∪ col b)
    (rowCover : ∀ k S, Live u T k S → ∀ o ∈ need, ∃ v ∈ S, o ∈ col v)
    (closed : ∀ A B a b d, Disjoint A B → allowed u d → a ≠ b → bin d a b ≠ a →
      bin d a b ≠ b → proper (bin d a b) → Cert0 A a → Cert0 B b →
      ColumnAdmissible roots raw col need (A ∪ B) (bin d a b) → Cert0 (A ∪ B) (bin d a b))
    (copies : ∀ A w, A ⊆ roots → proper w → Cert0 A w →
      CopyCertificate roots raw col need Cert0 u T A w)
    (width : (roots.image raw).card = cap) (missing : ¬ Cert0 roots T) :
    Impossible u T cap (roots.image raw) := by
  intro k hk run
  obtain ⟨label, part, entries, supports⟩ := initial_cert_state roots raw col Cert0 distinct initial
  have bound := live_size run
  by_cases tight : (roots.image raw).card = k + 1
  · exact missing (tight_closure_fresh_state roots raw col need Cert0 u T gateCol rowCover closed
      run tight label part entries supports)
  · have deficit : (roots.image raw).card = k := by omega
    exact deficit_one_exclusion_state roots raw col need Cert0 u T gateCol rowCover closed copies
      run deficit label part entries supports


abbrev tableCert {α : Type} [DecidableEq α] (table : Finset (Finset α × Sig))
    (A : Finset α) (v : Sig) : Prop := (A, v) ∈ table

abbrev rowRejected {α Ω : Type} [DecidableEq α]
    (roots : Finset α) (raw : α → Sig) (col : Sig → Ω → Bool) (need : Ω → Bool)
    (A : Finset α) (v : Sig) (o : Ω) : Prop :=
  need o = true ∧ col v o = false ∧ ∀ r ∈ roots, r ∉ A → col (raw r) o = false

theorem rowRejected_not_admissible {α Ω : Type} [DecidableEq α]
    (roots : Finset α) (raw : α → Sig) (col : Sig → Ω → Bool) (need : Ω → Bool)
    (A : Finset α) (v : Sig) (o : Ω) (rejected : rowRejected roots raw col need A v o) :
    ¬ ColumnAdmissible roots raw (fun w => {q | col w q = true}) {q | need q = true} A v := by
  intro admissible
  have bad := admissible o rejected.1 (by
    intro r hr outside
    change col (raw r) o ≠ true
    rw [rejected.2.2 r hr outside]
    decide)
  change col v o = true at bad
  rw [rejected.2.1] at bad
  cases bad

def witnessClosedCheck {α Ω : Type} [DecidableEq α]
    (roots : Finset α) (raw : α → Sig) (col : Sig → Ω → Bool) (need : Ω → Bool)
    (table : Finset (Finset α × Sig)) (u : Bool)
    (witness : (Finset α × Sig) → (Finset α × Sig) → Nat → Ω) : Bool :=
  @decide (∀ p ∈ table, ∀ q ∈ table, ∀ d ∈ Finset.range 4,
    (Disjoint p.1 q.1 ∧ allowed u d ∧ p.2 ≠ q.2 ∧
      bin d p.2 q.2 ≠ p.2 ∧ bin d p.2 q.2 ≠ q.2 ∧ proper (bin d p.2 q.2)) →
      tableCert table (p.1 ∪ q.1) (bin d p.2 q.2) ∨
      rowRejected roots raw col need (p.1 ∪ q.1) (bin d p.2 q.2) (witness p q d))
    (by unfold allowed proper; infer_instance)

theorem witnessClosedCheck_sound {α Ω : Type} [DecidableEq α]
    (roots : Finset α) (raw : α → Sig) (col : Sig → Ω → Bool) (need : Ω → Bool)
    (table : Finset (Finset α × Sig)) (u : Bool)
    (witness : (Finset α × Sig) → (Finset α × Sig) → Nat → Ω)
    (checked : witnessClosedCheck roots raw col need table u witness = true) :
    ∀ A B a b d, Disjoint A B → allowed u d → a ≠ b →
      bin d a b ≠ a → bin d a b ≠ b → proper (bin d a b) →
      tableCert table A a → tableCert table B b →
      ColumnAdmissible roots raw (fun w => {q | col w q = true}) {q | need q = true}
        (A ∪ B) (bin d a b) → tableCert table (A ∪ B) (bin d a b) := by
  intro A B a b d hAB hd hab hza hzb hz hA hB admissible
  simp only [witnessClosedCheck, decide_eq_true_eq] at checked
  have limit : d < 4 := by
    rcases allowed_four hd with rfl | rfl | ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> decide
  rcases checked (A, a) hA (B, b) hB d (Finset.mem_range.mpr limit)
    ⟨hAB, hd, hab, hza, hzb, hz⟩ with entry | rejected
  · exact entry
  · exact False.elim
      (rowRejected_not_admissible roots raw col need (A ∪ B) (bin d a b)
        (witness (A, a) (B, b) d) rejected admissible)

def witnessBridgeCheck {α β Ω : Type} [DecidableEq α] [DecidableEq β]
    (roots : Finset β) (raw : β → Sig) (col : Sig → Ω → Bool) (need : Ω → Bool)
    (lift : Finset α → Finset β) (A : Finset α)
    (source : Finset (Finset α × Sig)) (target : Finset (Finset β × Sig))
    (witness : (Finset α × Sig) → Ω) : Bool :=
  decide (∀ p ∈ source, Disjoint A p.1 → tableCert target (lift p.1) p.2 ∨
    rowRejected roots raw col need (lift p.1) p.2 (witness p))

theorem witnessBridgeCheck_sound {α β Ω : Type} [DecidableEq α] [DecidableEq β]
    (roots : Finset β) (raw : β → Sig) (col : Sig → Ω → Bool) (need : Ω → Bool)
    (lift : Finset α → Finset β) (A : Finset α)
    (source : Finset (Finset α × Sig)) (target : Finset (Finset β × Sig))
    (witness : (Finset α × Sig) → Ω)
    (checked : witnessBridgeCheck roots raw col need lift A source target witness = true) :
    ∀ B v, tableCert source B v → Disjoint A B →
      ColumnAdmissible roots raw (fun w => {q | col w q = true}) {q | need q = true} (lift B) v →
      tableCert target (lift B) v := by
  intro B v entry disjoint admissible
  simp only [witnessBridgeCheck, decide_eq_true_eq] at checked
  rcases checked (B, v) entry disjoint with found | rejected
  · exact found
  · exact False.elim
      (rowRejected_not_admissible roots raw col need (lift B) v (witness (B, v))
        rejected admissible)
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Terminal0
abbrev Pair := Fin 225
def roots : Finset (Fin 12) := Finset.univ
def s0 : Sig := 0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa
def s1 : Sig := 0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc
def s2 : Sig := 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0
def s3 : Sig := 0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00
def s4 : Sig := 0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000
def s5 : Sig := 0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000
def s6 : Sig := 0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000
def s7 : Sig := 0xffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000
def s8 : Sig := 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000000000000000000000000000000000000
def s9 : Sig := 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
def s10 : Sig := 0x8888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888
def s11 : Sig := 0xf8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8
def s12 : Sig := 0xf800f800f800f800f800f800f800f800f800f800f800f800f800f800f800f800f800f800f800f800f800f800f800f800f800f800f800f800f800f800f800f800f800f800f800f800f800f800f800f800f800f800f800f800f800f800f800f800f800f800f800f800f800f800f800f800f800f800f800f800f800f800f800f800
def s13 : Sig := 0xfaaafaaafaaafaaafaaafaaafaaafaaafaaafaaafaaafaaafaaafaaafaaafaaafaaafaaafaaafaaafaaafaaafaaafaaafaaafaaafaaafaaafaaafaaafaaafaaafaaafaaafaaafaaafaaafaaafaaafaaafaaafaaafaaafaaafaaafaaafaaafaaafaaafaaafaaafaaafaaafaaafaaafaaafaaafaaafaaafaaafaaafaaafaaafaaa
def s14 : Sig := 0xfffffffffaaafaaafffffffffaaafaaafffffffffaaafaaafffffffffaaafaaafffffffffaaafaaafffffffffaaafaaafffffffffaaafaaafffffffffaaafaaafffffffffaaafaaafffffffffaaafaaafffffffffaaafaaafffffffffaaafaaafffffffffaaafaaafffffffffaaafaaafffffffffaaafaaafffffffffaaafaaa
def s15 : Sig := 0xfffffffffffffffffffffffffffffffffaaafaaafaaafaaafaaafaaafaaafaaafffffffffffffffffffffffffffffffffaaafaaafaaafaaafaaafaaafaaafaaafffffffffffffffffffffffffffffffffaaafaaafaaafaaafaaafaaafaaafaaafffffffffffffffffffffffffffffffffaaafaaafaaafaaafaaafaaafaaafaaa
def s16 : Sig := 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000ffffffffffffffff0000000000000000
def s17 : Sig := 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc8fffffffffffffffffffffffffffffffffffffffffffffffffffffaeafffff8c8fffffffffffffffffffffffffffafff8ffffffffffffffffffffffffffeaffc8fffffffffffefcfcfffffffffffaf8f8ffeefeeeffeefcccffeafaeaffeaf8c8
def s18 : Sig := 0xfffffffffaaafaaafffffffffaaafaaafaaafaaafaaafaaafaaafaaafaaafaaafffffffffaaafaaafffffffffaaafaaafaaafaaafaaafaaafaaafaaafaaafaaafffffffffaaafaaafffffffffaaafaaafaaafaaafaaafaaafaaafaaafaaafaaafffffffffaaafaaafffffffffaaafaaafaaafaaafaaafaaafaaafaaafaaafaaa
def s19 : Sig := 0xffffffffccccccccffffffffccccccccffffffffccccccccffffffffccccccccffffffffccccccccffffffffccccccccffffffffccccccccffffffffccccccccffffffffccccccccffffffffccccccccffffffffccccccccffffffffccccccccffffffffccccccccffffffffccccccccffffffffccccccccffffffffcccccccc
def s20 : Sig := 0xffffffffffffffffffffffffffffffffccccccccccccccccccccccccccccccccffffffffffffffffffffffffffffffffccccccccccccccccccccccccccccccccffffffffffffffffffffffffffffffffccccccccccccccccccccccccccccccccffffffffffffffffffffffffffffffffcccccccccccccccccccccccccccccccc
def s21 : Sig := 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc
def s22 : Sig := 0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc0000000000000000cccccccccccccccc0000000000000000cccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc0000000000000000cccccccccccccccc0000000000000000
def s23 : Sig := 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffccccccccccccccccffffffffffffffffccccccccccccccccffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffccccccccccccccccffffffffffffffffcccccccccccccccc
def s24 : Sig := 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffcccccccccccccccc0000000000000000cccccccccccccccc0000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffcccccccccccccccc0000000000000000cccccccccccccccc0000000000000000
def s25 : Sig := 0xffffffffccccccccffffffffccccccccffffffffccccccccffffffffccccccccffffffffccccccccffffffff00000000ffffffffccccccccffffffff00000000ffffffffccccccccffffffffccccccccffffffffccccccccffffffffccccccccffffffffccccccccffffffff00000000ffffffffccccccccffffffff00000000
def s26 : Sig := 0xffffffffffffffffffffffffffffffffccccccccccccccccccccccccccccccccffffffffffffffffffffffffffffffffcccccccccccccccc0000000000000000ffffffffffffffffffffffffffffffffccccccccccccccccccccccccccccccccffffffffffffffffffffffffffffffffcccccccccccccccc0000000000000000
def s27 : Sig := 0xfffffffffffffffffffffffffffffffffeeefeeefeeefeeefeeefeeefeeefeeefffffffffffffffffffffffffffffffffeeefeeefeeefeeefaaafaaafaaafaaafffffffffffffffffffffffffffffffffeeefeeefeeefeeefeeefeeefeeefeeefffffffffffffffffffffffffffffffffeeefeeefeeefeeefaaafaaafaaafaaa
def s28 : Sig := 0xfffffffffaaafaaafffffffffaaafaaafeeefeeefaaafaaafeeefeeefaaafaaafffffffffaaafaaafffffffffaaafaaafeeefeeefaaafaaafaaafaaafaaafaaafffffffffaaafaaafffffffffaaafaaafeeefeeefaaafaaafeeefeeefaaafaaafffffffffaaafaaafffffffffaaafaaafeeefeeefaaafaaafaaafaaafaaafaaa
def s29 : Sig := 0xfffffffffafafafafffffffffafafafafffffffffafafafafffffffffafafafafffffffffafafafafffffffffafafafafffffffffafafafafffffffffafafafafffffffffafafafafffffffffafafafafffffffffafafafafffffffffafafafafffffffffafafafafffffffffafafafafffffffffafafafafffffffffafafafa
def s30 : Sig := 0xf8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f80000000000000000f8f8f8f8f8f8f8f80000000000000000f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f80000000000000000f8f8f8f8f8f8f8f80000000000000000
def s31 : Sig := 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff8f8f8f8f8f8f8f8fffffffffffffffff8f8f8f8f8f8f8f8fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff8f8f8f8f8f8f8f8fffffffffffffffff8f8f8f8f8f8f8f8
def s32 : Sig := 0xfffffffffafafafafffffffffafafafafaaafaaafaaafaaafaaafaaafaaafaaafffffffffafafafafffffffffafafafafaaafaaafaaafaaafaaafaaafaaafaaafffffffffafafafafffffffffafafafafaaafaaafaaafaaafaaafaaafaaafaaafffffffffafafafafffffffffafafafafaaafaaafaaafaaafaaafaaafaaafaaa
def s33 : Sig := 0xfffffffffafafafafffffffffafafafafffffffffafafafafffffffffafafafafffffffffafafafafffffffffaaafaaafffffffffafafafafffffffffaaafaaafffffffffafafafafffffffffafafafafffffffffafafafafffffffffafafafafffffffffafafafafffffffffaaafaaafffffffffafafafafffffffffaaafaaa
def s34 : Sig := 0xccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc8c8c8c8c8c8c8c8ccccccccccccccccc8c8c8c8c8c8c8c8ccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc8c8c8c8c8c8c8c8ccccccccccccccccc8c8c8c8c8c8c8c8
def s35 : Sig := 0xfffffffffafafafafffffffffafafafafaaafaaafaaafaaafaaafaaafaaafaaafffffffffafafafafffffffffaaafaaafaaafaaafaaafaaafaaafaaafaaafaaafffffffffafafafafffffffffafafafafaaafaaafaaafaaafaaafaaafaaafaaafffffffffafafafafffffffffaaafaaafaaafaaafaaafaaafaaafaaafaaafaaa
def s36 : Sig := 0xffffffffffaaffaaffffffffffaaffaaffffffffffaaffaaffffffffffaaffaaffffffffffaaffaaffffffffffaaffaaffffffffffaaffaaffffffffffaaffaaffffffffffaaffaaffffffffffaaffaaffffffffffaaffaaffffffffffaaffaaffffffffffaaffaaffffffffffaaffaaffffffffffaaffaaffffffffffaaffaa
def s37 : Sig := 0xffffffffffffffffff00ff00ff00ff00ffffffffffffffffff00ff00ff00ff00ffffffffffffffffff00ff00ff00ff00ffffffffffffffffff00ff00ff00ff00ffffffffffffffffff00ff00ff00ff00ffffffffffffffffff00ff00ff00ff00ffffffffffffffffff00ff00ff00ff00ffffffffffffffffff00ff00ff00ff00
def s38 : Sig := 0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff000000000000000000ff00ff00ff00ff000000000000000000ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff000000000000000000ff00ff00ff00ff000000000000000000
def s39 : Sig := 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff00ff00ff00ff00ffffffffffffffffff00ff00ff00ff00ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff00ff00ff00ff00ffffffffffffffffff00ff00ff00ff00
def s40 : Sig := 0xffffffffffaaffaaffffffffffaaffaafaaafaaafaaafaaafaaafaaafaaafaaaffffffffffaaffaaffffffffffaaffaafaaafaaafaaafaaafaaafaaafaaafaaaffffffffffaaffaaffffffffffaaffaafaaafaaafaaafaaafaaafaaafaaafaaaffffffffffaaffaaffffffffffaaffaafaaafaaafaaafaaafaaafaaafaaafaaa
def s41 : Sig := 0xffffffffffffffffff00ff00ff00ff00ffffffffffffffffff00ff00ff00ff00ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffffff00ff00ff00ff00ffffffffffffffffff00ff00ff00ff00ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000
def s42 : Sig := 0xffffffffffaaffaaffffffffffaaffaaffffffffffaaffaaffffffffffaaffaaffffffffffaaffaafffffffffaaafaaaffffffffffaaffaafffffffffaaafaaaffffffffffaaffaaffffffffffaaffaaffffffffffaaffaaffffffffffaaffaaffffffffffaaffaafffffffffaaafaaaffffffffffaaffaafffffffffaaafaaa
def s43 : Sig := 0xffffffffffffffffffffffffffffffffff00ff00ff00ff00ff00ff00ff00ff00ffffffffffffffffffffffffffffffffff00ff00ff00ff000000000000000000ffffffffffffffffffffffffffffffffff00ff00ff00ff00ff00ff00ff00ff00ffffffffffffffffffffffffffffffffff00ff00ff00ff000000000000000000
def s44 : Sig := 0xffffffffffaaffaaffffffffffaaffaafaaafaaafaaafaaafaaafaaafaaafaaaffffffffffaaffaafffffffffaaafaaafaaafaaafaaafaaafaaafaaafaaafaaaffffffffffaaffaaffffffffffaaffaafaaafaaafaaafaaafaaafaaafaaafaaaffffffffffaaffaafffffffffaaafaaafaaafaaafaaafaaafaaafaaafaaafaaa
def s45 : Sig := 0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000
def s46 : Sig := 0xffff0000faaa0000ffff0000faaa0000ffff0000faaa0000ffff0000faaa0000ffff0000faaa0000ffff0000faaa0000ffff0000faaa0000ffff0000faaa0000ffff0000faaa0000ffff0000faaa0000ffff0000faaa0000ffff0000faaa0000ffff0000faaa0000ffff0000faaa0000ffff0000faaa0000ffff0000faaa0000
def s47 : Sig := 0xffffffffffffffffffffffffffffffffffff0000ffff0000ffff0000ffff0000ffffffffffffffffffffffffffffffffffff0000ffff0000ffff0000ffff0000ffffffffffffffffffffffffffffffffffff0000ffff0000ffff0000ffff0000ffffffffffffffffffffffffffffffffffff0000ffff0000ffff0000ffff0000
def s48 : Sig := 0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff00000000000000000000ffff0000ffff00000000000000000000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff00000000000000000000ffff0000ffff00000000000000000000
def s49 : Sig := 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000ffff0000ffffffffffffffffffff0000ffff0000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000ffff0000ffffffffffffffffffff0000ffff0000
def s50 : Sig := 0xfffffffffaaa0000fffffffffaaa0000fffffffffaaa0000fffffffffaaa0000fffffffffaaa0000fffffffffaaa0000fffffffffaaa0000fffffffffaaa0000fffffffffaaa0000fffffffffaaa0000fffffffffaaa0000fffffffffaaa0000fffffffffaaa0000fffffffffaaa0000fffffffffaaa0000fffffffffaaa0000
def s51 : Sig := 0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffff00000000ffffffffffff0000ffffffff00000000ffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffff00000000ffffffffffff0000ffffffff00000000
def s52 : Sig := 0xffffffffffffffffffffffffffffffffffff0000ffff0000ffff0000ffff0000ffffffffffffffffffffffffffffffffffff0000ffff00000000000000000000ffffffffffffffffffffffffffffffffffff0000ffff0000ffff0000ffff0000ffffffffffffffffffffffffffffffffffff0000ffff00000000000000000000
def s53 : Sig := 0xfffffffffaaafaaafffffffffaaafaaafffffffffaaafaaafffffffffaaafaaafffffffffaaafaaaffff0000faaa0000fffffffffaaafaaaffff0000faaa0000fffffffffaaafaaafffffffffaaafaaafffffffffaaafaaafffffffffaaafaaafffffffffaaafaaaffff0000faaa0000fffffffffaaafaaaffff0000faaa0000
def s54 : Sig := 0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000
def s55 : Sig := 0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000ffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000ffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000ffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000
def s56 : Sig := 0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff000000000000000000000000ffffffff000000000000000000000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff000000000000000000000000ffffffff000000000000000000000000
def s57 : Sig := 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000
def s58 : Sig := 0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000
def s59 : Sig := 0xfffffffff8f8f8f8fffffffff8f8f8f8fffffffff8f8f8f8fffffffff8f8f8f8fffffffff8f8f8f8f8f8f8f8f8f8f8f8fffffffff8f8f8f8f8f8f8f8f8f8f8f8fffffffff8f8f8f8fffffffff8f8f8f8fffffffff8f8f8f8fffffffff8f8f8f8fffffffff8f8f8f8f8f8f8f8f8f8f8f8fffffffff8f8f8f8f8f8f8f8f8f8f8f8
def s60 : Sig := 0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000ffffffffffffffffffffffffffffffffffffffff000000000000000000000000ffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000ffffffffffffffffffffffffffffffffffffffff000000000000000000000000
def s61 : Sig := 0xfffffffffaaafaaafffffffffaaafaaafffffffffaaafaaafffffffffaaafaaafffffffffaaafaaa0000000000000000fffffffffaaafaaa0000000000000000fffffffffaaafaaafffffffffaaafaaafffffffffaaafaaafffffffffaaafaaafffffffffaaafaaa0000000000000000fffffffffaaafaaa0000000000000000
def s62 : Sig := 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffaaafaaafffffffffffffffffffffffffaaafaaafffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffaaafaaafffffffffffffffffffffffffaaafaaa
def s63 : Sig := 0xfffffffffffffffffffffffffffffffffaaafaaafaaafaaafaaafaaafaaafaaafffffffffffffffffffffffffaaafaaafaaafaaafaaafaaafaaafaaafaaafaaafffffffffffffffffffffffffffffffffaaafaaafaaafaaafaaafaaafaaafaaafffffffffffffffffffffffffaaafaaafaaafaaafaaafaaafaaafaaafaaafaaa
def s64 : Sig := 0xffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffff000000000000000000000000000000000000000000000000
def s65 : Sig := 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000
def s66 : Sig := 0xfffffffffffffffffffffffffffffffffaaafaaafaaafaaafaaafaaafaaafaaaffffffffffffffff0000000000000000faaafaaafaaafaaa0000000000000000fffffffffffffffffffffffffffffffffaaafaaafaaafaaafaaafaaafaaafaaaffffffffffffffff0000000000000000faaafaaafaaafaaa0000000000000000
def s67 : Sig := 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffaaafaaafaaafaaafffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffaaafaaafaaafaaa
def s68 : Sig := 0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000faaafaaa00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000faaafaaa00000000
def s69 : Sig := 0xfffffffffaaafaaafffffffffaaafaaafffffffffaaafaaafffffffffaaafaaafffffffffaaafaaafffffffffaaafaaafffffffffaaafaaafaaafaaafaaafaaafffffffffaaafaaafffffffffaaafaaafffffffffaaafaaafffffffffaaafaaafffffffffaaafaaafffffffffaaafaaafffffffffaaafaaafaaafaaafaaafaaa
def s70 : Sig := 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffaaafaaafaaafaaafaaafaaafaaafaaafffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffaaafaaafaaafaaafaaafaaafaaafaaa
def s71 : Sig := 0xfffffffffaaafaaafffffffffaaafaaafffffffffaaafaaafffffffffaaafaaafffffffffaaafaaafffffffffaaafaaafaaafaaafaaafaaafaaafaaafaaafaaafffffffffaaafaaafffffffffaaafaaafffffffffaaafaaafffffffffaaafaaafffffffffaaafaaafffffffffaaafaaafaaafaaafaaafaaafaaafaaafaaafaaa
def s72 : Sig := 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffaaafaaafffffffffaaafaaafffffffffaaafaaafffffffffaaafaaafffffffffaaafaaafffffffffaaafaaafffffffffaaafaaafffffffffaaafaaa
def s73 : Sig := 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000000000000000000000000000000000000
def s74 : Sig := 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000ffffffffffffffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
def s75 : Sig := 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000ffffffffffffffff0000000000000000
def s76 : Sig := 0xfffffffffffffffffffffffffffffffffaaafaaafaaafaaafaaafaaafaaafaaafffffffffffffffffffffffffffffffffaaafaaafaaafaaafaaafaaafaaafaaafffffffffaaafaaafffffffffaaafaaafaaafaaafaaafaaafaaafaaafaaafaaafffffffffaaafaaafffffffffaaafaaafaaafaaafaaafaaafaaafaaafaaafaaa
def s77 : Sig := 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000000000000000000000000000000000000
def s78 : Sig := 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffaaafaaafffffffffffffffffffffffffaaafaaafffffffffaaafaaafffffffffaaafaaafffffffffaaafaaafffffffffaaafaaafffffffffaaafaaafffffffffaaafaaafffffffffaaafaaafffffffffaaafaaa
def s79 : Sig := 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffaaafaaafaaafaaafffffffffffffffffffffffffffffffffaaafaaafaaafaaafaaafaaafaaafaaafffffffffffffffffffffffffffffffffaaafaaafaaafaaafaaafaaafaaafaaa
def s80 : Sig := 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffaaafaaafffffffffffffffffaaafaaafaaafaaafffffffffaaafaaafffffffffaaafaaafaaafaaafaaafaaafaaafaaafaaafaaafffffffffaaafaaafffffffffaaafaaafaaafaaafaaafaaafaaafaaafaaafaaa
def s81 : Sig := 0xfffffffffffffffffffffffffffffffffaaafaaafaaafaaafaaafaaafaaafaaafffffffffffffffffffffffffaaafaaafaaafaaafaaafaaafaaafaaafaaafaaafffffffffaaafaaafffffffffaaafaaafaaafaaafaaafaaafaaafaaafaaafaaafffffffffaaafaaafffffffffaaafaaafaaafaaafaaafaaafaaafaaafaaafaaa
def s82 : Sig := 0xfffffffffaaafaaafffffffffaaafaaafffffffffaaafaaafffffffffaaafaaafffffffffaaafaaafffffffffaaafaaafffffffffaaafaaafaaafaaafaaafaaafffffffffaaafaaafffffffffaaafaaafaaafaaafaaafaaafaaafaaafaaafaaafffffffffaaafaaafffffffffaaafaaafaaafaaafaaafaaafaaafaaafaaafaaa
def s83 : Sig := 0xfffffffffaaafaaafffffffffaaafaaafaaafaaafaaafaaafaaafaaafaaafaaafffffffffaaafaaa0000000000000000faaafaaafaaafaaa0000000000000000fffffffffaaafaaafffffffffaaafaaafaaafaaafaaafaaafaaafaaafaaafaaafffffffffaaafaaa0000000000000000faaafaaafaaafaaa0000000000000000
def s84 : Sig := 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffaaafaaafffffffffffffffffaaafaaafaaafaaafffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffaaafaaafffffffffffffffffaaafaaafaaafaaa
def rawValues : Array Sig := #[s1, s11, s3, s4, s5, s14, s6, s7, s15, s8, s16, s9]
def raw (i : Fin 12) : Sig := rawValues.getD i.val zero
def positiveRows : Array Row := #[3, 6, 12, 24, 17, 33, 66, 132, 264, 528, 160, 640, 576, 320, 288]
def negativeRows : Array Row := #[50, 69, 104, 116, 138, 201, 208, 276, 385, 402, 521, 548, 554, 770, 773]
def positive (i : Pair) : Row := positiveRows.getD (i.val / 15) 0
def negative (i : Pair) : Row := negativeRows.getD (i.val % 15) 0
def need (_ : Pair) : Bool := true
def col (v : Sig) (i : Pair) : Bool := bit (positive i) v && !(bit (negative i) v)
def oldTable : Finset (Finset (Fin 12) × Sig) := {
  ({0}, s1),
  ({1}, s11),
  ({2}, s3),
  ({3}, s4),
  ({4}, s5),
  ({5}, s14),
  ({6}, s6),
  ({7}, s7),
  ({8}, s15),
  ({9}, s8),
  ({10}, s16),
  ({11}, s9),
  ({5, 8}, s18)}

def copyTable0 : Finset (Finset (Sum (Fin 12) Bool) × Sig) := {
  ({Sum.inl 1}, s11),
  ({Sum.inl 2}, s3),
  ({Sum.inl 3}, s4),
  ({Sum.inl 4}, s5),
  ({Sum.inl 5}, s14),
  ({Sum.inl 6}, s6),
  ({Sum.inl 7}, s7),
  ({Sum.inl 8}, s15),
  ({Sum.inl 9}, s8),
  ({Sum.inl 10}, s16),
  ({Sum.inl 11}, s9),
  ({Sum.inr false}, s1),
  ({Sum.inr true}, s1),
  ({Sum.inl 5, Sum.inl 8}, s18),
  ({Sum.inl 4, Sum.inr false}, s19),
  ({Sum.inl 7, Sum.inr false}, s20),
  ({Sum.inl 9, Sum.inr false}, s21),
  ({Sum.inl 10, Sum.inr false}, s22),
  ({Sum.inl 10, Sum.inr false}, s23),
  ({Sum.inl 4, Sum.inr true}, s19),
  ({Sum.inl 7, Sum.inr true}, s20),
  ({Sum.inl 9, Sum.inr true}, s21),
  ({Sum.inl 10, Sum.inr true}, s22),
  ({Sum.inl 10, Sum.inr true}, s23),
  ({Sum.inl 9, Sum.inl 10, Sum.inr false}, s24),
  ({Sum.inl 4, Sum.inl 10, Sum.inr false}, s25),
  ({Sum.inl 7, Sum.inl 10, Sum.inr false}, s26),
  ({Sum.inl 8, Sum.inl 10, Sum.inr false}, s27),
  ({Sum.inl 9, Sum.inl 10, Sum.inr true}, s24),
  ({Sum.inl 4, Sum.inl 10, Sum.inr true}, s25),
  ({Sum.inl 7, Sum.inl 10, Sum.inr true}, s26),
  ({Sum.inl 8, Sum.inl 10, Sum.inr true}, s27),
  ({Sum.inl 5, Sum.inl 8, Sum.inl 10, Sum.inr false}, s28),
  ({Sum.inl 5, Sum.inl 8, Sum.inl 10, Sum.inr true}, s28)}

def copyTable1 : Finset (Finset (Sum (Fin 12) Bool) × Sig) := {
  ({Sum.inl 0}, s1),
  ({Sum.inl 2}, s3),
  ({Sum.inl 3}, s4),
  ({Sum.inl 4}, s5),
  ({Sum.inl 5}, s14),
  ({Sum.inl 6}, s6),
  ({Sum.inl 7}, s7),
  ({Sum.inl 8}, s15),
  ({Sum.inl 9}, s8),
  ({Sum.inl 10}, s16),
  ({Sum.inl 11}, s9),
  ({Sum.inr false}, s11),
  ({Sum.inr true}, s11),
  ({Sum.inl 5, Sum.inl 8}, s18),
  ({Sum.inl 5, Sum.inr false}, s29),
  ({Sum.inl 10, Sum.inr false}, s30),
  ({Sum.inl 10, Sum.inr false}, s31),
  ({Sum.inl 5, Sum.inr true}, s29),
  ({Sum.inl 10, Sum.inr true}, s30),
  ({Sum.inl 10, Sum.inr true}, s31),
  ({Sum.inl 5, Sum.inl 8, Sum.inr false}, s32),
  ({Sum.inl 5, Sum.inl 10, Sum.inr false}, s33),
  ({Sum.inl 0, Sum.inl 10, Sum.inr false}, s34),
  ({Sum.inl 5, Sum.inl 8, Sum.inr true}, s32),
  ({Sum.inl 5, Sum.inl 10, Sum.inr true}, s33),
  ({Sum.inl 0, Sum.inl 10, Sum.inr true}, s34),
  ({Sum.inl 5, Sum.inl 8, Sum.inl 10, Sum.inr false}, s35),
  ({Sum.inl 5, Sum.inl 8, Sum.inl 10, Sum.inr true}, s35)}

def copyTable2 : Finset (Finset (Sum (Fin 12) Bool) × Sig) := {
  ({Sum.inl 0}, s1),
  ({Sum.inl 1}, s11),
  ({Sum.inl 3}, s4),
  ({Sum.inl 4}, s5),
  ({Sum.inl 5}, s14),
  ({Sum.inl 6}, s6),
  ({Sum.inl 7}, s7),
  ({Sum.inl 8}, s15),
  ({Sum.inl 9}, s8),
  ({Sum.inl 10}, s16),
  ({Sum.inl 11}, s9),
  ({Sum.inr false}, s3),
  ({Sum.inr true}, s3),
  ({Sum.inl 5, Sum.inl 8}, s18),
  ({Sum.inl 5, Sum.inr false}, s36),
  ({Sum.inl 6, Sum.inr false}, s37),
  ({Sum.inl 10, Sum.inr false}, s38),
  ({Sum.inl 10, Sum.inr false}, s39),
  ({Sum.inl 5, Sum.inr true}, s36),
  ({Sum.inl 6, Sum.inr true}, s37),
  ({Sum.inl 10, Sum.inr true}, s38),
  ({Sum.inl 10, Sum.inr true}, s39),
  ({Sum.inl 5, Sum.inl 8, Sum.inr false}, s40),
  ({Sum.inl 6, Sum.inl 10, Sum.inr false}, s41),
  ({Sum.inl 5, Sum.inl 10, Sum.inr false}, s42),
  ({Sum.inl 7, Sum.inl 10, Sum.inr false}, s43),
  ({Sum.inl 5, Sum.inl 8, Sum.inr true}, s40),
  ({Sum.inl 6, Sum.inl 10, Sum.inr true}, s41),
  ({Sum.inl 5, Sum.inl 10, Sum.inr true}, s42),
  ({Sum.inl 7, Sum.inl 10, Sum.inr true}, s43),
  ({Sum.inl 5, Sum.inl 8, Sum.inl 10, Sum.inr false}, s44),
  ({Sum.inl 5, Sum.inl 8, Sum.inl 10, Sum.inr true}, s44)}

def copyTable3 : Finset (Finset (Sum (Fin 12) Bool) × Sig) := {
  ({Sum.inl 0}, s1),
  ({Sum.inl 1}, s11),
  ({Sum.inl 2}, s3),
  ({Sum.inl 4}, s5),
  ({Sum.inl 5}, s14),
  ({Sum.inl 6}, s6),
  ({Sum.inl 7}, s7),
  ({Sum.inl 8}, s15),
  ({Sum.inl 9}, s8),
  ({Sum.inl 10}, s16),
  ({Sum.inl 11}, s9),
  ({Sum.inr false}, s4),
  ({Sum.inr true}, s4),
  ({Sum.inl 5, Sum.inl 8}, s18),
  ({Sum.inl 4, Sum.inr false}, s45),
  ({Sum.inl 5, Sum.inr false}, s46),
  ({Sum.inl 7, Sum.inr false}, s47),
  ({Sum.inl 10, Sum.inr false}, s48),
  ({Sum.inl 10, Sum.inr false}, s49),
  ({Sum.inl 4, Sum.inr true}, s45),
  ({Sum.inl 5, Sum.inr true}, s46),
  ({Sum.inl 7, Sum.inr true}, s47),
  ({Sum.inl 10, Sum.inr true}, s48),
  ({Sum.inl 10, Sum.inr true}, s49),
  ({Sum.inl 4, Sum.inl 5, Sum.inr false}, s50),
  ({Sum.inl 4, Sum.inl 10, Sum.inr false}, s51),
  ({Sum.inl 7, Sum.inl 10, Sum.inr false}, s52),
  ({Sum.inl 5, Sum.inl 10, Sum.inr false}, s53),
  ({Sum.inl 4, Sum.inl 5, Sum.inr true}, s50),
  ({Sum.inl 4, Sum.inl 10, Sum.inr true}, s51),
  ({Sum.inl 7, Sum.inl 10, Sum.inr true}, s52),
  ({Sum.inl 5, Sum.inl 10, Sum.inr true}, s53)}

def copyTable4 : Finset (Finset (Sum (Fin 12) Bool) × Sig) := {
  ({Sum.inl 0}, s1),
  ({Sum.inl 1}, s11),
  ({Sum.inl 2}, s3),
  ({Sum.inl 3}, s4),
  ({Sum.inl 5}, s14),
  ({Sum.inl 6}, s6),
  ({Sum.inl 7}, s7),
  ({Sum.inl 8}, s15),
  ({Sum.inl 9}, s8),
  ({Sum.inl 10}, s16),
  ({Sum.inl 11}, s9),
  ({Sum.inr false}, s5),
  ({Sum.inr true}, s5),
  ({Sum.inl 5, Sum.inl 8}, s18),
  ({Sum.inl 6, Sum.inr false}, s54),
  ({Sum.inl 7, Sum.inr false}, s55),
  ({Sum.inl 10, Sum.inr false}, s56),
  ({Sum.inl 10, Sum.inr false}, s57),
  ({Sum.inl 6, Sum.inr true}, s54),
  ({Sum.inl 7, Sum.inr true}, s55),
  ({Sum.inl 10, Sum.inr true}, s56),
  ({Sum.inl 10, Sum.inr true}, s57),
  ({Sum.inl 6, Sum.inl 10, Sum.inr false}, s58),
  ({Sum.inl 1, Sum.inl 10, Sum.inr false}, s59),
  ({Sum.inl 7, Sum.inl 10, Sum.inr false}, s60),
  ({Sum.inl 6, Sum.inl 10, Sum.inr true}, s58),
  ({Sum.inl 1, Sum.inl 10, Sum.inr true}, s59),
  ({Sum.inl 7, Sum.inl 10, Sum.inr true}, s60)}

def copyTable5 : Finset (Finset (Sum (Fin 12) Bool) × Sig) := {
  ({Sum.inl 0}, s1),
  ({Sum.inl 1}, s11),
  ({Sum.inl 2}, s3),
  ({Sum.inl 3}, s4),
  ({Sum.inl 4}, s5),
  ({Sum.inl 6}, s6),
  ({Sum.inl 7}, s7),
  ({Sum.inl 8}, s15),
  ({Sum.inl 9}, s8),
  ({Sum.inl 10}, s16),
  ({Sum.inl 11}, s9),
  ({Sum.inr false}, s14),
  ({Sum.inr true}, s14),
  ({Sum.inl 8, Sum.inr false}, s18),
  ({Sum.inl 10, Sum.inr false}, s61),
  ({Sum.inl 10, Sum.inr false}, s62),
  ({Sum.inl 8, Sum.inr true}, s18),
  ({Sum.inl 10, Sum.inr true}, s61),
  ({Sum.inl 10, Sum.inr true}, s62),
  ({Sum.inl 8, Sum.inl 10, Sum.inr false}, s63),
  ({Sum.inl 8, Sum.inl 10, Sum.inr true}, s63),
  ({Sum.inl 8, Sum.inl 10, Sum.inr false, Sum.inr true}, s18)}

def copyTable6 : Finset (Finset (Sum (Fin 12) Bool) × Sig) := {
  ({Sum.inl 0}, s1),
  ({Sum.inl 1}, s11),
  ({Sum.inl 2}, s3),
  ({Sum.inl 3}, s4),
  ({Sum.inl 4}, s5),
  ({Sum.inl 5}, s14),
  ({Sum.inl 7}, s7),
  ({Sum.inl 8}, s15),
  ({Sum.inl 9}, s8),
  ({Sum.inl 10}, s16),
  ({Sum.inl 11}, s9),
  ({Sum.inr false}, s6),
  ({Sum.inr true}, s6),
  ({Sum.inl 5, Sum.inl 8}, s18)}

def copyTable7 : Finset (Finset (Sum (Fin 12) Bool) × Sig) := {
  ({Sum.inl 0}, s1),
  ({Sum.inl 1}, s11),
  ({Sum.inl 2}, s3),
  ({Sum.inl 3}, s4),
  ({Sum.inl 4}, s5),
  ({Sum.inl 5}, s14),
  ({Sum.inl 6}, s6),
  ({Sum.inl 8}, s15),
  ({Sum.inl 9}, s8),
  ({Sum.inl 10}, s16),
  ({Sum.inl 11}, s9),
  ({Sum.inr false}, s7),
  ({Sum.inr true}, s7),
  ({Sum.inl 5, Sum.inl 8}, s18),
  ({Sum.inl 10, Sum.inr false}, s64),
  ({Sum.inl 10, Sum.inr false}, s65),
  ({Sum.inl 10, Sum.inr true}, s64),
  ({Sum.inl 10, Sum.inr true}, s65)}

def copyTable8 : Finset (Finset (Sum (Fin 12) Bool) × Sig) := {
  ({Sum.inl 0}, s1),
  ({Sum.inl 1}, s11),
  ({Sum.inl 2}, s3),
  ({Sum.inl 3}, s4),
  ({Sum.inl 4}, s5),
  ({Sum.inl 5}, s14),
  ({Sum.inl 6}, s6),
  ({Sum.inl 7}, s7),
  ({Sum.inl 9}, s8),
  ({Sum.inl 10}, s16),
  ({Sum.inl 11}, s9),
  ({Sum.inr false}, s15),
  ({Sum.inr true}, s15),
  ({Sum.inl 5, Sum.inr false}, s18),
  ({Sum.inl 10, Sum.inr false}, s66),
  ({Sum.inl 10, Sum.inr false}, s67),
  ({Sum.inl 5, Sum.inr true}, s18),
  ({Sum.inl 10, Sum.inr true}, s66),
  ({Sum.inl 10, Sum.inr true}, s67),
  ({Sum.inl 4, Sum.inl 10, Sum.inr false}, s68),
  ({Sum.inl 5, Sum.inl 10, Sum.inr false}, s69),
  ({Sum.inl 4, Sum.inl 10, Sum.inr true}, s68),
  ({Sum.inl 5, Sum.inl 10, Sum.inr true}, s69),
  ({Sum.inl 5, Sum.inl 10, Sum.inr false, Sum.inr true}, s18)}

def copyTable9 : Finset (Finset (Sum (Fin 12) Bool) × Sig) := {
  ({Sum.inl 0}, s1),
  ({Sum.inl 1}, s11),
  ({Sum.inl 2}, s3),
  ({Sum.inl 3}, s4),
  ({Sum.inl 4}, s5),
  ({Sum.inl 5}, s14),
  ({Sum.inl 6}, s6),
  ({Sum.inl 7}, s7),
  ({Sum.inl 8}, s15),
  ({Sum.inl 10}, s16),
  ({Sum.inl 11}, s9),
  ({Sum.inr false}, s8),
  ({Sum.inr true}, s8),
  ({Sum.inl 5, Sum.inl 8}, s18),
  ({Sum.inl 8, Sum.inr false}, s70),
  ({Sum.inl 8, Sum.inr true}, s70),
  ({Sum.inl 5, Sum.inl 8, Sum.inr false}, s71),
  ({Sum.inl 5, Sum.inl 8, Sum.inr true}, s71)}

def copyTable10 : Finset (Finset (Sum (Fin 12) Bool) × Sig) := {
  ({Sum.inl 0}, s1),
  ({Sum.inl 1}, s11),
  ({Sum.inl 2}, s3),
  ({Sum.inl 3}, s4),
  ({Sum.inl 4}, s5),
  ({Sum.inl 5}, s14),
  ({Sum.inl 6}, s6),
  ({Sum.inl 7}, s7),
  ({Sum.inl 8}, s15),
  ({Sum.inl 9}, s8),
  ({Sum.inl 11}, s9),
  ({Sum.inr false}, s16),
  ({Sum.inr true}, s16),
  ({Sum.inl 5, Sum.inl 8}, s18)}

def copyTable11 : Finset (Finset (Sum (Fin 12) Bool) × Sig) := {
  ({Sum.inl 0}, s1),
  ({Sum.inl 1}, s11),
  ({Sum.inl 2}, s3),
  ({Sum.inl 3}, s4),
  ({Sum.inl 4}, s5),
  ({Sum.inl 5}, s14),
  ({Sum.inl 6}, s6),
  ({Sum.inl 7}, s7),
  ({Sum.inl 8}, s15),
  ({Sum.inl 9}, s8),
  ({Sum.inl 10}, s16),
  ({Sum.inr false}, s9),
  ({Sum.inr true}, s9),
  ({Sum.inl 5, Sum.inl 8}, s18),
  ({Sum.inl 5, Sum.inr false}, s72),
  ({Sum.inl 9, Sum.inr false}, s73),
  ({Sum.inl 10, Sum.inr false}, s74),
  ({Sum.inl 10, Sum.inr false}, s75),
  ({Sum.inl 5, Sum.inr true}, s72),
  ({Sum.inl 9, Sum.inr true}, s73),
  ({Sum.inl 10, Sum.inr true}, s74),
  ({Sum.inl 10, Sum.inr true}, s75),
  ({Sum.inl 5, Sum.inl 8, Sum.inr false}, s76),
  ({Sum.inl 9, Sum.inl 10, Sum.inr false}, s77),
  ({Sum.inl 5, Sum.inl 10, Sum.inr false}, s78),
  ({Sum.inl 8, Sum.inl 10, Sum.inr false}, s79),
  ({Sum.inl 5, Sum.inl 8, Sum.inl 10, Sum.inr false}, s80),
  ({Sum.inl 5, Sum.inl 8, Sum.inr true}, s76),
  ({Sum.inl 9, Sum.inl 10, Sum.inr true}, s77),
  ({Sum.inl 5, Sum.inl 10, Sum.inr true}, s78),
  ({Sum.inl 8, Sum.inl 10, Sum.inr true}, s79),
  ({Sum.inl 5, Sum.inl 8, Sum.inl 10, Sum.inr true}, s80),
  ({Sum.inl 5, Sum.inl 8, Sum.inl 10, Sum.inr false}, s81),
  ({Sum.inl 5, Sum.inl 8, Sum.inl 10, Sum.inr false}, s82),
  ({Sum.inl 5, Sum.inl 8, Sum.inl 10, Sum.inr true}, s81),
  ({Sum.inl 5, Sum.inl 8, Sum.inl 10, Sum.inr true}, s82)}

def copyTable12 : Finset (Finset (Sum (Fin 12) Bool) × Sig) := {
  ({Sum.inl 0}, s1),
  ({Sum.inl 1}, s11),
  ({Sum.inl 2}, s3),
  ({Sum.inl 3}, s4),
  ({Sum.inl 4}, s5),
  ({Sum.inl 6}, s6),
  ({Sum.inl 7}, s7),
  ({Sum.inl 9}, s8),
  ({Sum.inl 10}, s16),
  ({Sum.inl 11}, s9),
  ({Sum.inr false}, s18),
  ({Sum.inr true}, s18),
  ({Sum.inl 10, Sum.inr false}, s83),
  ({Sum.inl 10, Sum.inr false}, s84),
  ({Sum.inl 10, Sum.inr true}, s83),
  ({Sum.inl 10, Sum.inr true}, s84),
  ({Sum.inl 4, Sum.inl 10, Sum.inr false}, s68),
  ({Sum.inl 4, Sum.inl 10, Sum.inr true}, s68)}

theorem col_eq (v : Sig) : {o | col v o = true} = separationColumn false positive negative v := by
  ext o
  simp [col, separationColumn]
theorem target_eq : s17 = graph := by decide +kernel
theorem target_valid : ∀ o : Pair, bit (positive o) s17 = true ∧ bit (negative o) s17 = false := by decide +kernel
def oldEntries : Array (Finset (Fin 12) × Sig) := #[
  ({0}, s1),
  ({1}, s11),
  ({2}, s3),
  ({3}, s4),
  ({4}, s5),
  ({5}, s14),
  ({6}, s6),
  ({7}, s7),
  ({8}, s15),
  ({9}, s8),
  ({10}, s16),
  ({11}, s9),
  ({5, 8}, s18)]
def oldWitnessCode : Nat := 0x563c00003f3c0000433c000000000000423c00003f3c0000000000003c3c0000322f00001f2d0000230f000001100000563c0000000000008a8700008e7a0000563c0000776a00006763000087420000554c0000372f00002c1f00001b0f00000e0100003f3c00008a87000000000000000000003f3c00006a6a000000000000424200004c4c00002f2f00001f1f0000180f000001010000433c00008e7a000000000000000000007d3c0000776a00006363000045420000534c0000442f00002c1f0000180f00000e01000000000000563c00003f3c00007d3c000000000000000000003f3c00003c0000003c3c0000312f00001f2d0000130f000001100000423c0000776a00006a6a0000776a000000000000000000006363000042420000504c0000312f0000331f0000130f00005f0100003f3c00006763000000000000636300003f3c00006363000000000000424200004c4c00002f2f00001f1f0000230f000001010000000000008742000042420000454200003c000000424200004242000000000000000000002f2f00001f2d00000f0f0000011000003c3c0000554c00004c4c0000534c00003c3c0000504c00004c4c000000000000000000002f2f00002d1f00000f0f000012010000322f0000372f00002f2f0000442f0000312f0000312f00002f2f00002f2f00002f2f0000000000002d1f00000f0f0000120100001f2d00002c1f00001f1f00002c1f00001f2d0000331f00001f1f00001f2d00002d1f00002d1f000000000000130f00002d010000230f00001b0f0000180f0000180f0000130f0000130f0000230f00000f0f00000f0f00000f0f0000130f00000000000001230000011000000e010000010100000e010000011000005f010000010100000110000012010000120100002d010000012300000000
def oldWitness (p q : Finset (Fin 12) × Sig) (d : Nat) : Pair :=
  let i := oldEntries.findIdx (fun x => x == p)
  let j := oldEntries.findIdx (fun x => x == q)
  ⟨(((oldWitnessCode >>> (8 * ((i * 13 + j) * 4 + d))) % 256) % 225), Nat.mod_lt _ (by decide)⟩
def copy0Entries : Array (Finset (Sum (Fin 12) Bool) × Sig) := #[
  ({Sum.inl 1}, s11),
  ({Sum.inl 2}, s3),
  ({Sum.inl 3}, s4),
  ({Sum.inl 4}, s5),
  ({Sum.inl 5}, s14),
  ({Sum.inl 6}, s6),
  ({Sum.inl 7}, s7),
  ({Sum.inl 8}, s15),
  ({Sum.inl 9}, s8),
  ({Sum.inl 10}, s16),
  ({Sum.inl 11}, s9),
  ({Sum.inr false}, s1),
  ({Sum.inr true}, s1),
  ({Sum.inl 5, Sum.inl 8}, s18),
  ({Sum.inl 4, Sum.inr false}, s19),
  ({Sum.inl 7, Sum.inr false}, s20),
  ({Sum.inl 9, Sum.inr false}, s21),
  ({Sum.inl 10, Sum.inr false}, s22),
  ({Sum.inl 10, Sum.inr false}, s23),
  ({Sum.inl 4, Sum.inr true}, s19),
  ({Sum.inl 7, Sum.inr true}, s20),
  ({Sum.inl 9, Sum.inr true}, s21),
  ({Sum.inl 10, Sum.inr true}, s22),
  ({Sum.inl 10, Sum.inr true}, s23),
  ({Sum.inl 9, Sum.inl 10, Sum.inr false}, s24),
  ({Sum.inl 4, Sum.inl 10, Sum.inr false}, s25),
  ({Sum.inl 7, Sum.inl 10, Sum.inr false}, s26),
  ({Sum.inl 8, Sum.inl 10, Sum.inr false}, s27),
  ({Sum.inl 9, Sum.inl 10, Sum.inr true}, s24),
  ({Sum.inl 4, Sum.inl 10, Sum.inr true}, s25),
  ({Sum.inl 7, Sum.inl 10, Sum.inr true}, s26),
  ({Sum.inl 8, Sum.inl 10, Sum.inr true}, s27),
  ({Sum.inl 5, Sum.inl 8, Sum.inl 10, Sum.inr false}, s28),
  ({Sum.inl 5, Sum.inl 8, Sum.inl 10, Sum.inr true}, s28)]
def copy0WitnessCode : Nat := 0x10e00000110000001100000000000000000000001100000563c000000000000433c000000000000423c00003f3c0000000000003c3c0000322f00001f2d0000230f0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000010e000001100000011000000000000000000000000000000000000000000000000000000110000000000000563c000000000000433c000000000000423c00003f3c0000000000003c3c0000322f00001f2d0000230f00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000010e00000110000001100000000000000000000001100000563c0000000000007c3c000000000000000000003f3c00003c0000003c3c0000312f00001f2d0000130f000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000e0100000000000012010000423c0000000000005f010000776a000000000000776a00006a3c0000000000005e6a000042420000504c0000312f0000331f0000130f000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000e01000012010000000000003c3c00000000000012010000554c000000000000534c00003c3c0000504c00004c4c000045420000000000002f2f00002d1f00000f0f00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000e0100000e010000433c0000000000000e010000827a000000000000000000007c3c0000776a0000637a000045420000534c0000442f00002c1f0000180f0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000010e000001100000011000000000000000000000000000000000000000000000000000000110000000000000563c0000000000007c3c000000000000000000003f3c00003c0000003c3c0000312f00001f2d0000130f00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000e01000000000000120100000000000000000000000000000000000000000000423c00005f01000000000000776a000000000000776a00006a3c0000000000005e6a000042420000504c0000312f0000331f0000130f00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000e010000120100000000000000000000000000000000000000000000000000003c3c00001201000000000000554c000000000000534c00003c3c0000504c00004c4c000045420000000000002f2f00002d1f00000f0f0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000e0100000e0100000000000000000000000000000000000000000000433c00000e01000000000000827a000000000000000000007c3c0000776a0000637a000045420000534c0000442f00002c1f0000180f0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000015f0000011200003c3c000000000000000000008787000000000000000000003c3c00006a6a000000000000424200004c4c00002f2f00001f1f00000f2300000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000453c000000000000000000009087000000000000007a0000003c0000006a000063be000045420000004c0000942f0000361f0000180f000000000000010e000000000000000000000000000000000000010e00000e0100000e0100000000000000000000000000000000000000000000000000000000000000000000000000000e6a00000e4c00003c3c00000000000000000000877a00007a000000000000003c3c0000776a0000637a000045420000534c0000312f00002c1f00000f2300000000000001100000000000000000000000000000000000000110000000000000120100000e0100000000000000000000000000000000000000000000015f0000000000000e6a000000000000124c00003c3c00000000000000000000776a00006a6a0000776a00003c3c000000000000636a000042420000504c0000312f00002d1f00000f2300000000000001100000000000000000000000000000000000000110000012010000000000000e010000000000000000000000000000000000000000000001120000000000000e4c0000124c0000000000003c3c00000000000000000000554c00004c4c0000534c00003c3c0000504c00004c4c000045420000000000002f2f00002d1f00000f23000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000015f00000112000000000000000000000000000000000000000000003c3c000000000000000000008787000000000000000000003c3c00006a6a000000000000424200004c4c00002f2f00001f1f00000f2300000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000453c000000000000000000009087000000000000007a0000003c0000006a000063be000045420000004c0000942f0000361f0000180f0000010e000000000000010e00000e0100000e01000000000000000000000000000000000000000000000000000000000000000000000e6a00000e4c000000000000000000000000000000000000000000003c3c00000000000000000000877a00007a000000000000003c3c0000776a0000637a000045420000534c0000312f00002c1f00000f23000001100000000000000110000000000000120100000e01000000000000000000000000000000000000015f0000000000000e6a000000000000124c000000000000000000000000000000000000000000003c3c00000000000000000000776a00006a6a0000776a00003c3c000000000000636a000042420000504c0000312f00002d1f00000f23000001100000000000000110000012010000000000000e0100000000000000000000000000000000000001120000000000000e4c0000124c00000000000000000000000000000000000000000000000000003c3c00000000000000000000554c00004c4c0000534c00003c3c0000504c00004c4c000045420000000000002f2f00002d1f00000f230000000000000000000000000000423c00003c3c0000433c000000000000423c00003c3c0000433c00003c3c0000453c00003c3c00003c3c00003c3c00003c3c0000453c00003c3c00003c3c00003c3c0000000000003c3c00003c3c0000563c00003f3c0000433c000000000000423c00003f3c0000000000003c3c0000322f00001f2d0000230f0000000000000110000000000000000000000000000000000000011000005f010000120100000e010000000000000000000000000000000000000000000000000000000000000000000000000000000000003c3c000000000000000000008787000000000000007a00003c3c0000006a000063c1000045420000004c0000312f00002d1f00000f2300000110000000000000011000005f010000120100000e01000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000003c3c000000000000000000008787000000000000007a00003c3c0000006a000063c1000045420000004c0000312f00002d1f00000f230000563c0000563c0000563c0000776a0000554c0000827a0000563c0000776a0000554c0000827a00008787000090870000877a0000776a0000554c00008787000090870000877a0000776a0000554c0000563c00008787000087870000000000008a8700008e7a0000563c0000776a00006763000087420000554c0000372f00002c1f00001b0f00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000007a0000006a6a00004c4c000000000000000000007a0000006a6a00004c4c00003f3c000000000000000000008a87000000000000000000003f3c00006a6a000000000000424200004c4c00002f2f00001f1f0000180f0000433c0000433c00007c3c0000776a0000534c0000000000007c3c0000776a0000534c00000000000000000000007a000000000000776a0000534c000000000000007a000000000000776a0000534c0000433c0000007a0000007a00008e7a000000000000000000007d3c0000776a00006363000045420000534c0000442f00002c1f0000180f00000000000000000000000000006a3c00003c3c00007c3c0000000000006a3c00003c3c00007c3c00003c3c0000003c00003c3c00003c3c00003c3c00003c3c0000003c00003c3c00003c3c00003c3c0000000000003c3c00003c3c0000563c00003f3c00007d3c000000000000000000003f3c00003c0000003c3c0000312f00001f2d0000130f0000423c0000423c00000000000000000000504c0000776a00000000000000000000504c0000776a00006a6a0000006a0000776a000000000000504c00006a6a0000006a0000776a000000000000504c0000423c0000006a0000006a0000776a00006a6a0000776a000000000000000000006363000042420000504c0000312f0000331f0000130f00003f3c00003f3c00003f3c00005e6a00004c4c0000637a00003f3c00005e6a00004c4c0000637a00000000000063be0000637a0000636a00004c4c00000000000063be0000637a0000636a00004c4c00003f3c000063c1000063c100006763000000000000636300003f3c00006363000000000000424200004c4c00002f2f00001f1f0000230f000000000000000000003c0000004242000045420000454200003c000000424200004542000045420000424200004542000045420000424200004542000042420000454200004542000042420000454200000000000045420000454200008742000042420000454200003c000000424200004242000000000000000000002f2f00001f2d00000f0f00003c3c00003c3c00003c3c0000504c000000000000534c00003c3c0000504c000000000000534c00004c4c0000004c0000534c0000504c0000000000004c4c0000004c0000534c0000504c0000000000003c3c0000004c0000004c0000554c00004c4c0000534c00003c3c0000504c00004c4c000000000000000000002f2f00002d1f00000f0f0000322f0000322f0000312f0000312f00002f2f0000442f0000312f0000312f00002f2f0000442f00002f2f0000942f0000312f0000312f00002f2f00002f2f0000942f0000312f0000312f00002f2f0000322f0000312f0000312f0000372f00002f2f0000442f0000312f0000312f00002f2f00002f2f00002f2f0000000000002d1f00000f0f00001f2d00001f2d00001f2d0000331f00002d1f00002c1f00001f2d0000331f00002d1f00002c1f00001f1f0000361f00002c1f00002d1f00002d1f00001f1f0000361f00002c1f00002d1f00002d1f00001f2d00002d1f00002d1f00002c1f00001f1f00002c1f00001f2d0000331f00001f1f00001f2d00002d1f00002d1f000000000000130f0000230f0000230f0000130f0000130f00000f0f0000180f0000130f0000130f00000f0f0000180f00000f230000180f00000f2300000f2300000f2300000f230000180f00000f2300000f2300000f230000230f00000f2300000f2300001b0f0000180f0000180f0000130f0000130f0000230f00000f0f00000f0f00000f0f0000130f00000000
def copy0Witness (p q : Finset (Sum (Fin 12) Bool) × Sig) (d : Nat) : Pair :=
  let i := copy0Entries.findIdx (fun x => x == p)
  let j := copy0Entries.findIdx (fun x => x == q)
  ⟨(((copy0WitnessCode >>> (8 * ((i * 34 + j) * 4 + d))) % 256) % 225), Nat.mod_lt _ (by decide)⟩
def copy0BridgeRows : Array Pair := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def copy0BridgeWitness (p : Finset (Fin 12) × Sig) : Pair :=
  copy0BridgeRows.getD (oldEntries.findIdx (fun x => x == p)) 0
def copy1Entries : Array (Finset (Sum (Fin 12) Bool) × Sig) := #[
  ({Sum.inl 0}, s1),
  ({Sum.inl 2}, s3),
  ({Sum.inl 3}, s4),
  ({Sum.inl 4}, s5),
  ({Sum.inl 5}, s14),
  ({Sum.inl 6}, s6),
  ({Sum.inl 7}, s7),
  ({Sum.inl 8}, s15),
  ({Sum.inl 9}, s8),
  ({Sum.inl 10}, s16),
  ({Sum.inl 11}, s9),
  ({Sum.inr false}, s11),
  ({Sum.inr true}, s11),
  ({Sum.inl 5, Sum.inl 8}, s18),
  ({Sum.inl 5, Sum.inr false}, s29),
  ({Sum.inl 10, Sum.inr false}, s30),
  ({Sum.inl 10, Sum.inr false}, s31),
  ({Sum.inl 5, Sum.inr true}, s29),
  ({Sum.inl 10, Sum.inr true}, s30),
  ({Sum.inl 10, Sum.inr true}, s31),
  ({Sum.inl 5, Sum.inl 8, Sum.inr false}, s32),
  ({Sum.inl 5, Sum.inl 10, Sum.inr false}, s33),
  ({Sum.inl 0, Sum.inl 10, Sum.inr false}, s34),
  ({Sum.inl 5, Sum.inl 8, Sum.inr true}, s32),
  ({Sum.inl 5, Sum.inl 10, Sum.inr true}, s33),
  ({Sum.inl 0, Sum.inl 10, Sum.inr true}, s34),
  ({Sum.inl 5, Sum.inl 8, Sum.inl 10, Sum.inr false}, s35),
  ({Sum.inl 5, Sum.inl 8, Sum.inl 10, Sum.inr true}, s35)]
def copy1WitnessCode : Nat := 0x230f0000563c000000000000433c000000000000423c00003f3c0000000000003c3c0000322f00001f2d000001100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000230f000000000000563c000000000000433c000000000000423c00003f3c0000000000003c3c0000322f00001f2d00000110000000000000000000000000000000000000000000000000000000000000010f00000000000000000000000000000000000000000000012200000110000000000000012300000e010000000000000e010000011000005f010000010100000110000012010000120100003601000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000f0f00008742000000000000454200003c000000424200004242000000000000000000002f2f00001f2d0000011000000000000000000000000000000000000000000000010f00000000000000000000000000000000000000000000090f00000f000000000000000000000000000000230f0000563c00003f3c0000433c000000000000423c00003f3c0000000000003c3c0000322f00001f2d00000110000000000000000000000000000000000000010f00000000000000000000000000000000000000000000012200000000000000000000000000000110000001230000000000000e010000000000000e010000011000005f0100000101000001100000120100001201000036010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000f0f0000000000008742000000000000454200003c000000424200004242000000000000000000002f2f00001f2d0000011000000000000000000000010f00000000000000000000000000000000000000000000090f00000f0000000000000000000000000000000000000000000000230f000000000000563c00003f3c0000433c000000000000423c00003f3c0000000000003c3c0000322f00001f2d00000110000000000000000000000000000000000000000000000000000000000000090f00000000000000000000000000000000000000000000092300003f3c000000000000000000008a87000000000000000000003f3c00006aaf000000000000424200004c4c00002f2f00001f2d000001000000000000000000000000000000000000000000000000000000000000000f0000000000000000000000000000000000000000000000000000003f3c000000000000000000008a87000000000000c47a00003f3c00006a6a0000c25a0000004200004c4c00003d2f00001f1f00000101000000000000000000000000000000000000000000000122000000000000000000000000000000000000000000000923000000000000000000000000000000000000000000008742000042420000454200003c000000424200004242000000000000000000002f2f00001f2d00000142000000000000000000000000000000000000090f00000000000000000000000000000000000000000000092300000000000000000000000000003f3c000000000000000000008a87000000000000000000003f3c00006aaf000000000000424200004c4c00002f2f00001f2d000001000000000000000000000000000000000000000f0000000000000000000000000000000000000000000000000000000000000000000000000000003f3c000000000000000000008a87000000000000c47a00003f3c00006a6a0000c25a0000004200004c4c00003d2f00001f1f00000101000000000000000000000122000000000000000000000000000000000000000000000923000000000000000000000000000000000000000000000000000000000000000000008742000042420000454200003c000000424200004242000000000000000000002f2f00001f2d00000142000000000000000000000110000000000000000000000110000000000000000000003f3c00003f3c0000000000003f3c00003f3c000000000000000000003f3c00003f3c0000563c00003f3c0000433c000000000000423c00003f3c0000000000003c3c0000322f00001f2d00000110000000000000230f0000000000000000000000000000012300000f0f0000230f00000000000000000000000000000000000000000000000000003f3c000000000000000000008a87000000000000c47a00003f3c00006aaf0000c2630000004200004c4c00003d2f00001f2d0000015b0000230f000000000000012300000f0f0000230f00000000000000000000000000000000000000000000000000000000000000000000000000003f3c000000000000000000008a87000000000000c47a00003f3c00006aaf0000c2630000004200004c4c00003d2f00001f2d0000015b0000563c0000563c00000e01000087420000563c00000e01000087420000563c00008a8700008a870000874200008a8700008a87000087420000563c00008a8700008a870000000000008a8700008e7a0000563c0000776a00006763000087420000554c0000372f00002c1f00000e010000000000000000000000000000000000003f3c000000000000000000003f3c00000000000000000000424200000000000000000000424200003f3c000000000000000000008a87000000000000000000003f3c00006a6a000000000000424200004c4c00002f2f00001f1f000001010000433c0000433c00000e01000045420000433c00000e01000045420000433c000000000000c47a00004542000000000000c47a000045420000433c0000c47a0000c47a00008e7a000000000000000000007d3c0000776a00006363000045420000534c0000442f00002c1f00000e0100000000000000000000011000003c00000000000000011000003c000000000000003f3c00003f3c00003c0000003f3c00003f3c00003c000000000000003f3c00003f3c0000563c00003f3c00007d3c000000000000000000003f3c00003c0000003c3c0000312f00001f2d000001100000423c0000423c00005f01000042420000423c00005f01000042420000423c00006aaf00006a6a0000424200006aaf00006a6a000042420000423c00006aaf00006aaf0000776a00006a6a0000776a000000000000000000006363000042420000504c0000312f0000331f00005f0100003f3c00003f3c000001010000424200003f3c000001010000424200003f3c000000000000c25a00004242000000000000c25a0000424200003f3c0000c2630000c26300006763000000000000636300003f3c00006363000000000000424200004c4c00002f2f00001f1f00000101000000000000000000000110000000000000000000000110000000000000000000004242000000420000000000004242000000420000000000000000000000420000004200008742000042420000454200003c000000424200004242000000000000000000002f2f00001f2d0000011000003c3c00003c3c000012010000000000003c3c000012010000000000003c3c00004c4c00004c4c0000000000004c4c00004c4c0000000000003c3c00004c4c00004c4c0000554c00004c4c0000534c00003c3c0000504c00004c4c000000000000000000002f2f00002d1f000012010000322f0000322f0000120100002f2f0000322f0000120100002f2f0000322f00002f2f00003d2f00002f2f00002f2f00003d2f00002f2f0000322f00003d2f00003d2f0000372f00002f2f0000442f0000312f0000312f00002f2f00002f2f00002f2f0000000000002d1f0000120100001f2d00001f2d0000360100001f2d00001f2d0000360100001f2d00001f2d00001f2d00001f1f00001f2d00001f2d00001f1f00001f2d00001f2d00001f2d00001f2d00002c1f00001f1f00002c1f00001f2d0000331f00001f1f00001f2d00002d1f00002d1f0000000000002d010000011000000110000000000000011000000110000000000000011000000110000001000000010100000142000001000000010100000142000001100000015b0000015b00000e010000010100000e010000011000005f010000010100000110000012010000120100002d0100000000
def copy1Witness (p q : Finset (Sum (Fin 12) Bool) × Sig) (d : Nat) : Pair :=
  let i := copy1Entries.findIdx (fun x => x == p)
  let j := copy1Entries.findIdx (fun x => x == q)
  ⟨(((copy1WitnessCode >>> (8 * ((i * 28 + j) * 4 + d))) % 256) % 225), Nat.mod_lt _ (by decide)⟩
def copy1BridgeRows : Array Pair := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def copy1BridgeWitness (p : Finset (Fin 12) × Sig) : Pair :=
  copy1BridgeRows.getD (oldEntries.findIdx (fun x => x == p)) 0
def copy2Entries : Array (Finset (Sum (Fin 12) Bool) × Sig) := #[
  ({Sum.inl 0}, s1),
  ({Sum.inl 1}, s11),
  ({Sum.inl 3}, s4),
  ({Sum.inl 4}, s5),
  ({Sum.inl 5}, s14),
  ({Sum.inl 6}, s6),
  ({Sum.inl 7}, s7),
  ({Sum.inl 8}, s15),
  ({Sum.inl 9}, s8),
  ({Sum.inl 10}, s16),
  ({Sum.inl 11}, s9),
  ({Sum.inr false}, s3),
  ({Sum.inr true}, s3),
  ({Sum.inl 5, Sum.inl 8}, s18),
  ({Sum.inl 5, Sum.inr false}, s36),
  ({Sum.inl 6, Sum.inr false}, s37),
  ({Sum.inl 10, Sum.inr false}, s38),
  ({Sum.inl 10, Sum.inr false}, s39),
  ({Sum.inl 5, Sum.inr true}, s36),
  ({Sum.inl 6, Sum.inr true}, s37),
  ({Sum.inl 10, Sum.inr true}, s38),
  ({Sum.inl 10, Sum.inr true}, s39),
  ({Sum.inl 5, Sum.inl 8, Sum.inr false}, s40),
  ({Sum.inl 6, Sum.inl 10, Sum.inr false}, s41),
  ({Sum.inl 5, Sum.inl 10, Sum.inr false}, s42),
  ({Sum.inl 7, Sum.inl 10, Sum.inr false}, s43),
  ({Sum.inl 5, Sum.inl 8, Sum.inr true}, s40),
  ({Sum.inl 6, Sum.inl 10, Sum.inr true}, s41),
  ({Sum.inl 5, Sum.inl 10, Sum.inr true}, s42),
  ({Sum.inl 7, Sum.inl 10, Sum.inr true}, s43),
  ({Sum.inl 5, Sum.inl 8, Sum.inl 10, Sum.inr false}, s44),
  ({Sum.inl 5, Sum.inl 8, Sum.inl 10, Sum.inr true}, s44)]
def copy2WitnessCode : Nat := 0x1f1f00000000000000000000000000001f2d0000563c000000000000433c000000000000423c00003f3c0000000000003c3c0000322f0000230f0000011000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001f1f00000000000000000000000000000000000000000000000000001f2d000000000000563c000000000000433c000000000000423c00003f3c0000000000003c3c0000322f0000230f0000011000000000000000000000000000000000000000000000000000000000000000000000000000001f1f00000000000000000000000000000000000000000000000000001f1f00001f1f0000423c000000000000331f0000776a000000000000776a00004d3c0000000000005e5a000042420000504c00002f2f0000130f00005c010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001f1f00000000000000000000000000001f2d00008742000000000000454200003c000000424200004242000000000000000000002f2f00000f0f0000011000000000000000000000000000000000000000000000000000000000000000000000000000001f1f0000000000000000000000000000000000000000000000000000000000001f1f00003f3c0000000000001f1f0000665a000000000000635a00003f3c00005e5a000000000000424200004c4c00002f2f0000230f0000010100000000000000000000000000000000000000000000000000001f1f0000000000001f1f000000000000000000000000000000000000000000001f1f00001f1f00001f1f00000000000000000000000000001f2d0000563c00003f3c0000433c000000000000423c00003f3c0000000000003c3c0000312f0000040f00000110000000000000000000000000000000000000000000001f1f00000000000000000000000000000000000000000000000000001f1f00001f1f000000000000000000000000000000000000423c0000331f000000000000776a000000000000776a00004d3c0000000000005e5a000042420000504c00002f2f0000130f00005c0100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001f1f00000000000000000000000000000000000000000000000000001f2d0000000000008742000000000000454200003c000000424200004242000000000000000000002f2f00000f0f00000110000000000000000000000000000000000000000000001f1f0000000000000000000000000000000000000000000000000000000000001f1f0000000000000000000000000000000000003f3c00001f1f000000000000665a000000000000635a00003f3c00005e5a000000000000424200004c4c00002f2f0000230f00000101000000000000000000001f1f0000000000001f1f000000000000000000000000000000000000000000001f1f00001f1f00001f1f00000000000000000000000000000000000000000000000000001f2d000000000000563c00003f3c0000433c000000000000423c00003f3c0000000000003c3c0000312f0000040f0000011000000000000000000000000000000000000000000000000000000000000000000000000000001f1f0000000000000000000000000000000000000000000000000000000000001f1f00003f3c000000000000000000008a87000000000000000000003f3c00006a6a000000000000424200004c4c00002f3d0000130f0000010100000000000000000000000000000000000000000000000000000000000000000000000000001f1f000000000000000000000000000000000000000000000000000000000000000000004d3c00000000000000000000aa870000000000007ac400004d3c0000006a0000005a000000420000504c00002f2f0000230f00005c010000000000001f1f0000000000000000000000000000000000001f1f00001f1f0000000000001f1f0000000000000000000000000000000000000000000000000000000000001f1f00003f3c00000000000000000000676300005e000000636300003f3c00006363000000000000424200004c4c00002f3d0000130f0000010100000000000000000000000000000000000000000000000000001f1f0000000000001f1f000000000000000000000000000000000000000000001f1f0000000000001f1f0000000000000000000000000000000000008742000042420000454200003c000000424200004242000000000000000000002f910000040f00000110000000000000000000000000000000000000000000001f1f0000000000000000000000000000000000000000000000000000000000001f1f0000000000000000000000000000000000003f3c000000000000000000008a87000000000000000000003f3c00006a6a000000000000424200004c4c00002f3d0000130f00000101000000000000000000000000000000000000000000001f1f00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000004d3c00000000000000000000aa870000000000007ac400004d3c0000006a0000005a000000420000504c00002f2f0000230f00005c0100001f1f0000000000001f1f00001f1f0000000000001f1f0000000000000000000000000000000000000000000000000000000000001f1f0000000000000000000000000000000000003f3c00000000000000000000676300005e000000636300003f3c00006363000000000000424200004c4c00002f3d0000130f00000101000000000000000000001f1f0000000000001f1f000000000000000000000000000000000000000000001f1f0000000000001f1f000000000000000000000000000000000000000000000000000000000000000000008742000042420000454200003c000000424200004242000000000000000000002f910000040f0000011000000000000000000000423c0000000000003f3c000000000000423c0000000000003f3c0000000000003f3c00004d3c00003f3c0000000000003f3c00004d3c00003f3c000000000000000000004d3c00004d3c0000563c00003f3c0000433c000000000000423c00003f3c0000000000003c3c0000322f0000230f000001100000000000001f2d000000000000000000000000000000000000331f00001f2d00001f1f00001f2d000000000000000000000000000000000000000000000000000000000000000000004d3c00000000000000000000a9870000000000007ac400004d3c0000af6a00000063000000420000504c00002f3d0000130f00005c0100001f2d000000000000331f00001f2d00001f1f00001f2d00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000004d3c00000000000000000000a9870000000000007ac400004d3c0000af6a00000063000000420000504c00002f3d0000130f00005c010000563c0000563c0000776a000087420000665a0000563c0000776a000087420000665a0000563c00008a870000aa87000067630000874200008a870000aa8700006763000087420000563c0000a9870000a9870000000000008a8700008e7a0000563c0000776a00006763000087420000554c0000372f00001b0f00000e01000000000000000000000000000000000000000000003f3c00000000000000000000000000003f3c000000000000000000005e0000004242000000000000000000005e000000424200003f3c000000000000000000008a87000000000000000000003f3c00006a6a000000000000424200004c4c00002f2f0000180f000001010000433c0000433c0000776a000045420000635a0000433c0000776a000045420000635a0000433c0000000000007ac400006363000045420000000000007ac400006363000045420000433c00007ac400007ac400008e7a000000000000000000007d3c0000776a00006363000045420000534c0000442f0000180f00000e01000000000000000000004d3c00003c0000003f3c0000000000004d3c00003c0000003f3c0000000000003f3c00004d3c00003f3c00003c0000003f3c00004d3c00003f3c00003c000000000000004d3c00004d3c0000563c00003f3c00007d3c000000000000000000003f3c00003c0000003c3c0000312f0000130f000001100000423c0000423c000000000000424200005e5a0000423c000000000000424200005e5a0000423c00006a6a0000006a000063630000424200006a6a0000006a00006363000042420000423c0000af6a0000af6a0000776a00006a6a0000776a000000000000000000006363000042420000504c0000312f0000130f00005f0100003f3c00003f3c00005e5a000042420000000000003f3c00005e5a000042420000000000003f3c000000000000005a0000000000004242000000000000005a000000000000424200003f3c000000630000006300006763000000000000636300003f3c00006363000000000000424200004c4c00002f2f0000230f0000010100000000000000000000424200000000000042420000000000004242000000000000424200000000000042420000004200004242000000000000424200000042000042420000000000000000000000420000004200008742000042420000454200003c000000424200004242000000000000000000002f2f00000f0f0000011000003c3c00003c3c0000504c0000000000004c4c00003c3c0000504c0000000000004c4c00003c3c00004c4c0000504c00004c4c0000000000004c4c0000504c00004c4c0000000000003c3c0000504c0000504c0000554c00004c4c0000534c00003c3c0000504c00004c4c000000000000000000002f2f00000f0f000012010000322f0000322f00002f2f00002f2f00002f2f0000312f00002f2f00002f2f00002f2f0000312f00002f3d00002f2f00002f3d00002f9100002f3d00002f2f00002f3d00002f910000322f00002f3d00002f3d0000372f00002f2f0000442f0000312f0000312f00002f2f00002f2f00002f2f0000000000000f0f000012010000230f0000230f0000130f00000f0f0000230f0000040f0000130f00000f0f0000230f0000040f0000130f0000230f0000130f0000040f0000130f0000230f0000130f0000040f0000230f0000130f0000130f00001b0f0000180f0000180f0000130f0000130f0000230f00000f0f00000f0f00000f0f0000000000000123000001100000011000005c0100000110000001010000011000005c010000011000000101000001100000010100005c0100000101000001100000010100005c0100000101000001100000011000005c0100005c0100000e010000010100000e010000011000005f01000001010000011000001201000012010000012300000000
def copy2Witness (p q : Finset (Sum (Fin 12) Bool) × Sig) (d : Nat) : Pair :=
  let i := copy2Entries.findIdx (fun x => x == p)
  let j := copy2Entries.findIdx (fun x => x == q)
  ⟨(((copy2WitnessCode >>> (8 * ((i * 32 + j) * 4 + d))) % 256) % 225), Nat.mod_lt _ (by decide)⟩
def copy2BridgeRows : Array Pair := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def copy2BridgeWitness (p : Finset (Fin 12) × Sig) : Pair :=
  copy2BridgeRows.getD (oldEntries.findIdx (fun x => x == p)) 0
def copy3Entries : Array (Finset (Sum (Fin 12) Bool) × Sig) := #[
  ({Sum.inl 0}, s1),
  ({Sum.inl 1}, s11),
  ({Sum.inl 2}, s3),
  ({Sum.inl 4}, s5),
  ({Sum.inl 5}, s14),
  ({Sum.inl 6}, s6),
  ({Sum.inl 7}, s7),
  ({Sum.inl 8}, s15),
  ({Sum.inl 9}, s8),
  ({Sum.inl 10}, s16),
  ({Sum.inl 11}, s9),
  ({Sum.inr false}, s4),
  ({Sum.inr true}, s4),
  ({Sum.inl 5, Sum.inl 8}, s18),
  ({Sum.inl 4, Sum.inr false}, s45),
  ({Sum.inl 5, Sum.inr false}, s46),
  ({Sum.inl 7, Sum.inr false}, s47),
  ({Sum.inl 10, Sum.inr false}, s48),
  ({Sum.inl 10, Sum.inr false}, s49),
  ({Sum.inl 4, Sum.inr true}, s45),
  ({Sum.inl 5, Sum.inr true}, s46),
  ({Sum.inl 7, Sum.inr true}, s47),
  ({Sum.inl 10, Sum.inr true}, s48),
  ({Sum.inl 10, Sum.inr true}, s49),
  ({Sum.inl 4, Sum.inl 5, Sum.inr false}, s50),
  ({Sum.inl 4, Sum.inl 10, Sum.inr false}, s51),
  ({Sum.inl 7, Sum.inl 10, Sum.inr false}, s52),
  ({Sum.inl 5, Sum.inl 10, Sum.inr false}, s53),
  ({Sum.inl 4, Sum.inl 5, Sum.inr true}, s50),
  ({Sum.inl 4, Sum.inl 10, Sum.inr true}, s51),
  ({Sum.inl 7, Sum.inl 10, Sum.inr true}, s52),
  ({Sum.inl 5, Sum.inl 10, Sum.inr true}, s53)]
def copy3WitnessCode : Nat := 0x2f2f0000000000002f2f000000000000000000002f2f00008742000000000000454200003c4b00004242000042420000000000004c4200001f1f00000f04000001010000000000000000000000000000000000000000000000000000000000002f2f000000000000000000000000000000000000000000000000000000000000000000002f2f00002f2f00003f3c000000000000312f0000776a000000000000776a00003f3c0000000000005e5a000042420000504c0000301f0000130f0000120100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000002f2f00002f2f0000000000003c3c0000000000002f2f0000554c000000000000534c00003c3c0000504c00004c4c000042420000000000002d1f00000f0f00001201000000000000000000000000000000000000000000002f2f0000000000000000000000000000000000000000000000000000000000002f2f00002f2f00002f2f0000000000000000000000000000000000002f2f00005542000042420000454200003cd90000424200004242000000000000000000002d1f00000f04000012010000000000000000000000000000000000000000000000000000000000000000000000000000000000002f2f0000000000002f2f00000000000000000000000000000000000000000000000000002f2f0000000000008742000000000000454200003c4b00004242000042420000000000004c4200001f1f00000f040000010100000000000000000000000000002f2f0000000000000000000000000000000000000000000000000000000000002f2f00002f2f000000000000000000000000000000000000000000003f3c0000312f000000000000776a000000000000776a00003f3c0000000000005e5a000042420000504c0000301f0000130f000012010000000000000000000000000000000000000000000000000000000000000000000000000000000000002f2f00002f2f00000000000000000000000000000000000000000000000000003c3c00002f2f000000000000554c000000000000534c00003c3c0000504c00004c4c000042420000000000002d1f00000f0f000012010000000000002f2f00000000000000000000000000000000000000000000000000002f2f00002f2f00002f2f000000000000000000000000000000000000000000000000000000000000000000002f2f0000000000005542000042420000454200003cd90000424200004242000000000000000000002d1f00000f04000012010000000000000000000000000000000000000000000000000000000000002f2f0000000000000000000000000000000000000000000000000000000000002f320000000000002f2f00003c4b0000000000000000000087a9000000000000000000003c4b00006a6a000000000000420000004c4c00001f1f00000f0f000001010000000000000000000000000000000000000000000000000000000000002f2f000000000000000000000000000000000000000000000000000000000000000000002f2f0000000000003f3c000000000000000000008a87000000000000c67a00003f3c0000006a0000635a000042420000004c0000301f0000180f000012010000000000000000000000000000000000002f2f0000000000002f2f00002f2f000000000000000000000000000000000000000000002f3200000000000000000000000000002f4c00003c4b00000000000000000000776a00006a6a0000776a00003c4b00000000000063630000426a0000504c00002d1f00000f0f00001201000000000000000000000000000000000000000000002f2f00002f2f0000000000000000000000000000000000000000000000000000000000002f2f00000000000000000000000000000000000000000000000000008742000042420000454200003c4b0000424200004242000000000000004200002d1f00000f04000012010000000000000000000000000000000000002f2f00002f2f0000000000000000000000000000000000000000000000000000000000002f2f0000000000002f4c000000000000000000003cd900000000000000000000554c00004c4c0000534c00003cda0000504c00004c4c000042000000000000002d1f00000f0f0000120100000000000000000000000000002f2f00000000000000000000000000000000000000000000000000002f320000000000002f2f000000000000000000000000000000000000000000003c4b0000000000000000000087a9000000000000000000003c4b00006a6a000000000000420000004c4c00001f1f00000f0f0000010100000000000000000000000000002f2f0000000000000000000000000000000000000000000000000000000000002f2f00000000000000000000000000000000000000000000000000003f3c000000000000000000008a87000000000000c67a00003f3c0000006a0000635a000042420000004c0000301f0000180f0000120100002f2f0000000000002f2f00002f2f0000000000000000000000000000000000002f3200000000000000000000000000002f4c000000000000000000000000000000000000000000003c4b00000000000000000000776a00006a6a0000776a00003c4b00000000000063630000426a0000504c00002d1f00000f0f000012010000000000002f2f00002f2f00000000000000000000000000000000000000000000000000002f2f000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000008742000042420000454200003c4b0000424200004242000000000000004200002d1f00000f040000120100002f2f00002f2f00000000000000000000000000000000000000000000000000002f2f0000000000002f4c0000000000000000000000000000000000000000000000000000000000003cd900000000000000000000554c00004c4c0000534c00003cda0000504c00004c4c000042000000000000002d1f00000f0f000012010000000000003f3c00003c3c000000000000000000003f3c00003c3c0000000000003c4b00003f3c00003c4b0000000000003cd900003c4b00003f3c00003c4b0000000000003cd90000000000003c4b00003c4b0000563c00003f3c0000433c000000000000423c00003f3c0000000000003c3c00001f2d0000230f000001100000000000000000000000000000000000002f2f0000312f00002f2f00002f2f0000000000000000000000000000000000000000000000000000000000000000000000000000000000003c4b0000000000000000000087a9000000000000c67a00003c4b0000006a00006363000042000000004c00002d1f00000f0f0000120100002f2f0000312f00002f2f00002f2f000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000003c4b0000000000000000000087a9000000000000c67a00003c4b0000006a00006363000042000000004c00002d1f00000f0f00001201000087420000776a0000554c00005542000087420000776a0000554c00005542000087a900008a870000776a000087420000554c000087a900008a870000776a000087420000554c0000563c000087a9000087a90000000000008a8700008e7a0000563c0000776a00006763000087420000554c00002c1f00001b0f00000e010000000000000000000000000000424200000000000000000000000000004242000000000000000000006a6a0000424200004c4c000000000000000000006a6a0000424200004c4c00003f3c000000000000000000008a87000000000000000000003f3c00006a6a000000000000424200004c4c00001f1f0000180f00000101000045420000776a0000534c00004542000045420000776a0000534c00004542000000000000c67a0000776a000045420000534c000000000000c67a0000776a000045420000534c0000433c0000c67a0000c67a00008e7a000000000000000000007d3c0000776a00006363000045420000534c00002c1f0000180f00000e0100003c4b00003f3c00003c3c00003cd900003c4b00003f3c00003c3c00003cd900003c4b00003f3c00003c4b00003c4b00003cda00003c4b00003f3c00003c4b00003c4b00003cda0000000000003c4b00003c4b0000563c00003f3c00007d3c000000000000000000003f3c00003c0000003c3c00001f2d0000130f0000011000004242000000000000504c0000424200004242000000000000504c0000424200006a6a0000006a00000000000042420000504c00006a6a0000006a00000000000042420000504c0000423c0000006a0000006a0000776a00006a6a0000776a000000000000000000006363000042420000504c0000331f0000130f00005f010000424200005e5a00004c4c000042420000424200005e5a00004c4c00004242000000000000635a000063630000424200004c4c000000000000635a000063630000424200004c4c00003f3c000063630000636300006763000000000000636300003f3c00006363000000000000424200004c4c00001f1f0000230f00000101000000000000424200004242000000000000000000004242000042420000000000004200000042420000426a000000000000420000004200000042420000426a000000000000420000000000000042000000420000008742000042420000454200003c000000424200004242000000000000000000001f2d00000f0f0000011000004c420000504c000000000000000000004c420000504c000000000000000000004c4c0000004c0000504c000000420000000000004c4c0000004c0000504c000000420000000000003c3c0000004c0000004c0000554c00004c4c0000534c00003c3c0000504c00004c4c000000000000000000002d1f00000f0f0000120100001f1f0000301f00002d1f00002d1f00001f1f0000301f00002d1f00002d1f00001f1f0000301f00002d1f00002d1f00002d1f00001f1f0000301f00002d1f00002d1f00002d1f00001f2d00002d1f00002d1f00002c1f00001f1f00002c1f00001f2d0000331f00001f1f00001f2d00002d1f000000000000130f00002d0100000f040000130f00000f0f00000f0400000f040000130f00000f0f00000f0400000f0f0000180f00000f0f00000f0400000f0f00000f0f0000180f00000f0f00000f0400000f0f0000230f00000f0f00000f0f00001b0f0000180f0000180f0000130f0000130f0000230f00000f0f00000f0f0000130f000000000000012300000101000012010000120100001201000001010000120100001201000012010000010100001201000012010000120100001201000001010000120100001201000012010000120100000110000012010000120100000e010000010100000e010000011000005f0100000101000001100000120100002d010000012300000000
def copy3Witness (p q : Finset (Sum (Fin 12) Bool) × Sig) (d : Nat) : Pair :=
  let i := copy3Entries.findIdx (fun x => x == p)
  let j := copy3Entries.findIdx (fun x => x == q)
  ⟨(((copy3WitnessCode >>> (8 * ((i * 32 + j) * 4 + d))) % 256) % 225), Nat.mod_lt _ (by decide)⟩
def copy3BridgeRows : Array Pair := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def copy3BridgeWitness (p : Finset (Fin 12) × Sig) : Pair :=
  copy3BridgeRows.getD (oldEntries.findIdx (fun x => x == p)) 0
def copy4Entries : Array (Finset (Sum (Fin 12) Bool) × Sig) := #[
  ({Sum.inl 0}, s1),
  ({Sum.inl 1}, s11),
  ({Sum.inl 2}, s3),
  ({Sum.inl 3}, s4),
  ({Sum.inl 5}, s14),
  ({Sum.inl 6}, s6),
  ({Sum.inl 7}, s7),
  ({Sum.inl 8}, s15),
  ({Sum.inl 9}, s8),
  ({Sum.inl 10}, s16),
  ({Sum.inl 11}, s9),
  ({Sum.inr false}, s5),
  ({Sum.inr true}, s5),
  ({Sum.inl 5, Sum.inl 8}, s18),
  ({Sum.inl 6, Sum.inr false}, s54),
  ({Sum.inl 7, Sum.inr false}, s55),
  ({Sum.inl 10, Sum.inr false}, s56),
  ({Sum.inl 10, Sum.inr false}, s57),
  ({Sum.inl 6, Sum.inr true}, s54),
  ({Sum.inl 7, Sum.inr true}, s55),
  ({Sum.inl 10, Sum.inr true}, s56),
  ({Sum.inl 10, Sum.inr true}, s57),
  ({Sum.inl 6, Sum.inl 10, Sum.inr false}, s58),
  ({Sum.inl 1, Sum.inl 10, Sum.inr false}, s59),
  ({Sum.inl 7, Sum.inl 10, Sum.inr false}, s60),
  ({Sum.inl 6, Sum.inl 10, Sum.inr true}, s58),
  ({Sum.inl 1, Sum.inl 10, Sum.inr true}, s59),
  ({Sum.inl 7, Sum.inl 10, Sum.inr true}, s60)]
def copy4WitnessCode : Nat := 0x4c4c00003f3c000000000000504c0000776a000000000000776a00003f3c0000000000005e5a0000424200002f2f0000301f0000130f0000120100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000f0f00000f0f0000200f0000000000000f0f00001b0f000000000000180f0000130f0000130f0000230f00000f0f00000f0f0000130f000000000000012300000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000004c4c0000000000003f3c0000000000004c4c0000665a000000000000635a00003f3c00005e5a000000000000424200002f2f00001f1f0000230f0000010100000000000000000000000000000000000000000000000000000000000000000000000000004c4c0000000000000000000000000000000000003f3c0000504c000000000000776a000000000000776a00003f3c0000000000005e5a0000424200002f2f0000301f0000130f00001201000000000000000000000000000000000000000000000000000000000000000000000f0f00000f0f000000000000000000000000000000000000200f00000f0f0000000000001b0f000000000000180f0000130f0000130f0000230f00000f0f00000f0f0000130f0000000000000123000000000000000000000000000000000000000000000000000000000000000000004c4c000000000000000000000000000000000000000000003f3c00004c4c000000000000665a000000000000635a00003f3c00005e5a000000000000424200002f2f00001f1f0000230f0000010100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000004c500000000000003c3c000000000000000000008787000000000000000000003c3c00006a6a000000000000424200002f2f00001f1f00000f0f00000101000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000003f3c000000000000000000008a870000000000007a7a00003f3c0000006a0000005a0000000000002f2f0000301f0000000f000012010000000000000000000000000000000000000f0f00004c4c0000000000000000000000000000000000004c50000000000000000000004c5000003c3c00000000000000000000776a00006a6a0000776a00003c3c00000000000063630000424200002f2f00002d1f00000f0f0000120100000000000000000000000000004c4c00000f0f0000000000000000000000000000000000000000000000000000000000004c500000000000003c3c00000000000000000000676300005a000000636300003c3c00006363000000000000424200002f2f00001f1f00000f0f00000101000000000000000000000000000000000000000000000000000000000000000000004c50000000000000000000000000000000000000000000003c3c000000000000000000008787000000000000000000003c3c00006a6a000000000000424200002f2f00001f1f00000f0f00000101000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000003f3c000000000000000000008a870000000000007a7a00003f3c0000006a0000005a0000000000002f2f0000301f0000000f000012010000000000000f0f00004c4c00000000000000000000000000004c50000000000000000000004c500000000000000000000000000000000000003c3c00000000000000000000776a00006a6a0000776a00003c3c00000000000063630000424200002f2f00002d1f00000f0f0000120100004c4c00000f0f00000000000000000000000000000000000000000000000000004c50000000000000000000000000000000000000000000003c3c00000000000000000000676300005a000000636300003c3c00006363000000000000424200002f2f00001f1f00000f0f0000010100003f3c0000200f00003f3c00003f3c0000200f00003f3c00003c3c00003f3c00003c3c00003c3c00003c3c00003f3c00003c3c00003c3c0000000000003c3c00003c3c0000563c00003f3c0000433c000000000000423c00003f3c000000000000322f00001f2d0000230f000001100000000000000000000000000000504c00000f0f00004c4c000000000000000000000000000000000000000000000000000000000000000000003c3c0000000000000000000087870000000000007a7a00003c3c0000006a000000630000000000002f2f00002d1f00000f0f000012010000504c00000f0f00004c4c000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000003c3c0000000000000000000087870000000000007a7a00003c3c0000006a000000630000000000002f2f00002d1f00000f0f000012010000776a00001b0f0000665a0000776a00001b0f0000665a0000878700008a870000776a000067630000878700008a870000776a000067630000563c00008787000087870000000000008a8700008e7a0000563c0000776a00006763000087420000372f00002c1f00001b0f00000e01000000000000000000000000000000000000000000000000000000000000000000006a6a00005a00000000000000000000006a6a00005a0000003f3c000000000000000000008a87000000000000000000003f3c00006a6a000000000000424200002f2f00001f1f0000180f000001010000776a0000180f0000635a0000776a0000180f0000635a0000000000007a7a0000776a000063630000000000007a7a0000776a000063630000433c00007a7a00007a7a00008e7a000000000000000000007d3c0000776a00006363000045420000442f00002c1f0000180f00000e0100003f3c0000130f00003f3c00003f3c0000130f00003f3c00003c3c00003f3c00003c3c00003c3c00003c3c00003f3c00003c3c00003c3c0000000000003c3c00003c3c0000563c00003f3c00007d3c000000000000000000003f3c00003c000000312f00001f2d0000130f00000110000000000000130f00005e5a000000000000130f00005e5a00006a6a0000006a000000000000636300006a6a0000006a00000000000063630000423c0000006a0000006a0000776a00006a6a0000776a000000000000000000006363000042420000312f0000331f0000130f00005f0100005e5a0000230f0000000000005e5a0000230f00000000000000000000005a0000636300000000000000000000005a000063630000000000003f3c000000630000006300006763000000000000636300003f3c00006363000000000000424200002f2f00001f1f0000230f000001010000424200000f0f000042420000424200000f0f00004242000042420000000000004242000042420000424200000000000042420000424200000000000000000000000000008742000042420000454200003c0000004242000042420000000000002f2f00001f2d00000f0f0000011000002f2f00000f0f00002f2f00002f2f00000f0f00002f2f00002f2f00002f2f00002f2f00002f2f00002f2f00002f2f00002f2f00002f2f0000322f00002f2f00002f2f0000372f00002f2f0000442f0000312f0000312f00002f2f00002f2f0000000000002d1f00000f0f000012010000301f0000130f00001f1f0000301f0000130f00001f1f00001f1f0000301f00002d1f00001f1f00001f1f0000301f00002d1f00001f1f00001f2d00002d1f00002d1f00002c1f00001f1f00002c1f00001f2d0000331f00001f1f00001f2d00002d1f000000000000130f00002d010000130f000000000000230f0000130f000000000000230f00000f0f0000000f00000f0f00000f0f00000f0f0000000f00000f0f00000f0f0000230f00000f0f00000f0f00001b0f0000180f0000180f0000130f0000130f0000230f00000f0f00000f0f0000130f0000000000000123000012010000012300000101000012010000012300000101000001010000120100001201000001010000010100001201000012010000010100000110000012010000120100000e010000010100000e010000011000005f0100000101000001100000120100002d010000012300000000
def copy4Witness (p q : Finset (Sum (Fin 12) Bool) × Sig) (d : Nat) : Pair :=
  let i := copy4Entries.findIdx (fun x => x == p)
  let j := copy4Entries.findIdx (fun x => x == q)
  ⟨(((copy4WitnessCode >>> (8 * ((i * 28 + j) * 4 + d))) % 256) % 225), Nat.mod_lt _ (by decide)⟩
def copy4BridgeRows : Array Pair := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def copy4BridgeWitness (p : Finset (Fin 12) × Sig) : Pair :=
  copy4BridgeRows.getD (oldEntries.findIdx (fun x => x == p)) 0
def copy5Entries : Array (Finset (Sum (Fin 12) Bool) × Sig) := #[
  ({Sum.inl 0}, s1),
  ({Sum.inl 1}, s11),
  ({Sum.inl 2}, s3),
  ({Sum.inl 3}, s4),
  ({Sum.inl 4}, s5),
  ({Sum.inl 6}, s6),
  ({Sum.inl 7}, s7),
  ({Sum.inl 8}, s15),
  ({Sum.inl 9}, s8),
  ({Sum.inl 10}, s16),
  ({Sum.inl 11}, s9),
  ({Sum.inr false}, s14),
  ({Sum.inr true}, s14),
  ({Sum.inl 8, Sum.inr false}, s18),
  ({Sum.inl 10, Sum.inr false}, s61),
  ({Sum.inl 10, Sum.inr false}, s62),
  ({Sum.inl 8, Sum.inr true}, s18),
  ({Sum.inl 10, Sum.inr true}, s61),
  ({Sum.inl 10, Sum.inr true}, s62),
  ({Sum.inl 8, Sum.inl 10, Sum.inr false}, s63),
  ({Sum.inl 8, Sum.inl 10, Sum.inr true}, s63),
  ({Sum.inl 8, Sum.inl 10, Sum.inr false, Sum.inr true}, s18)]
def copy5WitnessCode : Nat := 0x563c000000000000433c000000000000423c00003f3c00003c3c0000322f00001f2d0000230f000001100000000000000000000000000000000000000000000000000000000000000000000000000000000000003c000000563c0000000000007d3c0000000000006a3c00003f3c00003c3c0000322f00001f2d0000180f0000011000000000000000000000000000000000000000000000000000000000000000000000000000003c00000000000000563c0000000000007d3c0000000000006a3c00003f3c00003c3c0000322f00001f2d0000180f00000110000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000008787000000000000000000003c0000006a6a000000000000000000002f2f00001f2d00000f0f00000110000000000000000000000000000000000000000000000000000000000000000000003f3c000000000000000000008a870000000000007a7a00003f3c00006a6a0000c25a00004c4c00002f2f00001f1f0000230f000001010000000000000000000000000000000000000000000000000000000000003f3c0000000000000000000000000000563c00003f3c00007d3c0000000000006a3c00003f3c00003c3c0000322f00001f2d0000230f00000110000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000008787000000000000000000003c0000006a6a000000000000000000002f2f00001f2d00000f0f00000110000000000000000000000000000000000000000000003f3c000000000000000000000000000000000000000000008a870000000000007a7a00003f3c00006a6a0000c25a00004c4c00002f2f00001f1f0000230f000001010000000000000000000000000000000000003f3c0000000000000000000000000000000000000000000000000000563c00003f3c00007d3c0000000000006a3c00003f3c00003c3c0000322f00001f2d0000230f00000110000000000000000000003c000000000000000000000000000000000000000000000000000000000000000000000087870000000000007a7a00003c0000006a6a0000c2630000000000002f2f00001f2d00000f0f000001100000000000003c00000000000000000000000000000000000000000000000000000000000000000000000000000087870000000000007a7a00003c0000006a6a0000c2630000000000002f2f00001f2d00000f0f000001100000563c0000563c0000563c0000878700008a870000563c0000878700008a870000563c00008787000087870000000000008a8700008e7a0000563c0000776a000067630000554c0000372f00002c1f00001b0f00000e01000000000000000000000000000000000000000000003f3c000000000000000000003f3c000000000000000000008a87000000000000000000003f3c00006a6a0000000000004c4c00002f2f00001f1f0000180f000001010000433c00007d3c00007d3c0000000000007a7a00007d3c0000000000007a7a00007d3c00007a7a00007a7a00008e7a000000000000000000007d3c0000776a000063630000534c0000442f00002c1f0000180f00000e0100000000000000000000000000003c0000003f3c0000000000003c0000003f3c0000000000003c0000003c000000563c00003f3c00007d3c000000000000000000003f3c00003c3c0000312f00001f2d0000130f000001100000423c00006a3c00006a3c00006a6a00006a6a00006a3c00006a6a00006a6a00006a3c00006a6a00006a6a0000776a00006a6a0000776a0000000000000000000063630000504c0000312f0000331f0000130f00005f0100003f3c00003f3c00003f3c000000000000c25a00003f3c000000000000c25a00003f3c0000c2630000c26300006763000000000000636300003f3c000063630000000000004c4c00002f2f00001f1f0000230f0000010100003c3c00003c3c00003c3c0000000000004c4c00003c3c0000000000004c4c00003c3c00000000000000000000554c00004c4c0000534c00003c3c0000504c00004c4c0000000000002f2f00002d1f00000f0f000012010000322f0000322f0000322f00002f2f00002f2f0000322f00002f2f00002f2f0000322f00002f2f00002f2f0000372f00002f2f0000442f0000312f0000312f00002f2f00002f2f0000000000002d1f00000f0f0000120100001f2d00001f2d00001f2d00001f2d00001f1f00001f2d00001f2d00001f1f00001f2d00001f2d00001f2d00002c1f00001f1f00002c1f00001f2d0000331f00001f1f00002d1f00002d1f000000000000130f00002d010000230f0000180f0000180f00000f0f0000230f0000230f00000f0f0000230f0000230f00000f0f00000f0f00001b0f0000180f0000180f0000130f0000130f0000230f00000f0f00000f0f0000130f0000000000000123000001100000011000000110000001100000010100000110000001100000010100000110000001100000011000000e010000010100000e010000011000005f0100000101000012010000120100002d010000012300000000
def copy5Witness (p q : Finset (Sum (Fin 12) Bool) × Sig) (d : Nat) : Pair :=
  let i := copy5Entries.findIdx (fun x => x == p)
  let j := copy5Entries.findIdx (fun x => x == q)
  ⟨(((copy5WitnessCode >>> (8 * ((i * 22 + j) * 4 + d))) % 256) % 225), Nat.mod_lt _ (by decide)⟩
def copy5BridgeRows : Array Pair := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def copy5BridgeWitness (p : Finset (Fin 12) × Sig) : Pair :=
  copy5BridgeRows.getD (oldEntries.findIdx (fun x => x == p)) 0
def copy6Entries : Array (Finset (Sum (Fin 12) Bool) × Sig) := #[
  ({Sum.inl 0}, s1),
  ({Sum.inl 1}, s11),
  ({Sum.inl 2}, s3),
  ({Sum.inl 3}, s4),
  ({Sum.inl 4}, s5),
  ({Sum.inl 5}, s14),
  ({Sum.inl 7}, s7),
  ({Sum.inl 8}, s15),
  ({Sum.inl 9}, s8),
  ({Sum.inl 10}, s16),
  ({Sum.inl 11}, s9),
  ({Sum.inr false}, s6),
  ({Sum.inr true}, s6),
  ({Sum.inl 5, Sum.inl 8}, s18)]
def copy6WitnessCode : Nat := 0x3f3c00003f3c0000563c00003f3c0000433c000000000000423c0000000000003c3c0000322f00001f2d0000230f0000011000003f3c000000000000000000008a870000000000007a7a00003f3c00006a6a0000424200004c4c00002f2f00001f1f0000230f0000010100003f3c000000000000000000008a870000000000007a7a00003f3c00006a6a0000424200004c4c00002f2f00001f1f0000230f000001010000563c00008a8700008a870000000000008a8700008e7a0000563c0000776a000087420000554c0000372f00002c1f00001b0f00000e0100003f3c000000000000000000008a87000000000000000000003f3c00006a6a0000424200004c4c00002f2f00001f1f0000180f000001010000433c00007a7a00007a7a00008e7a000000000000000000007d3c0000776a000045420000534c0000442f00002c1f0000180f00000e010000000000003f3c00003f3c0000563c00003f3c00007d3c000000000000000000003c0000003c3c0000312f00001f2d0000130f000001100000423c00006a6a00006a6a0000776a00006a6a0000776a0000000000000000000042420000504c0000312f0000331f0000130f00005f0100000000000042420000424200008742000042420000454200003c0000004242000000000000000000002f2f00001f2d00000f0f0000011000003c3c00004c4c00004c4c0000554c00004c4c0000534c00003c3c0000504c000000000000000000002f2f00002d1f00000f0f000012010000322f00002f2f00002f2f0000372f00002f2f0000442f0000312f0000312f00002f2f00002f2f0000000000002d1f00000f0f0000120100001f2d00001f1f00001f1f00002c1f00001f1f00002c1f00001f2d0000331f00001f2d00002d1f00002d1f000000000000130f00002d010000230f0000230f0000230f00001b0f0000180f0000180f0000130f0000130f00000f0f00000f0f00000f0f0000130f000000000000012300000110000001010000010100000e010000010100000e010000011000005f0100000110000012010000120100002d010000012300000000
def copy6Witness (p q : Finset (Sum (Fin 12) Bool) × Sig) (d : Nat) : Pair :=
  let i := copy6Entries.findIdx (fun x => x == p)
  let j := copy6Entries.findIdx (fun x => x == q)
  ⟨(((copy6WitnessCode >>> (8 * ((i * 14 + j) * 4 + d))) % 256) % 225), Nat.mod_lt _ (by decide)⟩
def copy6BridgeRows : Array Pair := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def copy6BridgeWitness (p : Finset (Fin 12) × Sig) : Pair :=
  copy6BridgeRows.getD (oldEntries.findIdx (fun x => x == p)) 0
def copy7Entries : Array (Finset (Sum (Fin 12) Bool) × Sig) := #[
  ({Sum.inl 0}, s1),
  ({Sum.inl 1}, s11),
  ({Sum.inl 2}, s3),
  ({Sum.inl 3}, s4),
  ({Sum.inl 4}, s5),
  ({Sum.inl 5}, s14),
  ({Sum.inl 6}, s6),
  ({Sum.inl 8}, s15),
  ({Sum.inl 9}, s8),
  ({Sum.inl 10}, s16),
  ({Sum.inl 11}, s9),
  ({Sum.inr false}, s7),
  ({Sum.inr true}, s7),
  ({Sum.inl 5, Sum.inl 8}, s18),
  ({Sum.inl 10, Sum.inr false}, s64),
  ({Sum.inl 10, Sum.inr false}, s65),
  ({Sum.inl 10, Sum.inr true}, s64),
  ({Sum.inl 10, Sum.inr true}, s65)]
def copy7WitnessCode : Nat := 0x3f3c000000000000000000008a87000000000000000000003f3c000000000000424200004c4c00002f2f00001f1f0000130f00000101000000000000000000000000000000000000423c000000000000000000008d870000000000007d7a000000000000635a000042420000504c0000322f0000331f0000180f00005f010000000000000000000000000000000000003f3c000000000000000000008a87000000000000000000003f3c000000000000424200004c4c00002f2f00001f1f0000130f00000101000000000000000000000000000000000000423c000000000000000000008d870000000000007d7a000000000000635a000042420000504c0000322f0000331f0000180f00005f0100003f3c0000423c00003f3c0000423c000000000000423c0000423c0000563c00003f3c0000433c0000000000003f3c0000000000003c3c0000322f00001f2d0000230f00000110000000000000000000000000000000000000423c000000000000000000008d870000000000007d7a0000000000006363000042420000504c0000312f0000331f0000130f00005f01000000000000000000000000000000000000423c000000000000000000008d870000000000007d7a0000000000006363000042420000504c0000312f0000331f0000130f00005f0100008a8700008d8700008a8700008d870000563c00008d8700008d870000000000008a8700008e7a0000563c00006763000087420000554c0000372f00002c1f00001b0f00000e010000000000000000000000000000000000003f3c000000000000000000008a87000000000000000000003f3c000000000000424200004c4c00002f2f00001f1f0000180f000001010000000000007d7a0000000000007d7a0000433c00007d7a00007d7a00008e7a000000000000000000007d3c00006363000045420000534c0000442f00002c1f0000180f00000e0100003f3c0000000000003f3c000000000000000000000000000000000000563c00003f3c00007d3c0000000000003f3c00003c0000003c3c0000312f00001f2d0000130f00000110000000000000635a000000000000635a00003f3c000063630000636300006763000000000000636300003f3c000000000000424200004c4c00002f2f00001f1f0000230f000001010000424200004242000042420000424200000000000042420000424200008742000042420000454200003c0000004242000000000000000000002f2f00001f2d00000f0f0000011000004c4c0000504c00004c4c0000504c00003c3c0000504c0000504c0000554c00004c4c0000534c00003c3c00004c4c000000000000000000002f2f00002d1f00000f0f0000120100002f2f0000322f00002f2f0000322f0000322f0000312f0000312f0000372f00002f2f0000442f0000312f00002f2f00002f2f00002f2f0000000000002d1f00000f0f0000120100001f1f0000331f00001f1f0000331f00001f2d0000331f0000331f00002c1f00001f1f00002c1f00001f2d00001f1f00001f2d00002d1f00002d1f000000000000130f00002d010000130f0000180f0000130f0000180f0000230f0000130f0000130f00001b0f0000180f0000180f0000130f0000230f00000f0f00000f0f00000f0f0000130f00000000000001230000010100005f010000010100005f010000011000005f0100005f0100000e010000010100000e01000001100000010100000110000012010000120100002d010000012300000000
def copy7Witness (p q : Finset (Sum (Fin 12) Bool) × Sig) (d : Nat) : Pair :=
  let i := copy7Entries.findIdx (fun x => x == p)
  let j := copy7Entries.findIdx (fun x => x == q)
  ⟨(((copy7WitnessCode >>> (8 * ((i * 18 + j) * 4 + d))) % 256) % 225), Nat.mod_lt _ (by decide)⟩
def copy7BridgeRows : Array Pair := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def copy7BridgeWitness (p : Finset (Fin 12) × Sig) : Pair :=
  copy7BridgeRows.getD (oldEntries.findIdx (fun x => x == p)) 0
def copy8Entries : Array (Finset (Sum (Fin 12) Bool) × Sig) := #[
  ({Sum.inl 0}, s1),
  ({Sum.inl 1}, s11),
  ({Sum.inl 2}, s3),
  ({Sum.inl 3}, s4),
  ({Sum.inl 4}, s5),
  ({Sum.inl 5}, s14),
  ({Sum.inl 6}, s6),
  ({Sum.inl 7}, s7),
  ({Sum.inl 9}, s8),
  ({Sum.inl 10}, s16),
  ({Sum.inl 11}, s9),
  ({Sum.inr false}, s15),
  ({Sum.inr true}, s15),
  ({Sum.inl 5, Sum.inr false}, s18),
  ({Sum.inl 10, Sum.inr false}, s66),
  ({Sum.inl 10, Sum.inr false}, s67),
  ({Sum.inl 5, Sum.inr true}, s18),
  ({Sum.inl 10, Sum.inr true}, s66),
  ({Sum.inl 10, Sum.inr true}, s67),
  ({Sum.inl 4, Sum.inl 10, Sum.inr false}, s68),
  ({Sum.inl 5, Sum.inl 10, Sum.inr false}, s69),
  ({Sum.inl 4, Sum.inl 10, Sum.inr true}, s68),
  ({Sum.inl 5, Sum.inl 10, Sum.inr true}, s69),
  ({Sum.inl 5, Sum.inl 10, Sum.inr false, Sum.inr true}, s18)]
def copy8WitnessCode : Nat := 0x563c000000000000433c0000423c00003f3c0000000000003c3c0000322f00001f2d0000230f0000011000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000003f0000008a42000000000000454200004242000042420000000000004c4200002f2f00001f2d0000230f000001100000000000000000000000000000000000000000000000000000000000000000000000000000000000003f3c0000000000003f3c0000554c000000000000534c0000504c00004c4c000000000000000000002f2f0000301f00004c0f00001201000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000003f000000000000008a42000000000000454200004242000042420000000000004c4200002f2f00001f2d0000230f000001100000000000000000000000000000000000000000000000000000000000003f3c00000000000000000000000000003f3c000000000000554c000000000000534c0000504c00004c4c000000000000000000002f2f0000301f00004c0f000012010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000008a87000000000000000000000000000000000000420000004c0000002f2f00001f2d0000130f00000110000000000000000000000000000000000000000000000000000000000000000000000000000000000000423c000000000000000000008d870000000000007d7a00006a6a0000635a0000424200004c4c0000322f00001f1f0000180f000001010000000000000000000000000000000000003f3c000000000000000000000000000000000000423c0000000000000000000000000000aa42000042420000454200004242000042420000000000004c420000322f00001f2d0000230f000001100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000008a87000000000000000000000000000000000000420000004c0000002f2f00001f2d0000130f00000110000000000000000000000000000000000000000000000000000000000000423c000000000000000000000000000000000000000000008d870000000000007d7a00006a6a0000635a0000424200004c4c0000322f00001f1f0000180f00000101000000000000000000003f3c0000000000000000000000000000423c0000000000000000000000000000000000000000000000000000aa42000042420000454200004242000042420000000000004c420000322f00001f2d0000230f0000011000000000000000000000000000003f0000003f3c000000000000000000000000000000000000000000000000000000000000000000008d870000000000007d7a00000000000063630000420000004cda0000312f00001f2d0000130f000001100000000000003f0000003f3c0000000000000000000000000000000000000000000000000000000000000000000000000000000000008d870000000000007d7a00000000000063630000420000004cda0000312f00001f2d0000130f000001100000563c00008a420000554c00008a420000554c00008a8700008d870000aa4200008a8700008d870000aa4200008d8700008d870000000000008a8700008e7a0000776a00006763000087420000554c0000372f00002c1f00001b0f00000e010000000000000000000000000000000000000000000000000000000000004242000000000000000000004242000000000000000000008a87000000000000000000006a6a000000000000424200004c4c00002f2f00001f1f0000180f000001010000433c000045420000534c000045420000534c0000000000007d7a000045420000000000007d7a0000454200007d7a00007d7a00008e7a00000000000000000000776a00006363000045420000534c0000442f00002c1f0000180f00000e010000423c000042420000504c000042420000504c0000000000006a6a000042420000000000006a6a0000424200000000000000000000776a00006a6a0000776a0000000000006363000042420000504c0000312f0000331f0000130f00005f0100003f3c0000424200004c4c0000424200004c4c000000000000635a00004242000000000000635a00004242000063630000636300006763000000000000636300006363000000000000424200004c4c00002f2f00001f1f0000230f00000101000000000000000000000000000000000000000000004200000042420000000000004200000042420000000000004200000042000000874200004242000045420000424200004242000000000000000000002f2f00001f2d00000f0f0000011000003c3c00004c420000000000004c420000000000004c0000004c4c00004c4200004c0000004c4c00004c4200004cda00004cda0000554c00004c4c0000534c0000504c00004c4c000000000000000000002f2f00002d1f00000f0f000012010000322f00002f2f00002f2f00002f2f00002f2f00002f2f0000322f0000322f00002f2f0000322f0000322f0000312f0000312f0000372f00002f2f0000442f0000312f00002f2f00002f2f00002f2f0000000000002d1f00000f0f0000120100001f2d00001f2d0000301f00001f2d0000301f00001f2d00001f1f00001f2d00001f2d00001f1f00001f2d00001f2d00001f2d00002c1f00001f1f00002c1f0000331f00001f1f00001f2d00002d1f00002d1f000000000000130f00002d010000230f0000230f00004c0f0000230f00004c0f0000130f0000180f0000230f0000130f0000180f0000230f0000130f0000130f00001b0f0000180f0000180f0000130f0000230f00000f0f00000f0f00000f0f0000130f00000000000001230000011000000110000012010000011000001201000001100000010100000110000001100000010100000110000001100000011000000e010000010100000e0100005f010000010100000110000012010000120100002d010000012300000000
def copy8Witness (p q : Finset (Sum (Fin 12) Bool) × Sig) (d : Nat) : Pair :=
  let i := copy8Entries.findIdx (fun x => x == p)
  let j := copy8Entries.findIdx (fun x => x == q)
  ⟨(((copy8WitnessCode >>> (8 * ((i * 24 + j) * 4 + d))) % 256) % 225), Nat.mod_lt _ (by decide)⟩
def copy8BridgeRows : Array Pair := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def copy8BridgeWitness (p : Finset (Fin 12) × Sig) : Pair :=
  copy8BridgeRows.getD (oldEntries.findIdx (fun x => x == p)) 0
def copy9Entries : Array (Finset (Sum (Fin 12) Bool) × Sig) := #[
  ({Sum.inl 0}, s1),
  ({Sum.inl 1}, s11),
  ({Sum.inl 2}, s3),
  ({Sum.inl 3}, s4),
  ({Sum.inl 4}, s5),
  ({Sum.inl 5}, s14),
  ({Sum.inl 6}, s6),
  ({Sum.inl 7}, s7),
  ({Sum.inl 8}, s15),
  ({Sum.inl 10}, s16),
  ({Sum.inl 11}, s9),
  ({Sum.inr false}, s8),
  ({Sum.inr true}, s8),
  ({Sum.inl 5, Sum.inl 8}, s18),
  ({Sum.inl 8, Sum.inr false}, s70),
  ({Sum.inl 8, Sum.inr true}, s70),
  ({Sum.inl 5, Sum.inl 8, Sum.inr false}, s71),
  ({Sum.inl 5, Sum.inl 8, Sum.inr true}, s71)]
def copy9WitnessCode : Nat := 0x433c0000563c00003f3c000000000000423c00003f3c0000000000003c3c0000322f00001f2d0000230f0000011000000000000000000000000000000000000000000000433c000000000000563c00003f3c000000000000423c00003f3c0000000000003c3c0000322f00001f2d0000230f00000110000000000000000000000000000000000000000000000000000000000000563c00003f3c000000000000000000003f3c00003c0000003c3c0000312f00001f2d0000130f00000110000000000000000000000000000000000000000000000000000000000000563c00003f3c000000000000000000003f3c00003c0000003c3c0000312f00001f2d0000130f0000011000000000000000000000000000000000000000000000433c0000433c0000563c00003f3c000000000000423c00003f3c0000000000003c3c0000322f00001f2d0000230f00000110000000000000433c00000000000000000000433c000000000000000000008e87000000000000003c0000776a00006363000045420000534c0000442f00002c1f0000180f00000e010000433c0000000000000000000000000000433c000000000000000000008e87000000000000003c0000776a00006363000045420000534c0000442f00002c1f0000180f00000e010000563c0000563c0000563c0000563c0000563c00008e8700008e870000000000008a870000563c0000776a00006763000087420000554c0000372f00002c1f00001b0f00000e0100003f3c00003f3c00003f3c00003f3c00003f3c000000000000000000008a870000000000003f3c00006a6a000000000000424200004c4c00002f2f00001f1f0000180f0000010100000000000000000000000000000000000000000000003c0000003c0000563c00003f3c000000000000000000003f3c00003c0000003c3c0000312f00001f2d0000130f000001100000423c0000423c00000000000000000000423c0000776a0000776a0000776a00006a6a000000000000000000006363000042420000504c0000312f0000331f0000130f00005f0100003f3c00003f3c00003f3c00003f3c00003f3c0000636300006363000067630000000000003f3c00006363000000000000424200004c4c00002f2f00001f1f0000230f00000101000000000000000000003c0000003c00000000000000454200004542000087420000424200003c000000424200004242000000000000000000002f2f00001f2d00000f0f0000011000003c3c00003c3c00003c3c00003c3c00003c3c0000534c0000534c0000554c00004c4c00003c3c0000504c00004c4c000000000000000000002f2f00002d1f00000f0f000012010000322f0000322f0000312f0000312f0000322f0000442f0000442f0000372f00002f2f0000312f0000312f00002f2f00002f2f00002f2f0000000000002d1f00000f0f0000120100001f2d00001f2d00001f2d00001f2d00001f2d00002c1f00002c1f00002c1f00001f1f00001f2d0000331f00001f1f00001f2d00002d1f00002d1f000000000000130f00002d010000230f0000230f0000130f0000130f0000230f0000180f0000180f00001b0f0000180f0000130f0000130f0000230f00000f0f00000f0f00000f0f0000130f0000000000000123000001100000011000000110000001100000011000000e0100000e0100000e01000001010000011000005f010000010100000110000012010000120100002d010000012300000000
def copy9Witness (p q : Finset (Sum (Fin 12) Bool) × Sig) (d : Nat) : Pair :=
  let i := copy9Entries.findIdx (fun x => x == p)
  let j := copy9Entries.findIdx (fun x => x == q)
  ⟨(((copy9WitnessCode >>> (8 * ((i * 18 + j) * 4 + d))) % 256) % 225), Nat.mod_lt _ (by decide)⟩
def copy9BridgeRows : Array Pair := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def copy9BridgeWitness (p : Finset (Fin 12) × Sig) : Pair :=
  copy9BridgeRows.getD (oldEntries.findIdx (fun x => x == p)) 0
def copy10Entries : Array (Finset (Sum (Fin 12) Bool) × Sig) := #[
  ({Sum.inl 0}, s1),
  ({Sum.inl 1}, s11),
  ({Sum.inl 2}, s3),
  ({Sum.inl 3}, s4),
  ({Sum.inl 4}, s5),
  ({Sum.inl 5}, s14),
  ({Sum.inl 6}, s6),
  ({Sum.inl 7}, s7),
  ({Sum.inl 8}, s15),
  ({Sum.inl 9}, s8),
  ({Sum.inl 11}, s9),
  ({Sum.inr false}, s16),
  ({Sum.inr true}, s16),
  ({Sum.inl 5, Sum.inl 8}, s18)]
def copy10WitnessCode : Nat := 0x3f3c00003f3c0000563c0000433c000000000000423c00003f3c0000000000003c3c0000322f00001f2d0000230f0000011000003f3c000000000000000000008a870000000000003f3c00006a6a000000000000424200004c4c00002f2f00001f1f0000180f0000010100003f3c000000000000000000008a870000000000003f3c00006a6a000000000000424200004c4c00002f2f00001f1f0000180f000001010000563c00008a8700008a870000000000008e7a0000563c0000776a00006763000087420000554c0000372f00002c1f00001b0f00000e010000433c000000000000000000008e7a0000000000007d3c0000776a00006363000045420000534c0000442f00002c1f0000180f00000e010000000000003f3c00003f3c0000563c00007d3c000000000000000000003f3c00003c0000003c3c0000312f00001f2d0000130f000001100000423c00006a6a00006a6a0000776a0000776a000000000000000000006363000042420000504c0000312f0000331f0000130f00005f0100003f3c0000000000000000000067630000636300003f3c00006363000000000000424200004c4c00002f2f00001f1f0000230f00000101000000000000424200004242000087420000454200003c000000424200004242000000000000000000002f2f00001f2d00000f0f0000011000003c3c00004c4c00004c4c0000554c0000534c00003c3c0000504c00004c4c000000000000000000002f2f00002d1f00000f0f000012010000322f00002f2f00002f2f0000372f0000442f0000312f0000312f00002f2f00002f2f00002f2f0000000000002d1f00000f0f0000120100001f2d00001f1f00001f1f00002c1f00002c1f00001f2d0000331f00001f1f00001f2d00002d1f00002d1f000000000000130f00002d010000230f0000180f0000180f00001b0f0000180f0000130f0000130f0000230f00000f0f00000f0f00000f0f0000130f000000000000012300000110000001010000010100000e0100000e010000011000005f010000010100000110000012010000120100002d010000012300000000
def copy10Witness (p q : Finset (Sum (Fin 12) Bool) × Sig) (d : Nat) : Pair :=
  let i := copy10Entries.findIdx (fun x => x == p)
  let j := copy10Entries.findIdx (fun x => x == q)
  ⟨(((copy10WitnessCode >>> (8 * ((i * 14 + j) * 4 + d))) % 256) % 225), Nat.mod_lt _ (by decide)⟩
def copy10BridgeRows : Array Pair := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def copy10BridgeWitness (p : Finset (Fin 12) × Sig) : Pair :=
  copy10BridgeRows.getD (oldEntries.findIdx (fun x => x == p)) 0
def copy11Entries : Array (Finset (Sum (Fin 12) Bool) × Sig) := #[
  ({Sum.inl 0}, s1),
  ({Sum.inl 1}, s11),
  ({Sum.inl 2}, s3),
  ({Sum.inl 3}, s4),
  ({Sum.inl 4}, s5),
  ({Sum.inl 5}, s14),
  ({Sum.inl 6}, s6),
  ({Sum.inl 7}, s7),
  ({Sum.inl 8}, s15),
  ({Sum.inl 9}, s8),
  ({Sum.inl 10}, s16),
  ({Sum.inr false}, s9),
  ({Sum.inr true}, s9),
  ({Sum.inl 5, Sum.inl 8}, s18),
  ({Sum.inl 5, Sum.inr false}, s72),
  ({Sum.inl 9, Sum.inr false}, s73),
  ({Sum.inl 10, Sum.inr false}, s74),
  ({Sum.inl 10, Sum.inr false}, s75),
  ({Sum.inl 5, Sum.inr true}, s72),
  ({Sum.inl 9, Sum.inr true}, s73),
  ({Sum.inl 10, Sum.inr true}, s74),
  ({Sum.inl 10, Sum.inr true}, s75),
  ({Sum.inl 5, Sum.inl 8, Sum.inr false}, s76),
  ({Sum.inl 9, Sum.inl 10, Sum.inr false}, s77),
  ({Sum.inl 5, Sum.inl 10, Sum.inr false}, s78),
  ({Sum.inl 8, Sum.inl 10, Sum.inr false}, s79),
  ({Sum.inl 5, Sum.inl 8, Sum.inl 10, Sum.inr false}, s80),
  ({Sum.inl 5, Sum.inl 8, Sum.inr true}, s76),
  ({Sum.inl 9, Sum.inl 10, Sum.inr true}, s77),
  ({Sum.inl 5, Sum.inl 10, Sum.inr true}, s78),
  ({Sum.inl 8, Sum.inl 10, Sum.inr true}, s79),
  ({Sum.inl 5, Sum.inl 8, Sum.inl 10, Sum.inr true}, s80),
  ({Sum.inl 5, Sum.inl 8, Sum.inl 10, Sum.inr false}, s81),
  ({Sum.inl 5, Sum.inl 8, Sum.inl 10, Sum.inr false}, s82),
  ({Sum.inl 5, Sum.inl 8, Sum.inl 10, Sum.inr true}, s81),
  ({Sum.inl 5, Sum.inl 8, Sum.inl 10, Sum.inr true}, s82)]
def copy11WitnessCode : Nat := 0x433c0000000000000000000000000000563c000000000000433c000000000000423c00003f3c0000000000003c3c0000322f00001f2d0000230f0000011000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000433c0000000000000000000000000000563c000000000000433c000000000000423c00003f3c0000000000003c3c0000322f00001f2d0000230f00000110000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000433c0000000000000000000000000000000000000000000000000000563c00000000000000000000433c000000000000423c00003f3c0000000000003c3c0000322f00001f2d0000230f00000110000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000433c0000000000000000000000000000000000000000000000000000563c00000000000000000000433c000000000000423c00003f3c0000000000003c3c0000322f00001f2d0000230f0000011000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000433c0000000000000000000000000000563c000000000000433c000000000000423c00003f3c0000000000003c3c0000322f00001f2d00000d0f0000011000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000563c00003c8700000000000000000000563c0000000000007c3c000000000000000000003f3c00003c0000003c3c0000312f00001f2d0000130f0000011000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000454200000000000000000000000000008742000000000000454200003c000000424200004242000000000000000000002f2f00001f2d00000f0f00000110000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000433c00000000000000000000000000000000000000000000000000000000000045420000433c000000000000827a000000000000000000007c3c0000776a0000635a000045420000534c0000442f00002c1f0000180f00000e010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000433c000000000000000000000000000000000000000000003f3c0000873c0000433c0000000000000000000000000000563c00003f3c0000433c000000000000423c00003f3c0000000000003c3c0000322f00001f2d0000230f00000110000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000433c0000000000000000000000000000000000000000000000000000563c00000000000000000000433c000000000000423c00003f3c0000000000003c3c0000322f00001f2d00000d0f00000110000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000563c00003c8700000000000000000000000000000000000000000000563c000000000000000000007c3c000000000000000000003f3c00003c0000003c3c0000312f00001f2d0000130f0000011000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000045420000000000000000000000000000000000000000000000000000874200000000000000000000454200003c000000424200004242000000000000000000002f2f00001f2d00000f0f0000011000000000000000000000000000000000000000000000000000000000000000000000433c000000000000000000000000000000000000000000000000000000000000000000004542000000000000000000000000000000000000433c0000827a00000000000000000000000000007c3c0000776a0000635a000045420000534c0000442f00002c1f0000180f00000e01000000000000000000000000000000000000000000000000000000000000433c00000000000000000000000000000000000000000000000000003f3c0000873c0000433c0000000000000000000000000000000000000000000000000000563c0000000000003f3c0000433c000000000000423c00003f3c0000000000003c3c0000322f00001f2d0000230f000001100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000003f3c000000000000000000000000000000000000000000000000000000000000424200003f3c0000000000000000000000000000000000003f3c00006a6a000000000000424200004c4c00002f2f00001f1f0000180f00000101000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000873c00000000000000000000000000000000000000000000000000000000000000000000003c0000000000000000000000000000007a0000003c0000776a0000675a000000420000594c00004a2f00002c1f00001c0f00000e0100000000000000000000433c0000433c00000000000000000000000000000000000000000000433c0000563c00004542000000000000433c00000000000000000000000000000000000000000000000000000000000045420000433c000000000000000000007a00000000000000563c0000776a00006363000045420000534c0000372f00002c1f0000180f00000e010000000000000000000000000000000000000000000000000000000000000000000000000000000000003c870000000000004542000000000000000000000000000000000000000000004242000000000000454200000000000000000000000000000000000042420000454200003c000000424200004242000000000000000000002f2f00001f2d00000f0f00000110000000000000000000000000000000000000000000000000000000000000000000003f3c0000000000000000000000000000000000000000000000000000000000000000000042420000000000000000000000000000000000003f3c0000000000000000000000000000000000003f3c00006a6a000000000000424200004c4c00002f2f00001f1f0000180f0000010100000000000000000000000000000000000000000000000000000000000000000000873c000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000003c0000000000000000000000000000007a0000003c0000776a0000675a000000420000594c00004a2f00002c1f00001c0f00000e010000433c0000433c00000000000000000000433c0000563c00004542000000000000433c000000000000000000000000000000000000000000000000000000000000000000004542000000000000000000000000000000000000433c000000000000000000007a00000000000000563c0000776a00006363000045420000534c0000372f00002c1f0000180f00000e01000000000000000000000000000000000000000000003c8700000000000045420000000000000000000000000000000000000000000000000000424200000000000045420000000000000000000000000000000000000000000000000000000000000000000042420000454200003c000000424200004242000000000000000000002f2f00001f2d00000f0f00000110000000000000000000000000000000000000000000000000000000000000433c000000000000000000000000000000000000433c0000000000003f3c0000003c0000433c0000000000003f3c0000003c0000433c00000000000000000000563c0000563c00003f3c0000433c000000000000423c00003f3c0000000000003c3c0000322f00001f2d0000230f0000011000000000000000000000563c0000563c00000000000000000000000000000000000000000000563c0000563c000087420000827a0000563c00000000000000000000000000000000000000000000000000000000000000000000563c0000000000000000000000000000007a0000563c0000776a00006763000000420000554c0000372f00002c1f00001b0f00000e010000563c0000563c00000000000000000000563c0000563c000087420000827a0000563c000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000563c0000000000000000000000000000007a0000563c0000776a00006763000000420000554c0000372f00002c1f00001b0f00000e01000000000000000000000000000000000000000000000000000000000000000000003f3c0000000000000000000000000000000000003f3c000000000000000000007a0000004242000000000000000000007a000000424200003f3c0000000000000000000000000000000000003f3c00006a6a000000000000424200004c4c00002f2f00001f1f0000180f000001010000433c0000433c0000433c0000433c0000433c00007c3c00004542000000000000433c0000433c00007c3c00004542000000000000433c000000000000007a0000000000004542000000000000007a00000000000045420000433c0000007a0000007a000000000000000000007d3c0000776a00006363000045420000534c0000442f00002c1f0000180f00000e0100000000000000000000000000000000000000000000000000003c0000007c3c00000000000000000000000000003c0000007c3c0000000000003f3c0000003c0000563c00003c0000003f3c0000003c0000563c00003c00000000000000563c0000563c00003f3c00007d3c000000000000000000003f3c00003c0000003c3c0000312f00001f2d0000130f000001100000423c0000423c0000423c0000423c0000423c00000000000042420000776a0000423c0000423c00000000000042420000776a0000423c00006a6a0000776a0000776a0000424200006a6a0000776a0000776a000042420000423c0000776a0000776a00006a6a0000776a000000000000000000006363000042420000504c0000312f0000331f0000130f00005f0100003f3c00003f3c00003f3c00003f3c00003f3c00003f3c000042420000635a00003f3c00003f3c00003f3c000042420000635a00003f3c000000000000675a0000636300004242000000000000675a000063630000424200003f3c0000676300006763000000000000636300003f3c00006363000000000000424200004c4c00002f2f00001f1f0000230f00000101000000000000000000000000000000000000000000003c000000000000004542000000000000000000003c000000000000004542000000000000424200000042000045420000000000004242000000420000454200000000000000000000004200000042000042420000454200003c000000424200004242000000000000000000002f2f00001f2d00000f0f0000011000003c3c00003c3c00003c3c00003c3c00003c3c00003c3c000000000000534c00003c3c00003c3c00003c3c000000000000534c00003c3c00004c4c0000594c0000534c0000000000004c4c0000594c0000534c0000000000003c3c0000554c0000554c00004c4c0000534c00003c3c0000504c00004c4c000000000000000000002f2f00002d1f00000f0f000012010000322f0000322f0000322f0000322f0000322f0000312f00002f2f0000442f0000322f0000322f0000312f00002f2f0000442f0000322f00002f2f00004a2f0000372f00002f2f00002f2f00004a2f0000372f00002f2f0000322f0000372f0000372f00002f2f0000442f0000312f0000312f00002f2f00002f2f00002f2f0000000000002d1f00000f0f0000120100001f2d00001f2d00001f2d00001f2d00001f2d00001f2d00001f2d00002c1f00001f2d00001f2d00001f2d00001f2d00002c1f00001f2d00001f1f00002c1f00002c1f00001f2d00001f1f00002c1f00002c1f00001f2d00001f2d00002c1f00002c1f00001f1f00002c1f00001f2d0000331f00001f1f00001f2d00002d1f00002d1f000000000000130f00002d010000230f0000230f0000230f0000230f00000d0f0000130f00000f0f0000180f0000230f00000d0f0000130f00000f0f0000180f0000230f0000180f00001c0f0000180f00000f0f0000180f00001c0f0000180f00000f0f0000230f00001b0f00001b0f0000180f0000180f0000130f0000130f0000230f00000f0f00000f0f00000f0f0000130f00000000000001230000011000000110000001100000011000000110000001100000011000000e010000011000000110000001100000011000000e01000001100000010100000e0100000e01000001100000010100000e0100000e01000001100000011000000e0100000e010000010100000e010000011000005f010000010100000110000012010000120100002d010000012300000000
def copy11Witness (p q : Finset (Sum (Fin 12) Bool) × Sig) (d : Nat) : Pair :=
  let i := copy11Entries.findIdx (fun x => x == p)
  let j := copy11Entries.findIdx (fun x => x == q)
  ⟨(((copy11WitnessCode >>> (8 * ((i * 36 + j) * 4 + d))) % 256) % 225), Nat.mod_lt _ (by decide)⟩
def copy11BridgeRows : Array Pair := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def copy11BridgeWitness (p : Finset (Fin 12) × Sig) : Pair :=
  copy11BridgeRows.getD (oldEntries.findIdx (fun x => x == p)) 0
def copy12Entries : Array (Finset (Sum (Fin 12) Bool) × Sig) := #[
  ({Sum.inl 0}, s1),
  ({Sum.inl 1}, s11),
  ({Sum.inl 2}, s3),
  ({Sum.inl 3}, s4),
  ({Sum.inl 4}, s5),
  ({Sum.inl 6}, s6),
  ({Sum.inl 7}, s7),
  ({Sum.inl 9}, s8),
  ({Sum.inl 10}, s16),
  ({Sum.inl 11}, s9),
  ({Sum.inr false}, s18),
  ({Sum.inr true}, s18),
  ({Sum.inl 10, Sum.inr false}, s83),
  ({Sum.inl 10, Sum.inr false}, s84),
  ({Sum.inl 10, Sum.inr true}, s83),
  ({Sum.inl 10, Sum.inr true}, s84),
  ({Sum.inl 4, Sum.inl 10, Sum.inr false}, s68),
  ({Sum.inl 4, Sum.inl 10, Sum.inr true}, s68)]
def copy12WitnessCode : Nat := 0x3f3c0000554c000000000000534c0000504c00004c4c0000000000002f2f0000301f00004c0f0000120100000000000000000000000000000000000000000000000000003f3c000000000000554c000000000000534c0000504c00004c4c0000000000002f2f0000301f00004c0f00001201000000000000000000000000000000000000000000000000000000000000000000008a87000000000000000000006a6a0000000000004c0000002f2f00001f2d0000180f0000011000000000000000000000000000000000000000000000000000000000000000000000aa870000000000007d7a00006a6a0000c25a00004c4c0000322f00001f1f0000230f00000101000000000000000000000000000000000000000000000000000000000000000000008a87000000000000000000006a6a0000000000004c0000002f2f00001f2d0000180f0000011000000000000000000000000000000000000000000000000000000000000000000000aa870000000000007d7a00006a6a0000c25a00004c4c0000322f00001f1f0000230f000001010000000000003f3c0000000000000000000000000000000000000000000000000000aa870000000000007d7a00006a6a0000c26300004cd90000322f00001f2d0000230f0000011000003f3c000000000000000000000000000000000000000000000000000000000000aa870000000000007d7a00006a6a0000c26300004cd90000322f00001f2d0000230f000001100000554c0000554c00008a870000aa8700008a870000aa870000aa870000aa870000000000008a8700008e7a0000746a000067630000554c0000372f00002c1f00001b0f00000e01000000000000000000000000000000000000000000000000000000000000000000008a87000000000000000000006a6a0000000000004c4c00002f2f00001f1f0000180f000001010000534c0000534c0000000000007d7a0000000000007d7a00007d7a00007d7a00008e7a00000000000000000000706a000063630000534c0000442f00002c1f0000180f00000e010000504c0000504c00006a6a00006a6a00006a6a00006a6a00006a6a00006a6a0000746a00006a6a0000706a00000000000063630000504c0000312f0000331f0000130f00005f0100004c4c00004c4c000000000000c25a000000000000c25a0000c2630000c263000067630000000000006363000063630000000000004c4c00002f2f00001f1f0000230f00000101000000000000000000004c0000004c4c00004c0000004c4c00004cd900004cd90000554c00004c4c0000534c0000504c00004c4c0000000000002f2f00002d1f00000f0f0000120100002f2f00002f2f00002f2f0000322f00002f2f0000322f0000322f0000322f0000372f00002f2f0000442f0000312f00002f2f00002f2f0000000000002d1f00000f0f000012010000301f0000301f00001f2d00001f1f00001f2d00001f1f00001f2d00001f2d00002c1f00001f1f00002c1f0000331f00001f1f00002d1f00002d1f000000000000130f00002d0100004c0f00004c0f0000180f0000230f0000180f0000230f0000230f0000230f00001b0f0000180f0000180f0000130f0000230f00000f0f00000f0f0000130f0000000000000123000012010000120100000110000001010000011000000101000001100000011000000e010000010100000e0100005f0100000101000012010000120100002d010000012300000000
def copy12Witness (p q : Finset (Sum (Fin 12) Bool) × Sig) (d : Nat) : Pair :=
  let i := copy12Entries.findIdx (fun x => x == p)
  let j := copy12Entries.findIdx (fun x => x == q)
  ⟨(((copy12WitnessCode >>> (8 * ((i * 18 + j) * 4 + d))) % 256) % 225), Nat.mod_lt _ (by decide)⟩
def copy12BridgeRows : Array Pair := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def copy12BridgeWitness (p : Finset (Fin 12) × Sig) : Pair :=
  copy12BridgeRows.getD (oldEntries.findIdx (fun x => x == p)) 0
theorem old_checked : witnessClosedCheck roots raw col need oldTable false oldWitness = true := by decide +kernel
end Terminal0
end PEqualNP.Outside.L_meta_2373.Live1024
