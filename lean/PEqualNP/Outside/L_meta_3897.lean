import PEqualNP.Defs
-- First-gate certificate from L-meta-5120 by freeedolin, adapted from dsgallups and L-meta-1667.
namespace PEqualNP.Outside.L_meta_3897
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
def varsX (m : Nat) : List Sig := if m.testBit 9 then vars m ++ [seed] else vars m
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
def supportPairs (w : Bool) (mask : Nat) : List (Sig × Row × Row) :=
  (selected mask).map fun (i,a) =>
    let r := if w && i==0 then 8 else if w && i==3 then 1 else 0
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
def rawMask (m : Nat) (c : ColumnInfo) : Nat := m ^^^ (m &&& (c.1 &&& 512))
def colCheck (m : Nat) (c : ColumnInfo) (prior : Nat → Nat) : Bool :=
  let (z,o,q,s,L) := c
  let ms := fixRows z o
  let raw := rawMask m c
  let free := colFree raw z o
  let G := movedWord ms (chartGoal m)
  let xs := supportPairs (free.testBit 9) s
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
  let free := colFree raw z o
  let G := movedWord ms (chartGoal m)
  let xs := supportPairs (free.testBit 9) s
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
def relabelOK (old rep : Nat) (swaps : List Nat) :=
  (properB (graphGoal old) && plainWord (graphGoal old) && (varsX old).all plainWord) && properB (graphGoal rep) &&
    checkMap (swaps.map swapRows) (varsX old) (graphGoal old) (varsX rep) (graphGoal rep)
theorem relabel_of {u old rep L swaps} (ok : relabelOK old rep swaps = true)
    (h : Lower u (varsX rep) (graphGoal rep) L) : Lower u (varsX old) (graphGoal old) L := by
  simp only [relabelOK,Bool.and_eq_true] at ok
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
abbrev Bits := BitVec 91
abbrev Signals := Bits × Bits
abbrev Decor := Sig × Signals
def ofRows {n : Nat} (r : Fin n → Row) (v : Sig) : BitVec n :=
  (BitVec.ofBoolListLE (List.ofFn (fun i => bit (r i) v))).cast List.length_ofFn
theorem ofRows_bit {n : Nat} (r : Fin n → Row) (v : Sig) (i : Fin n) :
    (ofRows r v).getLsbD i.val = bit (r i) v := by
  simp only [ofRows,BitVec.getLsbD_cast,BitVec.getLsbD_ofBoolListLE,List.getD_eq_getElem?_getD,List.getElem?_ofFn]
  simp [i.isLt]
def pairSig (r s : Fin 91 → Row) (a : Sig) : Signals := (ofRows r a,ofRows s a)
def properPairs (T : Sig) (r s : Fin 91 → Row) :=
  ∀ i, bit (r i) T = true ∧ bit (s i) T = false
theorem pair_sep {T r s} (h : properPairs T r s) : Sep T 91 r s (pairSig r s) := by
  exact ⟨h,fun a i => ⟨ofRows_bit _ _ _,ofRows_bit _ _ _⟩⟩
def faithful (r s : Fin 91 → Row) (x : Decor) := x.2 = pairSig r s x.1
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
def asRow (cols : Nat → Bits) (i : Fin 91) : Row :=
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
theorem asRow_bit (cols : Nat → Bits) (i : Fin 91) (j : Fin 9) :
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
theorem bit_vertex (m : Nat) (v : Nat → Bits) (i : Fin 91) (j : Fin 9) :
    bit (asRow v i) (vertex m j.val) =
    ((if m.testBit j.val then v j.val else 0) : Bits).getLsbD i.val := by
  by_cases hh : m.testBit j.val = true
  · simpa [vertex,hh] using asRow_bit v i j
  · simp [vertex,hh,bit_zero]
theorem bit_liftGoal (m : Nat) (v : Nat → Bits) (i : Fin 91) :
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
  let n := v.toNat  %  2305843009213693951
  (n*(n+971))  %  2305843009213693951
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
def cornerWeight (s : BitVec 6) : Nat :=
  let b := s.getLsbD
  let a0 := b 0 != b 1
  let a1 := b 3 != b 4
  let c0 := b 0 != b 2
  let c1 := b 3 != b 5
  if !(a0 || a1 || c0 || c1) then 0
  else if !(a0 || a1) || !(c0 || c1) then 1
  else if a0 && a1 && c0 && c1 && (b 0 != b 3) then 3 else 2
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem corner_sub : ∀ (d : Fin 4) (a b : BitVec 6),
    cornerWeight (bv d.val a b) ≤ cornerWeight a+cornerWeight b := by decide +kernel
theorem corner_card {u T k S} (run : Live u T k S) : S.card≤k+1 := by
  induction run using Live.ind with
  | stop => simp
  | @binary k U a b d hd _ _ ne fresh _ ih =>
    have free : bin d a b∉U := fun h => fresh (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem h))
    rw [Finset.card_insert_of_notMem free] at ih
    have h₁ := Finset.card_insert_le (a:=a) (s:=insert b U)
    have h₂ := Finset.card_insert_le (a:=b) (s:=U)
    omega
theorem tight_mass {u T k S} (run : Live u T k S) (w : Sig → Nat)
    (sub : ∀ d a b, allowed u d → w (bin d a b) ≤ w a+w b) :
    S.card=k+1 → w T ≤ ∑ x ∈ S, w x := by
  induction run using Live.ind with
  | stop => simp
  | @binary k U a b d hd _ _ ne fresh tail ih =>
    intro sat
    have free : bin d a b∉U := fun h => fresh (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem h))
    have cap := corner_card tail
    rw [Finset.card_insert_of_notMem free] at cap
    have h₁ := Finset.card_insert_le (a:=a) (s:=insert b U)
    have h₂ := Finset.card_insert_le (a:=b) (s:=U)
    have aN : a∉insert b U := by
      intro ha
      rw [Finset.insert_eq_of_mem ha] at sat
      omega
    have bN : b∉U := by
      intro hb
      rw [Finset.insert_eq_of_mem hb] at sat
      have h := Finset.card_insert_le (a:=a) (s:=U)
      omega
    rw [Finset.card_insert_of_notMem aN,Finset.card_insert_of_notMem bN] at sat
    have n : (insert (bin d a b) U).card=k+1 := by rw [Finset.card_insert_of_notMem free]; omega
    have h := ih n
    rw [Finset.sum_insert free] at h
    rw [Finset.sum_insert aN,Finset.sum_insert bN]
    have hb := sub d a b hd
    omega
def cornerValue (r : Fin 6 → Row) (v : Sig) : Nat :=
  let p := bit (r 0) v
  let q := bit (r 3) v
  let a0 := p != bit (r 1) v
  let a1 := q != bit (r 4) v
  let c0 := p != bit (r 2) v
  let c1 := q != bit (r 5) v
  if !(a0 || a1 || c0 || c1) then 0
  else if !(a0 || a1) || !(c0 || c1) then 1
  else if a0 && a1 && c0 && c1 && (p != q) then 3 else 2
theorem cornerAsRows (r : Fin 6 → Row) (v : Sig) : cornerValue r v=cornerWeight (ofRows r v) := by
  have read (i : Fin 6) := ofRows_bit r v i
  simp only [cornerWeight,cornerValue]
  rw [←read 0,←read 1,←read 2,←read 3,←read 4,←read 5]
  rfl
theorem cornerBound (r : Fin 6 → Row) {u T k S}
    (n : S.card=k+1) (more : (∑ x ∈ S, cornerValue r x) < cornerValue r T) :
    Impossible u T k S := by
  intro t ht run
  have size := corner_card run
  have same : t=k := by omega
  subst t
  apply Nat.not_le_of_gt more (tight_mass run (cornerValue r) (fun d a b hd => ?_) n)
  have lt : d<4 := by rcases hd with h|h <;> omega
  simp only [cornerAsRows]
  rw [ofRows_bin]
  exact corner_sub ⟨d,lt⟩ _ _
abbrev NodeContext := Nat × Nat × List Decor × CovPair × List BoundPool × (Nat → List (List Sig)) × Bool
def evalMove (c : NodeContext) (op : Nat) (a b z : Decor) (ka kb : Bool) :=
  let (cap,n,ws,cov,pools,links,flag) := c
  let len := 1+(n - (if ka then 0 else 1) - (if kb then 0 else 1))
  if len>cap then true else if (len==cap) && flag then true else
    let d := !cov.2
    let rs := restCov cov.1 (column d a.2) (column d b.2) ka kb
    if (rs ||| column d z.2) != BitVec.allOnes 91 then true else
    if !properB z.1 || ws.any (fun v => v.1==z.1) then true else
      let rest := (delTwo ws a b ka kb).map Prod.fst
      closeChild cov.2 pools links (cap-1) rest (movedChoice op a b)
def moveFront (ws : List Decor) (op : Nat) (a b : Decor) (ka kb : Bool) :=
  (dbin op a b).1 :: (delTwo ws a b ka kb).map Prod.fst
def cornerRows (code : Nat) (i : Fin 6) : Row := Fin.ofNat 512 ((code >>> (9*i.val)) &&& 511)
def totalCorner (codes : List Nat) (v : Sig) := (codes.map (fun c => cornerValue (cornerRows c) v)).sum
theorem totalCorner_sub (codes : List Nat) {d : Nat} (hd : d<4) (a b : Sig) :
    totalCorner codes (bin d a b)≤totalCorner codes a+totalCorner codes b := by
  induction codes with
  | nil => simp [totalCorner]
  | cons c cs ih =>
    have one : cornerValue (cornerRows c) (bin d a b) ≤
        cornerValue (cornerRows c) a+cornerValue (cornerRows c) b := by
      simp only [cornerAsRows]
      rw [ofRows_bin]
      exact corner_sub ⟨d,hd⟩ _ _
    simp only [totalCorner,List.map_cons,List.sum_cons] at ih ⊢
    omega
def retentionReady (codes : List Nat) (T : Sig) (cap : Nat) (ws : List Sig) :=
  !codes.isEmpty && ws.all (fun v => totalCorner codes v ≤ 1) &&
    decide ((ws.map (totalCorner codes)).sum + (cap+1-ws.length) < totalCorner codes T)
theorem cornerSumList (w : Sig → Nat) {xs : List Sig} (nd : xs.Nodup) :
    (∑ x ∈ xs.toFinset, w x)=(xs.map w).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have hp := List.nodup_cons.mp nd
    have no : x∉xs.toFinset := by simpa using hp.1
    simp [no,ih hp.2]
theorem erasedMass (f : Decor → Nat) {xs : List Decor} {x : Decor} (mem : x∈xs) :
    ((xs.erase x).map f).sum + f x = (xs.map f).sum := by
  have eq := (List.Perm.map f (List.perm_cons_erase mem)).sum_eq
  simpa [Nat.add_comm] using eq.symm
theorem keptMass (f : Decor → Nat) {xs : List Decor} {a b : Decor} (ha : a∈xs) (hb : b∈xs)
    (ne : a≠b) (ka kb : Bool) (ba : f a≤1) (bb : f b≤1) :
    ((delTwo xs a b ka kb).map f).sum+f a+f b ≤ (xs.map f).sum+ka.toNat+kb.toNat := by
  have ba' : b∈xs.erase a := (List.mem_erase_of_ne (Ne.symm ne)).mpr hb
  have e₁ := erasedMass f ha
  have e₂ := erasedMass f hb
  have e₃ := erasedMass f ba'
  cases ka <;> cases kb <;> simp [delTwo,delOne] <;> omega
theorem retentionSound {codes u T cap ws a b d ka kb}
    (ready : retentionReady codes T cap (ws.map Prod.fst)=true)
    (nd : (ws.map Prod.fst).Nodup) (ha : a∈ws) (hb : b∈ws) (ne : a.1≠b.1) (hd : d<4)
    (fresh : (dbin d a b).1∉ws.map Prod.fst) (pos : 0<cap)
    (len : (moveFront ws d a b ka kb).length=cap) :
    Impossible u T (cap-1) (moveFront ws d a b ka kb).toFinset := by
  let w := totalCorner codes
  let f := fun v : Decor => w v.1
  have sub : ∀ op a b, allowed u op → w (bin op a b) ≤ w a+w b := by
    intro op a b ok
    apply totalCorner_sub codes _ a b
    rcases ok with h|h <;> omega
  have ab : a≠b := fun h => ne (congrArg Prod.fst h)
  have inc := (keep_sub ws a b ka kb).map Prod.fst
  have ndc : (moveFront ws d a b ka kb).Nodup :=
    List.nodup_cons.mpr ⟨fun mem => fresh (inc.subset mem),nd.sublist inc⟩
  have minlen : 2≤ws.length := by
    cases ws with
    | nil => simp at ha
    | cons x xs =>
      cases xs with
      | nil => simp_all
      | cons => simp
  have len' := len_keep ws a b ka kb ha hb ab
  simp only [moveFront,List.length_map,List.length_cons] at len
  have number : ka.toNat+kb.toNat=cap+1-ws.length := by
    cases ka <;> cases kb <;> simp_all <;> omega
  simp only [retentionReady,Bool.and_eq_true,decide_eq_true_eq,List.all_eq_true] at ready
  have aa : f a≤1 := ready.1.2 _ (List.mem_map_of_mem ha)
  have bb : f b≤1 := ready.1.2 _ (List.mem_map_of_mem hb)
  have raw := keptMass f ha hb ab ka kb aa bb
  have cost := totalCorner_sub codes hd a.1 b.1
  have start : (ws.map f).sum+(cap+1-ws.length)<w T := by
    simpa [w,f,Function.comp_def] using ready.2
  have smaller : ((moveFront ws d a b ka kb).map w).sum<w T := by
    simp only [moveFront,dbin,List.map_cons,List.map_map,List.sum_cons,Function.comp_def]
    change w (bin d a.1 b.1)+((delTwo ws a b ka kb).map f).sum<w T
    change w (bin d a.1 b.1)≤f a+f b at cost
    omega
  intro t ht live
  have size:=corner_card live
  rw [List.toFinset_card_of_nodup ndc] at size
  have actual : (moveFront ws d a b ka kb).length=cap := by simpa [moveFront] using len
  have sat : (moveFront ws d a b ka kb).toFinset.card=t+1 := by
    rw [List.toFinset_card_of_nodup ndc]
    omega
  have h:=tight_mass live w sub sat
  rw [cornerSumList w ndc] at h
  omega
theorem evalMove_sound {u raw T r s ws pools links cap a b op ka kb flag}
    (pairs : properPairs T r s) (faith : ∀ w ∈ ws, faithful r s w)
    (nd : (ws.map Prod.fst).Nodup) (ha : a ∈ ws) (hb : b ∈ ws)
    (ne : a≠b) (hcap : 0<cap)
    (pv : ∀ p ∈ pools, ValidPool u raw T p)
    (lv : ∀ tag xs, xs ∈ links tag → Impossible u T (cap-1) (List.toFinset xs))
    (shortcut : flag=true → (moveFront ws op a b ka kb).length=cap →
      Impossible u T (cap-1) (moveFront ws op a b ka kb).toFinset)
    (pro : proper (dbin op a b).1) (fresh : (dbin op a b).1 ∉ ws.map Prod.fst)
    (test : evalMove (cap,ws.length,ws,preCov u ws,pools,links,flag) op a b (dbin op a b) ka kb = true) :
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
  by_cases fast : ((child.length==cap) && flag)=true
  · simp only [Bool.and_eq_true,beq_iff_eq] at fast
    exact shortcut fast.2 fast.1 k hk h
  rw [if_neg fast] at test
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
  have be : ((restCov (coverage (!u) ws) (column (!u) a.2) (column (!u) b.2) ka kb ||| column (!u) z.2) != BitVec.allOnes 91) = false := by
    simpa using sep
  change (if (restCov (coverage (!u) ws) (column (!u) a.2) (column (!u) b.2) ka kb ||| column (!u) z.2) != BitVec.allOnes 91 then true else if !properB z.1 || ws.any (fun v => v.1==z.1) then true else _) = true at test
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
theorem node_sound {u raw T r s ws pools links cap flag}
    (pairs : properPairs T r s) (faith : ∀ w ∈ ws, faithful r s w)
    (nd : (ws.map Prod.fst).Nodup) (out : T ∉ ws.map Prod.fst)
    (pv : ∀ p ∈ pools, ValidPool u raw T p)
    (lv : ∀ tag xs, xs ∈ links tag → Impossible u T (cap-1) (List.toFinset xs))
    (shortcut : ∀ a∈ws, ∀ b∈ws, ∀ d, allowed u d → ∀ ka kb,
      a.1≠b.1 → (dbin d a b).1 ∉ ws.map Prod.fst → flag=true → (moveFront ws d a b ka kb).length=cap →
      Impossible u T (cap-1) (moveFront ws d a b ka kb).toFinset)
    (checks : testAll (cap,ws.length,ws,preCov u ws,pools,links,flag) ws = true) :
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
  have one (a b : Decor) (d : Nat) (opOK : allowed u d) (aa : a∈ws) (bb : b∈ws) (ne' : a.1≠b.1) (ka kb : Bool)
      (pr : proper (bin d a.1 b.1)) (fr : bin d a.1 b.1 ∉ ws.map Prod.fst)
      (test : testPair (cap,ws.length,ws,preCov u ws,pools,links,flag) a b d = true) :
      Impossible u T (cap-1) (childTwo (ws.map Prod.fst) a.1 b.1 d ka kb).toFinset := by
    rw [←binary_front nd aa bb ne']
    exact evalMove_sound pairs faith nd aa bb (fun e => ne' (congrArg Prod.fst e)) hc' pv lv
      (shortcut a aa b bb d opOK ka kb ne' fr) pr fr (testPair_at test ka kb)
  rcases all_binary checks haW hbW ab with hh | hh
  · exact one a b d hd haW hbW ne ka kb pro fresh (hh d hd)
  · rw [childTwo_swap _ nd _ _ d hd]
    exact one b a (flipOp d) (flip_flip hd).1 hbW haW (Ne.symm ne) kb ka (bin_flip hd a.1 b.1 ▸ pro)
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
  let shift := pos  %  8192
  let lo := word i >>> shift
  if shift+len ≤ 8192 then lo &&& ((1 <<< len)-1)
  else (lo ||| (word (i+1) <<< (8192-shift))) &&& ((1 <<< len)-1)
def lookupWord (nb slots sw vw iw pw : Nat) (data : Nat → Nat) (h : Nat) : Option (Nat × Nat) :=
  let a := h  %  nb
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
theorem chart_bit (m : Nat) (v : Nat → Bits) (i : Fin 91) :
    bit (asRow v i) (chartGoal m) = (chartSamples m v).getLsbD i.val := by
  exact bit_liftGoal m v i
theorem chart_pairs {m : Nat} {p q : Nat → Bits}
    (hp : chartSamples m p = BitVec.allOnes 91) (hq : chartSamples m q = 0) :
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
def omittedSlot (g : Forest) (k i : Nat) : Bool :=
  let z := 32*g.mask+k
  let bits : Nat := (if z<53221 then (if z<12264 then (if z<6055 then (if z<997 then (if z<996 then 0x0 else 0x1) else (if z<6053 then 0x0 else (if z<6054 then 0x1 else 0x3))) else (if z<6119 then (if z<6118 then 0x0 else 0xfff) else (if z<6120 then 0xf9ff3f5e5f3b6e72faebeafff8000 else (if z<12263 then 0x0 else 0x3)))) else (if z<16362 then (if z<12266 then (if z<12265 then 0xf700000000000 else 0x881800000000000000000000000000000) else (if z<16360 then 0x0 else (if z<16361 then 0x3f else 0x3ffffffffff0000))) else (if z<49129 then (if z<16363 then 0xf7dabf5ffffdffff800000000000000000000000000000000000 else (if z<49128 then 0x0 else 0x1)) else (if z<49130 then 0x1fa else (if z<49131 then 0x8d213000 else 0x0))))) else (if z<61417 then (if z<60903 then (if z<58854 then (if z<53223 then 0x1 else 0x0) else (if z<58855 then 0x3 else (if z<60902 then 0x0 else 0x40))) else (if z<61414 then (if z<60904 then 0x2382c3e80 else (if z<60905 then 0x104021800248100000000000 else 0x0)) else (if z<61415 then 0x4 else (if z<61416 then 0x73fffec0 else 0xac657e9f3789bbf79c9bfd58000000000000)))) else (if z<65002 then (if z<64999 then (if z<61418 then 0x10834aa80688eae7652a0861e60416b61185d49332816b40034402e1d310486ee3173729605c146994c0000000000000000000000000000000000000000000000000000 else 0x0) else (if z<65000 then 0x1 else (if z<65001 then 0x1fffff0 else 0x56efcffbfffffefff8000000000000000000000))) else (if z<65514 then (if z<65512 then 0x0 else (if z<65513 then 0x3e1fc else 0x2fbf7eeffdfffbd3fbff1ffffff800000000000000)) else (if z<65515 then 0x3deffbf7af69bcebcbffcf3efffdfdffddff3fffffb277edf7ffd7fffacdef57fdffef7feffb3bfbbf7efeeffbff53f80000000000000000000000000000000000000000000000000000000000000000000000000000000000000 else (if z<65516 then 0x6715d046453c72c5e59799b0d5c07678347b96444cf7ca58fd3512d64be264040f703d29211e24acc12d11b230000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 else 0x0))))))
  bits.testBit i
def slotWires (g : Forest) (k i : Nat) : List Sig :=
  if omittedSlot g k i then [] else stateSet g k i
theorem emptySlot {u T cap} : Impossible u T cap ∅ := by
  intro t _
  cases t with
  | zero => simp [Live]
  | succ n =>
    rintro ⟨U,a,b,d,_,eq,_⟩
    have h : a ∈ (∅ : Finset Sig) := eq.symm ▸ Finset.mem_insert_self a (insert b U)
    exact Finset.notMem_empty _ h
def linkedSet (g : Forest) (k : Nat) (pair : Nat × Nat) : Option (List Sig) :=
  if pair.1 ≥ (g.levels k).1 then none else
    (g.autos[pair.2]?).map fun perm => (slotWires g k pair.1).map (movedWord (perm.map swapRows).reverse)
theorem linkedSet_sound (g : Forest) (k : Nat)
    (names : ∀ x ∈ g.autos, autoOK (targetOf g) (x.map swapRows) = true)
    (earlier : ∀ i < (g.levels k).1, Impossible g.mode (targetOf g) k (slotWires g k i).toFinset)
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
def witnessWords (i : Nat) : Nat := (if i<2 then (if i<1 then 0x211221d0881100840945824041403055069141024060d834320404830150681410100c0541a050404030150601410100c0441a01040141985c460410040605834120401018160d00810000c0541a0502a050aa8160a00a8142a884c2202a050aa0130800a2412cd22b14028904b168ac500a2412ac12290028904aaa45a280a2412a890682028904aa049a000a2412a812280028904aa041a000a2410cd22b1402890431c8ac500a2410c5a2b140289019348ac500a240648a070202890192201c080a2010cc22b14028502a78149a00a140a8e05228028502a1a058280a140a868060a028502a18058200a0906e270b81028241b88c2e040a0906e230980028241b83c2e040a0906c2a0d02028241a984a2400a0906a610880028241a83c2e040a09068e86c32028241a3a130c80a09068e82c32028241a1a1b0c80a09068682c12028241a1a030480a09068680c02028241a180b0480a09068602c10028241989c2e040a09066270981028241988c2e040a09066230980028241983c2e040a090620f0b81028240789c2e040a08066230b81028201883c2e040890422c84c320220108e8161a00880422c84c320220108aa170a80880422a058280220108a2130880880422880c22020241a1a0b0480809066270981020201989c2e040808066230981020201988c260008080642a0d0202020190883408080806261289002020183a1b0c80808060686c3202020181a0b0480808060682c1002020181a0b0080808060680c0202020180b030080800422884c2201180854181c04044021706078101100855483450044021516070501100854483410044021512070401100854185c04044021506070101100854101c040424031b0946801024160d018040405030582212010140c0e058280404036170781010100cc4613000404031b0d468010100c6c251a0040403184d468010100c4c251200404030341609010100c0d018240404030309408010100c0c058240404030301608010040669351a00401018a4d46801000854181c04029008a68168a00a0806160a850022810aa9068a00880433088c40022010ac122900088042aa45a28022010a89068a0088042a241a08021408868160a008402278149a00210088e0522800840221a05828021008868160800840221a01828021008860160800828066a349a0020a019a8c26800828062c129a0020a018582a140080807168ac500202019a8d26800808066a349200202019a85268008080662349a0020201988c26800808066230980020201948a25000808065228840020201948a2000080806361a8900202018984a240080806160a8500202018582a100080806160a8100202018582a0000808060e0681002020181c1805008080606128900200088e8160a00800221a058280000000000000 else 0x9351a04424131a49468110904c61351a04424131849468110904c4c351a04424131309448110904c0d058244424130340609110904c0c058244424130301608110904c0c0182044240331184c0110900c6c351a04424031b09468110900c69351a0442403184d468110900c4c351a04424030341609110100c4c351a0410090629548a10402418854220410090514ca4510402414132914410090504c245104024141309044100904245209104024109108244080506524914102014184924104080503144a451020140c5109144080502144a0510201408510814400110a0d548a0a24128b21b0c828904a28058200a0142a0b0d02828050a82c32090a004220b0d0282414031309448090500c0d0582420080c0342a050540a1544060101502854c874320540a1520160801502844c874320540817321d0c8150201cc874320540806161d0c81500844c07432054021124160901468255160f05051a09544834101448255160f0505120954581c141448255120d0405120954181c041448255020d0005120954081c0014320d0541a0505048351184c0414120d0541a050504834150601414120d0441a01050403415068141409059a4d468050241661351a0140905930d468050241629351a01409058944c24050240669351a01409019a4c468050240661351a0140901930d468050240629351a0140501984d46804c08062612890130201818182404c06134526914130184d14984504c06134426110130184c90782404c06132416090130184c88742204c0613201e080130184c80702004c06114526914130184514984504c06114426914130184510984404c061124160901301841949a4504c0610472691413018401c9a4504c040745269141300845149a4504c021144269141300844c8743204a29166a349a0128a458182a04048a0533088c40122814c8a2702048a0532281c08122814c822300048a0532081c00122814aa9168a048a052aa41a28122814a892682048a052a241a08122814a812280048a042aa45a28122810aa9068a048a042a245a281228062a9168a0482817168ac50120a05c1a2b0404828166a349a0120a059a8c26804828166230980120a05958aa5404828165228940120a05948221004828164208800120a058986a340482816261a890120a058984a240482816160a850120a05858221404828161608840120a058184a240482816060a810120a058182a0004828160608850120a05818220004828066a349a0120a019a8c26804828066a261a0120a01988d2680482806160a8501208058182a04048141b85c4e041205066171381048141985c46041204068180602044061145269141101845149845044061145161141100845149a450440211452611411008451098450440211442611011008449058240440) else (if i<3 then 0x52050101944a4508140406150b05204240303006098108a40aac522a0422032ab148a8102a142592092040a840ea64328102a103a980ca0310888e0522880c42221a0582a030281c5a2b1480c0a066a349a20302819a8526880c0a066a148a2030281988c26080c0a065208842030281948220080c0a0626128920302818582a1480c0a0606128920302818184a0480c0807168ac52030088860520880828062c12892020a0189a4824808280626128920209849368a4580826124ca291602098491e8a4580826104da291602098411e8a4580824424da29160208841328a4580102804a8502a0020901868a4580082404ca29160008841328a4544a2916061a811128a059a8d2684424130150681510904c0441a0140a41229a45a290290488e0522840a41221a05829029048860520840a412218058210282418582a1440a09060612811028048a69168a408150a6a741a10202018984a24400814025428150004420994422400110821540a0a0482c0342a0528104a20b0d028a0412880c340a24140b01506814900a25617838122950aa78349a08a4926c2a0d02229249a1a0b0488a09068682c1222412890a250288904a2420940a22020181a0b0488301a0c28940a20c0682aa652288250289e0526820940a238148a0825028868160a20940a21a018288100a0488e432204028122310888100a0428940a20402800b250288100a000c940a190904d85c1e046424131309448190900c4c25120548a556124904152295485128145468355160f05151a0d54581c145468355060701150c874150681454321d05418051422150851281450301c0541a051409042361d0c850241085834121409018361d0c8500914c1a450214024528b55228500914a0d548a14024428b55228500910a0d548a140044286512085001108304a0512412494532914490492514c24512412494132914490492504c24112412490914824490403514ca45120a0590a834084828160e86c32120a0581a1b0c84828160682c12120a0183a1b0c84828060e82c32120a0181a0b0484822135209848120884d08068244822131a8d868120880c6a361a04808060686c3212020181a0b04848080600c2c12120144b159a450480512c466914120144b0a91408480512c2245021201443159a450480510c46611012014430a91408450291629548a1140a458854220450291514ca451140a454132914450291504c2411140a45091482445029142442091140a45081082045029122d548a1140a44835522845029103452091140a418a55228450290621548a114024188552284482516124904112094485128144460315520d1411180c544834104460315060701110904d85c1e044424133108440110904c85418044424132140601110904c6c351a04424131b09468110904c6 else 0xc04130829540a30104c20855028894520c4c2512221018882c340a82e070aaa170aa0b148a868160a8260708aa170aa0980c22a85c2a8260308a21308a09028360f0b818240a0c69269260902830a41a09824080d83c2e0609020320f0b81824080c83c2a2a0824921868a45820924047a29160504836170781814120d8541e0605048331184c0814120c6c351a20504831a4d468814120c4c251220504830341609814120c0c250220504830301609814100d85c1e060504036150781814100cc4613020504031309448814100c0d05826050181c562d1481406066c13192050181944a4508140407158b4))
def witnessWord (i : Nat) := packedAt witnessWords (54*i) 54
def rowPack15k3i0 (i : Nat) : Nat := 0x30
def witnesses15 (k i : Nat) : Nat := if i < 0 ∨ 0 < i then 0 else packedAt rowPack15k3i0 (9*(i-0)) 9
def rowPack31k4i0 (i : Nat) : Nat := 0x75
def rowPack31k5i0 (i : Nat) : Nat := 0x12449
def witnesses31 (k i : Nat) : Nat := (if k<5 then if i < 0 ∨ 0 < i then 0 else packedAt rowPack31k4i0 (9*(i-0)) 9 else (if k<6 then if i < 0 ∨ 1 < i then 0 else packedAt rowPack31k5i0 (9*(i-0)) 9 else 0))
def witnesses111 (k i : Nat) : Nat := (if k<6 then 0 else 0)
def rowPack189k5i0 (i : Nat) : Nat := 0xc2
def rowPack189k6i0 (i : Nat) : Nat := 0xac92
def rowPack189k7i0 (i : Nat) : Nat := 0x440981e
def witnesses189 (k i : Nat) : Nat := (if k<6 then if i < 0 ∨ 0 < i then 0 else packedAt rowPack189k5i0 (9*(i-0)) 9 else (if k<7 then if i < 0 ∨ 1 < i then 0 else packedAt rowPack189k6i0 (9*(i-0)) 9 else if i < 0 ∨ 0 < i then 0 else packedAt rowPack189k7i0 (27*(i-0)) 27))
def rowPack191k6i0 (i : Nat) : Nat := 0x3ae8438ad521d504813c20cee75
def rowPack191k7i0 (i : Nat) : Nat := 0xc875241dcccad782bcccad332b6209224e5eb59423ac4d007321d4ca1a
def rowPack191k7i13 (i : Nat) : Nat := 0x24812093b87620003bac460924666cc8210ec41e29204954ea7543315de863b9552468569a3379e14219179a3bc421430341a0004c99024ea68049a0ec89881d4ea095896a20773a9a03ac53b82738772aa4b2c772499a20090f1e0d08c2d122210c3ac43331010a184e1d341d460783ab022110
def rowPack191k8i0 (i : Nat) : Nat := 0x110321d60c550b440ccad
def rowPack191k8i3 (i : Nat) : Nat := 0x2209234026209288248aa868824a204900000921d2482460c58807524b11830cd809362c892b288248d07788249e4b188074000018318619b1866c619b248749809ad2c8928624e60aab118076b409340900000881dc0000cf824aac5ad2c800001830492b13430c00002aac493982630ed25524b0e204945ac4601e3782516b1000009277000022049362c8d0c32a875248626026201d
def rowPack191k8i70 (i : Nat) : Nat := 0x609200440015c2a8006000881262068ae43524002a9552510000022068494422110634418c1d340773a00630746110
def rowPack191k9i2 (i : Nat) : Nat := 0x440921d
def witnesses191 (k i : Nat) : Nat := (if k<8 then (if k<7 then if i < 0 ∨ 11 < i then 0 else packedAt rowPack191k6i0 (9*(i-0)) 9 else (if i<13 then if i < 0 ∨ 12 < i then 0 else packedAt rowPack191k7i0 (18*(i-0)) 18 else if i < 13 ∨ 115 < i then 0 else packedAt rowPack191k7i13 (9*(i-13)) 9)) else (if k<9 then (if i<3 then if i < 0 ∨ 2 < i then 0 else packedAt rowPack191k8i0 (27*(i-0)) 27 else (if i<70 then if i < 3 ∨ 69 < i then 0 else packedAt rowPack191k8i3 (18*(i-3)) 18 else if i < 70 ∨ 111 < i then 0 else packedAt rowPack191k8i70 (9*(i-70)) 9)) else (if k<10 then if i < 2 ∨ 2 < i then 0 else packedAt rowPack191k9i2 (27*(i-2)) 27 else 0)))
def rowPack383k7i0 (i : Nat) : Nat := 0x190c8
def rowPack383k8i0 (i : Nat) : Nat := 0x1f879a300498dcccad1f8789209790230bb9480f3a2c819b208620490fdb6066d2aa0c2fe888120b0332b492b6832952eab332b520b024edc920d24ecdb6ac24a9492b6198089205848e53020248751cb07e880e0141f894d1b246ac061b06a8c5e614
def rowPack383k8i44 (i : Nat) : Nat := 0x1d15e3203cc8646f426c8
def rowPack383k9i0 (i : Nat) : Nat := 0x116790222c6656c58ccad
def rowPack383k9i3 (i : Nat) : Nat := 0x340520230188789c091887892091e075c2bb24aec601d482ee2eb18b3c9c233d4ba62cbb490c493b7382ec921d248f0d1bc34324d005382edc2bb24875c2bb7ba8124312487c92bb29bdcd0141f879c2bb343d45e1b24aece0bb1fb20d01424ecc8af74c0822c4918075243127050d1bc2485520b04a8b93020b20c1302024a947e1e248747e1e1f87a2c6882080ccbb1fb20ccbb8b925b230708c093bc8b2c0920933320923c82f4520b077b1c93bc8ba95c2bb3401092bd498dce0bb24af4e009670c1b2308232492bd8b1987eca8b1a07ec91eb25b4bb790b0921f790509215be546f952783d892a5822ef523c81aec93bc482c22ca924ec49c148b2ec7ec8332ed3014
def rowPack383k9i119 (i : Nat) : Nat := 0x923c8bd0fa468386f49dd338138d03f
def rowPack383k10i6 (i : Nat) : Nat := 0x11634052f84964c58601d000000000000022c490e92479bd0000000681fb25c23064a61eec9
def rowPack383k10i19 (i : Nat) : Nat := 0x708c0621e1887800008b1a0000024ef00000490c4000000001c23f70aee2c490000208bb8b8c530bb70aec93bc248240000820fe2c68708fc92bb
def witnesses383 (k i : Nat) : Nat := (if k<10 then (if k<8 then if i < 0 ∨ 1 < i then 0 else packedAt rowPack383k7i0 (9*(i-0)) 9 else (if k<9 then (if i<44 then if i < 0 ∨ 43 < i then 0 else packedAt rowPack383k8i0 (18*(i-0)) 18 else if i < 44 ∨ 52 < i then 0 else packedAt rowPack383k8i44 (9*(i-44)) 9) else (if i<3 then if i < 0 ∨ 2 < i then 0 else packedAt rowPack383k9i0 (27*(i-0)) 27 else (if i<119 then if i < 3 ∨ 118 < i then 0 else packedAt rowPack383k9i3 (18*(i-3)) 18 else if i < 119 ∨ 132 < i then 0 else packedAt rowPack383k9i119 (9*(i-119)) 9)))) else (if k<11 then (if i<19 then if i < 6 ∨ 16 < i then 0 else packedAt rowPack383k10i6 (27*(i-6)) 27 else if i < 19 ∨ 44 < i then 0 else packedAt rowPack383k10i19 (18*(i-19)) 18) else (if k<12 then 0 else 0)))
def rowPack511k8i0 (i : Nat) : Nat := 0x2071e004783c
def rowPack511k9i0 (i : Nat) : Nat := 0xbe4409c0a332b4d015d58f0d00c340308cb322331e238b3154d1b6346e4ccb53702ad63c
def rowPack511k9i16 (i : Nat) : Nat := 0x20162007aea29a57878c2610f078ad63004020703aec02142f8f0783c00e300ecd9b0a468c299cc8c7bc2e0515a3c
def rowPack511k10i0 (i : Nat) : Nat := 0x8ce8b09537c885af563c
def rowPack511k10i3 (i : Nat) : Nat := 0x34050d1b978c98d00aa0c96627770ca4ccb3332b5b4ad3430ce80f79024d1b51a004920979024ccbb3402cabb4346d4d0f78838262013401de409346f5e409318f1b4072aaa1e409346f2205f6c740d00a6e9dcd014332b4ccad989ddc329be59c92096e9dde3314f498d007340509209318f0c63c24824d1bc700f1e2f7340509209332ecd1bd2a853a2c634051b3d2b3f40cc01318f0c63c31ba4d00a332cdc137a4154aca83a2ecd0c3ae024d00b78bdcc6e734028d00a88741bc07508f09db44f0d1b8ad88748d0c3318f0aaba346d4ccbb2aaee8528700f0c6f7492c492098d970e8bb276d0aac0332cc68c22abdeb8091a9ddc230703dcd01488740d00aa41a1180731b9e7326318f1e40988380ccbb788fdb48224824b936332ecd0f7a41a1e5346cf5cc23c332cde52931bdcdcbb332ce6e01343dcccf7
def rowPack511k10i143 (i : Nat) : Nat := 0x283f0a308680130b19d2011e004c6e1510fe6c7700cc4683cdeb1878a2988247e341e31976d998b10283c4fb1812c31f8f1ee143a775ee1498ef0c6e11f88ceec6008fcc6c6ec050143c
def rowPack511k11i1 (i : Nat) : Nat := 0x440d0149c9a01510318fe20680a440d0f76d4c4028cec30a20665dc40ccbb8818dd31024826ce631e440d1bc899a01539262ee20637b9447e77be2318510318f220d9ebdf221d0881a029103a3dedef21a440c63cbe44145394f49a845554441e409
def rowPack511k11i30 (i : Nat) : Nat := 0x794c4e8bb31bdde531346f0e9373a2ecd0146e9dcc63cb708e20632aaea2063346f0e8bb70aece8bba44c5c234318f1e43f3a2ede414362efb0c6790d4d0141fb0cd01470cc4d01470b193d31318f290633a2ece0bb39bdca27788364d01479051ba77318f220633a2ece8f7
def rowPack511k11i78 (i : Nat) : Nat := 0xc698b198ce1
def rowPack511k12i5 (i : Nat) : Nat := 0x440e8bb
def witnesses511 (k i : Nat) : Nat := (if k<11 then (if k<9 then if i < 0 ∨ 5 < i then 0 else packedAt rowPack511k8i0 (9*(i-0)) 9 else (if k<10 then (if i<16 then if i < 0 ∨ 15 < i then 0 else packedAt rowPack511k9i0 (18*(i-0)) 18 else if i < 16 ∨ 57 < i then 0 else packedAt rowPack511k9i16 (9*(i-16)) 9) else (if i<3 then if i < 0 ∨ 2 < i then 0 else packedAt rowPack511k10i0 (27*(i-0)) 27 else (if i<143 then if i < 3 ∨ 142 < i then 0 else packedAt rowPack511k10i3 (18*(i-3)) 18 else if i < 143 ∨ 208 < i then 0 else packedAt rowPack511k10i143 (9*(i-143)) 9)))) else (if k<12 then (if i<30 then if i < 1 ∨ 29 < i then 0 else packedAt rowPack511k11i1 (27*(i-1)) 27 else (if i<78 then if i < 30 ∨ 77 < i then 0 else packedAt rowPack511k11i30 (18*(i-30)) 18 else if i < 78 ∨ 82 < i then 0 else packedAt rowPack511k11i78 (9*(i-78)) 9)) else (if k<13 then if i < 5 ∨ 5 < i then 0 else packedAt rowPack511k12i5 (27*(i-5)) 27 else 0)))
def rowPack1535k8i0 (i : Nat) : Nat := 0x3c
def rowPack1535k9i0 (i : Nat) : Nat := 0x221dc
def rowPack1535k9i1 (i : Nat) : Nat := 0x51578783c3ce30fe7a
def rowPack1535k10i0 (i : Nat) : Nat := 0x1537c886c6d055
def rowPack1535k10i2 (i : Nat) : Nat := 0x2205fbe59de2f724826521e30ba621047f091b1ce
def rowPack1535k10i11 (i : Nat) : Nat := 0x900000683c1e3a478a2c60f0014b0480029dd7b850c64e
def rowPack1535k11i0 (i : Nat) : Nat := 0x881a029103402400000000000008818dd3102482719044459cc63c8818def106cf5ef91051441b1d0
def rowPack1535k11i12 (i : Nat) : Nat := 0x4502478883a220c6f73a2c4d1bc7ba222009340527268b792e20632aae8e8bb00000e8bb3a220e1b4881a290683402abe742a85000003a2ede414881a0d8bb386d0d01434024d014000007880881d20488881d0e0bb1e222207439bdd1409289de20d91e220000034024c63c823ba20633405620681e1e29068
def rowPack1535k11i66 (i : Nat) : Nat := 0x3c9c95400c61e4c4016fbe319248845001143c6338478f2
def rowPack1535k12i5 (i : Nat) : Nat := 0x5f0e8883a0f11000000000000000000000be440d000000000000000000000881d1760000000e83c445f22068
def witnesses1535 (k i : Nat) : Nat := (if k<11 then (if k<9 then if i < 0 ∨ 0 < i then 0 else packedAt rowPack1535k8i0 (9*(i-0)) 9 else (if k<10 then (if i<1 then if i < 0 ∨ 0 < i then 0 else packedAt rowPack1535k9i0 (18*(i-0)) 18 else if i < 1 ∨ 8 < i then 0 else packedAt rowPack1535k9i1 (9*(i-1)) 9) else (if i<2 then if i < 0 ∨ 1 < i then 0 else packedAt rowPack1535k10i0 (27*(i-0)) 27 else (if i<11 then if i < 2 ∨ 10 < i then 0 else packedAt rowPack1535k10i2 (18*(i-2)) 18 else if i < 11 ∨ 31 < i then 0 else packedAt rowPack1535k10i11 (9*(i-11)) 9)))) else (if k<13 then (if k<12 then (if i<12 then if i < 0 ∨ 11 < i then 0 else packedAt rowPack1535k11i0 (27*(i-0)) 27 else (if i<66 then if i < 12 ∨ 65 < i then 0 else packedAt rowPack1535k11i12 (18*(i-12)) 18 else if i < 66 ∨ 86 < i then 0 else packedAt rowPack1535k11i66 (9*(i-66)) 9)) else if i < 5 ∨ 17 < i then 0 else packedAt rowPack1535k12i5 (27*(i-5)) 27) else (if k<14 then 0 else 0)))
def rowPack1839k6i0 (i : Nat) : Nat := 0x19316
def rowPack1839k7i0 (i : Nat) : Nat := 0x22c30
def witnesses1839 (k i : Nat) : Nat := (if k<7 then if i < 0 ∨ 1 < i then 0 else packedAt rowPack1839k6i0 (9*(i-0)) 9 else if i < 0 ∨ 0 < i then 0 else packedAt rowPack1839k7i0 (18*(i-0)) 18)
def rowPack1663k5i0 (i : Nat) : Nat := 0x31
def rowPack1663k6i0 (i : Nat) : Nat := 0x31
def rowPack1663k7i0 (i : Nat) : Nat := 0x603a
def witnesses1663 (k i : Nat) : Nat := (if k<7 then (if k<6 then if i < 0 ∨ 0 < i then 0 else packedAt rowPack1663k5i0 (9*(i-0)) 9 else if i < 0 ∨ 0 < i then 0 else packedAt rowPack1663k6i0 (9*(i-0)) 9) else (if k<8 then if i < 0 ∨ 1 < i then 0 else packedAt rowPack1663k7i0 (9*(i-0)) 9 else 0))
def rowPack1903k5i0 (i : Nat) : Nat := 0x1ad
def rowPack1903k6i0 (i : Nat) : Nat := 0x3443c4b0cd3231
def rowPack1903k6i3 (i : Nat) : Nat := 0x7e00001af
def rowPack1903k7i0 (i : Nat) : Nat := 0x3563c000019e334c0cdac304d8f15316
def rowPack1903k7i7 (i : Nat) : Nat := 0x3d9233188506231000f000308ced5a6311f8036bb518eeee8a91fee00033
def rowPack1903k8i1 (i : Nat) : Nat := 0xe014700f1c0f700001bb304d0f1303f382ed38146eac89c0a6c8c352e96b8c1c23000002d4e0276d530316b8f13234c50522ce9678fe2ca9382eef9303803e2ca96eac9c2144c0c4e00a708cd3034aeaa1b2304e0ff563c
def rowPack1903k8i40 (i : Nat) : Nat := 0x3c000f2fb3164aec00ee64bb992c90a0fc2814e9cc4003098384280095375640064ac965164c00062d970aedbe001e0c460b97755152148b001c0d9
def rowPack1903k9i1 (i : Nat) : Nat := 0x458e014
def rowPack1903k9i7 (i : Nat) : Nat := 0x70aedc2bb00001c23f708c1c33170aedc2bb70aedc2bb000000000708f1c230
def witnesses1903 (k i : Nat) : Nat := (if k<8 then (if k<6 then if i < 0 ∨ 0 < i then 0 else packedAt rowPack1903k5i0 (9*(i-0)) 9 else (if k<7 then (if i<3 then if i < 0 ∨ 2 < i then 0 else packedAt rowPack1903k6i0 (18*(i-0)) 18 else if i < 3 ∨ 6 < i then 0 else packedAt rowPack1903k6i3 (9*(i-3)) 9) else (if i<7 then if i < 0 ∨ 6 < i then 0 else packedAt rowPack1903k7i0 (18*(i-0)) 18 else if i < 7 ∨ 33 < i then 0 else packedAt rowPack1903k7i7 (9*(i-7)) 9))) else (if k<9 then (if i<40 then if i < 1 ∨ 39 < i then 0 else packedAt rowPack1903k8i1 (18*(i-1)) 18 else if i < 40 ∨ 92 < i then 0 else packedAt rowPack1903k8i40 (9*(i-40)) 9) else (if k<10 then (if i<7 then if i < 1 ∨ 1 < i then 0 else packedAt rowPack1903k9i1 (27*(i-1)) 27 else if i < 7 ∨ 20 < i then 0 else packedAt rowPack1903k9i7 (18*(i-7)) 18) else 0)))
def rowPack1919k6i0 (i : Nat) : Nat := 0x13231
def rowPack1919k6i2 (i : Nat) : Nat := 0x31
def rowPack1919k7i0 (i : Nat) : Nat := 0x132314c0c53231be422fc31
def rowPack1919k7i6 (i : Nat) : Nat := 0x150a905c01ae190c6f89418c5c797dbe4207f17bde9af7c518d40629d
def rowPack1919k8i0 (i : Nat) : Nat := 0x7bbd8c529a61fdb22e3c
def rowPack1919k8i3 (i : Nat) : Nat := 0x1534c1f8753c318b8634c31be5253c33198740000d20fef930490ff563c00003638e000013c31830bc7e1dbe4b0761ebe4ab4c3f83294661dd5beef52a4f423626924a9400004f0cc941d8b8612433be0c6f6314f0fc661f3e0c4661dbe4aaf8e6bdcc1aa314f0c47e1d
def rowPack1919k8i51 (i : Nat) : Nat := 0x13c9218f2a2e3c98801a43fbe4c2a5174ea7a460098548677c954b952333bc01d231974aa549ebdcc2f892188c068314f0038a34efa7878300021e54310054e2f1da7caaf97c1e0cb4d170052aae31918013dba0000062fcaf0fcef4d984ab511718800627e9b8ff8231
def rowPack1919k9i0 (i : Nat) : Nat := 0xb5eac796c8b8f2949e1fe9eb83c
def rowPack1919k9i8 (i : Nat) : Nat := 0x34051bab11f874781dd4cac781d1e074601d700edc03fd8d54681db09dc7e1d0000000006e9dde41418e0400001887712148b3b8d00ac829a2e1819874661dbe4a9e40f00001c121490fe9ee07ce0496b1d8b4f1bc7382dc000024824d00ed4cc07e1d00001ba776e8f1bf8079039c0414f0c62c3f78bdc0000248252430be0cce0bd8cac5b1d0790393c3f4c2c5c03f8b295e9308b3c45e1b6fadeb83c6a0c12433c68c0621ea70f1c2bb4f0cc7e1f6cf1e2c49700fc92a518874d0b1276c6618025ac86381343dd3d318c8f1771619874d9c734056f8a91f875b2304f4c720a624a947e1d6c0f0661d1987467bd18e047e788b5fd2433d48bd53bc00001bab16c8ce447700001e414c40487e78700f0661d8b2c4661d700f1b03026875c03fd60f0618279050d8b2198971a30be0cdc03fbe4c232b1272f53d2f8c0f31a3019e00681d4f0c47fbebe0c71214700fc621dbe0cc6381c83a1b23f708c00000443831ab7700fdc03f1f8947e1d6c8ec97b424824e0b7276d284e71f9dc661d6c8c62d7f18b2c96b1b0ac467801f9e124347010400008b3a5e2f7a7b81c1d078bde2ca98caa5c1371e07476781fa207e1d6e9df1ab7700ec9cb100000e0bb
def rowPack1919k9i207 (i : Nat) : Nat := 0x17614188c4ee146c9dfa4778c8ad76330a0f067bd00600018b3b8ac0077b0aec00f71f8f1d2e91f85078b73bf480116a78c697310a4a8000e12ac400307a54c63c75b9dc2800180f29f161e36467614f2ec289f000c461611e0c6b92a6c8f2327718850637c182ec61beac8c063ac588d260e11e1dc63235d8755231180c77a000a4c38f31000c069ab1848eb97cab0007931180cc62bb5d8c174d90a0d078341e58564344f8c4003c00779c37c4f0f02892362eddc0018826f834000fc0031002a462921f8c6f959be0f260311e0c46345e553d7609770fc609eb0f28780098bddc03f7bda879ac180c701301e1dc60bb914c4001da78c4623f188f262301885028318b8c428779f2c46600ba748ef2a1d8f0783f748cc7e3f0a48c00e98d0c77aa9d52ec63ca748c029165dd3c794fb087577d44f2c4292a18e0078ee19ba963603bbd28a3cb70f2b6d91a46828140cc5cf0778b8c5623f981a47e1d1fef4623f7b8c4623c1e0c2543f7b9dc123049001c077
def rowPack1919k10i2 (i : Nat) : Nat := 0x286680a00000000000000000000308705d8000000000000000000022c300e80000008b124131678bdc00000000000004c0d03a0000002c23c3be3dae300000000991a0762c92180000000000000000000009c3c0ed2dc03cd4d707800000022d8d58c58e0bb00000000000000000000458d00e00000015f25ac4000000459e414
def rowPack1919k10i40 (i : Nat) : Nat := 0xe0bb7bb25b331ae2c463be00001c2bb00001c2bb8b2ec00006cf2a9ee01f9e289d3b02ec00006eac5b2308d2ec00000000263806c8c4d0f78b1a1c230be2c69ee070aec00008b3b9c230793247e1dbe2e9c03cd60c1c23c70aee2c30708c6f9316c8c1ba77700fc0000c6ac5e4f78b0c1c329708c4d014708c2c23ca7bb9c0f7c6addbab134051383000000d014be2ea2ca96e9dc63816c8fcd0f74f4c5ba77be2a62d8d8b2a5c2bbc68c1b2f7000000000a7b8000000000078776c8c07e1d70aec0000708d00000000031ab76c8f29e3c79051c23434051bf8034051c2bb708c1c2bb6c8c07fbd00001c2bb00000000000001c2bb708c5c23070aedba3c703b9c3316eac6dc3ca78f07e1d700f2f8ee1e1dd243f70d522ebb70aedc2bb7905000001f894000070aef1ab7c6bdc7e776eac5c2bb6fe01c23f708c6dc306eac400000000208bb6e9dc0000c6ade08f7708c1c234708c0d180490fc7e1dd60f1c230000031a30d60fcd01470aec7e1d6eaca2c30beac5e41470aeefab170c8f1ab7a7b8000008b1a1beb8b0aec7e1d70aedc23f708f1bb8b6eac5bf8000000d0144e0c1b33100002c2bb700fc000070aec0000000022c928b2edc23f708c1e531703b9c230703de2cbb
def rowPack1919k10i243 (i : Nat) : Nat := 0x18001777c000fef831000c1c20070d8ec630002ec60bb5db85c2001fb8400bb00385ee0070b85c2e15d8022c0070801c23f5dc5a2ce1182ec78301f8f262e1184c5c2bb98cc5c2bb1838400008b2ed76e170802623070cc576e170800000070cc5c2bba338478bb5d8f060317080177315d8022d16a20f000bb708fe2c00000c5c230000c00131
def witnesses1919 (k i : Nat) : Nat := (if k<9 then (if k<7 then (if k<6 then 0 else (if i<2 then if i < 0 ∨ 0 < i then 0 else packedAt rowPack1919k6i0 (18*(i-0)) 18 else if i < 2 ∨ 2 < i then 0 else packedAt rowPack1919k6i2 (9*(i-2)) 9)) else (if k<8 then (if i<6 then if i < 0 ∨ 4 < i then 0 else packedAt rowPack1919k7i0 (18*(i-0)) 18 else if i < 6 ∨ 30 < i then 0 else packedAt rowPack1919k7i6 (9*(i-6)) 9) else (if i<3 then if i < 0 ∨ 2 < i then 0 else packedAt rowPack1919k8i0 (27*(i-0)) 27 else (if i<51 then if i < 3 ∨ 49 < i then 0 else packedAt rowPack1919k8i3 (18*(i-3)) 18 else if i < 51 ∨ 144 < i then 0 else packedAt rowPack1919k8i51 (9*(i-51)) 9)))) else (if k<11 then (if k<10 then (if i<8 then if i < 0 ∨ 3 < i then 0 else packedAt rowPack1919k9i0 (27*(i-0)) 27 else (if i<207 then if i < 8 ∨ 205 < i then 0 else packedAt rowPack1919k9i8 (18*(i-8)) 18 else if i < 207 ∨ 536 < i then 0 else packedAt rowPack1919k9i207 (9*(i-207)) 9)) else (if i<40 then if i < 2 ∨ 39 < i then 0 else packedAt rowPack1919k10i2 (27*(i-2)) 27 else (if i<243 then if i < 40 ∨ 242 < i then 0 else packedAt rowPack1919k10i40 (18*(i-40)) 18 else if i < 243 ∨ 362 < i then 0 else packedAt rowPack1919k10i243 (9*(i-243)) 9))) else (if k<12 then 0 else 0)))
def rowPack2031k7i0 (i : Nat) : Nat := 0x3c
def rowPack2031k8i0 (i : Nat) : Nat := 0x87156cc55678d356f7
def rowPack2031k8i4 (i : Nat) : Nat := 0x15e1e05078143193f1814318f8783c5178d7c3f07971d2a9
def rowPack2031k9i0 (i : Nat) : Nat := 0x1537c882fb563c
def rowPack2031k9i2 (i : Nat) : Nat := 0xe83c380289e14f16d6f82238050aa113a2e49e141a88ce63cd444116bbbe18c9e3c8d970a203318f06a23288f09e3f886d4aa0f28ac8aa0f70486f91031ba621d7270289c0a4c4c4a23c31bba20e098a15b31e392ecc63c31bdcc6e7318ee206345ac8e4bb8e13cc63c3a2c9b3d2398f0e8ae6eac8a8ba678d09cb2678fcc63c313dcaa14703ddc03f3a2c8e0bb31908aac0707409e1428ac8c64231bddb3d231bace6ee704dcac3c8817c9db5678d4a20f2b2e6d0551f88ef8104e0d5c03c
def rowPack2031k9i87 (i : Nat) : Nat := 0x5d8f078149a98c683c288f3ba3f283a5b29a31d4d443c5faeda03c5d8f130bb050518cbb1f98ca2341fa8acf361e08f6a342a8f177315daec29365f95544852b2ee6e3427850e8f7118507823
def rowPack2031k10i0 (i : Nat) : Nat := 0x1393802a20745dc58aabb881c17710380522c745dd08aaa8881d0791031bde20d9ebc409db5881381510708c2ce631e440e8bbbe154217c8828af8745da607e23881d1771031ba530551fc419e35
def rowPack2031k10i23 (i : Nat) : Nat := 0x3a2edbb313a2edba84ec30ce0bb70b0d3331a41c0e8b9278fe21d83a2ec7e23a44c5303f70aedc2148818cc63c2aae8e8bb318f0c63c3805138234e0d4a23c3a2ece0c338050e6f73a2ee20633a2edc2349e9d290551a88dba23a418ce01438050c63c8818dc23c3a2eca2b231bba20e03a2efb02388366905131bdcaa0f318f1c21438050e63c
def rowPack2031k10i83 (i : Nat) : Nat := 0x4c576bb003198c7463387b0e15db1976c6
def rowPack2031k11i4 (i : Nat) : Nat := 0x440e8bb000000110708c220745dc40e8bb
def witnesses2031 (k i : Nat) : Nat := (if k<10 then (if k<8 then if i < 0 ∨ 0 < i then 0 else packedAt rowPack2031k7i0 (9*(i-0)) 9 else (if k<9 then (if i<4 then if i < 0 ∨ 3 < i then 0 else packedAt rowPack2031k8i0 (18*(i-0)) 18 else if i < 4 ∨ 24 < i then 0 else packedAt rowPack2031k8i4 (9*(i-4)) 9) else (if i<2 then if i < 0 ∨ 1 < i then 0 else packedAt rowPack2031k9i0 (27*(i-0)) 27 else (if i<87 then if i < 2 ∨ 86 < i then 0 else packedAt rowPack2031k9i2 (18*(i-2)) 18 else if i < 87 ∨ 154 < i then 0 else packedAt rowPack2031k9i87 (9*(i-87)) 9)))) else (if k<11 then (if i<23 then if i < 0 ∨ 22 < i then 0 else packedAt rowPack2031k10i0 (27*(i-0)) 27 else (if i<83 then if i < 23 ∨ 82 < i then 0 else packedAt rowPack2031k10i23 (18*(i-23)) 18 else if i < 83 ∨ 97 < i then 0 else packedAt rowPack2031k10i83 (9*(i-83)) 9)) else (if k<12 then if i < 4 ∨ 8 < i then 0 else packedAt rowPack2031k11i4 (27*(i-4)) 27 else 0)))
def rowPack2047k7i0 (i : Nat) : Nat := 0x388ff
def rowPack2047k8i0 (i : Nat) : Nat := 0xee389c7db
def rowPack2047k8i2 (i : Nat) : Nat := 0x2e694b9532b80000e4006974a8f2b16cb85c
def rowPack2047k9i0 (i : Nat) : Nat := 0x3e8ed3d77be3b30729be398ac3ca413af8e68d9594fbfc1c7800002780f563f88186f91fbe43e8f788817a1e4027028b9c62782af91fbe450fba5a3cab563fb37713dcc2b72783102702b07074f0ff062f8a172f8ec2b0ef231be0c489c21a3caa365c887709e0a8d9735641c1ca72661be3993c4088a7a2699d58fd3230d5906365c
def rowPack2047k9i59 (i : Nat) : Nat := 0x288797c2e52e274700098761d1f87479a5a45f078633197276318e96400c12e1707753884d6212f1e0db4a55d2dd74a781e0c4b85c9c74ef97cf418ef83fa3df2277c9e973c3c331c427b3c1e0f0b85c1a164845ca38f082009e80297e02e5f078e9b28f0c63ce40f0ade71ff94683c89c407e5c881c7b947
def rowPack2047k10i0 (i : Nat) : Nat := 0x363662ac4ca43c
def rowPack2047k10i4 (i : Nat) : Nat := 0x25ac4e8bb34028d8bb2b0f2b0a8398f0e8c6be440e8bb382ca0510b4957531ebe443bac0510ecaaa8b3c1d16b1aeed2f8634f7306a1d2b0f123d06c0fce83cb7748d8b23f289300ac9985e2f7b415621d02702b855ed5bb2d77c4f420d6b400000681d362caf91025ac6365c8a18cfb7c3a2ee90f18d98ed055880b4d8b2b3f48000078dcd4542a44c624741a874d4ae2b2ef2b7c28e81c2302a83addd23a0f1c2308b0c28f2a2a2e8c6e7880607678a4154e8bbb30bdc03f318fcc2e72b0f0e8bbbe4413cf93a2ecc6e7d2c40c71524825c124b74a5c30725ac6b9b52a8762030c3441b1d78b3bace3f88742b2a8392e4c2e93edf2ce3f382ece8bbb58f284e745ac6f9208a383195f2b0f2243028ac40000318f0b83b24826621d00000d8b2707370635a44b52435b74a4d8b29e155e2f770c7add1e2a2ee20bb700b4c6f724824c63c4f0d1c230319068e5cbe47ca2784f0c4aaa88d97096b125ac4c6edd58f220612caee84e72b2ca7855c998c9c0a35ad3191031908c642881d0e0b28918ca23c27828c6e9390f0c0f76c741b3078d9722ce989f4f25481f874a2b1be441c03c392ee904e390f0aca8a3caaf91087b8116a930ba62a2d4903af85c88411c041b8740c242289e0d4ae2a86cc6e7be440c62ab4956c4ee6c74092a5708c2205f00002905c8d958e83c1a874e8bb6cc1ef9103190a365c8d972912d3a2ecb2a86c73b563cb70c0e63c8818ce43c8d9722c42d58f2cfd2700fde2f72b2ee365cbe3b4ac3c31bdce63c3a318e8b2392eea6e16c741b2346c8d22c594f10383106cca6cfd0700fe368f3a02b19108d972ce638817e243c31c59b3d2318ecb0a83a0f3191b2a2e93c319d9713d2ad298ce8e7b38d4e8bb6cc78acba31bdef9392b31a206d3a2ec9cb13a318c6e78818e8f2ac6459c2bb8d98f19103a0f0b0bb3a2ecc6e570485bab16cca4adc9318f3563cb80b7463c362c93c3489382dcb1b88c0b2a8be443563f70104980e8a170e8c6ae02ac4e93a2eef86330904e8b9a5b80acba3382af85c8b2ee7e552c2a0c641b70d53d21700fef96f
def rowPack2047k10i342 (i : Nat) : Nat := 0xf285163d87488c28340a4f6977c3ba883bd81e319efe97be4cc63c1f8f07929dea89d72f0e8f02935988f0001d4f1d2f86300520ef3d1e3acee85eee31763c60d003a003a15429362a9d3ab471df3a201d1e0f028c131cc447bd78802f9361e4d93d53a38f0ee3f5dd2012f71faedd7790a5becd10630507e144f3818a1404da58c3f98d9d8c140e970792f5ca14e81497850783bbe0758d7c6c9d2214718c40ab10209d879100ea8976c131bdc783cde8f07e3f510f0841d514407f672acda2767a41725e5604ac460c674ba478710a52079a5a40753eb92f8edee1d7595620637bc40783c1f98ef8c11b0f25ec61e4d8c67821026f8771e2e81e3c8f0d0797c0ea7ae214d4279d21d1a0503a74988f10a3f3b9d3b375f0077c2f71e3ae621d3a0d1ee77880ec461d1e440ab31886f428747bbebc8f7eb59ef81d1fa2e53101f956f8632acc6903c3bcc484559b8f0ec55319dcabe1de98c78741e08e9e141e1c58c71de85078008874ef9595def4e8550a2ecbe09b4cc67263608f03a6358800c63c0a00028c18847c29d3be3dc79d83a170b8c19bcd446f20e852903c4f075877c3a0f2f9bd608502874
def rowPack2047k11i4 (i : Nat) : Nat := 0x440d0149c9a014a9be4428455545bcd8b2be59a516dd58f220631e458a2b1881cc797c2aaa3277c31df0d4ae0000001936cc7b81102fc40c63c88383a11645ac5457cb3c41b3d22edf2211024826f86c59441c03c8818ddd6fb775e204904c4096b14c0fc3b103190620631e42ca23c8818def7c883c620725dc41240ef31c8791031bde20e01fd08c6e7f28f03b1231bae206374c58c642881cc7914318f00000006962063df955811645ac4000000440a2b18a98c796f3a0f2de745cc41b3078818c77106c8d6206320c41c03fb3958796f35ad2204e58a60681d88367a5a52b2ea20dd58c41b1d08b18c857c2a2e8000000610e4bb
def rowPack2047k11i77 (i : Nat) : Nat := (if i<1 then 0xe20302aaee36633405220e0700f1b3298818dba7700002f91070c7a3663708c0c63c31bdcd014700f290558818caaba1fef4c6f7be5a5c12f318f0e8bb4f4aa20a28d0f22ca2882ee96a21ab18c6f76eac400001aef4e8f73a0f1e40ab128c9cb1b8aec92098838469bda415620630000236a231ba5c33198a12e2b13a2ecd021346c6dc30be440e8bb2aaa220f83a0f0e8a8a41d0e8bb88762f834ad2c8aaba6eac6905688365c3d27905220687903e20ee318f0aabb708c2621b24824687731bdc7e23a41a0c63c31bdce8bb1fb04981d45aee84a83a0f2f863708c1c3296eac620748230caac698876203c883dde414708d4e8bba4288e8bb2aaede5d23a0f2f834318f2907470ca5b2343a2ee2074881a0e63c3a0f0d1bd00000c63c28ac40000883b8d0148b0f0e83c8b0f0a2b1bb0d238743a2edc03cb38d6d2f74c074e83c880d691311e318aaba3a0f3b0c66cf5cc6f7318f1c3313a2ec0000881d0e8bb318f22074700b5e414a44c4aabb3a2edc1d09c9a1c02d79052f8a331ba62063318f0d8bb3a2ecaaa83a2ee20e0318f2206145aec92093a0f0e8c628ac4e43c3a0f0e8bba1154d00abe1b1e41470c79c2bbbe440c736ad2a0c6f71e1dde5743a2ecc6edbe1d06ac62b052de3c881d1c2303a2ecaa1470f2dc23c882ecc6f73a0f2f8ed340530f103a0ee2074b7dba209c340523663be300a8bb398f0d014700f286bb318f0e8b91ab18d00a1f9de621d882ee9055362c8a23c6c8c4d01488380e83c1a88c7e77880f0e8bb881d0d014881c6d255be050e0bb9c828e8bba1ba4d8bba41a2f8c68818ce8bb6e9de9063884d4d8bbb70d5c0ee340529074318f0c63cb70d0c6f728ac8e8f7308fcacbb8818e6277be18caac31ab0620bb1ab047ec6882edc3233a3de20e0b8a16365c700f2f863be440e8bb4f0d1e414883ba20e0318f078779ef762074288f1c35370b1a2014382ec93bc318fcd8b21e220c6f731bdc6a1d700fdb23f1aef5e2f77074220f2708d5c23034053c2146c740d0f7ec318e83c28ac4e6f779051c3d2343ded23c708c1e414703dcc6f734050d8b228ac4e83c3a0f2913170aece84239bdcd00a1a075e4141e220e97c79051c12731bdca2b18818cd0096c8d5321d3a3ddc3238818ede7400000c63c881d35830823b87e778d970e0bbbe1d0c6f7882efb43c3a2edc2308d9d0e83c708d4d014a43c8e8bba4171c331af98ce83fbe18cd8bb708c1c32934050981d34050e8c63a2ef087028ac67a63318f0d814880f116a8a418cc6f77902a20683a2e67a682aaa0920934050c6f7700fce83c24826c4eebe441e488708fef9103402977102b0f1e414318fcc63c318f1b3d2708c286ee382f4aa143a2ecd8b21a87478783a2eef96788386f86324ef0ac3cbe0c0e83ca418cc63c3a0f220e06c742203c3a0f06ac6 else 0xe8bb700fe91311e074e8bba5b807888794c4d0142b0f3b0c6a3ca916b2790506ac631bddc03f882ede4211ab18681d2aaa4c6f71a874c63c2a850e8bb88380e0bb3a2ece83c1fb1a8474898c1c230b8aee20e03a2c6f9103a2edc03cb7b81e4f7318f0d8b21f8769ee031ba4c6e93a0f0c63c386f0c63c25ac5c337289e2f939989dce8bb7ba20ac3c2482492096c8c1c2bb398f0e8bb3a028e8423a3def8748875caabb3a0f07ec13a4d9381d9cb8220f7883822c3031bb916b139bddc231be440e8bb31bde872931ba5e430a5b80d8f79e954c63c70cc4e8bb883c4c63cbe156907400002f830883dc6ac6a41d22049510f0d01428ac5c2bb70f4a21d21ab18aaa8be440c63c3a2ece8bb1f9d)
def rowPack2047k11i652 (i : Nat) : Nat := 0xec4c5761d31ef662f76cdf03b6e88761c0c61e4c5823c2abc878e1be0dbc0741e050e9101e6f4783cde07662345198cd0bb5da158c632af6046bb1e1d176e06374a20e098cc576141e5d2de3c6c955c2141e522203c70aedee3f1e4c4ab3163387b0f794b842856632edb23f5daecc7317705220e11e1dcc6745d9d3b03f2a8f27274184c6e4c6be0fe6ec698946f948341566dd82acc4e8f23a2737a3c2ab0d8cf25d802203cec0fe6f1000386903cb4ef57710791de21d8632ecaabb2ab8621e4aa31878513ba14e8001e1d078f71b3df9ee15d9d286743ba2d76e11fbc801311a1553f6e7b8f07855deb8478c651bc8d17cec1d220b9183187ee1f0b18aa63453dd76741f9558c001fb677b31ec1566c632a9dcee14be366637cec3ddc3486cb19c36f8831829d2709dc283c4f6f620bb1b157a4c61fdbe9ee16cb850ae10a3c8c63c1e4e828f23a520783c61df3c2e12aa718c8b1f9a0697c2ab18c748630f176301e050aac158aedc23c318f226771e520783c0a318ab3600520e8c11e364e8145d95446c6700f3c8f2be5207ef7
def rowPack2047k12i24 (i : Nat) : Nat := 0x290f298c10aabbbe440e94879155e4557bc40c6f700000017c7930e2068de00000004ccc43b6e1a88ef83560df220142abdd8710708c220680a441ba7779154297c8818e20631e440e8bbbe441dc741e31a20745ddf220a3881d17710708f236631e0000000883c8291031bba20e15dc40d0f78b155771028ac686555dce4e8bb708fd8d1079052de6c5d80000009c9d176511f9de72680a440e8bb881d07910708c220741e440d014be154295f318f2f91077440c63c8818c797c3a2ee20d91a800000088387a510398f220705dc40c63c8818c7910708c226680a5bcc63c00000000000002205158c40a2770000001103a2ec0000005f220638818c7f10318f220745d8000000709547e9c1aef62073e5440d01400000016f3a2e6f91034440e8f7
def rowPack2047k12i110 (i : Nat) : Nat := 0x70aee9131000000000881d22074a41d1c23070cc6de743a2ec0000880f220743a2ec6ac63a3dc00003a2ece8bb3a0ffb0c6be441c331881d1c23500001c2bba4154e8bba41d0000070cc4e8bb3a2edc23f3a2ee20e13a2eef9103a3dc0000a41d0e8bb3a0f0aabb70b18e8c63a0f0e83c3a0f22c553a2efb0c670b1a9074880c1c3313a2ec6ac61fb1a207488760e83c881d220748838672743a0f2207470b19c2c68838672e100000e83c88762f855881d221d88838400003a0f0e8bb0000290742aaee2074
def witnesses2047 (k i : Nat) : Nat := (if k<11 then (if k<9 then (if k<8 then if i < 0 ∨ 0 < i then 0 else packedAt rowPack2047k7i0 (18*(i-0)) 18 else (if i<2 then if i < 0 ∨ 1 < i then 0 else packedAt rowPack2047k8i0 (18*(i-0)) 18 else if i < 2 ∨ 17 < i then 0 else packedAt rowPack2047k8i2 (9*(i-2)) 9)) else (if k<10 then (if i<59 then if i < 0 ∨ 57 < i then 0 else packedAt rowPack2047k9i0 (18*(i-0)) 18 else if i < 59 ∨ 165 < i then 0 else packedAt rowPack2047k9i59 (9*(i-59)) 9) else (if i<4 then if i < 0 ∨ 1 < i then 0 else packedAt rowPack2047k10i0 (27*(i-0)) 27 else (if i<342 then if i < 4 ∨ 341 < i then 0 else packedAt rowPack2047k10i4 (18*(i-4)) 18 else if i < 342 ∨ 721 < i then 0 else packedAt rowPack2047k10i342 (9*(i-342)) 9)))) else (if k<13 then (if k<12 then (if i<77 then if i < 4 ∨ 76 < i then 0 else packedAt rowPack2047k11i4 (27*(i-4)) 27 else (if i<652 then if i < 77 ∨ 651 < i then 0 else packedAt rowPack2047k11i77 (18*(i-77)) 18 else if i < 652 ∨ 1007 < i then 0 else packedAt rowPack2047k11i652 (9*(i-652)) 9)) else (if i<110 then if i < 24 ∨ 109 < i then 0 else packedAt rowPack2047k12i24 (27*(i-24)) 27 else if i < 110 ∨ 197 < i then 0 else packedAt rowPack2047k12i110 (18*(i-110)) 18)) else (if k<14 then 0 else 0)))
def witnessSet (m k i : Nat) : Nat := (if m<1535 then (if m<189 then (if m<31 then witnesses15 k i else (if m<111 then witnesses31 k i else witnesses111 k i)) else (if m<383 then (if m<191 then witnesses189 k i else witnesses191 k i) else (if m<511 then witnesses383 k i else witnesses511 k i))) else (if m<1903 then (if m<1663 then witnesses1535 k i else (if m<1839 then witnesses1663 k i else witnesses1839 k i)) else (if m<2031 then (if m<1919 then witnesses1903 k i else witnesses1919 k i) else (if m<2047 then witnesses2031 k i else witnesses2047 k i))))
def cornerCode (m k i : Nat) := witnessWord (witnessSet m k i &&& 511)
def retentionCodes (m k i : Nat) : List Nat :=
  let w := witnessSet m k i
  if w<512 then [] else
    let a := witnessWord (w &&& 511)
    let b := witnessWord ((w >>> 9) &&& 511)
    if w<262144 then [a,b] else [a,b,witnessWord ((w >>> 18) &&& 511)]
def wantsRetention (g : Forest) (k i : Nat) := decide (512 ≤ witnessSet g.mask k i)
def vettedRetention (g : Forest) (k i : Nat) :=
  !(wantsRetention g k i) || retentionReady (retentionCodes g.mask k i) (targetOf g) k (stateSet g k i)
theorem vettedReady {g k i} (v : vettedRetention g k i=true) (w : wantsRetention g k i=true) :
    retentionReady (retentionCodes g.mask k i) (targetOf g) k (stateSet g k i)=true := by
  simpa [vettedRetention,w] using v
def baseVerified (g : Forest) (k i : Nat) :=
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
  vettedRetention g k i && (decide values.Nodup && !(values.contains (targetOf g)) &&
    (if k=0 then true else testAll (k,ws.length,ws,preCov g.mode ws,rules,ls,wantsRetention g k i) ws))
theorem baseVerified_sound (g : Forest) (k i : Nat)
    (samples : properPairs (targetOf g) (asRow fun j => (g.samples j).1) (asRow fun j => (g.samples j).2))
    (cols : ∀ ci ∈ g.cols, Slice g.mode (varsX (rawMask g.mask ci)) (targetOf g) (subcube ci.1 ci.2.1) ci.2.2.2.2)
    (names : ∀ x ∈ g.autos, autoOK (targetOf g) (x.map swapRows) = true)
    (prior : k>0 → ∀ j < (g.levels (k-1)).1, Impossible g.mode (targetOf g) (k-1) (slotWires g (k-1) j).toFinset)
    (checked : baseVerified g k i = true) : Impossible g.mode (targetOf g) k (slotWires g k i).toFinset := by
  by_cases gone : omittedSlot g k i=true
  · simpa [slotWires,gone] using (emptySlot (u:=g.mode) (T:=targetOf g) (cap:=k))
  rw [slotWires,if_neg gone]
  simp only [baseVerified,Bool.and_eq_true,decide_eq_true_eq,Bool.not_eq_true',List.contains_eq_mem] at checked
  have audit := checked.1
  replace checked := checked.2
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
  apply node_sound (raw:=vars g.mask) samples _ hN hT _ _ _ (by simpa only [h0,if_false] using checked.2)
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
  · intro a ha b hb d hd ka kb ne fr ready len
    have lt : d<4 := by rcases hd with h|h <;> omega
    exact retentionSound (vettedReady audit ready) hN ha hb ne lt fr (Nat.pos_of_ne_zero h0) len
def cornerOK (g : Forest) (k i : Nat) :=
  if omittedSlot g k i then true else
    let code := cornerCode g.mask k i
    let r := fun t : Fin 6 => Fin.ofNat 512 ((code >>> (9*t.val)) &&& 511)
    let ws := stateSet g k i
    decide (ws.length=k+1 ∧ ws.Nodup ∧ (ws.map (cornerValue r)).sum<cornerValue r (targetOf g))
theorem cornerOK_sound {g k i} (h : cornerOK g k i=true) :
    Impossible g.mode (targetOf g) k (slotWires g k i).toFinset := by
  by_cases gone : omittedSlot g k i=true
  · simpa [slotWires,gone] using (emptySlot (u:=g.mode) (T:=targetOf g) (cap:=k))
  rw [slotWires,if_neg gone]
  simp only [cornerOK,if_neg gone,decide_eq_true_eq] at h
  apply cornerBound _
  · rw [List.toFinset_card_of_nodup h.2.1,h.1]
  · rw [cornerSumList _ h.2.1]
    exact h.2.2
def nodeVerified (g : Forest) (k i : Nat) := cornerOK g k i || baseVerified g k i
theorem nodeVerified_sound (g : Forest) (k i : Nat)
    (samples : properPairs (targetOf g) (asRow fun j => (g.samples j).1) (asRow fun j => (g.samples j).2))
    (cols : ∀ ci ∈ g.cols, Slice g.mode (varsX (rawMask g.mask ci)) (targetOf g) (subcube ci.1 ci.2.1) ci.2.2.2.2)
    (names : ∀ x ∈ g.autos, autoOK (targetOf g) (x.map swapRows) = true)
    (prior : k>0 → ∀ j < (g.levels (k-1)).1, Impossible g.mode (targetOf g) (k-1) (slotWires g (k-1) j).toFinset)
    (h : nodeVerified g k i=true) : Impossible g.mode (targetOf g) k (slotWires g k i).toFinset := by
  simp only [nodeVerified,Bool.or_eq_true] at h
  rcases h with analytic|standard
  · exact cornerOK_sound analytic
  · exact baseVerified_sound g k i samples cols names prior standard
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
  (chartSamples g.mask (fun j => (g.samples j).1) == BitVec.allOnes 91) &&
  (chartSamples g.mask (fun j => (g.samples j).2) == 0) &&
  g.cols.all (fun c => colCheck g.mask c prior) &&
  g.autos.all (fun p => autoOK (targetOf g) (p.map swapRows))
theorem forest_all (g : Forest) (top : Nat) (prior : Nat → Nat)
    (lower : ∀ q, Lower g.mode (varsX q) (graphGoal q) (prior q))
    (geometry : graphValid g prior = true) (rows : checkedTables g top) :
    ∀ k ≤ top, ∀ i < (g.levels k).1, Impossible g.mode (targetOf g) k (slotWires g k i).toFinset := by
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
  decide (i < (g.levels k).1) && sameWords (slotWires g k i) ws
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
def extendKnown (old : List (Nat × Nat)) (L : Nat) (relabels : List (Nat × List Nat)) :=
  relabels.map (fun v => (v.1,L)) ++ old
theorem extendKnown_ok {u old L m relabels} (previous : Known u old)
    (main : Lower u (varsX m) (graphGoal m) L)
    (ok : relabels.all (fun v => relabelOK v.1 m v.2) = true) :
    Known u (extendKnown old L relabels) := by
  intro e he
  rcases List.mem_append.mp he with hx | h
  · obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hx
    exact relabel_of (List.all_eq_true.mp ok _ hv) main
  · exact previous e h
theorem baseKnown : Known true [] := by simp [Known]
theorem known_down {u es} (h : Known true es) : Known u es := fun e he => lower_down (h e he)
def lanePlace (v : Nat) (upper : Nat) := 2^92*upper+v
def combineLanes {α : Type} (f : α → Bits) : List α → Nat
  | [] => 0
  | x::xs => lanePlace (f x).toNat (combineLanes f xs)
def units : Nat → Nat
  | 0 => 0
  | n+1 => lanePlace 1 (units n)
theorem laneSmall (x : Bits) : x.toNat < 2^92 :=
  lt_trans x.isLt (by decide +kernel)
theorem place_and (a b : Bits) (u v : Nat) :
    lanePlace a.toNat u &&& lanePlace b.toNat v = lanePlace (a &&& b).toNat (u &&& v) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [lanePlace,Nat.testBit_and,Nat.testBit_two_pow_mul_add _ (laneSmall _)]
  by_cases h : i<92 <;> simp only [h,ite_true,ite_false,BitVec.toNat_and,Nat.testBit_and]
theorem place_or (a b : Bits) (u v : Nat) :
    lanePlace a.toNat u ||| lanePlace b.toNat v = lanePlace (a ||| b).toNat (u ||| v) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [lanePlace,Nat.testBit_or,Nat.testBit_two_pow_mul_add _ (laneSmall _)]
  by_cases h : i<92 <;> simp only [h,ite_true,ite_false,BitVec.toNat_or,Nat.testBit_or]
theorem place_xor (a b : Bits) (u v : Nat) :
    lanePlace a.toNat u ^^^ lanePlace b.toNat v = lanePlace (a ^^^ b).toNat (u ^^^ v) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [lanePlace,Nat.testBit_xor,Nat.testBit_two_pow_mul_add _ (laneSmall _)]
  by_cases h : i<92 <;> simp only [h,ite_true,ite_false,BitVec.toNat_xor,Nat.testBit_xor]
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
def fullMarks (r packed : Nat) := ((packed+r) >>> 91) &&& r
theorem unit_bit (n i : Nat) (hi : i<n) : (units n).testBit (92*i) = true := by
  induction n generalizing i with
  | zero => omega
  | succ n ih =>
    rw [units,lanePlace,Nat.testBit_two_pow_mul_add _ (by decide +kernel : 1 < 2^92)]
    cases i with
    | zero => simp
    | succ i =>
      have di : 92*(i+1)-92=92*i := by omega
      have ge : ¬92*(i+1)<92 := by omega
      simp only [ge,ite_false,di]
      exact ih _ (by omega)
set_option maxRecDepth 8192 in
theorem guardBit (a : Bits) : (a.toNat+1).testBit 91 = (a==BitVec.allOnes 91) := by
  by_cases h : a=BitVec.allOnes 91
  · subst a
    decide +kernel
  · have lim := a.isLt
    have ne : a.toNat ≠ 2^91-1 := by
      intro eq
      apply h
      apply BitVec.eq_of_toNat_eq
      simpa only [BitVec.toNat_allOnes] using eq
    have lt : a.toNat+1<2^91 := by omega
    rw [Nat.testBit_eq_false_of_lt lt]
    exact (beq_eq_false_iff_ne.mpr h).symm
set_option maxRecDepth 8192 in
theorem mark_at {α} (f : α → Bits) (xs : List α) (i : Nat) (hi : i<xs.length) :
    (fullMarks (units xs.length) (combineLanes f xs)).testBit (92*i) =
      (f xs[i]==BitVec.allOnes 91) := by
  simp only [fullMarks,Nat.testBit_and,Nat.testBit_shiftRight,unit_bit _ _ hi,Bool.and_true]
  induction xs generalizing i with
  | nil => simp at hi
  | cons a xs ih =>
    simp only [combineLanes,List.length_cons,units,lanePlace]
    have sum (u v x : Nat) : 2^92*u+x+(2^92*v+1)=2^92*(u+v)+(x+1) := by omega
    rw [sum,Nat.testBit_two_pow_mul_add _ (show (f a).toNat+1<2^92 from by have := (f a).isLt; omega)]
    have hi' : i < xs.length+1 := hi
    cases i with
    | zero => simpa using guardBit (f a)
    | succ i =>
      have ge : ¬92*(i+1)+91<92 := by omega
      have di : 92*(i+1)+91-92=92*i+91 := by omega
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
    ((mask &&& 1 == 0) || f x) && onMarks f (mask >>> 92) xs
theorem marked_ok {α} (f : α → Bool) (mask : Nat) (xs : List α) (i : Nat) (hi : i<xs.length)
    (bitOn : mask.testBit (92*i)=true) (ok : onMarks f mask xs=true) : f xs[i]=true := by
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
      apply ih (mask:=mask >>> 92) (i:=i) (by simpa using hi) _ ok.2
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
def summarizePool (u : Bool) (ws : List Decor) (p : BoundPool) : QuickPool :=
  (p,ws.countP (fun w => isMaskedConstant p.domain w.1),
     ws.all (fun w => availableB u p.domain p.wires w.1))
def fastCost (s : QuickPool) (k : Nat) (a b : Decor) (op : Nat) (ka kb : Bool) :=
  if !s.2.2 then false else
  let p := s.1
  let const := fun w : Decor => isMaskedConstant p.domain w.1
  let z := choiceVal (movedChoice op a b)
  let zm := masked p.domain z
  let zc := isMaskedConstant p.domain z
  let cm := s.2.1 - constantLoss const a ka - constantLoss const b kb + zc.toNat
  let free := zc || zm==masked p.domain a.1 || zm==masked p.domain b.1
  decide (k+p.paid+(!free).toNat < p.bound+cm)
theorem fastCost_good {u p k ws a b op ka kb} (ha : a∈ws) (hb : b∈ws) (al : allowedB u op=true)
    (h : fastCost (summarizePool u ws p) k a b op ka kb=true) :
    scalarPoolCut u p k ((delTwo ws a b ka kb).map Prod.fst) (movedChoice op a b)=true := by
  let z := choiceVal (movedChoice op a b)
  let const := fun w : Decor => isMaskedConstant p.domain w.1
  let free := isMaskedConstant p.domain z || masked p.domain z==masked p.domain a.1 ||
      masked p.domain z==masked p.domain b.1
  let rest := delTwo ws a b ka kb
  have ck := keptCount const ws a b ka kb
  change ws.countP const - constantLoss const a ka - constantLoss const b kb ≤ rest.countP const at ck
  by_cases all : ws.all (fun w => availableB u p.domain p.wires w.1)=true
  · have hav := List.all_eq_true.mp all
    have ready : free=true → availableB u p.domain p.wires z=true := by
      intro f
      simp only [free,Bool.or_eq_true,beq_iff_eq] at f
      rcases f with (zc|za)|zb
      · simp only [availableB,isMaskedConstant,Bool.or_eq_true] at zc ⊢
        exact Or.inl (Or.inl zc)
      · rw [available_mask,za,←available_mask]
        exact hav _ ha
      · rw [available_mask,zb,←available_mask]
        exact hav _ hb
    have extra : (!availableB u p.domain p.wires z).toNat ≤ (!free).toNat := by
      cases hf : free <;> cases he : availableB u p.domain p.wires z <;> simp_all
    have hs : (rest.map Prod.fst).all (availableB u p.domain p.wires)=true := by
      apply List.all_eq_true.mpr
      intro _ hm
      obtain ⟨w,hw,rfl⟩ := List.mem_map.mp hm
      exact hav w ((keep_sub ws a b ka kb).subset hw)
    have opOK : choiceOK u p.domain p.wires (movedChoice op a b)=true := by
      simp [choiceOK,movedChoice,hav _ ha,hav _ hb,al]
    simp only [fastCost,summarizePool,all,Bool.not_true,Bool.false_eq_true,ite_false,decide_eq_true_eq] at h
    change k+p.paid+(!free).toNat < p.bound+(ws.countP const - constantLoss const a ka -
        constantLoss const b kb+(isMaskedConstant p.domain z).toNat) at h
    dsimp only [rest] at hs
    simp only [scalarPoolCut,hs,opOK,Bool.or_true,Bool.and_true,decide_eq_true_eq,List.countP_cons,
      List.countP_map,Function.comp_def]
    change k+p.paid+(!availableB u p.domain p.wires z).toNat <
      p.bound+(rest.countP const + if isMaskedConstant p.domain z then 1 else 0)
    cases hc : isMaskedConstant p.domain z <;> simp [hc] at h ⊢ <;> omega
  · simp [fastCost,summarizePool,all] at h
def quickAt (c : NodeContext) (i j op : Nat) (ka kb : Bool) :=
  let a := contextWire c i
  let b := contextWire c j
  (c.2.2.2.2.1.map (summarizePool c.2.2.2.1.2 c.2.2.1)).any (fun s => fastCost s (c.1-1) a b op ka kb)
theorem quickAt_good {c i j op ka kb} (hi : i<c.2.2.1.length) (hj : j<c.2.2.1.length) (al : allowedB c.2.2.2.1.2 op=true)
    (h : quickAt c i j op ka kb=true) : checkAt c i j op ka kb=true := by
  have mem (t) (ht : t<c.2.2.1.length) : contextWire c t ∈ c.2.2.1 := by
    simp [contextWire,List.getD_eq_getElem?_getD,ht]
  obtain ⟨_,hm,ok⟩ := List.any_eq_true.mp h
  obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hm
  have closed := fastCost_good (mem _ hi) (mem _ hj) al ok
  have cut : c.2.2.2.2.1.any (fun p => scalarPoolCut c.2.2.2.1.2 p (c.1-1)
      ((delTwo c.2.2.1 (contextWire c i) (contextWire c j) ka kb).map Prod.fst)
      (movedChoice op (contextWire c i) (contextWire c j)))=true :=
    List.any_eq_true.mpr ⟨p,hp,closed⟩
  simp only [checkAt,evalMove,closeChild,cut,Bool.or_true]
  repeat' split
  all_goals rfl
def flagged (c : NodeContext) (ka kb : Bool) :=
  (1+(c.2.1-(if ka then 0 else 1)-(if kb then 0 else 1))==c.1) && c.2.2.2.2.2.2
theorem flagged_sound {c i j op ka kb} (fast : flagged c ka kb=true) : checkAt c i j op ka kb=true := by
  rcases c with ⟨k,n,ws,cov,pools,links,flag⟩
  simp only [flagged,Bool.and_eq_true,beq_iff_eq] at fast
  simp [checkAt,evalMove,fast.1,fast.2]
def fallbackAt (c : NodeContext) (i j op : Nat) (ka kb : Bool) :=
  if flagged c ka kb then true else
  (if (i<c.2.2.1.length ∧ j<c.2.2.1.length) ∧ allowedB c.2.2.2.1.2 op=true then quickAt c i j op ka kb else false) ||
    checkAt c i j op ka kb
theorem fallback_sound {c i j op ka kb} (h : fallbackAt c i j op ka kb=true) :
    checkAt c i j op ka kb=true := by
  by_cases early : flagged c ka kb=true
  · exact flagged_sound early
  rw [fallbackAt,if_neg early] at h
  simp only [Bool.or_eq_true] at h
  rcases h with h | h
  · split at h
    next yes => exact quickAt_good yes.1.1 yes.1.2 yes.2 h
    next => contradiction
  · exact h
def batchMove (u : Bool) (b : Batch) (xs : List NodeContext) (i j op : Nat) (ka kb : Bool) :=
  let (k,n,r,_,cov) := b
  let len := 1+(n-(if ka then 0 else 1)-(if kb then 0 else 1))
  if len>k then true else if (len==k) && (xs.all (fun c : NodeContext => c.2.2.2.2.2.2)) then true else
    let a := laneWire b i
    let b' := laneWire b j
    let z := packedOp op a b'
    let mask := fullMarks r (takePacked cov (packedColumn (!u) a) (packedColumn (!u) b') ka kb ||| packedColumn (!u) z)
    onMarks (fun c => fallbackAt c i j op ka kb) mask xs
theorem batchMove_at {u} (k n) (xs : List NodeContext) {i j op : Nat} {ka kb}
    (hi : i<n) (hj : j<n) {q : Nat} (hq : q<xs.length)
    (budget : xs[q].1=k) (arity : xs[q].2.1=n) (mode : xs[q].2.2.2.1.2=u)
    (pass : batchMove u (makeBatch k n xs) xs i j op ka kb=true) :
    checkAt xs[q] i j op ka kb=true := by
  let len := 1+(n-(if ka then 0 else 1)-(if kb then 0 else 1))
  have eval : checkAt xs[q] i j op ka kb =
      if len>k then true else if (len==k) && xs[q].2.2.2.2.2.2 then true else if combField xs[q] (!u) ka kb op i j != BitVec.allOnes 91 then true
      else if !properB (dbin op (contextWire xs[q] i) (contextWire xs[q] j)).1 ||
        xs[q].2.2.1.any (fun v => v.1==(dbin op (contextWire xs[q] i) (contextWire xs[q] j)).1)
      then true else closeChild u xs[q].2.2.2.2.1 xs[q].2.2.2.2.2.1 (k-1)
        ((delTwo xs[q].2.2.1 (contextWire xs[q] i) (contextWire xs[q] j) ka kb).map Prod.fst)
        (movedChoice op (contextWire xs[q] i) (contextWire xs[q] j)) := by
    simp only [checkAt,evalMove,budget,arity,mode,len,combField] <;> rfl
  by_cases early : ((len==k) && xs[q].2.2.2.2.2.2)=true
  · by_cases tooLong : len>k <;> simp [eval,tooLong,early]
  have notAll : ((len==k) && (xs.all (fun c : NodeContext => c.2.2.2.2.2.2)))≠true := by
    intro all
    simp only [Bool.and_eq_true,List.all_eq_true] at all
    apply early
    simp only [Bool.and_eq_true]
    exact ⟨all.1,all.2 _ (List.getElem_mem hq)⟩
  by_cases small : len>k
  · simp [eval,small]
  · let r := units xs.length
    let a := laneWire (makeBatch k n xs) i
    let b := laneWire (makeBatch k n xs) j
    let cov := packedCov (fun c : NodeContext => c.2.2.2.1.1) xs
    change (if len>k then true else if (len==k) && (xs.all (fun c : NodeContext => c.2.2.2.2.2.2)) then true else onMarks _ (fullMarks r
       (takePacked cov (packedColumn (!u) a) (packedColumn (!u) b) ka kb |||
        packedColumn (!u) (packedOp op a b))) xs) = true at pass
    rw [if_neg small,if_neg notAll] at pass
    have ca : a = _ := laneWire_at k n xs hi
    have cb : b = _ := laneWire_at k n xs hj
    dsimp only [r,cov] at pass
    rw [ca,cb,packed_op,packed_column,packed_column,packed_column,takePacked_ok,lanes_or] at pass
    by_cases hit : combField xs[q] (!u) ka kb op i j = BitVec.allOnes 91
    · apply fallback_sound
      apply marked_ok _ _ _ q hq _ pass
      rw [mark_at _ _ _ hq]
      exact beq_iff_eq.mpr hit
    · rw [eval,if_neg small,if_neg early,if_pos (bne_iff_ne.mpr hit)]
def batchPair (u : Bool) (b : Batch) (xs : List NodeContext) (i j op : Nat) :=
  let f := batchMove u b xs i j op
  f false false && f true false && f false true && f true true
def batchRow (u : Bool) (b : Batch) (xs : List NodeContext) (i : Nat) (js : List Nat) :=
    js.all (fun j => (opsOf u).all (batchPair u b xs i j))
def batchRows (u : Bool) (b : Batch) (xs : List NodeContext) : List Nat → Bool
  | [] => true
  | i::js => batchRow u b xs i js && batchRows u b xs js
theorem batchRows_at {u} (k n) (xs : List NodeContext) {q : Nat} (hq : q<xs.length)
    (budget : xs[q].1=k) (arity : xs[q].2.1=n) (mode : xs[q].2.2.2.1.2=u) (js : List Nat)
    (bounds : ∀ j ∈ js, j<n) (allRows : batchRows u (makeBatch k n xs) xs js=true) :
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
    have check := @batchMove_at u k n xs i j op
    simp only [batchPair,Bool.and_eq_true] at pass
    simp only [testPair,Bool.and_eq_true]
    exact ⟨⟨⟨check hi hj' hq budget arity mode pass.1.1.1,check hi hj' hq budget arity mode pass.1.1.2⟩,
      check hi hj' hq budget arity mode pass.1.2⟩,check hi hj' hq budget arity mode pass.2⟩
def runBatch (u : Bool) (k n : Nat) (xs : List NodeContext) :=
    batchRows u (makeBatch k n xs) xs (List.range n)
theorem runBatch_at {u k n} {xs : List NodeContext} {q} (hq : q<xs.length)
    (hb : xs[q].1=k) (ha : xs[q].2.1=n) (hm : xs[q].2.2.2.1.2=u) (hn : xs[q].2.2.1.length=n)
    (pass : runBatch u k n xs=true) : testAll xs[q] xs[q].2.2.1=true := by
  have all := batchRows_at k n xs hq hb ha hm (List.range n) (fun _ => List.mem_range.mp) pass
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
  (k,ws.length,ws,preCov g.mode ws,rules,ls,wantsRetention g k i)
def prelim (T : Sig) (c : NodeContext) :=
  let ws := c.2.2.1.map Prod.fst
  decide ws.Nodup && !(ws.contains T)
theorem from_context (g : Forest) (k i : Nat) (valid : vettedRetention g k i=true)
    (h : (prelim (targetOf g) (contextOf g k i) &&
      (if k=0 then true else testAll (contextOf g k i) (contextOf g k i).2.2.1))=true) :
    nodeVerified g k i=true := by
  rw [nodeVerified,Bool.or_eq_true]
  apply Or.inr
  change (vettedRetention g k i && _) = true
  rw [Bool.and_eq_true]
  exact ⟨valid,h⟩
theorem makeBlock {g k start n} (h : ∀ (i : Nat), start ≤ i → i < start + n → nodeVerified g k i = true) :
    block g k start n=true := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [block,Bool.and_eq_true]
    exact ⟨h _ (by omega) (by omega),ih (fun i le lt => h i le (by omega))⟩
def cornerRange (g : Forest) (k start n : Nat) :=
  (List.range n).all (fun j => cornerOK g k (start+j))
theorem cornerRange_sound {g k start n} (all : cornerRange g k start n=true) :
    block g k start n=true := by
  apply makeBlock
  intro i low high
  have one := List.all_eq_true.mp all (i-start) (List.mem_range.mpr (by omega))
  rw [nodeVerified,Bool.or_eq_true]
  exact Or.inl (by simpa only [Nat.add_sub_of_le low] using one)
def contexts (g : Forest) (k start n : Nat) :=
  ((List.range n).map (start+·)).map (contextOf g k)
def header (g : Forest) (k start n ar : Nat) :=
  ((List.range n).all (fun j => vettedRetention g k (start+j))) &&
  (contexts g k start n).all (fun c => c.2.1==ar && prelim (targetOf g) c)
def rowCut (g : Forest) (k start n ar lo len : Nat) :=
  let xs := contexts g k start n
  let b := makeBatch k ar xs
  (List.range len).all (fun d =>
    let i := lo+d
    batchRow g.mode b xs i (List.range' (i+1) (ar-(i+1))))
theorem rowCut_at {g k start n ar lo len} (h : rowCut g k start n ar lo len=true)
    (i : Nat) (l : lo ≤ i) (r : i < lo+len) :
    batchRow g.mode (makeBatch k ar (contexts g k start n)) (contexts g k start n)
      i (List.range' (i+1) (ar-(i+1)))=true := by
  have ha := List.all_eq_true.mp h (i-lo) (List.mem_range.mpr (by omega))
  simpa only [Nat.add_sub_of_le l] using ha
theorem rowCut_merge {g k start n ar lo a b}
    (h : rowCut g k start n ar lo a=true) (t : rowCut g k start n ar (lo+a) b=true) :
    rowCut g k start n ar lo (a+b)=true := by
  apply List.all_eq_true.mpr
  intro j hj
  have jlt := List.mem_range.mp hj
  by_cases first : j<a
  · exact rowCut_at h (lo+j) (by omega) (by omega)
  · exact rowCut_at t (lo+j) (by omega) (by omega)
theorem cutsRun {g k start n ar} (h : rowCut g k start n ar 0 ar=true) :
    runBatch g.mode k ar (contexts g k start n)=true := by
  let xs := contexts g k start n
  have go (lo num : Nat) (eq : lo+num=ar) :
      batchRows g.mode (makeBatch k ar xs) xs (List.range' lo num)=true := by
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
  rw [header,Bool.and_eq_true] at hd
  have audit := List.all_eq_true.mp hd.1 (i-start) (List.mem_range.mpr (by omega))
  have valid : vettedRetention g k i=true := by simpa only [Nat.add_sub_of_le lo] using audit
  have one := List.all_eq_true.mp hd.2 _ hm
  simp only [Bool.and_eq_true,beq_iff_eq] at one
  have hb : xs[q].1=k := by rw [e]; rfl
  have ha : xs[q].2.1=ar := e ▸ one.1
  have hm : xs[q].2.2.2.1.2=g.mode := by rw [e]; rfl
  have hn : xs[q].2.2.1.length=ar := by rw [e]; exact one.1
  apply from_context _ _ _ valid
  rw [Bool.and_eq_true]
  refine ⟨one.2,?_⟩
  split
  · rfl
  · exact e ▸ runBatch_at hq hb ha hm hn (cutsRun h)
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
def rootB (m : Nat) : List Sig := vars m ++ [seed]
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
def splitPairs (l : List (Nat × Nat)) : List (Sig × Row × Row) :=
  l.map fun (i,r) => (inputs.getD i zero,Fin.ofNat 512 r,Fin.ofNat 512 (r ||| (1 <<< i)))
def splitOK (m : Nat) (l : List (Nat × Nat)) : Bool :=
  let xs := splitPairs l
  checkEssential (graphGoal m) (rootB m) xs && (xs.map Prod.fst == vars m) && properB (graphGoal m)
theorem strong_split {u} {m l} (ok : splitOK m l = true) {k : Nat} {S : Finset Sig}
    (h : Live u (graphGoal m) k S) (sub : ∀ v ∈ S, v ∈ rootB m) :
    S=(vars m).toFinset ∨ S=(rootB m).toFinset := by
  simp only [splitOK,Bool.and_eq_true,beq_iff_eq] at ok
  obtain ⟨⟨ess,alls⟩,_⟩ := ok
  have rest : ∀ v ∈ vars m, v ∈ S := by
    intro v hv
    rw [←alls] at hv
    obtain ⟨r,s,hd,hi⟩ := essential_ok ess v (List.mem_toFinset.mpr hv)
    exact raw_required h (rootB m) v sub r s hd hi
  by_cases hs : seed ∈ S
  · refine Or.inr ?_
    ext v
    rw [List.mem_toFinset]
    refine ⟨sub v,fun hv => ?_⟩
    rcases List.mem_append.mp hv with hv | hv
    · exact rest v hv
    · rwa [List.mem_singleton.mp hv]
  · refine Or.inl ?_
    ext v
    rw [List.mem_toFinset]
    refine ⟨fun hv => ?_,rest v⟩
    rcases List.mem_append.mp (sub v hv) with hv' | hv'
    · exact hv'
    · exact absurd (List.mem_singleton.mp hv' ▸ hv) hs
theorem strong_low {u} {m l cap} (ok : splitOK m l = true)
    (a : Impossible u (graphGoal m) cap (vars m).toFinset)
    (b : Impossible u (graphGoal m) cap (rootB m).toFinset) :
    Lower u (rootB m) (graphGoal m) (cap+1) := by
  have ok' := ok
  simp only [splitOK,Bool.and_eq_true,beq_iff_eq] at ok'
  intro p bank hr ha
  obtain ⟨k,S,hk,run,hs⟩ := reach_live (proper_of _ ok'.2) (essential_plain ok'.1.1).1 (essential_plain ok'.1.1).2 hr ha
  by_contra! small
  rcases strong_split ok run hs with e | e
  · exact a k (by omega) (e ▸ run)
  · exact b k (by omega) (e ▸ run)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low3 : Lower true (vars 3) (graphGoal 3) 1 := size_of (hints:=1) (by decide +kernel)
def known3 := extendKnown [] 1 [(12,[49,32])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid3 : Known true known3 := extendKnown_ok (m:=3) baseKnown low3 (by decide +kernel)
def g15d3 (i : Nat) : Nat := 0xf
def g15l3 : Packing := (1,0,1,0,0,0,0,g15d3)
def g15samples : Array (Bits × Bits) := #[(0x7ffffffffffffffffffffff,0x0),(0x7ffffffffffffffffffffff,0x7ffffffffffffffffffffff),(0x0,0x0),(0x0,0x0),(0,0),(0,0),(0,0),(0,0),(0,0)]
def g15columns : List ColumnInfo := []
def g15autos : List (List Nat) := [[],[48,33]]
def g15levels : Nat → Packing
  | 3 => g15l3
  | _ => emptyPacking
def g15index : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g15 : Forest := ⟨15,3,fun j => g15samples[j]?.getD (0,0),g15columns,g15autos,g15levels,g15index⟩
set_option maxHeartbeats 0 in
theorem geomg15 : graphValid g15 (boundsBefore known3) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=0) ?_⟩,listPieces_all (d:=0) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sg15_3_0 : block g15 3 0 1=true := by
  exact cornerRange_sound (by decide +kernel)
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
theorem low15 : Lower true (vars 15) (graphGoal 15) 4 := plain_low (hints:=8449) (by decide +kernel) (index_root (g:=g15) (i:=0) rfl rfl (before_sound known3 valid3) geomg15 tablesg15 (by decide +kernel))
def known15 := extendKnown known3 4 [(15,[]),(23,[64,48,32,16]),(27,[66,16]),(29,[50,65]),(30,[50,33,16,64]),(39,[80,64,48,32,16]),(57,[32,82,64,16]),(78,[96,80,64]),(83,[99,83,64,32,16]),(99,[48,96,83,64,32,16]),(135,[115,99,83,67]),(156,[112,96,48,50,33,81,64]),(163,[115,50,98,83,66,16]),(165,[114,33,97,82,50,65]),(166,[114,98,83,33,16,64]),(172,[114,50,99,48,33,81,64]),(177,[115,99,82,64,16]),(198,[115,96,83,64]),(270,[131,115,99,83,50,33,16,64]),(281,[131,115,99,50,82,65]),(291,[131,115,50,98,83,66,16]),(300,[130,114,98,49,32,81,64]),(305,[131,115,99,82,64,16]),(312,[130,114,49,98,81,64]),(323,[131,115,98,83,66]),(326,[131,115,98,83,32,64]),(330,[130,114,97,82,16,64]),(332,[130,50,115,98,49,32,81,64]),(344,[130,50,115,49,98,81,64]),(353,[130,33,113,99,82,65]),(354,[130,33,50,113,99,82,16,64]),(396,[48,128,115,96,50,33,81,64]),(420,[131,33,114,99,32,81,64]),(424,[129,33,115,48,98,81,64]),(480,[32,50,128,115,98,81,64])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid15 : Known true known15 := extendKnown_ok (m:=15) valid3 low15 (by decide +kernel)
def g31d6 (i : Nat) : Nat := 0x11a20bf
def g31l6 : Packing := (1,0,3,0,0,0,0,g31d6)
def g31h6 (i : Nat) : Nat := 0x30be670208000065000016357504004755c084
def g31d5 (i : Nat) : Nat := 0x40828fd20fd10
def g31l5 : Packing := (2,1,3,0,0,3,0,g31d5)
def g31h5 (i : Nat) : Nat := 0x300
def g31d4 (i : Nat) : Nat := 0x5dd4520
def g31l4 : Packing := (1,2,3,0,0,0,0,g31d4)
def g31samples : Array (Bits × Bits) := #[(0x5755d5755d5755d5755d575,0x16459164591645916459164),(0x2dab6adab6adab6adab6ada,0x292a4a92a4a92a4a92a4a92),(0x5ad6b5ad6b5ad6b5ad6b5ad,0x50d4350d4350d4350d4350d),(0x2769da769da769da769da76,0x2709c2709c2709c2709c270),(0x78be2f8be2f8be2f8be2f8b,0x48b22c8b22c8b22c8b22c8b),(0,0),(0,0),(0,0),(0,0)]
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
  exact cornerRange_sound (by decide +kernel)
theorem allg31_5 : block g31 5 0 2=true := sg31_5_0
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sg31_4_0 : block g31 4 0 1=true := by
  exact cornerRange_sound (by decide +kernel)
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
def known47 := extendKnown known31 5 [(47,[]),(61,[50,65]),(94,[101,50,33,16,64]),(157,[117,101,33,32,65,48]),(173,[113,97,82,32,65,48]),(181,[114,81,98,50,65]),(188,[114,83,48,33,97,64])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid47 : Known true known47 := extendKnown_ok (m:=47) valid31 low47 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low55 : Lower true (vars 55) (graphGoal 55) 5 := plain_low (hints:=257) (by decide +kernel) (cut_root (prior:=boundsBefore known47) (before_sound known47 valid47) (16,0,39,0,4) (by decide +kernel) (by decide +kernel))
def known55 := extendKnown known47 5 [(55,[]),(79,[101,50,33,16,64]),(376,[128,80,84,66,16,114,97,48])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid55 : Known true known55 := extendKnown_ok (m:=55) valid47 low55 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low63 : Lower true (vars 63) (graphGoal 63) 8 := plain_low (hints:=8449) (by decide +kernel) (cut_root (prior:=boundsBefore known55) (before_sound known55 valid55) (32,0,31,0,7) (by decide +kernel) (by decide +kernel))
def known63 := extendKnown known55 8 [(95,[101,66,16]),(159,[117,101,67,32]),(231,[83,82,114,99,66,16]),(335,[131,115,100,50,33,16,80]),(350,[132,116,84,48,33,96]),(359,[131,67,116,99,82,16]),(377,[128,81,67,112,97,32]),(462,[83,133,115,67,32,96]),(483,[83,80,132,115,96,32,16])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid63 : Known true known63 := extendKnown_ok (m:=63) valid55 low63 (by decide +kernel)
def g111d6 (i : Nat) : Nat := 0x7213f
def g111l6 : Packing := (1,0,2,0,0,0,0,g111d6)
def g111h6 (i : Nat) : Nat := 0x8000
def g111d5 (i : Nat) : Nat := 0x17e51
def g111l5 : Packing := (1,1,2,0,0,0,0,g111d5)
def g111samples : Array (Bits × Bits) := #[(0x5c1ee0f707b83dc1ee0f707,0x441e20f107883c41e20f107),(0x2b655b2ad956cab655b2ad9,0x2a21510a885442a21510a88),(0x14bca5e52f29794bca5e52f,0x109c84e427213909c84e427),(0x6ccb665b32d996ccb665b32,0x6c43621b10d886c43621b10),(0,0),(0x70f3879c3ce1e70f3879c3c,0x30e1870c3861c30e1870c38),(0x77c3be1df0ef877c3be1df0,0x55c2ae1570ab855c2ae1570),(0,0),(0,0)]
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
def known111 := extendKnown known63 7 [(111,[]),(123,[101,66,16]),(187,[117,80,66,96,16]),(190,[114,83,48,33,97,64]),(215,[115,83,67]),(222,[101,117,50,33,16,64]),(238,[83,114,99,33,16,64]),(243,[82,98,115,66,16]),(311,[131,115,99,67,82,16]),(318,[128,112,96,49,64]),(343,[131,115,83,67,98]),(349,[128,80,117,32,16,98,65,48]),(365,[129,113,82,65,48]),(378,[129,33,97,81,16,114,49,64]),(413,[134,117,33,32,65,48]),(427,[98,134,114,66,81]),(437,[134,81,114,50,65]),(455,[83,133,115,67,32,96]),(476,[82,50,133,98,49,32,113,64]),(485,[80,81,129,114,50,65,96]),(490,[81,33,80,128,97,114,49,64]),(497,[98,99,81,131,114,65]),(504,[49,50,83,48,130,113,64])]
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
def g189samples : Array (Bits × Bits) := #[(0x55a175685d5a175685d5a17,0x512134484d12134484d1213),(0,0),(0x71077c41df1077c41df1077,0x11036440d91036440d91036),(0x42dcb0b72c2dcb0b72c2dcb,0x40d49035240d49035240d49),(0x3e3a4f8e93e3a4f8e93e3a4,0x2e0a4b8292e0a4b8292e0a4),(0x8df8237e08df8237e08df8,0xde0037800de0037800de0),(0,0),(0x2f628bd8a2f628bd8a2f628,0x2e208b8822e208b8822e208),(0,0)]
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
  exact cornerRange_sound (by decide +kernel)
theorem allg189_6 : block g189 6 0 2=true := sg189_6_0
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sg189_5_0 : block g189 5 0 1=true := by
  exact cornerRange_sound (by decide +kernel)
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
def known127 := extendKnown known189 9 [(127,[]),(223,[117,67,32]),(239,[116,83,32]),(478,[99,132,84,48,33,112]),(508,[48,84,100,49,129,112])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid127 : Known true known127 := extendKnown_ok (m:=127) valid189 low127 (by decide +kernel)
def g191d10 (i : Nat) : Nat := 0x8201ff
def g191l10 : Packing := (1,0,5,0,0,0,0,g191d10)
def g191h10 (i : Nat) : Nat := 0x99090000b500000001a152f05d5c000e4006080015749fa60141c73802b0a68137976081bca199eaaa3d961388c0f3a0002328c00084a05000089c2a
def g191d9 (i : Nat) : Nat := 0x288616180c48a1166c008c818588a2e004e68c2c214019ce1852e22410102944c300431c508936018138408051218b0c0328614b0a030139610c0803944862a8614888704038c28424018278d600745a25b53e43cce27c5e0bc00ff483fe30ff4c3fd10ff54ffe10ff903fe20ff4c7fc20ff58ffd40
def g191l9 : Packing := (12,1,5,0,0,10,0,g191d9)
def g191h9 (i : Nat) : Nat := 0x140000000000000198cb0000a04e08a520001a51c20000531e80b64388d00078963d80a7524800343b41a670800007a7cc632d75239502d607286400000000060840000002a100028a67e35dbbd50001a6c315cd7a0d113ac27000121800052568158594ec000682af90000f6880000010b6fab800321ac31374a97c0018068243a2b09f06ef8c8000c984c7fad8000732e29d36fd3c9ba4660000003c50a43a2e72f0000037c5c484413000060966343d567081fd24000161fd8fb857db1616c2d70bc0001da504981c000a8cb68709baa54393350153817e93b2ee08a0b35c971e4812648c40cf0c890074a5b901b85c19b060f0f30f9c6d46f822909e468ae58b600010460007b00142a8dc0d2c800031c60005ad28d4a60000000000000046100000000000000005978000750c07fc419a5a33000612dc38451b04000033fe570000002d76000244c429f180a5d34b0ba1360001a731afd48a565b2f860060014b1d8111aaaac600056d800000000026c2da68678cd5b803ae00010d91906c6000000173ec82c4200058c80000000001b509c9847ce37e90001c466a9e954000000c99484d7ca82a800f93447182024f80000c48dc000596030083ad05a1c75006c10817410814060062c35820051841c00801071c96460c20000020c70c01c908b0c0000080000041016
def g191d8 (i : Nat) : Nat := 0x29041122ca0d10c1820e2c410001141c82c503187102c6803c1124102c4286221684a403891a1842c51018c10e162422c50c48b4430a88388165811860b20b1820c885832094438592320063450060d08b10b180c70058c1900e2022c1a5209182101c43050318240243908070c3401c48f00c068888850b06303893850c08507122ce9438b1828486848141c49306545830c58c50e24583241123461c483184422438d145120600b2021630704107122ca0450b1891c2020848b2091a24b1851630a0e2c4e0c2892183831688b8058c1a6022c6104c00e4880838a18100084071660e244249870640e24594065442458c0090e3142c41c48e18c4c045890e3ce143811444a1c58a1308c183a1164c42058c4c2022859400f123080808c4a28a0048b18c1624c24381180210b4051306022161ce1858a1930e0c61c00d160ca0458a1c1121c19010712845940a0160c4941400e4881c482223108b38718245905810e24196007163140c48060a1240e251001628c306c54c090413820e260901871630c3c38c2458d8309030a1a24597160142c98f02998bd87a29983922b8057d178f7697196e56a367d6576235ef59f55d5374f532f3974b229947f44b4253f13bd39735532f3092d529329325f25e6e722a6e71e917d111097046ff6fb4f80f3eeeeeace78e28df4dced8cd66d40cb8c68c34bf2bb0514b7cb1eaf8ab6a66a322989fe9d86e69a49388f68988568227d279074070c6e666c6005cc5985485144d24d24824323f03843422f22be2982561f818c14a1160d4092042001ff54930ffaa0a07fd71483feb1c21ff50120ffcc5207fd52503fe98221ff58e20ffac0987fd1058ffeb9a41ff58640ffa60907fd72443fe882a7ff50910ffee2907fd2058ffe98c41ff54131ffa20907fd21903feb1281ff48153ffa42a07fe72443fe90c41ffdcd20ffa65087fd32883feb0c61ff8ca10ffa43187fd2158ffeb9a21ff54931ffac098ffd62903feb1461ff58931ffac0a07fd204c7fa38a417f5c520bfae5107f920842ffb9281fddc520ff221105fd75902feb88417fdd110fba60b1fdd324c6feb94617f5ce10bfee0a9dfd7054efebac61fdc8610bfee2907f910482ffb9263fd48531bfee2b1fbf744c2ffbb2617f5c163bfaed185ff71502ffb92217f5c553bfae9105fd76902feb9c417f5cc20bfee2a9dff704c7dea14817f5ca10ff260905ff7258fee982637fdd531fea63087dd3054efeb92637f5c131bfae2b1dff724c2ffbb2817fdcd10ff261105fd718c2feb8c817fdcd20bfeeaa05ff7058efeb9a41fe48230bfae3107dd3258efeba4217fdd530bfee2987f5514c6feb94817f5c963bfeec98df771482eeb9c416fdd130
def g191l8 : Packing := (113,2,5,0,0,12,0,g191d8)
def g191h8 (i : Nat) : Nat := 0x38d5055793c3679268754bc6188000001bef920589c626a6500070140c8d5de5f1d7a21d0344d98ee800183ee488000001119701a189f7ac18d073c41c5a460f2f6dbb0d3e90a06b82f5bcc02928e3aa852e880000109c34616429775d57a00841de8968c753cd4f7779436ba625de899899071c11166c07285d4158b1c40cba3819701ff1ed4e0000001d75e386545f25c03c4e3ccfe7905e2217770000000a100005011f8991186d800000144100008f313025a433c0cd88dae660be94000121c0000002c88000000655b0af52342fd8c3fbe11d039049a5a1e7325180004d4e9a308f4f4000000ef1802b07e014cea170acb800000009b4c4008e61bc79a059a0f70fccb137f85b2554dc0000000f21e93d1260001258003490000000000283ab340000000b1c0000000003185023a5319608aa0001913478000000000000000046621400000000000005b0dc8e000000426e6c726f99d415a6c3045000127023e070c8d80b889403631ef964fdd2196b35879ca860c0656093c9b66e604e1a08c20003c8494d7228964094caf59a8139a149ac000c151050440002c01002420821110471482078810951470800420470000020001001c02830c50400010400800405400402040000c00080070800c100000d0040151000c0040141188000004000
def g191d7 (i : Nat) : Nat := 0x8c1c20910608042054220a8110405882c4181082510650898021418109284883401030a0842c2041626109020848e8420410c03103842420006d00a8d000011a8d1a00069a70000000000023724001a61400346ddc06800ada351ab4a70027200000d0008d004b000000045c0000004080a000000082e80000000f54d0000000093a1b6ce00000000060ad11a00000011a340029c009a46904000000048f0050280000003593882000010468000000000000007c2405000000000df4815ca209fd879c9109fd82dc163df5215c620aff8654931ff38148230fe92054930df7715c5209fd82dd530b7f8558140bf7815c520bbf844c1209ff815c163df771501209ff815c1539fd81dc163fe92048630df920dc530ff210dc5209fd825c640f755154131bf78148131df7815ca10df7815ca40ddf714c163bf7815cd209fd8798a409ff815ca20fd5514c131df97244220bf9809c910dbf74549309ff805c5639fd81dd930ded20dc963cfd764c620df4815ca40bf9808ca10b7f85581319fd82dc530df9205c630ff210481319fd80dc5539fd81dd530bbd849c910bf58158e109ff805c963aff8654940ddf714c963df7715cd209fd80dd9319fd82dc563df551dc131ddd215ce20df7714c120fe92050910df5315ca10df783dc5209fd825c630ded52dc931dbd425d640df610dd9319ff815cd20bf78148163df5515c1319fd82dc540ddf764c1319fd878ca109fd81dcd209fd80dc5639ff815ca40dbd54dc940ff110dc520dbf7458130ded215ca30df5615d210bbf844c110ff081482309fd82dd1109fd82dd540df471dcd20df77144120bbf845cd20dbd425c640bf7814ca10ff3714c120bdf8350910bf78148153df7215d210bf78158131fe52048531bf78154131ded7248640cfd764ca209ff815c963bbf845cd10df583dc520edd6358130df4715cd20df771dcd20ddf714c153ff0714c120fd5314ca109f7815c5209f7815cd209bf845c1539ef825c5639bf845c1639bf845ce10fe120c861097f855da408fd86dd5319bf845cd209bf845c1319f7815ca409f581dc163
def g191l7 : Packing := (116,3,5,0,0,9,0,g191d7)
def g191h7 (i : Nat) : Nat := 0x30450ac641c0062400b2c00a0c8100000001c50000042a883a
def g191d6 (i : Nat) : Nat := 0x8fb4c102b944193f85dd1604c23ef22c16eaa062fe1b7454930cdbc26e2982411f79161e6290336f0838ae69056de5183dc5208fb4c0e2b9a419b784dc5734823ef22c16ea9847de4582dd110
def g191l6 : Packing := (12,4,5,0,0,0,0,g191d6)
def g191samples : Array (Bits × Bits) := #[(0x7e74c90f46d703f3a6487a3,0x7852498306d113c2924c183),(0x17cddc86132844be6ee4309,0x78994041128003c4ca0208),(0x486704a6f0f3de433825378,0x40666080c053c6033304060),(0x3a8a3b68314ca1d451db418,0x3b801b49310401dc00da498),(0x441db73c882a2e20edb9e44,0x40da434c82a2c206d21a64),(0x25a822515d25c12d41128ae,0x52822405924c029411202c),(0,0),(0x13809557a998389c04aabd4,0x12819117208838940c88b90),(0,0)]
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
  refine @block_merge g191 8 70 4 32 ?_ ?_
  · exact cornerRange_sound (by decide +kernel)
  · refine @block_merge g191 8 74 1 31 ?_ ?_
    · apply cellsBlock (ar:=9) (rows:=0) (d:=0)
      simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
      repeat' apply And.intro
      all_goals decide +kernel
    · refine @block_merge g191 8 75 13 18 ?_ ?_
      · exact cornerRange_sound (by decide +kernel)
      · refine @block_merge g191 8 88 2 16 ?_ ?_
        · apply cellsBlock (ar:=9) (rows:=0) (d:=0)
          simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
          repeat' apply And.intro
          all_goals decide +kernel
        · refine @block_merge g191 8 90 4 12 ?_ ?_
          · exact cornerRange_sound (by decide +kernel)
          · refine @block_merge g191 8 94 1 11 ?_ ?_
            · apply cellsBlock (ar:=9) (rows:=0) (d:=0)
              simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
              repeat' apply And.intro
              all_goals decide +kernel
            · refine @block_merge g191 8 95 7 4 ?_ ?_
              · exact cornerRange_sound (by decide +kernel)
              · refine @block_merge g191 8 102 1 3 ?_ ?_
                · apply cellsBlock (ar:=9) (rows:=0) (d:=0)
                  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
                  repeat' apply And.intro
                  all_goals decide +kernel
                · refine @block_merge g191 8 103 1 2 ?_ ?_
                  · exact cornerRange_sound (by decide +kernel)
                  · refine @block_merge g191 8 104 1 1 ?_ ?_
                    · apply cellsBlock (ar:=9) (rows:=0) (d:=0)
                      simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
                      repeat' apply And.intro
                      all_goals decide +kernel
                    · exact cornerRange_sound (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sg191_8_106 : block g191 8 106 7=true := by
  refine @block_merge g191 8 106 1 6 ?_ ?_
  · exact cornerRange_sound (by decide +kernel)
  · refine @block_merge g191 8 107 1 5 ?_ ?_
    · apply cellsBlock (ar:=9) (rows:=0) (d:=0)
      simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
      repeat' apply And.intro
      all_goals decide +kernel
    · refine @block_merge g191 8 108 1 4 ?_ ?_
      · exact cornerRange_sound (by decide +kernel)
      · refine @block_merge g191 8 109 1 3 ?_ ?_
        · apply cellsBlock (ar:=9) (rows:=0) (d:=0)
          simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
          repeat' apply And.intro
          all_goals decide +kernel
        · refine @block_merge g191 8 110 2 1 ?_ ?_
          · exact cornerRange_sound (by decide +kernel)
          · apply cellsBlock (ar:=9) (rows:=0) (d:=0)
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
  exact cornerRange_sound (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sg191_7_49 : block g191 7 49 36=true := by
  refine @block_merge g191 7 49 21 15 ?_ ?_
  · exact cornerRange_sound (by decide +kernel)
  · refine @block_merge g191 7 70 1 14 ?_ ?_
    · apply cellsBlock (ar:=8) (rows:=0) (d:=0)
      simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
      repeat' apply And.intro
      all_goals decide +kernel
    · exact cornerRange_sound (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sg191_7_85 : block g191 7 85 31=true := by
  refine @block_merge g191 7 85 24 7 ?_ ?_
  · exact cornerRange_sound (by decide +kernel)
  · refine @block_merge g191 7 109 1 6 ?_ ?_
    · apply cellsBlock (ar:=8) (rows:=0) (d:=0)
      simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
      repeat' apply And.intro
      all_goals decide +kernel
    · exact cornerRange_sound (by decide +kernel)
theorem allg191_7 : block g191 7 0 116=true := (@block_merge g191 7 0 85 31 (@block_merge g191 7 0 49 36 (@block_merge g191 7 0 13 36 sg191_7_0 sg191_7_13) sg191_7_49) sg191_7_85)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sg191_6_0 : block g191 6 0 12=true := by
  exact cornerRange_sound (by decide +kernel)
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
def known191 := extendKnown known127 11 [(191,[]),(319,[135,50,65]),(351,[133,117,101,33,48]),(367,[128,16,64,100,80,113,33,48]),(379,[130,50,81,115,98,65]),(445,[129,82,97,48]),(487,[115,83,82,130,99,66,16]),(494,[64,132,49,96])]
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
def known255 := extendKnown known251 12 [(255,[]),(479,[118,133,33,48]),(503,[115,82,98,131,66,16]),(507,[99,81,115,130,65]),(509,[82,129,48]),(510,[100,49,128])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid255 : Known true known255 := extendKnown_ok (m:=255) valid251 low255 (by decide +kernel)
def g383d12 (i : Nat) : Nat := 0x1840804ff
def g383l12 : Packing := (1,0,6,0,0,0,0,g383d12)
def g383h12 (i : Nat) : Nat := 0x2e190000e44028954b00129713b90021c5c400a24a286e030000000000d800006790000005048cec0c584c000029410000109
def g383d11 (i : Nat) : Nat := 0x1c1800c080840a80c160880850c1604287044044070d0e04282102a03050f061043070d0a08508680361365e17803fe087fc30ffa61ff443ff187fe10
def g383l11 : Packing := (6,1,6,0,0,9,0,g383d11)
def g383h11 (i : Nat) : Nat := 0x605ec8c0000001117d3d8e632bfc434126a560a0c97cd1c2e0006879dce0130002029832241d31f89848e70800000000019dd990a81d83401050198b41ca520a2f40adbada290270002212000f0240555b3c62d0c010b44640b0000000000a02000000274e000193000140ac0e19590854ad62490de02102d21d6156142944000d8a4082dc48550007f7944400014100014220513068000058000991281875380f661504984eda4b2e787cc39625232a002653d245061c2fea2000000680400000024e94b1850b1ad217010100600b00017050301c050070e260404451400410
def g383d10 (i : Nat) : Nat := 0x2e1d841e238187821614a130f09110b0a4647c0c3c2c18584708850c6160840207a04c442860211d1a16112300a10082e1c613110b0a854746c2c18450988a30282238785a1041c141914442a102d2088a12224460a05c2c108040f40583c282820b0a1c4c45191c4824c230c8c080b82901e8c30705040d0e361a2878510342c181c14442810482548c140e0b081664205840b0a288858242a3038a6087241610242880a1187821e14641060587110b302838984902d191c284824c230c8c0e201c167464204470a090f0b46183a30206a2871d0832102c28a861e0f818409821c149061607c10ac2110440306e0e161e00585201a1f0427082c10e0c140a08406050d0ac1080438303848582821818242f042010c0e0b8423821408711c2060407c3c0c10a0f50303826061e086e1058728151c18370b04281100c080b87828f85801412a07050418804020c561f04108080a20504121e003e160821aa5a88677263e56a4163021ce13a025f31e5dd49c75be1a8d9b99057d173d66959550142d33922513107cf48e34d20c2cb98aa49d08fc8086b456044c2f828421017c1280d4003ff5c530ffd73443ff5c130ffd73043ff1cc10ffd73843ffa0d10ffd718c3ff9c430ffd30443ff1ce10ffc83443ffcc110fff814c3ffa0530ffe718c3ff4c610ffd318c3ff9ce10ffe318c3ff60530ffd710c3ff1c430fff83443ffcc610ffd83443ff20530fff718c3efe1130ff9708c2ff60d10bfd818c2ff60c10bfd838c2ff60610bfd810c2ff61e30ff9704c2ffe0530bfd83842ffe0d10bde83042bf61830bed828c2fb60810bdd83042efe1130
def g383l10 : Packing := (47,2,6,0,0,12,0,g383d10)
def g383h10 (i : Nat) : Nat := 0x71198115833604b01a0000606e88fc000242d7c1fb0faad280000000907200000000000000000011a60000c095e07a03c80000000207200b0000f0374218000083d74340000000000010fe000191d800038c8000000000050001a19c0000000f0d80002417105f0001002bc08ec1b0001e12c0000000f0e7e92d81a6801000081e2997c07b60460002f86e047b093591c0b42863642440b4814a40900000001016701f80992cbb0308000c10b416439d943b147aae0000000140000000051cc437e4b4604d43368120000516302b9f1000004067d0c8043000061b56b100000c580000000783f104c0003fbb80009070d07382c4f54000000014a410460001715080ea8740833a5880002404721a41d7010e870e0a6000041e7802d68a0000000000000016605c32d9336823a9a000d7e20d86d416e10a400828f5440c813b83e60a220d8fa1581020e4099e8197842301210c9aa808357404e01fd304041e1023c6482e6b2cf063e21e71a6056370a003201825400056b139c293c35f0f8311d9031132ca772115827b06218a0203561cf86910f5a5f4b8b233b382b58ee49dec3300d7802d8c0502fd10109b0c0a907ee0a0fc274022d3a10d5060b108505d001d3c31732301838cca1790204071480aad97c1b8000509cd0a402a9482901e3171c30000064ac78e80004854e040ddec841106f32a0420d715820cb2810092535383b24a5005e83218280109ecf40006a47e0540003c1d6c17800c84f7001b077b0900001c268000e088000143b221e2f0000390d00040c17340800211f04000c3852005c082b04030102880201024c3d0e17000f0511410100573e04001200070500016400040b010407000d00010204010004000a010e07000000003720
def g383d9 (i : Nat) : Nat := (if i<1 then 0x5c2e083ca040c82c60f0a0a8a0a078c1e0b102c382e18141e0b05143684058448130891c1e0b28448e13e08641e68382b080b205c2c0a181414191f08220f1817080b05100a17058c081a0c8c160a1041080b0890220a14101e2a30128a0e230b820f0510240a048f81c10782c145e083b0a0a0214100fe0828085f51f3af08ee8ebfea8e88e5fadb11fe36e1fe08adbe1fadbe08dd6db6d84d3bd52d3bd24d04cdbcb2c92c72c49c29c09450bf2bd2b699a9bbbb929c9adbb69b29b49b29b12af2adbab215f11fa92a72a5ba3ba1b5309e99c99a99929609379178e58c589c3e788585c84582e8177ee7c533079c77c75c72a70a37e6d86b842767d65d63d61d5e25cb5995704d95475305074f03e74d94b94904704504274073e73b537e39537e37e35e3473302fe2d52a326823f21f1ff1df1b619617615f13611f1080df0b6096064032000dfeb8b07186ff60573843f7f08b8a61bfc7360610bfecb902986ff606738437fb0fc1a21bff874c110bffcbb06885ffe5d304437fb0e98c217fd9720d10bffcba63085ff65f30442ffb2fc1a217fd97a0d10bfecbe63084ff66173443bf2e1b8c613fd981cc109fe4c2e6884ffe61730427fb30388613fc985c530ddfca307184ffe45878c27fb30b9821bed828c6309ffcbb06085fbe4983442efb2a40a61fd9315c130deec1a63085fe64073842dff2cb88613fd985c130dfb38b02187dee55708c27fb2fc0a61bf581e0530def41f06884ff66173842f7f28c0a61bf57160430bdeca502986f7e0f304427fb3039c21afd91618309fecc6e3185fee41318c27ff2ec1a21bee7360810ddfca307085fee41318437bb2ec18217df935c1309ffcbb07086ef247844c37bb07c1a2177d959c430bfcc8463186fb60a718c27fb3138c61bdd835cc10bfcc80e6084ffa61734427fd30b8a613ff9760630df6cbb05185bf65b318437dd22c1461fd8935c130df6c8b05186f725d830437dae6c10213ff985c630df6c10e6086fbdcd82042feb2398221bed825c630ddf48f08986efe47844c377f08c0a617f5911ce10fddc22e0986efe11704c35fb0cb8861bed9360a30bdeca0e2186efe11714c37f730b84616ff965c630df6c16e3186fda07814c35fb0d38861bdf9760c10bf7c9302986f760c834427fb3138861bf581205309fecc4e7084ff65d810c27ff30b9c217f990dc630dfcc1ae1186fd605318c27ff2ec08617bf944c110ddfc2702985fee41834427fb3198c21bdd83cc610ddfc2502985fe643318435fd22c3061bef9260d109fecc2e3185df65683442efb2b982217ef924c610def4bb06086fb609318c3fb662b82617ef924c6309ffcc2e2186fba5d828c3faa63c0a619fd875c6309fecbf06886f7e0d3044377f0840a61bbd91e11309fecc463184fbe498344277f28c1c213bf9460e30 else 0x39830408828a13050a820f420381450788c163e18282e11201c14209a150830702a08112415081608901609103c082028101e0b0514160a0b0c0a080205c1c502828082509942609105c1c2020281c3058142c0a203c161105110809050c080a088e8e0a0782c9c3078387c10782860f0b0b0811058c221a10938411079022040503c9040882c6040508460b07880e0e078c120b10142c0b05118c0e0c8c080f070c140b1416080a18101e0a181c140462838a0405828645048446090508160a0208c3250484414122215080a182830080b83ca110502460f0282c1c405064411c3038164058884110788240b10102d050510422082414805020382e4638682e308c10163a0828328405958a0a078c3f42e083c14523038163e101f820a0203cc100585c6080a028605098247c0e103b820f0518261114180a11c202ca15ac02816402114121120281c2e1f04140f211c1620503c4040702861b820441640f04c1e34202c143e081c140f2210140b182422121c741)
def g383l9 : Packing := (136,3,6,0,0,12,0,g383d9)
def g383h9 (i : Nat) : Nat := 0xa16f054972c28000915083d009e0b000184b4aa00070df9a0000000103800000000040895c7d1f430452c83b41000000066c401a931403589000181590e60c4006e970739878c268f4319a8a1e8a227410f80515a000677800202f029915b907440e6c7f8b08b068a9c416408c84be1fb32f040001432000000000000000000001daa0990d58b4800e1d917e01640581811720991cb65f653999ed0240cf0c80400004d08a6610820084081054000400010000a42100804
def g383d8 (i : Nat) : Nat := 0xa102e08584082e10440a10161614242040a06448204190800f08141cd1e1e1e1ebeaf1e69a0871e1e231e1e1e781e0f1e691e1e1e1e1e1e1e001e1e1e1e1e1e1e001e0f1e5a4132001e00231e1e1e0f00dafe5b845c530cefe1f944c110aef69c91e1130afb68f7360810cefe119720530cef5c79460e30cfb61f924c610adfe9587e0d10cef5c79460e10cdb655821cc10f745c5315c1308fdea581205308efe91985c1308fb689981cc10caf619941c4308fbe89985cd108bf69a985c530afa6829760a30cafe5b845c530ccfe119520530cdb655829c630cfa609901cc10cebe539260d10aebe8991e1130af66809760c10cbbe59825c6308fb68b9161e308efe91989ce108bfe999760430af36889760c10ceb651828c6308efe91985ce108fb6a582dc6308bfe9b985c4308bfe99985c630c9f655869c430cebe139260530ad76949760c108bf6a3965c430acf69491e11308f7ea58320d10cfa609908c630af9a869760a30add6967160430aeb6929760a30af96869760a308ef6a784a0530ceb651821cc108dfe9597e0530aebe919360a30ccfe57845c130cee611901cc108fb6a3924c630
def g383l8 : Packing := (53,4,6,0,0,8,0,g383d8)
def g383h8 (i : Nat) : Nat := 0x834601a000
def g383d7 (i : Nat) : Nat := 0x295fdb2e3ca3070852bfb65c79460e30
def g383l7 : Packing := (2,5,6,0,0,0,0,g383d7)
def g383samples : Array (Bits × Bits) := #[(0x290f52c7a90e534699487a9,0x80e52c6810802028040729),(0x73608f305f68dea8d39b047,0x716089101e10d500678b044),(0x4010edec20450a195a00876,0x1004ec204502991800802),(0x684e0179bace53b2434270,0x784e001db288126043c270),(0x43701b834871841bc21b80,0x310138248718413801880),(0x18880019d670119c0cc4400,0x18000115670119c0c0c000),(0x6f01045c32520b69837808,0x4900045c16420b69824800),(0,0),(0x78b011ea2493ae222bc5808,0x382011aa20830e4161c1008)]
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
  refine @block_merge g383 9 119 14 3 ?_ ?_
  · exact cornerRange_sound (by decide +kernel)
  · apply cellsBlock (ar:=10) (rows:=0) (d:=0)
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
  exact cornerRange_sound (by decide +kernel)
theorem allg383_8 : block g383 8 0 53=true := (@block_merge g383 8 0 44 9 (@block_merge g383 8 0 36 8 sg383_8_0 sg383_8_36) sg383_8_44)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sg383_7_0 : block g383 7 0 2=true := by
  exact cornerRange_sound (by decide +kernel)
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
def xud13 (i : Nat) : Nat := 0x110f0d0b08070502009ffd30
def xul13 : Packing := (1,1,7,0,0,0,0,xud13)
def xuh13 (i : Nat) : Nat := 0x603511000718f15175000a06672412001000766b71408d13d02b65e04c63a61062000000000000d172738053002071800d9980b
def xud12 (i : Nat) : Nat := 0x40592d0844c03098708e05270f60541184c343e009244851210044230f8680225170f07281d00068330f86c0e2c1489042c0182c261f2781c4821000c16101193c4a4a1e8046130f8680227030f08a70f86c2605120836081e00c261f2781c482134f490f4b029a1ce488ac007ff60530ffe90a61ffd514c3ffb22987efe5130ffc902617fd914c2fff22985efe5130
def xul12 : Packing := (9,2,7,0,0,10,0,xud12)
def xuh12 (i : Nat) : Nat := 0x1e0e5c5a0820865e4113812d88ab840e148c0f6034000000000004b18d2930127592a019d02f025c01fcc260001033c0000000e03a0000000501f0000a0f246188ada0056c11c9a733120976041852903e101402e119d6917e02cc13c02a180ed00b20bb426c0032119cc59c4a80003026e11f004b8431085602d81200000001a543c06800000008102024000097406498000204ab04200000007046100020a001eb9b8000000000000000e69ce42ac1388310052200409073c1666c00e040400000001806a80a2b0b27a14104c1553960001c0bd428fb95374cd48359c208bc0a7e063011b04c0000000000015b8701f0049c0ae030607620dcdc5a8045605c15681980000000208841680002039c04602700008191aec501a900ce00d5541016201b276c0000000000000001498453e0aae62a000201d48070767a0cbda878d1d12c814041b234f516640ac0000326027e8d0c822a82654103000620000001210001001060010e0090004000021300201222001030010104003000201007010039100000000001220000000200340090000060004060095000010000000011
def xud11 (i : Nat) : Nat := (if i<1 then 0x1c6618270b02106c1c32001220f448140da100e2300079860281428220684d4481407181e0440d0980a038c922100d5080a0460b014c960144ad000890803a9261a89c3d18030807028407b0061c0a050a8c8280d8c1dc3d8606c1c2834840294301cc951387a3000458403814281a08a00040140718340370fa1821e0700a240a03940685a0eb178051207014806b8603a896481f06c084709c970c08f034481a070149047810aa890200e0282947250070d07b1304316072196e4b8483e0061b81821894b08c332408f02c48100701496118664b810700a62408440015035493120681407202a0680dc3c32a4b00a240a039500063c1034c252406814072422e0421e4a890ac083e000e85187d12c582870370fa242ec0018040e0f2000d51206814c901c80501903b8664a8906c084011c270d07c00c93120a2014e4d9203808290c8012dc921144e1e1581c98000864c14c3e9208c0a461f44843c0e0015b260a23810aa890200e0282938440ef0ec5d12140107e0b810201a0280e094fc32104903544e1e0d81c840386e1d08a268bc3c0e402087d0944e00070147c3c19e1289c001864817470fc3709c0d12069aeeb73eb83da7aca75f4ad4d57aa3b3d8a64526e8b54059ec4e366c13339654a764b90c7917c7ba36f17689fc3d218f086827c039f9af78796bbb1d42e7471eb819b76d7a69cb39195ac6c615aee16c6b3657fab7154aa5050ca7612de91a462a1990227bc3ae9bf8d526542f59630a824f625591588023ac1ba8c5858226c11087583161360708258082000fff549814c3ffd8254530fff615214c3ffda960530fff689514c3ffd9260530fff655214c3ffda548530dff6a5514c2fffa954530ffe481914c37fea954530dff6a5814c2fffa254530bffea5214c37fda264530dff6a5214c3ffba848130dff655214c3ff9a148130ff754d914c3ffba148130dffaa5814c2ffda948530bffe89914c37fd9264530ff768d514c2fffa548530ffee95204c37fd52e4530bff695914c37fd8264530dff655914c3fbd81e5130dff617914c37fda564530dff60b914c37ffa864530fef547944c37fda864530fef487944c3ffba054530ffe695204c3ff92054530bffea1914c37fd9864530ffe601914c37fd9260530ffe601214c37ffa564530dffe89914c37fea948530ffe6a1204c3ff92060530bffe95914c3ffba0645309ff6a5814c27fda564530dfe483914c37bfa464530dfee81914c37bd51e5130def607944c37bd91e5130def687944c3fd931481309ff6a5214c3fd953481309ff6a3914c27ffa5645309ffea5514c37f920645309ff68b914c37bd21e5130fee483944c3bf98060530bfeea1204c27ffa864530bfee81914c27fda5e4530ff6e8d204c3fe92048530bfee81514c2fdda3545309ffe89914c27bfa464530 else 0x1212861664a89c0096821084e01042100501c585519c0022050a1c16e1121a0a1121b03e07210a28700420140b41f070e9221a05113800340a21007240ac002249c144340e39420db021001c0d03e7c3c08c001f0a00e30540d01a801240401407210f0200e0a081a01008d12198466c1b00029920200e0b41c401b8001407102a03592c001a0380a3a00040280d93840d593050816a0c112100d8340531780512a0441a03814205e068238001c051834a243308c81501b800340501c6c001e6480a050a0881a125120501c6023000401f038b8310d80010c21600a1e000680e05081404211512c94106037000b40e028b0201c0ee014481460440d0be890380a332d0070fc2702c331304201981c140218ba2422381ac26001681c0518230740e64e8964a083e00c30140a120002b818200e281b8032607014580384e180864989050fc3f0c04703878)
def xul11 : Packing := (86,3,7,0,0,13,0,xud11)
def xuh11 (i : Nat) : Nat := (if i<1 then 0x5ae1ab4079e09050a5d6ceb457b29c602306b11011eb14c0afc14d10cb26b9a08490b5f07fc0ac80a0108babcf202e830dc085576c0b5894be36a9d282273f101eb105813a00000000000bf01ae07866c9a75660c920929664f12780710000703f0000005612a27014300090a2c08f0000d0aa00006038000000007297505e40959033407c9004b00a9083e6b7503bb001f70c0b0d00c100c09062d10e6048e67007a7b09ed0297054013da04e1380521fc03703c290b8d691a06a509c102f308a0000000000000000a1afc6b300000000b199005711a00662b89c60bd766f70cdc01221c92036b0a4d006e74ef11c215870a75028c7a2603cd075507760997002d6b0f13820506005707677a9c0b06696c052b625928d3b951070e0b70000000030a1f0abb0930000d060d0a300c200008024a0d010100000d04044580000000040650000c25630cce06fd1d0000000000000d04fa673805d91a280b9802231b5eb57b044206ce019a042539a704a204500003227203eb016a69f5047c0a80000f1bdd0bad146119f8114f07e00007784210c0000a24d0000c13f20800000b06e0000f6bf0000876d000016ac0000000000000000918f209bf046b1b90180a143d6350000db9a30587068000080697a970000d66af03100000000c05b008ec06b0000208d8007000020883155e097009101a400000000000000000000112c20c39061a05c802a3623b63f400ca055686d80ce007d000031b720c7b26d91b0000000000000000000a951c2f043000000000000402c76a370c8b09a000000009059300f110040739098000031a140517035d0ca007b50673ba301c741c3503d5259e16bd657c074b049361a0000b02b52bee04c3a56e6c00000603200000000606610b6b0094753d08c70b1901d303030261355800ee053e03a50c53081d04dc0b245c270be60208039d2a166af000037b7511100000000000040ae57c200bf46219008d0219157f1b6202db01c4041b07ada0c801f305fb0170082e671a08600000000b087f0b3100d00000000c0cf000093b310c6f02700300000004401e00f0010010040000c00000440000140800070070400400030001002800000054010000003890056000000c00000120120460c01c300204c04000600100000000301a04000300000000f08000000e1c000018004d88000b0050020000002410000800061010c000100068400241400000000004008040200008f08100000000800000c0004004400402000010001000010800000003c00010c00002400002c00800001800400800000000020c03800010c00003400030001800800c00410800000420800030010000870000000002400000400000000030400000010070010000000000800030430000010001800000400030020000400000c2001080000080000 else 0x61a8e09db025f680e66d0000000001a6a3d0f0a680c4e04b1663c6ba417eb764c0b400000000f094c018c1b3e2ad000001c870340000809600000000a01b72c2000000000000b176f74d0000406300000000f015506de67820bc00bb000027b2366ce251206400ad94a3c1ae67c41089409fb0031013c0722774)
def xud10 (i : Nat) : Nat := (if i<1 then 0x54b914c3bdfda32a90a619ff68985e4530ddff4cc93029877bf94695214c3bf6a9305c8a61ffc6052054530fd7f6cc0f28984ffdb8e89514c33fea9750c8a619ffe958264530ffb30bd1a409847fdbaaa5814c337fd3352c0a619fee81a9545308ffb7554aa2986fdba068d514c23fed934bc8a613feec1a564530cf7f28d2b229867bf946a5214c2bdfd9343ca2615fdec598645308ffb73d12a29847ffb26a5814c23fedd30bc8a615ef6d521e5130cf7f68d4a429847ffb2695914c2bdedc343ca2619efe93a5645308fff64d47229847ffb56a3914c3bddd2740c8a61fea48121e5130af7f68d4aa29867bd85e91914c23ffd9750c8a615fd6c6a960530cfdaa5d1322985ef9b6ea1204c33dea9748c8a61be7e51a354530cfdf44d13229857bfb46a5814c3fe8c0a6290261afeea1a8481308fff6bd43229857f5b1aa5214c33dfd2750c8a615efee921e5130af7b7490f289847ffb568b914c27fcd8752a8a61ff254d20485308fff6ad4a429857f7b16a5214c33fdd0552a8a617eeec151e5130cf7f48d13229856ffb66a1914c23fed974ac8a617f6ecda548130bbf76ed2a409847fdbaaa5214c337fd3552c0a61fda54ba548130efd2a4903229863fda8ea1914c23fedab5290a615efee1a1e5130afef62d4b029857dfb36a1914c2f5fdb303ca2619efe91a864530d7f750c0322986fd953ea1204c3bdac0aa3ca2617f6ecda848130ff3728a9a40987f9b944c5204c33dfda34ac8a615efee951e5130dfd241d2a42985fd7b168d514c27eed9f44a8a619ef689a1e5130afef62cab229847fdb5e89914c33dfd234ac8a61dfa483a264530dfb240d1aa29847fdb5ea1914c33bed2f4ac8a61beee53a848130cf7f49d1322986fe952ea1204c23ffdc345c8a613fe6cba054530cf7f29d1322984ff9b8e81914c2bfbd8b24c8a617f66d7a348130debf4aa9b229847ffb8697914c33dfca750c8a613f76cfa954530dfb760d1aa2985febb26a1204c3bddd2240c8a611ff6cba9545308ffb73d2a42984ff8ba481514c33dfca75290a611ff6e982e4530dfab02d1aa29857bdba547944c33dfca74a90a61bf6e8153645308fff65d2b229847ffb2697914c27fcd875290a61bfae892064530cf7f68d4b02986ef9b6ea1204c23fedc74ac8a615fdec5a954530cf7b05d2322985fdbb54c5204c37ecd9f40a8a61fe6e53a3481308ffb71d1322987fe121e85204c2bdfdd303ca261dfa54920e4530af7f68d4a429847fdb2ea1914c27fdd8744a8a619ef6a1a1e5130aff760d43229857f5b1aa5514c2affdbaa5c8a61eeee518060530dfb746d42409867bf94e95914c33fdd834ac8a61deee512064530cf7f29d4aa29857bfb5687944c33dfca744a8a615feec1a564530ef7729d03229856bfb6607944c3fe090a6290261fd25495348130 else (if i<2 then 0x1101f1996f03e1300792b0c62704201348901c02819970000a36e03ac5b93300a01c05060200700a181c028201c07c40b40508c480e028381003840500501f182f01c028608c050b0029204630680241581420230100a01d1011818103d03820500f040280a081680e10220382b240380a0c0501b100d01002807101180e01a0508028074b0181401c06c7a100501f1d840152c00a100700a103b02403814017281b04420100380a0e0401c168901007c159015814102801c201007c070c0400ed12028807c07081a00901407c11940d00e028301c0e840500d880a00a102301006c0710c480a01c341002840201400e1d84d120e40de08280a2100387c3c070a4900e028301403840380a0ac900a01c0980e158000a01c30100505e06c3189c1f803c5f9232d8212a48c482a01b8000d00a0840cc07280d83104206a04292c000a00726ac3546a9053929a81db1f252b9e7b4880edd1b688f42c7da46b280d3eb9dd0f9273f38f9af37b269cf3d9944c35bd92e70ed8f925832a6945c9124271f8451c71c6631ac79ec64630315b89aa28e24b0ff86cc2ce131072826409966afea7e23ed07c8f8e7aebd0966af3d780bb6c438e2275ab9e5ca65550ed9bb11b2e22703b7b1b4aa8233a8b683804fe6c5050d17cd8a6ac91c5a66cf7668b2551b24d8637b15166ac396099bb11fe1db0e01b457f01c05eeaf09738b765a82cd43b6b0f3222bd159caa85412919456a0546ca6a12d884739ea4943b655547fa3643b68be451a2210c48474109fec3805553f01b44dd86ec3dd1e24eb06ec39e9360e445553839bb0da255535b1a40cea64430997b4b8e5a12aa95c0aaa51927f136097a48c23891588603ff0e00f903b63a81c1076c6ce34c1988c005b42bf14c897446e1db0e008703ec1db0e006102bc14306d81a00019ff6a55260530affb64c2f229877ed52e89914c3bdedd303ca261bfe603a548530ef7f28c12a2986ff951ea1204c3bdfca32a90a61ff66153148130ef7f28d12a2987fd8ba54d204c3bdfca30a90a61fee60520e5130bff760caa42987fe920549814c2bffdc2a5c8a61bfee818254530affb6b54a429877bf94549814c2ffcd9740a8a613ff6e3a548530bff36bd42409867fd98e95214c3bded2a43ca2617feee1a548130ffd240c2a42986ffba0689514c33fed4b0a90a619ff609a5e4530bf7b6a90f28987fd953ea1204c2ffbd8b24c0a61def549a1e5130ff730090f28986ff9b2e81514c3bdfca352c0a61def54ba464530ffd2a5d4240985ffbb0695214c3bdfca324c0a619ff617a264530afff6ac17229877f985483914c37fdd434a90261dfe617a064530efdaa4c1322987fb581547944c3dfac0b04a8a61dfe6152064530affb6ac1322985dffb7689514c33fea9351c8a61ffc607a148130bbff6ed2a429875ffb7 else 0x11a02841a0281d02030080382025c000e0cdb82201c050cb140a049782201c39420500e0c11014100a8100386028840980108036302807c525ac96899424046100406820fc1100e028404610280700f8c11822160001007066480a00a180a410203807c40fa5b8229120380a19c940802807080380d080fc890280608020070a0400a1408081d01c08c602b0000e1c120e000280287c021681f1b92050084606807080dc1a03e33240840d8c8402201c38554378041aa10594203a4a8c0704cb011c103169c000400e200a0562003401a0440500e2d0005607c60200701f183b0240a00701b280a60003860340400e014403602840880708e0d890156480a00e300e0502561e0744822200804607c608c0200e32406ca0d411814180ad12088073922e8992c07c60600f8814014100803e05060900e080d01b110801c2010800070c1200a01c3e00038050c0a00e121203607060ac0f880d014074302406c0e0c0400a01c30760341600e014501405c4020))
def xul10 : Packing := (209,4,7,0,0,13,0,xud10)
def xuh10 (i : Nat) : Nat := 0x3039797480b404d6e6b0b74034088000126a5da0002c02d0864280002c4b91a800014e3c1a59cc0005013800888c000000141f00020170000000007b9853034000803141100030b663d2066e05a8b250d3d0797800008067861c1e41b60001c10f2144310000c3780a400000025a3e0b380f62d4000d0c08080003c597470000405641c70c9c33409350b0002124a05242757028350001c2a0000445e69bc184025c2610bac2b92c0425e0be12127ac000a03800054488e6707441b40480000000401d0e00000001c230003807b081c05000380a06b183660180000000a00c08c008242f45040080080824440002
def xud9 (i : Nat) : Nat := 0x1b2414bb4b44b0181f00b8805c2c10101a0a5a007080280385c00101fb0016040407c201410140c040070050c03807c4000e08140050118f5581b20ea84f71d0fdef53a10ea6296538ea2896148e874b8148e92cf71d0e92ce664ae0743a53a9c743a1d0e92c3a428a474292e0e8743a1d0a47e3a1d0e85200e6bfa6e515260530c7bdbae518548530e6bfa6e51a960530f7355260551e5130fab980ed981e5130ff6152605205453095ffc76c985e4530fb65526058254530ff49522e95348130d6bfb66e981e5130d6bdcaed981e5130bed9c62e95348130dee9b654ba848130e7ad52e53a264530e6bf94e999260530f3b7946058254530c7bdb8e53a254530e7ad52e93a264530e7afa45498264530b5bfc7549a1e5130d5bfb7e51a254530b5bfc754ba464530dfd181ed53148130cdfbb7ea1a548130efa952e53a848130ff495354ba848130d5bfb7e51a548530ffc1216153148130c7bfa46d582645309dbfc76d521e5130cfdbb3e818254530bebbc660520e5130cfbb946cba054530c7bdb8e53a548530cdfbb7e81a254530adfbc76cba054530ff498554d2048530c5fda8edd52e4530cff1812e92054530a5ffc754ba864530d7ad52ec9a1e5130ded9b654fa848130ff8121e51314813087bdcbe53a94853087becbe51a94853086fdcbe9aa960530ff0952e515348130c6bfb6e91a864530c6bfb6ed1a96053087becbe51a56453095bfc76d521e513087f9cbe82a954530ebd180605a354530c6bfa6ed1a96053086fecbe99a96053096bfc66e1a1e513087bdcbe53a954530ef495254fa848130
def xul9 : Packing := (58,5,7,0,0,9,0,xud9)
def xuh9 (i : Nat) : Nat := 0x18900180341e81b04817c2000000
def xud8 (i : Nat) : Nat := 0x602020000a3897f6fd3728a930298616ff1fa46d58264530df24a938c5d2a690261f32552e5181609514c3fa17aea9728a9a40987792549b654fa848130
def xul8 : Packing := (6,6,7,0,0,3,0,xud8)
def xusamples : Array (Bits × Bits) := #[(0x6d7c3ed0493817cf4100245,0x212cb611c80000ca4100044),(0x6832028d3c79594a06bb37,0x681000000c10514a069333),(0x117e4a8b6806784042085a6,0x11564e6b4c0258004000004),(0x6ea18307b14125e0b0301d8,0xea0000491c825e0b0201c0),(0x51c3487806525a47021a018,0x5043486806125a05021a018),(0x1ad3000a1fac0c383c601e0,0x8d3000e110c893038201a0),(0x97456be9928a00041a7800,0x97406be9928a0004182800),(0x6608318082c142c07fdc600,0x6608318082c102c007dc600),(0x300cfd5c24036a3f81dc600,0x3008f8406413400f005c600)]
def xucolumns : List ColumnInfo := [(17,0,494,0,11),(128,0,383,0,13),(64,0,447,0,13),(8,0,503,0,12),(32,0,479,0,12),(2,0,509,0,12),(256,0,255,0,12),(4,0,507,0,12),(25,0,486,0,8),(66,0,445,0,11),(404,8,99,0,4),(160,0,351,0,11),(3,0,508,0,9),(9,16,486,0,8),(114,1,396,0,4),(24,0,487,0,11),(162,0,349,0,7),(83,0,428,0,7),(132,0,379,0,11),(320,0,191,0,11),(31,0,480,0,4),(134,0,377,0,8),(322,0,189,0,8),(91,0,420,0,4),(340,8,163,0,4),(352,0,159,0,8),(7,0,504,0,7),(202,4,305,0,4),(178,1,332,0,4),(260,0,251,0,8),(74,0,437,0,7),(85,2,424,0,4),(102,128,281,0,4),(164,0,347,0,8),(297,16,198,0,4),(120,256,135,0,4),(28,0,483,0,8),(21,0,490,0,7),(344,0,167,0,7),(33,0,478,0,9),(449,32,30,0,4),(26,0,485,0,7),(14,0,497,0,7),(232,256,23,0,4),(156,0,355,0,7),(35,0,476,0,7),(324,0,187,0,7),(49,0,462,0,8),(198,0,313,0,7),(56,0,455,0,7),(416,0,95,0,8),(197,2,312,0,4),(2,64,189,256,9),(133,0,378,0,7),(259,64,188,0,5),(258,64,189,0,8),(266,64,181,0,5),(484,0,27,0,4),(154,4,353,0,4),(32,128,347,4,9),(185,0,326,0,4),(181,0,330,0,4),(274,64,173,0,5),(6,16,480,9,6),(273,32,78,128,5),(36,128,347,0,8),(15,16,480,0,4)]
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
  | 12 => lookupWord 145 183 4 15 7 4 xuh12
  | 11 => lookupWord 352 441 6 16 8 4 xuh11
  | 10 => lookupWord 23 127 6 14 6 4 xuh10
  | 9 => lookupWord 1 11 1 11 3 4 xuh9
  | _ => fun _ => none
def xu : Forest := ⟨511,13,fun j => xusamples[j]?.getD (0,0),xucolumns,xuautos,xulevels,xuindex⟩
set_option maxHeartbeats 0 in
theorem geomxu : graphValid xu (boundsBefore known383) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=4) ?_⟩,listPieces_all (d:=2) ?_⟩
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
theorem sxu_11_66 : block xu 11 66 12=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sxu_11_78 : block xu 11 78 8=true := by
  refine @block_merge xu 11 78 5 3 ?_ ?_
  · exact cornerRange_sound (by decide +kernel)
  · apply cellsBlock (ar:=12) (rows:=0) (d:=0)
    simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
    repeat' apply And.intro
    all_goals decide +kernel
theorem allxu_11 : block xu 11 0 86=true := (@block_merge xu 11 0 78 8 (@block_merge xu 11 0 66 12 (@block_merge xu 11 0 30 36 (@block_merge xu 11 0 1 29 sxu_11_0 sxu_11_1) sxu_11_30) sxu_11_66) sxu_11_78)
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
theorem sxu_10_111 : block xu 10 111 32=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sxu_10_143 : block xu 10 143 36=true := by
  exact cornerRange_sound (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sxu_10_179 : block xu 10 179 30=true := by
  exact cornerRange_sound (by decide +kernel)
theorem allxu_10 : block xu 10 0 209=true := (@block_merge xu 10 0 179 30 (@block_merge xu 10 0 143 36 (@block_merge xu 10 0 111 32 (@block_merge xu 10 0 75 36 (@block_merge xu 10 0 39 36 (@block_merge xu 10 0 3 36 sxu_10_0 sxu_10_3) sxu_10_39) sxu_10_75) sxu_10_111) sxu_10_143) sxu_10_179)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sxu_9_0 : block xu 9 0 16=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sxu_9_16 : block xu 9 16 36=true := by
  exact cornerRange_sound (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sxu_9_52 : block xu 9 52 6=true := by
  exact cornerRange_sound (by decide +kernel)
theorem allxu_9 : block xu 9 0 58=true := (@block_merge xu 9 0 52 6 (@block_merge xu 9 0 16 36 sxu_9_0 sxu_9_16) sxu_9_52)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sxu_8_0 : block xu 8 0 6=true := by
  exact cornerRange_sound (by decide +kernel)
theorem allxu_8 : block xu 8 0 6=true := sxu_8_0
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
theorem caseUB : Impossible true (graphGoal 511) 13 (rootB 511).toFinset :=
  index_root (g:=xu) (i:=0) rfl rfl (before_sound known383 valid383) geomxu tablesxu (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem caseUA : Impossible true (graphGoal 511) 13 (vars 511).toFinset :=
  cut_root (prior:=boundsBefore known383) (before_sound known383 valid383) (128,0,383,0,13) (by decide +kernel) (by decide +kernel)
theorem validF : Known false known383 := known_down valid383
def xdd14 (i : Nat) : Nat := 0x7185103081011ff
def xdl14 : Packing := (1,0,6,0,0,0,0,xdd14)
def xdh14 (i : Nat) : Nat := 0x72b600002081ca4000006212e80052e946141a6b20caf10a0204d
def xdd13 (i : Nat) : Nat := 0x1222438b085863888b0e38a0d004a23c5890c44280191e9e80ffd20ffd10ffd30
def xdl13 : Packing := (3,1,6,0,0,7,0,xdd13)
def xdh13 (i : Nat) : Nat := 0x109240d604212c0006120005308000000911293a596c28d80302f5208823202b88c12000316a3a3082c842027b2180048d522f007822a0fe26300c000c0680280018400006438030e9c0003b708be08960e9038809415ec00000003c206e010a00261014100000020622012100001101000010000010
def xdd12 (i : Nat) : Nat := 0x3825958b0e9184b30c36ac54a868b101236561e167ac45881c6a531f0e2117012a192122f9187150c9e9712912834314c588864b4a16561e2e009049434531f1619296660412122f8f87090d80b09f12a83431709c548868a4b16523c322e1e00aa50a204c4a0d0f1445212a2e1839621899187169f0c1c847c50dc0480c093e1e2890325c51b2b230d3e2e18d878b859497306c8c3c58a864b093e3e1e2c46025431e6148d8a100ddb361668b9d4923d3f066cab1191c82bc3d03d001ffd53483ffb22907ff64d20ffec0a61ffd82443ffa42987ff64910ffea8a61ffd83443ffa64887ff64530ffe98a41ffd98483ffb26887fe48110bfecc241ff9204c2ffb24885ff64530
def xdl12 : Packing := (19,2,6,0,0,11,0,xdd12)
def xdh12 (i : Nat) : Nat := 0x5854805b80a40000000f0600000000290200000001c860000605d88185cc32b0b0550f36500901e427900bf59bb005504a6c03adb9096a0228069614304b97a2405841451310001ef0740e0000b441f05c0000bb560a00ccf98bc9550000e08ec248000000160d0c0680000000000000000001007f5284a0a013906a000008c1bcc9751d5240003a4ae0acae415ca484a04360000000000000000000000232af0aa000140af04e50560001120115700000000dd0b22140120743109a8c5658688b20dc6127fa98815c28d8000e06e000218f2b4c0001145ec0620140000000068a1a18d01e214d1d5e12ea72ac08042c3a040065822a01f1851946e44aac1628182602a8680002010c47a3440445c0010001c09c0000000483d2f242081844a0338ca300bdb3ad08e82c00007031421ee849daa8824a10530600007833621580fd88f2121000064508231910904514a2c26a8129077e2ccc013d18636fa4fc00000000001a8cc000283c303660e34201b11469c881400050485b9c0000022f00b8085a5300002a44262ccb3c427f33baa0000e541d7a36622e61338e9f137d1a0000051d9a00000100282508800d06ce5264073841803b8d120a38000500de10dc03b021104ca0f540473035133485900fb804c72fea2ac296345690e301ec508000185035b140500201000b21ca0004002804e00021488c301000080e0000a1300e08090309420014a0000640900020816100012a00010403
def xdd11 (i : Nat) : Nat := (if i<1 then 0x30b03c40f0382c3258a41c3070582030a8270c1608151218485841608080150a6182c1028382c4b09078b060b0406126288c20c30a8971586a5a88a0e6c04084a6283820425a1828160814134a0b040809a50943c403058203430582a32587c2032284290290489b1586a5a44810c30549860b04061381d170c0e2c18134a0b040a0e65048204650404a3240258a0c08150d451587894b0f840627c507c20411085121520244c104552f0c60bc0e0c10a5054c5b848407060484294152b141c101e1820151b3c1c1018270c100a918a166184314d8a59d0d4512038809c505820462e2e901e212c121608120c0962854205035141c1023281c10191428150810462111041b14bc51e86160d05442cbc35290c510042974acc1b8a1b070408100fb2eb18a2a182c101d141cc808110e0e0f0e8a160832e9598316d9e120811b016080d8a5d0dd6020509040403a286f8186c50542080e32b17860f094c2f16f17174aac048e2ec58b44a1c09182d8b435282a103014554bc36282a103f143d48459282586072286861462c2050ad2b30cb081529cba56604a103058974acc038206a2e2db015081786779f71f6c31fb64359f51f47b3fb37b2fb2331fb14314319f14312f066f9ef1ef1eda2cfec5ab92aeea4a9ca949c468ca770b7e6ce64e5864be41a39a2d222e1ae10a065f79c45e8de0dd45cc5c45bc5b21a1196d8c98257816b96155954f13e12ad1c111d054fd4f30eb0dc4d20ca0bd8b7ca4895c84c7606745644303682a01b40c8003ffd5260530fff609514c3ffda954d20fff65532443ffda960d10fff54983443ffda960530fff54d98483ffda254530fff61531483ffda54c910fff54d91483ffd9260530fff6a582443ffd8364520fff64983443ffd854c910fff54d92443ffca954d20fff655214c3ffda548530fff61593483ffd8264d10dff54d924437fd9366120bff6a191483ff92064530dff64d914837fda960530bff68d914837fda94c910dff689914c2ffda564910bff69532443ff93064520ff754d914c2ffda948530dff4c5984837fd9264530eff605984837fda166120dff66193443ff55164d10dff65592443ff9a548110dff6a583443ff5514c910bff695914c37fd8264530bff6a1924437fd9564530dff661914837fda564530dff6a1924437fda864530ffe54d20443fed5264d20ffe68d20443ff5814c520ffe481934437fd9864530bff68d98483ff91066120ffe601914c37fd8364910dff649814c3ff98048530bff69593483ff92060d10dff68d92443ff93066120ffe68131483ff92060530dff661924437fd9364910dff65593483ff551649109ff6a5834427fda1661209ff2a5314827fca954d20ff64c1314827fda364910ff948531483fd93054d20dfe481914c3bf98060530ffa481214c37f93066120 else 0xb5144a32e958634530c940a840a0e0806c61f080912cb0f8c12940f0408120704061fc)
def xdl11 : Packing := (89,3,6,0,0,12,0,xdd11)
def xdh11 (i : Nat) : Nat := 0xd10f6570be2a600bb4e232218be89e0e800000021e108b8dc0016960004848c098c7d7485adc3ecb272e00000340396b9915d40f61bc5b90b9c210010000b40a09c14a0ab31a41f219748113c0016183070a1c001c0d0005ab86e12ea000714f49b6280002bde2d000000000004efe060000000000e52410400c00000000000015866cdb670002045408000531169666c702905c59204b179f222013145e09f8324a2e250001858130492149993b88ee02305480189421c89721c01a2830416c501c64a218689009
def xdd10 (i : Nat) : Nat := 0xb02020780e04061306a128684e18150cc7c3061b082011b40ed14102514080800b060251686102f8302030401e1416105b0605460f0202a182e283c20b03c4016160c3204040b062205410103c10982d078764020205a8b9298605411040fe0128a550c088206c82fdb42ada7a8f8d635a023594e3a8d61c80de071db86557c5b55451522424f035cc82948c10400affb70a9b248857fdb54c5984833fec295298a413ff6e98254530bdfb6c54aa69067fca96a553483fecc2a6098a41ff64c0a954d20ffd240a9302987fe585485314827fe5d2a6cc241ff654d2060d10ffd240a93068867fda961532443ff2c12a299221dfb5498264530f7eb02c12a29877f985481914c2bfedab04c8a61ffc5452060530dfeb50a8a64887fd1814c131483fe4a9a4090a61dfa54920645308ffb66d0b309047fdb52a531483bec98a60cc241ff8485a04c520cfeb0254a629073f9814c198483fe09824298a41ef44c58060530
def xdl10 : Packing := (32,4,6,0,0,10,0,xdd10)
def xdh10 (i : Nat) : Nat := 0x162d60c000001a0b48548a00180640e804000000001a87a4ec1148fe71800a08483e03413640a0000081001041
def xdd9 (i : Nat) : Nat := 0x1e01c040605408080801e161b0800806dc04a40815204080087fcca6d53166120ff61525452060530fb65526058254530ff49524c0a954d20ded9b64c0a954d20a6fdc62a5a954d20ffc130615214c520ff495254d2060d10e7e552604a94c520f3d1316053066120
def xdl9 : Packing := (10,5,6,0,0,7,0,xdd9)
def xdh9 (i : Nat) : Nat := 0x1c0
def xdd8 (i : Nat) : Nat := 0x7792549b64c0a954d20
def xdl8 : Packing := (1,6,6,0,0,0,0,xdd8)
def xdsamples : Array (Bits × Bits) := #[(0x4130138558c4504c04e1563,0x150aa38450d8e542a8e1143),(0x14140d6b21420505035ac85,0x22f55c63000108bd5718c00),(0x6082a8a879081820aa2a1e,0x4d00a088853ed3402822214),(0x284160147ec0aa1058051fb,0x10df18147ac10437c6051eb),(0x68210468c0005a08411a300,0x6a20446880261a88111a200),(0x1801070bf2d0060041c2fc,0x28051850af270a0146142bc),(0x10068480f8020401a1203e0,0x180a0080f826860280203e0),(0x2880700c01100a201c0300,0x12fa4700400024be91c0100),(0x42c7ff00282010b1ffc00,0x4720e72b001871c839cac00)]
def xdcolumns : List ColumnInfo := [(128,0,383,0,13),(16,0,495,0,13),(64,0,447,0,13),(32,0,479,0,12),(2,0,509,0,12),(256,0,255,0,12),(17,0,494,0,11),(4,0,507,0,12),(8,0,503,0,12),(83,0,428,0,7),(66,0,445,0,11),(132,0,379,0,11),(196,2,312,1,5),(35,0,476,0,7),(202,4,305,0,4),(320,0,191,0,11),(114,1,396,0,4),(197,2,312,0,4),(7,0,504,0,7),(74,0,437,0,7),(25,0,486,0,8),(404,8,99,0,4),(31,0,480,0,4),(268,0,243,0,7),(24,0,487,0,11),(160,0,351,0,11),(322,0,189,0,8),(156,0,355,0,7),(56,0,455,0,7),(416,0,95,0,8),(85,2,424,0,4),(167,0,344,0,4),(297,16,198,0,4),(224,256,23,8,5),(344,0,167,0,7),(15,16,480,0,4),(49,0,462,0,8),(232,256,23,0,4),(257,32,94,128,6),(134,0,377,0,8),(340,8,163,0,4),(188,0,323,0,4),(176,0,335,0,8),(177,0,334,0,7),(178,1,332,0,4),(2,64,189,256,9),(296,0,215,0,7),(32,128,347,4,9),(120,256,135,0,4),(449,32,30,0,4),(208,0,303,0,8),(91,0,420,0,4),(290,64,157,0,5),(36,128,347,0,8)]
def xdautos : List (List Nat) := [[],[81,130,118],[16,82,131,100],[16,32,48,128,100,80,116],[32,83,116],[32,49,128,81,116,100],[48,33,133,118],[48,129,82],[80,16,33,50,116,131,100],[80,129,50,116],[128,49,100],[128,81,32,49,100,116]]
def xdlevels : Nat → Packing
  | 14 => xdl14
  | 13 => xdl13
  | 12 => xdl12
  | 11 => xdl11
  | 10 => xdl10
  | 9 => xdl9
  | 8 => xdl8
  | _ => emptyPacking
def xdindex : Nat → Nat → Option (Nat × Nat)
  | 14 => lookupWord 7 19 3 10 2 4 xdh14
  | 13 => lookupWord 47 59 4 13 5 4 xdh13
  | 12 => lookupWord 100 253 5 15 7 4 xdh12
  | 11 => lookupWord 22 113 6 13 5 4 xdh11
  | 10 => lookupWord 19 25 3 12 4 4 xdh10
  | 9 => lookupWord 1 3 1 9 1 4 xdh9
  | _ => fun _ => none
def xd : Forest := ⟨1535,14,fun j => xdsamples[j]?.getD (0,0),xdcolumns,xdautos,xdlevels,xdindex⟩
set_option maxHeartbeats 0 in
theorem geomxd : graphValid xd (boundsBefore known383) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=4) ?_⟩,listPieces_all (d:=2) ?_⟩
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
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sxd_13_0 : block xd 13 0 3=true := by
  apply cellsBlock (ar:=10) (rows:=1) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allxd_13 : block xd 13 0 3=true := sxd_13_0
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sxd_12_0 : block xd 12 0 5=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sxd_12_5 : block xd 12 5 14=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allxd_12 : block xd 12 0 19=true := (@block_merge xd 12 0 5 14 sxd_12_0 sxd_12_5)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sxd_11_0 : block xd 11 0 12=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sxd_11_12 : block xd 11 12 36=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sxd_11_48 : block xd 11 48 18=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sxd_11_66 : block xd 11 66 23=true := by
  refine @block_merge xd 11 66 6 17 ?_ ?_
  · exact cornerRange_sound (by decide +kernel)
  · refine @block_merge xd 11 72 1 16 ?_ ?_
    · apply cellsBlock (ar:=12) (rows:=0) (d:=0)
      simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
      repeat' apply And.intro
      all_goals decide +kernel
    · refine @block_merge xd 11 73 6 10 ?_ ?_
      · exact cornerRange_sound (by decide +kernel)
      · refine @block_merge xd 11 79 1 9 ?_ ?_
        · apply cellsBlock (ar:=12) (rows:=0) (d:=0)
          simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
          repeat' apply And.intro
          all_goals decide +kernel
        · refine @block_merge xd 11 80 3 6 ?_ ?_
          · exact cornerRange_sound (by decide +kernel)
          · refine @block_merge xd 11 83 1 5 ?_ ?_
            · apply cellsBlock (ar:=12) (rows:=0) (d:=0)
              simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
              repeat' apply And.intro
              all_goals decide +kernel
            · refine @block_merge xd 11 84 3 2 ?_ ?_
              · exact cornerRange_sound (by decide +kernel)
              · apply cellsBlock (ar:=12) (rows:=0) (d:=0)
                simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
                repeat' apply And.intro
                all_goals decide +kernel
theorem allxd_11 : block xd 11 0 89=true := (@block_merge xd 11 0 66 23 (@block_merge xd 11 0 48 18 (@block_merge xd 11 0 12 36 sxd_11_0 sxd_11_12) sxd_11_48) sxd_11_66)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sxd_10_0 : block xd 10 0 2=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sxd_10_2 : block xd 10 2 9=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sxd_10_11 : block xd 10 11 21=true := by
  refine @block_merge xd 10 11 6 15 ?_ ?_
  · exact cornerRange_sound (by decide +kernel)
  · refine @block_merge xd 10 17 1 14 ?_ ?_
    · apply cellsBlock (ar:=11) (rows:=0) (d:=0)
      simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
      repeat' apply And.intro
      all_goals decide +kernel
    · refine @block_merge xd 10 18 2 12 ?_ ?_
      · exact cornerRange_sound (by decide +kernel)
      · refine @block_merge xd 10 20 1 11 ?_ ?_
        · apply cellsBlock (ar:=11) (rows:=0) (d:=0)
          simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
          repeat' apply And.intro
          all_goals decide +kernel
        · refine @block_merge xd 10 21 8 3 ?_ ?_
          · exact cornerRange_sound (by decide +kernel)
          · refine @block_merge xd 10 29 2 1 ?_ ?_
            · apply cellsBlock (ar:=11) (rows:=0) (d:=0)
              simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
              repeat' apply And.intro
              all_goals decide +kernel
            · exact cornerRange_sound (by decide +kernel)
theorem allxd_10 : block xd 10 0 32=true := (@block_merge xd 10 0 11 21 (@block_merge xd 10 0 2 9 sxd_10_0 sxd_10_2) sxd_10_11)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sxd_9_0 : block xd 9 0 1=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sxd_9_1 : block xd 9 1 9=true := by
  refine @block_merge xd 9 1 8 1 ?_ ?_
  · exact cornerRange_sound (by decide +kernel)
  · apply cellsBlock (ar:=10) (rows:=0) (d:=0)
    simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
    repeat' apply And.intro
    all_goals decide +kernel
theorem allxd_9 : block xd 9 0 10=true := (@block_merge xd 9 0 1 9 sxd_9_0 sxd_9_1)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sxd_8_0 : block xd 8 0 1=true := by
  exact cornerRange_sound (by decide +kernel)
theorem allxd_8 : block xd 8 0 1=true := sxd_8_0
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
  · exact allxd_8
  · exact allxd_9
  · exact allxd_10
  · exact allxd_11
  · exact allxd_12
  · exact allxd_13
  · exact allxd_14
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem caseFA : Impossible false (graphGoal 1535) 14 (vars 1535).toFinset :=
  index_root (g:=xd) (i:=0) rfl rfl (before_sound known383 validF) geomxd tablesxd (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem lowx15 : Lower false (varsX 1551) (graphGoal 1551) 4 :=
  strong_low (m:=1551) (cap:=3) (l:=[(0,10),(1,1),(2,2),(3,5)]) (by decide +kernel) (plainA (q:=15) (prior:=boundsBefore known383) (before_sound known383 validF) (by decide +kernel))
    (cut_root (prior:=boundsBefore known383) (before_sound known383 validF) (512,1,12,2,2) (by decide +kernel) (by decide +kernel))
def knownx15 := extendKnown known383 4 [(1551,[]),(1833,[130,114,33,97,82,65])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem validx15 : Known false knownx15 := extendKnown_ok (m:=1551) validF lowx15 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem lowx111 : Lower false (varsX 1647) (graphGoal 1647) 7 :=
  strong_low (m:=1647) (cap:=6) (l:=[(0,10),(1,1),(2,2),(3,5),(5,1),(6,2)]) (by decide +kernel) (plainA (q:=111) (prior:=boundsBefore knownx15) (before_sound knownx15 validx15) (by decide +kernel))
    (cut_root (prior:=boundsBefore knownx15) (before_sound knownx15 validx15) (512,8,99,4,5) (by decide +kernel) (by decide +kernel))
def knownx111 := extendKnown knownx15 7 [(1647,[]),(1901,[129,113,82,65,48]),(1963,[98,134,114,66,81])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem validx111 : Known false knownx111 := extendKnown_ok (m:=1647) validx15 lowx111 (by decide +kernel)
def x303d7 (i : Nat) : Nat := 0x105fd30
def x303l7 : Packing := (1,1,1,0,0,0,0,x303d7)
def x303h7 (i : Nat) : Nat := 0x1ef762040000000008400000011bce4000001439
def x303d6 (i : Nat) : Nat := 0x21bf58530fe48130
def x303l6 : Packing := (2,2,1,0,0,0,0,x303d6)
def x303samples : Array (Bits × Bits) := #[(0x2ccb32ccb32ccb32ccb32cc,0x34cd334cd334cd334cd334c),(0x4c731cc731cc731cc731cc7,0x48120481204812048120481),(0x5334cd334cd334cd334cd33,0x320c8320c8320c8320c832),(0x10842108421084210842108,0x3c8f23c8f23c8f23c8f23c8),(0,0),(0x2328ca328ca328ca328ca32,0xa2288a2288a2288a2288a2),(0,0),(0,0),(0x3c0f03c0f03c0f03c0f03c,0x1405014050140501405014)]
def x303columns : List ColumnInfo := [(288,0,1551,0,4),(6,0,1833,0,4)]
def x303autos : List (List Nat) := [[],[81,130],[16,82,131],[16,32,48,128,80],[32,83],[32,49,128,81],[48,33,133],[48,129,82],[80,16,33,50,131],[80,129,50],[128,49],[128,81,32,49]]
def x303levels : Nat → Packing
  | 7 => x303l7
  | 6 => x303l6
  | _ => emptyPacking
def x303index : Nat → Nat → Option (Nat × Nat)
  | 7 => lookupWord 4 17 1 9 1 4 x303h7
  | _ => fun _ => none
def x303 : Forest := ⟨1839,7,fun j => x303samples[j]?.getD (0,0),x303columns,x303autos,x303levels,x303index⟩
set_option maxHeartbeats 0 in
theorem geomx303 : graphValid x303 (boundsBefore knownx111) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=0) ?_⟩,listPieces_all (d:=2) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx303_7_0 : block x303 7 0 1=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allx303_7 : block x303 7 0 1=true := sx303_7_0
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx303_6_0 : block x303 6 0 2=true := by
  exact cornerRange_sound (by decide +kernel)
theorem allx303_6 : block x303 6 0 2=true := sx303_6_0
theorem tablesx303 : checkedTables x303 7 := by
  intro k hk
  interval_cases k
  · exact (rfl : block x303 0 0 0 = true)
  · exact (rfl : block x303 1 0 0 = true)
  · exact (rfl : block x303 2 0 0 = true)
  · exact (rfl : block x303 3 0 0 = true)
  · exact (rfl : block x303 4 0 0 = true)
  · exact (rfl : block x303 5 0 0 = true)
  · exact allx303_6
  · exact allx303_7
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem lowx303 : Lower false (varsX 1839) (graphGoal 1839) 8 :=
  strong_low (m:=1839) (cap:=7) (l:=[(0,10),(1,1),(2,2),(3,5),(5,1),(8,8)]) (by decide +kernel) (plainA (q:=303) (prior:=boundsBefore knownx111) (before_sound knownx111 validx111) (by decide +kernel))
    (index_root (g:=x303) (i:=0) rfl rfl (before_sound knownx111 validx111) geomx303 tablesx303 (by decide +kernel))
def knownx303 := extendKnown knownx111 8 [(1839,[])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem validx303 : Known false knownx303 := extendKnown_ok (m:=1839) validx111 lowx303 (by decide +kernel)
def x127d8 (i : Nat) : Nat := 0x194813fd30
def x127l8 : Packing := (1,1,3,0,0,0,0,x127d8)
def x127h8 (i : Nat) : Nat := 0x8e80
def x127d7 (i : Nat) : Nat := 0x4944490bc37eb0261df54530
def x127l7 : Packing := (2,2,3,0,0,4,0,x127d7)
def x127h7 (i : Nat) : Nat := 0x68
def x127d6 (i : Nat) : Nat := 0x641b788054530
def x127l6 : Packing := (1,3,3,0,0,0,0,x127d6)
def x127h6 (i : Nat) : Nat := 0x78000
def x127d5 (i : Nat) : Nat := 0x320cce6508054530
def x127l5 : Packing := (1,4,3,0,0,0,0,x127d5)
def x127samples : Array (Bits × Bits) := #[(0x24ad25692b495a4ad25692b,0x46aa3551aa8d546aa3551aa),(0x13549aa4d526a93549aa4d5,0x1944ca26513289944ca2651),(0x41b20d906c83641b20d906c,0x44922491248924492249124),(0x482e41720b905c82e41720b,0x3a2dd16e8b745ba2dd16e8b),(0x8d046823411a08d0468234,0x1500a805402a01500a8054),(0x241920c906483241920c906,0x3911c88e447223911c88e44),(0x12e09704b825c12e09704b8,0x66a33519a8cd466a33519a8),(0,0),(0,0)]
def x127columns : List ColumnInfo := [(532,8,99,0,4),(608,0,31,0,7),(528,0,111,0,7),(514,64,61,0,5),(546,64,29,0,4),(561,0,78,0,4)]
def x127autos : List (List Nat) := [[],[16,66,101]]
def x127levels : Nat → Packing
  | 8 => x127l8
  | 7 => x127l7
  | 6 => x127l6
  | 5 => x127l5
  | _ => emptyPacking
def x127index : Nat → Nat → Option (Nat × Nat)
  | 8 => lookupWord 1 3 1 6 1 1 x127h8
  | 7 => lookupWord 1 3 1 6 1 1 x127h7
  | 6 => lookupWord 1 3 1 6 1 1 x127h6
  | _ => fun _ => none
def x127 : Forest := ⟨1663,8,fun j => x127samples[j]?.getD (0,0),x127columns,x127autos,x127levels,x127index⟩
set_option maxHeartbeats 0 in
theorem geomx127 : graphValid x127 (boundsBefore knownx303) = true := by
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
  exact cornerRange_sound (by decide +kernel)
theorem allx127_7 : block x127 7 0 2=true := sx127_7_0
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx127_6_0 : block x127 6 0 1=true := by
  exact cornerRange_sound (by decide +kernel)
theorem allx127_6 : block x127 6 0 1=true := sx127_6_0
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx127_5_0 : block x127 5 0 1=true := by
  exact cornerRange_sound (by decide +kernel)
theorem allx127_5 : block x127 5 0 1=true := sx127_5_0
theorem tablesx127 : checkedTables x127 8 := by
  intro k hk
  interval_cases k
  · exact (rfl : block x127 0 0 0 = true)
  · exact (rfl : block x127 1 0 0 = true)
  · exact (rfl : block x127 2 0 0 = true)
  · exact (rfl : block x127 3 0 0 = true)
  · exact (rfl : block x127 4 0 0 = true)
  · exact allx127_5
  · exact allx127_6
  · exact allx127_7
  · exact allx127_8
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem lowx127 : Lower false (varsX 1663) (graphGoal 1663) 9 :=
  strong_low (m:=1663) (cap:=8) (l:=[(0,10),(1,1),(2,2),(3,5),(4,1),(5,1),(6,2)]) (by decide +kernel) (plainA (q:=127) (prior:=boundsBefore knownx303) (before_sound knownx303 validx303) (by decide +kernel))
    (index_root (g:=x127) (i:=0) rfl rfl (before_sound knownx303 validx303) geomx127 tablesx127 (by decide +kernel))
def knownx127 := extendKnown knownx303 9 [(1663,[]),(1917,[129,82,113,48])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem validx127 : Known false knownx127 := extendKnown_ok (m:=1663) validx303 lowx127 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem lowx239 : Lower false (varsX 1775) (graphGoal 1775) 9 :=
  strong_low (m:=1775) (cap:=8) (l:=[(0,10),(1,1),(2,2),(3,5),(5,1),(6,2),(7,4)]) (by decide +kernel) (plainA (q:=239) (prior:=boundsBefore knownx127) (before_sound knownx127 validx127) (by decide +kernel))
    (cut_root (prior:=boundsBefore knownx127) (before_sound knownx127 validx127) (520,0,231,0,8) (by decide +kernel) (by decide +kernel))
def knownx239 := extendKnown knownx127 9 [(1775,[])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem validx239 : Known false knownx239 := extendKnown_ok (m:=1775) validx127 lowx239 (by decide +kernel)
def x367d10 (i : Nat) : Nat := 0x10200ffd30
def x367l10 : Packing := (1,1,5,0,0,0,0,x367d10)
def x367h10 (i : Nat) : Nat := 0x163f67bd198c001891c5001c00e2488527e2a8085042063a29b8928f42fa534182920de480000180aa15cdf1a70dc23c840c63143800e22014001cc00000000000316a0bb22
def x367d9 (i : Nat) : Nat := 0x9083832070a0c6302020b061400e0d204283184010a001066121c0c0840cc08383180840c3904040a1a082060102c50509084830201220241041430300805043850c0cc0028318480081902008500194604030828006780021070651b08001160c28c40184141802840202042061ce3020180083833f21bb6658c5d35d5413fc84ff382c92f0aba5e7c9a24a0d81b001ff18530ffae4987fd614c3fe38a61ff58130ffa82987fd754c3feb8a61ff54930ffa84987fd214c3fea8a61ff48130ffaa0987fd104c2feb9261fe58130bf8e2987f9204c2feb8a617f5d530
def x367l9 : Packing := (21,2,5,0,0,10,0,x367d9)
def x367h9 (i : Nat) : Nat := 0x6d1648d70732530b727c00229544f7e87253eacf8ff835304000089000044881f50f0e94149d6c0959458000e0e00000006213ec70a566201d5037046876455000095e08142ee8790a3a9a404c2c906e846000000242dc2a54f00058db44a8441a910ddc4e808e2a7314001b2f00010e1c85049c07b81ca30430d1d048984454cb0644fe0963191ad1065e89e09017f851c17135000505d4b8000d150003424a014968000001d47a27000000000000030cdab1311e189498000000b26000249e35c30c28ca014a456a000000000007000001e5d91e29dc8f4000d0dd0fb10688e04300012c0ca2920e29284c0000006a758780006390e2b85b8b030c295f48de3564df06ed040b582000038d64a1a5bbaa800141c2050000041278c03b15800144ca3410000d000500910800030302000234270a09211c0d0d0053061515010313010f010003
def x367d8 (i : Nat) : Nat := 0x2881c080c6200a0f004020a0a1200c46000c700061e3128007184810281901e09006001070a031a1400387100c1450206204428003201878838284107001030189060040c0e20400188280c40a030030309105840c1848210b0c070542033400500202040006400070318604820290300c2460a2020106031c08288301c0c62206209031020188000c40e06210031048203810582819c24181460e000630c01050320081880c1c40280061240003071860388081c0c60f840630907030620100038c140c402120630107101841834402000e0640c061009032ebfd459f63fc3877429b3827e4fcf1f29c16c6d0e30cdfc14d75edd5ad346f1ec856baac29853541a3829a83cfa87125276cd89872ba4cc9414c29a3fc6a89b0e215c16812f51e3bba72a951bc35366c0b590b045deb495eaa805aa4d3f2694a885cfd1dd370148c71a331c468b494c26e4687e8d8176298448740ce14816800fed6248130dfd615d530ff96448130dfc7644130ff96050930dfd8754530bfd8518530ff55158530ff96054930dfd215c530ff96548130dfd8758530dfd515c530dfd655c530dfd641c530dfd545c530dfd645c530bfd8558530bfd8650530ff96058530f7d5354130fbd5450530f7d5154930dfd7150930ff96148130bfd8550530dfd515c930dfd655c930dfd651c530dfd615c530dfd645c930dfd545c930fdd3148530dfd541c530dfc8758530bfd851c530ff96048530fed5248530f7d5454930dfd215d530f7c8558530bfd861c530bfd8548530dfc7654130dfd7550930ff95448130ff56150530fdd3154930dfd525c530fdd3154530dfd615c930ff95148130ff960545309fd865c530fe92050930df971481309fc8758530dbd7450530df976481309fd821c5309fd87581309fc87509309fd825d5309fd815c930df88758130fd93158130df9605d530bf98018530ef96058530fe921481309fd861c5309fc8754530df9605c9309fc87505309fc8754930fd93148130df9601c530fd531485309fd8718530f9d43505309fd815d530ddd315c9309fd8750930dec825c5309fd851c5309fd8750530bbd841c5309fd841c530bdd8350530fb884581309fc8748530fd943481309bd841c530
def x367l8 : Packing := (93,3,5,0,0,11,0,x367d8)
def x367h8 (i : Nat) : Nat := 0x190a899872853cce0458ef0310d00618b04c00000000000060a4808460000007885c470bf81a8280000060ca0f290684c8f8002cbb8258108adcb483800000087a8070e10c4c0c06809305c0d80040890a00c10014c0648000000090000080
def x367d7 (i : Nat) : Nat := 0xa0d004070100c6010188001000420901880e0310242030c000620385f71df5f609f5f69df5f5f5f5f5f5bdf5f495f495be41f5f609f5bd610494cc9438023fb2a43a849865f2158758530cdec22ca38a611fd9521d614c23fb2c43aa49867e581851c530cfc43ac0a8a611fc98585754c33f10eb02c29873e5808758530af6c90eca82615ed921d9104c23fb2c43aa2987bc58151585308feca90ea0a619f960608714c32f90a43ac29863f595861c5308fecab0c38a6197d65614714c23fb2c43a829847f6448750930fe290a62a92619f887581214c23fb2c43a429879e5808558530cde43aa8a0a61f894250d204c3da2c298ac09866e611601c530cdc4830838a619b887211604c33d10e90284987f04853148130
def x367l7 : Packing := (34,4,5,0,0,8,0,x367d7)
def x367h7 (i : Nat) : Nat := 0x6a090000521407cc000028e2c04
def x367d6 (i : Nat) : Nat := 0xe01880908061037df778f0319d436448750930f944c560215614c3879602148758530f344c56021d614c2d88a75094348130a2e69890610714c21b8a9611601c530
def x367l6 : Packing := (7,5,5,0,0,6,0,x367d6)
def x367h6 (i : Nat) : Nat := 0x40
def x367d5 (i : Nat) : Nat := 0x1e14215315808758530
def x367l5 : Packing := (1,6,5,0,0,0,0,x367d5)
def x367samples : Array (Bits × Bits) := #[(0x47048064704806470480647,0x42b1c5142b1c5142b1c5142),(0x7b4b1047b4b1047b4b1047b,0x390a28eb90a28eb90a28eb9),(0x8095218809521880952188,0x40b556040b556040b556040),(0x17106319710631971063197,0x174a81b974a81b974a81b97),(0,0),(0x240484a240484a240484a24,0x44e12a844e12a844e12a84),(0x6e208006e208006e208006,0x6c4d3106c4d3106c4d3106),(0,0),(0x38b02d838b02d838b02d838,0x68312c468312c468312c468)]
def x367columns : List ColumnInfo := [(524,0,355,0,7),(545,0,334,0,7),(64,0,1839,0,8),(546,1,332,0,4),(256,0,1647,0,7),(525,0,354,0,4),(70,0,1833,0,4),(772,8,99,0,4),(0,4,353,10,6),(769,32,78,0,4),(556,0,323,0,4),(514,4,353,8,5),(2,0,1901,0,7),(553,0,326,0,4),(2,4,353,8,5),(609,0,270,0,4),(522,4,353,0,4),(832,0,47,0,5),(800,0,79,0,5)]
def x367autos : List (List Nat) := [[],[32,83],[48,129,82],[80,129,50]]
def x367levels : Nat → Packing
  | 10 => x367l10
  | 9 => x367l9
  | 8 => x367l8
  | 7 => x367l7
  | 6 => x367l6
  | 5 => x367l5
  | _ => emptyPacking
def x367index : Nat → Nat → Option (Nat × Nat)
  | 10 => lookupWord 9 47 4 11 5 2 x367h10
  | 9 => lookupWord 35 179 8 13 7 2 x367h9
  | 8 => lookupWord 41 53 3 12 6 2 x367h8
  | 7 => lookupWord 3 13 3 9 3 2 x367h7
  | 6 => lookupWord 1 3 1 7 1 2 x367h6
  | _ => fun _ => none
def x367 : Forest := ⟨1903,10,fun j => x367samples[j]?.getD (0,0),x367columns,x367autos,x367levels,x367index⟩
set_option maxHeartbeats 0 in
theorem geomx367 : graphValid x367 (boundsBefore knownx239) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=2) ?_⟩,listPieces_all (d:=0) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx367_10_0 : block x367 10 0 1=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allx367_10 : block x367 10 0 1=true := sx367_10_0
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx367_9_0 : block x367 9 0 6=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx367_9_6 : block x367 9 6 15=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allx367_9 : block x367 9 0 21=true := (@block_merge x367 9 0 6 15 sx367_9_0 sx367_9_6)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx367_8_0 : block x367 8 0 1=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx367_8_1 : block x367 8 1 36=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx367_8_37 : block x367 8 37 3=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx367_8_40 : block x367 8 40 36=true := by
  refine @block_merge x367 8 40 2 34 ?_ ?_
  · exact cornerRange_sound (by decide +kernel)
  · refine @block_merge x367 8 42 1 33 ?_ ?_
    · apply cellsBlock (ar:=9) (rows:=0) (d:=0)
      simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
      repeat' apply And.intro
      all_goals decide +kernel
    · refine @block_merge x367 8 43 9 24 ?_ ?_
      · exact cornerRange_sound (by decide +kernel)
      · refine @block_merge x367 8 52 1 23 ?_ ?_
        · apply cellsBlock (ar:=9) (rows:=0) (d:=0)
          simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
          repeat' apply And.intro
          all_goals decide +kernel
        · refine @block_merge x367 8 53 5 18 ?_ ?_
          · exact cornerRange_sound (by decide +kernel)
          · refine @block_merge x367 8 58 1 17 ?_ ?_
            · apply cellsBlock (ar:=9) (rows:=0) (d:=0)
              simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
              repeat' apply And.intro
              all_goals decide +kernel
            · refine @block_merge x367 8 59 5 12 ?_ ?_
              · exact cornerRange_sound (by decide +kernel)
              · refine @block_merge x367 8 64 1 11 ?_ ?_
                · apply cellsBlock (ar:=9) (rows:=0) (d:=0)
                  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
                  repeat' apply And.intro
                  all_goals decide +kernel
                · refine @block_merge x367 8 65 3 8 ?_ ?_
                  · exact cornerRange_sound (by decide +kernel)
                  · refine @block_merge x367 8 68 1 7 ?_ ?_
                    · apply cellsBlock (ar:=9) (rows:=0) (d:=0)
                      simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
                      repeat' apply And.intro
                      all_goals decide +kernel
                    · refine @block_merge x367 8 69 4 3 ?_ ?_
                      · exact cornerRange_sound (by decide +kernel)
                      · refine @block_merge x367 8 73 1 2 ?_ ?_
                        · apply cellsBlock (ar:=9) (rows:=0) (d:=0)
                          simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
                          repeat' apply And.intro
                          all_goals decide +kernel
                        · exact cornerRange_sound (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx367_8_76 : block x367 8 76 17=true := by
  refine @block_merge x367 8 76 9 8 ?_ ?_
  · exact cornerRange_sound (by decide +kernel)
  · refine @block_merge x367 8 85 1 7 ?_ ?_
    · apply cellsBlock (ar:=9) (rows:=0) (d:=0)
      simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
      repeat' apply And.intro
      all_goals decide +kernel
    · refine @block_merge x367 8 86 5 2 ?_ ?_
      · exact cornerRange_sound (by decide +kernel)
      · refine @block_merge x367 8 91 1 1 ?_ ?_
        · apply cellsBlock (ar:=9) (rows:=0) (d:=0)
          simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
          repeat' apply And.intro
          all_goals decide +kernel
        · exact cornerRange_sound (by decide +kernel)
theorem allx367_8 : block x367 8 0 93=true := (@block_merge x367 8 0 76 17 (@block_merge x367 8 0 40 36 (@block_merge x367 8 0 37 3 (@block_merge x367 8 0 1 36 sx367_8_0 sx367_8_1) sx367_8_37) sx367_8_40) sx367_8_76)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx367_7_0 : block x367 7 0 7=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx367_7_7 : block x367 7 7 27=true := by
  refine @block_merge x367 7 7 1 26 ?_ ?_
  · exact cornerRange_sound (by decide +kernel)
  · refine @block_merge x367 7 8 1 25 ?_ ?_
    · apply cellsBlock (ar:=8) (rows:=0) (d:=0)
      simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
      repeat' apply And.intro
      all_goals decide +kernel
    · refine @block_merge x367 7 9 8 17 ?_ ?_
      · exact cornerRange_sound (by decide +kernel)
      · refine @block_merge x367 7 17 1 16 ?_ ?_
        · apply cellsBlock (ar:=8) (rows:=0) (d:=0)
          simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
          repeat' apply And.intro
          all_goals decide +kernel
        · refine @block_merge x367 7 18 6 10 ?_ ?_
          · exact cornerRange_sound (by decide +kernel)
          · refine @block_merge x367 7 24 1 9 ?_ ?_
            · apply cellsBlock (ar:=8) (rows:=0) (d:=0)
              simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
              repeat' apply And.intro
              all_goals decide +kernel
            · refine @block_merge x367 7 25 1 8 ?_ ?_
              · exact cornerRange_sound (by decide +kernel)
              · refine @block_merge x367 7 26 1 7 ?_ ?_
                · apply cellsBlock (ar:=8) (rows:=0) (d:=0)
                  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
                  repeat' apply And.intro
                  all_goals decide +kernel
                · exact cornerRange_sound (by decide +kernel)
theorem allx367_7 : block x367 7 0 34=true := (@block_merge x367 7 0 7 27 sx367_7_0 sx367_7_7)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx367_6_0 : block x367 6 0 3=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx367_6_3 : block x367 6 3 4=true := by
  refine @block_merge x367 6 3 1 3 ?_ ?_
  · exact cornerRange_sound (by decide +kernel)
  · refine @block_merge x367 6 4 2 1 ?_ ?_
    · apply cellsBlock (ar:=7) (rows:=0) (d:=0)
      simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
      repeat' apply And.intro
      all_goals decide +kernel
    · exact cornerRange_sound (by decide +kernel)
theorem allx367_6 : block x367 6 0 7=true := (@block_merge x367 6 0 3 4 sx367_6_0 sx367_6_3)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx367_5_0 : block x367 5 0 1=true := by
  exact cornerRange_sound (by decide +kernel)
theorem allx367_5 : block x367 5 0 1=true := sx367_5_0
theorem tablesx367 : checkedTables x367 10 := by
  intro k hk
  interval_cases k
  · exact (rfl : block x367 0 0 0 = true)
  · exact (rfl : block x367 1 0 0 = true)
  · exact (rfl : block x367 2 0 0 = true)
  · exact (rfl : block x367 3 0 0 = true)
  · exact (rfl : block x367 4 0 0 = true)
  · exact allx367_5
  · exact allx367_6
  · exact allx367_7
  · exact allx367_8
  · exact allx367_9
  · exact allx367_10
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem lowx367 : Lower false (varsX 1903) (graphGoal 1903) 11 :=
  strong_low (m:=1903) (cap:=10) (l:=[(0,10),(1,1),(2,2),(3,5),(5,1),(6,2),(8,8)]) (by decide +kernel) (plainA (q:=367) (prior:=boundsBefore knownx239) (before_sound knownx239 validx239) (by decide +kernel))
    (index_root (g:=x367) (i:=0) rfl rfl (before_sound knownx239 validx239) geomx367 tablesx367 (by decide +kernel))
def knownx367 := extendKnown knownx239 11 [(1903,[]),(1967,[118,130,81])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem validx367 : Known false knownx367 := extendKnown_ok (m:=1903) validx239 lowx367 (by decide +kernel)
def x383d12 (i : Nat) : Nat := 0x870a08027fd30
def x383l12 : Packing := (1,1,6,0,0,0,0,x383d12)
def x383h12 (i : Nat) : Nat := 0xe8900f505015106818000203000f8150c21070df9100000048f70438600070838a90b000000795984500000e94000000988000b80000807000a85214001f9750a000000000000d8ea8c383000000000102390913a1601171758711230900000069310e000088610000000600004200040000008003
def x383d11 (i : Nat) : Nat := 0x1c190824230b0f060120c1382820e1185870008a051207062076161a08682059c3818302423044b0e01081160c12100f8587000880908c3c1428010044070386040360a140262424230b04410e00141120e1810840d82870098983120508100b3088706048403a8e121c020833024210f0f070a00104129c12210098100870e06080f07c3c2418004507038406048360a121c0262c37053200142410e080a12981650a090806c1c2800543045040184e161e0c01f06003061211848783000c70908c3c1428036160c0218314230f0b0600b902f5dc6b134b273ca28ab021ddb86642b514ba423ca6a0bd9261d23304785a05a003ff5c530ffd704c3ff0c130ffd504c3ff58130ffd104c3ff61930ffd614c3ff60930ffd214c3ff1c130ffd524c3ff60530ffc714c3ff54530ffd624c3ff20530ffc104c3ff48130bfd814c2ff20530bfd824c2ff61930ff9204c3fe5c130
def x383l11 : Packing := (25,2,6,0,0,11,0,x383d11)
def x383h11 (i : Nat) : Nat := (if i<1 then 0x108c12584b6a01e9250702cf0cc0000c1740000c24ef200000082800000000000000000307a00000000d00c0001e262000130e30072f935c54d22220000c2cb0044000082192146e0514275c00f609461d4226d9072e165c2cd3249c12c9275d1e0094b4121c1563217729cb1136015a18c916cc9b5617ff180405a72408273128e215d82b4e2af5299a1aadc35411800000001020aa0edc0920001e178000001a331b9519f011b800c000000000000b0b9d1a1f2b49264000161d011180001323b287580c56115b0969051619a0001d289f2ce0000403cc23130c9ae13a0a6621626660062f2780000e01c0000025f61c80001c176d0ad506cd2b162bb503001961174e62e71400001c02ed9d16266011f8acf60de000040f931f4000112b29cc52276415e11e901f40000305e000040da00000000000000000001e048d23f6086842c50af2013101d00c200000001c1e751fa00000000b0daa13e00000206095c71b00000000192600001606661f60000a27c0000000000009a000000000000000000000042200000951000000000000000000001008e000000000001a0e40001d2c40000000000000001cd0e00008101e0d650b7c20ca1fad1ec022af220c4738056a03471d0029c61f8bd4b622e000062b00000205c000060bcb1d22074000020f3c162c04b40594dd1c029316581aea1074ec4607680246038414ace2e880ce26800000000000020b9610b623d403e4143426b20af1252a23b41820001821c6d3470dd221e629fc28c01f0000042266288a018b20c0001e0b6328da11000fe000000000001a1c60000000121bc0001c0b269b2a293c51e61cce017319b009e914e5122f13e20988239418a20a4c1e2e037008bb046355c20a921a750825001a0b1c127c05fa160426400003064000132b8000000000000112471ddb0a6c1d600d3a0cbe13b20dd418fb0e902b8326b90a942a5b2a481fcb05770f262a381b14214d255604c226071f3825c228a22c2d1f7029480cfd2184104f263a08d2a780001a2c600000001a290c054828501c3726c60bbd2c3044962c941ce124e42c0e13200000082852eb0c561c022035d7c4168616a000052ca0000a03ba2bef25c21ddb17a000000000000000000000000000041e80001b25e0000917d626e0001e212406fa139e2440000f0fe00000000206c81704812b001c78038082870c080030c00a950000600000c002000c100000838224003060004083001c01e0e2400a0e000050000302006400600300000a3008e2418005103890a00085020c0040002185860000287001c183062c0960e0448110000000a1c00c040801f023c0010c14682002e4870204000200170a28005170000087102c000020540500681000a04000120031800000800a005830a7418002005850c1cd800a080020400004 else 0x19176000090172191e030f1a7e1dad257e06400000001e008000061ee00000000000000018144000061de0000d188742de07ce005e1408040c1b400004195e51000000001c1be0001e0e20000203224c16228f14b8eb510f862012d39824942d301b620d990bf9c0df29622960000821ae534000051780001d04160c0409c11980000000000000001b09200000000000000008088000081fec2bc000181eba55e0000817c00007d5c0000bdd3e28e0001116a000171c0000000000000000081b200002286022dc0060000000041b8d212000120a27111e068c299a24782ce0000000041a120f7a1d3a0a19086d139a0f54c6640fa81c42128c053e13cf1513167b063e23f8e009282c1986172d0bc000000bfa2332096e154b1540000000051ea00900001d2080000000000000001f938e0cdc2a0000100e800016134000182085160000042500000b035b036008022b73095212bc23452ba0001d535402a20ee64a82271411cb29e42361236e2d682b39089427808c42103f27e00016166d02f80c9204202c5e1d800aa000092c71156020e81306253501082a9a1e4d12a0001c1490061a02771e2004751c6000050ba0000f0e4000090980000c192a0b4012fb134713c00000000000000000001c10e000010fc00000000820531e6d0840001629a0001e2d0202c31729e78027e0000019fdac400000000e04e816fd0fa297c0000419c60f1b29a0001b27cc0209078607e0001c1ec61a44185222500eb209bc070b4720000c0c79054a0e18011053fa15ac14e0000f2ad81e00000211261baf0a2a14d111c00011153255c0001407a2000e00a6243484862aae2119ece0000a0fc000001ac4002208460d46078e0d101f37103610c02404258218911ef8180c254000062560000000162820001c24ac0ac00000000000090d3024ca136303e00010186015021a8b2336116124c215800000001416c425a617a606bc0e6c2d501ca1149c2a67ab502ade123001b627a2022101bf202000194a93a12415200014)
def x383d10 (i : Nat) : Nat := (if i<2 then (if i<1 then 0xc4c2e0986ff245824c3ff24008261ff97548130dfecc2c4986ff481814c2ffb2c182617fd9254130bfe4c2c2986ff5d5814c2ffb2ea8261fed7248130ffcbb240987fe481864c37fb24c3261bfd9760930dfecbb02986ff61d504c2ffb2218261bfd9260530feea9b04987f74c5814c37faa2c1261bfc1061930ffcb8102986ff5c1814c3ff120a8a61bfd6160930fee988e0986ff441864c3fba62c12617fd9760930dfea830c987fe5c1814c3fba62b0261ff9700c130ffc48a40987bf585604c2ffb24b0261bfd7560930ffcb830c986ff1cc814c2ffb3038a61ff9205c530bfeca902987fe5c5704c3ff220b0261bfd861c530ffcb8304987fe25d204c37fae4c0a617fc9854530dfe4bb02986ff205864c37facac0a617fd9154130ffcb82c0985ff649864c3ff32ab8261bfd8720530ffc49ae0985ff645604c3ff2e6b8261ff9765c130bfe4c2e2987fb249814c2ffb2c40a617fd9148130dfec0b04986ff609504c3ff24038a61f7d5154130dfec10e2986ff615204c3ff2e690261bfd5320530ffccba40987fe480704c37fae6c1261bfd5020530ffaa8a20985ff658704c2ffb22c1261bfd8760930dfeb1302987fd585714c37f90218261efc965c530bfe4c2a4986ff645864c37fa40c3261bfc8160930dfecb304985ff655824c37fa42c32617fc9848530bfec8ac4986ff615604c37fb22c1261bfd7660930f7eb0ac4986ff4c5814c37fb3090a61ff9215c130dfec30e0986ff604304c2ffb2ca82617fd9154930bfecbac0986ff661614c37fae040a61bfc8720530feea9a40985ff640714c2ffb2238261bfd7061930feea9902986ff604704c2ffb2438a61bfc811c130dfec2b04986ff618304c37f92ec1261bfd8154930dfec0b0c986ff21d824c3efaa2a9261bfd5261930ffccb240985ff65c104c37fa20c0a61bfd8261930ff6b92c4986ff5d4814c2ffb22c32617fd9220530ffc902a0986ff609604c37facac1261bfc9161930dfe88304986ff655814c37fb0eb0261ff9515c130ff690ac4987fb5c9824c3ff24040a61ff95148130bfecbb02987f74c5204c3ff2eab8261bfc9844130bfec98e0985ff648104c3ff2e0a8261bfd9854530ffcb2a40987bf595604c3ff240c0a61bfd31609309fecbb02984ff261714c2efb2a40a61fd9315c1309fecc2e0985fb648704c3fb2a690261bf9855c1309fec9902985bf658304c27fb24c0a61bf92060530bfcc80e2985f764c104c27fb2a40a61fe97248130df6b9304986fe5c1864c2fdb24082613fc98545309fec8102987de255704c2f7b2838a61fe921481309fecb902987fa481524c3fb2a6b82617bd94041309fec930c984ff660714c2bfb2e08261df9755c130bbeca820984ff645864c2ff120a8a613fd9854930b7ecb020986fb249814c26fb2a40a613dd9320530 else 0x313eb27964e889b39308259a4ab49391252242e47948cc1142224443c085f109e20b440584e28fc01f0a3d707830eb01d0e38c46f68dbb1adc34f06850ce1198232186180c0717982e685af8b3616082b245548a89148a28704fe09e5138a26704b5093811e822e4443885510221eec3bb874e0e261b6034e86620c7218402ea85a30abe14d828204c9091c112804203fd07960e1c19d02ff05880a00122808403f006d004201700108048c07d00b6010800dc00b8000ffeb9a20987ff0c1864c3ffae2a9261ffd521c530ffe98aa0987ff661714c3ffae640a61ffd211c130ffeb9820987ff5c5504c3ffae6b8261ffd2144130ffeb8860987ff585504c3ffae488261ffd7258130ffe180e2987ff5c5204c3ffaa4c0a61ffd7558130ffecb2a4987ff5d5814c3ffb20b1261ffd9058530ffecb2e2987ff5c8814c3ffac2a8a61ffd7548530ffeb2b02987ff585714c3ffaca90261ffd810c130ffe882e2987ff585104c3ffac2c1261ffd2154530ffeb2902987ff5cd624c3ffac238261ffd610c130ffe4c2e2987ff485814c3ffaec90a61ffd9548530ffeb9020987ff5d9814c3ffb26b0a61ffd3158130ffecc2c2987ff595704c3ffaa4c3261ffd5348130ffe49ae0987ff548814c3ffae4a8261ffd9254530ffe90ae0987ff5d9504c3ffac0a9261ffd6154930ffebb304987ff5c1524c3ffb26a8a61ffd6148130ffebab04987ff5cd504c3ffa42c3261ffc905c530ffebaa20987ff4c5204c3ffb2eb1261ffd7558930ffec8242987ff589504c3ffae2c3261ffd9054930ffebaae0987ff545624c3ffb22a9261ffd9358930ffe882a4987ff485604c3ffaec90261ffd7254530ffeb82e2987ff485504c3ffb2ea8a61ffd9848530ffeb1302987ff65d214c3ffac4b8261ffd7348130ffeb10e0987ff661624c3ffa64a8261ffd7358130ffeb1820987ff585814c3ffae2c1261ffd9854930ffecb2a2987ff595824c3ff92e88261ffd6320530ffec9a42987ff65d614c3ffaea90261ffd7160530ffecaac4987ff655614c3ffaea40a61ffc9344130ffebb220987ff589714c3ffaec08261ffd1058930ffea9ac0987ff5c5604c3ffac6a8261ffd7620530ffebb2a2986ff61d814c37fae6c0a61ff97054930dfecc2a4986ff61c104c37fae2c3261efd6558930ff690a40985ff659524c2ffb2608261bfd7160930ffcb12e0987fe585204c37fb04082617fd965c530bfecbac4987fe441204c37fb2ac1261ff9655c130bfec90e0985ff65c814c3ff220b8261bfd5161930ffcb8020986ff605504c37fb02b0261dfd755c130dfec10e0987fe645204c2ff930b1261ff92058130ffc98a40987df255704c37fa42c0a61bfd7320530feea9b02987fe655204c3fbaa6b0261fed2054930bfecb0e2987bf58d604c2ffb2c08261fdd9354530ff) else (if i<3 then 0x1d1888610520e18831e0c16098402204a185300961c003b4202040c068001420407042101c2184c0814c0242486a1058261008813009440302604204008080d8600a092602d2868422207000a010f006187420042c240c0c2106c3010c0200e04c04302e5a101b000408148780260148c303810708442000d4202183010a185c0a0e60813009c00403604222185008701808661b0700140814100c05c1a84043038201802108404876009858482301c109840cc309810610a18106412101b858008010e0ca1850084c01383030d01058002840643059300a4c1d041c0b02140883400503250c0400ac1026028674460d820e05810d802604186042826020609840a0b0c033001408010f800d8181c0d058302e05483c1a4cc00240a043f0b001002101c0cc00602004320c240504040166e1307014308010c0e60e00301002181c10058308050901c0c46183b001408010d8061850200428249d802602020043824981005900e19c00301e50310f83800804cc0c0770700100998360e0c6028410021c0c0c0201f00170283d005070100c0c2c201dc3c0304300438989c0902820981002200c0c26600260430182e07c00601860300ca341c004c0870c041838011810c17070302780a10400880493b0008260400872703b86c1c00600870b8380c14c05080810470808050590100c0b6002610021c0805049301650af0b82c3c00502004403f000c182c182848ef23210f41fe83bd068e0ad418382b504a207fc0d68148e03203dc0408052ff95fde3f8a7ed4fce1f90bf0a7db0f08df57be867ca8f889ef83dd97b3cf5f9eaf3d2c7a06f345e5d3c9a79186d6de31bc437846efe9ded3b8d6a94e8f1db23b3b7636ebc9d64baa074b8e8f1d00b9d87370e619caa323e7256c730dadb8f971a0e29dc3f3855706ae031bed37ba6f22dda1b9fb7286dfedb599c5a57d6d36d9c9b203617647cd795ad0b5816ac2d529a99b50a69d4c8f9a57b48668ccd0f5a0eb3f467a8ced19c5b3506660cc41973b2d9654ec9f992f323e642ac78d8e631ac6306c4b587db0ae611cc171810afdd5f44bd544e2aef65d52ba0172bae0a5b68b5e56a82d2759eab27d63b2c3b5824af395c9ab6a5682ac60ad42ae6558caa2d52caa1553b4a6c54c8a95f525aa35d44e287c5070a03cd30a7cb4f449dc139626f12b509a4932ba6014b8c96752bea54b4a0e9355248a45f485a8fc91dba38e46ca8c8518522d8457089d1121221043aa86690b42151425083b5050204a40307fe0c0d9fa23ee07cf8f861ee33d627a68f2b1e243bd27700eac1d1d39a07278e3a9c3a38466fa0ddf89fc37086d6cd901aee35666a04d309a2f341e672cccc9970326a6454c6898a830fe6110c0d97ce2f385d84b9c16e22d845a64b2f16352c181d38ae895a82aec5510a8d94c52914513ca1 else (if i<4 then 0x52104009800d85cc1c080102ec1c050ce07c00300c4c02198410a0814082409e01018610300a10020502617c0280c046103986100c60100426600264472000813207820180205c0a14c0204806a18400a1b02063009086009806a1810d80098400840213b0018220c868c05840a080802436050c01099804820301002101e10064002e043060200b0212820e41a011907021c1c80065082804360c1c0b02120e80028408100604c0840801a84c302168613080c1a0ee19381604330e1d0026050a1803013001014430e4ea181300c108182011098108c11181060608c3816042840098027130b0903a2383c3010182f8049091c100202c98603810323e1e004a080c04008702e00260420600ac10804f01433a00981f0b921c06618500850b860284203818247876009c0646010c17433043103080501c04c02b064cc00380c0434241015e090c0a1009e01218080140980a1980c1061810980080106c10860026042b0586c2e160008103d05008c83810a0509938121403818ec3c013008102d08160460840a09a1930090008181e108003a8604304037800b903010c00108c143402064c07010f800208180e02600265838502038721821000613008704e009804081417c2c004008507306190043810c08a150e00100218134206050085830604430604c0844403b000906010c09870430006a130c0886084c2e18080141c04c0268580040400850605c0a30c508081402840278061a70007608340856104300080c161d8006508085131302004250b000608010b0308082b0102400280c081c1380038140850a850098007040c108006c0840c21818100d8101cc16105300b876009c8c03010cc1834330010075080880493300100215840e4301081860841000c02190c1814380d8008030086030103010205c1208c00340a60860098042108201702600986036009c0c021600062650c08103505000e83810a0c0981060e20a301604289c26041a220c800613a86043814980403040a1803c301a460c0c200609810c074184060586132000407040e07860340844702c1804210918140802c9c6c004098042306844c8001a86100220180e08600285080302e18c0308c1883a300a41284b824c0b860298061270141028d878002040908430189cc3021a11000981084cc0040084808302004c006cd80069300a40843809802615000ca108c085c01302004205831430b814081007601210218101d8026198700061310e103239004c0a1036c303040318032002e101a380d0b0a101c10c02300c04301c841c0805826050205300a44107010c03010c802605c618433040f0c02181017028c1ac12750c0e04301b000826010a09210142e080a0401680c219830380020204e02240ec1020d060b83850205c0e00084c08140e17028e84c28001a861002 else 0x70304300042c44a2c2c01122040c8d8610858d82c2618400980323300101e00080508101b416142c085a0e000e0820530004261030c2c00500a5066002004206c840cc0040086c00144096150f001402810e1028e000841190b00042714261c0c8c9d43086000850f930414100830c2c0078285c05043814223a184cc01286c1c00109c5616003c4c0a158205a182c085036004140450b000902184004260f004c020d87800e01028503e003804203b010c08130a2008082980028f00147600364c2050381f18400a1f193a878002102180260c24090330c21800601105108600084a18100a0620340886181c0b800210200d85810807020703240381a828c26600087c00109c388945842305810d1126600264c001408388944320b02141ec30201c325086000a0420481205c0050a8e27600084a18140806201b00240d902f80260908140607c741460121640b9082180021408110c8c1c190c02c817c00102840981c3819205c44228e0042042053004c02118342c001c10043505190b02100ec20205c32508131001f20500cc20d87ca0703507008c26010e0502018780460407802608088616000812a1130010090c1210616000a04314408800c900e1c0c8d8380028108100208078002308204a18303e3c0078283c050c0a04204010c2a1e00086c0070363c00702830281f0004221828e2703300042e002e4c0a111d80020f0004260d820d0802c9800a05c2404284216202e000830be0008162021824ea1932008008011214030101c10281a86040750421800c210019098c30100583008)))
def x383l10 : Packing := (364,3,6,0,0,15,0,x383d10)
def x383h10 (i : Nat) : Nat := (if i<1 then 0xd0b02dc800311bf40cb600820279105e921aa83e2c2b8009ec0de80291c21c3041f0bcf880b81dfe103b00b80000000011ae78a000003842e0000b02c8000003de307e26c08c25e83340000c04710101e3b410240885484c462a0cdec70cef8354c019a08108f631084412f6033000000001c298e1b77047e41c000000000f0cf80001429a000010400000341ca000020c9a81cc0000c048f8f1f846400220000e096882c80001e0b100005117c0000a1be28ebf846c000000000000586f16111e0b9a0b4f83300000406b000000003b3d9417660fd4824fc26b4171507b805780000000090ec00000c09e0000988b1856f2067c0ee88c9000038389cdb1000000002c37621430000705440001a01a300200000028a803f70c50079c0000000030a7784dcc0a2e1b538073482a23600000c054d4590000000fd98f10000001e540940000487f8000181ee98fce86b5c3d60000f05c0e1c00001e17490aea83d2c0b9414408e8354600001a1a0b1098000000000000801d00002a36820da0000303efe2c4e0fcaad27c4a580fa00003088a9460a308000000000000242c9605f50155005760f8f155e82500000e17c0000f05f08347c397a009b06e20563a08bc17e08d43063b825e00006024a0496004c0000a03c4418782020000e0c7c8040a2b7c17a0000542d000000000500a5023362ff01f5a0d5788390401216b609ebc529c407e120e03458779a399806ca0909452f23740206000000001016a61c1700c6984a0393a0e9000044489237b403c0000000000000206f000000003400c000000007429484160000905dd01eb625f711e0000000000000000000007c5a288698061c4d1000000001f1b70000000010351c17808a0cc135808721db8452583dac2e6509980d380000000000000000704e000000000987e80002c08d30d3f8bab84fb03a40000b0e7800000951b1be0060782a00001408d90799051881a000003059944ac000040a300000000000000000987780001c1fe60ada823cc7a5437e201f40501077f43328096481dfc34a036950933011b073222b391b9d2520000203f00000b0bda80ad8346c16d00003045800010162588d841e140809c1870104082050cd00820a0850238485800b74102280010b42043800424085160439d081668b000048004747080039a8b062801302040366c10080261420002380020a0028400181857008081020000f303c20d042818000301010200a80060c5020a0000906006000608003000800e02e400220000800000002000419b1e0040326001010608385000009d080000404000000c040001200000020090100002041e4830f04002930200706160830a02ac09d04140000000081000c200002c1810a00200001020a180448900149010208002160400022040821a0408b020080e000c080 else (if i<2 then 0x620c6062b07c74201e05d00004b8188104a022f102663052264a15600b6281d6a22ae19b88f400003f25c0000d804a1459019ee016106c78218a2f62db20000743cca3016025d8c5000014255015f000068071406b98c378511030e017f610d4854000004847a210d8968a41201cc0000000034799dbbe00003829c87ec00016008708efc6cc0001d16b91078000202590112787b387b461b335ce50c00059a436c4117f83c084ac205bd612f83ad84cc81ac01a548f7d062da34a719f90f35f7400001f11066618c15f032281d7801bdc43c0000e0890000000000000301f000019693016d20dbe8c400003c0ef0188a0c90c08a441bc0cdb8b9c82984076a177b90280159642841a6a0feec42f414a2563609dc801fc17ab15a10b1fc46243aa90f9d2509032b61bd6186e833905950850c1f4b85bc806e814fe0aa10585046b8229207cc0eb68409228581b041042837de29c70e280ea10327840a21e0608ab086202b421c29887287aa82a131ac8033b87c84319008810f2d405388796216709cb87ffd3a1110138b31070d005805c650257c4c2c10fe113e04c04735013780e8d0d6600e7012420fe9841ac146013291e75017b400140abf1d928dc6c3b601d42036501880002e942e1420000000000000618498e548270405ce15700000000300260000f0350000063ee508798cd000002050000000005038203f2e021f82fb63e00000a1b9000000002a0da00000000000030305a10950ed4874c000000000000447210370000020c0a44ab418e600bd01ed04300001e019501a186bd8238013f60aae849dc295213268db00000000000001881c86ae611831f800000000000014027f8d380000420e0000800f000035ae5c084a0936c5b68352f06a208378856025c4108c05600002a1420000701f00002406420ed28245035280e2000000000000000000000d866604282338804cf03f503d5413e0000208c000014403608b78e1800000000000030480000000000000000009370000180de000078663216da0d900002409821ca612260b0000000897e0ae10e0000004a2200000000712a50247c1fcb0012026b60e4e0b42022f8507823fc06dd0c1a0655014540bc00003835c02c20000000000002408200001032586c9c42980e200000178c000000008069907cfe058802487016843f23fe801d808800003c2ff4129b0418818ce00480cbd02f2c06d41e2ddf790b50827482b2620990be0052081a4f1fb70d70464203d3f19910a7f030a628a604748428000240c08153d0075033800000000003a584d3c1f2ec68000000002c0cba1700072400c0000000005025881094363a11e0000507348248f19700003c7948a776050302728548000090d0180544164438e2104d06408014c09aa168d0f4043ee80ed71f5e0d9e024460ab71118 else 0x323f4000040e400000c0ae21d9384d0000162420000a071800000000195600003c83c0000000000ee9052cebef81e382b90000143efe0ba6057f0526c0cc0000c0d2552a4c2fa000050d100003802400005016d42d40001a0e1801c4071684148028787ac018b229081050000644d40001a0850000000000000000040a07802800000000000000000000070a3000068718000181f07827d814c0000c08a000000000032ec189104aa81ef43d80000509b00000000030a60000083afe1cc000062ddb81a703a2cd5d00e5000004260000000000000083ec000000007014b818db05aa0ba803e800000000d0c87c494401e0000403f80003238e10c956656016f0157c1e14000603b1c0a9215480dd2c4fea1e8b0ebc8332867942dcf17d7006d438ee42764d34039381e78339421260e8001696851c16fb0148b12e6bd1d4a8000000000000120f00000000000000917aa0c680001c0dc0000000000000000011580000201c0421740448856800000000c1dce062000000001c2110000584e800000000a8403c59c0001e1ce00000000000000000507380000c25040c15e8b8000041bb01e2ee3a80000000141e4b0c2b85c80000405800003851d42ce0000e10380000000080a160c3f0652800600000000000000))
def x383d9 (i : Nat) : Nat := (if i<3 then (if i<1 then 0x9161930bee6909148130dde244955c130df664d2020530afe6a131481309fe2a551481308ff6859854930afe2a1105c130dd76555320530cdf660955c130afb6888760930dde648955c130cfb65892605309fe68890545308ff6a4810c130dee6512004130af72a13160930ede545855c130efa4812160530cf769d9320530cef651861c530fd654d755c130f5e5d5655c130cdf6557020530cfe641861c530c7f2a19704130f7a5c973481309ef2a1941c530dde2819520530cbf658810c130f5e5c4955c130cfe261105c130dde6552020530cf71cd93205308ff698985c530cef6a1941c530c7f65d7020530cdf65551619308ff6a55020530aef6901061930afe2a17060530bee6909054530dfa649201c130ff84853148130cdf6555320530e7e5c5855c130cbf660965c530df5645311c130afb6888720530dde254985c130b7e69c9054530af768c9161930cf729d93205308ff6a47320530bfa6897054930cdf54c9854530cdf1cd9520530cdf6558720530abf6981061930cbf6598204130ef54c49161930cdf6819520530df664d7004130ff44c5715c130bbe698935c130cfb649821c530dde6557020530cdf5459854930fd65455348130cfb649811c130cbf659810c130cdf6558204130cfe481981c530adf694811c130cf764d821c530cdf69d9520530dfa4809854930dde658955c130afd6847320530dbe6592004130fd35495348130cbf659860c130cfb28997605308ff6a19654130adf694810c130afe2a17061930dd754c9854530dde6552004130fd654c9054530cfb649821c1308ff6a57020530bfa6889054530bfa6897548130ede2957061930adf6948161930cdf65575205309fe2a5515c130cfb6498704130dde54c90545308ff2a19758930dfa48098485308ff6989854530dd768d9520530a7f69c1061930ef64c57061930dfa6497004130dee681941c530df64c49054530bde6949148130cbf619961c530dfa649201c530dfa6492020530aef6907320530afb6887320530d7e65d70205308ff6a575205308ff6a521619308ff6a570619308ff69c9854530bf66855348130adf6948160930cdf5949854530dee6517004130ef54c52161930cef65187041308ff6a19254130e7b5c97360930adf6949161930cfb6099204130cdf6555020530dee651201c530f7a5c57248130bf668c9148130efa5492060530bbe69891481309fe6a5201c530efa5c92060530af768c9160930df3649311c130bfa68951481308ff2a57160930c7f65d8204130cef6518204130adf6947320530afd2859660930cfb649861c130d7e65d20041308ff689981c530dbe659700c130cdf295985c130f745c5315c1308ef2a1941c5309ee690905453097e69c9054530fd25495348130bf228d72481309fa6889054530f5654d755c130 else (if i<2 then 0xdfe2a57054930d7f65d72041309ff6a552205309ff2a57344130dbf6597304130aff6956260530efb5d49260530d7f68d9704130bf728d7244130ddf6557604130aff2a15260530e7f5c57660930f7b5c57260930edf5957560930ddf6557320530dbf648965c5309ff6849854930dbf640965c530aff6857560930dfe2419354530d7f6899704130bfe69d6148130d7f65d7220530dfe5c09848530ff64c56548130ddf5949854530ddf6557204130df76495320530ebf5956260530fde2815154930dfe5c49054530ff64c57648130dfb649211c130df76595320530ebf61d6158930df764d7620530ff54c5215c130dfb649521c5309ff6989854530f7e5c17558930ff64c57054930dbf58d9758130aff2a16560530ff94853148130aff6a17054930bfe6849748130bfe69c9148130fbe480965c530ff35c93148130cff5cd95205309ff6a5621c130ffa5c92058130bfe6889054530aff6989760930aff69497605309ff6a57654530ddf6557304130aff6952161930df765d5320530dfe659201c130ddf6556320530efe589855c130aff6949760930b7f69d625c530aff6849760930edf6155158930bfb68971481309ff6a5611c130ebf6156158930fd754d7548130fd754d6154530f7e5c175485309ff69c98545309ff6a5211c130cff2a58154930aff2a17560530df728d9758930bf728d7258130cff65d8204130aff6848760930dbf659611c130dfb6497604130cff659821c130dfb69d9204130fde545655c130edf6156154530def6517204130edf5d55320530fd754d5220530cff6498720530def6517604130dfb6497220530cff65d810c130d7f65d7604130dfe5c09858930cff65d50205309ff6a57220530fb758d5358130dfe2419654530dbf6597204130efb5c92060530efd5c49160930cff6617648530fbe58d7058130aff2a17244130bfb688905c530fde5456548130cff645821c130dfd645611c1308ff6a57060530cef651821c5308ff68898545308ff688985c530fd654d70549308ff6a4811c1308ff6a487205308ff69d9320530b7e69c9148130dfa4819204130f7c5c5515c1308ff2a19154930e7b5c97160930cfb648811c1308ff2a57161930ff14853148130adf6949160930cfb2499760530adf6941061930cbf260965c5308ff2a1965c5308ff2a19654930df664d201c5308ff6959161930cf74c59261930bf328d7258930cdf6557320530cdf68d9520530df62419354530cfb24995605309fe69c9054530fda5495148130afe6808720530bfc2859648130afb68810619308ff6999854930f7c5c1615c530e7e5c171619308ff6a1961c530ff248553481308ff6a531609308ff6a57161930fd654d515c130abf6987320530f3e5c0965c530cfd2859261930cfe641821c530afd2859261930cfb289 else 0x56148130dbf685960c130bfe6949748130fde484955c130ddf6556520530ffa5c91048130dfe24161545309ff6a5521c530cff6617644130bfe2819548530f7e5c0905c5309ff6a56154930fb758d7358130efb5c91060930ff35c953481309ff6a57620530ff554d615c530bfe685655c130fbe5c16158930fde4c8955c130dfb685921c130efb6097254530dbf5d99604130aff69d6260530dbf69d9604130ff54c52154130f9f5957558130f9f5957558930cff660301c530cff6498704130fd754d1054930dfe0c1901c530df754d9158930fd754d5158930aff6948760930dfe2419254530f9f5957654530bbf6856558930cff261705c530efd5c55160930cff6159158930fdb5497254530f7b5c97358930cff548985c530ef74c57560930dbf6597620530bbf698301c5309ff69d9604130cff61d9158930dfd645710c130efb5d89260530fde54c9054530f7e5c1625c530bfe69c9054530ff54c5705c530bbf698935c130ddf6557520530ff654d61481309ff6a4301c530fde5457054930fd754d7544130dfe4c49054530f7d5c57654530ffa4817254530efb5c98254130dfe641521c530cff2617544130ddf6557620530dbf6596304130cff661625c1309ff6a5610c130dfe28d901c530fd754d7558930fde584955c130efb5c962605309ff6a57520530fdb5495348130dfe2819154930dfb5c99254130dfb5c99258130aff6a17558930dfe6457054930bfe2819558530dbf68d9604130fbd544965c5309ff69c9848530d7f65d7620530fdd5c55154130f9f5456558930aff2a17160530bfe2815158930f7b5c97348130aff2a57560530efe21d1048130efe585855c1309ff69c9858930bfe6989748130dbf258985c530dfb6496304130cff21d9148130dfe645201c130dfe5c09854930f7e5c0985c530ddf6557220530ff64c5700c130def6517304130fbd5857158130ff54c576485309ff69c9858530cff261105c530dfe6497020530dfe6597020530fd754d9548530fd754d6154930fd754d2154530ffa5489748130fde5949054530dfe5c09858530efb5c98548130dfe2417654530ddf6556304130dfb649625c530fde255625c130ffc5c49148130dfb699921c130cff6617548530fde5d56548130fd754d7520530f5f5d5655c130dfe2412154530f7b5c97148130fbe5c16558930ffa5c92054130bfe684935c130dfe2419754530efe5d52060530bfe6956148130dfb6497304130efb5c92061930ffa481211c130dfe65d2004130fb754d6158930bbf68d6558130d7f65d6304130cff645860c130ddf6899520530dfe65d2020530aff6956160930bbf6983061930dfb649621c130ddf5459654930efe5c15261930ffa4817548530cff2617254530ffa4849748130d7f65d73041309ff6a56520530dfe649700413)) else (if i<4 then 0x1f55de77711da11d25d887595d4274a5d105dadced70e4a191d25cca5dad5096edca1972c56087238a005c09c7f7149c397059bf36f690275191bb7564176b6e51b716d89b3f6c71b036b59ab36a6989769648fc68b1a0967c14645605509675d66266f9464666d978655591e643d8ec63758ba625d87e409d85b59885e6610961760cd81a5fa0a1960057e81f557cf56057ac50157935de976b5d497395ca97115c096e95b183390dfd6a3564168a599d66259888fc58fd626585d60857948343c155cc56a559051905a5560546455a07d5551552254254f053354be5295464523147d519144150794054f393ab4df837f4d9534c124931f4c193064bb428a0a28e10085c2174b511a34ac4d2f49c0618490d21618c51df47191a3179918024e114944709e743e50d642a45e60a2821718c50863750b0e418d04007d0569409c28a4010aeb3f84aeb3ef821713383bb0eecf913de037f3d2cf283c14eec3b24ea639e421739308d938cce1037b4a323750db10dfc28a3660d7f3548d2f3408cdf32f028a328cc8a31c4c4e292cc2b3020bef2f30ba9279cb862d64b4a0a28b272c38aeb0a28abe1798a910a28a6418c42d014b4a4b2800a320744a1928009e727389a125f89510eec28a24e091f23f08d90a2821722d889d21c084d20d08111fb82171f547b21e3c5cd1d8874918c47261c0c4921b586b31a68681195063117984ce1630618085c5ff17985cd0a2828a16f85a51630569151852d14004e713384b51248479118043d10403f70eec3de0eec398085c37f0d703390c802fd0a282d00a8c28a097423a085c1f407441ae05dc140044c0e6026c06e0104000cff549981c530cff54997605309ff698985c530dfe5c19158930ebf608965c530efb5497260530f7e5c1615c530efd5c561609309ff6a5710c130aff69d6160930dfb649611c130efe59520605309ff6989854930ddf6999520530aff2a176605309ff69d9204130ddf69d9520530cff6598720530f7d5c57254530edf5495161930ffc5c55148130efb5c98258130cff5c59854930efe5d92060530cff261985c530edf5955160930f7b5c9625c530def651521c5309ff2a57161930dbf659810c130dfe2417254530dfe5c0985c530ff64c57548130ff64c5765c130dfb5c99204130aff6957260530ff62a55348130aff2a15261930aff69c8160930dbf259985c530fbd585625c530dbf659610c130ffa4817648530def6516304130ffa4817154930ddf6555220530aff2a56560530dfe5c19654930f3f5c0965c530aff6a16154930cff65c810c130aff6988760930dbf659710c130ebf58d8758130edf6152154530fdd5451054930d7f6999704130f7e5c17154930aff2a55261930aff69c9160930efb5949260530dfe645700c130ebf58d8558130bfb6897548130ffc5c else (if i<5 then 0xc090c0c8ac1010861d1c0230030101f100815088ee00041a0c101c04100d608819080a0f8815040061821c0026301029111160a0c0770052381001060900bc00284040201099c008270301001080282620401910080c081703013182606700080080b9813e0005010960d000600840941204f8005ca1880a20601c01460700c080f090501804006280814032861014010191819400203013800ac18201c13032300010010606826020c1901040a7000c0c10030041821c0008302c1801404203a08080b304190108c0318020f00014101860020810600041e820283e342c182300520198002002104c050402838080c27040041f000c080f06404180c080805010405f0002808402c1701460581c0c00840140e010609d86020c1e05c412008203018101c0603234001b01060301c080d80010441826080c430401f181c0c00830300e6001420201e000d01060c0082e00100106070180b80a40600e05c0521834001802100d01040c020203013170002080c0645a1808220e8003810211c030283a008e04c0420180808170645c000a020c18038041882020323018171023c0018021000054041832098b0004004180e0280830101915000282030382201076080a0303e403804150c06032304c0701060c311c000a405024014626008207017101e038080c930006c0418080a080c05c408008204c041008105c18104e02080e01804181c0b83030101010278000a02138005c405808205010101606008309c131218080b8006c041b00c70260210870105c00262030100106060080f8c0c0104060200f8f8001410180e0808070101f18274000a021080a381301080b80a2033800400421180582030301301060001c020c06e00181f000e008304018e0014010a0f8080849c1317c20100502c80200a0c01641441350cc1e0023010e028200980c40140404c0b21822770008046021a9b8a67e3d78cde972a53d90fa4b28ffa37136556063d7a2e56175191bb7a280fbea21e86ea17e83256068199fda4d6944a7bf610a7928f5dc7f9e0d4649daa75b9d31a099ca67105a8d6625dadc7f855e6f75c0a6d49aee6a29a2665298bd58128023d716f960898325e975965d05de8a1996de5949166567953a535944a4ef935a4bd5dea0e992924818f5e4687da0749916643690763d78fea3d716fa3aa8e1e3788d7e346830633716fa31e81b22fb8b622bf8a722838980d98891df59280222e533621587ca1cf409d90f86b219385ea15771fd027409e13e846e10270e547d7d00749625e0e9834159083056627da209e6ede08581b2053809a00d51f56086d89fe0616d5cc1f55fbd585df9a60cdf817d01f68616df59582176b7d017e87c9d608519190f5dadf04598989735fc3de139dc7f71fdeeb70e50277b49eaf7a0976b795474978c9e195ba5e00 else 0xe0080c8c1907040a3000b8264c0004090606600098c0513380010802e00020c170640518400b8b0001040a008205c20cc000b82640c80d102f8000830141013380010a0c70006826406021203e2144380044e133801f0026081ce0040a099c00c040b040c03220111d10240a00bc0030541a80038602f00098f800101c1a0d400814080409e06080c0be001c01080803e204f80100a0203230380441860a03e205380121c06080db041918200c0a0e080a0803e304c1710480240c30178001062101c0201641338009068004040bc4288082438202216205f80010606700020c1701040b8080c8c0c07c4080080c8c130145c000a20b8171031c002030938001060c830020ec104040690c201419010627008204c05e007c00462e0012103e0e0a0c0e001209830180510260c8b8004040dc13c0020401022109dc0030119004e001c182602700309380103007090c0820098805040421009c00ec3010402f0020368004061183002700406c14e0025202006026307c14141826080402c40a027c00e090501f181a87081801804183161032304e0c100a060815c0010191160c16301419170008118304c20c02002026404c1017000200a3e001701460582620100506460e009030c24013801c16105010e00647009c00c0481840a01802600442410e0062605a20941b06013e0014304a0a09dc01005c00131d860c8906e00403f002066c10106026000e0c130101918300a38402700505024603e080ec10808c0038301404e007a0808201380014603700201820883220501310260a081f23040a026020c2406440c80a242c20e03220641811181e02c2101c10381910280270030538001460220c206404014600408c07c61600820ac3c00423053801809c00a8e0138018081008)))
def x383l9 : Packing := (537,4,6,0,0,14,0,x383d9)
def x383h9 (i : Nat) : Nat := 0x3c43088e4114c1db833e418f8d4205aac42c84c06291440000835c03251a40004012000161bc000581af072000041b3c0a409b4163c2379201084f118000244380260002c1c08000000214f40d8000c8d60003a8288700000000084018186918a190000401de007121c000780710af1162c41101e0000e168000707a0000e08a0072827c0d60002c2180000000c02bc2ec331c012e05d441c06d00080000000588858b5e2260089615187e00a90316050e0fc000161dec01a906a0a0445d84a105600000002879a06e41b1011e851ba4ca0f34170000c82ac44f2011030e00400038066c8fa0c071e000000006088805082f0c10684dd18b833000000ab20bf627ab4210d1284c02ff0594064f00020d800000006d64c4868780001cd6901a380f2074823e02d800000c350b80124873610800000005532907a2205d10000010e8596922a001cd05861940001a23707781ed039004f8118303d446c01040d30ddb404786a00013966e028000d02ac080000483f52477141410b8450000a1590290000e09359d8000084cf07d01f5000c86e60e20001c42c85c2097e02c0001077a0fee851a1a3c4ca0c621f0e416829e29c007c0000087604c0002dab384170eb4153827000000010d774033805f8fb31da412f847a0902100000000db05a686b8198000d80fbc535020599b0605fbd001000012012cf700028204229111c0908e3e2230f000848000080290e1c1040400480
def x383d8 (i : Nat) : Nat := (if i<1 then 0x2afcdb920b0aa2985d79b72815154930fe92a6902e4a8a61b5e69d53241514c3bac482a6b0aa2985779b72819520530deb2a6d1120a8a615fa6c89064d514c37b4d12ca482a2987fc1214c57548130cebaa6d3930a8a61e795c971545824c3ee8b8a62b82a4987dd1315c17548530aef172b092ab8261bda68953241514c2bf4d9120cb2a29857b9b42419354530af736848242a8a6197e69d31241514c379cd22ca482a2986f58a054d9548530e1f930b812cb8a61d9e241655d9514c2b7cdb060c80e29855f9b72419254530afd364482eca8a613ee6d0a0545624c3b6c98b2cb8060984df9b72815158930af736848324a8a61f1d595715d9514c2bbc5caa2b2a409867e9a74809848530adf36c51b2038a619fc2a571545204c37b8b8b4a48a409857b9b42419654530cef140d332a40a61f78545715c9204c3eb8b8aa2b82a4985fc8b35c910481309ef174a8ae0a9261bbc5c5a6245204c2afcdb920cb2a29877589054d2154530cf734898920a8a617b66d8a954d204c2fe459ae4902c0986f58a054d51589309f9974b926290261f744c570261714c33f4d12e2482a2984f5db528d72441308ff174c8ae0a92617ce6d0a0545524c2bf45ca40b92a29857b9b42416154530c5fb4ccc06038a61d3e5c096261714c33dcd22e2482a29847f8b9685655c130cebaa6d0930a9261f595c5525c9514c2bbcd91224aae0986b75a55c49160930ff824298aec90261b5e69d65241514c2afcdb920c9aa2987f5131484955c130af9966b9324b02615de6d891255704c33ec98b4e482a2985778b9484955c130fec2e2a92a2902615fa6c89065d514c2bdcda120b92a2987fc1214c56548130aef172a8acab8261b7a5c1a2241714c3ee098ae2b924098636d956888720530ae73684892ab82613e36d0a35c9624c33ac54aa6a8ae09867c9a24c49054530ae73685032a40a610df6d5a91cc814c2bac5caa2a9a40986769536889054530de3348a9920a8a618fa2a1925c0104c3ba4a9a404c2a4986799a44c49054530f3a2e298ae0c326197669d31241514c23bc5d32ab81029863d8a864d7004130c6db2ad10e640a61bd268953241514c28f6d9150cb820985799b42419354530ceb2a6d1120a8a614f36c8a764c814c313ecab4c39902986f49536895148130abb36e48326a8a611ee6d0a9545204c3cb8a8ae2c2ae098535db529d9320530f9a262b812cb8a6155e6dca0654814c31bacab4239902984fc5b128d7258930c6f150caae040a619ce69153241514c32bcd3aa6482a2985769b22819520530c4fb2cd2902182619d654da7241514c319ecab48399029857c9b22419354530de92a4d0aa690261b5669d53241514c31dc54328b80209847b9b42a5515c130c6db24d29023826195654da7241514c33a4a9b44482a2984f89b428d7248130 else 0x237000107b080c88068180263026017c00ee10181010700202e04c40140c880a38010190082031e00020c1185c000410140a0c0814021e0060300988098402b8010230282026010405009880c840285c0068007c0040a5c27000108017c00041813f00203201458240a7801810008203204c4e0006880c040a780101302020081e1206008006200b0260646e0005804180b030014604c0f8bc0010008302801040100a0bc0004101300a20160100c8c0702317800300507e00058041818f000507621c00051805030201601040600c880804020191005008207800320140c0042f80026014118042b8000a04c0812f28e4e9e2a6744f8e6961054f0edd191b66eb24722a537d84c8d61064d338769bc548aed2efe8548a9c8d4233e6619f191ac20a9c4175684610beb79454d089902a67c5d5153652844c81c8fead78a9b29422c256915353a99cf899146054d081933e2744d899125c54c711922a62b0a94df0ec54c15152ed054bfa7bef1054bb4732df854b6e67ac5d37af1152b2d580c9152a292a26f4a88e4548a91922a464a1e1522a4fc0c915c774549b73222a4b58a928a4a8878a91e82a4648e41922a4570a90da0c40055f9b72412154530d7d240542e4882615ee6d0905d9514c3e3cbaae0b2ac4984f9db428d7258130fe92a454aa6902615ee6d09065d514c3fa4a9a40baa42987cf1615c1625c530eeb2a6482e4a8a61dd654d31241514c379cd22a6482a2987759535c490545309f3b6851ae48826179e2c151595624c)
def x383l8 : Packing := (145,5,6,0,0,11,0,x383d8)
def x383h8 (i : Nat) : Nat := 0x69cd0e58cc99c8f601011703000195b92786f04a09f1f785e0ff06e1d000488000491000000112e19b8e01401b71eb1a202b00c16d0ac1c77b00061069480d20b513000c0800060ca9e107b15000000000a17000000918405022714d38b0580403050900
def x383d7 (i : Nat) : Nat := 0x2e00200b70020130bc00020b825e00402170020050ee107e0037000082000c8403420081198cc663319954670d7837d84a5198cc663308a2066003b8cc44662a8e06600110440000fd4153545715c9204c35c654db42416154530d559536dc90585514c33b1595b128d7258930e5e1722a571545204c3d344c570258985c5309f89c42cd72481604c31ce699b42819520530e7195369131241514c39d254da25c49054530b639c4241655d9514c25e3710b35c99258130de49526d8a954d204c33d2481b528d7244130d719536d090485514c25ce710b95456548130d719536d0905c9514c33e2481b428d7244130d559536dc90485514c2bc6710a054d5158930e5593169d53241514c2b5671ca054d51589309739c42e551595704c39c654da45c49054530c579a66dca0654814c338e595b42815158930d749532e5205c9514c24ce321b4244955c13083b8c86d0a9545704c20ee321b42a55148130c719536d0a9545204c29c6710a954d515c130
def x383l7 : Packing := (32,6,6,0,0,9,0,x383d7)
def x383h7 (i : Nat) : Nat := 0xf090b26608180000002
def x383d6 (i : Nat) : Nat := 0x9840081924480f2a0a9ae454ae2a8a409844ce361c42e551595204c28e91b4a9972902e4a8a610339da321b4244955c130
def x383l6 : Packing := (4,7,6,0,0,6,0,x383d6)
def x383h6 (i : Nat) : Nat := 0x1e0
def x383d5 (i : Nat) : Nat := 0x261d1505c4da54cb94817254530
def x383l5 : Packing := (1,8,6,0,0,0,0,x383d5)
def x383samples : Array (Bits × Bits) := #[(0x27f14021892009fc50086,0xd40e31a2181c35038c6886),(0x22202b2c0c6228880acb031,0x50aa04e50872342a8139421),(0x20006227746c08001889dd,0xf145b02f50d43c516c0bd4),(0x54c004028294d5300100a0a,0x20c3a4b802b0a830e92e00a),(0x10841040dcc104210410373,0x523c1845dc4e148f0611771),(0x11bc0801b480046f02006d,0x32931ca08a7c2ca4c728229),(0x2800081d63a00a00020758e,0x2251b818a38cc8946e0628e),(0,0),(0x4d5800917c10135600245f0,0x4d2c43475403134b10d1d50)]
def x383columns : List ColumnInfo := [(16,0,1903,0,11),(544,0,351,0,11),(576,0,319,0,11),(516,0,379,0,11),(562,1,332,0,4),(525,16,354,0,4),(540,0,355,0,7),(545,0,350,0,8),(256,0,1663,0,9),(2,0,1917,0,9),(518,0,377,0,8),(561,0,334,0,7),(582,0,313,0,7),(569,0,326,0,4),(864,0,31,0,7),(546,0,349,0,7),(788,8,99,0,4),(548,0,347,0,8),(577,0,318,0,7),(586,4,305,0,4),(581,2,312,0,4),(772,0,123,0,7),(320,32,30,1,5),(802,64,29,0,4),(616,256,23,0,4),(785,32,78,0,4),(519,0,376,0,5),(774,64,57,0,4),(614,0,281,0,4),(80,0,1839,0,8),(834,0,61,0,5),(538,4,353,0,4),(595,0,300,0,4),(551,0,344,0,4),(604,0,291,0,4),(833,32,30,0,4),(868,0,27,0,4),(584,0,311,0,7),(18,0,1901,0,7),(784,0,111,0,7),(553,16,326,0,4),(848,0,47,0,5),(796,0,99,0,4),(541,0,354,0,4),(572,0,323,0,4),(880,0,15,0,4),(86,0,1833,0,4),(565,0,330,0,4),(552,0,343,0,7),(866,0,29,0,4),(838,0,57,0,4)]
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
  | 12 => lookupWord 44 67 3 12 5 3 x383h12
  | 11 => lookupWord 195 795 7 16 9 3 x383h11
  | 10 => lookupWord 265 1075 7 17 10 3 x383h10
  | 9 => lookupWord 51 259 7 15 8 3 x383h9
  | 8 => lookupWord 23 59 4 12 5 3 x383h8
  | 7 => lookupWord 2 9 2 9 2 3 x383h7
  | 6 => lookupWord 1 3 1 8 1 3 x383h6
  | _ => fun _ => none
def x383 : Forest := ⟨1919,12,fun j => x383samples[j]?.getD (0,0),x383columns,x383autos,x383levels,x383index⟩
set_option maxHeartbeats 0 in
theorem geomx383 : graphValid x383 (boundsBefore knownx367) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=4) ?_⟩,listPieces_all (d:=1) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx383_12_0 : block x383 12 0 1=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allx383_12 : block x383 12 0 1=true := sx383_12_0
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx383_11_0 : block x383 11 0 6=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx383_11_6 : block x383 11 6 19=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allx383_11 : block x383 11 0 25=true := (@block_merge x383 11 0 6 19 sx383_11_0 sx383_11_6)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx383_10_0 : block x383 10 0 2=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx383_10_2 : block x383 10 2 36=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx383_10_38 : block x383 10 38 2=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx383_10_40 : block x383 10 40 36=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx383_10_76 : block x383 10 76 36=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx383_10_112 : block x383 10 112 36=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx383_10_148 : block x383 10 148 36=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx383_10_184 : block x383 10 184 36=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx383_10_220 : block x383 10 220 23=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx383_10_243 : block x383 10 243 36=true := by
  refine @block_merge x383 10 243 1 35 ?_ ?_
  · exact cornerRange_sound (by decide +kernel)
  · refine @block_merge x383 10 244 1 34 ?_ ?_
    · apply cellsBlock (ar:=11) (rows:=0) (d:=0)
      simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
      repeat' apply And.intro
      all_goals decide +kernel
    · refine @block_merge x383 10 245 1 33 ?_ ?_
      · exact cornerRange_sound (by decide +kernel)
      · refine @block_merge x383 10 246 1 32 ?_ ?_
        · apply cellsBlock (ar:=11) (rows:=0) (d:=0)
          simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
          repeat' apply And.intro
          all_goals decide +kernel
        · refine @block_merge x383 10 247 3 29 ?_ ?_
          · exact cornerRange_sound (by decide +kernel)
          · refine @block_merge x383 10 250 2 27 ?_ ?_
            · apply cellsBlock (ar:=11) (rows:=0) (d:=0)
              simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
              repeat' apply And.intro
              all_goals decide +kernel
            · refine @block_merge x383 10 252 4 23 ?_ ?_
              · exact cornerRange_sound (by decide +kernel)
              · refine @block_merge x383 10 256 1 22 ?_ ?_
                · apply cellsBlock (ar:=11) (rows:=0) (d:=0)
                  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
                  repeat' apply And.intro
                  all_goals decide +kernel
                · refine @block_merge x383 10 257 4 18 ?_ ?_
                  · exact cornerRange_sound (by decide +kernel)
                  · refine @block_merge x383 10 261 1 17 ?_ ?_
                    · apply cellsBlock (ar:=11) (rows:=0) (d:=0)
                      simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
                      repeat' apply And.intro
                      all_goals decide +kernel
                    · refine @block_merge x383 10 262 3 14 ?_ ?_
                      · exact cornerRange_sound (by decide +kernel)
                      · refine @block_merge x383 10 265 1 13 ?_ ?_
                        · apply cellsBlock (ar:=11) (rows:=0) (d:=0)
                          simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
                          repeat' apply And.intro
                          all_goals decide +kernel
                        · exact cornerRange_sound (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx383_10_279 : block x383 10 279 36=true := by
  refine @block_merge x383 10 279 3 33 ?_ ?_
  · apply cellsBlock (ar:=11) (rows:=0) (d:=0)
    simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
    repeat' apply And.intro
    all_goals decide +kernel
  · refine @block_merge x383 10 282 7 26 ?_ ?_
    · exact cornerRange_sound (by decide +kernel)
    · refine @block_merge x383 10 289 1 25 ?_ ?_
      · apply cellsBlock (ar:=11) (rows:=0) (d:=0)
        simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
        repeat' apply And.intro
        all_goals decide +kernel
      · refine @block_merge x383 10 290 5 20 ?_ ?_
        · exact cornerRange_sound (by decide +kernel)
        · refine @block_merge x383 10 295 2 18 ?_ ?_
          · apply cellsBlock (ar:=11) (rows:=0) (d:=0)
            simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
            repeat' apply And.intro
            all_goals decide +kernel
          · exact cornerRange_sound (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx383_10_315 : block x383 10 315 36=true := by
  refine @block_merge x383 10 315 6 30 ?_ ?_
  · exact cornerRange_sound (by decide +kernel)
  · refine @block_merge x383 10 321 1 29 ?_ ?_
    · apply cellsBlock (ar:=11) (rows:=0) (d:=0)
      simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
      repeat' apply And.intro
      all_goals decide +kernel
    · refine @block_merge x383 10 322 1 28 ?_ ?_
      · exact cornerRange_sound (by decide +kernel)
      · refine @block_merge x383 10 323 1 27 ?_ ?_
        · apply cellsBlock (ar:=11) (rows:=0) (d:=0)
          simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
          repeat' apply And.intro
          all_goals decide +kernel
        · refine @block_merge x383 10 324 1 26 ?_ ?_
          · exact cornerRange_sound (by decide +kernel)
          · refine @block_merge x383 10 325 1 25 ?_ ?_
            · apply cellsBlock (ar:=11) (rows:=0) (d:=0)
              simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
              repeat' apply And.intro
              all_goals decide +kernel
            · refine @block_merge x383 10 326 5 20 ?_ ?_
              · exact cornerRange_sound (by decide +kernel)
              · refine @block_merge x383 10 331 1 19 ?_ ?_
                · apply cellsBlock (ar:=11) (rows:=0) (d:=0)
                  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
                  repeat' apply And.intro
                  all_goals decide +kernel
                · refine @block_merge x383 10 332 2 17 ?_ ?_
                  · exact cornerRange_sound (by decide +kernel)
                  · refine @block_merge x383 10 334 1 16 ?_ ?_
                    · apply cellsBlock (ar:=11) (rows:=0) (d:=0)
                      simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
                      repeat' apply And.intro
                      all_goals decide +kernel
                    · refine @block_merge x383 10 335 1 15 ?_ ?_
                      · exact cornerRange_sound (by decide +kernel)
                      · refine @block_merge x383 10 336 1 14 ?_ ?_
                        · apply cellsBlock (ar:=11) (rows:=0) (d:=0)
                          simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
                          repeat' apply And.intro
                          all_goals decide +kernel
                        · refine @block_merge x383 10 337 2 12 ?_ ?_
                          · exact cornerRange_sound (by decide +kernel)
                          · refine @block_merge x383 10 339 1 11 ?_ ?_
                            · apply cellsBlock (ar:=11) (rows:=0) (d:=0)
                              simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
                              repeat' apply And.intro
                              all_goals decide +kernel
                            · refine @block_merge x383 10 340 6 5 ?_ ?_
                              · exact cornerRange_sound (by decide +kernel)
                              · refine @block_merge x383 10 346 1 4 ?_ ?_
                                · apply cellsBlock (ar:=11) (rows:=0) (d:=0)
                                  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
                                  repeat' apply And.intro
                                  all_goals decide +kernel
                                · exact cornerRange_sound (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx383_10_351 : block x383 10 351 13=true := by
  refine @block_merge x383 10 351 1 12 ?_ ?_
  · apply cellsBlock (ar:=11) (rows:=0) (d:=0)
    simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
    repeat' apply And.intro
    all_goals decide +kernel
  · refine @block_merge x383 10 352 2 10 ?_ ?_
    · exact cornerRange_sound (by decide +kernel)
    · refine @block_merge x383 10 354 1 9 ?_ ?_
      · apply cellsBlock (ar:=11) (rows:=0) (d:=0)
        simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
        repeat' apply And.intro
        all_goals decide +kernel
      · refine @block_merge x383 10 355 3 6 ?_ ?_
        · exact cornerRange_sound (by decide +kernel)
        · refine @block_merge x383 10 358 1 5 ?_ ?_
          · apply cellsBlock (ar:=11) (rows:=0) (d:=0)
            simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
            repeat' apply And.intro
            all_goals decide +kernel
          · refine @block_merge x383 10 359 2 3 ?_ ?_
            · exact cornerRange_sound (by decide +kernel)
            · refine @block_merge x383 10 361 1 2 ?_ ?_
              · apply cellsBlock (ar:=11) (rows:=0) (d:=0)
                simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
                repeat' apply And.intro
                all_goals decide +kernel
              · refine @block_merge x383 10 362 1 1 ?_ ?_
                · exact cornerRange_sound (by decide +kernel)
                · apply cellsBlock (ar:=11) (rows:=0) (d:=0)
                  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
                  repeat' apply And.intro
                  all_goals decide +kernel
theorem allx383_10 : block x383 10 0 364=true := (@block_merge x383 10 0 351 13 (@block_merge x383 10 0 315 36 (@block_merge x383 10 0 279 36 (@block_merge x383 10 0 243 36 (@block_merge x383 10 0 220 23 (@block_merge x383 10 0 184 36 (@block_merge x383 10 0 148 36 (@block_merge x383 10 0 112 36 (@block_merge x383 10 0 76 36 (@block_merge x383 10 0 40 36 (@block_merge x383 10 0 38 2 (@block_merge x383 10 0 2 36 sx383_10_0 sx383_10_2) sx383_10_38) sx383_10_40) sx383_10_76) sx383_10_112) sx383_10_148) sx383_10_184) sx383_10_220) sx383_10_243) sx383_10_279) sx383_10_315) sx383_10_351)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx383_9_0 : block x383 9 0 8=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx383_9_8 : block x383 9 8 36=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx383_9_44 : block x383 9 44 36=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx383_9_80 : block x383 9 80 36=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx383_9_116 : block x383 9 116 36=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx383_9_152 : block x383 9 152 36=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx383_9_188 : block x383 9 188 18=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx383_9_206 : block x383 9 206 36=true := by
  refine @block_merge x383 9 206 1 35 ?_ ?_
  · apply cellsBlock (ar:=10) (rows:=0) (d:=0)
    simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
    repeat' apply And.intro
    all_goals decide +kernel
  · refine @block_merge x383 9 207 2 33 ?_ ?_
    · exact cornerRange_sound (by decide +kernel)
    · refine @block_merge x383 9 209 1 32 ?_ ?_
      · apply cellsBlock (ar:=10) (rows:=0) (d:=0)
        simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
        repeat' apply And.intro
        all_goals decide +kernel
      · exact cornerRange_sound (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx383_9_242 : block x383 9 242 36=true := by
  exact cornerRange_sound (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx383_9_278 : block x383 9 278 36=true := by
  refine @block_merge x383 9 278 6 30 ?_ ?_
  · exact cornerRange_sound (by decide +kernel)
  · refine @block_merge x383 9 284 1 29 ?_ ?_
    · apply cellsBlock (ar:=10) (rows:=0) (d:=0)
      simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
      repeat' apply And.intro
      all_goals decide +kernel
    · refine @block_merge x383 9 285 14 15 ?_ ?_
      · exact cornerRange_sound (by decide +kernel)
      · refine @block_merge x383 9 299 1 14 ?_ ?_
        · apply cellsBlock (ar:=10) (rows:=0) (d:=0)
          simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
          repeat' apply And.intro
          all_goals decide +kernel
        · exact cornerRange_sound (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx383_9_314 : block x383 9 314 36=true := by
  refine @block_merge x383 9 314 6 30 ?_ ?_
  · exact cornerRange_sound (by decide +kernel)
  · refine @block_merge x383 9 320 1 29 ?_ ?_
    · apply cellsBlock (ar:=10) (rows:=0) (d:=0)
      simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
      repeat' apply And.intro
      all_goals decide +kernel
    · refine @block_merge x383 9 321 18 11 ?_ ?_
      · exact cornerRange_sound (by decide +kernel)
      · refine @block_merge x383 9 339 1 10 ?_ ?_
        · apply cellsBlock (ar:=10) (rows:=0) (d:=0)
          simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
          repeat' apply And.intro
          all_goals decide +kernel
        · exact cornerRange_sound (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx383_9_350 : block x383 9 350 36=true := by
  refine @block_merge x383 9 350 16 20 ?_ ?_
  · exact cornerRange_sound (by decide +kernel)
  · refine @block_merge x383 9 366 1 19 ?_ ?_
    · apply cellsBlock (ar:=10) (rows:=0) (d:=0)
      simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
      repeat' apply And.intro
      all_goals decide +kernel
    · refine @block_merge x383 9 367 1 18 ?_ ?_
      · exact cornerRange_sound (by decide +kernel)
      · refine @block_merge x383 9 368 1 17 ?_ ?_
        · apply cellsBlock (ar:=10) (rows:=0) (d:=0)
          simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
          repeat' apply And.intro
          all_goals decide +kernel
        · refine @block_merge x383 9 369 1 16 ?_ ?_
          · exact cornerRange_sound (by decide +kernel)
          · refine @block_merge x383 9 370 1 15 ?_ ?_
            · apply cellsBlock (ar:=10) (rows:=0) (d:=0)
              simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
              repeat' apply And.intro
              all_goals decide +kernel
            · refine @block_merge x383 9 371 4 11 ?_ ?_
              · exact cornerRange_sound (by decide +kernel)
              · refine @block_merge x383 9 375 1 10 ?_ ?_
                · apply cellsBlock (ar:=10) (rows:=0) (d:=0)
                  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
                  repeat' apply And.intro
                  all_goals decide +kernel
                · exact cornerRange_sound (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx383_9_386 : block x383 9 386 36=true := by
  refine @block_merge x383 9 386 1 35 ?_ ?_
  · apply cellsBlock (ar:=10) (rows:=0) (d:=0)
    simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
    repeat' apply And.intro
    all_goals decide +kernel
  · refine @block_merge x383 9 387 1 34 ?_ ?_
    · exact cornerRange_sound (by decide +kernel)
    · refine @block_merge x383 9 388 1 33 ?_ ?_
      · apply cellsBlock (ar:=10) (rows:=0) (d:=0)
        simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
        repeat' apply And.intro
        all_goals decide +kernel
      · refine @block_merge x383 9 389 20 13 ?_ ?_
        · exact cornerRange_sound (by decide +kernel)
        · refine @block_merge x383 9 409 1 12 ?_ ?_
          · apply cellsBlock (ar:=10) (rows:=0) (d:=0)
            simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
            repeat' apply And.intro
            all_goals decide +kernel
          · refine @block_merge x383 9 410 8 4 ?_ ?_
            · exact cornerRange_sound (by decide +kernel)
            · refine @block_merge x383 9 418 1 3 ?_ ?_
              · apply cellsBlock (ar:=10) (rows:=0) (d:=0)
                simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
                repeat' apply And.intro
                all_goals decide +kernel
              · exact cornerRange_sound (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx383_9_422 : block x383 9 422 36=true := by
  refine @block_merge x383 9 422 1 35 ?_ ?_
  · exact cornerRange_sound (by decide +kernel)
  · refine @block_merge x383 9 423 1 34 ?_ ?_
    · apply cellsBlock (ar:=10) (rows:=0) (d:=0)
      simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
      repeat' apply And.intro
      all_goals decide +kernel
    · exact cornerRange_sound (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx383_9_458 : block x383 9 458 36=true := by
  refine @block_merge x383 9 458 4 32 ?_ ?_
  · exact cornerRange_sound (by decide +kernel)
  · refine @block_merge x383 9 462 1 31 ?_ ?_
    · apply cellsBlock (ar:=10) (rows:=0) (d:=0)
      simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
      repeat' apply And.intro
      all_goals decide +kernel
    · refine @block_merge x383 9 463 12 19 ?_ ?_
      · exact cornerRange_sound (by decide +kernel)
      · refine @block_merge x383 9 475 1 18 ?_ ?_
        · apply cellsBlock (ar:=10) (rows:=0) (d:=0)
          simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
          repeat' apply And.intro
          all_goals decide +kernel
        · refine @block_merge x383 9 476 8 10 ?_ ?_
          · exact cornerRange_sound (by decide +kernel)
          · refine @block_merge x383 9 484 1 9 ?_ ?_
            · apply cellsBlock (ar:=10) (rows:=0) (d:=0)
              simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
              repeat' apply And.intro
              all_goals decide +kernel
            · refine @block_merge x383 9 485 3 6 ?_ ?_
              · exact cornerRange_sound (by decide +kernel)
              · refine @block_merge x383 9 488 1 5 ?_ ?_
                · apply cellsBlock (ar:=10) (rows:=0) (d:=0)
                  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
                  repeat' apply And.intro
                  all_goals decide +kernel
                · exact cornerRange_sound (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx383_9_494 : block x383 9 494 36=true := by
  refine @block_merge x383 9 494 2 34 ?_ ?_
  · exact cornerRange_sound (by decide +kernel)
  · refine @block_merge x383 9 496 1 33 ?_ ?_
    · apply cellsBlock (ar:=10) (rows:=0) (d:=0)
      simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
      repeat' apply And.intro
      all_goals decide +kernel
    · refine @block_merge x383 9 497 11 22 ?_ ?_
      · exact cornerRange_sound (by decide +kernel)
      · refine @block_merge x383 9 508 1 21 ?_ ?_
        · apply cellsBlock (ar:=10) (rows:=0) (d:=0)
          simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
          repeat' apply And.intro
          all_goals decide +kernel
        · refine @block_merge x383 9 509 3 18 ?_ ?_
          · exact cornerRange_sound (by decide +kernel)
          · refine @block_merge x383 9 512 1 17 ?_ ?_
            · apply cellsBlock (ar:=10) (rows:=0) (d:=0)
              simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
              repeat' apply And.intro
              all_goals decide +kernel
            · refine @block_merge x383 9 513 3 14 ?_ ?_
              · exact cornerRange_sound (by decide +kernel)
              · refine @block_merge x383 9 516 1 13 ?_ ?_
                · apply cellsBlock (ar:=10) (rows:=0) (d:=0)
                  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
                  repeat' apply And.intro
                  all_goals decide +kernel
                · refine @block_merge x383 9 517 1 12 ?_ ?_
                  · exact cornerRange_sound (by decide +kernel)
                  · refine @block_merge x383 9 518 1 11 ?_ ?_
                    · apply cellsBlock (ar:=10) (rows:=0) (d:=0)
                      simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
                      repeat' apply And.intro
                      all_goals decide +kernel
                    · exact cornerRange_sound (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx383_9_530 : block x383 9 530 7=true := by
  exact cornerRange_sound (by decide +kernel)
theorem allx383_9 : block x383 9 0 537=true := (@block_merge x383 9 0 530 7 (@block_merge x383 9 0 494 36 (@block_merge x383 9 0 458 36 (@block_merge x383 9 0 422 36 (@block_merge x383 9 0 386 36 (@block_merge x383 9 0 350 36 (@block_merge x383 9 0 314 36 (@block_merge x383 9 0 278 36 (@block_merge x383 9 0 242 36 (@block_merge x383 9 0 206 36 (@block_merge x383 9 0 188 18 (@block_merge x383 9 0 152 36 (@block_merge x383 9 0 116 36 (@block_merge x383 9 0 80 36 (@block_merge x383 9 0 44 36 (@block_merge x383 9 0 8 36 sx383_9_0 sx383_9_8) sx383_9_44) sx383_9_80) sx383_9_116) sx383_9_152) sx383_9_188) sx383_9_206) sx383_9_242) sx383_9_278) sx383_9_314) sx383_9_350) sx383_9_386) sx383_9_422) sx383_9_458) sx383_9_494) sx383_9_530)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx383_8_0 : block x383 8 0 3=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx383_8_3 : block x383 8 3 36=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx383_8_39 : block x383 8 39 11=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx383_8_50 : block x383 8 50 36=true := by
  refine @block_merge x383 8 50 1 35 ?_ ?_
  · apply cellsBlock (ar:=9) (rows:=0) (d:=0)
    simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
    repeat' apply And.intro
    all_goals decide +kernel
  · refine @block_merge x383 8 51 6 29 ?_ ?_
    · exact cornerRange_sound (by decide +kernel)
    · refine @block_merge x383 8 57 1 28 ?_ ?_
      · apply cellsBlock (ar:=9) (rows:=0) (d:=0)
        simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
        repeat' apply And.intro
        all_goals decide +kernel
      · refine @block_merge x383 8 58 11 17 ?_ ?_
        · exact cornerRange_sound (by decide +kernel)
        · refine @block_merge x383 8 69 2 15 ?_ ?_
          · apply cellsBlock (ar:=9) (rows:=0) (d:=0)
            simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
            repeat' apply And.intro
            all_goals decide +kernel
          · refine @block_merge x383 8 71 2 13 ?_ ?_
            · exact cornerRange_sound (by decide +kernel)
            · refine @block_merge x383 8 73 1 12 ?_ ?_
              · apply cellsBlock (ar:=9) (rows:=0) (d:=0)
                simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
                repeat' apply And.intro
                all_goals decide +kernel
              · refine @block_merge x383 8 74 4 8 ?_ ?_
                · exact cornerRange_sound (by decide +kernel)
                · refine @block_merge x383 8 78 1 7 ?_ ?_
                  · apply cellsBlock (ar:=9) (rows:=0) (d:=0)
                    simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
                    repeat' apply And.intro
                    all_goals decide +kernel
                  · exact cornerRange_sound (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx383_8_86 : block x383 8 86 36=true := by
  refine @block_merge x383 8 86 4 32 ?_ ?_
  · exact cornerRange_sound (by decide +kernel)
  · refine @block_merge x383 8 90 1 31 ?_ ?_
    · apply cellsBlock (ar:=9) (rows:=0) (d:=0)
      simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
      repeat' apply And.intro
      all_goals decide +kernel
    · refine @block_merge x383 8 91 3 28 ?_ ?_
      · exact cornerRange_sound (by decide +kernel)
      · refine @block_merge x383 8 94 1 27 ?_ ?_
        · apply cellsBlock (ar:=9) (rows:=0) (d:=0)
          simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
          repeat' apply And.intro
          all_goals decide +kernel
        · refine @block_merge x383 8 95 6 21 ?_ ?_
          · exact cornerRange_sound (by decide +kernel)
          · refine @block_merge x383 8 101 1 20 ?_ ?_
            · apply cellsBlock (ar:=9) (rows:=0) (d:=0)
              simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
              repeat' apply And.intro
              all_goals decide +kernel
            · exact cornerRange_sound (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx383_8_122 : block x383 8 122 23=true := by
  refine @block_merge x383 8 122 5 18 ?_ ?_
  · exact cornerRange_sound (by decide +kernel)
  · refine @block_merge x383 8 127 1 17 ?_ ?_
    · apply cellsBlock (ar:=9) (rows:=0) (d:=0)
      simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
      repeat' apply And.intro
      all_goals decide +kernel
    · refine @block_merge x383 8 128 9 8 ?_ ?_
      · exact cornerRange_sound (by decide +kernel)
      · refine @block_merge x383 8 137 1 7 ?_ ?_
        · apply cellsBlock (ar:=9) (rows:=0) (d:=0)
          simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
          repeat' apply And.intro
          all_goals decide +kernel
        · exact cornerRange_sound (by decide +kernel)
theorem allx383_8 : block x383 8 0 145=true := (@block_merge x383 8 0 122 23 (@block_merge x383 8 0 86 36 (@block_merge x383 8 0 50 36 (@block_merge x383 8 0 39 11 (@block_merge x383 8 0 3 36 sx383_8_0 sx383_8_3) sx383_8_39) sx383_8_50) sx383_8_86) sx383_8_122)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx383_7_0 : block x383 7 0 5=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx383_7_5 : block x383 7 5 27=true := by
  refine @block_merge x383 7 5 1 26 ?_ ?_
  · apply cellsBlock (ar:=8) (rows:=0) (d:=0)
    simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
    repeat' apply And.intro
    all_goals decide +kernel
  · refine @block_merge x383 7 6 21 5 ?_ ?_
    · exact cornerRange_sound (by decide +kernel)
    · refine @block_merge x383 7 27 1 4 ?_ ?_
      · apply cellsBlock (ar:=8) (rows:=0) (d:=0)
        simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
        repeat' apply And.intro
        all_goals decide +kernel
      · refine @block_merge x383 7 28 3 1 ?_ ?_
        · exact cornerRange_sound (by decide +kernel)
        · apply cellsBlock (ar:=8) (rows:=0) (d:=0)
          simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
          repeat' apply And.intro
          all_goals decide +kernel
theorem allx383_7 : block x383 7 0 32=true := (@block_merge x383 7 0 5 27 sx383_7_0 sx383_7_5)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx383_6_0 : block x383 6 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx383_6_1 : block x383 6 1 3=true := by
  refine @block_merge x383 6 1 1 2 ?_ ?_
  · apply cellsBlock (ar:=7) (rows:=0) (d:=0)
    simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
    repeat' apply And.intro
    all_goals decide +kernel
  · refine @block_merge x383 6 2 1 1 ?_ ?_
    · exact cornerRange_sound (by decide +kernel)
    · apply cellsBlock (ar:=7) (rows:=0) (d:=0)
      simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
      repeat' apply And.intro
      all_goals decide +kernel
theorem allx383_6 : block x383 6 0 4=true := (@block_merge x383 6 0 1 3 sx383_6_0 sx383_6_1)
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
theorem lowx383 : Lower false (varsX 1919) (graphGoal 1919) 13 :=
  strong_low (m:=1919) (cap:=12) (l:=[(0,10),(1,1),(2,2),(3,5),(4,1),(5,1),(6,2),(8,8)]) (by decide +kernel) (plainA (q:=383) (prior:=boundsBefore knownx367) (before_sound knownx367 validx367) (by decide +kernel))
    (index_root (g:=x383) (i:=0) rfl rfl (before_sound knownx367 validx367) geomx383 tablesx383 (by decide +kernel))
def knownx383 := extendKnown knownx367 13 [(1919,[]),(1983,[118,130,81])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem validx383 : Known false knownx383 := extendKnown_ok (m:=1919) validx367 lowx383 (by decide +kernel)
def x495d12 (i : Nat) : Nat := 0x406080802ffd30
def x495l12 : Packing := (1,1,6,0,0,0,0,x495d12)
def x495h12 (i : Nat) : Nat := 0x1c0fc9e0950441800000000003d3000030ae3140001100000000012a000c8b12f43811039050650c5c83a7644804d0000a28800000000012c00001980041200061000
def x495d11 (i : Nat) : Nat := 0x241c002202120a0e041540c12100f090502002014a090807050080818483820f5874183068296002830149010216140a50908070500848382810650040c1c1061424201e120a0e041500903060a4875c85ad3e464ec25c6a09400ffd714c3ff60530ffd414c3ff10530ffc214c3ff1c530ffd214c3fe48130bfd814c2ff20530
def x495l11 : Packing := (10,2,6,0,0,10,0,x495d11)
def x495h11 (i : Nat) : Nat := 0xc1a501962a489e8228000000584400000000000001c57c21e6310b462a2e1bec170000c08000089b8000000000160300012070000000000000000000000001428a0320000001e6d800000000006c6c06b60e602468479b32e12851cee086c620204aeeab236e1e0067255f041429e166830c982c14e1790aeb047023f00be0a209484f52b0e8ef09681d6005e15125b62b59a9470d0ab616108900fe09c85529946ee8bb7a2bca5ec0d481fa2633450830b0fc2d804d052a8b14cdf0b4a09c042c23409ae5c589381e906e85bf28369ef0566df036a8039901a0f68c740bb8baa05b8616e3f813291fb8a0aa411a06b388722e13a6c1f0000e8840bdce0503ae19613aa2f800101d800020af19262cb85a461f822cac8001a0c19c10e47036ad6000081cc92f8068000612000000012704a49a98a95d15a0007803e018001c0400000000242a2120638303315e0b00018003badcab88a421f800021380000003014ad71a3c856200808b80002285082e643890ca1d0704577a0b2178000a638000000000000026000000f8c000060000184060010000100800214000100400002000874230100021c00000080800c002000000a82000000400000000000000000408200000010600188060000500002030a002050000201000400000000010000000000000000002000018082020018000000000000000000400204000030000000000000002001000200080000010000001870000000000008000000000000000
def x495d10 (i : Nat) : Nat := (if i<1 then 0x6c00050483ca83028181e406047060f20540c20e0541c3828181e302840143040161a0f00064c10050810000883c80902e0c000f2a1f041b0b84401840ce05219c183c11810c61037824a0c0a0f0c902e07078688120ca202e0e08857038207a801830be081e5c10140c0f260b060007930606078c000506818806078906060b8c0a11078f0581400588170701702000c02b05834a2306000b8401e6048000c0f202c2a0e1e0d280f184c142030284830883c6090406f05810c840148038200c0f06014c0d050146070603f020b05014e07048670218c10441e80f03c160a0297041bc2064200a32001e0c02900e17c102433810883d181028010183c10601e8038243000c08380a7038641017c1604220f40201e0a0293050441e04220f301c1200c1017021005200017c0e0f0406079f000f06014807046040c000b814e0804834140528670200c105c220f38241012006041c05383c0800c08380a67e0c0ce014fea7e0bea9f02f587933bf5da8eab7413989c84e196fc9c09ba099e6dcb61cd84d6769f34553e0ce3658b2458acc365fdaf496e6b1d575a7c1572a90533a7c14a0a3050827c136a99e4ba9c09286702476a25d0dc8453f31ed0f165883b11d08e327023611544dc46c234c990cc105df2df967cb105712a894109924a923290607cc3ab1c10cd45d02a412b88b83e61390d305882720f506181fc076000ffeb9282987ff509714c3ffb24a0a61ffd421c530ffeba042987ff5d1214c3ffae290a61ffd925c530ffeb8a82987ff661714c3ffa8290a61ffd7210530ffeca242987ff5d1814c3ff924b8a61ffd4260530ffeb8b02985ff660414c37fb30a0a617fd9460530dfecc242986ff661714c37fb0ec0a61bfd8148530dfe4c282986ff605414c37fb0810a61bfd7420530ffcb82e2986ff609814c37fae440a61fdd9350530dfea1102985ff648714c37fa84c0a61ff9205c530ffc4ba40987f750d814c2ffb2810a61ff92010530ffcca240986ff65d814c37f93090a61bfc8210530dfec1082986ff611814c37fae2c0a61bfd9460530ffcb8302985ff649814c3ff122902617fd981c530bfeca242987fd5c5414c3fba62a0a61bfc7420530dfec2242987fe481414c37f928c0a61bfc9760530ffc4a240987fe645204c2ffb2420a617fd9808530dfec10e2987fe480714c3ff24090a617fd9760530dfe4c2e2987fe5c1214c37fb04a0a61ff92060530dfe410e2987fe65d204c37f924c0a61bfd9260530ffcb8042984ff661414c27fb3010a617dd93105309fecc0e2984ff65d814c2dfb2c38a617dd9350530bfcc8042986fe481814c3bf2e0b8a613fd97205309fecc242985fe640714c3fb2869026177d9508530deea1b02987fa481214c2f7b2810a613fd92205309fecc082987f64c5204c27fb2840a61bf97020530 else 0x812060080220308190791001b078c15004003c90003080b0003064818c1200324802001e050c940a0f4004480f8001832480029000f206502800b901406078c0a16088c14090303c80f00044688c203c3240306448107e08301928000c191817058307911000078649040be060a0e281414000a060a050303c6188203c01050b9b080f0c8c3704442060a17360400060890121b0c83f041d0b818238150601e06c0a0c3211c105d209c160c0c0a28)
def x495l10 : Packing := (100,3,6,0,0,13,0,x495d10)
def x495h10 (i : Nat) : Nat := 0x8014c2d587e562c008400050878237c1ee8048000b07d222ec40800000000001022007f10abe9488199036d321ecc0c12f993c12e21e88373078c044e1f71a1e95b40ef298f94719483080a12309c0000a027c180d45d0510001ea27089901700000001008f041c0b7e8f093c594be4c000000000000e50400000006807a4540001583383a8047c0ac44b383730d6407583a4093261600000006a270001a0bc00000000001018713de24b3656e1cd032688a000149d00280a380001ca230138b40e6102042442b98d4018ce20000382c409f82521c9406d90380001005880800c600000004815b0bc00000000000540e0000000504e22ec0e2e02b2875970aa01ac9428351062c0a4c1ff049f6d7e06bd48e81e663a459180b616eb01cc5bec4c00000000a10c000194ef0bb01a30026b35464000030aff06790846231505e80f6124c14a814605876e224f7032c862b133ace8903416dc078665c4c0410050d4a1bc084cb11f106e00ac0a3082844dc897816b07640d2e0b8800888654de85cd444ea2e0000460cc06e0592098edcf425d834b0bea23a9973838a08dc07f8b3a84766ae424119f80000000a211826d012e2a40000886804a8100e5f80000000241900e60975091b11081e4000000000000000446aa4cb0ae81c344d681990e5099243342040001cdd300c502a270cc1c5836036400010a104120000768c00000000000642005510af0000c07b809a8836a3104e6e1175330000c06080c8000715000000000000488f000000039897853e6caa17180579161036000000049889077200e810714a42e42151ca28000e0f8000384a99000002c007cb012c281003a1c8803a009880641900a421a007001211000c0800808001020038314140861c00106382000f063028d0604082023009d04043000628c0002242000a50001
def x495d9 (i : Nat) : Nat := (if i<1 then 0x18616313611d0fa0e10b409b08c055000cff5d198085309ff2a5425c530bfe69c9148130cff50997605309ff6a57210530ff65c543481309ff6a57250530ffa5089748130efd504985c530dfe6417408530f7d5c57250530cff6497420530efe609705c530ff65d13148130f7e5c17148530efe61d2048530ffc5c52050530fed505425c530ffa481425c530bfe69c9448130ef750d7160530dfb649421c530efe5c09848530dfe65d2010530ddf6557408530bfe6909748130aff68898505309ff6a57408530cff5d19848530efb5089260530aff6a0925c530def6517408530cff6517220530ffc5c49148130efd5c58250530cff2a19448530efe5c14220530ffa4817148530ff650d2048530cff65d8250530dfb6497210530cff261925c530cff65d42205309ff6a54148530ff64c5705c530cff65d8210530cff509981c530dfe509901c530def69d9408530dbf509961c530aff6909260530dfe65d2050530ef750d8148530ef721d3150530ffa4817448530aff6909848530f7e5c0925c5309ff6a5421c530cff2619448530cff2619250530efd5c49850530aff69c9460530bfe680925c530efe5d12060530cff1d19220530aff6909760530ff62a54348130aff688985c530cfe64184085308ff6a58460530cdf21195085308ff6899720530ef54c584485308ff6a58760530cf764c8210530cdf6119508530cef21194085308ff6a47420530cfe5c19808530ff44c57048530cf764d8210530bee6909148130cfe21190085309fe2a52050530cef21d9408530df648193105308ff2a58448530cfe21d9008530cef6517420530c7f5c99720530cbf658821c530cbf659821c5308ff6a4821c530fea5092050530ff44c52048530bf668c9148130e7e5c0985c5308ff6a582605308ff6899850530cef6514220530cfe641821c530df664d201c530efa48181485308ff6a54220530dee6517008530cdf61d9508530cfe481981c530afe6809260530df64819350530b7e69c9148130bde6949148130cf764d821c530cef61d94085308ff2a58250530cfe48198105308ff69198085309fe6a57008530dbe6597008530cef6a19408530cfb649821c530de768d9408530cfe65170205308ff689981c530cfe6497020530bf668c9448130cfe48197605308ff2a54260530efa5092060530dfa649201c530cef6119408530cbf6a1961c530bbe6989148130df55c593505309fe6a5201c530cef2a194085308ff6899810530dbe659201c530ef650d2060530d7e65d7008530bde6949448130dde6557008530dfa6492050530df664d7008530ff45c531481308ff6919720530e7e5c17420530cdf21d9508530cf764d8408530ff44c5705c530cfb6497220530ee750943605308ff6a48210530dfa6492010530ff04853148130fe25094348130 else 0x180a03c60540a0e81e403c00100a0c022303c13103084080a4008003c80b80c2044161000106500100c102820807830000f180a088800504a203c16044605500078d00038171f0605020305f81e0c607842201419102e4180a301810103209880ea0417182c02880a0180f183607880a6000f1d060280c30140003c6400419018405000078c1f08008281e30181006470480c050c0f05c40301420743c102c0c8c050440f18001382e30980f11060a81c305c070580f230608880a0140f18300001e360e0506c0623060540a0310000884000302a0c1503860720a050c1703c40b814260c0a03c7c102c0c0c2402840f04420140f101407880c0142218000781430640f1031c10140001e50000a10460784430000f08405204007880903c40c0260e8c0905c0f18000881e303c11170607880003c407c0a030c0603c40480a0501e4e0c10150607880005c0f190607880a06440001c0c0d04400101b07c0c0a031005028441830088c0005c40e8120781440540e101e1803820281903cbc150700609c09360881e8c212992b2bf4bdbbb8b9f47eb86b5947eb40b27b18affaf041fae1ad2aafa9647ea911fea32a7883981625d47ea55a32a0f9ec08c9c99b099797495b08c94291f29990625d8e38ca8a78a776c88486129985283947e8168077e449725d7c179e78576c75d73a71711d2766f42cb6db6b811d27668b34d67264f2b227662c5ff1c209b5d25b95a057d25d55a5415285054e225d4c94b049708c47e45b1fe41f34d25d4382b22b211d41f3e834d11d2991fe11d3cf11d3ac25d37f36634d32a30708c2e42cb2b21a929927625d1fe2301fe2171fe1db1c21a9)
def x495l9 : Packing := (155,4,6,0,0,12,0,x495d9)
def x495h9 (i : Nat) : Nat := 0x16ce000c1c60f86c00184bc16001c0142c812000422828819610001408000426603620a0c000ac000000001b031e25e68001ac4005e1422b4472da24461fe57e06001c2e60acdc46be84016494001020c2
def x495d8 (i : Nat) : Nat := 0x1d0f8301e201e14001f0604050003e080c80f180f0222000a01e2f040600c8c0c840d840481d01e3364cd0e8743c6210f843b750e87669b14e8c43a1d0e87361186c26007da5425c57250530beb36a54a86902614ef6dc84650214c29fcdb908c804298537db72119508530df62e2d2122902618fd5c4a9609414c3fe0ba24298a409853bdb72a19408530dee2e2d292290261cfa5c1925c8814c29fcda10ec8042987f89422a54348130ff42e2a1240a0a61a7e5c1a2261714c3fc4a12e2a1a409871f9706497420530a6fb6843b2a10a619fc5c4a9481414c3ee8ba262b8242987fc1425c53148130f3a262b8130b8a61d745c17164d414c38dcba328b8102987b89205094360530
def x495l8 : Packing := (25,5,6,0,0,9,0,x495d8)
def x495h8 (i : Nat) : Nat := 0x60
def x495d7 (i : Nat) : Nat := 0x37c26d5422a54348130
def x495l7 : Packing := (1,6,6,0,0,0,0,x495d7)
def x495samples : Array (Bits × Bits) := #[(0x71f100d000f1f100d000f1f,0x7176ab2010f176ab2010f17),(0x1a119432a11a119432a11a1,0xa094459c70a094459c70a0),(0x26609d041626609d0416266,0x446bb84280446bb8428044),(0x43b2010d04c3b2010d04c3b,0x3b8447ad483b8447ad483b),(0,0),(0xdc842c0400dc842c0400dc,0x48054c6ec048054c6ec048),(0x5842022a905842022a9058,0x58411a638058411a638058),(0x7608480013f608480013f60,0x7209003913f209003913f20),(0x7806220949f806220949f80,0x7803aa01037803aa0103780)]
def x495columns : List ColumnInfo := [(521,0,486,0,8),(128,0,1903,0,11),(64,0,1967,0,11),(520,0,487,0,11),(513,0,494,0,11),(579,0,428,0,7),(527,0,480,0,4),(545,0,462,0,8),(256,0,1775,0,9),(524,0,483,0,8),(900,8,99,0,4),(776,0,231,0,8),(652,0,355,0,7),(673,0,334,0,7),(809,0,198,0,4),(674,1,332,0,4),(610,1,396,0,4),(836,8,163,0,4),(513,32,78,384,6),(587,0,420,0,4),(840,0,167,0,7),(198,0,1833,0,4),(778,64,165,0,4),(650,4,353,0,4),(616,256,135,0,4),(581,2,424,0,4),(841,0,166,0,4),(384,32,78,1,5),(522,0,485,0,7),(684,0,323,0,4),(130,0,1901,0,7),(681,0,326,0,4),(517,0,490,0,7),(769,32,78,128,5),(897,32,78,0,4),(769,0,238,0,7),(192,0,1839,0,8),(677,0,330,0,4),(68,0,1963,0,7),(737,0,270,0,4)]
def x495autos : List (List Nat) := [[],[81,130,118],[48,33,133,118],[48,129,82],[96,115,133],[96,129,82,115,33,48],[112,33,99],[112,81,130,99,33,48]]
def x495levels : Nat → Packing
  | 12 => x495l12
  | 11 => x495l11
  | 10 => x495l10
  | 9 => x495l9
  | 8 => x495l8
  | 7 => x495l7
  | _ => emptyPacking
def x495index : Nat → Nat → Option (Nat × Nat)
  | 12 => lookupWord 14 43 4 11 4 3 x495h12
  | 11 => lookupWord 177 223 7 14 7 3 x495h11
  | 10 => lookupWord 85 319 7 15 8 3 x495h10
  | 9 => lookupWord 19 49 3 12 5 3 x495h9
  | 8 => lookupWord 1 3 1 8 1 3 x495h8
  | _ => fun _ => none
def x495 : Forest := ⟨2031,12,fun j => x495samples[j]?.getD (0,0),x495columns,x495autos,x495levels,x495index⟩
set_option maxHeartbeats 0 in
theorem geomx495 : graphValid x495 (boundsBefore knownx383) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=3) ?_⟩,listPieces_all (d:=1) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx495_12_0 : block x495 12 0 1=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allx495_12 : block x495 12 0 1=true := sx495_12_0
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx495_11_0 : block x495 11 0 3=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx495_11_3 : block x495 11 3 7=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allx495_11 : block x495 11 0 10=true := (@block_merge x495 11 0 3 7 sx495_11_0 sx495_11_3)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx495_10_0 : block x495 10 0 23=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx495_10_23 : block x495 10 23 36=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx495_10_59 : block x495 10 59 24=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx495_10_83 : block x495 10 83 17=true := by
  refine @block_merge x495 10 83 11 6 ?_ ?_
  · exact cornerRange_sound (by decide +kernel)
  · refine @block_merge x495 10 94 1 5 ?_ ?_
    · apply cellsBlock (ar:=11) (rows:=0) (d:=0)
      simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
      repeat' apply And.intro
      all_goals decide +kernel
    · refine @block_merge x495 10 95 3 2 ?_ ?_
      · exact cornerRange_sound (by decide +kernel)
      · apply cellsBlock (ar:=11) (rows:=0) (d:=0)
        simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
        repeat' apply And.intro
        all_goals decide +kernel
theorem allx495_10 : block x495 10 0 100=true := (@block_merge x495 10 0 83 17 (@block_merge x495 10 0 59 24 (@block_merge x495 10 0 23 36 sx495_10_0 sx495_10_23) sx495_10_59) sx495_10_83)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx495_9_0 : block x495 9 0 2=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx495_9_2 : block x495 9 2 36=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx495_9_38 : block x495 9 38 36=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx495_9_74 : block x495 9 74 13=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx495_9_87 : block x495 9 87 36=true := by
  exact cornerRange_sound (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx495_9_123 : block x495 9 123 32=true := by
  exact cornerRange_sound (by decide +kernel)
theorem allx495_9 : block x495 9 0 155=true := (@block_merge x495 9 0 123 32 (@block_merge x495 9 0 87 36 (@block_merge x495 9 0 74 13 (@block_merge x495 9 0 38 36 (@block_merge x495 9 0 2 36 sx495_9_0 sx495_9_2) sx495_9_38) sx495_9_74) sx495_9_87) sx495_9_123)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx495_8_0 : block x495 8 0 4=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx495_8_4 : block x495 8 4 21=true := by
  exact cornerRange_sound (by decide +kernel)
theorem allx495_8 : block x495 8 0 25=true := (@block_merge x495 8 0 4 21 sx495_8_0 sx495_8_4)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx495_7_0 : block x495 7 0 1=true := by
  exact cornerRange_sound (by decide +kernel)
theorem allx495_7 : block x495 7 0 1=true := sx495_7_0
theorem tablesx495 : checkedTables x495 12 := by
  intro k hk
  interval_cases k
  · exact (rfl : block x495 0 0 0 = true)
  · exact (rfl : block x495 1 0 0 = true)
  · exact (rfl : block x495 2 0 0 = true)
  · exact (rfl : block x495 3 0 0 = true)
  · exact (rfl : block x495 4 0 0 = true)
  · exact (rfl : block x495 5 0 0 = true)
  · exact (rfl : block x495 6 0 0 = true)
  · exact allx495_7
  · exact allx495_8
  · exact allx495_9
  · exact allx495_10
  · exact allx495_11
  · exact allx495_12
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem lowx495 : Lower false (varsX 2031) (graphGoal 2031) 13 :=
  strong_low (m:=2031) (cap:=12) (l:=[(0,10),(1,1),(2,2),(3,5),(5,1),(6,2),(7,4),(8,8)]) (by decide +kernel) (plainA (q:=495) (prior:=boundsBefore knownx383) (before_sound knownx383 validx383) (by decide +kernel))
    (index_root (g:=x495) (i:=0) rfl rfl (before_sound knownx383 validx383) geomx495 tablesx495 (by decide +kernel))
def knownx495 := extendKnown knownx383 13 [(2031,[])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem validx495 : Known false knownx495 := extendKnown_ok (m:=2031) validx383 lowx495 (by decide +kernel)
def xmd14 (i : Nat) : Nat := 0x100e0c0a08060402009ffd30
def xml14 : Packing := (1,1,7,0,0,0,0,xmd14)
def xmh14 (i : Nat) : Nat := 0xe64a1800070b872000000b1321b162b06000e00a12119d10000f70000000a09360000961271d02617a04166e73c05965767077a07914b63c11b08b7490a503a1a000000001f853803a5000
def xmd13 (i : Nat) : Nat := 0x220982a160e8781a1a088880c0a00d82c1e088880404208a403c130542c21110481a190f0280c01b058441207004521cf06434150b084401d0e098140418c04812108883a1e07044321605018036110781c12008e451d108742a1a0102808351084441d0e0682a1413020640416c02402028a0494060781a1e0501801c0a0803c0e088681406009f1377bf6b9921ce6293d3309a15800ffec0a61ffc814c3ffa42987ff08530ffe90261ffd514c3ff8a2987ff64530ffe88261ffc914c3ff240985ff64530
def xml13 : Packing := (12,2,7,0,0,10,0,xmd13)
def xmh13 (i : Nat) : Nat := (if i<1 then 0x4827500f80001854691018b56301000b800000000000000018e2b8ccc024000060168000000000000000680e305bfb51c81320331094c3cb21438baddb13c308b0a66bbb804c2050a025284260428823c82c00000000705a000000004040783be0a900000000000000002d4b0816681ca835800000007848000000007825d038800000000000000000004006000000006802000020df8000093280548000000019d130cdc3df685200004047000038cef045e02d984f2851933f40308330483c49534034f00f000000004881800030db18ca80000000283f80005858f90180000000000003bc90150000181700000000000000002862f3900018800023823b2a00001b5b00002519800018187d14130d0d53631900006b3ea4102057800053acb919d0112855fa8e800000007859e80280002b00800068bf3341eb330000000038050844585d6853000348de7014d840d81b403ab0371309e032000050938000000018357817c839f81183a35395e3a508d300007060f82b4047983dc05ed32bb0b20049d399e8d59b5bf14b2d3c8000201ddb248b501829181d1b9deb92c13c9b5c8006884fb00c4028105cc8c0c8c7000008074048f01080c1c355800078d8f33ff84ad0212810702c983e883430d9c83b4813d10ed8d65804602e3000ebd1b021d0d2d098033888b872d3000040b4c15c783008dcc84a3b150000303a2099fb977b5153d8a05fcbdc68563b4c8014683e30233801881a2837b51068b16029b809e033a3b7d85c411400003028f84198624309385af00d901290202844e31400b98846b031d008d321702f80006b1f80005b3a20df301aa003c38f1001000078123832a8ada3d328d4e323684bd85160434804a0002849485e0344531f6d0ee81fb853e826401c7314dd5c331b80c5402a502090d1084b404e208d3b387b36682be00ee85dd019385753072856d82eeb1b4096538eeb560861f03c9bc2a015d89a9845035d501beb4b400b00279ba7782d0b4098097bc2082483a6981e45d15bc5404dd036d08e90313861004cb03f6838280a133a9808703d18079b491043e022409a5050584d105f704eb3b0c00ad354b8597b4afbdd682f6c5c034c000000005b44a8db909933159b3e5b2028607b25581ecbc4888dc3942baf801f300d605280c390268bbc202280367ba2603948058855482acb1ce85b3819b80c820000006041010218000091804100022400400267000017280000c00f16140110008000323420000ec0830000285000c4850000000260460200140050230181062c28e0004004080c1050000080043402708344830a001800c0400028003820200281021030500081000200009080011a00040802c0018004040800e100010000000021800002004810200100000c000002000c0200082020c6840a08000 else 0x68d388b8f33b00000000000000005046000000000000000000004c140000000000006041385800000)
def xmd12 (i : Nat) : Nat := (if i<2 then (if i<1 then 0x3ffd8254530fff6a1104c3ffda148130fff645514c3ffd5020530fff681514c3ffd9544130fff649914c3ffd8244130fff4c8514c3ffd2060530fff654214c3ffc5224530fff481914c3ffd8548530fff614214c3ffc8508530fff614914c3ffda960530fff4c9104c3ffca954530fff285204c3ffc9214530fff545214c3ffca264530fff4c5514c3ffda864530fff481514c3ffd5060530fff689514c3ffca564530fff648814c3ffd5224530fff655914c3ffd1048530fff661914c3ffd3148130fff601914c3ffd5348130fff289514c3ffda564530fff600214c3ffd3164530fff6a5214c3ffd9260530fff648514c3ffda548130fff6a1204c3ffd3144130fff148814c3ffca960530fff2a5214c3ffd5144130fff208514c3ffda954530fff2a1914c3ffc8524530fff608914c3ffd9244130fff601814c3ffca548130fff441814c3ffd9844130fff601214c3ffda544130fff540214c3ffd9144130fff645214c3ffd9548530fff681214c3ffda548530fff60d104c3ffca848130fff681814c3ffd5344130fff480814c3ffd8214530fff481214c3ffca548530fff480514c3ffda264530fff541214c3ffd9254530fff54d914c3ffda244130dff6a5514c37fd3164530ffe481104c37fd5164530dff541914c3ff99148130ffe281514c37fd2164530dff6a5814c3ff98044130dff2a5514c37fd9524530ff754c914c37fd3264530dff60d914c2ffda014530dff689914c37fda948530dff615914c3ff9a148130ffe661204c2ffda948530ffe4c9204c2ffda824530bff6a4214c3fed2048530dff649914c2ffda214530ffe295204c3fdda354530dff289914c3ff92020530bff688814c37fd8064530bff68c514c37fd9220530bff68d514c2ffda954530bff688914c37fd8264530dff655914c3ff98348130bff695104c37fd9224530dff695914c2ffda344130bff680214c2ffda048530ffe601204c37fda864530dff54d914c3ff9a548130ffe4c5204c3ff8a848130ffe649204c2ffda508530ffe600914c3ff95148130bff681814c3ff98008530dff661914c3ff92014530ffe2a5204c2ffda020530dff295914c3ff99548130ffe609204c3ff92048530dff648514c37fd9260530ffe601214c2ffda914530ffe54d204c3ff8a148130ffe480914c3ff9a848130bff6a4814c3ff92060530bff694914c37fd9824530ffe601814c37fca864530ffd545104c37fd9508530dff441914c37fd20645309ff6a5814c27fda9085309ff695914c2fdda314530bfe680214c2f7da508530bbf698214c2fbda420530ff64c5204c27fda944130b7f69c814c27fca9605309ff6a5214c3fd953481309ff6a4514c2fbda4085309ff2a5214c37f920645309ff6a4814c2ff9a020530efe601814c3fe92048530bf768d514c27fca954530 else 0x17c0702c001905530431103b0f4300ac281b812558082ac61988a1e07c0903c070007c125028c2b1043813816020fa540aa8100108781f00c0423688154b0ac43158102a9510e092105c2088c1009c0c18c008a21c12580901e000d6020cd1404a2036200981f03a1f02c0301049404e0a42e0e43823442138121980824cc0d0342287c001909a8a401342b0b43b0e43111816038004c09301f40d07c028e08c19a29008029806040910e049f05c1c14223010680b385612025806040a31c761a036200921f02c070009812530c02206c2813816004382a0fa804a168802702c002321c1f483e84601470460cd147a1505a1811c1303a2187c0700c0968181342a114350f81b1180e05802d0922087c008e228260490c331043812c2e0580a540aa41f0120721f01c00190a18a4824024060a6034503e04a18661687c0f0281d03c05a2c001f04988490a43e02446004504c0925030268541e86a230361f01c0b005e004410a438358091404a2046158706b010668a02500250b4381248e018094410a42509300c0423688153e1183c120c60580c180923044228ac001504a8738290440e0c6028182e05a10321a05616086201401f02c04174301268578250d81d1180e05802024c0c0bc008a21cc0400f8250d81b0b81603802704c008e228815e118181780114439f05c230302f00228873e024411406900400d86a1f02c0700381015c0980914951b030ac1621b0002ca23e0208812309304c0e86a1f02c0700400801b0b43e0580e00702007c0f002280b238e4510e068c09078403d0d81b0f81603801c2bc0c86c030102ca23816446018082045180402286c0f01c0b00380803d0d81e0580e00701304a1a85c0b01c00e0200c02e0580838049e02b3fd97ef4fc1df633e997c88f80dee13d777a94f335e4b3c0f77b0ee5ddb03b157594ea4dd2939df733ce59d7393930713ee1a1bffb7d26efadbd9b32b62e6beed6b1abfb53e6a22d369a4cb42667b6cee19bbb354664eca81939b2146392c6718b2b12e6216c2d9844b0345fe6bec97b3af305d66b9c9709add25abeb4a1673acc4591ab0415ecab4855beaaa151fa9cc5316a489475a8be510ea1913f3a79c4eca9ce1367a65c4b829511263a44048128e59196a2b044ca88410eca16641d282a0adc203f3f987d64f781e873c8c77c4ece1d47399471d4e101bcb36ec6c5cd571a31337c65a4c761883305c5f14ba416e92cec585cadc15592a305294a0513ab265c4b1492e11fd235044d487010771ff43e947940ed31d1038f46f90d891a40330463b0c0317202cec56e0a7d145026ac4a608d9110820bc3e807850e601b9434806090b6815cc28a04e708a21270228842407b20e601a6832a05aa0a2811f821c040606e00b6812c01c202580258000fff548814c3ffda354530fff549814c) else (if i<3 then 0x48f800320a8c0d4250802e87048c860280a8f00c0b01050843012c2b0e48d0d4402b808280ce05803700a38140489843100490f03c130650e0926096200981c1983012390d808160a130021c18098122e058060248a125c009e05070210c04e1183e02058248c00872bc14205c0b82ac430f80032092086c0588c0014054d0260006b1016824681185c001fc068a824e4360004828091585c1e8761c1102d0908412c04a24319800284381a138246a1c170482c219040270102d243600c384c048246027056141a0490842413c0b014317846018383009140dc200b06287048c05828090f0002702c04142d0c04b0ac450e0a8280d0258160380330003f01c0814281e82610c421382606c28520b83f8160380380b098190681440e0cc070202558010e13b440a158561c1208509c04170450cc09405b100a02a0d02481c1980e0404af0141c0d02c14048c818420a824102120fe0147514a0250cc0887050b8030a4f0284a150707414048b800280a8c1b02708621030490506813c0b0143180ab10c3e0004832091f000588e024152e000a026091304c0d0841c12c0702c003305d502b0b0431103b0e0a602452180aac8680f05a1708a21070248704f020330108c127c10c440ec38138180b80915800240bb0868218881d870740d063024330104980a30d01b0ac450e0490f816038004c093509c0b01430122c0ac2c10c401203e02456001182ebc13034168841f01c030208417540742d0ec42104401805e058081a09310941302c07000a4183c0809310c383580d1404a20406b01a28092c0ac2c10c401603e04956021182ab8158581d87042864412ac0b01034156611838340a11c059b04c0d0542017c0302c042307d503b0e1260981d0cc2b1181603802c146158881d03c0b0104f0007c125c06c330a0490f816038004c092a862150922287c0b01c002604940a6044383e0a8646217002208706b0122809410a849100ae004510e092305c2013c0814c050c049142b0b443100a10c43e0580e0013024cc208804c09c008a23814410e0202503e0181028c7230441302c0431c00170490128560be040ae001830e840c1fc068841f0006426a2938290a098120a111806024502aa21a056160761c086200dc090cc041260340a6104460e43914950164702ab0bc1fc0688c001909a8a440d841118390f4281284e0580a540ab2864268522087c0b01c0019055442e004410e0a60245012881585c130309686c0b00c041550134431143b0e4310b81603800320ab186614874400dc0b014a8154813841118390e0c4138141980824b810126158805301a281f0252c2b10c382f81603800320aa4122170022087c0426228094e0b842120910e059b05217082201302702c030108c125d0cc350ac2910c42110390f438198160206824f6158861c else 0x1882a9583e092134460380514a62187410120c4180550905f02c052a625655c2248c1284e0580e009811030ac118250905412c0b01c0168401383b0e058246c001305012202e0ab10c3e000483209200d4170102c1a048d8460e866020c024621988c018709809048e43e000a024402f05a150880c120241309b01c0a0c660083e0547028521b05614098449140c1406417c0702431a05e00068320a9604c001a03428048d8010e0482809160f4901a05302c0700382a9202484e014550e7c008704426048b0201380603450346615870849105c1504909c0702c01605a0706605808286c0104c0509048a81e004393c0d140f41308a218821c298241705019c0700229c43600c38280a97086218705c1506009c048a4a94816000c82a442409c218841c1943012403783d0ec3c2209122818120c60381218d0a7044118861d09c0c3104818c0817c0700710cc76000a024502f0003426048b02600c403f80d15049c85c001905488210c04e020582862230009812220706605808285c0088a1d8702412350cc40340a02a818250660580812b0601521b00c2187))
def xml12 : Packing := (198,3,7,0,0,15,0,xmd12)
def xmh12 (i : Nat) : Nat := (if i<3 then (if i<1 then 0xe1f2d850bc1de5c198c04c6c048bb7d9812470916416f50fa68113e8c3d03d106f7e40461157dddad115d4c34f702bc000000001c013d0d37d945d6ca682cf715e640c350bca89b7811e958713053e4b9d50193454057d0b490860b8ec74f60cbe1f5b406d95a11d0555da5cb017bc0f4b7d9bc2630000247d3a0e985f6b0000000000000140e5602100000a7fad47734326ec3dc761c80000212a5c43222e0802c8e0f6e800800002c119016200000b0bb7c6e60000000000000103ebd029c0000000029cb3b07d80000b054608e66067581f2906b38309713d3df7790de7c023f2f1f5adaa0a061e25d0b26db600000182e640f97cbcb00001907190bec0000f033c01a2100139d3700002d5db50f740000000000000d020687e9864aa1be7c039f5e9b30ad38361d0de3c334700e941d57010d435107d1000007190c9acc632a6c16376204000052cc0408ad7d1c00000000000000000386c5a019801230000040b5c3c62817bc65d4c72671a0bc0f8400914394e0cf5410ee0b451f8510c99c3b8000000000571e00000702f006d59699ac38e000000000000000000b63b601010000281473145b839861e9c878496d5c1db650ea9595ab0c16c055116a38214f1cc7182400001819f00003c6a2c065381a500001ddd9f770b83bd20c3802525737a80a240608980af65aa1af39694c000087bd1c4a020f1c0000f6c8a033b1047b87ba06e99df3c107f80000b0edbda8f043304000c000026200a00002f00360f060218089f0d020513040706230a0901410408500c00070000010d310b00000cc60619202266011401350000500302001054003629010129000001270202095600081b7a1d06262303020b970303250005453d000c232b0008000e25003408026004200303062d12001905271604001c441c0d0a49102204190c06071e001600090200702234050814001e03170f03190001011210041518040002084a4f000004750103050303120a01190000000904003c08090900080500065923122501002200020200331e100805010704020400122c317c080c400b0105000a02010b071f270208070806025d00141e05000505000205010200050314081b010800090512060023070103071a4201000c0143120b2008052f09040107300a30100a000002001a83000b01160226214320ae052a00020a080016010c07000100000102021d07200a0c020c08021215040100000e091c0104051f041d00033e00070001052b0b10637301071c1333040004090a0e000005020108040001041d03130d422d0205002b01010a020902030e0207030e011b020800030203010201050100091501010c0306001505000a04002a0c03310f120000100501110b0e06380518000014010001020407330804306d0a180201001a0e0e073c050b0909120200 else (if i<2 then 0xc0000006d4000030c015d050000287b1f61dfc0cb40854000026c380000a789283ad62da40000308191abc00001c11f00000000000001edea58f40000000000000060cb40000000031b2e767fc000050094c086b43ae6e0271ee5185793c440000c043400000000263450000100ab00003c242d018b84bd00000df7b3723104a6400b50146003084090ba42000000000000000000340b1f1365c00540e72c367f0e9700dcc08700000e607c0000000011ca38071c000091e35006f703420202e0adfc0290000381e5000038044b1dc2025a33f60c366f076302a510ab00000f0dba830d00000062ff09600000c1c84d74c111e686ec705a800000000259fc00000412fd7ad40000a68ad9bbeb6f68c49ea024800007018442c630ac1c0e3005818211205b7c1d0e0c548234d6932409eb6886808d057cfcbd4f0dfa43d270e16c154e16ea837b00e9082550000140c7a0d222b7c000011f65421ad830210f400000d1558000056b00c3770000207900b9840000c01d7da77b07b55a2f564688190f10c2e3990000300eab08430632705f747e35023840780000042bbb0a500000205850336c046c830f911e000000000081d690a56191800000000000001c74c862340000b3eb800000000046da302fc000000000c1c965a83822d2136b80e2a0acc0b7f00000433500003834c2765e04e6000039adf207bc0000417bbc764905b39ddf268e00000000024732261372b40000000000827cd192f205a28679906185fc0f0d250bd58032901f467be301b921848000030150477fe647c0000503ddc3c880d8b02a600001c0e6e1296c6a492c3982c0c0a7d035890a6b2f9f8ae750074302cc9bdd803b1876e96926017c766e4000000002c2fa6b4c19ca547e761d8d41a1a000f000018d1341ab7028d9056c0000000012cf0001b0c23991f97c48920ae9839100000000090106c003061600063b0700000011df00000d0f52c2cc707e800004054840d3a07fd03d9200784135306fbc3b4c050a0291b703549ad46a16825b56a6304c9f0eb28706d8e960125e005162c5000008271ca4ec0d4db73a0825680f9a4138000010275e7b6400007ac3c000087c4c000027238000030fbf1e8560dc041da123fac3c050cdf4026000024729002f95a418031b81e4b07e1424070aa344ec86eac00003745e02d9000010303000024095e0d68000000dcc000780c2c8b7960f7e01e9503f0016780ac5df86a60c742d8000030aad969ac00009780f0179e6c69c359101b8c5ec0035718ad00000000027669c184a56b699273045118df112540000bb98d22adf07815f04e005940c0800cd03ae27b3dc51ee208c039261ad9079e0a291935f2a961451d76c53db2d574f4c1f036315c1d770f5995dae0385c1c51017700f3b03e7833e812afc304111f3050ed0c584034 else 0x16bb2c0200000205ad000000000109e9e2d100000000076a7c000066bac0000b1a50576c000000000b0de80000009f0000080aa985e40000007db179ae9b837711101b77052c0000000022da7909dc0000b0a0800000000000002b118abc00000183ab00003ead9a05ae008b90c300000c02eb1b62c0a39d046c63b8822471e0c0000a498c000000002c04b000011a4f00000c70461c2dda4a0000102033072886b1f02640000702d00000b73a949a346b75c09a9046bc0c5f2290000048dfccaa100001ab8686d000000d023c000034b640000304600000e67540000a1e0a8a9d000004132a02218c5d00001c27400002c13d000015cf8000020ee7709b90107000000000d08f40220b02140000e6e1c000000002437632de241dd00000010000002049334ab65ee1c01459aae466fdc7d5c0b4f80ed00f0c814910d404280d05921a1600001439df74b8000011404000001b38000036bd043cc00bd482f970d8d423a6727fc045b7f75c26fcb3d5dbd040b700000778b555caa012b9b5300003c04930b875ec37085cdb3460a800374ebb640000504e48145f7b04c208d66584674000000000b12f3cb1620a3feb4467a72042457ce38b3ad0541829ca666202f000ae000002272887ac60f9e400910a900080e011f8185503071acabafae82adb028cc2f6a0cc20299308ca5856f7b03c0cc17d8ec72361429024eb0475428700001afd8f0c46d900562401df3109cd5c242b955c18c9082b06bf506000000d20c7031000000000021564000022d2e4bd0000012b1511270c7c196d560195000000000b0e300000861e96f96f00640000000015af780f92c22cf05c0873b20e0c00000000080fd614bf04a7da89146f530831814010b898279000022aa1f6e48000017d5c0000d70ca069d10764035ec106e4057102581e91f2226020f76d600000a094d1d9c2061c000060737453200002c357d8b640000a1eb48021d09200000c1abc83c5e0c071fd5d04ed5ae781e2d8199068c580ae30d2f019ec28bb4296f0c689ae96040d5f49017002e8d052900000000000000f073c00000000000009b1d21a1bbbdd608df06010020e11a5b83ed80310184a80c9e017830378000000002c0020000281e7b18a44e2f71c680000000000000000014720000000000a7de8638900002836400003c2686100b69da3069d980e779b0822f47172109b0000202a3f6030421beacdc9ee0f0109c26d03dd5856b0000000000000386de0000280aa80425c2a100b140000000032d4746ed4815700000824f80d74000000000000000003446496eb98601813488780008a6096ce017c00002678b437d569388388f0bdd403f000035b7817f6e83690000000001149ad878a17459255000000000bb8500000880f40000760dedaff9a68c000000003173586b0)) else (if i<4 then 0xf4000000000000011408432b51dbc4082037cec24300bcf84b4000038027707040000608140000600ab42ca10af0db31419300000d00b04b61263ac0000608360112d71585d58f4e7c000007269017742228831920bab02c4e6cfb0ace97e8fc4f6a0e86c241812fc0000a2a500000d033643b301178000076b1c9f1ff01de01b4a63a483b520472808c50ad8000021d700000d0e82ab670000280b907d3b025476909e83210c7342e0b20f41a75000000000000000000e2d6d4a6400432df4fc0a16c13e00003039500002c14170b5541a60000181725177b99c2000011ae8e1e4c00005000503cde08f000006004301281718801ebd09f5c91a00000000096408000000000823e806c3d9e0104e945ea11c6e042d0000387c20143741af85b3b5e476645800009003643cf823ec0000503a25ee2901e5c1a3000028642513f4995b80964000031f364105000024cb400000000006a48000000000000010987ab7f206a60603000000000e02d8000080596038dc007c870d90d38dd79000000000b1fa0815c00001821d1045f097e6169e0006d6f20abd547bdc0000709d80000f62d4000031ce60250c049c00002670d8314e1d55c3e1e0299062ec4b31867a80f4c8153f05899ea1c6f5c0000a7a5282db7036e803d000021b51000018399a668b826b7776c524bb0691416edbc0f586fc1f1a83ba0000000001025c000010e01c771001ca07e400003825e768f3081bf17b70191b2d9c0000b0b0507462065981dbf683d98c266f8f836fc0bbcc7bc31882c24c000029a70e6ef60ac55155d437fa01300000d01f701ee20060000000001418110244c4e4d7efd1e45a60e102d0000010312f01b69c4680324000000003009d60a63190f202b0c4b600000000040c7a1dafc0b69dbcde0e280000f0f040000000030130206ab02abf0e2f004e46f6c0000b0c62eb3530998c2eb0019cc0a9a013c000000002d9e90000141223062da369d3e5842ce0088f195887ab75b5970227845c5742202fdfbbb08e55008e34534669940000c04fc0000f77680000670f140dde6def0098767900000781adc15f50fa80000000d4000081d529b75908af4183a01cc000031b24c663409ee82337016b187f00c85414eb0ea6056e30ad4433c6609d4fa9c9b64003c402878718c0cea98dcc08dc0000b0bf09f6da06e380871079902a936e6c9887f1923801236dcae13b1708143bf4118d072700000000011c90c39e0000281aed10bc5c87612e0000070a30000066cfd1c7f000000000a6d7ae77a000015e23f0fa09eb4a01340000374a800000000069dbc05100000f0f1bc3a300003424db03c8838fa04195a0c000020143b111a5b4d505680000000024355c1b665a61000028ed4000020ce3919000000d089bdede30e5b8192000015baf0000001bd70ce4000 else (if i<5 then 0xd780b4946ccd62940000972151cfb90639c3d700003c267c157000002174f05e877a3c0000d69fdc07a204aac2cb000000000f1be7cb0c769418052d66974371006b506c80000006bea617380d8a087a16d9b2cf61f29e72eadec2000005b81000031848e64b59d000000383b796b0403c9263a08270e0ec1c12956b6587ef7098b0aa2702b6810fa6eb640e460348c55000003c17e812b19eced0f0960df23906587e01db0dc3d372641dee80b909a7d60afc000072a838329203d7d81470f780000000015ba3e1ca3c13c1ad30cbc5101c000000000180b8f071000000000000000000140c870926c2dd000010e1486f4b1b04000024032000000000000000000b0b500000206700000b697958beb0ab901a8d7c06dec5a00c0045d803c2dba16176c838251a8143e2806ce04b50000283930000383af010e8000070ae4000070d83dd09c6453c599407f381ec0b1c4dab811b830ed98044000006151dc2bd40089400e800da4031f8cdfc0fea4877c3d5f0d7e44f01081e00d4b6dc1424a570440000b0e9cc3caf004400000000399c596c84000086d230736222a942c7060f5c36b0000340d920c9183ec00000035600002017500002447f5602d1e95000001ea2f09cb0ead91306d91300003de57e0e064b6dc65cc000021b2841c2883f80000b706000006015b8222219f8000000000821a803ead75b6084ac3e050ba6c060905988260c0bd00b72e0e13cbe0f33d6812c70e42ab6c105652b4540ba000003111747d890d49021f20a0c0000f0d1c020000002c23f8002883b270684400b362ffdb7f000035b7600ec7a37267e2c00004006cacc200f699b715161849dbe00b81b4542c239d7106b384068c1af611eac1bc1007bf0a8946fd902a181b110a2d0480000028e88114a2dc5b40c7c019330993983900d1b012650c751be10654919eb70abf41cca057765df416de4700d005d405040caa9ebbb6fa2c68761454029d6071b826c00bb9d432a03ed806b619be0197e04836978a00efc7a4d73128111d0412c2cdf7c6c0000000012d130000006fbe0055836a80bf90509a15769cfc81a68c14aa07a24218fa2abc3a890dc80000b03c4000020d6c00009095cc20b51cf5cf10016254037000018656b097c4487903690133c477d190e30d03067fc77fc8546e6a3b012140b9c000031b53df5452d0000004aab40000d042a0038b05d99dc3c762181bb00003c1a0201abc75744f2c58e1904dc50b5c0af95d44904d1c7107062001d3b0d961e06a0cc543bc117d8c28430b7e42d600778c1e310a6d05c4f0efa5829e633fc20492df3c174b1067189f1042d831b6672400006aae58519b0e5c0000000009c553025080a400383c0ff4066a41f1e7db1811500002003900000ca44939f800002034743687091aa5f6000000000600a2c0ce119 else 0x401df01fe425d568540000b03bd1bd600003035c91e3aa9ca50cba87cea664401d4e1a4923c730d4c000000002029e302ef1da396840000026be89cd633ce79aa6a2e6495780000283a2914c1c39bb7cc54bbea0c89029000003db1bd06fd4247000000000c7470c09300b5d5d6221c515f52e7faa01f5621e7d0f5f07dc0000603ae416917ac18acbb014e8602f06c800001026c000040c8001c88265fc32cc1c2884c27678c0000b05c781e136a8f0108109e14f0b6ab15c26a00f2cd93e3078ac20190b97818d311d00000464d34307f6eda456030f610b8611d215bd5467bc41f92144b820971ea94230608640000e0e1ec5e610e27596419ab505132669c000056b136fcd52b640504506271b0b00002986aa00ac1beca69da5b6e708d400b7f14e00000000019261c1967023b707aa04bbc08b800001651e0bc0000034342209fe800cf66ba18c9c0a20000000000877bf1cde839f115e29d76000035c39e0ee40000b5f2c0000f11c798fd70270000060c5f5a5210cfdc12e00003c1fb9063c00000000001df00d040000713b6d2d49664d80596074782de416d45caab72c10afbc2c5600b2e0d0d832541f6782516ae1142a7502c1c30a565550fcbf074a46e38170b8292607731e58902f74333d01015e6900002012d7040bc34a807cf43868072f411660c218306f089683c4a0535c14ce027e96ad477c880e9b4de80000c07f7c3ce408a0000000002c000e1e239846d0bfc037cb1a6f86d696b4b4638c01f8832320dd4000041be8000020d5002c300002439a0000244e3c18e400008056205b142f6fc67694e48822122c3d00eee089d197d80b08db130bab4d8f9a006a83bb000019b00c0db182f890738866bd2d110289317cf007120c4ceb89108d98244873bc0000a055a41ba50a2881bc803db82977016cd85b000000000bb3af005816d3f82ec070cddd8166b15427e40f8f814800001425ca0070002f000034136805fc0000705eb980f508c7ec8112fae052c000029eb6000009999e1a640000800f8c0dfe04ac9aaf9a6b65875d06ad4536f7e940000a1bd9ce02e61405a1c00003c05cf020e8173c0ce00000501940000166340000e1c17c6884369c9cdc00000d979508ab019b70d15df1ad6adecb8491ea5c7359790b0286f035ac558101d8c9461732900a040a4ec3ee90ca3d9d8c0bc40664578a0063070db4c332763fd99426706bdaad8057b4b9ab78e89be5501f18344c6ad0821630ac9c1c3801a698b31084c0000a099640a546139826900001424b1062a00)))
def xmd11 (i : Nat) : Nat := (if i<7 then (if i<3 then (if i<1 then 0x648814c37bed2aa040a613ff2e92054530ddfb4cc0042984ffdba248514c33fed4b4a88261dfd54521645309ffb64d48a2986ff8ba545204c33fe54b52a8a61ff64c5a548130defb4ac2922987fd95154d204c33fed490428a61b7f6c1a7205309ffb6ad00429867fdb26a5814c3bfac0952a8a619ff2e1a944130bfeb6242842986fbd85690214c3bfacc2a2882619ff6a4a548130ffe302a8a409877f8a9655204c2bfedaa64c8a61bfe481a314530dfbb46c92a2987fd9514c5204c3bfcc8950902619ff2c9a564530cffb52d12209857fdb9540214c3bfac0b52a8a61bf768d9154530cffb6ad4a429857fdb52a1914c3bfc90324c8a61ffa5492024530ddfb4ca80429867fcb56a5214c3ff4a926290261ff94853148130efda40d4a42986feda2480814c3fec90a62902619ff2a1a564530ffe30298a40986fdd53680214c2bfed9150c8a61bfe6952024530bff37052a40985ff9b52a1204c37fcdd30010a61bfe6858048130dff240d1aa29867fd98681214c2bfeda944c8a61b7f6e5a720530cffb4aca8429867fc852a5214c33fed4b4a90261bbf6988508530ffb242a9a40987fe920441214c2ffcda942902619ff601a948530dfbb46c0042986fdd53681214c33fed4a4040a61dfe4815164530dff374900a2986ff9a0648814c3ff49034090a617fe6e12014530bff36654240986dfda7600214c2feed98a448a611ff6e998645308ffb74cab22987fd1214c5204c33ee5cb46a8a611ff6d5a908530dfb160d1aa2987fc95254d204c33fc9035228a6197f649a720530ddf300d3042984fddb3694914c2fbcda942902619df6e5a508530dfb140d1aa2986f7980694214c3fe8c0a62902619fe481a9205309ff374901029867dda3648514c3fe490aa690261afe6a18008530ff8a62902429847fdba649914c33bed2b2a10a61bfa6892014530dfb346901029873f995601814c23fed9352c0a611ff6c9a9145308ffb6454aa2985fb9b4285204c37ec9034628a619fe6819220530cff240d4a209877e920485914c337ecc34c10a611ff2e98264530cff330d00429857f9b0289914c37f4d124048a61bf6481a3545308ffb6454b02985ef9b6295204c2fecd994290261b7e481a720530cff300d4842985fb9b4295204c27fc5d2a2902617be6d8a148130dfab02d1aa29867dda3648814c2ff4d9140a8a619ef649a420530bfb36652a409867f995680214c337ecab4c10a61bee601a408530b7f37050a40986bf9a8600914c37dc9034840a61bfa6892020530dfb2a6d00429867bd95690214c23fed935240a611ff6d4a9485309ff370d0042986edd53698214c33f6d132440a613fe6e98048130bbf36e50a40986f5db3694214c2fdcda140a8a619df661a508530ff824298a40987f495254d204c23de5cb4810a611ef2e5a420530 else (if i<2 then 0x61bf7485a354530defb66d28429877f980654214c33fe52b50c8a61ffa548a948130dfba64d1aa2987fd953661204c33fed432a10a6177f6dc8524530cffb52d02a29857fdb8648914c33fed1952a8a619ff4c9a914530ffaa62a8a209867fd95681214c33fec934040a61bfe2e98048530cffb44d4322987fe9216a1204c37fcdc34010a619ff6a19524530cffb44c9122986feda2608514c33fec935228a61bf768d2020530affb64d4322987fd531601814c3ff898b00c0a61df754d3264530cffb64d49029867fd32695914c37ded20a440a61ff66d53148130affb64cab229877f5106a5514c2feed994a90a61bfe284a948130cffb6ad48429857fdb56a5214c3fec90346a8a613ff6e98214530cffb64d48a29877f980654914c3ff4902a440a615ff6c59864530bff360512a2986ff9ba480814c3feca9b4a902619ff6959524530bff360513229867fd92695104c3bfca8240c8a617fe6e12024530dfbb46ca842987ff181285204c2bfed9352a8a61ff654ca148130efeb0298b22986fdda854c914c3bee99262c8a61fd754d8524530dfdb44c1122986fddb268c514c3fb6a9240a8a61dfe6458048130ffd24254a409857fdb9295214c37fc5094a90261ffa5499848130ffb2a6d0a40987fd531481214c33fe4ab5210a61bfe688a054530efdaa4c1322987fd9834c5204c3ff49035290a617fe6e13248130cff974c9302987bf581609514c3bfc90220c8a619ff649a014530feeaa4a8a209867fda92a5214c3bf6c1264c8a619ff6a59844130cffb02d4a42987fd953480914c33fedd32a10a615ff6e5a848130eff322d2a409877f985481914c33fe29152c0a61bfe6c1a220530dff344c01229877dd53660914c3bfcc8b0490261bfe6a0a948130efda4290322985ff9b0214914c37fca834040a619ff2d5a944130affb6ac1322986ff9a8295204c2bfed814ac8a613ff6c9a824530bdfb6c52a409867fda5648814c37fcc0346882619ff289a8645309ffb74901029857fdb02a1914c3feca9a64902619ff541a920530aff974c1322987fe952645204c3bfc9032ac8a615ff2e98564530cffb44cab229857fdb9480514c33fed4a4028a61bfe481a014530dfbb44d1aa2986dfdb269c814c2efedb942902617fe6c0a864530cffb44d2b229867fda22a5514c33fea9352882615ff6e5a548130ff9aa6902429857fdb2295914c37fcd295290261dfe4819864530cffb5254240985ff9b12a1204c33fed035290a61efe6018524530cffa4254aa29867fd206a5814c2fbedaa40a8a617fe6c4a948130eff32a90220985ff9b2281514c2ffcd930090261efe6011060530dfbaa6d01029877f9204c5914c33fed2b2448a61bfe280a254530affb64cc322987f7950481514c3bfcc894a90261bf72c9a314530fedaa4a9a40986dfda7 else 0x66d29229867fda36a5514c37eed9b4a10a619ff6e5a220530bfbb66512a2987bf921601814c35fed430010a619ff2c9a944130cffb52d42209867fca2695914c3fec98a6490261bfe6a12014530cff924d4902986ff9a0148814c3bee5cb46a8a619ff215a948530cffb4ad4a429877f920695914c33fed132a48a61dfd5451064530dff350d2a40986ff9206a5514c377ec2b4c10a61bf76895324530cffb0254aa2986fdda3648814c37ee59346a8a619ff655a008530fef2a2d2a40986ff9b5680814c27fed934028a619ff6899220530eff330902209877f5214c5914c37fac0b46a8a615ff2e5a254530bff174c1a409877f92060d914c2bfedc144c8a617fe6c052245309ffb64d4aa2987fe920545214c37bed2b0a10a619ff2e5a354530cffaa0d4b029867fd506a4214c37eed2aa648a617fe6e0a148130bdfb6c512a2986f7da5540214c37fcd2b0048a613ff6c9a920530bfbb6650a409857fdb96a1104c3dfcc030a10a619ff601a908530efeaa2d4b02987fe921609204c3bfc5cb50902619ff6e99214530ffaa6252a42985ff9b3285204c2bfed934ac8a617fe2e95348130dff2a0d0042985ff9b3295204c2bfedca4040a613ff6e985245309ff974c92a2986f7cb8694214c3ff4a935090261ff654d8024530eff240a9b229857fdb22a5514c37fcd934040a61bfe6a18024530ffb140d1aa2984ffcba649814c2feed994ac8a61bfe6812020530cffb5254b02987bf9806a5814c37fc9035290a617fe6e0a948130defaa4d2922986efda6654214c3ff49030a90a61efe60580481309ffb74cab22987fd9532a5204c3fec98b0090261bfe2a5a148130cffb04d4a20987fd8b068d514c33fe5935240a613ff6e98508530dff350d0a409857fdb9695104c37fc5494a902619ff2c9a960530ffd2a090242987fd9312a1204c3bfcc8b4290261dfe2a59848130affb72a9b22986f7da5654214c37ee5cb46a8a619ff655a908530ffd17490242987fd9532a1204c37fcd414290261bf768d9214530cffb0ad4a42986ff9b5680214c2ffad890a48a619ff6a19214530cffb30d0042986dfda7540214c2f7edb0a440a617f76cd5144130cffb64d2b229877f595545104c3bf6a9144c8a61bdf6c1a508530dfdb44c9102987fd531681214c2ffcdab4290261bf76c9a354530eff322d42409867fda8648914c2bfedaa42c8a61bdf2e5a508530ffb2a690102985f7db5285204c27fedd0a448a615ff6cca264530bff36a99240985ff9b1601204c2ffcd810428a619ff649a920530affb6652b22986bfda8540214c37f6d124028a613ff6c9a314530eff24052b22986ff985680214c3fecd8aa6902615ff6d5a864530bff362c1240985bfdb8285204c2f7edb14290261dfb6552048530efdb30902429857fdb1655914c2ffcd894a902)) else (if i<5 then (if i<4 then 0x14c27fedab4040a619ff609a914530ffd240c8a429867fda9685204c3fe698a4090a613ff6e99864530ffd2a4c9240987fe921655204c3bf6a9240c8a61bfe6a12024530cffb72d28429867fd822a5514c3ff490b4a90261ff64c59248130ffb37498a40985fddb3295204c37fc9035228a619ff6a19824530dff240d49029857fdb9548814c37f6d1240a8a619ff6a4a148130ffaa62d2a429867fd516a5214c27fedd10a10a615ff6e5a148130dfbb46a80429867fda9295214c33fe54344c8a61bfe601a948530df7aa4d2102986ff9806a4214c33fe5ab5210a619ff289a954530dbfb4e901029857fdb0289914c3feca9a4088261efe600a960530dfbb46490a2986ff9a0214214c3faea92a648a61bfe481a544130aff972d2a42987fe920695214c3bfcc8a6490261ffa48592481309ff974a9a40986ff9a5480814c33fec934628a61dfe60192645309ff974c0242987fd8ba4c5204c27fedd0a440a61dfe481a864530dff160d1aa2987fd9854c5204c33fea835290a61ffa548a148130affb6a90322987fd58168d514c3feca9b24902613ff6c9a524530d7fb50ca8429877f991481214c2ffcdc34a90261ff554d5144130ffe220902a2987fd8ba54d204c37eed1aa040a617fe6e13148130bdfb6c42922985fbdb4289514c2bfedcb4488261ffa548a848130affb7052b229867fdba648814c33fea935240a613ff6e1a008530dff350c0042984ffcba655214c37eed1b52a8a613ff2e93148130eff172d2a40986dfda7654214c27fedab5210a615ff6d592245309ffb74410a29867fda9248514c3fec9894a902615ff6c59264530ffd242cc240986ff9a2480514c37fcd2b0010a61ff64c4a948130affb72d0242987bf981609204c2ffc5d26290261bdf6958008530bff174a8a40986dfda7540814c2ffcda95290261dfe480a864530cffb0ad4a20987fe952655204c3fea88346a8a61bfe6812048530dfbaa6d1a209867fda2660914c3bfc5d240c8a61ffa4855348130ffd240d12a2987fd8b36a1204c27fedd324c8a61bfe281a954530ffd24254240985ff9b5609204c3ff49014a90a61bf7609a314530ffd240a9302985fddb3214914c3bfcc8952902619ff6899214530ffaa62a82429857fdb5660914c33fe9034ac8a61bf768d2014530cffb04d2b22987fe952481104c2bfedc32428a619ff2c9a914530cff94ad1322987fe921601204c33fed2b3048a61ff64c4a054530ffb262d0a40986fdd8268d514c3ff49094a90261ff64c59548130dff340a91029867fda26a5514c33fedcb4428a619ff6a59244130cffb02d2b229873fd806a5814c33fecab4040a61ff54c51048530defb72d2842986fdda3681514c2ffcd8a6490261bfe601a008530dfbb46512a29857fdb9289514c37de42b4810a61bfe6a18248130dfbb else 0xe4818254530ffdaa4c1122987ff9ba601214c3bfecc34a90a617ff6c9a354530ffb966c10a2987ff531545104c37fed4144a8a61ffe604a948130ffeb02d1aa29877fd9268d514c3bfec2b5290a61dff6153264530ffda42a9a40987ff980645214c3ffcd1140a8a61ff754d1048530dffb04d02429877fd80289914c3ffa90b22a8a61ffe481a354530fff30052a42985ffdb5681214c3ffcc022090a617ff6d53244130ffdb5090242986ffd826a0914c3bfea9150c8a61bff6a15008530fefaa4c8aa29877fc856a5214c3bfec2b44c8a61bff549a824530fff242502a29877fd98545214c3ffc9030688261bff615a344130dffb5052a42987f7d8554d104c37fed430010a61bff6898224530dffb44a91229877fd954c5204c3ffc902a4c0a61ffb6952048530fff174c0242987ff950481214c3bfecab4090a617ff6c95144130effb0452b229877fd826a5514c3ffcc0b24902617ff6d4a848130ffbaa654240985ffdb1615214c3bfec2b50c8a61dff5491064530ffeb02c92a2987ff932281514c3ffcc2b4a90261dff654a848130effb0490b22987ff953285204c2ffed8b04a8a617ff6e1a048530ffbaa698a209877fd98481214c3bfe90b30c8a61dff6498344130fff30a901229877fd85545914c37fed1152a8a61ff754da048530ffeaa2c1a20986ffdb8688914c3ffcc0b3090261dff5453264530bffb6ad4a42987ff985609204c3bfec2a62c8a61bff6898344130bffb7050a409877fcba615914c3ffa88346a8a61ff76095324530effb06c90a2986ffda5614214c37fed02a4c0a61ffe54da848130fff2a254240987ff982295204c2ffedc14a90a61dff2e99260530fff306d2a40987ff5514c9104c3ffc5c34a90261ffe540a848130effaa4d4322986ffd816a5514c2ffed8b0688261bff6a12054530ffbb04d1aa2987ff9514c5204c3ffac0952a8a61ff76c95324530fff30ac9240987ff980545214c3ffac2aa288261dff549a264530dffb6ad1102987ff9804c5514c3bfec132a48a61dff6059564530fff2a290242987ff980614214c3bfecc34090a61dff6091064530ffbaa690242987ff9514c9204c2ffed930a48a61dff540a864530cffb0ad4842986ff9a2480814c37eed1952a8a619ff548a960530cffb5242842987fe952685204c33fed4b50902615ff6e5a054530cffb4ad4322987fd953600214c35fec135048a61bfe281a354530cffb24d1aa29867fda9549814c2f7edb0a448a61dfe481a264530dff34490122986fdd3268c514c33fe90b4ac8a613ff6e88524530cff90454aa2986fdd316a5514c2ffcd8262902619ff614a948530ffb374a9a409857fdb32a1914c37bedc34a10a61ffa480a948530cffb5229102984ffcba609514c37fcd032a10a617fb6c88524530dfbb46902a2984ffcba6152) else (if i<6 then 0x240987ff980689514c2ffedc262a8a61ffe2c1a254530effa42a9b22985ffdb8441214c2ffed9220c0a61dff540a264530dff950d2a40987f7d52649514c3bfec2b4ac8a617ff6cca254530bffb6a882429877fd524c5914c3ffcc034a90a61ffe5498024530dffb66d28429877fd52661914c3ffcc294290261bff6c9a524530fff30a98a409877fdba615914c3ffcc0b04902617ff6c8a954530dffb06d00429877fd922a5814c3ffcc0b2a90261ffd5458060530dffb4a99220987ff5816a5514c37fedd304a8a61ffe6098024530ffea62c0302986ffdb8688514c37fed434a90a61ffe4818060530dffb40c2a42986ffd52680814c37fed4322a8a61bff605a948530fff220a9a40987fdd5254c914c37fed1324a8a61bff6c9a824530dffb44d1aa29877fd92441814c3ffca826290261dff4c9a954530effb0a88322987ff9804c5104c37fed4324a8a61dff6558060530fff300c1a20986ffdba548914c3ffac094290261dff5412164530fff300883029877fd98441214c3bfecc344a8a61bff6a12014530effb3098a209877fd2160d914c2ffed9352c0a61dff601a948530dffaa4d4902987ff8a0609514c3ffcc1b4290261bff6a13214530effaa0d4b02986ffdb5688914c37fed295290a61ffe60d2048530fff240c2a42986ffda5681214c3fee99346a8a61ffe6153248130fff2a6902429877fd82660914c37fec134a88261ffe60ca148130effb22c12a29877fd85648914c3ff6c124090a61ffe5418060530bffb6454b02986ffdb8694214c3feec1a62a8a61bff549a344130effb30a9a20987ff921601204c37fed424090a61dff649a960530ffeb64a8a20985ffdb2214914c3ffcd295090261dff6498060530effb24d12a29877fd956a5214c3ffac0b40a8a61ffe5458348130fff2a4cc240987ff581289514c3ffca932a90261dff6455348130dffb50a82429877fd85481914c3dfec12a0c0a617ff6d4a948530bffb7052b22987ff5b8545104c2ffedaa6290261ffd6052054530effb74c93029877fd9254d104c3ff6a9144c8a61ffe601a048530dffb04d29229877fd80485914c3ffa88304a8a61bff689a954530dffb74c2a42987ff55154d104c3ffc5834a90a61dff6551048530fff30ac8a40987ff982601204c3ff6c126428a61dff6553154530effb3052a42987ff521545104c3ffca9b4a90261bff6888524530ffda40c2a429877fd91615214c3bfea8950c8a61fdf5495344130dffb04d00a2987ff581645514c3dfec1220c0a61dff6159508530dffb42a9a40986ffdba608914c3bfea932a48a61fdf5495144130dffb44883029877fd81649914c3ffc98940a8a61ffe605a548130dffb4a98a409877fd82541914c37fedd30a10a61ffe4811060530dffb44c29229877fd954c5104c3bfe90b2ac8a61ff else 0x391538ef38be3882383b381537ef37be376136ee36bd36973671363535c235913560350e34e834b73486343f340e33e833b7337b331e32ed32c7326a322e320831d731a6316a31391de330bb308a24b830382cf62fe62fb52f842f5324b82f382f1222872ec02e792e322e012dd017852d942d4d2d1c2cf62cc52c892c4d2be52ba92b8e2b472b0b2ac42a932a622a3c2a0029cf299e2962292628ea288d28512836280527df278d2751272026fa26be2677261a24b825f425ad25712535250424de24b82492244b241a23e923c323922356231a22e922b822872256222521f421c3215b211f20e320b2208120662040200f1fe91fb81f871f561f251ea71e761e501e141de31dbd1d8c1d5b1d351d041cd31cad1c871c401c0f1b911b341b0e1add1ab71a7b1a0819e219b1198b194f191e18b618851849181817dc17ab1785175f1744171316ed16bc1696165a162915d7157a153314cb1479143d13f613a4133c11e4131612c41272124111e41192112a10c2107b10340fd70f900f330ee10e8f0e320de00d830d310cd40c8d0c3b01eb0be90b970b450afe0aac0a4f0a0809ab0964091d08cb0863080607ca0778051f073101eb06f5068d064605f405a20571051f04e3049c043f03e20385032802f7029a023d01eb01a4015200f500b900670041004100260000bffb6ac0302986ffda8689514c37fed1b40a8a61dff608a954530fff240d4b029877fd984c5514c37fed1340a8a61ffe5499148130fff30054a42987ff953685204c3bfe99152a8a61dff6552048530fff30098a40986ffdba608514c3ffc90b3090261dff6059864530dffb0ad0042986ffd52694914c3feea9b2290a617ff6e0a548130dffb5098a209877fd506a5214c3ffcc026428a617ff6d52048530ffbaa6d2a42986ffda8681214c3ffac0b04a8a61ffd545a060530fff30ad42409877fd52695914c2ffedc144a8a61ffd6053148130fff174a9a409877fd52660914c3ffca930690261ffe60da848130effb52a93029877fcb968d514c3fee5cb46a8a61bff695a948530ffdb0290242987ff985685204c3bfec094ac8a61bff615a908530bffb6a513229877fd95695214c37fe90b52a8a61ffe480a960530effaa2c1b22985ffdb2601814c3bfeca95290a61dff6159264530fff30652a40987ff985481104c37fed2a6288261ffe4859548130bffb66d0302985ffdb84c8514c3ffcc026488261ffe481a254530fff140d1aa2987ff8b068d514c37fec2b5290a61dff60ca564530dffaa6d0042986ffda2645514c3bfecaa6488261ffe614a948130fff300d4a42985ffdb3545104c3ffca930088261dff614a264530dffb50c90a2987fdd324c5514c3ffcc0a6490261bff6898214530bffb7090242985ffdb52a1914c3bfec1240c8a61bff6895020530ffdaa454))) else (if i<11 then (if i<9 then (if i<8 then 0x98479816957497e597ca97ba97899763973d970c96f196cb969a9669963824b895fc206695d695a59574954e9528950294e794c1949b947594399429940393e893b793919360932492fe92cd929c926b922f920991ee91bd91979166912a90f990bd90979066902a8ff98fde8fad8f7c8f618c278f468f0a8ed98eb38e828e5c8e362cf68e268e168de58dbf8d838d3c8d0b8cf08cb48c838c5d8c378c278c018bdb8b9f8b6e8b488b228af18ac08a9a8a748a4e8a338a0d89dc89b68990895f892388fd88cc88b1888b885a8829880387dd87758744871386d760c7869b866a863985fd496a85b68559852884b5847984484e2a840c83c583898363833d830182e682c0482e82635768823d77b3820c4cc781e670e681b5816e8148811780f1405280b58079803d7feb7fc57f5d7f167ee57ebf17447e5d7e997e5d7e377e067dca7d8e7d5d7d1673a11e147ce57cb47c837c3c7c0b7bda7ba97b7824b87b477b007ac47a937a4c7a1b79ea79a3797d794c78fa78b378827846780a77e477b37782775176e976ad7666761f75ee75bd756b33e8753a751474ee74b274295d8a73ed4cc773c773a1734472c624b87253721771e6253571c07179714833e833e8710c70e670aa70847053702270076fcb6f9a6f746f4e6f1225716ed66ea56e746e436ddb6d9f6d6e17446d3d6cd53c576c786c526c2c24b86bfb6bd56ba46b7e6b426acf6a936a626a3169df69a36972694c68fa689d686c683b680a67c3677c20666756670f66d36697662f65e8638165b7657b654a651964fe33e84be264d8649c646b64243f4763f35a1763cd63a76381635062e862ac627b623f620e61e861806139611360ed60c7607560445fdc5fab5f6f5f3e5eec5eb05e695e385e075dcb5da55d8a2f535d4e5d1d5cec5cb05c7f5c595c285bcb5b9a5b695b435ae65ac05a795a3d5a1759a4595d592158da24b858b4588e585d582c57f057b4578324b857685737570656bf56835652562155e555a95578552654f554c45493174454785452541653e553a9536d533c530b52cf528833e8522b51d933e8519d516c1fe9511a50e950a2503a4ffe4fd84f914f604f2f4f1417444ee34eb240524e814e454e2a4e044dbd4d814d03231a4cc74c5f4c391e144c084be24bb14b804b2e231a4afd4ae24ab14a8b4a6549fd49b64985496a2cf64923482e48fd48c148904854482e47f21d3547c14785472846f746c6468a2cf62cf6464e461d45ec45bb457f454e452844f738ef44bb4474442243e643c04384433d431742f142aa4279423d420141c541894142411c40bf4083174440523fea3fc43f9e24b83f6d3f473f213ee53eb43e8e3e5233e83e0b20663da324b83d5c3d413d103cea17443cae3c883c573c1b3bdf3ba33b723b2b3b053abe3a8d3a513a2039ef39b3398d395c else 0x7010246a060548428ae00085438124701e040500950c02e600b0240870051461c130124508062a2b8001550e048e41f8028a046a380f8123903e0207d44700514098092202701011c0381019042703a08780f0003fc08130124014021c024748a04c048e0200f82b03dc07810290128025c040a18a03e034c40c0a70091d22813012381fe020ae9548a04c048e01e45700e0208c0f8123f0460b22b8001590e048e02781700e020c01a1b81b05915c000ac8702470680ac0bf02e0061c0c8154012e020514501f012620605780809e0005c13012400503e05380811012602981f8018e050048c07f80e07e0062813012381960607e4402be01228130124832e0602243f0091409809238101402463806940a700e05c04068280247e05a178003302e054dc0381109e02048a02c0f82fe0322006c8a04c0493c080a70031c098091b81b08915c000ac870247e08c238048a90e0640a9c0d487914034981c0a701315c000f8123f01034a28208092f0103321a5101f01a651041c0ff01e00a2813012440b20921982f0002b21c09200d00b6100364548703205500740ff01911c024502602480100680481e201104202643f0091409809238230460b22b804870320551c054401fe00a28130123809e000854382602460560505598ae0007c091c1583160922b8048703205504278110ce02048a06381c8ae00056438123f02e03c0060c8058b808100163be45bdfebde3bcdebdb2bd81a7c9bd50bd35bcf9bcde9066bcadbc87bc4bbc25bbf4bbcebb9258b4bb6c98fabb51bb15baefbabeba8dba51ba20b9fab9beb998b972b941b910b8f5b8aeb89eb8838148b852b821b7f09574b37fb7cab799b77eb74db706b6f6b6afb67eb637b4a5b606b5d58dbfb5afb57eb56eb56e9574b548b4a58148b517b4f1b4cbb4a5b469482e24b8b42db407b3d6b3a5b37fb34eb312b2e1b2c6b28ab264b233b1f7b1c69574b1a09209b17ab149b118b0dc8a33b0abb090b03eb00dafdc1696afc1af90af5f9502af44aefdaed7aea6ae75ae4fae08ade2adbcad6aad23acf2acc1ac9bac6a95a5ac44ac1e96f1abedabbcab96ab70888bab5524b8ab24aafeaacda179aa91aa6baa3aaa14a9e3a9c8a997a97198faa940a91aa8f4a8c3a887a861a846a820a7faa7c9a7a3a77da741a705a6c9a6a3a672a64ca626a5f5a5b9a593a562a526a4f5a4b9a488a457a426a3f5a3daa3a9a38398fa4be2a35da321a2f0a2bfa28e6ea5a25da237a211a1eba1baa194a179a1538ff9a12da112a0e1a0a59e4fa07fa043a033a00d9fdc9fa09f7a9f549f2e9f139ee29eb19e809e4f9e1e9df895289dc79d8b9d659d299cf89cdd9cac4be29c7b9c3f9c249be89bc29b9c9b769b459b149aee9ab29a769a509a2a95d69a0f99f499d999a89977993b992098fa98d498b99888986d) else (if i<10 then 0x8a8127a000bf80a8803e054091c4400904c04896169c81702a4013c000a012203202a203a068090c55815b1021f80012032790b6228028730e048c614c4700e05c040a1a8001d032054861c05814024490bc218381d024560842580817a080ccdc000f0ab04c407e050090cc4700028048940180187032054ac06827000300a4ae201881403e04815c8ae034a920548403203e048b4100c8b80187057c08c70143388a540ca048122c88c01401439870246600a1c0a8142607e026880a12800140243409c078001a024502701414814200701605c091043708e0005c0c9419700a0605009158430090e07809140b814e044278081203fc0106210380903e048a02c090982c880240cc881c0f8361a8530b6200f819012048e03643700050048b80005826024401341c0c8e0270140e050091442f0070e04c81815303102a0480fe0ce05c0604a00581a024310dc004380d050048d42380019068048a2178009e034050ac200c32a02e430e0ac0b8f800140243409c04090ec4500b0fc0582012358890e07c091380701514068805780812181051c0500a938001415610009178470080e06009178170070e0489c028203e0584e03c000a0152700c0e098091006c8a90e068802580307024460003414012202102a05f01812e02623817004d88064069438122e0041c61c058152c8560e0541d1004d0003205480481b090382606c3e000c40b815232a02804860340581902a450b400840172009a012380a919df0003205480940b9850240c78082f04c053801a25d0002821c0912020120743e11c01038180245e03c000a0122012e040e878338170102846094000a01f200b0280486a1c0b81f028402f40018815201fa06054721c0c0121825e03c00c381402a6e0207c04812201f034054c4021e0581c0a700024639606b0381fe02050d170002a80228c8090e84287020048809e818151b0090e81c08012298502405f8102b0620500af0030eae00098090c1928706204880340d0291d880620c9950122f00a1009809100ba040280240af02025c0143a64300b02806480570381fe02048b01d190100244a1006405834024590e069828122032028048681c0903618130242e00a200a012250302806460848181f0244c0e0500a8f805080320d009170201a30e04880c815843e00a28130123c090100cb8028a31c0640aa381014e0007d438153038027c0b808186180cc0b8154808063c0245487032054e06018b0c02e054a2af8170006263809180a007e0123a4502602470560640f82f911c024502602499140540e8f03f0102862b8001f02476100c78048a90e0640a9c18b0c02e0489c0d81b0890fc0245026024880640f80f02e0005c0a9c08488e0207f8002b914098092409f0103e0254470051409809240a70051ca28130123404409c0b80 else 0x2943a581c87a0662009148440b02e3035c004380d050048c0ac2501702a460ae880a019201702a20640694381221850120640a9380b0c212054900005c87032054a04c1d0818f0102a3042c0e0248703e048c02405f00028054a0c40b81f04205411f0205fc03808125e04e03c000d012281504207c08812029c014728a4c8781604878238002602440240601b0d9db87e000548c1c0e831024402e05409702089c00c39c4470002805480501b08c46070640488c05820151a0703e0486a2055814e026202181f5140252620c3a24c000240b9982700050048809809080d70003a61c14012303202a0e8640b03f00064048bc0057842024480002e440140245e000500a8d08f0040e060091404f0002805480af80f00028048a0840ab2402804b8048a90e806205c0c815200be000640a90816030120481d140a3080172180c940a00b90c06498008001902a4c0e0480a0192109710066020362b040640600a90840260243b0f4e421812200910ec100c8152a0330b21f8002602460634000901150c0980a9c0ce04e00068091418b2a02e30438108001f0245a08e21c383e038424c0c80a01518120160d86c2243b00034078091805c880280488a1943f01090068a61d8053904c048a619025030240e8ac0c0583490e048aa2280701310a280d1a8001403e303e05409044043c014728a44000172140a012280be0009809101882102b6140970102f28a86264402102a330e0ac0a8d04832032054803413012181202e054661f0000b032054aa168450002e4e046380a0f8008701a0a009140a9080240c81b01f30150420482201f013c014728a481a409c04c4009024603e06458000581902a402a61c090c0f903b1121c09168001a062330fc000a01224886000c41901228097100acc381228218080240f8122a87e000640a900a81fe0381f8018a301d0240c4607c0af0190f010091b0298802005c802544701514068a61c0a03202a4c09c0b8081a2700e0207d452092f0008405460ac18d0c032401242103b0090e048dc0204819190030a2780a1010c044080a009145581530b4e780019301f04c048604a438361b048000a009101881703e04b81047e0343100c41081203e61781015089c0380a8c401403205494000a01918150680e86a1b80702e02050a0444301511004b8082102fc0381290380b028048802e4281402442560c40c702e0205f061d8009e028331180010826228601209809118140521204808017301fe0301009138001902a3b104000f8122009b100ae43812281703fc0a03f01e000500aa02300d08a0508c0c0f815182103fc078001a032a2804a302185e020480d1403815074310f4aa0481226080160480b910270031c06809158280b03404880c410817025c080f8150880c380f005b0380810c091009700043c040fc)) else (if i<13 then (if i<12 then 0x15e002780c905583a1021a1005543812280990e0481b108001403e3e0121c0f8f0398ae040501d14c560701a0a0091682f000340488623800320244069c040a81420240620840a012089c064552a481510f402d1019290450a0481b1004f0003a05496154381f086068c3f01514025207c04d88e0405380812a5482080480c8ec401f0243b11c02c38122702e0205067370180907440240500c8f800129152380a945582120841d0481fe01c0b808125604e006380d012283290e050091005a8502807c802780815e040500bd0c3e04e024000d0122c0806405c09138001302430690000903102e0980a9c958abc07c234470003e06500840581f0244029c00168152701a00050091284700024a280a019328530bc068001a024602e050090e0201206205f8081534044080480a019298a90f4000c815283102a07d4470002406b80a8a4b0121241e8003606265140240a0122302412048080172b0401741c109005c88034048802c1b080f84202a309c0c805c870245914c100c815201802a420801870246a0680c0a821250002e0546c10188121b0002807c640c0a987024404207e04088e0242780019514921002c0c834024570fc000a0152108016c0c0b8122831a0005c0a900f83202a304340c0ad07029c001d28e5149034c0dc3c00028054c82013012190906605c6040130121d08710a1e8010506c07cf622801870244b10a1c0f83103461f80a8a01290138200e8172303a06622438122b039100c809100ab2461204b8048a90e706206b80a8a0125808c0a02f018120b0ca238001402a40260c40b815230806521c0c012298ac0e064606009080a00b51007c0a9643b0003c04898000481402e44238384452a02a520fc088484c270122005060510381902a4068084c470002405c0a826420403461c091019700032054807f80812184402b42409031e00a2943a38090902a38044260381d04c048d02200407030048a02409033181531007f03821e03c00c5028024a0300578470030e048dc2005a07030048aa1780809e0006809180a03f024320f02c090c10815d0e04880400c8340244511c0882d3902e5a07024c40120745b1081c0f812209e0282c0e21c0a83a213be000640a901098501209f81014370801701c0c0122985c0e0540a100680b04c0489c0380809514068a21f80009050048ac2380026024440962103d0330a07c0c9e02701034048861c0a20702a420fc000e04c209104220620481b0c43f00e022440a1404814e00054941c05a88028048ae15c3f01122424a0569cd87024450f0000a01227000200ca438122f0006207e45701812603e81103f0202405380f004091515a1f8018ac06048fc000d487012048a052438260244069014094009140980a9c18b040300d880400d387e000500a982201506204810809e00a else 0x50e05009140aa0b02804890120488124860300cc9c0282009032460a04850241d080a809e0004009170002b0240548048190361d03042056439300015028302804a950f800586040d0150250248050108151924024a1c0c0332a02412427800ab032603e024108122015026202a81c090148085034623800142286e040f4781c880261e0c0812e020f0781e43814198530f4e780019290906c040091281812416306c050090c18d0402e04880528181703e4e01410090e04e0405a30294a80a8d8448710120700cc661f8001403240520981b8d840150123c094000901a26005100d848812281f02805c64200a81a042402e05058000a0121b0590e04804900ac0702807c98101a828183302804860c4108150280481270091521d2a208381f02a4a09c040c012203103fc0608c092d0330b6200f819290803eca809108410002405c862180539032054a0878070103f22a049818817b11c02c3f02e024250c001403e02a406207c1081702bc0b80012057c05406b02700050048a052801870244013c000581402a5413021c401206405cdc000e98e034048a04c228141b04876054621f80009028048b0780d099d82602430880540a012063c0245487403204c0486a1f8002602440120481b0c04f0003404880d2000129152380a9b800140323016c0c0a0122017a080486026c450003e064a056c450013c064b80015831a08064a08455f0102807d45009383206204860860540470e0ac0ff020a5025262a81d8810e0481d18c512a04c0488c00130121d000340846c0c19700028048a14413012184c0634300c9043b0001a0a0091682014b1121c1b160401d02405c9c000688810e098091b80b000280489c068001402a460721c08012203103f22380c8a81a6e000c813012200be000a0091145500032054841f800140244d10c16438122702e03c00090912126207c000a28e02a5e0006013012203103fa2b027018126910c1c1901221050120a40a1082014b1021c0903a30150840e8602680014032410bc0380887e041400a1f80a88a0e07c0a812300b90a0500a914418890f80009178008813c0e00a154381f06c3e00034130122539e0061c091380f00212054900e02014e0407f8081202fc0130200a02603a048b0110220710e07c0c9b0460022061c278123285a080c41b10c2d0004c04882238003103fc0645409380703e0500b9303832024303a0c4090c04f08e0141c09141081a02e40d02009029c0413702025c0184080a019c0e054a434c3812190002804860c60201502404f80f00b44804805c0a988043c0822014025c00c72c0a83303407c0902b911c0380c8a5009e000641a012290850e0840a92c3b0c02a3115c0043f0204e050c441038320244c086209d81f0245e002bc0a0e818144000b40a960201906c3c004000a01520) else (if i<14 then 0xc9e0260790e050804816c090664673c00540e4382102a430fc000910927020922c06054c4487a00048c0cc094881d0702804a9512800363100488b35048211809311c00090150426607220080c15814074303ec0e8230231121c1b1c04c08e00084488123209e000500912440330280649c00048121c0006c0500912048310323e000240c8e8202606c42492200b8490244c0e0480a0c0a932024302a02441264403802442100480d0c18f014120e8901f00017028048a8200900b1c8a90e05009128082906c3a0fc000a0122009914202e0c80a81420360160486057800140324213c00090f038122203a0fc000a814209120a05c058122c090500e87c0014080a84203e340e07c0a0e8183621206494100a818181f06805460524381f064054a61e8001202a084b02780015412048a108068151a056000540b930204b02438120e80a0c094111220849c0b8009130e424a048220331d040120540c100a832e000500c940a81d034048802780287024050b21c0903601240254e448836201741206706100af00034048981c140804c88092048861c0c0361e07024054605780019156a1ca0604301206c402b4000c8ab2015064050091203e000280489417800121985e00050605380012181741204b06100a01506c306c0484ce7800151815033c00740c0a0b80015025024805e03e00028048bc008481919240622bd04821281d081fe020d8721a438140244c0721f8001402a50130301a0cc402102a36000540c0c09014128702404c1b100fe070240c89c0006a090244413c0084812220760005c0a1019817028390b02c0a01224093114001b0122d030240d860688440b062048b0240d012a544042824461e800310324a0604818036260002e050058122817654230d40f03c870245c18050130e0e8150243062110108c0481202e02c8a1f80014412402a0240c0d43287c0005009168181520e0480f97027000243605421818c0e8361014042202402c52181b014024402f4a80a012250350b410c4036281806c2a0007c0a0e1901402a3025830521e8001502846020d8521c0b8121c090240501d120498706c048804983898404098120640d88c200900b1814a54064605c09109a1848120845c00220261f000580540910c3d0006c048805e8002303e4812c0644700034590e0a41b0c0a20c02a0248057800140244024050108f800158123e000481a0d0483a10284120e860540a01218ab30e07c604c0b909a18064b420301c09014181f0282c060d804819270002405060c40950002e430c0540a52a02450120481f8c18b05b1121c88788101406c430b4e7800122017c0081c0a0192815e00048604b8008c401290e0ac8056438141c8600e0501d100fe070280340a97021090240d8804c810122120d8bc0009018180990e0480a1143600 else 0x84821034048941182302a0261c1b181b1091187a720481b100a8120300d880540a2870744029c00407c0a607012048b41009080a20c012054811104821181550fc00090142d00020a28721c0a40b0244033024198c0ac87e0005009140a01501630a00545024438120280e8b41082c871d030240501b128190802a0849408c281106c048a61703d030244e0061c0c8cc47000580540914c401506c302a027038f0250005206482ac0a83203e4024440424410b39e044ac0b98848484b0c101702802c091281814c0e048805380017024490e04c1b0c848360280489c08848804c1002a04892201088a81242409180a040ac87c014000a01236070240340a9301d0790fc000a012301550e0480a10810362120488c2009034181703e410c392950425815024381605409014252a0280486056800141f0002a060602f01d08910064b4100a8120280d8a0541a01f1a850281081d10094090280e880538001518070240501d100a809e00050091504d880240cc940418880a9098120481b158270106c302e0c80a01521028120500903629090280d80910140120663311c00090c0a70002a06090240a01206c403e61c1901402e5809027800192033030230a05644287c0140))))
def xml11 : Packing := (1008,4,7,0,0,16,0,xmd11)
def xmh11 (i : Nat) : Nat := (if i<2 then (if i<1 then 0x20ca0adc0000004f980f33191f4061c00e0009300003c2c5d06d8000000000982600000000050ae3642200000000000003027580795c135209e0c105342ec000066a6d0110c09600000d015f40155675c59e3206e00c22105e3c659802714008e005b1ec8a01708801f0321c1c616a2f40b8813cc80cce0504866be0882814f00002c05bc02829dadea57d00d1706df99ee5707b21bc372040000207700000e690812c73004c018a000000000f067d962990966c2b56134819a8928a48097900e65a44f6438c0fe00003d8f324b2ac182778d8413d000000000708fe804731789d067200e9067bc134000000000041e040650000090574000000003025e5a86a0136706c8000070670c1dba0144804f90525c1ebe0a20806f80a980000405cc000076058414e2059dc230b0a394a48e6007c481908500000000038120c005081a10000219c8c0703c29de0528001b773a0822ec17c2caa3a466dc0440062599d9d04200000901e2c196000024121000680000701b8c0b0939e9468ed0969c9500000081a070009458a10a680000b16b7a1a251a29096df6734818be651e58d00000289c76094581aac0aaaa156e064d5cd0805598276a663541040000158dff6041812b8676800003405241c1b0873456590a4bc24300003c102903c002b0a1770199bd026400003187e41e2d090800005096c417c0000000005298f00bb914cfc0faa08f400d7e69a38077f04b40000a08d3828900003e5e00000102c39003cc0ae89078000060536dac5617018056e007d02c660460000000002416a00003d8b0000014088020cc0000000000000e0a0dc0a900000425fb745c00002060e0205000012a72b074ac07420b2bc22821afb000700002c1e100002413b000000000a04dc00000000000006084601d101a88400b29a579a5210275806bc62d6c080f262c8a04b083c00004085f01910438800000000244d701050002c0e2c06a050000406190c000980a018040813008048203090040e061380806050480014035301412040e0600202040005600031542c020782800200106c29130c0044a05000090a2b0e00c94000600c020900810040a0302406000180c180d078148c0d0686534180d04442002081012010e0d0360104090040208818080b0080c0204050047c29068047a17072581409008081a03158001e100487086010105000032c804a0000683802033500c040701828000001804080007a887a000080c3c121284032000d8080c1f031101a02008284a03050000401031002603030181a01018740a07038240a0213808000b0589c100a198903c0a060180a021184402000104812000302cda1305854200d000840a0400020120a020000213010340c04050445004020000e08000146600018283a000080c30080505800061d80c0002050180201 else 0x34212208100885c49cb00d256aeb0106609e800000000000009a6f1c29e102474085000000000000028d2eb01d4000066a919a6a107d16247d7090c0460000180efc08040000108908001e15250050000029914a643c00006062000004004bd12ed61ebcaa8f07c8829b401f102a50000002c100000c0310000000007010101e7a05ad80df4073202a7a0107811480a29810d00000000000000000080ab0c11739759ddf20052342be60a63410e7046b00ca0000084a729090000070b1ec177d0263426a0000181f9467b40000471c140cebb7dc589bb133d591d603d54068705840000000000000407ec8164b13ad2ac8f04c5997550aec4471000000000b01e8000040afcc2440000141ac00000d91a93a555ce547a7c0073707b801d8c04550146000000000c071140b6602300000262768225d0079819ab07e8000000000da7d00000000040940000000000816f06250422900003c0e880178000000000000090665c254b654cc181000025ceb00001401ca64e814cf301c24691600b8015cf5789c1f30000000acc34ddcaa2013da0213005db5e396772c403d80123025220228000000001d20f5037704c5377d4403e0000000005074c0000391c000000000385cb000021d7e808c40000407f0000000000000000003c10c000001a01b04ff01c800000000000001a196b60c4c1e9366e0c21f90018000030024c04de09a4868957727859ee0365419b0000381d9e0206c155f611800007047bc169228440000613880000709ae05e800003c1bbb058b405800002c00e8009b1901000000000e024000000000040de26a7c0000516be416630a340000c2a30000000003597470ae7cddb404e5805f5039c8094706bbc45ee3a1980eec22ccc21d00642015a4668880e9005ee4063d00fc0000f0564000001610984ad0089402c801abc13c000000000000000000a065f5e4d8054f05f7a08294227242380000e093dc0cdd05480000305bbd05c10a580000d70a2022d00000000000003826c573f7812c904000000f61a0000000a7dc0059022f41d652a9a011b00001823bf0300c200c0a1999db541988079f08e124c151857c2715069ded6a975d12e72709338261602df8447804a844bd801240000501fbd85fa0972827000001c247f73500000c040c000000000002a509e4c09201a540000f06fc00005146f0dd0000000000b0013c299000025c36a008d2467404a48122312dac2b6e79fd42ae208f0412f30428e0f116b37da9de36380000217284021f857f58c10000001af20324000000001c2749093a423a36258652e902e40000b6830208080ac782077019711e0f63580000805081caa00157022c9a6a80255400a00000003a8d01a6051ec1ecc745641ffb07080000602fa413a0000201ddc00a5823200779588f70af) else (if i<3 then 0x700000c03f00000000021e90900824291006480000000000000360e00000e014e8ce28032ec1f000ab40000a000fdd123052e81431019800000000180450000380e08088dc27f6016a024de00d8000000000c0f8592e40000b05ff01be7190d0401a048c0a9de06ac0000e634bc0ff671eac1a64767ec0ebe0a8489aa318a7007df27efc2cbb0176425d67310d887000038165000000000d0a72c16cf6162d8555012e406d37a880000f0181c617400f129b8302d6995fd06c30030201c88ec20b306596ef7713d8ff3789b40d3000000095661f301e48a33c0000a6b0b404e969af90b930065c0b2e4339c19d0000281c7000000000526fe1a2680aa4800c000000000601a70264708ac81ad10905c4d9525ae1a3e71297012ed4aff4237f057f811900028199cf04a08a951014b406cf07c70226a03e782afd430741d4209dfca3d7027982876005ec8b477527c0b1c176d1ca7c09f545b9d151b40a510369822ac081842c0547bf569400a3151f7000b48116501c7c20326194000071ac542ba48a7501d570a8a00e24035bc02f3075e4285614838127e0a1059e9c094fc00d6125c9e9ba7493426fe2902c4214127cc956907d7011c0000180a2713f810247684b09dcc03da1ded80360e1c5d08cd594f50a5181a5a056341f6002ab58300083b40f173666121c90a0b619b41622026d4a22700a654212d83af02d0000081082c064206300000a092f82c9c1a7bc144506d09c69907685dbb5098321b8b1582c40220188851230226580ef11d245d9c1199527f205c1012416644822250a5d4215a00edcac2e15bfddd6c0af5420d9021a1a6c466aa81cb156b58054563f54067e572cde40e004600c4e068b416da63810561906038059d09021a9c6058dc27e117968651a055d411db042785c71763b018e205f601548179800003aa7400000000140839274581e8706c481df109c80a22006600000b659a5cbaa0a0581fd50714c235000031019000005a9712b23c1f7312d00000d168e028f709f00000c16c00000f13535da700003c186802115ce9a0867c500579e95eb9a76c50130000000000000000000000028236916c4c0fdf68b08a1af6929d85dc04c9c0e5ab83d421be04ce9e1ff9068850756013457417089c0d54261d4246c03d0c0e1861580000a063581a8000034076d01fc0000c24c00000c05c60113905fa00dbe64e042a0f028d41a4d136802a311a60198f4047f452ce0b4780ab0000245b4909cd4018772109a0b5031fc5667122400dca086b46c200000808d000000000d074291d6104e1c15142629c2b33082fc15ba28df40bfa0238000040825c0cfb186c000090292422f60b35c1cd9023d00c60098942165bb08ca539624d415000001427bc80e31489e183fc2b2213058160567de80c25645d401d50393c9a20000186b else 0xf7a095c000000003809ac009dc957f05d559980000341c9000020293000971dca803140000700ce028b767d0c19e00003c1b9306f008c700003821e909b80000e038d8221a222601400000342cc000000000000000000102cc000028b1e5a1a0000240bca0808014cc0a000000c270b59df90a5780ad0000041b3e26e0c087b030dc172a049941fe8072ad8c7d76f0000000002c15e50b100000703b0000060b425d5eb0b3d80a7378aa81a3a521581f8c078e4263f05d1009f100de00d0209295d46a26f082c2f0398409b305e4000030a90000080ad285ba741c00000d19158111d05e800004099cc0000000141bd906a798f6a0aac447ca0448e033e63c55a40270691e11419e6c2a8c061242493691f010b90b3a45a6c09a04218f035380241660dc24500000000000003004a715c2c239760e581ba514f7407b8095842c87043f042b20996454ef0406501e000000569060f00000304d0023e345d00000823c40000000000000307a80000c626400000000140fb00003c6bfb06d44034002e900c1f041f00a80000100100000000bd8079bc5d2672e48493f0615c0a1766de182e907b700ed90131624200821826600003c18f4061edaac507380000500c800007092241c307679002bd0a40419507064ddb8965280000000018042107bc0000612089d296051640960000341cf00001416800000c0af9a5180000a61e3c485268235879e71bc0082e102bc0f2879ac0000408409850300d6c043279c94125968))
def xmd10 (i : Nat) : Nat := (if i<4 then (if i<2 then (if i<1 then 0xffc1216153148130afb9c42e95148130cfd8a06cca254530c7f9b06a4850853087fdcb214a948530c6fdb66a48508530ebb980615a408530ffc1314811048530edd953481a720530aef9c6284a5481308ff8ca6c0a254530bfc9c2281a354530af3dc42e1a508530ceddb668ca254530cbf9ba6058048130ff4953548a948130a7f9c9541a020530e6f980655a608530aef9c6284a948130a7f9c96e1a008530cfd9c32e951481309df9c72e93148130ff4953549a848130cfd9536e1a008530afe9c56892020530d7e9526c0a264530c7ddb968d8008530afd8ca5453148130afd8ca6c55348130e7d953601a908530a7f8ca481a564530eaf985601a608530afb5c1215a408530c7bdb96905220530c5fdb969d8008530ff61524412054530cfb9b46a0a548130cbf9ba6018524530eb79a560185245308efdc62e93148130afe9c2280a254530bed9c62e93148130cbf9806e98508530cfd9b36a0a548130ef69a55492024530cfe9c22e95148130a6fdc6289a954530ffc1314858048130cef8a06d8a254530ff49534818548530dfd1b14c4a8481309ef9c62e95348130dfc9b3480a548530cbf9856e1a008530dbd9536e0a148130cf9db468ca254530cef9b06988508530ffc131484a548130cf5db86cda5085308ff8cb6958024530cff0ba6055148130afb9c4281a954530ded9536d8a148130cfd9b068ca254530ebd9a854d8024530a77dc92e1a508530eb79b8601a508530e6dd53661a608530d7d9b3644a548130ffc1204c5a548530cfd5a36c48508530fbd1316058048130cebdb6690522053087fdcb6a52020530cef5b169885085309fd9c56cca148130def1816d8a148130afb9c4281a354530ffc131480a548530ceedb26988508530dfd1b14c4a548130ffc1314858248130a7f9c96d5a008530af9dc42c9a3145308efdc66e88508530ded9b64c4a548130df69c26d4a148130c7edb96892020530eb79806958508530eed98054da608530df59b554ca848130ff49535499548130a7f9c02c9a914530df59536d5824813087fdc96e98508530cbf9b8688a054530dee9b6484a548130c7edb56899220530c7f9b06a48214530aeddc62c9a354530ffc131480a948530ff49535492024530efa952481a420530a77cc96e1a508530cfb9b4284a548130c7f5b16a4850853087fdc52e98264530dfc9526cca148130ccfdb76988508530df59536d4a148130cfb9a86d0a148130c3fdb96a15008530dee9b6548a148130ee5d8554da608530a7bdc4289a954530cf78ca6d4a148130adddc72c9a314530dbd9b84c4a054530af9dc42c9a354530ef9953481a420530e3f9a86019524530df69c56c8a054530afe9ca5492024530ffc1214c59548130af99c4281a354530afc9c2281a354530ebd180605a35453097b8c96d0a548130 else 0xffc131484a948130afe9c2281a954530aebdc6215a408530afd9c02c9a3545309ef9c62e93148130dfc9b3484a54813087fdcb615a948530af79c5284a948130c7f9806d5a908530afb9c0215a40853087fdc56c9a92053087fdc86d4a948530a7f5c1214a948530cfd9a36c08214530dfd1316c58248130cbf9a86e120245308ff8cb481a354530efc9536892024530afd9c8481a314530cf5d526cda524530a6fdc8655a608530cfd9a86cca148130ff4953548a148130efc9536892020530c6fda96d85220530ae7dc62e1a508530ff495254ca848130afd8cb481a354530c7ddb968d2014530ff4952481a354530dfa9b4484a548130ffc131485a548130ef598554da0085308efdc62e95348130c7bccb649a4205308fdccb609a354530e7d953481a920530abf9c8280a25453087fdca6e4a54853087fdc56c8a960530afd9c2281a354530c77db96955008530abf9c8284a948130fb59536018524530efc920689a354530a7f9c0214a948530e779806959508530c77db86959508530efd1812c1a354530e7e952481a944130af79c02e1a508530e779806e5a508530af5dc32e1a508530abddc82c9a314530cef9b62a4a548130d7b9b4644a54813087fdcb601a94853097f8cb645a848130cfb9b4688a054530cef9a06d85220530df99536d0a148130afd8ca481a354530ef4d5268d2054530c6fda96d8a1481308ff8cb6952024530af5dc36958524530afb9c4280a25453087fdcb6a52014530a5fdc5649a720530afd9c568d2020530ff49535499848130cef9b66a0a148130aeddc62c9a314530afd9c22c1a35453087fccb649a354530efd0a0605a354530df71816d4a148130c7bc852e5a408530c7bccb655a408530ffc131485a848130ddd9536dca148130cdf8a96dca148130cff1a06c4850853087fdc92e982545309ef9c62e95148130c7f9b96812020530c7bc522e5a420530cfd8a96cca148130a7f9c8655a008530a7f8ca481a864530cbf9b86a12014530e7b980655a408530cef9c62e95148130afd8ca6d531481308ff9c82e95148130dfc9b24c4a054530c7ed826c8a954530c6fda96d8a548130ffc131481a048530cfe9526e92020530c6fdb9699800853097bcc96d0a254530a7f9c9601a0085308fdccb68d9254530afe9c2281a354530ffc13148592481309fe9c26c4a548130c7dda96cca148130cfd9316e98048130cfd9b32a4a548130c7ecba5498264530afd8ca5455348130f7e1214813164530dfa9526d0a148130a7f9c8481a914530cdf9a86dca148130c77da96d4a148130a77dc86e5a508530e7d5812e5a3545309fd9c32e95148130ffc1214c4a848130d6f9b6644a548130ebf180605a354530efc95268d2020530cef9b66a0a548130c7dcb96c9a354530c7f9b06a45220530dfd1816cca148130) else (if i<3 then 0x97fdc36c8a954530ff5953614a148130c7fda96e0a548130aff8ca5458348130def9b6614a148130ebeda85498224530d7ed526c8a864530bfb9c4281825453097fdc52e98264530ef5d526a15324530ffd131600a948530df6d526d53148130a7fdc52e1a9441308ffdc82e92054530ffc9532e92048530f7e952480a864530aff8ca615a848130bf9dc42cd8214530dfb5816d0a254530aff9c82e95148130eff181284a548130ff4d535498224530efe9206a1a254530cfdcc36e98214530a7fdca6099524530b7f9c0215a948530c7fdb8688a954530a7fdc52c9a944130dfe9c36c8a054530e7f985655a008530dbf9b8484a054530c7fdb268ca954530f3ed816093264530efd8a12e95348130cff4ba60592545309ff9c82e93148130df79b554ca148130e7eda26099824530ebdd53609a82453097fccb549a864530e7ed522c9a960530def5816d8a14813087fdc96c9a52453087fdc96e8850853087fdca6e4a25453087fdc96e88214530cfd9b36808508530ef5552605a354530e3f980615a908530cbf5a86c48508530ffc131481a948530cf75a56c4850853087fdc96e85220530fbd1316058248130fbd1834c58060530ef59806cda508530ffc1312e92048530ebd581609a354530dbe9b8548a148130a7ddc36959824530ef9953601a408530c7ddb868d921453087fdc86c8a954530df59c36d4a148130abf9c8284a54813087fdcb148a960530fb598554d8008530c7f8c96e98048130cfe9a26e120245308ff9c02e98254530e3f9956a1800853087fdc96d5a008530ff61526055148130c7bd522e5a420530cf79b56a0a148130d7e9b2480a564530fbd131600a960530cfd8c36e98048130c7bd852e5a408530fb65526058254530ff49534815220530ff49535492044130cfb8a56d0a148130a7bdc9615a408530ff49522e9534813087fdcb208a954530c5fdb969d5020530ffc1212e9314813087fdcb6a19214530cfb9c42e95148130df99b44c4a548130ff4953549a148130ccfda76d85220530f7e1205452164530d7f1b1644a548130fbd131601a960530afd9c02c9a31453087fdc92e98548530ebd9536a18008530bed9c62e95348130d7e9206d52164530efc920485a354530bf99c4281a3545308efdc62e92054530a6fdc6214a948530a77dc96cda508530ceddb36988508530ffc1315412048530c5fda96dca148130cfb9b0690522053087fcca6d58264530c7f9956e1a0085308ff9c06e885085308ff9c06e85220530cfd9b36805220530afd9ca4c4a054530e75db3661a5085309fd9c16cca5481308fdccb609a314530c3fda96e0a148130df99b44c4a054530ad7dc72e1a508530cfd9806cda5245309fe9c26d4a148130cfd9206cda524530afd9c0609a354530e7d953661a008530a7bdc9215a408530 else 0xbfe9c22c1a254530cfddb36a0a548530dfd9536e0a148130cefdb66a0a254530dff1812e95148130c7fda96e0a148130ddf9b760ca148130a7fdc52a1a264530ff4d5254d2048530e77d856959224530ff5953615a548130eedd8554da608530e7ed52289a5645309ff8cb6059548130ef79b8601a508530aff8ca601a254530dfe9526cca848130ffd1315412048530d7f4b96058254530dfe9c16c8a054530d7f9b9600a548530a7fcca615a864530ffd131600a548530dfb9b4484a054530dfd9b54c4a848130d7edb2608a954530cff9b8688a054530d7edb2608a564530c7fcb96a1a548530ff71505458060530cf7da56c98524530ff69522e95348130c7fdb56a4a948530afedca5498224530c7fdba2e99260530ff71815412054530ff65524418254530dfd5316d4a948530bfd5c12cd8214530c7fdb2604a954530efd5316a0a548530f76d526455348130efd9536a12024530def9c26d8a5481308ffdc52e99260530e7f4a9605a354530def5816d8a254530aff9ca484a054530d7f9b5644a848130a7fdc86959224530f7e9204858364530dbf9c36e0a148130d3fdb96095060530f3f582604a954530ff5953615a848130efd8ca4c58048130eff0a0605a354530aff9ca5498024530dff0ba6053148130f75d5254d9824530d3fdb8608a564530d7f5816e4a254530d7f8ba6152064530aff9c2281a954530c7fdb26a4a960530d7f9b96153148130aff9c8284a948130dfd9536c58248130bfd9c12e95348130c7fda82e5a254530ff595254d8024530f7d53164980605308ffdc52e93148130def9b660ca148130efe9a26098024530efd5a3604a954530bfd8ca6c55348130dff1b1544a848130fb79806155344130dbf9b8688a054530cfdda36c8a9545309ff9c52e98348130c7fdb96a120545309ff8cb601a254530ddf9b754ca148130ffd1316011060530efe920694a948530ef5d8554da008530f7d5312e99260530dbf9b84c4a054530eff0a1604a948130a7fdc52e99260530dfb9b44c4a054530efd5316a15048530d7ddb3660a548530df79b5544a848130dfd9532e98348130ff59536152044130bef9c62e95348130c7fca96d5a948530ffd131481526053097fdc56c8a864530dfe9522e95348130dfd5316c98060530cfdda26cc8524530dfd5816cca14813097fdcb660a54853097fdcb608a564530dbf9856e0a148130efd8a0609a354530f7e5316612048530cff8a06e0a254530bfd9c52e93148130ff59535498044130e6fd85661a608530e7dda254d9824530df75816d4a148130dfd5316d58060530d7ed526e0a264530a7fdc8255a908530ffd1814c5a548130a7fdc82d5a948530f7e9204855364530dfb9b4688a054530ffd131601a548530dfd9b84c4a548130cfdd536c9a824530a7fcca6095064530)) else (if i<6 then (if i<5 then 0xff692054953441309ff9cb544a848130efd98554da008530c7fda86e4a2545309ff8cb6015148530f775526615144130efd8a04c9a354530dbf9b860ca548130c7fda86d59224530ef79a56152024530e77db8661a508530dfe9b24c4a054530a7fdc8295a264530dfe9526e13148130efd9536892024530a7fdc82d5a908530def9c86d8a548130cfbdb46a0a25453097fdc86d4a264530c7fcba6553148130efd980485a354530ffd13148580481308ffdc26e88524530a7fcca549a564530e7f9a26019524530e7eca2549a864530dfe9b2484a054530dfe9206d4a948530dfd5316c8a960530a7fdc2295a864530c7fdb86a4a548530dfd9b3600a548530cdfda26dc8524530efe9a26152024530bfb9c4281a354530ffc953484a848130cfedca6c88524530c7fdba2e98564530a7fdca4c8a954530cff8a16e0a548130dbf9b860ca148130efe920689a354530e6fd85655a608530c7fdb96a0a548530dff1816c0a254530a7fcca549a864530bfe9c2281a354530a7fcca615a5645309ff9c56e0a148130dbf9c56e0a148130ffc9212e9534813097fccb609a954530cfeda26c88524530ffc5314855348130dbf9b8600a548530dbf5816e0a254530fbf1316058048130aff8ca481a354530cff8a06c9a354530ffd1312e98048530dfd9b84c4a054530cff4ba6053148130dfb9856d0a148130f7d531648a960530dfd9b554ca848130ffd131601a048530f77552604a954530dfe9b5484a848130af7dc82e5a508530ef5da254d8524530ff5953615a148130d7f9b8480a5645309ff8cb605a548130ff5953614a948130a7fdc26959824530dfd8cb54da148130ebf9a26018524530efd9a254d8024530dfe9b8480a548530dfb9b4608a548130ddf9856dca14813097fdcb608a954530dfe9526c4a848130cff8ba6013148130ef6da55498224530ff59534818548530fbf180605a354530cfdda86cca254530dfd5b84c4a548530ffc95348582481309ff8cb481a354530cff9c82e95148130dfe8c86c8a054530dfd5816cca254530c7fdba6153264530c7fdb96a12014530ef5d8554da048530cefda26d88524530dfd9856cca148130ffc9524c4a848130efccb36898214530ffd1314818060530e7ed522c9a944130dfe9b24c8a054530ebf9a86013214530def9b654ca148130dfb9b44c8a05453097fdc82e5a2545309ff8cb601a548530e3fda86159508530ffd131480a960530ebf9a85498024530f7e9524818364530d7f5b2604a954530def9b660ca548130efd9312e98048530dfd5316e12048530df79b5614a148130d7f9b8644a548130ffd1316e98048530aff9ca61520245309ff8cb54da848130cff9a26c08524530ff7181545a5481309ff9c52e93148130ef5d536895224530cfdcb36e98254530efe9a85492024530 else 0x54f6040b4eed3922134c251b701ca13c09374dd4ded4c712ff4b592ad4a40e9b3220221493c6a21a881734838a8b07291e542611c8461cb0645a914d0ab44f02135124441cc422c190de102d0b51d18c25111509841ec1ad4178e9b1afc2f3102d035102d0183e9cf7e3d54f2c05ccf0f3bc8c883b845533b102903a6c40b39f81733984e44389c2f32a2ce0a37b4dc435dcd4e34c4d0833ac32d05cccce05cccb132201ad2c1887605ccc5f3108c2513c040b1afcbfc2f1c1730bccb92102cb692d301732c8c1732c18add102caa82a2ca6e2914a10276c9be05cc7460bcc989081095424dc90215088cd22f0173224c876213482408847ef1f4879d0ab45421d1877405cc7571d187051b7057c1afc6a20b2868519105df16d82ca15f059909cc1ca0b2857c154c42805cc173150851913c04c7102c4621114428102c3ee0f443a80bcc38b0d5832d0c402f30b282ad0a4027308f822108101e707281ad0640173055812d04400db026809a0134000dbf9806c8a960530c7fccb6a55260530c7fdb56a4a848130afddca2cd8214530ffd1314818548530e7eda26099524530d7ed522e982645308ffdca6c58254530a7fdc52c9a960530fbf1814818254530ffe1526053148130df79c36d4a148130d7f4b16e99260530ffe181548a14813097fccb6458254530ff655260582545309ff9c82e95148130cff5a26c48524530f7e952644a848130bfe9c22818254530d7f9b5480a864530df79b560ca148130df79c86d4a148130e7f985661a008530ff59536152024530dfe9526e0a148130fed9c62e95348130ef79a56018508530e77d526959824530dfe9b8484a548130def9c36d8a548130dfe9c56c8a054530a7fdc8484a954530aff9c8280a254530c7fda86d4a264530cfdcb36e982145308ffdca6c98524530e7f980615a9085309ff9cb281825453097fdc82e5a548530aff8ca481a254530cff5812e92054530ffc92054da548530dff1816d4a1481309fdccb609a354530ffe1215453148130c7fca96c9a960530fbf18128182545309ff9c82e95348130def9b6608a548130b6fdc6215a948530a7fdc22a5a954530fbd5316095060530ffc5314818548530a7fcca5499864530df5db554ca848130efcda26095324530dbf9b84c8a054530c7fcb96e98254530dfe9c86c8a054530df75816d52054530ebf9812e98048530d3fd856e0a264530cff9a86c0a254530aff8ca6013154530ff4d8554d20485308ffdc82e99254530aff9c2281a354530dbf9b854ca148130bbf9c8480a960530ffd1316011048530c7fdb8484a954530ebeda86093214530eef985601a608530a7fdc82d5a944130df5d536c98524530dfd9536c4a848130ef79a55498024530e3fda86099524530c7fda26d59824530f7e9206458548530aff8ca4818254530) else (if i<7 then 0x980a8827805040258080743044014101081f806809128000980486028062201501917800130090c07c0484e060242054015150250380f80c90048098406402a2604019102980a880480d8401a02a201501210c40090805da280e868120322d00487014015278118601980b80917c08057c000cc05c048c06c01207fe0402803a6d4f47d27f47520d40deee80734dacd0a94e77fec4e57bf4b1d25347741eecb1d19b43d82563f48507414150a13083233f7cf0b3b18fd33887e2f35fcd0a01ccc94428224e614cc232d3cadb28dc990173c94d1c8441d07bbae23051d186bf8c160c894e0746c8db20dc7920c85b964fec74f1b641ef18dc5c20c8150a614807315341ef136150b119c3f230583230df45370cea8970a5b86e2ae1d19107c22306bc13a45041ec173829b0318fd300841eefdf3b84685bf0aeb8be96f7ca538746bd7e61441ee0c8b2c60c8bd3a0c8bcc688fbc5171fbc0eef2bb264d515f293d1d1aeb88506141ba9ee7eb2c6e558320e27b8b2e1bb7ca0c8b726dacae6e46da76a084b63e0c898c60c88322d728fd16e5b5260c880707468322d209e282ad8322cf716660a61d1acda15082ad5b960c815f057c41ed07b1d1acb1b25054241ec685b1dc2ad8322c4eb0c457c8322c0815088bcafaebda8fd2bc91d1a4059e2abacae6eb728d2eb49ac820a6ab7c746ab0aaa51d184f0a9c107ba09dfd1a94deeea90aa25a8229eba76a9bd150a9a0a5de94e821293d83201ad1508746a482903a399290a2f68a07f456e5a23e8725b96084985285582128381d1a827a02a7ed9f1279b9e2907b83223f49d8675083227279bfa6c99a826835b9665a98c6305985260341ec2ad150a5e605ce5d596e23f4963e5721d1a55594e251b93fa3f493564b8926c685922a1e391b64502915fd190ce422821240583221b58fd23e38f1a39d8dd22748d2e3228c1507b8ba22cb8aba29177fe274892e23a79887468876200878d07b150a1c686d5f8b86606bf05ce17b41ee15e8506130841e0de7f460cd83220b77f4507b829a095821107b798a067812817380b601c5c7e00b7fb9fd10ab5fa87e2df6e7d45f2829151077c2deee7b15ea879fde621a89124081198b2135e4505cc2ca78702ca662ddff778817326f9db908f9d9c05cd5ef75fc2ad7559a6474b42ad1d1986c744027372ddc8e2a2dc717091c076f79b6d6d41b1b6bc840b6a05a6409cda3b102da0615f19dd13c0ee11d199b4072998b05cd93e22f192106b58ec5c082731b718c33a6d8a60e2d889213586c1d1984360981735fc4e9b06b42ca1a157d41a141731d5d7ab06b57762c186855d648bc4dd44f0310973c1a8971f5c096e55af074642607461d18221102d693594817358a42ca58311e557bd290571959108855501afd51b05cd4da1a894b151c144713c14124ab53f else (if i<8 then 0xc0e1832080b80f88053c000647013e000243f00029012180a81b0090c0480505c0e028203101715800090bc0008459100242305b000151cc2840d3c0048200242c87012158081b0b21c20348122c04015101080d0805381c40421034f000121884b800090ea2020036080f840d0202810210121602009094100485e00111009c4021880500cc4611016024301201712839c388057800404202a0343e0701f16800090806804902460240782387f00029181b0090805c0545a00028024301f015100800a880c4048054730a02a201d01f1010e0200c8c08409804862100242021015017f02f00012f013b8082381d0c0ac0485e0202be00025e042126409012164564380d0e0450ac05404805fc0bc0407fc01206203220ab305015019200d00680c8c2ac08405e0240c7c0bc03c04049208a028228701f014181f8068140091005407c0647a73b0e0243000014012180d01080bf8080a7801805c064418de0002802440260140121a838090804404840120242031012036180c00a88057c00034050803a074200b0260121ec46800140091004c0e8409c024201a021101480d0bc00048401390e07433030150121e0200ac4380f80c95800050048606204c200b015150200a00c8c05621c0480e88093e03e00034028500d0310170152006810e450140091401c0cc07c6063e0202802406c50150320121d0278080900d130780684a100242015036100a80380c8c15c048406202e025e0408fe02a187608012100d00f8090cc100480d86024066200dc8a70002801228558c2f8000a80c940c405c054604206c2f0201ff01e07f00280c80a880480e8400004c0243e07012101f80a00a8f4080c8048602802a2014021100400f880240480d8601202a2031017d88012014f02f0101fd2a4e8000a01d0c0240480e86e0004c024303f015100902a8805c20680242700014012181c00b8805c050540e0242015021100e8188801c0484025c0e02a3f0201ff01015f000143106f808090e61c048540e0a2024341e01a100a01b0b010064404201a0243f00409019180400908c200485e04156074302101501f019200af8002200c900480340d8606202a2d0001901518130090802c0500486857e000620324b03012110480908057c000487e01e0218c028400dc8a028012200f81b0803402c0a0048980910e028024403f0121281d02780f801008781fc040508032102101f0121d8200a8bc00138048780803206c301ff0000d01227817800b621c0361c048860004c024330501510090541362005121c0d8be0007c02a3014012102880908048054403fe03c0e315e005031017d88d8752af02f011094780c438090c0540e8402e024260401203a180a874000c40647e00028024300901503a181881080b809781023f80780a0050064401002a2032012100 else 0x3c08427c00048804202a201f88717800090140e81281c0486024212203102111038407c424048660b01602a390801510c2b80e8000a92810203e0620323c8a01a0211819814880840a0403f30e2015f000120c622822438805781c048621a06202e380b080f8220842404807c6115e00024300d0c048090842407d61c603e0422308015100a80a080cc0645a00034201420d10098405240004860862202015409100c0198812c048406c02802430ab014012180a01d0a623400530ba720323f000151295058240e8402a70e2042088484c22c000487a001604081880900b8fc000480507e00024042310d080fcc3f800c0c405c0487e0018c2d040181015f800806b400064602804207e30c6056012180c00909827c00048602bc0e2f00019100f80a7038dc000484211a000243015207100c06a1c260602a201a080ff038090c62b81c048603fc0e02a3031017015f00028280bf8088048108431402bc0e0244012809101304c140485a000322e03012101884c13404402510e2031015021180f80900b8f4e420867102f0001412828148a61fc00054701202a27390e838090804407c40240642607081980a0a620054403006c024301f387f001d03840d14000487a0810c60170121810cc47800c068a1fc0007c803e02bc0e3185015100c4800090c053c00048603e02824070c8381488828207802a2f000129881e820090805404c40248122017b01100900c080514000486062024201f607101404054124402f606201732a10048781c0545))))
def xml10 : Packing := (722,5,7,0,0,14,0,xmd10)
def xmh10 (i : Nat) : Nat := 0x30a24424fc282c1bec2100001818ec0b80001405e82050131dc524139c25bd18a01e4c21bc27a81795897a0fac1ad9a8d05c8980941f059f6001f021e41f480db411cc12cc1d289a4410941fb8075c00d0011812b40575d0f41a5c1ef018800000002e58a054c0167c1ba4116095a98680003423d0168c25d0293c477408980e6902800000a43d97400000003d9950154d93800aac145c11800000001c07f49179d38000000000000000181c40003804ac1b0000301c981a200ac4a1c1dac0059c22800030260c2440000c17140fe40c080b1800b413dca2ade5c44cb00ec0000c23b410c000281d8003b423780849db4000000000003003cc0d0513c000140de899f009e8251c5e400038d114287c991057949aac24a098198240001415d016de0aec5a3c20b40700001043fc0fa01580002528654c2c14981d40003c277c22fc02061ee455900b6c27c0036026c00014181c294410208c1423000018127c0cfc08ec05145b80000000301c1c27040e1406e4135811280040001063c000341a880a40142c9fdc0979a05d01c000248ac40d605ffc217c02d44c388f0d0b240f79dcdc02ac1500002c2214192a210014f804e4198c1940001209fc12000000000c26b81ce984240f2ed3d59a10093817f889f614240c48104000281ff441c856800021a65c033420000000001c227186c0000000000000002c00000000000c0bc00018821c20d81b540780001c0240003099800000000428900140001c0cb001941e298f6828f91500000000341ebc045c2640240000000410255809a49200001c0800000000000a2817681620660406110079cddc0e8c1de1a1c898ec9e3019e6d0cc06b01858064000045c58c010faa86960c04d71140111052104760000493430290c406f0032832c500a7c804140394a00e90009b142
def xmd9 (i : Nat) : Nat := (if i<1 then 0x409876f46e131600a548530dfa4a93825d2a690261dbe181721b2281514c39ee3026536a50a409853f5744c36e98214530efb0c0b8ad9140a8a619ef1c6604ba545204c2dbb3ae65262c0240986ef8605c22818254530b7f0e9140c0b46a8a61be6952718ba54d204c33eb2a6e2b7050a409873bc281816d8a254530c7ece43865d2a2902612fb9d432980689514c31dbaa6e317498a4098775654d856dca148130a7bcec194da94290261cbd9a36e132281514c31fb366e4140512a29877c654d856d0a148130c7ec50196c1346a8a61bbb181710a0609514c39f9346e4364502a29877f0605526cca148130d5ead438259b0428a618ff181329b0289514c3be9242daaa6542409847f6371536c58248130d7e4a9194daa62902615fc8db54d21609204c3be92a6a937050a40986bbc605c6284a948130efa4a9196a9b42902618ef9b6720a0289514c3b6b2a6c2b7050a409873f4281816cca254530c7dce43885d2a290261eb598568953600914c3b7a262c036454b029862fe729b8484a054530efa4a92a65d30690261dfc1216e131295204c33fa19698b00d2a429863fa721c22e9514813097ecec194a8a6290261cbf1802e9814c5204c23fa9b898b64c0302986ef472131480a960530e7e4d1b6499140a8a610fd8db7018268d514c3b692a6dc2a450a409853ce750ca6d4a148130d7a4e2aa4d1a4040a61cb5953601ba614214c33e92a4e2b6650a409878d661553601a90853093dc6cb885d2a290261af495232d2068d514c31f3366e2140512a29877d06cd526055148130e5acd9b70c034a10a61be4952718ba54d204c24e79b2e2170d2842986bd254dc56892020530e578c0b6cd414290261cf49a3715b2281514c2bf83a4d8a6252a40984be6750ca481a354530e5e8c0b50d9942902618fc9b3708a0289514c30d7972e310ad20429862be6d9c8280a25453083deee0a45cb4840a619f49c3709b5285204c3bf0242da26252a4098779254db6548a148130c7cce536898940a8a616f49d369552480914c357a302e0304d1aa29862ee6d1c8284a548130f52cc030aa9b4c10a61bec121718ba4c5204c20f7bb842972d2042987ac654d80615a40853087f4e9196d2b0048a616b59d369580614914c31d738cda14252a40986bd2548ca6c55348130c5ecd9b9050144a8a618fc9c3708ba545204c3bd8262db24252a409861ed2e5c1215a408530c5ece537098940a8a618eb9c4718ba545204c397a37498b02c02409861af325b66905220530c75cdb38850144a8a61ef095254d20690814c356b386c034ac28429872dc605b56a0a148130d7a4a938458346a8a618ee9b6708a0289514c31dd38ce1174a8a409865ea484c96d0a548130cfa4a9b84da9429026187b8b970085690214c3be12a6a936850a409863e6711c32e95148130 else 0x3409a070090c0620171741020150108b603f0016c00201f01b0803e01515c003e0700f8802e01210055e000281e621e00278000485e070ae1ee002e0200484036cc389e0010188404201510054360409a2802e01f1f81c0242cc404067d0110050203100d005c601700f8803ec87110343f000090807e100afc004b870805c3f0006308002100f806460170130802e0151008402ff01f801001610198406c100f806440150090be00100900d8403f0090ae000121006420260802406c201d040241bbc7b4f69ed7427b4005bf46a7b4f69edb5b638f6ccf742310f6a663da7b511d6fabaad8001ed2280029f51fa1b3ba678009467b6421ed3da7b632c5386905508bf67c8f48002113da7b4f68007667b5d0ab671e7b5b1b44422845991ed3da998f6b136027b4f68003da7b56a91456c3594b9ed3da7b462285000998f69ed3da7b52a1ed46a88cf69ed3da7b5089f20007b4000d63822182a800086000529a200060c0014a0001540012627029400000000000001262283d4528551ac000000c40000000000010c10c0000000000052886000000338550000002180000009009000024003bdc302db2a450a40987f92549c62e95348130dfe090b8a5d262902614ef9d6285b8295204c3bf82a4d8a62542409877f06e131480a548530e7e4d1b86d9140a8a61af9982710a068d514c23fa9b898b6454b029876d654dc56e0a148130e9f2c0b64c1152a8a614fe9d2281b8289514c3e6cb04a930254aa2986be3689c42cd8214530df64e32425d2a6902615fe1d1321b2281514c3be9362a92a6542409867ba719522e95348130cface1b90da94290261af7181714a12a5204c31df390e3174a8a40986afc604ca4818254530c5fce1b70d1140a8a614f78db69552600914c28dfbac5d32a98a409863f668dcb2818254530f5a6a92a6c135048a61cfd1d32e981545204c39f63a85d302a8a40987ad6549a854d8024530fdb0a930250304a8a61afc5a2704b3608514c31f3b74e2166c10a29857bc758ba6053148130afb4ea990d9140a8a61ef49a854d52480914c29f3ba859b74c12a2985bb6758a12e95348130b7d8ea140c0b46a8a613ed9d6329b154d204c3bf836a98a4054a42986bb6758ca6c55348130e37ad4b02db142902611ef9d632d536a1204c31f7394da264502a2986bbc605c6284a548130c7ecd9b905d2a2902612fb9d432920689514c29f73a850370512a29873d6369c36d4a148130dfa4a9194d8aa690261afc9a3708a0609514c3bcb2a6db30a50a409877f0485b54c4a848130f7a4a9b44c2a4048a61cf99a36d132281514c3de92a450974a9a)
def xml9 : Packing := (166,6,7,0,0,11,0,xmd9)
def xmh9 (i : Nat) : Nat := 0x3012016803e050817421e11000000348700e900181ac05c2a0000000000e4f000403009de0f9105804000642f06d024810646522a81c0808618800001201040
def xmd8 (i : Nat) : Nat := 0x6c009080360802bf800803100680171803410068017007c600907700004840005c0121002a0090a404221435d87b5eaa8f642211a08442239084200e3ac605c4718ba545204c3ae49d6548ca6c55348130e3e4605c470cba545204c3bb2152605c42818254530a6f43b131601b22a5814c24fc8ed68dc86c8a054530a3e63ad82710a068d514c28fc8eb68dc2281825453083f63b5a372ca0609514c36e49d6548a12e95348130cf9275952329b154d204c38ee181719c22e95148130b3e4790a0605b3289514c38bd181721c32e95148130e3ac605b6710a0289514c34b7181760ca6d4a148130f2d06a1b354981545204c30bd18136dc0609a354530
def xml8 : Packing := (18,7,7,0,0,9,0,xmd8)
def xmh8 (i : Nat) : Nat := 0
def xmd7 (i : Nat) : Nat := 0xfe0200485c2d05498136dc0609a354530
def xml7 : Packing := (1,8,7,0,0,0,0,xmd7)
def xmsamples : Array (Bits × Bits) := #[(0x2000117826510854400022f,0x3330103e9e0a44216660207),(0x2246ecc810011ae0448dd99,0x44c6ac4101b1a9d0898d588),(0x12d066918804048025a0cd2,0xa104084ee4c422f1420810),(0x5901f38812621030b203e7,0x51cc1f3a11119900a3983e7),(0x402d0c0044021160805a18,0xc02c0c160e422de1805818),(0x48208be262988008904117c,0x40cc8bc060143b8e8199178),(0xf130410005220001e260,0x11091302f204522e2212260),(0x10231c03480084002046380,0x3523140311a384506a46280),(0x490be00401aa40099217c00,0x2e3260050cea04515c64c00)]
def xmcolumns : List ColumnInfo := [(16,0,2031,0,13),(128,0,1919,0,13),(64,0,1983,0,13),(520,0,503,0,12),(513,0,510,0,12),(544,0,479,0,12),(514,0,509,0,12),(644,0,379,0,11),(768,0,255,0,12),(537,0,486,0,8),(578,0,445,0,11),(595,0,428,0,7),(529,0,494,0,11),(521,16,486,0,8),(672,0,351,0,11),(646,0,377,0,8),(856,0,167,0,7),(834,0,189,0,8),(626,1,396,0,4),(519,0,504,0,7),(543,0,480,0,4),(852,8,163,0,4),(130,0,1917,0,9),(709,2,312,0,4),(547,0,476,0,7),(690,1,332,0,4),(809,16,198,0,4),(673,0,350,0,8),(610,0,413,0,7),(689,0,334,0,7),(710,0,313,0,7),(714,4,305,0,4),(966,0,57,0,4),(632,256,135,0,4),(832,0,191,0,11),(527,16,480,0,4),(800,0,223,0,9),(772,0,251,0,8),(916,8,99,0,4),(645,0,378,0,7),(653,16,354,0,4),(742,0,281,0,4),(536,0,487,0,11),(548,128,347,0,8),(803,64,156,0,4),(697,0,326,0,4),(768,32,94,129,7),(992,0,31,0,7),(603,0,420,0,4),(961,32,30,0,4),(668,0,355,0,7),(913,32,78,0,4),(780,0,243,0,7),(658,4,353,8,5),(597,2,424,0,4),(144,4,353,10,6),(801,0,222,0,7),(80,0,1967,0,11),(666,4,353,0,4),(144,0,1903,0,11),(565,128,330,0,4),(786,64,173,0,5),(674,0,349,0,7),(533,0,490,0,7),(384,0,1663,0,9),(224,256,23,8,5),(526,0,497,0,7),(744,256,23,0,4),(996,0,27,0,4),(994,0,29,0,4),(770,64,189,0,8),(841,16,166,0,4),(833,0,190,0,7),(787,64,172,0,4),(596,0,427,0,7),(825,0,198,0,4),(551,128,344,0,4),(704,0,319,0,11),(900,0,123,0,7),(676,0,347,0,8),(808,0,215,0,7),(912,0,111,0,7),(614,128,281,0,4),(568,0,455,0,7),(658,0,365,0,7),(940,0,83,0,4),(794,64,165,0,4),(208,0,1839,0,8)]
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
  | 14 => lookupWord 12 47 4 12 4 4 xmh14
  | 13 => lookupWord 181 453 7 16 8 4 xmh13
  | 12 => lookupWord 493 2467 8 18 10 4 xmh12
  | 11 => lookupWord 292 1463 9 18 10 4 xmh11
  | 10 => lookupWord 61 309 6 16 8 4 xmh10
  | 9 => lookupWord 26 33 3 13 5 4 xmh9
  | 8 => lookupWord 1 3 1 9 1 4 xmh8
  | _ => fun _ => none
def xm : Forest := ⟨2047,14,fun j => xmsamples[j]?.getD (0,0),xmcolumns,xmautos,xmlevels,xmindex⟩
set_option maxHeartbeats 0 in
theorem geomxm : graphValid xm (boundsBefore knownx495) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=4) ?_⟩,listPieces_all (d:=2) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sxm_14_0 : block xm 14 0 1=true := by
  apply cellsBlock (ar:=10) (rows:=1) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allxm_14 : block xm 14 0 1=true := sxm_14_0
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sxm_13_0 : block xm 13 0 2=true := by
  apply cellsBlock (ar:=10) (rows:=1) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sxm_13_2 : block xm 13 2 10=true := by
  apply cellsBlock (ar:=11) (rows:=1) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allxm_13 : block xm 13 0 12=true := (@block_merge xm 13 0 2 10 sxm_13_0 sxm_13_2)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sxm_12_0 : block xm 12 0 24=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sxm_12_24 : block xm 12 24 36=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sxm_12_60 : block xm 12 60 36=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sxm_12_96 : block xm 12 96 14=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sxm_12_110 : block xm 12 110 36=true := by
  apply cellsBlock (ar:=12) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sxm_12_146 : block xm 12 146 36=true := by
  apply cellsBlock (ar:=12) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sxm_12_182 : block xm 12 182 16=true := by
  apply cellsBlock (ar:=12) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allxm_12 : block xm 12 0 198=true := (@block_merge xm 12 0 182 16 (@block_merge xm 12 0 146 36 (@block_merge xm 12 0 110 36 (@block_merge xm 12 0 96 14 (@block_merge xm 12 0 60 36 (@block_merge xm 12 0 24 36 sxm_12_0 sxm_12_24) sxm_12_60) sxm_12_96) sxm_12_110) sxm_12_146) sxm_12_182)
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
theorem sxm_11_40 : block xm 11 40 36=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sxm_11_76 : block xm 11 76 1=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sxm_11_77 : block xm 11 77 36=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sxm_11_113 : block xm 11 113 36=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sxm_11_149 : block xm 11 149 36=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sxm_11_185 : block xm 11 185 36=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sxm_11_221 : block xm 11 221 36=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sxm_11_257 : block xm 11 257 36=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sxm_11_293 : block xm 11 293 36=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sxm_11_329 : block xm 11 329 36=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sxm_11_365 : block xm 11 365 36=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sxm_11_401 : block xm 11 401 36=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sxm_11_437 : block xm 11 437 36=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sxm_11_473 : block xm 11 473 36=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sxm_11_509 : block xm 11 509 36=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sxm_11_545 : block xm 11 545 36=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sxm_11_581 : block xm 11 581 36=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sxm_11_617 : block xm 11 617 35=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sxm_11_652 : block xm 11 652 36=true := by
  refine @block_merge xm 11 652 19 17 ?_ ?_
  · exact cornerRange_sound (by decide +kernel)
  · refine @block_merge xm 11 671 1 16 ?_ ?_
    · apply cellsBlock (ar:=12) (rows:=0) (d:=0)
      simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
      repeat' apply And.intro
      all_goals decide +kernel
    · exact cornerRange_sound (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sxm_11_688 : block xm 11 688 36=true := by
  exact cornerRange_sound (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sxm_11_724 : block xm 11 724 36=true := by
  exact cornerRange_sound (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sxm_11_760 : block xm 11 760 36=true := by
  refine @block_merge xm 11 760 12 24 ?_ ?_
  · exact cornerRange_sound (by decide +kernel)
  · refine @block_merge xm 11 772 1 23 ?_ ?_
    · apply cellsBlock (ar:=12) (rows:=0) (d:=0)
      simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
      repeat' apply And.intro
      all_goals decide +kernel
    · exact cornerRange_sound (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sxm_11_796 : block xm 11 796 36=true := by
  refine @block_merge xm 11 796 13 23 ?_ ?_
  · exact cornerRange_sound (by decide +kernel)
  · refine @block_merge xm 11 809 1 22 ?_ ?_
    · apply cellsBlock (ar:=12) (rows:=0) (d:=0)
      simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
      repeat' apply And.intro
      all_goals decide +kernel
    · refine @block_merge xm 11 810 18 4 ?_ ?_
      · exact cornerRange_sound (by decide +kernel)
      · refine @block_merge xm 11 828 1 3 ?_ ?_
        · apply cellsBlock (ar:=12) (rows:=0) (d:=0)
          simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
          repeat' apply And.intro
          all_goals decide +kernel
        · exact cornerRange_sound (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sxm_11_832 : block xm 11 832 36=true := by
  refine @block_merge xm 11 832 23 13 ?_ ?_
  · exact cornerRange_sound (by decide +kernel)
  · refine @block_merge xm 11 855 1 12 ?_ ?_
    · apply cellsBlock (ar:=12) (rows:=0) (d:=0)
      simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
      repeat' apply And.intro
      all_goals decide +kernel
    · refine @block_merge xm 11 856 6 6 ?_ ?_
      · exact cornerRange_sound (by decide +kernel)
      · refine @block_merge xm 11 862 1 5 ?_ ?_
        · apply cellsBlock (ar:=12) (rows:=0) (d:=0)
          simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
          repeat' apply And.intro
          all_goals decide +kernel
        · exact cornerRange_sound (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sxm_11_868 : block xm 11 868 36=true := by
  exact cornerRange_sound (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sxm_11_904 : block xm 11 904 36=true := by
  exact cornerRange_sound (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sxm_11_940 : block xm 11 940 36=true := by
  exact cornerRange_sound (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sxm_11_976 : block xm 11 976 32=true := by
  exact cornerRange_sound (by decide +kernel)
theorem allxm_11 : block xm 11 0 1008=true := (@block_merge xm 11 0 976 32 (@block_merge xm 11 0 940 36 (@block_merge xm 11 0 904 36 (@block_merge xm 11 0 868 36 (@block_merge xm 11 0 832 36 (@block_merge xm 11 0 796 36 (@block_merge xm 11 0 760 36 (@block_merge xm 11 0 724 36 (@block_merge xm 11 0 688 36 (@block_merge xm 11 0 652 36 (@block_merge xm 11 0 617 35 (@block_merge xm 11 0 581 36 (@block_merge xm 11 0 545 36 (@block_merge xm 11 0 509 36 (@block_merge xm 11 0 473 36 (@block_merge xm 11 0 437 36 (@block_merge xm 11 0 401 36 (@block_merge xm 11 0 365 36 (@block_merge xm 11 0 329 36 (@block_merge xm 11 0 293 36 (@block_merge xm 11 0 257 36 (@block_merge xm 11 0 221 36 (@block_merge xm 11 0 185 36 (@block_merge xm 11 0 149 36 (@block_merge xm 11 0 113 36 (@block_merge xm 11 0 77 36 (@block_merge xm 11 0 76 1 (@block_merge xm 11 0 40 36 (@block_merge xm 11 0 4 36 sxm_11_0 sxm_11_4) sxm_11_40) sxm_11_76) sxm_11_77) sxm_11_113) sxm_11_149) sxm_11_185) sxm_11_221) sxm_11_257) sxm_11_293) sxm_11_329) sxm_11_365) sxm_11_401) sxm_11_437) sxm_11_473) sxm_11_509) sxm_11_545) sxm_11_581) sxm_11_617) sxm_11_652) sxm_11_688) sxm_11_724) sxm_11_760) sxm_11_796) sxm_11_832) sxm_11_868) sxm_11_904) sxm_11_940) sxm_11_976)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sxm_10_0 : block xm 10 0 4=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sxm_10_4 : block xm 10 4 36=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sxm_10_40 : block xm 10 40 36=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sxm_10_76 : block xm 10 76 36=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sxm_10_112 : block xm 10 112 36=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sxm_10_148 : block xm 10 148 36=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sxm_10_184 : block xm 10 184 36=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sxm_10_220 : block xm 10 220 36=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sxm_10_256 : block xm 10 256 36=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sxm_10_292 : block xm 10 292 36=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sxm_10_328 : block xm 10 328 14=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sxm_10_342 : block xm 10 342 36=true := by
  refine @block_merge xm 10 342 34 2 ?_ ?_
  · exact cornerRange_sound (by decide +kernel)
  · refine @block_merge xm 10 376 1 1 ?_ ?_
    · apply cellsBlock (ar:=11) (rows:=0) (d:=0)
      simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
      repeat' apply And.intro
      all_goals decide +kernel
    · exact cornerRange_sound (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sxm_10_378 : block xm 10 378 36=true := by
  refine @block_merge xm 10 378 2 34 ?_ ?_
  · exact cornerRange_sound (by decide +kernel)
  · refine @block_merge xm 10 380 1 33 ?_ ?_
    · apply cellsBlock (ar:=11) (rows:=0) (d:=0)
      simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
      repeat' apply And.intro
      all_goals decide +kernel
    · refine @block_merge xm 10 381 21 12 ?_ ?_
      · exact cornerRange_sound (by decide +kernel)
      · refine @block_merge xm 10 402 1 11 ?_ ?_
        · apply cellsBlock (ar:=11) (rows:=0) (d:=0)
          simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
          repeat' apply And.intro
          all_goals decide +kernel
        · exact cornerRange_sound (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sxm_10_414 : block xm 10 414 36=true := by
  exact cornerRange_sound (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sxm_10_450 : block xm 10 450 36=true := by
  exact cornerRange_sound (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sxm_10_486 : block xm 10 486 36=true := by
  exact cornerRange_sound (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sxm_10_522 : block xm 10 522 36=true := by
  exact cornerRange_sound (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sxm_10_558 : block xm 10 558 36=true := by
  exact cornerRange_sound (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sxm_10_594 : block xm 10 594 36=true := by
  exact cornerRange_sound (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sxm_10_630 : block xm 10 630 36=true := by
  refine @block_merge xm 10 630 10 26 ?_ ?_
  · exact cornerRange_sound (by decide +kernel)
  · refine @block_merge xm 10 640 1 25 ?_ ?_
    · apply cellsBlock (ar:=11) (rows:=0) (d:=0)
      simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
      repeat' apply And.intro
      all_goals decide +kernel
    · refine @block_merge xm 10 641 21 4 ?_ ?_
      · exact cornerRange_sound (by decide +kernel)
      · refine @block_merge xm 10 662 1 3 ?_ ?_
        · apply cellsBlock (ar:=11) (rows:=0) (d:=0)
          simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
          repeat' apply And.intro
          all_goals decide +kernel
        · exact cornerRange_sound (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sxm_10_666 : block xm 10 666 36=true := by
  refine @block_merge xm 10 666 11 25 ?_ ?_
  · exact cornerRange_sound (by decide +kernel)
  · refine @block_merge xm 10 677 1 24 ?_ ?_
    · apply cellsBlock (ar:=11) (rows:=0) (d:=0)
      simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
      repeat' apply And.intro
      all_goals decide +kernel
    · refine @block_merge xm 10 678 5 19 ?_ ?_
      · exact cornerRange_sound (by decide +kernel)
      · refine @block_merge xm 10 683 1 18 ?_ ?_
        · apply cellsBlock (ar:=11) (rows:=0) (d:=0)
          simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
          repeat' apply And.intro
          all_goals decide +kernel
        · exact cornerRange_sound (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sxm_10_702 : block xm 10 702 20=true := by
  exact cornerRange_sound (by decide +kernel)
theorem allxm_10 : block xm 10 0 722=true := (@block_merge xm 10 0 702 20 (@block_merge xm 10 0 666 36 (@block_merge xm 10 0 630 36 (@block_merge xm 10 0 594 36 (@block_merge xm 10 0 558 36 (@block_merge xm 10 0 522 36 (@block_merge xm 10 0 486 36 (@block_merge xm 10 0 450 36 (@block_merge xm 10 0 414 36 (@block_merge xm 10 0 378 36 (@block_merge xm 10 0 342 36 (@block_merge xm 10 0 328 14 (@block_merge xm 10 0 292 36 (@block_merge xm 10 0 256 36 (@block_merge xm 10 0 220 36 (@block_merge xm 10 0 184 36 (@block_merge xm 10 0 148 36 (@block_merge xm 10 0 112 36 (@block_merge xm 10 0 76 36 (@block_merge xm 10 0 40 36 (@block_merge xm 10 0 4 36 sxm_10_0 sxm_10_4) sxm_10_40) sxm_10_76) sxm_10_112) sxm_10_148) sxm_10_184) sxm_10_220) sxm_10_256) sxm_10_292) sxm_10_328) sxm_10_342) sxm_10_378) sxm_10_414) sxm_10_450) sxm_10_486) sxm_10_522) sxm_10_558) sxm_10_594) sxm_10_630) sxm_10_666) sxm_10_702)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sxm_9_0 : block xm 9 0 36=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sxm_9_36 : block xm 9 36 23=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sxm_9_59 : block xm 9 59 36=true := by
  refine @block_merge xm 9 59 26 10 ?_ ?_
  · exact cornerRange_sound (by decide +kernel)
  · refine @block_merge xm 9 85 1 9 ?_ ?_
    · apply cellsBlock (ar:=10) (rows:=0) (d:=0)
      simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
      repeat' apply And.intro
      all_goals decide +kernel
    · refine @block_merge xm 9 86 1 8 ?_ ?_
      · exact cornerRange_sound (by decide +kernel)
      · refine @block_merge xm 9 87 1 7 ?_ ?_
        · apply cellsBlock (ar:=10) (rows:=0) (d:=0)
          simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
          repeat' apply And.intro
          all_goals decide +kernel
        · exact cornerRange_sound (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sxm_9_95 : block xm 9 95 36=true := by
  exact cornerRange_sound (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sxm_9_131 : block xm 9 131 35=true := by
  refine @block_merge xm 9 131 9 26 ?_ ?_
  · exact cornerRange_sound (by decide +kernel)
  · refine @block_merge xm 9 140 1 25 ?_ ?_
    · apply cellsBlock (ar:=10) (rows:=0) (d:=0)
      simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
      repeat' apply And.intro
      all_goals decide +kernel
    · refine @block_merge xm 9 141 17 8 ?_ ?_
      · exact cornerRange_sound (by decide +kernel)
      · refine @block_merge xm 9 158 1 7 ?_ ?_
        · apply cellsBlock (ar:=10) (rows:=0) (d:=0)
          simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
          repeat' apply And.intro
          all_goals decide +kernel
        · exact cornerRange_sound (by decide +kernel)
theorem allxm_9 : block xm 9 0 166=true := (@block_merge xm 9 0 131 35 (@block_merge xm 9 0 95 36 (@block_merge xm 9 0 59 36 (@block_merge xm 9 0 36 23 sxm_9_0 sxm_9_36) sxm_9_59) sxm_9_95) sxm_9_131)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sxm_8_0 : block xm 8 0 2=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sxm_8_2 : block xm 8 2 16=true := by
  refine @block_merge xm 8 2 7 9 ?_ ?_
  · exact cornerRange_sound (by decide +kernel)
  · refine @block_merge xm 8 9 1 8 ?_ ?_
    · apply cellsBlock (ar:=9) (rows:=0) (d:=0)
      simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
      repeat' apply And.intro
      all_goals decide +kernel
    · refine @block_merge xm 8 10 1 7 ?_ ?_
      · exact cornerRange_sound (by decide +kernel)
      · refine @block_merge xm 8 11 2 5 ?_ ?_
        · apply cellsBlock (ar:=9) (rows:=0) (d:=0)
          simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
          repeat' apply And.intro
          all_goals decide +kernel
        · exact cornerRange_sound (by decide +kernel)
theorem allxm_8 : block xm 8 0 18=true := (@block_merge xm 8 0 2 16 sxm_8_0 sxm_8_2)
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
theorem caseFB : Impossible false (graphGoal 2047) 14 (rootB 2047).toFinset :=
  index_root (g:=xm) (i:=0) rfl rfl (before_sound knownx495 validx495) geomxm tablesxm (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem bound : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C →
      (∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 0 || y 3)) →
      PEqualNP.MetaComplexity.circuitFun 9 C = edge → 16 ≤ C.size := by
  intro C legal first h
  by_contra! small
  obtain ⟨u,k,S,hk,run,sub⟩ := initial_live C legal first h (by omega)
  have eg : graph=graphGoal 511 := by decide +kernel
  have er : inputs++[seed]=rootB 511 := by decide +kernel
  rw [eg] at run
  rw [er] at sub
  have ok : splitOK 511 [(0,10),(1,1),(2,2),(3,5),(4,1),(5,1),(6,2),(7,4),(8,8)] = true := by decide +kernel
  have g1 : graphGoal 1535=graphGoal 511 := by decide +kernel
  have g2 : graphGoal 2047=graphGoal 511 := by decide +kernel
  have v1 : vars 1535=vars 511 := by decide +kernel
  have v2 : rootB 2047=rootB 511 := by decide +kernel
  have ha := caseFA
  have hb := caseFB
  rw [g1,v1] at ha
  rw [g2,v2] at hb
  cases u
  · rcases strong_split ok run sub with e | e
    · exact ha k hk (e ▸ run)
    · exact hb k hk (e ▸ run)
  · rcases strong_split ok run sub with e | e
    · exact caseUA k hk (e ▸ run)
    · exact caseUB k hk (e ▸ run)
end PEqualNP.Outside.L_meta_3897

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
namespace PEqualNP.Outside.L_meta_3897.Tail

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def run (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl step w

theorem run_preserves (gs : List Gate) (w : List Bool) (i : ℕ)
    (hi : i < w.length) :
    (run gs w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
      calc
        (run (g :: gs) w).getD i false =
            (run gs (step w g)).getD i false := rfl
        _ = (step w g).getD i false := ih (step w g)
          (by simp [step]; omega)
        _ = w.getD i false := List.getD_append _ _ _ _ hi

theorem run_length (gs : List Gate) (w : List Bool) : (run gs w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp [run]
  | cons g gs ih =>
    change (run gs (step w g)).length = _
    rw [ih]
    simp [step, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

end PEqualNP.Outside.L_meta_3897.Tail

open PEqualNP.Outside.L_meta_3897.Tail
open PEqualNP.Outside.L_meta_3897

theorem PEqualNP.Outside.L_meta_3897 : ∀ (x1 : List PEqualNP.CircuitLowerBounds.Gate),   x1.length = (13 : ℕ) →     PEqualNP.MetaComplexity.FanInTwo { gates := x1, output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit } →       List.countP (fun (x4 : PEqualNP.CircuitLowerBounds.Gate) => x4.op.eval [Bool.false]) x1 ≤ (1 : ℕ) →         ∀ (x5 : ℕ),           (12 : ℕ) ≤ x5 →             x5 < (22 : ℕ) →               have x8 : (Fin (9 : ℕ) → Bool) → ℕ → Bool := fun (x8 : Fin (9 : ℕ) → Bool) (x9 : ℕ) => ({ gates := x1, output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit }.wires (List.ofFn x8 ++ [x8 (0 : Fin (9 : ℕ)) || x8 (3 : Fin (9 : ℕ))])).getD x9 Bool.false;               have x9 : (Fin (9 : ℕ) → Bool) → Bool := fun (x9 : Fin (9 : ℕ) → Bool) => x9 (0 : Fin (9 : ℕ)) && x9 (1 : Fin (9 : ℕ)) || x9 (1 : Fin (9 : ℕ)) && x9 (2 : Fin (9 : ℕ)) || x9 (2 : Fin (9 : ℕ)) && x9 (3 : Fin (9 : ℕ)) || x9 (3 : Fin (9 : ℕ)) && x9 (4 : Fin (9 : ℕ)) || x9 (4 : Fin (9 : ℕ)) && x9 (0 : Fin (9 : ℕ)) || x9 (0 : Fin (9 : ℕ)) && x9 (5 : Fin (9 : ℕ)) || x9 (1 : Fin (9 : ℕ)) && x9 (6 : Fin (9 : ℕ)) || x9 (2 : Fin (9 : ℕ)) && x9 (7 : Fin (9 : ℕ)) || x9 (3 : Fin (9 : ℕ)) && x9 (8 : Fin (9 : ℕ)) || x9 (5 : Fin (9 : ℕ)) && x9 (7 : Fin (9 : ℕ)) || x9 (6 : Fin (9 : ℕ)) && x9 (8 : Fin (9 : ℕ)) || x9 (8 : Fin (9 : ℕ)) && x9 (5 : Fin (9 : ℕ));               (∀ x10 ∈ [x5, (22 : ℕ)], (x1.getD (x10 - (10 : ℕ)) { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [] : PEqualNP.CircuitLowerBounds.Gate }).op ≠ PEqualNP.CircuitLowerBounds.GateOp.not) → (∃ (x11 : Fin (9 : ℕ) → Bool), x8 x11 x5 = Bool.true ∧ x8 x11 (22 : ℕ) = Bool.false) → (∃ (x12 : Fin (9 : ℕ) → Bool), x8 x12 x5 = Bool.false ∧ x8 x12 (22 : ℕ) = Bool.true) → ∃ (x13 : Fin (9 : ℕ) → Bool), (x8 x13 x5 && x8 x13 (22 : ℕ)) ≠ x9 x13 := by
  intro gs hlen hfan _ r _ _ w f _ _ _
  by_contra! agrees
  let first : Gate := ⟨.or, [0, 3]⟩
  let last : Gate := ⟨.and, [r, 22]⟩
  let D : Circuit := ⟨first :: (gs ++ [last]), 23⟩
  have legal : FanInTwo D := by
    intro g hg
    change g ∈ first :: (gs ++ [last]) at hg
    rcases List.mem_cons.mp hg with rfl | hg
    · simp [first]
    · rcases List.mem_append.mp hg with hg | hg
      · exact hfan g hg
      · obtain rfl := List.mem_singleton.mp hg
        simp [last]
  have firstStep (x : Fin 9 → Bool) :
      step (List.ofFn x) first = List.ofFn x ++ [x 0 || x 3] := by
    simp [step, first, GateOp.eval, List.getD_eq_getElem?_getD]
  have seedWire (x : Fin 9 → Bool) : (D.wires (List.ofFn x)).getD 9 false = (x 0 || x 3) := by
    change (run (gs ++ [last]) (step (List.ofFn x) first)).getD 9 false = _
    rw [firstStep, run_preserves _ _ _ (by simp), List.getD_append_right _ _ _ _ (by simp)]
    simp
  have computes : circuitFun 9 D = edge := by
    funext x
    let ws := run gs (List.ofFn x ++ [x 0 || x 3])
    have length : ws.length = 23 := by
      simp [ws, run_length, hlen]
    change (run (gs ++ [last]) (step (List.ofFn x) first)).getD 23 false = _
    rw [firstStep]
    unfold run
    rw [List.foldl_append]
    change (ws ++ [last.op.eval (last.inputs.map (fun j => ws.getD j false))]).getD 23 false = _
    rw [List.getD_append_right _ _ _ _ (by omega)]
    simp only [length, Nat.sub_self, List.getD_cons_zero, last, List.map_cons, List.map_nil,
      GateOp.eval, List.all_cons, id_eq, List.all_nil, Bool.and_true]
    exact agrees x
  have lb := bound D legal seedWire computes
  change 16 ≤ (first :: (gs ++ [last])).length at lb
  simp [hlen] at lb
