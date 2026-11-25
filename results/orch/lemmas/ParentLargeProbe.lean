import PEqualNP.Defs
-- First-gate certificate by freeedolin, adapted from dsgallups and the project L_meta_1667 extraction.
namespace PEqualNP.Outside.L_meta_670.ParentLarge
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
abbrev Packing := Nat × Nat × Nat × Nat × Nat × Nat × Nat × Nat × (Nat → Nat)
def emptyPacking : Packing := (0,0,0,0,0,0,0,0,fun _ => 0)
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
def cmpException (iw ow : Nat) : Nat → Nat → Nat → Option Nat
  | 0,_,_ => none
  | n+1,packed,i =>
    if packed &&& ((1 <<< iw)-1) = i then
      some ((packed >>> iw) &&& ((1 <<< ow)-1))
    else cmpException iw ow n (packed >>> (iw+ow)) i
def cmpWidth (g : Forest) (k : Nat) : Nat :=
  let (_,depth,_,pw,_,_,_,_,_) := g.levels k
  (if depth=0 then 0 else pw+10)+(wiresOf g).length+depth
def cmpNode (g : Forest) (k i : Nat) : Nat :=
  let (_,_,_,_,_,_,_,_,data) := g.levels k
  packedAt data (i*cmpWidth g k) (cmpWidth g k)
def cmpParent (g : Forest) (k i : Nat) : Nat :=
  let (_,_,_,pw,_,_,_,_,_) := g.levels k
  cmpNode g k i &&& ((1 <<< pw)-1)
def cmpOps (g : Forest) : Nat → Nat → Nat → Nat
  | 0,_,_ => 0
  | fuel+1,k,i =>
    let (_,depth,_,pw,iw,_,ec,ex,_) := g.levels k
    match cmpException iw (10*depth) ec ex i with
    | some ops => ops
    | none =>
      cmpOps g fuel (k+1) (cmpParent g k i) |||
        (((cmpNode g k i >>> pw) &&& 1023) <<< (10*(depth-1)))
def readNode (g : Forest) (k i : Nat) : Nat × List Decor × List Decor :=
  let raw := wiresOf g
  let (_,depth,_,pw,_,_,_,_,_) := g.levels k
  let len := if depth=0 then 0 else pw+10
  let recp := cmpNode g k i
  let ops := cmpOps g depth k i
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
def cmpNewRules (g : Forest) (k i : Nat) : List (Nat × Nat) :=
  let (num,depth,cw,_,_,ow,_,_,data) := g.levels k
  let start := num*cmpWidth g k
  let pos := start+num*ow+packedAt data (start+i*ow) ow
  let nr := packedAt data pos 5
  getPairs data cw depth nr (pos+5)
def cmpRules (g : Forest) : Nat → Nat → Nat → List (Nat × Nat)
  | 0,k,i => cmpNewRules g k i
  | fuel+1,k,i =>
    let parent := cmpParent g k i
    let fresh := cmpNewRules g k i
    if parent < (g.levels (k+1)).1 then
      fresh ++ cmpRules g fuel (k+1) parent
    else fresh
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
  let depth := (g.levels k).2.1
  let (ops,bank,ws) := readNode g k i
  let values := ws.map Prod.fst
  let rules := (cmpRules g depth k i).filterMap (fun (a,b) => buildRule g ops depth bank a b)
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
  let depth := (g.levels k).2.1
  let (ops,bank,ws) := readNode g k i
  let rules := (cmpRules g depth k i).filterMap (fun (a,b) => buildRule g ops depth bank a b)
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
def g15l3 : Packing := (1,0,1,0,0,0,0,0x0,g15d3)
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
def g31l6 : Packing := (1,0,3,0,0,0,0,0x0,g31d6)
def g31h6 (i : Nat) : Nat := 0x30be670208000065000016357504004755c084
def g31d5 (i : Nat) : Nat := 0x3f481fa20
def g31l5 : Packing := (2,1,3,1,1,0,0,0x0,g31d5)
def g31h5 (i : Nat) : Nat := 0x300
def g31d4 (i : Nat) : Nat := 0x5dd45
def g31l4 : Packing := (1,2,3,2,0,0,0,0x0,g31d4)
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
def g111l6 : Packing := (1,0,2,0,0,0,0,0x0,g111d6)
def g111h6 (i : Nat) : Nat := 0x8000
def g111d5 (i : Nat) : Nat := 0x2fca2
def g111l5 : Packing := (1,1,2,1,0,0,0,0x0,g111d5)
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
def g189l7 : Packing := (1,0,3,0,0,0,0,0x0,g189d7)
def g189h7 (i : Nat) : Nat := 0x42f9f28c08140000000020f801630c00d0
def g189d6 (i : Nat) : Nat := 0xfe903fa20
def g189l6 : Packing := (2,1,3,1,1,0,0,0x0,g189d6)
def g189h6 (i : Nat) : Nat := 0x18000
def g189d5 (i : Nat) : Nat := 0xb7d8d
def g189l5 : Packing := (1,2,3,2,0,0,0,0x0,g189d5)
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
def g191l10 : Packing := (1,0,5,0,0,0,0,0x0,g191d10)
def g191h10 (i : Nat) : Nat := 0x99090000b500000001a152f05d5c000e4006080015749fa60141c73802b0a68137976081bca199eaaa3d961388c0f3a0002328c00084a05000089c2a
def g191d9 (i : Nat) : Nat := 0x616286029a59230b018b28616280c68c2870c0638b24616231448c2c3018d24616029448c2870c0730b18580a59448e30a19c81c616228c2881c05dbe3acb3c89ba98e983a9184600ff481ff183fd307fa20ff54dff083fe407fc40ff4c5fe103fd637fa80
def g191l9 : Packing := (12,1,5,1,4,9,0,0x0,g191d9)
def g191h9 (i : Nat) : Nat := 0x140000000000000198cb0000a04e08a520001a51c20000531e80b64388d00078963d80a7524800343b41a670800007a7cc632d75239502d607286400000000060840000002a100028a67e35dbbd50001a6c315cd7a0d113ac27000121800052568158594ec000682af90000f6880000010b6fab800321ac31374a97c0018068243a2b09f06ef8c8000c984c7fad8000732e29d36fd3c9ba4660000003c50a43a2e72f0000037c5c484413000060966343d567081fd24000161fd8fb857db1616c2d70bc0001da504981c000a8cb68709baa54393350153817e93b2ee08a0b35c971e4812648c40cf0c890074a5b901b85c19b060f0f30f9c6d46f822909e468ae58b600010460007b00142a8dc0d2c800031c60005ad28d4a60000000000000046100000000000000005978000750c07fc419a5a33000612dc38451b04000033fe570000002d76000244c429f180a5d34b0ba1360001a731afd48a565b2f860060014b1d8111aaaac600056d800000000026c2da68678cd5b803ae00010d91906c6000000173ec82c4200058c80000000001b509c9847ce37e90001c466a9e954000000c99484d7ca82a800f93447182024f80000c48dc000596030083ad05a1c75006c10817410814060062c35820051841c00801071c96460c20000020c70c01c908b0c0000080000041016
def g191d8 (i : Nat) : Nat := 0x4c110c062140c42c4071890f0463058a18b150862c50860b8d0082831823114018c160c6305c018b4a0c63050880710c078063058a121c19860b0e9611498a121c90422848718b130071928858a121e345c38102c3831e00a6092130064c48719416243906043847890e988283885874b0882f1085098431e244312884874d0882c4c18040130e21610e0e08c5890e3162444a00888c162439460710b0e2170040c23048848710d4d160903c110b0621e1c51a2e1c041a2c58b00ae2cf7b65616cfa68143492c2d6b31d5462ed375506b69214731d40cd685a551174d6cf79d7344c74b793b17641aa835b1c0508a18bb174d68a135b10e0a0e67d8f2c130e677eaa1d2b8b35a1b4c71ad35a6b5bc33b642c5584aef35aa70c729c5aaad0d69ad5386395429c4f69a1238e6468869039f435a6b4e99b235a6687318e2e85d0ad1472684307c8e61a631c5a0a11001b42d04704c04c007fd529ffaa01ff5c6ffeb1b7fd40bffcc4bff5483fe9847fd634ffac13ff4407feb9dffd615ffa617ff5ca3fe883ffd428ffee37ff4807fe98a7fd503ffa217ff4857feb107fd207ffa421ff9ca3fe90a7ff73bffa64dff4c93feb0d7fe326ffa435ff4847feb9c7fd523ffac07ff5897feb157fd623ffac01ff480ffa38ddfd71bbfae49fe481affb907f771bff22097f5d56feb895ff748fba603f74c8efeb955fd736bfee0f7f5c1efebad7f7216bfee37fe442effb91ff5213bfee23efdd26ffbb4dfd701bfaed57fdc42ffb945fd717bfae897f5d96feb9a5fd732bfee2f7fdc0fdea12dfd726ff26177fdc87ee981dff753fea62df74c1efeb91dfd703bfae237fdca6ffbb05ff738ff26097f5c6afeb8adff73bbfeea17fdc06feb9dff920abfae29f74c86feba35ff759bfee33fd544efeb92dfd721bfeec77ddc6eeeb9a5bf749
def g191l8 : Packing := (113,2,5,4,7,11,0,0x0,g191d8)
def g191h8 (i : Nat) : Nat := 0x38d5055793c3679268754bc6188000001bef920589c626a6500070140c8d5de5f1d7a21d0344d98ee800183ee488000001119701a189f7ac18d073c41c5a460f2f6dbb0d3e90a06b82f5bcc02928e3aa852e880000109c34616429775d57a00841de8968c753cd4f7779436ba625de899899071c11166c07285d4158b1c40cba3819701ff1ed4e0000001d75e386545f25c03c4e3ccfe7905e2217770000000a100005011f8991186d800000144100008f313025a433c0cd88dae660be94000121c0000002c88000000655b0af52342fd8c3fbe11d039049a5a1e7325180004d4e9a308f4f4000000ef1802b07e014cea170acb800000009b4c4008e61bc79a059a0f70fccb137f85b2554dc0000000f21e93d1260001258003490000000000283ab340000000b1c0000000003185023a5319608aa0001913478000000000000000046621400000000000005b0dc8e000000426e6c726f99d415a6c3045000127023e070c8d80b889403631ef964fdd2196b35879ca860c0656093c9b66e604e1a08c20003c8494d7228964094caf59a8139a149ac000c151050440002c01002420821110471482078810951470800420470000020001001c02830c50400010400800405400402040000c00080070800c100000d0040151000c0040141188000004000
def g191d7 (i : Nat) : Nat := 0x61043024a10a0c086802161090d084300c400000270000000000000000820000000000007500000000004e1a00004e00344100000000000000000000000000680000001a270000001a000000000000000000005b4e0000000000004100000000340000000000001a0000000000270000000000001a00001a0000000000000005000000000000df481873fb0f5a7f60876fa908baff8699fe70233fa48386fbb8c49fd82116ff0b1efde0775dfc21f9ff8159beee3b27fe05b4fec08efe9209fbf2401ffc842fcfec111f7551b97ef031b7de0506fbc085ddf71777ef03967f61f5cffc0c3fd5513bbf2e4fefe602b6dfba709ff802f3fb02b77b480f67ebb5ddf4810b7f30142dfe165cfec107df92025fe4211a7f6011cfec088bbd84ad7eb03b67fe00257fc36addf7115beee3967f6001cfec12fdf55145bba42977ddc4fff49060df53141bef077e7f60896f6a931dbd427dbec200e7fe072dfbc0dedf551313fb04ab77dd8ecfec3d09fd81a93fb00be7fe042edeaa41ff110bfb7ee99f7b485cefab089bbf84d3fe102327f609e4fec10fdf471a9beee36eefe132edea111bf781a7fe6e27ef7e0f05fbc0d8df721137ef032ff948185fbc0dcded72b59faed4a7fe0425dfc24ddf58305dbac79f7d1c72efbb8d4ddf7135fe0e27ff54c69cfbc0ee9f781cb37f08da7be08bcdfc22c9bf8471fc240d25fe15347ec31c9bf84cb37f08627de042cfac08e
def g191l7 : Packing := (116,3,5,7,7,8,0,0x0,g191d7)
def g191h7 (i : Nat) : Nat := 0x30450ac641c0062400b2c00a0c8100000001c50000042a883a
def g191d6 (i : Nat) : Nat := 0x8fb4c73c9fc2aa8fbc8a4c5fc354cdbc21e8fbc8d9cdbc211adbca138fb4c11cdbc2428fbc8eb8fbc8a5
def g191l6 : Packing := (12,4,5,7,4,0,0,0x0,g191d6)
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
def g383l12 : Packing := (1,0,6,0,0,0,0,0x0,g383d12)
def g383h12 (i : Nat) : Nat := 0x2e190000e44028954b00129713b90021c5c400a24a286e030000000000d800006790000005048cec0c584c000029410000109
def g383d11 (i : Nat) : Nat := 0x3860a108203050904a20305090e1418080e18284870a0c04070c14242826d1a96c2f0000ff820ff860ffa60ffa20ffc60ffc20
def g383l11 : Packing := (6,1,6,1,3,8,0,0x0,g383d11)
def g383h11 (i : Nat) : Nat := 0x605ec8c0000001117d3d8e632bfc434126a560a0c97cd1c2e0006879dce0130002029832241d31f89848e70800000000019dd990a81d83401050198b41ca520a2f40adbada290270002212000f0240555b3c62d0c010b44640b0000000000a02000000274e000193000140ac0e19590854ad62490de02102d21d6156142944000d8a4082dc48550007f7944400014100014220513068000058000991281875380f661504984eda4b2e787cc39625232a002653d245061c2fea2000000680400000024e94b1850b1ad217010100600b00017050301c050070e260404451400410
def g383d10 (i : Nat) : Nat := 0xb888787058561e160e0284c443c2c28251d1a16130f0b0701c30221e15858261813110a084746858448c0b8704104c442c291d1a16130b05426221e168e8c6110b0a458428884a28c3c28211b0b04c2c28170a413121109474630887a44323609838341f0c81e148b86412110d0b0a09305852342102c2a10628221c168d0b8270a09841878561e090442e1c626120e3120b0a094746308880705c323183c2c28251d18c1c1a0e8c8b8660c0b0a84207870503e160e01c58442b0b04a1a16158785838070b0987c2c128504342823048161220b09c118885616090443c281f0f0b070101c1a160f8785838080d0a47c2c128504a3e1e160e01c4022b0f823003e160e013e6757e45b575865bc4d7e6ee5a7b055368c4f399d2663a457834ff5ec3bb73cda59a2ff594a953423b3fc744e219f3145b4a410317c2442a02508e0a812825001ffae2fff5cd7feb83ffd73bff8e77ff5cc7ff41affd713ffce33ff4c17fe398ffc835ffe60bffe05fff40bffe713ffa623ff4c4fff398ffe313ffb02fff5c67fe38cfff835ffe623ff60d7fe40bfff713f7f08ffe5c0dfec1abfd8137fb076ff60cdfec08bfd8197fb0e7fe5c1dffc0bbfd8317ff06af7a0ed7ec34bed8237db056f760eddfc23
def g383l10 : Packing := (47,2,6,3,6,11,0,0x0,g383d10)
def g383h10 (i : Nat) : Nat := 0x71198115833604b01a0000606e88fc000242d7c1fb0faad280000000907200000000000000000011a60000c095e07a03c80000000207200b0000f0374218000083d74340000000000010fe000191d800038c8000000000050001a19c0000000f0d80002417105f0001002bc08ec1b0001e12c0000000f0e7e92d81a6801000081e2997c07b60460002f86e047b093591c0b42863642440b4814a40900000001016701f80992cbb0308000c10b416439d943b147aae0000000140000000051cc437e4b4604d43368120000516302b9f1000004067d0c8043000061b56b100000c580000000783f104c0003fbb80009070d07382c4f54000000014a410460001715080ea8740833a5880002404721a41d7010e870e0a6000041e7802d68a0000000000000016605c32d9336823a9a000d7e20d86d416e10a400828f5440c813b83e60a220d8fa1581020e4099e8197842301210c9aa808357404e01fd304041e1023c6482e6b2cf063e21e71a6056370a003201825400056b139c293c35f0f8311d9031132ca772115827b06218a0203561cf86910f5a5f4b8b233b382b58ee49dec3300d7802d8c0502fd10109b0c0a907ee0a0fc274022d3a10d5060b108505d001d3c31732301838cca1790204071480aad97c1b8000509cd0a402a9482901e3171c30000064ac78e80004854e040ddec841106f32a0420d715820cb2810092535383b24a5005e83218280109ecf40006a47e0540003c1d6c17800c84f7001b077b0900001c268000e088000143b221e2f0000390d00040c17340800211f04000c3852005c082b04030102880201024c3d0e17000f0511410100573e04001200070500016400040b010407000d00010204010004000a010e07000000003720
def g383d9 (i : Nat) : Nat := 0x84a088460f105c220ae1902685420c220e820c2c11828c12112842c0b103c162a3841fc310448a20d04481107f0881182084210582441608641cc6183c1c282c104230c88320a16182220588240b105a0a2108820b04207021a0bb1c60b820833411314214087e85c118388c2e17044170808280a040f85c1e00c261836105580a881c1e1f0440b083c1420d8460830f03c412088a3bc2e08c280f151420f0870162e18436100642647e0920f84105c2c20c87841c2042e10d06440a08402110c10346a28b821090783c0103b0bc1183f822bf457f3d663c742af0d5fa2be23eed24f32f384afdcc32e57e6995f2bf6f8af95f4e969ec815f11f60ab585c2be65c6f15faa951a8e8ab2be65e7c5069f093e4e4e19a657c47cb393857e4295f4e8dc4af95f2bf1b8af95f47057caf9ea8af1261915f837011edbcd2beeb5cb37f6e2d8da1b2c0b8c557f2de2beaf9582995048e0afa744ba93c272381568610095f00057cf51ca3663e8d99b334a65cc01722c857c9b11f2103e8760de1a02e45589d11e2043505c09c0dc0b800dfeb89bbfd81a7f7f0976ff1cccbfecba9bfd81737fb0ebeffe1e5bffcbab7ff97977fb0ef5ff65e3bffcbbd7fd978affb2ebdff65e8bfecbad3fd98b7bf2e09cff662a9fe4c5b3ff98ae7fb30c4ff262eddfca1b3ff912a7fb315efb609b9ffcb9d7ef9256efb2aa7f64c6cdeec1bd7f99092dff2cccff662cdfb3897f7b95467fb2f0efd6048def41af3fd98a6f7f28d6fd5c4bbdeca41bdf838a7fb3126bf64449fecc277fb90767ff2eaefb9cc2ddfca0f7fb907b7bb2e75f7e4ec9ffcb8fbbc914b7bb06bddf6566bfcc837bed827e7fb30fef760ebbfcc8553fe98b67fd3174ffe5cfdf6cb876fd965b7dd221ff624ecdf6c887bdc973b7dae614ffe627df6c155bef730afeb2316fb60a7ddf48a5bbf914b77f08d5fd6464fddc213bbf84275fb0ccefb64c3bdeca31bbf84bb7f7308dbfe5a7df6c127bf681875fb0d36f7e5cebf7c935bdd838e7fb3136fd60549fecc393fd972e7ff314dfe6413dfcc1a3bf581767ff2e5defe525ddfc2437fb90567fb30b6f760d6ddfc2417f9905b5fd2226fbe4959fecc4f77d95a2efb2b15fbe49edef4b9dbed8277fb66365fbe49d9ffcc33bee970ffaa62467f61e79fecbafbdf839777f08a6ef64529fecc373ef925677f283cefe50d
def g383l9 : Packing := (136,3,6,6,8,11,0,0x0,g383d9)
def g383h9 (i : Nat) : Nat := 0xa16f054972c28000915083d009e0b000184b4aa00070df9a0000000103800000000040895c7d1f430452c83b41000000066c401a931403589000181590e60c4006e970739878c268f4319a8a1e8a227410f80515a000677800202f029915b907440e6c7f8b08b068a9c416408c84be1fb32f040001432000000000000000000001daa0990d58b4800e1d917e01640581811720991cb65f653999ed0240cf0c80400004d08a6610820084081054000400010000a42100804
def g383d8 (i : Nat) : Nat := 0xa1020585850a08102820c84140000000000000000000000280000208000019000000000000000000000000000000000001446500000a0000000036bf9685cefe1c72bbda74eafb68ceb3bf8483cef5c4033ed8710adfe96073bd7101cdb654efdd171688fdea4923bfa4648fb689d32bd862f8fbe89da2fda645afa6802b2bf9685ccfe11a736d954acfa6091f3af9414aebe8812bd9a03ecbbe58e23eda26e8efe908e2ffa622af3688fb3ad946c8efe917a3eda92b8bfe982e2ffa613c9f654a73af8427ad7694fa2fda865acf6953a3dfa926cfa6092ebe6a10aadd6958ebada40aaf96842a3bda917ceb650ee37fa561aebe90c333f9533cee6111e3eda80c
def g383l8 : Packing := (53,4,6,8,6,7,0,0x0,g383d8)
def g383h8 (i : Nat) : Nat := 0x834601a000
def g383d7 (i : Nat) : Nat := 0x295fdb594afedaf
def g383l7 : Packing := (2,5,6,6,1,0,0,0x0,g383d7)
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
def xul13 : Packing := (1,1,7,0,0,0,1,0x130,xud13)
def xuh13 (i : Nat) : Nat := 0x603511000718f15175000a06672412001000766b71408d13d02b65e04c63a61062000000000000d172738053002071800d9980b
def xud12 (i : Nat) : Nat := 0x2582c9308c3d1308c3e1303005854289287a270d848020210f0722d1308c3e1a00907034198b052270f86c0c01593c4e1f0982c09b269287e27098230461e89c3e1b098180211387c3613025c983f1387c260b0278edee661393f8c31d844003ffb02ffe90bffaa2ffec8bf7f28ffc902ffb22bffc8af7f28
def xul12 : Packing := (9,2,7,1,4,10,0,0x0,xud12)
def xuh12 (i : Nat) : Nat := 0x1e0e5c5a0820865e4113812d88ab840e148c0f6034000000000004b18d2930127592a019d02f025c01fcc260001033c0000000e03a0000000501f0000a0f246188ada0056c11c9a733120976041852903e101402e119d6917e02cc13c02a180ed00b20bb426c0032119cc59c4a80003026e11f004b8431085602d81200000001a543c06800000008102024000097406498000204ab04200000007046100020a001eb9b8000000000000000e69ce42ac1388310052200409073c1666c00e040400000001806a80a2b0b27a14104c1553960001c0bd428fb95374cd48359c208bc0a7e063011b04c0000000000015b8701f0049c0ae030607620dcdc5a8045605c15681980000000208841680002039c04602700008191aec501a900ce00d5541016201b276c0000000000000001498453e0aae62a000201d48070767a0cbda878d1d12c814041b234f516640ac0000326027e8d0c822a82654103000620000001210001001060010e0090004000021300201222001030010104003000201007010039100000000001220000000200340090000060004060095000010000000011
def xud11 (i : Nat) : Nat := 0x484a185992a2608c00e05411800c2246615c0081c16e1b0440f8280721a80b4a107c1c0530032480d0280721a05600749c220390d02b0031421003e0d8340730270a01fc3f00201a0560030a81a248614042d0719202b06c00c0701a0560040a81a64b00203610d414e106168440d834c581544a1083600a068140440e205e08e0030d03308e8920540d01c0681580181e05192c00812023448c1fc0045860d800c1a0500e80081404410b2544c1060b700103b44c0980102f046891b2d0470ec3709c0c007088190518ba2607305ac2600308c1d64d9203a89820e0a60020380a82381800ac9e00205192e1b84800b87f0fc370240b0270841c06d8630480e0360551283982604689184c0f022349023068146480aa2684c012115258781d44a10607814c0060da3220741c06f0f618a0d028c961e07513431c1403b00182210d021c3c0e0340aa2686e0700505a0ed1380101f06c1a6480ea27863f2408d13c3709c0982a0a411a27812f250781cc5c11c3400765b9283e0861b84e060043240881c0530dc0981c6480a61b8128540d5240701a0540070c82a06a92c3c0e0340aa270050620d5240701a0570500202b08821e4a89e04c1403a0a61f44e0060b818c3c0da2700303c0d32544901b064146480ea27863828c941fc3709001814e4d92038815f258781d44942305292c3c0a800c158420a32787d13c0e0080a829a278120501103ac5d13c398250680e02b82e04c0d8358781d44a11c31f0fa2e89e1f86281544d098010190601764b0fa2784c01144f0fc3709c09631f16c89fc3aa15305e80ebf49f4af827afbd41b3af0f7713ad5d4ce8370d37b5b94ca36ceb571a5ed0c679b341946c62624b0717f2bae5b6ad295feae6557aa594bea324f8a6c114e98d4b5242d1947e9453a2390ae80c3f49f68ee274437c9ae0d026362f09680ad251e25a918083e3de1ce8dc064a2e415b8a0047e1ea0de85f02760f005c823006e000fff54a3ffd826fff615fffda98fff689bffd928fff655fffda57dff6a5afffa96ffe48177fea96dff6a62fffa26bffea5f7fda25dff6a5fffba83dff655fff9a13ff754d7ffba13dffaa62ffda97bffe8977fd925ff768dafffa57ffee94f7fd521bff69577fd825dff6557fbd814dff61477fda55dff60877ffa85fef54537fda85fef4853ffba06ffe694fff9206bffea177fd985ffe60177fd928ffe601f7ffa52dffe8977fea97ffe6a0fff9208bffe94bffba059ff6a627fda55dfe48077bfa45dfee8177bd514def60537bd914def6853fd93139ff6a5ffd95339ff6a067ffa559ffea5b7f92059ff68877bd214fee4813bf9808bfeea0e7ffa82bfee8167fda51ff6e8cffe9207bfee81afdda369ffe88a7bfa45
def xul11 : Packing := (86,3,7,4,7,13,0,0x0,xud11)
def xuh11 (i : Nat) : Nat := (if i<1 then 0x5ae1ab4079e09050a5d6ceb457b29c602306b11011eb14c0afc14d10cb26b9a08490b5f07fc0ac80a0108babcf202e830dc085576c0b5894be36a9d282273f101eb105813a00000000000bf01ae07866c9a75660c920929664f12780710000703f0000005612a27014300090a2c08f0000d0aa00006038000000007297505e40959033407c9004b00a9083e6b7503bb001f70c0b0d00c100c09062d10e6048e67007a7b09ed0297054013da04e1380521fc03703c290b8d691a06a509c102f308a0000000000000000a1afc6b300000000b199005711a00662b89c60bd766f70cdc01221c92036b0a4d006e74ef11c215870a75028c7a2603cd075507760997002d6b0f13820506005707677a9c0b06696c052b625928d3b951070e0b70000000030a1f0abb0930000d060d0a300c200008024a0d010100000d04044580000000040650000c25630cce06fd1d0000000000000d04fa673805d91a280b9802231b5eb57b044206ce019a042539a704a204500003227203eb016a69f5047c0a80000f1bdd0bad146119f8114f07e00007784210c0000a24d0000c13f20800000b06e0000f6bf0000876d000016ac0000000000000000918f209bf046b1b90180a143d6350000db9a30587068000080697a970000d66af03100000000c05b008ec06b0000208d8007000020883155e097009101a400000000000000000000112c20c39061a05c802a3623b63f400ca055686d80ce007d000031b720c7b26d91b0000000000000000000a951c2f043000000000000402c76a370c8b09a000000009059300f110040739098000031a140517035d0ca007b50673ba301c741c3503d5259e16bd657c074b049361a0000b02b52bee04c3a56e6c00000603200000000606610b6b0094753d08c70b1901d303030261355800ee053e03a50c53081d04dc0b245c270be60208039d2a166af000037b7511100000000000040ae57c200bf46219008d0219157f1b6202db01c4041b07ada0c801f305fb0170082e671a08600000000b087f0b3100d00000000c0cf000093b310c6f02700300000004401e00f0010010040000c00000440000140800070070400400030001002800000054010000003890056000000c00000120120460c01c300204c04000600100000000301a04000300000000f08000000e1c000018004d88000b0050020000002410000800061010c000100068400241400000000004008040200008f08100000000800000c0004004400402000010001000010800000003c00010c00002400002c00800001800400800000000020c03800010c00003400030001800800c00410800000420800030010000870000000002400000400000000030400000010070010000000000800030430000010001800000400030020000400000c2001080000080000 else 0x61a8e09db025f680e66d0000000001a6a3d0f0a680c4e04b1663c6ba417eb764c0b400000000f094c018c1b3e2ad000001c870340000809600000000a01b72c2000000000000b176f74d0000406300000000f015506de67820bc00bb000027b2366ce251206400ad94a3c1ae67c41089409fb0031013c0722774)
def xud10 (i : Nat) : Nat := (if i<1 then 0x21060997cc3120589ce018685f29ebc310835e51de48b42d0310cedd78469d0c311c483103103102d0311c089cc685b183109cc6843109cdaac2d11b83119e83108359510f98e43102d187980c3917cc8343104a84a8310e317603117203103116e16a03104a9660ced5f473155c3114f14b03103113952fd1792bd1f84a83102d03103111b83103103911788351383103110f8e303103110b9020f88310f1c2d0eb0310e70310e30310df0d849cccecc54c14ba8b3c310aa4310a0c9cc3109608f48b43103108742d08343107703104a87303103106c46846443105545144a83104683fc3103903243102d01880f00033fed4d5affb64cfbf6a923ef7b74d37fcc03aef7f29537fca8c4ef7f293ffecc294ef7f2947fec5d12ef7f294ffdcc08bbff7610fff49055afff70e37fdd054affb6a8bbdfca55bff364b27fedc3abff36b133fecc3aef7b4ab6ffddc2bffd2414f7fdd051cffb534f3fec106bf7b6ab7feca989bfef6343bdea915ff7300b77fcd92cef7f294bbdea91affd2a512ffdd84eef7f29433fec2a3afff6ac7bfcc29bdff750afbfcc29eefdaa4dbfdac0aff7eb0353bfcc2cbaffb6adaeffdbd1cffaa447ff8c0c0bbff6f3baffdbb8ef7f693f3fed133ddff4d43bdfca4eefdaa4c7ff8c0aafd7f6cd27fedc48cffaa4c33ffd2b6ffb30a163fedd3fcdff4d4b3fdd04d8ffb752b7edd03b8ffb641a7fdd837cf7f28df3dfca3eaf7f6456bfbd8a88ffb73223ffd91d8ffb74cebdedaadcf7f68fa3ffd937af7b70573dfd21f8fff64463ffda91ef77487bfd4902daf7f69373dec2808fff6422bfad8bfcfdaa4f6f7cdb44cf7aa46b7cfca02cfdf451abdfda52ffa302535fdd4218fff6ac2bfad8a2cf7f48c2bdfdd2daf7b74b63ffda8d9ff36133fe4a9848fff6afabfbd8c5cff7412afddd82fcf7f491ab7fdb2e8ffb647efedd9abbbf76eae3fedd22cdff4cfffb4a939efd2a52f1fed4308ffb6afabdfdc15afef634abefd9aebd7f6cd33dfd22ed7f7509f7eca989ef6b02befedd9a1ff37284bfcdca14cf7f68debdfdd2fdfd240eafebd8bb9fbb67233ded115afef62d63fedaa3cf7f48dfbf49023dfb2400a3fedab0cefb4a7f7ddca09cf7f488f7f4a9098fff70367fcd92ccf7f288e7fcdc1eafef62f2fecda85debf4b063ffdc06cf7f28c27eed9ccdfb7600aff5d921ef77492e3fed94c8ffb72ea7fc5d2acf7f291e3fedd31dfab02eebdedd2fcf7f28eb7edd0418fff64423ffd9069ff3611f7f5d14bcf7f694b77cdb448ffb7042bfbd8cdcf7b0402fedda94dfb366b3fcdca058ffb708fff090c0af7f74d3bf4a91baf7f69163fed9309ff761233ded415aff760babfad8caabff6ee3dddca0adfb746873dfca1fcff760dfbddca4bcf7f2932bdfda95cf7f2922bfdd837ef77287ab5fdb34ff824253fa4a912 else 0xe91a02804083405180e012e00336e0880a00e201f01c225e1942194325ac96892040046207e088070c1100e101cc002014820407c0e081f4b79123038052040c0d00e101f031224602a040a09040a600142de0028341210185506a86d08e005943254404704085a700102ba00201a02840ec0d81201c401a13836480700ab1250500384ac011689f02404606c020c116891496d12203e06040a020900e080d041207800509041581f101c03604860ec16080b87c9608b0de13c0e00303304d224606026ddc9d8bc0040381810105e10461c0010680ac048c1d028046304606040f40e081e04168411040a592100e01a028608c0a00d1cb0081b0282015a1052c005584183b02e048606c2072040815e89102b0e89081f083404607c04901d041181b100e0a080839037a2704584280a080e0142e1e102924840500708135921000a07c960ff17822c3781c0070840cf000c140210370230016a111ba97a8b431031284a8083127c83103121b03106846849cc8367048366997226025950f83103110f86865286848342d24be4523ba3222b431221c3103103121b11790f90b883617)
def xul10 : Packing := (209,4,7,7,8,12,0,0x0,xud10)
def xuh10 (i : Nat) : Nat := 0x3039797480b404d6e6b0b74034088000126a5da0002c02d0864280002c4b91a800014e3c1a59cc0005013800888c000000141f00020170000000007b9853034000803141100030b663d2066e05a8b250d3d0797800008067861c1e41b60001c10f2144310000c3780a400000025a3e0b380f62d4000d0c08080003c597470000405641c70c9c33409350b0002124a05242757028350001c2a0000445e69bc184025c2610bac2b92c0425e0be12127ac000a03800054488e6707441b40480000000401d0e00000001c230003807b081c05000380a06b183660180000000a00c08c008242f45040080080824440002
def xud9 (i : Nat) : Nat := 0x1b2414bb4b44b0180b8407c2968100a0f000407ec005810100e0c040400501e4bbaa111111111111aa111111119911881111111138111111771111116649381111111111111111111111111127161111111111111111111100e6bfa6bec7bdbac5e6bfa6adf73552a2fab98093ff61529495ffc7cffb6552a1ff4952c6d6bfb6cdd6bdca93bed9c6c6dee9b6abe7ad5237e6bf9497f3b794a1c7bdb805e7ad523be7afa4a3b5bfc7b0d5bfb7c7b5bfc771dfd1811acdfbb7a5efa9523cff4953abd5bfb796ffc121c8c7bfa49f9dbfc7b3cfdbb3c0bebbc6c4cfbb94bdc7bdb825cdfbb7b6adfbc7bdff498564c5fda89acff1812aa5ffc791d7ad5285ded9b64eff81214a87bdcb2987becb8686fdcb59ff09524bc6bfb650c6bfb61f87becb8795bfc7b387f9cb61ebd18027c6bfa61f86fecb8d96bfc67d87bdcb07ef49524e
def xul9 : Packing := (58,5,7,8,6,8,0,0x0,xud9)
def xuh9 (i : Nat) : Nat := 0x18900180341e81b04817c2000000
def xud8 (i : Nat) : Nat := 0x602020000a3897f6fce16ff1dddf24a95df32552abfa17ae5f7925490
def xul8 : Packing := (6,6,7,6,3,3,0,0x0,xud8)

end PEqualNP.Outside.L_meta_670.ParentLarge
