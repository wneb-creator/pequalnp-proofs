import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_10393_aux
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
def W (a : Nat) : Sig := BitVec.ofNat 128 a
def full : Nat := 0xffffffffffffffffffffffffffffffff
def xN : Nat → Nat
  | 0 => 0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa
  | 1 => 0xcccccccccccccccccccccccccccccccc
  | 2 => 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0
  | 3 => 0xff00ff00ff00ff00ff00ff00ff00ff00
  | 4 => 0xffff0000ffff0000ffff0000ffff0000
  | 5 => 0xffffffff00000000ffffffff00000000
  | _ => 0xffffffffffffffff0000000000000000
def nb (o a b : Nat) : Nat :=
  bif Nat.beq o 0 then Nat.land a b else bif Nat.beq o 1 then Nat.lor a b else
    bif Nat.beq o 2 then Nat.xor a (Nat.land a b) else Nat.xor b (Nat.land a b)
theorem bit_W (r : Row) (a : Nat) : bit r (W a) = a.testBit r.val := by
  unfold bit W
  rw [BitVec.getLsbD_ofNat]
  simp [r.isLt]
theorem tb_land (a b i : Nat) : (Nat.land a b).testBit i = (a.testBit i && b.testBit i) := Nat.testBit_and ..
theorem tb_lor (a b i : Nat) : (Nat.lor a b).testBit i = (a.testBit i || b.testBit i) := Nat.testBit_or ..
theorem tb_xor (a b i : Nat) : (Nat.xor a b).testBit i = (a.testBit i ^^ b.testBit i) := Nat.testBit_xor ..
theorem nbeq {a b : Nat} (h : a ≠ b) : Nat.beq a b = false := by
  cases e : Nat.beq a b
  · rfl
  · exact absurd (Nat.eq_of_beq_eq_true e) h
theorem W_nb (o a b : Nat) : W (nb o a b) = bin o (W a) (W b) := by
  apply bit_ext
  intro r
  rw [bit_bin,bit_W,bit_W,bit_W]
  by_cases h0 : o = 0
  · subst h0
    exact tb_land a b _
  by_cases h1 : o = 1
  · subst h1
    exact tb_lor a b _
  by_cases h2 : o = 2
  · subst h2
    change (Nat.xor a (Nat.land a b)).testBit r.val = _
    rw [tb_xor,tb_land]
    cases a.testBit r.val <;> cases b.testBit r.val <;> rfl
  · unfold nb
    rw [nbeq h0,nbeq h1,nbeq h2,if_neg h0,if_neg h1,if_neg h2]
    change (Nat.xor b (Nat.land a b)).testBit r.val = _
    rw [tb_xor,tb_land]
    cases a.testBit r.val <;> cases b.testBit r.val <;> rfl
theorem bin_four (u : Bool) (o : Nat) (h : (u || Nat.blt o 2) = true) : ∃ e, allowed u e ∧ ∀ a b, bin o a b = bin e a b := by
  cases u
  · refine ⟨o,Or.inl ?_,fun _ _ => rfl⟩
    simpa only [Bool.false_or,Nat.blt_eq] using h
  · by_cases h : o < 4
    · exact ⟨o,Or.inr ⟨rfl,h⟩,fun _ _ => rfl⟩
    · refine ⟨3,Or.inr ⟨rfl,by omega⟩,fun a b => ?_⟩
      have h0 : o ≠ 0 := by omega
      have h1 : o ≠ 1 := by omega
      have h2 : o ≠ 2 := by omega
      simp [bin,h0,h1,h2]
theorem W_zero : W 0 = zero := rfl
theorem W_full : W full = one := by
  apply bit_ext
  intro r
  rw [bit_W,bit_one]
  revert r
  decide +kernel
theorem W_inj {a b : Nat} (ha : a < 2^128) (hb : b < 2^128) (h : W a = W b) : a = b := by
  have := congrArg BitVec.toNat h
  simpa only [W,BitVec.toNat_ofNat,Nat.mod_eq_of_lt ha,Nat.mod_eq_of_lt hb] using this
def rootsW (R : List Nat) : List Sig := R.map fun i => W (xN i)
def LowN (u : Bool) (R : List Nat) (T L : Nat) : Prop := Lower u (rootsW R) (W T) L
abbrev SliceD := Nat × Nat × List Nat
def SliceN (u : Bool) (R : List Nat) (T : Nat) (s : SliceD) : Prop :=
  Slice u (rootsW R) (W T) (W s.1) s.2.1 ∧ ∀ v ∈ s.2.2, v ∈ R
def baseOK (T : Nat) (R : List Nat) (E : List (Nat × Nat × Nat)) : Bool :=
  decide (T < 2^128) && !(T.testBit 0) && (E.map Prod.fst == R) && !R.isEmpty && decide (rootsW R).Nodup &&
  R.all (fun i => !((xN i).testBit 0)) &&
  E.all (fun e => decide (e.2.1 < 128) && decide (e.2.2 < 128) && (T.testBit e.2.1 != T.testBit e.2.2) &&
    R.all (fun i => i == e.1 || (xN i).testBit e.2.1 == (xN i).testBit e.2.2))
abbrev BaseP (T : Nat) (R : List Nat) : Prop :=
  T < 2^128 ∧ plainWord (W T) = true ∧ (rootsW R).Nodup ∧ (rootsW R).all plainWord = true ∧
  (∀ a ∈ rootsW R, Essential (W T) (rootsW R) a) ∧ proper (W T)
theorem BaseP.lt {T R} (h : BaseP T R) : T < 2^128 := h.1
theorem BaseP.plain {T R} (h : BaseP T R) : plainWord (W T) = true := h.2.1
theorem BaseP.nodup {T R} (h : BaseP T R) : (rootsW R).Nodup := h.2.2.1
theorem BaseP.plainR {T R} (h : BaseP T R) : (rootsW R).all plainWord = true := h.2.2.2.1
theorem BaseP.ess {T R} (h : BaseP T R) : ∀ a ∈ rootsW R, Essential (W T) (rootsW R) a := h.2.2.2.2.1
theorem BaseP.prop {T R} (h : BaseP T R) : proper (W T) := h.2.2.2.2.2
theorem baseOK_ok {T R E} (h : baseOK T R E = true) : BaseP T R := by
  simp only [baseOK,Bool.and_eq_true,decide_eq_true_eq,beq_iff_eq,Bool.not_eq_true',List.all_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨hT,h0⟩,hE⟩,hne⟩,nd⟩,pr⟩,he⟩ := h
  have ess : ∀ a ∈ rootsW R, Essential (W T) (rootsW R) a := by
    intro a ha
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp ha
    rw [←hE] at hi
    obtain ⟨e,hem,rfl⟩ := List.mem_map.mp hi
    obtain ⟨⟨⟨h1,h2⟩,h3⟩,h4⟩ := he e hem
    refine ⟨⟨e.2.1,h1⟩,⟨e.2.2,h2⟩,?_,?_⟩
    · rw [bit_W,bit_W]
      simpa using h3
    · intro v hv hne
      obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hv
      rw [bit_W,bit_W]
      have := h4 j hj
      simp only [Bool.or_eq_true,beq_iff_eq] at this
      rcases this with rfl | this
      · exact absurd rfl hne
      · exact this
  refine ⟨hT,?_,nd,?_,ess,?_⟩
  · have : bit 0 (W T) = false := (bit_W 0 T).trans h0
    simp [plainWord,this]
  · rw [List.all_eq_true]
    intro a ha
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp ha
    have : bit 0 (W (xN i)) = false := (bit_W 0 _).trans (by simpa using pr i hi)
    simp [plainWord,this]
  · cases R with
    | nil => simp at hne
    | cons i R =>
      obtain ⟨r,s,hd,_⟩ := ess (W (xN i)) (by simp [rootsW])
      constructor
      · intro hh
        rw [hh,bit_zero,bit_zero] at hd
        exact hd rfl
      · intro hh
        rw [hh,bit_one,bit_one] at hd
        exact hd rfl
theorem lowOf {u T R E K} (hB : baseOK T R E = true) (h : Impossible u (W T) K (rootsW R).toFinset) :
    LowN u R T (K+1) := by
  have b := baseOK_ok hB
  exact lower_impossible b.prop b.plain b.plainR b.ess h
theorem lowCount {u T R E K} (hB : baseOK T R E = true) (h : K + 2 ≤ R.length) : LowN u R T (K+1) := by
  apply lowOf hB
  intro k hk run
  have b := baseOK_ok hB
  have := live_size run
  rw [List.toFinset_card_of_nodup b.nodup,rootsW,List.length_map] at this
  omega
def rowOf : List Nat → Nat → Nat → Nat
  | [],w,_ => w
  | v::vs,w,r => rowOf vs (w + ((r % 2) <<< v)) (r / 2)
def sliceChk (R : List Nat) (T : Nat) (R' : List Nat) (G d : Nat) (vs : List Nat) (w : Nat) : Bool :=
  vs.all (fun v => R.contains v) &&
  (List.range 128).all (fun r => let q := rowOf vs w r
    Nat.blt q 128 && d.testBit q && (T.testBit q == G.testBit r)) &&
  R.all (fun i => (List.range 128).all (fun r => !((xN i).testBit (rowOf vs w r))) ||
    (List.range 128).all (fun r => (xN i).testBit (rowOf vs w r)) ||
    R'.any (fun j => (List.range 128).all (fun r => (xN i).testBit (rowOf vs w r) == (xN j).testBit r)))
theorem mkSlice {u R T E R' G E' d L vs w} (_hB : baseOK T R E = true) (hB' : baseOK G R' E' = true)
    (hL : LowN u R' G L) (h : sliceChk R T R' G d vs w = true) : SliceN u R T (d,L,vs) := by
  have b' := baseOK_ok hB'
  simp only [sliceChk,Bool.and_eq_true,List.all_eq_true,List.mem_range,Bool.or_eq_true,beq_iff_eq,
    Bool.not_eq_true',List.any_eq_true,Nat.blt_eq,List.contains_eq_mem,decide_eq_true_eq] at h
  obtain ⟨⟨hv,hr⟩,hR⟩ := h
  let f : Row → Row := fun r => ⟨rowOf vs w r.val,(hr r.val r.isLt).1.1⟩
  have fe (r : Row) (a : Nat) : bit (f r) (W a) = a.testBit (rowOf vs w r.val) := bit_W _ _
  have obs : restrictRows f (observe (W T)) = observe (W G) := by
    funext r
    change bit (f r) (W T) = bit r (W G)
    rw [fe,bit_W]
    exact (hr r.val r.isLt).2
  refine ⟨⟨f,rootsW R',?_,?_,?_,?_⟩,hv⟩
  · intro r
    rw [fe]
    exact (hr r.val r.isLt).1.2
  · intro a ha
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp ha
    rcases hR i hi with (h | h) | ⟨j,hj,h⟩
    · refine Or.inr (Or.inl ⟨false,funext fun r => ?_⟩)
      exact (fe r _).trans (h r.val r.isLt)
    · refine Or.inr (Or.inl ⟨true,funext fun r => ?_⟩)
      exact (fe r _).trans (h r.val r.isLt)
    · have e : restrictRows f (observe (W (xN i))) = observe (W (xN j)) := by
        funext r
        exact (fe r _).trans ((h r.val r.isLt).trans (bit_W r _).symm)
      rw [e]
      exact Or.inl (List.mem_map_of_mem (List.mem_map_of_mem hj))
  · rw [obs]
    exact observe_proper b'.prop
  · rw [obs]
    exact hL
def opOK (u : Bool) (o : Nat) : Bool := u || Nat.blt o 2
def av (u : Bool) (d : Nat) (P : List Nat) (v : Nat) : Bool :=
  let m := Nat.land v d
  Nat.beq m 0 || Nat.beq m d || P.any (fun x => Nat.beq x m || (u && Nat.beq x (Nat.xor d m)))
def cn (d v : Nat) : Nat :=
  let m := Nat.land v d
  bif Nat.beq m 0 || Nat.beq m d then 1 else 0
def sumc (d : Nat) : List Nat → Nat
  | [] => 0
  | v::l => Nat.add (cn d v) (sumc d l)
def mkPool (u : Bool) (P : List Nat) : List (Nat × Nat × Nat) → List Nat
  | [] => P
  | c::cs => mkPool u (bif opOK u c.1 then P ++ [nb c.1 (P.getD c.2.1 0) (P.getD c.2.2 0)] else P) cs
def initPool (d : Nat) (vs : List Nat) : List Nat := vs.map fun v => Nat.land (xN v) d
abbrev RF (f : Row → Row) (v : Nat) : Wire Row := restrictRows f (observe (W v))
def PS (u : Bool) (f : Row → Row) (bank : List (Wire Row)) (P : List Nat) : Prop :=
  ∀ v ∈ P, Available u bank (RF f v)
theorem rf_apply (f : Row → Row) (v : Nat) (r : Row) : RF f v r = v.testBit (f r).val := bit_W _ _
theorem rf_land {f : Row → Row} {d : Nat} (dom : ∀ r, bit (f r) (W d) = true) (v : Nat) :
    RF f (Nat.land v d) = RF f v := by
  funext r
  have h := dom r
  rw [bit_W] at h
  rw [rf_apply,rf_apply]
  have : (Nat.land v d).testBit (f r).val = (v.testBit (f r).val && d.testBit (f r).val) := Nat.testBit_and ..
  rw [this,h,Bool.and_true]
theorem rf_zero {f : Row → Row} : RF f 0 = fun _ => false := by
  funext r
  rw [rf_apply]
  exact Nat.zero_testBit _
theorem rf_dom {f : Row → Row} {d : Nat} (dom : ∀ r, bit (f r) (W d) = true) : RF f d = fun _ => true := by
  funext r
  exact dom r
theorem rf_xor {f : Row → Row} {d : Nat} (dom : ∀ r, bit (f r) (W d) = true) (m : Nat) :
    RF f (Nat.xor d m) = inv (RF f m) := by
  funext r
  have h := dom r
  rw [bit_W] at h
  change RF f (Nat.xor d m) r = !(RF f m r)
  rw [rf_apply,rf_apply]
  have : (Nat.xor d m).testBit (f r).val = ((d.testBit (f r).val) ^^ (m.testBit (f r).val)) := Nat.testBit_xor ..
  rw [this,h,Bool.true_xor]
theorem cn_ok {f : Row → Row} {d : Nat} (dom : ∀ r, bit (f r) (W d) = true) (v : Nat) : cn d v ≤ cost (RF f v) := by
  change (bif (Nat.beq (Nat.land v d) 0 || Nat.beq (Nat.land v d) d) then 1 else 0) ≤ _
  cases h : (Nat.beq (Nat.land v d) 0 || Nat.beq (Nat.land v d) d)
  · exact Nat.zero_le _
  · have c : Constant (RF f v) := by
      rw [←rf_land dom v]
      rw [Bool.or_eq_true] at h
      rcases h with h | h
      · rw [Nat.eq_of_beq_eq_true h,rf_zero]
        exact ⟨false,rfl⟩
      · rw [Nat.eq_of_beq_eq_true h,rf_dom dom]
        exact ⟨true,rfl⟩
    rw [cost,if_pos c]
    exact Nat.le_refl 1
theorem av_ok {u} {f : Row → Row} {d : Nat} (dom : ∀ r, bit (f r) (W d) = true) {bank P v} (hP : PS u f bank P)
    (h : av u d P v = true) : Available u bank (RF f v) := by
  simp only [av,Bool.or_eq_true,List.any_eq_true,Bool.and_eq_true] at h
  rw [←rf_land dom v]
  rcases h with (h | h) | ⟨x,hx,h | ⟨hu,h⟩⟩
  · rw [Nat.eq_of_beq_eq_true h,rf_zero]
    exact Or.inr (Or.inl ⟨false,rfl⟩)
  · rw [Nat.eq_of_beq_eq_true h,rf_dom dom]
    exact Or.inr (Or.inl ⟨true,rfl⟩)
  · rw [←Nat.eq_of_beq_eq_true h]
    exact hP x hx
  · have e := hP x hx
    rw [Nat.eq_of_beq_eq_true h,rf_xor dom] at e
    have e' := avail_inv hu e
    rwa [inv_inv'] at e'
theorem rf_nb (f : Row → Row) (o a b : Nat) : RF f (nb o a b) = comb o (RF f a) (RF f b) := by
  unfold RF
  rw [W_nb,obs_bin,restrict_comb]
theorem pay_nb {u} {f : Row → Row} {roots bank p P} (o a b : Nat) (ho : opOK u o = true) (hr : Reach u roots p bank) (hP : PS u f bank P)
    (ha : Available u bank (RF f a)) (hb : Available u bank (RF f b)) :
    ∃ next, Reach u roots (p+1) next ∧ PS u f next P ∧ Available u next (RF f (nb o a b)) ∧
      ∀ v, Available u bank v → Available u next v := by
  obtain ⟨e,he,heq⟩ := bin_four u o ho
  have hn : RF f (nb o a b) = comb e (RF f a) (RF f b) := by
    unfold RF
    rw [W_nb,heq,obs_bin,restrict_comb]
  obtain ⟨op,x,y,e1,hx,hy,_,_⟩ := comb_prime (d:=e) he ha hb
  refine ⟨_,Reach.two op hr hx hy,fun v hv => available_cons _ (hP v hv),?_,fun v hv => available_cons _ hv⟩
  rw [hn,e1]
  exact Or.inl (by simp)
theorem getD_ps {u} {f : Row → Row} {bank P} (hP : PS u f bank P) (i : Nat) : Available u bank (RF f (P.getD i 0)) := by
  rw [List.getD_eq_getElem?_getD]
  cases h : P[i]? with
  | none => exact Or.inr (Or.inl ⟨false,rf_zero⟩)
  | some a => exact hP a (List.mem_of_getElem? h)
theorem mkPool_ok {u} {f : Row → Row} {roots} (cs : List (Nat × Nat × Nat)) {bank p P} (hr : Reach u roots p bank)
    (hP : PS u f bank P) : ∃ next, Reach u roots (p+cs.length) next ∧ PS u f next (mkPool u P cs) := by
  induction cs generalizing bank p P with
  | nil => exact ⟨bank,hr,hP⟩
  | cons c cs ih =>
    have big : ∃ next, Reach u roots (p+1) next ∧ PS u f next (bif opOK u c.1 then P ++ [nb c.1 (P.getD c.2.1 0) (P.getD c.2.2 0)] else P) := by
      cases ho : opOK u c.1
      · refine ⟨_,Reach.two false hr (Or.inr (Or.inl ⟨false,rfl⟩)) (Or.inr (Or.inl ⟨false,rfl⟩)),fun v hv => available_cons _ (hP v hv)⟩
      · obtain ⟨next,h1,h2,h3,_⟩ := pay_nb c.1 _ _ ho hr hP (getD_ps hP c.2.1) (getD_ps hP c.2.2)
        refine ⟨next,h1,?_⟩
        intro v hv
        rw [cond_true] at hv
        rcases List.mem_append.mp hv with hv | hv
        · exact h2 v hv
        · rw [List.mem_singleton.mp hv]
          exact h3
    obtain ⟨next,h1,this⟩ := big
    obtain ⟨out,o1,o2⟩ := ih h1 this
    exact ⟨out,by rw [List.length_cons,show p+(cs.length+1) = p+1+cs.length by omega]; exact o1,o2⟩
abbrev CutV := Nat × Nat × Nat × List Nat
def keepB (u : Bool) (d : Nat) (P : List Nat) (ka : Bool) (a : Nat) : Bool := bif ka then av u d P a else true
def keepC (d : Nat) (ka : Bool) (a : Nat) : Nat := bif ka then cn d a else 0
def cutEval (u : Bool) (k : Nat) (rest : List Nat) (a b z : Nat) (ka kb : Bool) (c : CutV) : Bool :=
  rest.all (av u c.1 c.2.2.2) && keepB u c.1 c.2.2.2 ka a && keepB u c.1 c.2.2.2 kb b &&
  (bif av u c.1 c.2.2.2 z then
    Nat.blt (Nat.add k c.2.2.1) (Nat.add c.2.1 (Nat.add (Nat.add (sumc c.1 rest) (cn c.1 z)) (Nat.add (keepC c.1 ka a) (keepC c.1 kb b))))
  else av u c.1 c.2.2.2 a && av u c.1 c.2.2.2 b &&
    Nat.blt (Nat.add (Nat.add k c.2.2.1) 1) (Nat.add c.2.1 (Nat.add (Nat.add (sumc c.1 rest) (cn c.1 z)) (Nat.add (keepC c.1 ka a) (keepC c.1 kb b)))))
def same (u : Bool) (p : Nat × Nat) (v : Nat) : Bool :=
  bif u then Nat.testBit v p.1 == Nat.testBit v p.2 else !(Nat.testBit v p.1) || Nat.testBit v p.2
def sepEval (u : Bool) (rest : List Nat) (a b z : Nat) (ka kb : Bool) (p : Nat × Nat) : Bool :=
  same u p z && (!ka || same u p a) && (!kb || same u p b) && rest.all (same u p)
def sepOK (T : Nat) (p : Nat × Nat) : Bool := Nat.blt p.1 128 && Nat.blt p.2 128 && T.testBit p.1 && !(T.testBit p.2)
def kidW (rest : List Nat) (a b z : Nat) (ka kb : Bool) : List Sig :=
  W z :: kept ka (W a) (kept kb (W b) (rest.map W))
theorem sumc_ok {f : Row → Row} {d : Nat} (dom : ∀ r, bit (f r) (W d) = true) (l : List Nat) :
    sumc d l ≤ mass (l.map (RF f)) := by
  induction l with
  | nil => simp [sumc]
  | cons v l ih =>
    rw [List.map_cons,mass_cons]
    exact Nat.add_le_add (cn_ok dom v) ih
theorem mass_keep {f : Row → Row} {d : Nat} (dom : ∀ r, bit (f r) (W d) = true) (ka : Bool) (a : Nat) (l : List (Wire Row)) :
    keepC d ka a + mass l ≤ mass (kept ka (RF f a) l) := by
  cases ka
  · simp [keepC,kept]
  · rw [kept,if_pos rfl,mass_cons]
    exact Nat.add_le_add_right (cn_ok dom a) _
theorem kid_map (f : Row → Row) (rest : List Nat) (a b z : Nat) (ka kb : Bool) :
    ((kidW rest a b z ka kb).map observe).map (restrictRows f) =
      RF f z :: kept ka (RF f a) (kept kb (RF f b) (rest.map (RF f))) := by
  cases ka <;> cases kb <;> simp [kidW,kept,List.map_map,Function.comp_def,RF]
def CutP (u : Bool) (_R : List Nat) (T : Nat) (c : CutV) : Prop :=
  ∃ (f : Row → Row) (roots : List Sig) (bank : List (Wire Row)), (∀ r, bit (f r) (W c.1) = true) ∧
    ¬Constant (restrictRows f (observe (W T))) ∧ Reach u (roots.map observe) c.2.2.1 bank ∧ PS u f bank c.2.2.2 ∧
    ∀ p bank, Reach u (roots.map observe) p bank → Available u bank (restrictRows f (observe (W T))) → c.2.1 ≤ p
theorem cut_sound {u R T c k rest a b o ka kb} (hc : CutP u R T c) (ho : opOK u o = true)
    (nd : (kidW rest a b (nb o a b) ka kb).Nodup)
    (h : cutEval u k rest a b (nb o a b) ka kb c = true) :
    Impossible u (W T) k (kidW rest a b (nb o a b) ka kb).toFinset := by
  obtain ⟨f,roots,bank,dom,nc,hr,hP,lo⟩ := hc
  simp only [cutEval,Bool.and_eq_true,List.all_eq_true] at h
  obtain ⟨⟨⟨h1,h2⟩,h3⟩,h4⟩ := h
  have key : ∃ q bank', Reach u (roots.map observe) q bank' ∧ PS u f bank' c.2.2.2 ∧ Available u bank' (RF f (nb o a b)) ∧
      k + q < c.2.1 + ((sumc c.1 rest + cn c.1 (nb o a b)) + (keepC c.1 ka a + keepC c.1 kb b)) := by
    cases hz : av u c.1 c.2.2.2 (nb o a b)
    · rw [hz,cond_false,Bool.and_eq_true,Bool.and_eq_true,Nat.blt_eq] at h4
      obtain ⟨next,n1,n2,n3,_⟩ := pay_nb o a b ho hr hP (av_ok dom hP h4.1.1) (av_ok dom hP h4.1.2)
      refine ⟨_,next,n1,n2,n3,?_⟩
      have := h4.2
      exact this
    · rw [hz,cond_true,Nat.blt_eq] at h4
      exact ⟨_,bank,hr,hP,av_ok dom hP hz,h4⟩
  obtain ⟨q,bank',r1,r2,r3,r4⟩ := key
  intro k' hk run
  have supp : supply u bank' (((kidW rest a b (nb o a b) ka kb).map observe).map (restrictRows f)) := by
    rw [kid_map]
    intro v hv
    rcases List.mem_cons.mp hv with rfl | hv
    · exact r3
    have kb' : ∀ v ∈ kept kb (RF f b) (rest.map (RF f)), Available u bank' v := by
      intro v hv
      cases kb
      · obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hv
        exact av_ok dom r2 (h1 x hx)
      · rcases List.mem_cons.mp hv with rfl | hv
        · exact av_ok dom r2 h3
        · obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hv
          exact av_ok dom r2 (h1 x hx)
    cases ka
    · exact kb' v hv
    · rcases List.mem_cons.mp hv with rfl | hv
      · exact av_ok dom r2 h2
      · exact kb' v hv
  have bound := projected_bound f (list_run run _ nd rfl) nc r1 supp lo
  rw [kid_map,mass_cons] at bound
  have m1 := mass_keep dom ka a (kept kb (RF f b) (rest.map (RF f)))
  have m2 := mass_keep dom kb b (rest.map (RF f))
  have m3 := sumc_ok dom rest
  have m4 := cn_ok dom (nb o a b)
  omega
theorem kid_mem {rest : List Nat} {a b z : Nat} {ka kb : Bool} {v : Sig} (hv : v ∈ kidW rest a b z ka kb) :
    ∃ x, v = W x ∧ (x = z ∨ (ka = true ∧ x = a) ∨ (kb = true ∧ x = b) ∨ x ∈ rest) := by
  rcases List.mem_cons.mp hv with rfl | hv
  · exact ⟨z,rfl,Or.inl rfl⟩
  have low : ∀ v ∈ kept kb (W b) (rest.map W), ∃ x, v = W x ∧ ((kb = true ∧ x = b) ∨ x ∈ rest) := by
    intro v hv
    cases kb
    · obtain ⟨x,hx,e⟩ := List.mem_map.mp hv
      exact ⟨x,e.symm,Or.inr hx⟩
    · rcases List.mem_cons.mp hv with e | hv
      · exact ⟨b,e,Or.inl ⟨rfl,rfl⟩⟩
      · obtain ⟨x,hx,e⟩ := List.mem_map.mp hv
        exact ⟨x,e.symm,Or.inr hx⟩
  cases ka
  · obtain ⟨x,h1,h2⟩ := low v hv
    exact ⟨x,h1,Or.inr (Or.inr h2)⟩
  · rcases List.mem_cons.mp hv with e | hv
    · exact ⟨a,e,Or.inr (Or.inl ⟨rfl,rfl⟩)⟩
    · obtain ⟨x,h1,h2⟩ := low v hv
      exact ⟨x,h1,Or.inr (Or.inr h2)⟩
theorem sep_sound {u T k rest a b o ka kb p} (hT : sepOK T p = true)
    (h : sepEval u rest a b (nb o a b) ka kb p = true) :
    Impossible u (W T) k (kidW rest a b (nb o a b) ka kb).toFinset := by
  simp only [sepOK,Bool.and_eq_true,Nat.blt_eq,Bool.not_eq_true'] at hT
  obtain ⟨⟨⟨p1,p2⟩,t1⟩,t2⟩ := hT
  simp only [sepEval,Bool.and_eq_true,Bool.or_eq_true,Bool.not_eq_true',List.all_eq_true] at h
  obtain ⟨⟨⟨h1,h2⟩,h3⟩,h4⟩ := h
  have all : ∀ v ∈ kidW rest a b (nb o a b) ka kb, ∃ x, v = W x ∧ same u p x = true := by
    intro v hv
    obtain ⟨x,rfl,hx⟩ := kid_mem hv
    refine ⟨x,rfl,?_⟩
    rcases hx with rfl | ⟨q,rfl⟩ | ⟨q,rfl⟩ | hx
    · exact h1
    · subst q; exact h2.resolve_left (by simp)
    · subst q; exact h3.resolve_left (by simp)
    · exact h4 x hx
  intro k' _ run
  cases u
  · obtain ⟨v,hv,hp,hn⟩ := mono_row_difference run rfl (r:=⟨p.1,p1⟩) (s:=⟨p.2,p2⟩) (by rw [bit_W]; exact t1) (by rw [bit_W]; exact t2)
    obtain ⟨x,rfl,hx⟩ := all v (List.mem_toFinset.mp hv)
    rw [bit_W] at hp hn
    simp only [same,cond_false,Bool.or_eq_true,Bool.not_eq_true'] at hx
    rcases hx with hx | hx
    · rw [hx] at hp; exact Bool.noConfusion hp
    · rw [hx] at hn; exact Bool.noConfusion hn
  · obtain ⟨v,hv,hne⟩ := live_row_difference run (r:=⟨p.1,p1⟩) (s:=⟨p.2,p2⟩) (by rw [bit_W,bit_W,t1,t2]; simp)
    obtain ⟨x,rfl,hx⟩ := all v (List.mem_toFinset.mp hv)
    apply hne
    rw [bit_W,bit_W]
    simpa only [same,cond_true,beq_iff_eq] using hx
def KWOwn (S : Finset Sig) (T : Sig) (owns : Sig → Row → Row → Prop) : Prop :=
  (∀ p n, bit p T = true → bit n T = false → ∃ v, owns v p n) ∧
  (∀ v p n, owns v p n → v ∈ S ∧ bit p v = true ∧ bit n v = false) ∧
  (∀ v w p n, owns v p n → owns w p n → v = w) ∧
  (∀ v p n p' n', owns v p n → owns v p' n' → owns v p n')
abbrev KWRooms (S : Finset Sig) (T : Sig) := {o : Sig → Row → Row → Prop // KWOwn S T o}
def KWRooms.owns {S T} (H : KWRooms S T) : Sig → Row → Row → Prop := H.1
theorem KWRooms.total {S T} (H : KWRooms S T) : ∀ p n, bit p T = true → bit n T = false → ∃ v, H.owns v p n := H.2.1
theorem KWRooms.valid {S T} (H : KWRooms S T) {v p n} : H.owns v p n → v ∈ S ∧ bit p v = true ∧ bit n v = false := H.2.2.1 v p n
theorem KWRooms.unique {S T} (H : KWRooms S T) {v w p n} : H.owns v p n → H.owns w p n → v = w := H.2.2.2.1 v w p n
theorem KWRooms.rect {S T} (H : KWRooms S T) {v p n p' n'} : H.owns v p n → H.owns v p' n' → H.owns v p n' := H.2.2.2.2 v p n p' n'
theorem kwLeaf (T : Sig) : Nonempty (KWRooms {T} T) := by
  refine ⟨⟨fun v p n => v = T ∧ bit p T = true ∧ bit n T = false,?_,?_,?_,?_⟩⟩
  · intro p n hp hn
    exact ⟨T,rfl,hp,hn⟩
  · rintro v p n ⟨rfl,hp,hn⟩
    exact ⟨by simp,hp,hn⟩
  · rintro v w p n ⟨rfl,_⟩ ⟨rfl,_⟩
    rfl
  · rintro v p n p' n' ⟨rfl,hp,_⟩ ⟨_,_,hn⟩
    exact ⟨rfl,hp,hn⟩
theorem kwFork {T : Sig} {U : Finset Sig} {a b : Sig} {d : Nat} (d01 : d=0 ∨ d=1) (hab : a ≠ b) (ha : a ∉ U) (hb : b ∉ U)
    (hz : bin d a b ∉ U) (H : KWRooms (insert (bin d a b) U) T) : Nonempty (KWRooms (insert a (insert b U)) T) := by
  classical
  let z := bin d a b
  let own : Sig → Row → Row → Prop := fun v p n => (v ∈ U ∧ H.owns v p n) ∨
    (H.owns z p n ∧ v = (if d=0 then (if bit n a = false then a else b) else (if bit p a = true then a else b)))
  have pickU : ∀ (p n : Row), (if d=0 then (if bit n a = false then a else b) else (if bit p a = true then a else b)) ∉ U := by
    intro p n
    split <;> split <;> assumption
  refine ⟨⟨own,?_,?_,?_,?_⟩⟩
  · intro p n hp hn
    obtain ⟨v,hv⟩ := H.total p n hp hn
    rcases Finset.mem_insert.mp (H.valid hv).1 with e | hm
    · refine ⟨_,Or.inr ⟨?_,rfl⟩⟩
      rw [show v = z from e] at hv
      exact hv
    · exact ⟨v,Or.inl ⟨hm,hv⟩⟩
  · intro v p n h
    rcases h with ⟨hm,hv⟩ | ⟨hv,rfl⟩
    · exact ⟨Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hm),(H.valid hv).2⟩
    · obtain ⟨_,hp,hn⟩ := H.valid hv
      change bit p (bin d a b) = true at hp
      change bit n (bin d a b) = false at hn
      rw [bit_bin] at hp hn
      rcases d01 with rfl | rfl
      · cases pa : bit p a <;> cases na : bit n a <;> cases pb : bit p b <;> cases nb' : bit n b <;> simp_all
      · cases pa : bit p a <;> cases na : bit n a <;> cases pb : bit p b <;> cases nb' : bit n b <;> simp_all
  · intro v w p n h1 h2
    rcases h1 with ⟨vU,hv⟩ | ⟨hv,rfl⟩ <;> rcases h2 with ⟨wU,hw⟩ | ⟨hw,rfl⟩
    · exact H.unique hv hw
    · exact absurd (show z ∈ U by rw [←H.unique hv hw]; exact vU) hz
    · exact absurd (show z ∈ U by rw [←H.unique hw hv]; exact wU) hz
    · rfl
  · intro v p n p' n' h1 h2
    rcases h1 with ⟨vU,hv⟩ | ⟨hv,e1⟩ <;> rcases h2 with ⟨wU,hw⟩ | ⟨hw,e2⟩
    · exact Or.inl ⟨vU,H.rect hv hw⟩
    · exact absurd (e2 ▸ vU) (pickU p' n')
    · exact absurd (e1 ▸ wU) (pickU p n)
    · refine Or.inr ⟨H.rect hv hw,?_⟩
      by_cases h : d=0
      · rw [if_pos h] at e2 ⊢
        exact e2
      · rw [if_neg h] at e1 ⊢
        exact e1
theorem kwTight {T : Sig} {k : Nat} {S : Finset Sig} (run : Live false T k S) (tight : S.card=k+1) :
    Nonempty (KWRooms S T) := by
  induction k generalizing S with
  | zero =>
    obtain ⟨rfl,_⟩ := run
    exact kwLeaf T
  | succ k ih =>
    obtain ⟨U,a,b,d,hd,rfl,_,_,hab,hfresh,tail⟩ := run
    have fresh : bin d a b ∉ U := fun h => hfresh (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem h))
    have li := live_size tail
    rw [Finset.card_insert_of_notMem fresh] at li
    have le1 := Finset.card_insert_le a (insert b U)
    have le2 := Finset.card_insert_le b U
    have ha : a ∉ U := by
      intro h
      rw [Finset.insert_eq_of_mem (Finset.mem_insert_of_mem h : a ∈ insert b U)] at tight
      omega
    have hb : b ∉ U := by
      intro h
      rw [Finset.insert_eq_of_mem h] at tight le1
      omega
    have eq : (insert (bin d a b) U).card=k+1 := by
      rw [Finset.card_insert_of_notMem fresh]
      omega
    obtain ⟨H⟩ := ih tail eq
    have d01 : d=0 ∨ d=1 := by
      rcases hd with h | ⟨h,_⟩
      · omega
      · exact Bool.noConfusion h
    exact kwFork d01 hab ha hb fresh H
def only (l : List Nat) (p n a : Nat) : Bool :=
  Nat.blt p 128 && Nat.blt n 128 && l.all (fun x => !(Nat.testBit x p) || Nat.testBit x n || Nat.beq x a)
abbrev KwD := Nat × Nat × Nat × Nat × Nat × Nat
def findW (l : List Nat) (p n : Nat) : Nat := (l.find? (fun x => Nat.testBit x p && !(Nat.testBit x n))).getD 0
def kwOK (T : Nat) (q : KwD) : Bool :=
  T.testBit q.1 && T.testBit q.2.2.2.1 && T.testBit q.2.2.2.2.2 && !(T.testBit q.2.1) && !(T.testBit q.2.2.1) && !(T.testBit q.2.2.2.2.1)
def kwList (l : List Nat) (q : KwD) : Bool :=
  let a := findW l q.1 q.2.2.1
  let b := findW l q.1 q.2.2.2.2.1
  only l q.1 q.2.2.1 a && only l q.2.2.2.1 q.2.1 a &&
  (bif Nat.beq q.1 q.2.2.2.2.2 && Nat.beq q.2.1 q.2.2.2.2.1 then !(Nat.testBit a q.1 && !(Nat.testBit a q.2.1))
   else only l q.1 q.2.2.2.2.1 b && only l q.2.2.2.2.2 q.2.1 b && !(Nat.beq a b))
theorem only_own {l : List Nat} {T p n a : Nat} (H : KWRooms ((l.map W).toFinset) (W T))
    (h : only l p n a = true) (tp : T.testBit p = true) (tn : T.testBit n = false) :
    ∃ (hp : p < 128) (hn : n < 128), H.owns (W a) ⟨p,hp⟩ ⟨n,hn⟩ := by
  simp only [only,Bool.and_eq_true,Nat.blt_eq,List.all_eq_true,Bool.or_eq_true,Bool.not_eq_true'] at h
  obtain ⟨⟨hp,hn⟩,hl⟩ := h
  refine ⟨hp,hn,?_⟩
  obtain ⟨v,hv⟩ := H.total ⟨p,hp⟩ ⟨n,hn⟩ (by rw [bit_W]; exact tp) (by rw [bit_W]; exact tn)
  obtain ⟨hm,h1,h2⟩ := H.valid hv
  obtain ⟨x,hx,rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hm)
  rw [bit_W] at h1 h2
  rcases hl x hx with (h | h) | h
  · rw [h] at h1; exact Bool.noConfusion h1
  · rw [h] at h2; exact Bool.noConfusion h2
  · rw [Nat.eq_of_beq_eq_true h] at hv
    exact hv
theorem kw_sound {T k : Nat} {l : List Nat} (nd : (l.map W).Nodup) (size : l.length = k+1) (lt : ∀ x ∈ l, x < 2^128) (q : KwD)
    (hT : kwOK T q = true) (h : kwList l q = true) : Impossible false (W T) k (l.map W).toFinset := by
  intro k' hk run
  have lb := live_size run
  rw [List.toFinset_card_of_nodup nd,List.length_map] at lb
  obtain ⟨H⟩ := kwTight run (by rw [List.toFinset_card_of_nodup nd,List.length_map]; omega)
  simp only [kwOK,Bool.and_eq_true,Bool.not_eq_true'] at hT
  obtain ⟨⟨⟨⟨⟨t1,t2⟩,t3⟩,t4⟩,t5⟩,t6⟩ := hT
  simp only [kwList,Bool.and_eq_true] at h
  obtain ⟨⟨h1,h2⟩,h3⟩ := h
  obtain ⟨hp,hna,o1⟩ := only_own H h1 t1 t5
  obtain ⟨hpa,hn,o2⟩ := only_own H h2 t2 t4
  have own := H.rect o1 o2
  cases hc : (Nat.beq q.1 q.2.2.2.2.2 && Nat.beq q.2.1 q.2.2.2.2.1)
  · rw [hc,cond_false] at h3
    simp only [Bool.and_eq_true,Bool.not_eq_true'] at h3
    obtain ⟨⟨h4,h5⟩,h6⟩ := h3
    obtain ⟨_,hnb,o3⟩ := only_own H h4 t1 t6
    obtain ⟨hpb,_,o4⟩ := only_own H h5 t3 t4
    have own' := H.rect o3 o4
    have ee := H.unique own own'
    have mem : ∀ {a : Nat}, W a ∈ (l.map W).toFinset → ∃ x ∈ l, W x = W a := by
      intro a ha
      obtain ⟨x,hx,e⟩ := List.mem_map.mp (List.mem_toFinset.mp ha)
      exact ⟨x,hx,e⟩
    have fw : ∀ p n, findW l p n < 2^128 := by
      intro p n
      unfold findW
      cases hf : l.find? (fun x => Nat.testBit x p && !(Nat.testBit x n)) with
      | none => exact Nat.two_pow_pos 128
      | some x => exact lt x (List.mem_of_find?_eq_some hf)
    have := W_inj (fw _ _) (fw _ _) ee
    rw [this,Nat.beq_refl] at h6
    exact Bool.noConfusion h6
  · rw [hc,cond_true] at h3
    have v := (H.valid own).2
    rw [bit_W,bit_W] at v
    rw [v.1,v.2] at h3
    exact Bool.noConfusion h3
def hiM : Nat → Nat
  | 0 => 0x22222222222222222222222222222222
  | 1 => 0x0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c
  | 2 => 0x00f000f000f000f000f000f000f000f0
  | 3 => 0x0000ff000000ff000000ff000000ff00
  | _ => 0x00000000ffff000000000000ffff0000
def loM : Nat → Nat
  | 0 => 0x44444444444444444444444444444444
  | 1 => 0x30303030303030303030303030303030
  | 2 => 0x0f000f000f000f000f000f000f000f00
  | 3 => 0x00ff000000ff000000ff000000ff0000
  | _ => 0x0000ffff000000000000ffff00000000
def keM : Nat → Nat
  | 0 => 0x99999999999999999999999999999999
  | 1 => 0xc3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3
  | 2 => 0xf00ff00ff00ff00ff00ff00ff00ff00f
  | 3 => 0xff0000ffff0000ffff0000ffff0000ff
  | _ => 0xffff00000000ffffffff00000000ffff
def shM : Nat → Nat
  | 0 => 1
  | 1 => 2
  | 2 => 4
  | 3 => 8
  | _ => 16
def swapN (i v : Nat) : Nat :=
  Nat.lor (Nat.lor (Nat.land v (keM i)) (Nat.shiftLeft (Nat.land v (hiM i)) (shM i))) (Nat.shiftRight (Nat.land v (loM i)) (shM i))
def sig (i : Nat) (r : Row) : Row :=
  if (hiM i).testBit r.val then Fin.ofNat 128 (r.val + shM i) else
    if (loM i).testBit r.val then Fin.ofNat 128 (r.val - shM i) else r
def swapFacts (i : Nat) (r : Row) : Prop :=
  ((keM i).testBit r.val = true ∧ (sig i r).val = r.val ∧ (decide (shM i ≤ r.val) && (hiM i).testBit (r.val - shM i)) = false ∧ (loM i).testBit (shM i + r.val) = false) ∨
  ((keM i).testBit r.val = false ∧ shM i ≤ r.val ∧ (sig i r).val = r.val - shM i ∧ (hiM i).testBit (r.val - shM i) = true ∧ (loM i).testBit (shM i + r.val) = false) ∨
  ((keM i).testBit r.val = false ∧ (sig i r).val = shM i + r.val ∧ (decide (shM i ≤ r.val) && (hiM i).testBit (r.val - shM i)) = false ∧ (loM i).testBit (shM i + r.val) = true)
theorem swap_facts : ∀ (i : Fin 5) (r : Row), swapFacts i.val r ∧ sig i.val (sig i.val r) = r := by
  unfold swapFacts
  decide +kernel
theorem swap_ok (i : Nat) (hi : i < 5) (v : Nat) : W (swapN i v) = rename (sig i) (W v) := by
  apply bit_ext
  intro r
  rw [bit_W,bit_rename,bit_W]
  have e : (swapN i v).testBit r.val = (((v.testBit r.val && (keM i).testBit r.val) ||
      (decide (shM i ≤ r.val) && (v.testBit (r.val - shM i) && (hiM i).testBit (r.val - shM i)))) ||
      (v.testBit (shM i + r.val) && (loM i).testBit (shM i + r.val))) := by
    have s1 : (Nat.shiftLeft (Nat.land v (hiM i)) (shM i)).testBit r.val = (decide (shM i ≤ r.val) && (Nat.land v (hiM i)).testBit (r.val - shM i)) := by
      exact Nat.testBit_shiftLeft ..
    have s2 : (Nat.shiftRight (Nat.land v (loM i)) (shM i)).testBit r.val = (Nat.land v (loM i)).testBit (shM i + r.val) := by
      exact Nat.testBit_shiftRight ..
    unfold swapN
    rw [tb_lor,tb_lor,s1,s2,tb_land,tb_land,tb_land]
  rw [e]
  rcases (swap_facts ⟨i,hi⟩ r).1 with ⟨h1,h2,h3,h4⟩ | ⟨h1,h2,h3,h4,h5⟩ | ⟨h1,h2,h3,h4⟩
  · change (sig i r).val = r.val at h2
    rw [h2]
    simp only [] at h1 h3 h4
    rw [h1,h4]
    cases hd : decide (shM i ≤ r.val)
    · simp
    · rw [hd,Bool.true_and] at h3
      rw [h3]; simp
  · change (sig i r).val = r.val - shM i at h3
    rw [h3]
    simp only [] at h1 h2 h4 h5
    rw [h1,h4,h5,decide_eq_true h2]
    simp
  · change (sig i r).val = shM i + r.val at h2
    rw [h2]
    simp only [] at h1 h3 h4
    rw [h1,h4]
    cases hd : decide (shM i ≤ r.val)
    · simp
    · rw [hd,Bool.true_and] at h3
      rw [h3]; simp
def permN (l : List Nat) (v : Nat) : Nat := l.foldl (fun v i => swapN i v) v
def symOK (T : Nat) (l : List Nat) : Bool := l.all fun i => Nat.blt i 5 && Nat.beq (swapN i T) T
theorem perm_sound {u T k} (l : List Nat) (hT : symOK T l = true) (s : List Nat)
    (h : Impossible u (W T) k ((s.map (permN l)).map W).toFinset) : Impossible u (W T) k (s.map W).toFinset := by
  induction l generalizing s with
  | nil =>
    simpa [show (permN [] : Nat → Nat) = id from rfl] using h
  | cons i l ih =>
    simp only [symOK,List.all_cons,Bool.and_eq_true,Nat.blt_eq] at hT
    obtain ⟨⟨hi,hs⟩,hl⟩ := hT
    have h' : Impossible u (W T) k ((s.map (swapN i)).map W).toFinset := by
      apply ih hl
      have : (s.map (swapN i)).map (permN l) = s.map (permN (i::l)) := by
        rw [List.map_map]
        rfl
      rw [this]
      exact h
    intro k' hk run
    have onto : Function.Surjective (sig i) := fun r => ⟨sig i r,(swap_facts ⟨i,hi⟩ r).2⟩
    have r2 := live_rename run (sig i) onto
    rw [←swap_ok i hi T,Nat.eq_of_beq_eq_true hs] at r2
    apply h' k' hk
    have : ((s.map (swapN i)).map W).toFinset = (s.map W).toFinset.image (rename (sig i)) := by
      ext v
      simp only [List.mem_toFinset,List.mem_map,Finset.mem_image,exists_exists_and_eq_and,swap_ok i hi]
    rw [this]
    exact r2
abbrev StD := List Nat × List (List Nat)
def picks : List Nat → List (Nat × List Nat)
  | [] => []
  | x::xs => (x,xs) :: (picks xs).map fun p => (p.1,x::p.2)
def pairs : List Nat → List (Nat × Nat × List Nat)
  | [] => []
  | x::xs => ((picks xs).map fun p => (x,p.1,p.2)) ++ (pairs xs).map fun p => (p.1,p.2.1,x::p.2.2)
theorem picks_ok {l : List Nat} {a : Nat} (h : a ∈ l) : ∃ p ∈ picks l, p.1 = a ∧ (a::p.2).Perm l := by
  induction l with
  | nil => cases h
  | cons x xs ih =>
    rcases List.mem_cons.mp h with rfl | h
    · exact ⟨(a,xs),by simp [picks],rfl,List.Perm.refl _⟩
    · obtain ⟨p,hp,rfl,q⟩ := ih h
      refine ⟨(p.1,x::p.2),?_,rfl,?_⟩
      · simp only [picks,List.mem_cons,List.mem_map]
        exact Or.inr ⟨p,hp,rfl⟩
      · exact (List.Perm.swap x p.1 p.2).trans (q.cons x)
theorem pairs_ok {l : List Nat} {a b : Nat} (ha : a ∈ l) (hb : b ∈ l) (hab : a ≠ b) :
    ∃ p ∈ pairs l, (p.1::p.2.1::p.2.2).Perm l ∧ ((p.1 = a ∧ p.2.1 = b) ∨ (p.1 = b ∧ p.2.1 = a)) := by
  induction l with
  | nil => cases ha
  | cons x xs ih =>
    have first (c : Nat) (hc : c ∈ xs) : ∃ p ∈ pairs (x::xs), (p.1::p.2.1::p.2.2).Perm (x::xs) ∧ p.1 = x ∧ p.2.1 = c := by
      obtain ⟨p,hp,rfl,q⟩ := picks_ok hc
      refine ⟨(x,p.1,p.2),?_,q.cons x,rfl,rfl⟩
      simp only [pairs,List.mem_append,List.mem_map]
      exact Or.inl ⟨p,hp,rfl⟩
    rcases List.mem_cons.mp ha with rfl | ha2
    · rcases List.mem_cons.mp hb with rfl | hb
      · exact absurd rfl hab
      · obtain ⟨p,h1,h2,h3,h4⟩ := first b hb
        exact ⟨p,h1,h2,Or.inl ⟨h3,h4⟩⟩
    · rcases List.mem_cons.mp hb with e | hb
      · subst e
        obtain ⟨p,h1,h2,h3,h4⟩ := first a ha2
        exact ⟨p,h1,h2,Or.inr ⟨h3,h4⟩⟩
      · obtain ⟨p,hp,q,e⟩ := ih ha2 hb
        refine ⟨(p.1,p.2.1,x::p.2.2),?_,?_,e⟩
        · simp only [pairs,List.mem_append,List.mem_map]
          exact Or.inr ⟨p,hp,rfl⟩
        · exact ((List.Perm.swap x p.2.1 p.2.2).cons p.1).trans ((List.Perm.swap x p.1 _).trans (q.cons x))
def mem1 (z : Nat) (l : List Nat) : Bool := l.any fun x => Nat.beq x z
def beqL : List Nat → List Nat → Bool
  | [],[] => true
  | x::xs,y::ys => Nat.beq x y && beqL xs ys
  | _,_ => false
theorem beqL_ok {a b : List Nat} (h : beqL a b = true) : a = b := by
  induction a generalizing b with
  | nil => cases b with
    | nil => rfl
    | cons => simp [beqL] at h
  | cons x xs ih => cases b with
    | nil => simp [beqL] at h
    | cons y ys =>
      simp only [beqL,Bool.and_eq_true] at h
      rw [Nat.eq_of_beq_eq_true h.1,ih h.2]
def ins (z : Nat) : List Nat → List Nat
  | [] => [z]
  | x::xs => bif Nat.ble z x then z::x::xs else x :: ins z xs
theorem mem_ins {z v : Nat} {l : List Nat} : v ∈ ins z l ↔ v = z ∨ v ∈ l := by
  induction l with
  | nil => simp [ins]
  | cons x xs ih =>
    unfold ins
    cases Nat.ble z x
    · simp only [cond_false,List.mem_cons,ih]
      tauto
    · simp
def kidN (rest : List Nat) (a b z : Nat) (ka kb : Bool) : List Nat :=
  ins z (bif ka then ins a (bif kb then ins b rest else rest) else bif kb then ins b rest else rest)
theorem kid_fin (rest : List Nat) (a b z : Nat) (ka kb : Bool) :
    ((kidN rest a b z ka kb).map W).toFinset = (kidW rest a b z ka kb).toFinset := by
  ext v
  cases ka <;> cases kb <;> simp [kidN,kidW,kept,mem_ins] <;> aesop
def keeps : List (Bool × Bool) := [(true,true),(true,false),(false,true),(false,false)]
def bl (b : Bool) : Nat := bif b then 1 else 0
def mkCut (u : Bool) (Z : List SliceD) (c : Nat × List (Nat × Nat × Nat)) : CutV :=
  let s := Z.getD c.1 (0,0,[])
  (s.1,s.2.1,c.2.length,mkPool u (initPool s.1 s.2.2) c.2)
abbrev Tabs := List CutV × List (Nat × Nat) × List KwD × List (List Nat)
def Tabs.cuts (t : Tabs) : List CutV := t.1
def Tabs.seps (t : Tabs) : List (Nat × Nat) := t.2.1
def Tabs.kws (t : Tabs) : List KwD := t.2.2.1
def Tabs.perms (t : Tabs) : List (List Nat) := t.2.2.2
def sortN (l : List Nat) : List Nat := l.foldr ins []
theorem mem_sortN {v : Nat} {l : List Nat} : v ∈ sortN l ↔ v ∈ l := by
  induction l with
  | nil => simp [sortN]
  | cons x xs ih =>
    change v ∈ ins x (sortN xs) ↔ _
    rw [mem_ins,ih]
    simp
def hintOK (u : Bool) (k : Nat) (next : List (List Nat)) (t : Tabs) (rest : List Nat) (a b z : Nat) (ka kb : Bool) (i : Nat) : Bool :=
  bif Nat.blt i 10000 then (match t.cuts[i]? with
    | some c => cutEval u k rest a b z ka kb c
    | none => false)
  else bif Nat.blt i 20000 then (match t.seps[i-10000]? with
    | some q => sepEval u rest a b z ka kb q
    | none => false)
  else bif Nat.blt i 30000 then (match t.kws[i-20000]? with
    | some q => !u && Nat.beq (kidN rest a b z ka kb).length (k+1) && kwList (kidN rest a b z ka kb) q
    | none => false)
  else (match t.perms[i-30000]? with
    | some l => next.any (beqL (sortN ((kidN rest a b z ka kb).map (permN l))))
    | none => false)
def kidOK (u : Bool) (k : Nat) (next : List (List Nat)) (t : Tabs) (rest : List Nat) (hints : List Nat)
    (a b z : Nat) (kk : Bool × Bool) : Bool :=
  Nat.blt k (Nat.add (Nat.add rest.length (Nat.add (bl kk.1) (bl kk.2))) 0) ||
  hints.any (hintOK u k next t rest a b z kk.1 kk.2)
def opsOf (u : Bool) : List Nat := bif u then [0,1,2,3] else [0,1]
def pairOK (u : Bool) (k : Nat) (next : List (List Nat)) (t : Tabs) (s : List Nat)
    (p : Nat × Nat × List Nat) (hints : List Nat) : Bool :=
  (opsOf u).all fun o =>
    let z := nb o p.1 p.2.1
    mem1 z s || Nat.beq z 0 || Nat.beq z full ||
      keeps.all (kidOK u k next t p.2.2 hints p.1 p.2.1 z)
def allZip (f : Nat × Nat × List Nat → List Nat → Bool) : List (Nat × Nat × List Nat) → List (List Nat) → Bool
  | [],_ => true
  | p::ps,[] => f p [] && allZip f ps []
  | p::ps,h::hs => f p h && allZip f ps hs
theorem allZip_ok {f ps hs} (h : allZip f ps hs = true) : ∀ p ∈ ps, ∃ x, f p x = true := by
  induction ps generalizing hs with
  | nil => intro p hp; cases hp
  | cons q ps ih =>
    intro p hp
    cases hs with
    | nil =>
      simp only [allZip,Bool.and_eq_true] at h
      rcases List.mem_cons.mp hp with rfl | hp
      · exact ⟨_,h.1⟩
      · exact ih h.2 p hp
    | cons x hs =>
      simp only [allZip,Bool.and_eq_true] at h
      rcases List.mem_cons.mp hp with rfl | hp
      · exact ⟨_,h.1⟩
      · exact ih h.2 p hp
def asc : List Nat → Bool
  | [] => true
  | [x] => Nat.blt x (2^128)
  | x::y::l => Nat.blt x y && asc (y::l)
theorem asc_ok {l : List Nat} (h : asc l = true) : l.Pairwise (· < ·) ∧ ∀ x ∈ l, x < 2^128 := by
  induction l with
  | nil => simp
  | cons x l ih =>
    cases l with
    | nil =>
      simp only [asc,Nat.blt_eq] at h
      simpa using h
    | cons y l =>
      simp only [asc,Bool.and_eq_true,Nat.blt_eq] at h
      obtain ⟨i1,i2⟩ := ih h.2
      have hy := List.pairwise_cons.mp i1
      refine ⟨List.pairwise_cons.mpr ⟨?_,i1⟩,?_⟩
      · intro v hv
        rcases List.mem_cons.mp hv with rfl | hv
        · exact h.1
        · exact h.1.trans (hy.1 v hv)
      · intro v hv
        rcases List.mem_cons.mp hv with rfl | hv
        · exact h.1.trans (i2 y (by simp))
        · exact i2 v hv
theorem asc_nodup {l : List Nat} (h : asc l = true) : l.Nodup ∧ (l.map W).Nodup := by
  obtain ⟨h1,h2⟩ := asc_ok h
  have nd : l.Nodup := h1.imp (fun h => Nat.ne_of_lt h)
  refine ⟨nd,?_⟩
  refine nd.map_on ?_
  intro x hx y hy e
  exact W_inj (h2 x hx) (h2 y hy) e
def stOK (u : Bool) (T : Nat) (t : Tabs) (k : Nat) (next : List (List Nat)) (st : StD) : Bool :=
  asc st.1 && !(mem1 T st.1) &&
  allZip (pairOK u k next t st.1) (pairs st.1) st.2
def levelOK (u : Bool) (T : Nat) (t : Tabs) (k : Nat) (next : List (List Nat)) (D : List StD) : Bool :=
  D.all (stOK u T t k next)
abbrev TabsP (u : Bool) (R : List Nat) (T : Nat) (t : Tabs) : Prop :=
  (∀ c ∈ t.cuts, CutP u R T c) ∧ t.seps.all (sepOK T) = true ∧ t.kws.all (kwOK T) = true ∧ t.perms.all (symOK T) = true
theorem TabsP.c {u R T t} (h : TabsP u R T t) : ∀ c ∈ t.cuts, CutP u R T c := h.1
theorem TabsP.s {u R T t} (h : TabsP u R T t) : t.seps.all (sepOK T) = true := h.2.1
theorem TabsP.k {u R T t} (h : TabsP u R T t) : t.kws.all (kwOK T) = true := h.2.2.1
theorem TabsP.p {u R T t} (h : TabsP u R T t) : t.perms.all (symOK T) = true := h.2.2.2
def LevelN (u : Bool) (T k : Nat) (D : List StD) : Prop :=
  ∀ st ∈ D, Impossible u (W T) k (st.1.map W).toFinset
theorem cutsGood {u R T} {Z : List SliceD} {C : List (Nat × List (Nat × Nat × Nat))} (hZ : ∀ s ∈ Z, SliceN u R T s)
    (hC : C.all (fun c => Nat.blt c.1 Z.length) = true) : ∀ c ∈ C.map (mkCut u Z), CutP u R T c := by
  intro c hc
  obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hc
  have hi : q.1 < Z.length := by simpa only [Nat.blt_eq] using List.all_eq_true.mp hC q hq
  have hm : Z.getD q.1 (0,0,[]) ∈ Z := by
    rw [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hi]
    exact List.getElem_mem hi
  obtain ⟨⟨f,roots,dom,base,nc,lo⟩,hv⟩ := hZ _ hm
  have ps : PS u f (roots.map observe) (initPool (Z.getD q.1 (0,0,[])).1 (Z.getD q.1 (0,0,[])).2.2) := by
    intro v hv'
    obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hv'
    rw [rf_land dom]
    exact base _ (List.mem_map_of_mem (hv j hj))
  obtain ⟨bank,b1,b2⟩ := mkPool_ok q.2 (Reach.start (u:=u) (roots:=roots.map observe)) ps
  refine ⟨f,roots,bank,dom,nc,?_,b2,lo⟩
  simpa [mkCut] using b1
theorem stStep {u R T E t k next st} (hB : baseOK T R E = true) (ht : TabsP u R T t)
    (hn : ∀ s ∈ next, Impossible u (W T) k (s.map W).toFinset)
    (h : stOK u T t k next st = true) : Impossible u (W T) (k+1) (st.1.map W).toFinset := by
  have b := baseOK_ok hB
  simp only [stOK,Bool.and_eq_true,Bool.not_eq_true'] at h
  obtain ⟨⟨ha,hT⟩,hz⟩ := h
  obtain ⟨nd,ndW⟩ := asc_nodup ha
  have lt := (asc_ok ha).2
  have hTm : W T ∉ st.1.map W := by
    intro hm
    obtain ⟨x,hx,e⟩ := List.mem_map.mp hm
    have := W_inj (lt x hx) b.lt e
    subst this
    have : mem1 x st.1 = true := List.any_eq_true.mpr ⟨x,hx,Nat.beq_refl x⟩
    rw [hT] at this
    exact Bool.noConfusion this
  apply enum_step ndW hTm
  intro a' ha' b' hb' d hd ka kb hab fresh hprop hlen
  obtain ⟨a,ham,rfl⟩ := List.mem_map.mp ha'
  obtain ⟨c,hcm,rfl⟩ := List.mem_map.mp hb'
  have hac : a ≠ c := fun h => hab (by rw [h])
  have inOps : ∀ {o : Nat}, allowed u o → o ∈ opsOf u := by
    intro o h
    cases u
    · rcases h with h | ⟨h,_⟩
      · have : o = 0 ∨ o = 1 := by omega
        simpa [opsOf] using this
      · exact Bool.noConfusion h
    · have : o = 0 ∨ o = 1 ∨ o = 2 ∨ o = 3 := by rcases h with h | ⟨_,h⟩ <;> omega
      simpa [opsOf] using this
  have opk : ∀ {o : Nat}, allowed u o → opOK u o = true := by
    intro o h
    cases u
    · rcases h with h | ⟨h,_⟩
      · simpa only [opOK,Bool.false_or,Nat.blt_eq] using h
      · exact Bool.noConfusion h
    · rfl
  obtain ⟨p,hp,perm,ho⟩ := pairs_ok ham hcm hac
  obtain ⟨x,hx⟩ := allZip_ok hz p hp
  have core : ∀ (o : Nat) (ja jb : Bool), allowed u o → W (nb o p.1 p.2.1) = bin d (W a) (W c) →
      (p.2.2.length + (bl ja + bl jb) ≤ k) →
      Impossible u (W T) k (kidW p.2.2 p.1 p.2.1 (nb o p.1 p.2.1) ja jb).toFinset := by
    intro o ja jb ho4 hW hl
    have hf := List.all_eq_true.mp hx o (inOps ho4)
    simp only [Bool.or_eq_true] at hf
    have pm (v : Nat) : v ∈ st.1 ↔ v = p.1 ∨ v = p.2.1 ∨ v ∈ p.2.2 := by
      rw [←perm.mem_iff]
      simp
    rcases hf with ((hf | hf) | hf) | hf
    · exfalso
      obtain ⟨y,hy,e⟩ := List.any_eq_true.mp hf
      apply fresh
      rw [←hW,←Nat.eq_of_beq_eq_true e]
      exact List.mem_map_of_mem hy
    · exfalso
      apply hprop.1
      rw [←hW,Nat.eq_of_beq_eq_true hf]
      rfl
    · exfalso
      apply hprop.2
      rw [←hW,Nat.eq_of_beq_eq_true hf]
      exact W_full
    have hk := List.all_eq_true.mp hf (ja,jb) (by cases ja <;> cases jb <;> simp [keeps])
    simp only [kidOK,Bool.or_eq_true] at hk
    have ndp : ((p.1::p.2.1::p.2.2).map W).Nodup := (perm.map W).nodup_iff.mpr ndW
    simp only [List.map_cons,List.nodup_cons,List.mem_cons,not_or] at ndp
    have nk : (kidW p.2.2 p.1 p.2.1 (nb o p.1 p.2.1) ja jb).Nodup := by
      have n1 := kept_nd jb (W p.2.1) _ ndp.2.2 ndp.2.1
      have n2 : W p.1 ∉ kept jb (W p.2.1) (p.2.2.map W) := by
        cases jb
        · exact ndp.1.2
        · simp only [kept,if_true,List.mem_cons,not_or]
          exact ndp.1
      refine List.nodup_cons.mpr ⟨?_,kept_nd ja _ _ n1 n2⟩
      intro hm
      apply fresh
      rw [←hW]
      have sub : W (nb o p.1 p.2.1) ∈ (p.1::p.2.1::p.2.2).map W := by
        rcases mem_kept hm with h | h
        · rw [h]; simp
        · rcases mem_kept h with h | h
          · rw [h]; simp
          · simp [h]
      exact (perm.map W).mem_iff.mp sub
    rcases hk with hk | hk
    · exfalso
      rw [Nat.blt_eq] at hk
      have : k < p.2.2.length + (bl ja + bl jb) + 0 := hk
      omega
    · obtain ⟨i,_,hi⟩ := List.any_eq_true.mp hk
      unfold hintOK at hi
      have sub : ∀ x ∈ kidN p.2.2 p.1 p.2.1 (nb o p.1 p.2.1) ja jb, x < 2^128 := by
        intro x hx
        have hx' : x = nb o p.1 p.2.1 ∨ x ∈ st.1 := by
          unfold kidN at hx
          rw [mem_ins] at hx
          rcases hx with hx | hx
          · exact Or.inl hx
          · right
            rw [pm]
            cases ja <;> cases jb <;> simp only [cond_true,cond_false,mem_ins] at hx <;> tauto
        rcases hx' with rfl | hx'
        · have l1 : p.1 < 2^128 := lt _ ((pm _).mpr (Or.inl rfl))
          have l2 : p.2.1 < 2^128 := lt _ ((pm _).mpr (Or.inr (Or.inl rfl)))
          have la : Nat.land p.1 p.2.1 < 2^128 := Nat.lt_of_le_of_lt (Nat.and_le_left) l1
          unfold nb
          cases Nat.beq o 0 <;> cases Nat.beq o 1 <;> cases Nat.beq o 2 <;>
            first | exact la | exact Nat.or_lt_two_pow l1 l2 | exact Nat.xor_lt_two_pow l1 la | exact Nat.xor_lt_two_pow l2 la
        · exact lt x hx'
      cases h1 : Nat.blt i 10000
      · rw [h1,cond_false] at hi
        cases h2 : Nat.blt i 20000
        · rw [h2,cond_false] at hi
          cases h3 : Nat.blt i 30000
          · rw [h3,cond_false] at hi
            cases hg : t.perms[i-30000]? with
            | none => rw [hg] at hi; exact Bool.noConfusion hi
            | some l =>
              rw [hg] at hi
              obtain ⟨s,hs',e⟩ := List.any_eq_true.mp hi
              rw [←kid_fin]
              apply perm_sound l (List.all_eq_true.mp ht.p l (List.mem_of_getElem? hg))
              have : (((kidN p.2.2 p.1 p.2.1 (nb o p.1 p.2.1) ja jb).map (permN l)).map W).toFinset = (s.map W).toFinset := by
                rw [←beqL_ok e]
                ext v
                simp only [List.mem_toFinset,List.mem_map,mem_sortN]
              rw [this]
              exact hn s hs'
          · rw [h3,cond_true] at hi
            cases hg : t.kws[i-20000]? with
            | none => rw [hg] at hi; exact Bool.noConfusion hi
            | some q =>
              rw [hg] at hi
              simp only [Bool.and_eq_true,Bool.not_eq_true'] at hi
              obtain ⟨⟨hu,hlen⟩,hkw⟩ := hi
              rw [←kid_fin]
              have sz := Nat.eq_of_beq_eq_true hlen
              have nd' : ((kidN p.2.2 p.1 p.2.1 (nb o p.1 p.2.1) ja jb).map W).Nodup := by
                apply List.dedup_eq_self.mp
                apply (List.dedup_sublist _).eq_of_length
                have c1 : ((kidN p.2.2 p.1 p.2.1 (nb o p.1 p.2.1) ja jb).map W).toFinset.card = (kidW p.2.2 p.1 p.2.1 (nb o p.1 p.2.1) ja jb).length := by
                  rw [kid_fin,List.toFinset_card_of_nodup nk]
                rw [List.card_toFinset] at c1
                rw [c1,List.length_map]
                have il : ∀ (z : Nat) (l : List Nat), (ins z l).length = l.length + 1 := by
                  intro z l
                  induction l with
                  | nil => rfl
                  | cons x xs ih =>
                    unfold ins
                    cases Nat.ble z x
                    · rw [cond_false,List.length_cons,ih,List.length_cons]
                    · rfl
                unfold kidN kidW
                cases ja <;> cases jb <;> simp [kept,il]
              subst hu
              exact kw_sound nd' sz sub q (List.all_eq_true.mp ht.k q (List.mem_of_getElem? hg)) hkw
        · rw [h2,cond_true] at hi
          cases hg : t.seps[i-10000]? with
          | none => rw [hg] at hi; exact Bool.noConfusion hi
          | some q =>
            rw [hg] at hi
            exact sep_sound (List.all_eq_true.mp ht.s q (List.mem_of_getElem? hg)) hi
      · rw [h1,cond_true] at hi
        cases hg : t.cuts[i]? with
        | none => rw [hg] at hi; exact Bool.noConfusion hi
        | some q =>
          rw [hg] at hi
          exact cut_sound (ht.c q (List.mem_of_getElem? hg)) (opk ho4) nk hi
  have rp : (((st.1.map W).erase (W a)).erase (W c)).Perm (p.2.2.map W) := by
    have e : (W a :: W c :: p.2.2.map W).Perm (st.1.map W) := by
      rcases ho with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
      · exact perm.map W
      · exact (List.Perm.swap _ _ _).trans (perm.map W)
    have e1 := e.erase (W a)
    rw [List.erase_cons_head] at e1
    have e2 := e1.erase (W c)
    rw [List.erase_cons_head] at e2
    exact e2.symm
  have lenr : (((st.1.map W).erase (W a)).erase (W c)).length = p.2.2.length := by
    rw [rp.length_eq,List.length_map]
  have fits : p.2.2.length + (bl ka + bl kb) ≤ k := by
    have h := hlen
    unfold childTwo at h
    cases ka <;> cases kb <;> simp [kept,lenr] at h <;> simp [bl] <;> omega
  rw [Nat.add_sub_cancel]
  rcases ho with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · have r := core d ka kb hd (W_nb _ _ _) fits
    have e : (childTwo (st.1.map W) (W p.1) (W p.2.1) d ka kb).toFinset = (kidW p.2.2 p.1 p.2.1 (nb d p.1 p.2.1) ka kb).toFinset := by
      unfold childTwo kidW
      rw [W_nb]
      ext v
      cases ka <;> cases kb <;> simp [kept,rp.mem_iff]
    rw [e]
    exact r
  · have hfl := flip_flip hd
    have r := core (flipOp d) kb ka hfl.1 (by rw [W_nb]; exact (bin_flip hd _ _).symm) (by omega)
    have e : (childTwo (st.1.map W) (W p.2.1) (W p.1) d ka kb).toFinset = (kidW p.2.2 p.1 p.2.1 (nb (flipOp d) p.1 p.2.1) kb ka).toFinset := by
      unfold childTwo kidW
      rw [W_nb,bin_flip hd]
      ext v
      cases ka <;> cases kb <;> simp [kept,rp.mem_iff] <;> tauto
    rw [e]
    exact r
theorem levelStep {u R T E t k D' D} (hB : baseOK T R E = true) (ht : TabsP u R T t)
    (hI : LevelN u T k D') (h : levelOK u T t k (D'.map Prod.fst) D = true) : LevelN u T (k+1) D := by
  intro st hst
  refine stStep hB ht ?_ (List.all_eq_true.mp h st hst)
  intro s hs
  obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hs
  exact hI q hq
theorem chunks {u : Bool} {T : Nat} {t : Tabs} {k : Nat} {next : List (List Nat)} (c : Nat) (D : List StD) (n : Nat) (hc : 0 < c)
    (hl : Nat.ble D.length (n*c) = true)
    (h : ∀ i, i < n → levelOK u T t k next ((D.drop (i*c)).take c) = true) : levelOK u T t k next D = true := by
  rw [levelOK,List.all_eq_true]
  intro x hx
  obtain ⟨j,hj,rfl⟩ := List.getElem_of_mem hx
  have hl' := Nat.le_of_ble_eq_true hl
  have hi : j / c < n := by
    rw [Nat.div_lt_iff_lt_mul hc]
    omega
  refine List.all_eq_true.mp (h _ hi) _ ?_
  have hm : j / c * c + j % c = j := by rw [Nat.mul_comm]; exact Nat.div_add_mod j c
  have hmod := Nat.mod_lt j hc
  refine List.mem_of_getElem? (i := j % c) ?_
  rw [List.getElem?_take_of_lt hmod,List.getElem?_drop,hm]
  exact List.getElem?_eq_getElem hj
theorem lowSearch {u R T E K D} (hB : baseOK T R E = true) (hI : LevelN u T K D)
    (h : (D.map Prod.fst).contains (R.map xN) = true) : LowN u R T (K+1) := by
  apply lowOf hB
  simp only [List.contains_eq_mem,decide_eq_true_eq] at h
  obtain ⟨q,hq,e⟩ := List.mem_map.mp h
  have := hI q hq
  rw [e] at this
  simpa only [rootsW,List.map_map,Function.comp_def] using this
end PEqualNP.Outside.L_meta_10393_aux

namespace PEqualNP.Outside.L_meta_10393_aux
open PEqualNP.CircuitLowerBounds
def sw0 : Nat := 0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa
def sw1 : Nat := 0xcccccccccccccccccccccccccccccccc
def sw2 : Nat := 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0
def sw3 : Nat := 0xff00ff00ff00ff00ff00ff00ff00ff00
def sw4 : Nat := 0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee
def sw5 : Nat := 0xffaaffaaffaaffaaffaaffaaffaaffaa
def sw6 : Nat := 0xffccffccffccffccffccffccffccffcc
def sw7 : Nat := 0xfefefefefefefefefefefefefefefefe
def sw8 : Nat := 0xee00ee00ee00ee00ee00ee00ee00ee
def sw9 : Nat := 0xfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfc
def sw10 : Nat := 0xfff0fff0fff0fff0fff0fff0fff0fff0
def sw11 : Nat := 0xfe00fe00fe00fe00fe00fe00fe00fe
def sw12 : Nat := 0xffff0000ffff0000ffff0000ffff0000
def sw13 : Nat := 0xffffaaaaffffaaaaffffaaaaffffaaaa
def sw14 : Nat := 0xffffccccffffccccffffccccffffcccc
def sw15 : Nat := 0xeeee0000eeee0000eeee0000eeee
def sw16 : Nat := 0xfffff0f0fffff0f0fffff0f0fffff0f0
def sw17 : Nat := 0xffffff00ffffff00ffffff00ffffff00
def sw18 : Nat := 0xfffffafafffffafafffffafafffffafa
def sw19 : Nat := 0xfffffcfcfffffcfcfffffcfcfffffcfc
def sw20 : Nat := 0xffeeffeeffeeffeeffeeffeeffeeffee
def sw21 : Nat := 0xffffeeeeffffeeeeffffeeeeffffeeee
def sw22 : Nat := 0xfffefffefffefffefffefffefffefffe
def sw23 : Nat := 0xfefe0000fefe0000fefe0000fefe
def sw24 : Nat := 0xaaa8aaa8aaa8aaa8aaa8aaa8aaa8aaa8
def sw25 : Nat := 0xfffcfffcfffcfffcfffcfffcfffcfffc
def sw26 : Nat := 0xa0000000a0000000a0000000a
def sw27 : Nat := 0xfffffff0fffffff0fffffff0fffffff0
def sw28 : Nat := 0x88888888888888888888888888888888
def sw29 : Nat := 0xaaaa0000aaaa0000aaaa0000aaaa
def sw30 : Nat := 0xaaaafefeaaaafefeaaaafefeaaaafefe
def sw31 : Nat := 0xf000f000f000f000f000f000f000f000
def sw32 : Nat := 0xfc00fc00fc00fc00fc00fc00fc00fc
def sw33 : Nat := 0xee000000ee000000ee000000ee
def sw34 : Nat := 0xfffafffafffafffafffafffafffafffa
def sw35 : Nat := 0xffffffaaffffffaaffffffaaffffffaa
def sw36 : Nat := 0xfafafafafafafafafafafafafafafafa
def sw37 : Nat := 0xfffffffcfffffffcfffffffcfffffffc
def sw38 : Nat := 0xffffffccffffffccffffffccffffffcc
def sw39 : Nat := 0xfa00fa00fa00fa00fa00fa00fa00fa
def sw40 : Nat := 0xfffe0000fffe0000fffe0000fffe
def sw41 : Nat := 0xfffffe00fffffe00fffffe00fffffe00
def sw42 : Nat := 0x2aaaa0002aaaa0002aaaa0002aaaa
def sw43 : Nat := 0xfffffefefffffefefffffefefffffefe
def sw44 : Nat := 0xaaaaaaa8aaaaaaa8aaaaaaa8aaaaaaa8
def sw45 : Nat := 0xfffffffefffffffefffffffefffffffe
def sw46 : Nat := 0xaaaafffeaaaafffeaaaafffeaaaafffe
def sw47 : Nat := 0xfe000000fe000000fe000000fe
def sw48 : Nat := 0xfffc0000fffc0000fffc0000fffc
def sw49 : Nat := 0xffff000affff000affff000affff000a
def sw50 : Nat := 0x55555550555555505555555055555550
def sw51 : Nat := 0xffff8888ffff8888ffff8888ffff8888
def sw52 : Nat := 0xfffefefefffefefefffefefefffefefe
def sw53 : Nat := 0xfefefe00fefefe00fefefe00fefefe
def sw54 : Nat := 0xff000000ff000000ff000000ff000000
def sw55 : Nat := 0xffff00aaffff00aaffff00aaffff00aa
def sw56 : Nat := 0xfefefffefefefffefefefffefefefffe
def sw57 : Nat := 0xaaa8fffcaaa8fffcaaa8fffcaaa8fffc
def sw58 : Nat := 0xffff00eeffff00eeffff00eeffff00ee
def sw59 : Nat := 0xaafeaafeaafeaafeaafeaafeaafeaafe
def sw60 : Nat := 0xeeeefffeeeeefffeeeeefffeeeeefffe
def sw61 : Nat := 0xaafe0000aafe0000aafe0000aafe
def sw62 : Nat := 0x8888fff88888fff88888fff88888fff8
def sw63 : Nat := 0xfcccfcccfcccfcccfcccfcccfcccfccc
def sw64 : Nat := 0xfffff000fffff000fffff000fffff000
def sw65 : Nat := 0xfff00000fff00000fff00000fff0
def sw66 : Nat := 0xaafcfe00aafcfe00aafcfe00aafcfe
def sw67 : Nat := 0xccfcccfcccfcccfcccfcccfcccfcccfc
def sw68 : Nat := 0xffffffeeffffffeeffffffeeffffffee
def sw69 : Nat := 0xf3f2f3f2f3f2f3f2f3f2f3f2f3f2f3f2
def sw70 : Nat := 0xf3f0f3f0f3f0f3f0f3f0f3f0f3f0f3f0
def sw71 : Nat := 0xaafaaafaaafaaafaaafaaafaaafaaafa
def sw72 : Nat := 0xfff0f0f0fff0f0f0fff0f0f0fff0f0f0
def sw73 : Nat := 0xfffffffafffffffafffffffafffffffa
def sw74 : Nat := 0xffffee00ffffee00ffffee00ffffee
def sw75 : Nat := 0xffa00000ffa00000ffa00000ffa
def sw76 : Nat := 0xeaeaeaeaeaeaeaeaeaeaeaeaeaeaeaea
def sw77 : Nat := 0xffc0ffc0ffc0ffc0ffc0ffc0ffc0ffc0
def sw78 : Nat := 0xffffc0c0ffffc0c0ffffc0c0ffffc0c0
def sw79 : Nat := 0x3fffc0003fffc0003fffc0003fffc
def sw80 : Nat := 0xfffeff00fffeff00fffeff00fffeff00
def sw81 : Nat := 0xff00fe00ff00fe00ff00fe00ff00fe00
def sw82 : Nat := 0xaaaafffcaaaafffcaaaafffcaaaafffc
def sw83 : Nat := 0x99989998999899989998999899989998
def sw84 : Nat := 0xffccccccffccccccffccccccffcccccc
def sw85 : Nat := 0xffe00000ffe00000ffe00000ffe
def sw86 : Nat := 0xffffffff00000000ffffffff00000000
def s1_T : Nat := 0x88888888888888888888888888888888
def s1_R : List Nat := [0, 1]
def s1_E : List (Nat × Nat × Nat) := [(0,2,3),(1,1,3)]
theorem s1_B : baseOK s1_T s1_R s1_E = true := by decide +kernel
theorem s1_L : LowN true s1_R s1_T 1 := lowCount s1_B (by decide +kernel)
def s2_T : Nat := 0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee
def s2_R : List Nat := [0, 1]
def s2_E : List (Nat × Nat × Nat) := [(0,0,1),(1,0,2)]
theorem s2_B : baseOK s2_T s2_R s2_E = true := by decide +kernel
theorem s2_L : LowN true s2_R s2_T 1 := lowCount s2_B (by decide +kernel)
def s3_T : Nat := 0xe8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8
def s3_R : List Nat := [0, 1, 2]
def s3_E : List (Nat × Nat × Nat) := [(0,2,3),(1,1,3),(2,1,5)]
theorem s3_B : baseOK s3_T s3_R s3_E = true := by decide +kernel
theorem s3_S0 : SliceN true s3_R s3_T (0x33333333333333333333333333333333,1,[0, 2]) := mkSlice (w:=0) s3_B s1_B s1_L (by decide +kernel)
theorem s3_S1 : SliceN true s3_R s3_T (0x55555555555555555555555555555555,1,[1, 2]) := mkSlice (w:=0) s3_B s1_B s1_L (by decide +kernel)
theorem s3_S2 : SliceN true s3_R s3_T (0xcccccccccccccccccccccccccccccccc,1,[0, 2]) := mkSlice (w:=2) s3_B s2_B s2_L (by decide +kernel)
theorem s3_S3 : SliceN true s3_R s3_T (0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,1,[1, 2]) := mkSlice (w:=1) s3_B s2_B s2_L (by decide +kernel)
theorem s3_S4 : SliceN true s3_R s3_T (0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f,1,[0, 1]) := mkSlice (w:=0) s3_B s1_B s1_L (by decide +kernel)
theorem s3_S5 : SliceN true s3_R s3_T (0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,1,[0, 1]) := mkSlice (w:=4) s3_B s2_B s2_L (by decide +kernel)
def s3_Z : List SliceD := [(0x33333333333333333333333333333333,1,[0, 2]),(0x55555555555555555555555555555555,1,[1, 2]),(0xcccccccccccccccccccccccccccccccc,1,[0, 2]),(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,1,[1, 2]),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f,1,[0, 1]),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,1,[0, 1])]
theorem s3_Y : ∀ s ∈ s3_Z, SliceN true s3_R s3_T s := by
  unfold s3_Z
  simp only [List.forall_mem_cons]
  exact ⟨s3_S0,s3_S1,s3_S2,s3_S3,s3_S4,s3_S5,by simp⟩
def s3_C : List (Nat × List (Nat × Nat × Nat)) := [(0,[]),(1,[]),(2,[]),(3,[]),(4,[]),(5,[])]
def s3_t : Tabs := (s3_C.map (mkCut true s3_Z),[(5,4),(3,1),(3,0),(3,2),(6,2),(5,1)],[],[])
theorem s3_W : TabsP true s3_R s3_T s3_t := ⟨cutsGood s3_Y (by decide +kernel),by decide +kernel,by decide +kernel,by decide +kernel⟩
noncomputable def s3_D3 : List StD := [
([sw0,sw1,sw2],[[0,1,10000,2,3,10001,10002],[4,1,10003,10000,3],[10001,0,5,2,10004,10005]])]
def s3_D2 : List StD := []
theorem s3_I2 : LevelN true s3_T 2 s3_D2 := by intro s h; cases h
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem s3_C3x0 : levelOK true s3_T s3_t 2 (s3_D2.map Prod.fst) ((s3_D3.drop (0*16)).take 16) = true := by decide +kernel
theorem s3_I3 : LevelN true s3_T 3 s3_D3 := levelStep s3_B s3_W s3_I2 (chunks 16 s3_D3 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact s3_C3x0
  ))
theorem s3_L : LowN true s3_R s3_T 4 := lowSearch s3_B s3_I3 (by decide +kernel)
def s4_T : Nat := 0xfefefefefefefefefefefefefefefefe
def s4_R : List Nat := [0, 1, 2]
def s4_E : List (Nat × Nat × Nat) := [(0,0,1),(1,0,2),(2,0,4)]
theorem s4_B : baseOK s4_T s4_R s4_E = true := by decide +kernel
theorem s4_L : LowN true s4_R s4_T 2 := lowCount s4_B (by decide +kernel)
def s5_T : Nat := 0xfee8fee8fee8fee8fee8fee8fee8fee8
def s5_R : List Nat := [0, 1, 2, 3]
def s5_E : List (Nat × Nat × Nat) := [(0,2,3),(1,1,3),(2,1,5),(3,1,9)]
theorem s5_B : baseOK s5_T s5_R s5_E = true := by decide +kernel
theorem s5_S0 : SliceN true s5_R s5_T (0x55555555555555555555555555555555,4,[1, 2, 3]) := mkSlice (w:=0) s5_B s3_B s3_L (by decide +kernel)
theorem s5_S1 : SliceN true s5_R s5_T (0x33333333333333333333333333333333,4,[0, 2, 3]) := mkSlice (w:=0) s5_B s3_B s3_L (by decide +kernel)
theorem s5_S2 : SliceN true s5_R s5_T (0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f,4,[0, 1, 3]) := mkSlice (w:=0) s5_B s3_B s3_L (by decide +kernel)
theorem s5_S3 : SliceN true s5_R s5_T (0xff00ff00ff00ff00ff00ff00ff00ff,4,[0, 1, 2]) := mkSlice (w:=0) s5_B s3_B s3_L (by decide +kernel)
theorem s5_S4 : SliceN true s5_R s5_T (0x11111111111111111111111111111111,1,[2, 3]) := mkSlice (w:=0) s5_B s1_B s1_L (by decide +kernel)
theorem s5_S5 : SliceN true s5_R s5_T (0x22222222222222222222222222222222,1,[2, 3]) := mkSlice (w:=1) s5_B s2_B s2_L (by decide +kernel)
theorem s5_S6 : SliceN true s5_R s5_T (0x44444444444444444444444444444444,1,[2, 3]) := mkSlice (w:=2) s5_B s2_B s2_L (by decide +kernel)
theorem s5_S7 : SliceN true s5_R s5_T (0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,2,[1, 2, 3]) := mkSlice (w:=1) s5_B s4_B s4_L (by decide +kernel)
theorem s5_S8 : SliceN true s5_R s5_T (0xcccccccccccccccccccccccccccccccc,2,[0, 2, 3]) := mkSlice (w:=2) s5_B s4_B s4_L (by decide +kernel)
theorem s5_S9 : SliceN true s5_R s5_T (0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,2,[0, 1, 3]) := mkSlice (w:=4) s5_B s4_B s4_L (by decide +kernel)
theorem s5_S10 : SliceN true s5_R s5_T (0xaa00aa00aa00aa00aa00aa00aa00aa,1,[1, 2]) := mkSlice (w:=1) s5_B s2_B s2_L (by decide +kernel)
theorem s5_S11 : SliceN true s5_R s5_T (0xff00ff00ff00ff00ff00ff00ff00ff00,2,[0, 1, 2]) := mkSlice (w:=8) s5_B s4_B s4_L (by decide +kernel)
theorem s5_S12 : SliceN true s5_R s5_T (0xcc00cc00cc00cc00cc00cc00cc00cc,1,[0, 2]) := mkSlice (w:=2) s5_B s2_B s2_L (by decide +kernel)
theorem s5_S13 : SliceN true s5_R s5_T (0x50505050505050505050505050505050,1,[1, 3]) := mkSlice (w:=4) s5_B s2_B s2_L (by decide +kernel)
def s5_Z : List SliceD := [(0x55555555555555555555555555555555,4,[1, 2, 3]),(0x33333333333333333333333333333333,4,[0, 2, 3]),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f,4,[0, 1, 3]),(0xff00ff00ff00ff00ff00ff00ff00ff,4,[0, 1, 2]),(0x11111111111111111111111111111111,1,[2, 3]),(0x22222222222222222222222222222222,1,[2, 3]),(0x44444444444444444444444444444444,1,[2, 3]),(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,2,[1, 2, 3]),(0xcccccccccccccccccccccccccccccccc,2,[0, 2, 3]),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,2,[0, 1, 3]),(0xaa00aa00aa00aa00aa00aa00aa00aa,1,[1, 2]),(0xff00ff00ff00ff00ff00ff00ff00ff00,2,[0, 1, 2]),(0xcc00cc00cc00cc00cc00cc00cc00cc,1,[0, 2]),(0x50505050505050505050505050505050,1,[1, 3])]
theorem s5_Y : ∀ s ∈ s5_Z, SliceN true s5_R s5_T s := by
  unfold s5_Z
  simp only [List.forall_mem_cons]
  exact ⟨s5_S0,s5_S1,s5_S2,s5_S3,s5_S4,s5_S5,s5_S6,s5_S7,s5_S8,s5_S9,s5_S10,s5_S11,s5_S12,s5_S13,by simp⟩
def s5_C : List (Nat × List (Nat × Nat × Nat)) := [(0,[]),(1,[]),(2,[]),(3,[]),(2,[(1,0,1)]),(3,[(1,0,1)]),(4,[]),(0,[(1,0,2)]),(1,[(1,0,2)]),(5,[]),(1,[(3,0,2)]),(6,[]),(0,[(3,0,2)]),(2,[(1,1,2)]),(2,[(1,0,2)]),(0,[(1,0,1)]),(1,[(1,0,1)]),(1,[(3,0,1)]),(7,[]),(0,[(3,0,1)]),(8,[]),(0,[(2,0,1)]),(9,[]),(10,[]),(0,[(2,0,2)]),(11,[]),(12,[]),(0,[(1,0,2),(1,1,2)]),(8,[(1,1,2)]),(0,[(1,0,1),(1,1,2)]),(0,[(1,0,1),(1,0,2)]),(0,[(1,1,2),(1,0,3)]),(3,[(3,1,2)]),(0,[(0,0,2)]),(0,[(2,1,2)]),(0,[(0,1,2)]),(13,[])]
def s5_t : Tabs := (s5_C.map (mkCut true s5_Z),[(5,4),(3,2),(3,1),(5,1),(9,8),(9,1),(6,4),(6,2),(10,8),(10,2),(12,8),(12,4),(7,8)],[],[[],[1],[2,1],[0,1],[0,2,1],[1,0,2,1],[0,1,2],[0,1,2,1],[1,2],[1,2,1],[2],[1,0]])
theorem s5_W : TabsP true s5_R s5_T s5_t := ⟨cutsGood s5_Y (by decide +kernel),by decide +kernel,by decide +kernel,by decide +kernel⟩
noncomputable def s5_D6 : List StD := [
([sw0,sw1,sw2,sw3],[[0,1,10000,30000,10001,10002],[0,10001,30001,10000,10003,2],[0,10000,30002,10004,10005,3],[1,10002,30003,10006,10007,2],[1,10002,30004,10008,10009,3],[2,10003,30005,10010,10011,3]])]
noncomputable def s5_D5 : List StD := [
([sw0,sw1,sw4,sw2,sw3],[[0,1],[1],[0,30006,10003,4],[0,30007,10005,5],[0],[1,30008,10007,4],[1,30009,10009,5],[4,6,2,30000,10003,30010,10010],[5,6,3,30010,10005,30000,10011],[10003,4,10010,10011]])]
noncomputable def s5_D4 : List StD := [
([sw0,sw1,sw2,sw5,sw6],[[7,30011,8],[7,9],[10],[7,8,9],[8,11],[8,7,11],[12],[13,9,10007],[14,11,10003],[7,8]]),
([sw0,sw1,sw2,sw7,sw3],[[15,4,16],[15,16,4],[17],[15,18],[4,15,16],[19],[16,20],[21],[4,22],[3,18,30000]]),
([sw8,sw0,sw1,sw2,sw3],[[0,1],[1,0],[2,23,6],[7],[24,23],[6,23],[6,25,5],[6,26],[23,25],[23,25]])]
noncomputable def s5_D3 : List StD := [
([sw0,sw9,sw6,sw10],[[27,28,10012],[29,28,10000],[30,10000,10001],[3,31,32],[3,28,1],[1,28]]),
([sw11,sw0,sw1,sw2],[[0,18],[24,20,33],[34,6,35],[36,18],[11,18],[9,20]])]
def s5_D2 : List StD := []
theorem s5_I2 : LevelN true s5_T 2 s5_D2 := by intro s h; cases h
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem s5_C3x0 : levelOK true s5_T s5_t 2 (s5_D2.map Prod.fst) ((s5_D3.drop (0*16)).take 16) = true := by decide +kernel
theorem s5_I3 : LevelN true s5_T 3 s5_D3 := levelStep s5_B s5_W s5_I2 (chunks 16 s5_D3 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact s5_C3x0
  ))
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem s5_C4x0 : levelOK true s5_T s5_t 3 (s5_D3.map Prod.fst) ((s5_D4.drop (0*16)).take 16) = true := by decide +kernel
theorem s5_I4 : LevelN true s5_T 4 s5_D4 := levelStep s5_B s5_W s5_I3 (chunks 16 s5_D4 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact s5_C4x0
  ))
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem s5_C5x0 : levelOK true s5_T s5_t 4 (s5_D4.map Prod.fst) ((s5_D5.drop (0*16)).take 16) = true := by decide +kernel
theorem s5_I5 : LevelN true s5_T 5 s5_D5 := levelStep s5_B s5_W s5_I4 (chunks 16 s5_D5 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact s5_C5x0
  ))
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem s5_C6x0 : levelOK true s5_T s5_t 5 (s5_D5.map Prod.fst) ((s5_D6.drop (0*16)).take 16) = true := by decide +kernel
theorem s5_I6 : LevelN true s5_T 6 s5_D6 := levelStep s5_B s5_W s5_I5 (chunks 16 s5_D6 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact s5_C6x0
  ))
theorem s5_L : LowN true s5_R s5_T 7 := lowSearch s5_B s5_I6 (by decide +kernel)
def s6_T : Nat := 0xfffefffefffefffefffefffefffefffe
def s6_R : List Nat := [0, 1, 2, 3]
def s6_E : List (Nat × Nat × Nat) := [(0,0,1),(1,0,2),(2,0,4),(3,0,8)]
theorem s6_B : baseOK s6_T s6_R s6_E = true := by decide +kernel
theorem s6_L : LowN true s6_R s6_T 3 := lowCount s6_B (by decide +kernel)
def s7_T : Nat := 0xfffefee8fffefee8fffefee8fffefee8
def s7_R : List Nat := [0, 1, 2, 3, 4]
def s7_E : List (Nat × Nat × Nat) := [(0,2,3),(1,1,3),(2,1,5),(3,1,9),(4,1,17)]
theorem s7_B : baseOK s7_T s7_R s7_E = true := by decide +kernel
theorem s7_S0 : SliceN true s7_R s7_T (0x55555555555555555555555555555555,7,[1, 2, 3, 4]) := mkSlice (w:=0) s7_B s5_B s5_L (by decide +kernel)
theorem s7_S1 : SliceN true s7_R s7_T (0x33333333333333333333333333333333,7,[0, 2, 3, 4]) := mkSlice (w:=0) s7_B s5_B s5_L (by decide +kernel)
theorem s7_S2 : SliceN true s7_R s7_T (0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f,7,[0, 1, 3, 4]) := mkSlice (w:=0) s7_B s5_B s5_L (by decide +kernel)
theorem s7_S3 : SliceN true s7_R s7_T (0xff00ff00ff00ff00ff00ff00ff00ff,7,[0, 1, 2, 4]) := mkSlice (w:=0) s7_B s5_B s5_L (by decide +kernel)
theorem s7_S4 : SliceN true s7_R s7_T (0xffff0000ffff0000ffff0000ffff,7,[0, 1, 2, 3]) := mkSlice (w:=0) s7_B s5_B s5_L (by decide +kernel)
theorem s7_S5 : SliceN true s7_R s7_T (0x11111111111111111111111111111111,4,[2, 3, 4]) := mkSlice (w:=0) s7_B s3_B s3_L (by decide +kernel)
theorem s7_S6 : SliceN true s7_R s7_T (0x3333000033330000333300003333,4,[0, 2, 3]) := mkSlice (w:=0) s7_B s3_B s3_L (by decide +kernel)
theorem s7_S7 : SliceN true s7_R s7_T (0x5555000055550000555500005555,4,[1, 2, 3]) := mkSlice (w:=0) s7_B s3_B s3_L (by decide +kernel)
theorem s7_S8 : SliceN true s7_R s7_T (0x3030303030303030303030303030303,4,[0, 3, 4]) := mkSlice (w:=0) s7_B s3_B s3_L (by decide +kernel)
theorem s7_S9 : SliceN true s7_R s7_T (0x5050505050505050505050505050505,4,[1, 3, 4]) := mkSlice (w:=0) s7_B s3_B s3_L (by decide +kernel)
theorem s7_S10 : SliceN true s7_R s7_T (0x1010101010101010101010101010101,1,[3, 4]) := mkSlice (w:=0) s7_B s1_B s1_L (by decide +kernel)
theorem s7_S11 : SliceN true s7_R s7_T (0xf000f000f000f000f000f000f000f,4,[0, 1, 4]) := mkSlice (w:=0) s7_B s3_B s3_L (by decide +kernel)
theorem s7_S12 : SliceN true s7_R s7_T (0xf0f00000f0f00000f0f00000f0f,4,[0, 1, 3]) := mkSlice (w:=0) s7_B s3_B s3_L (by decide +kernel)
theorem s7_S13 : SliceN true s7_R s7_T (0xff000000ff000000ff000000ff,4,[0, 1, 2]) := mkSlice (w:=0) s7_B s3_B s3_L (by decide +kernel)
theorem s7_S14 : SliceN true s7_R s7_T (0x550055005500550055005500550055,4,[1, 2, 4]) := mkSlice (w:=0) s7_B s3_B s3_L (by decide +kernel)
theorem s7_S15 : SliceN true s7_R s7_T (0x33003300330033003300330033003300,2,[0, 2, 4]) := mkSlice (w:=8) s7_B s4_B s4_L (by decide +kernel)
theorem s7_S16 : SliceN true s7_R s7_T (0xffff0000ffff0000ffff0000ffff0000,3,[0, 1, 2, 3]) := mkSlice (w:=16) s7_B s6_B s6_L (by decide +kernel)
theorem s7_S17 : SliceN true s7_R s7_T (0x11110000111100001111000011110000,1,[2, 3]) := mkSlice (w:=16) s7_B s2_B s2_L (by decide +kernel)
theorem s7_S18 : SliceN true s7_R s7_T (0x10101010101010101010101010101010,1,[3, 4]) := mkSlice (w:=4) s7_B s2_B s2_L (by decide +kernel)
theorem s7_S19 : SliceN true s7_R s7_T (0x11001100110011001100110011001100,1,[2, 4]) := mkSlice (w:=8) s7_B s2_B s2_L (by decide +kernel)
theorem s7_S20 : SliceN true s7_R s7_T (0x22222222222222222222222222222222,2,[2, 3, 4]) := mkSlice (w:=1) s7_B s4_B s4_L (by decide +kernel)
theorem s7_S21 : SliceN true s7_R s7_T (0x2222000022220000222200002222,1,[2, 3]) := mkSlice (w:=1) s7_B s2_B s2_L (by decide +kernel)
theorem s7_S22 : SliceN true s7_R s7_T (0xff000000ff000000ff000000ff0000,2,[0, 1, 2]) := mkSlice (w:=16) s7_B s4_B s4_L (by decide +kernel)
theorem s7_S23 : SliceN true s7_R s7_T (0x2020202020202020202020202020202,1,[3, 4]) := mkSlice (w:=1) s7_B s2_B s2_L (by decide +kernel)
theorem s7_S24 : SliceN true s7_R s7_T (0xcc000000cc000000cc000000cc,1,[0, 2]) := mkSlice (w:=2) s7_B s2_B s2_L (by decide +kernel)
theorem s7_S25 : SliceN true s7_R s7_T (0xcccccccccccccccccccccccccccccccc,3,[0, 2, 3, 4]) := mkSlice (w:=2) s7_B s6_B s6_L (by decide +kernel)
theorem s7_S26 : SliceN true s7_R s7_T (0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,2,[1, 3, 4]) := mkSlice (w:=1) s7_B s4_B s4_L (by decide +kernel)
theorem s7_S27 : SliceN true s7_R s7_T (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2,[0, 3, 4]) := mkSlice (w:=2) s7_B s4_B s4_L (by decide +kernel)
theorem s7_S28 : SliceN true s7_R s7_T (0xa0a00000a0a00000a0a00000a0a,1,[1, 3]) := mkSlice (w:=1) s7_B s2_B s2_L (by decide +kernel)
theorem s7_S29 : SliceN true s7_R s7_T (0xcccc0000cccc0000cccc0000cccc,2,[0, 2, 3]) := mkSlice (w:=2) s7_B s4_B s4_L (by decide +kernel)
theorem s7_S30 : SliceN true s7_R s7_T (0x330033003300330033003300330033,4,[0, 2, 4]) := mkSlice (w:=0) s7_B s3_B s3_L (by decide +kernel)
theorem s7_S31 : SliceN true s7_R s7_T (0x30003000300030003000300030003,1,[0, 4]) := mkSlice (w:=0) s7_B s1_B s1_L (by decide +kernel)
theorem s7_S32 : SliceN true s7_R s7_T (0x44444444444444444444444444444444,2,[2, 3, 4]) := mkSlice (w:=2) s7_B s4_B s4_L (by decide +kernel)
theorem s7_S33 : SliceN true s7_R s7_T (0xaa00aa00aa00aa00aa00aa00aa00aa,2,[1, 2, 4]) := mkSlice (w:=1) s7_B s4_B s4_L (by decide +kernel)
theorem s7_S34 : SliceN true s7_R s7_T (0xf0f00000f0f00000f0f00000f0f0,2,[0, 1, 3]) := mkSlice (w:=4) s7_B s4_B s4_L (by decide +kernel)
theorem s7_S35 : SliceN true s7_R s7_T (0xff00ff00ff00ff00ff00ff00ff00ff00,3,[0, 1, 2, 4]) := mkSlice (w:=8) s7_B s6_B s6_L (by decide +kernel)
theorem s7_S36 : SliceN true s7_R s7_T (0x30303030303030303030303030303030,2,[0, 3, 4]) := mkSlice (w:=4) s7_B s4_B s4_L (by decide +kernel)
theorem s7_S37 : SliceN true s7_R s7_T (0x33330000333300003333000033330000,2,[0, 2, 3]) := mkSlice (w:=16) s7_B s4_B s4_L (by decide +kernel)
theorem s7_S38 : SliceN true s7_R s7_T (0x50505050505050505050505050505050,2,[1, 3, 4]) := mkSlice (w:=4) s7_B s4_B s4_L (by decide +kernel)
theorem s7_S39 : SliceN true s7_R s7_T (0x55005500550055005500550055005500,2,[1, 2, 4]) := mkSlice (w:=8) s7_B s4_B s4_L (by decide +kernel)
theorem s7_S40 : SliceN true s7_R s7_T (0x55550000555500005555000055550000,2,[1, 2, 3]) := mkSlice (w:=16) s7_B s4_B s4_L (by decide +kernel)
theorem s7_S41 : SliceN true s7_R s7_T (0xaa000000aa000000aa000000aa,1,[1, 2]) := mkSlice (w:=1) s7_B s2_B s2_L (by decide +kernel)
theorem s7_S42 : SliceN true s7_R s7_T (0xc0c00000c0c00000c0c00000c0c,1,[0, 3]) := mkSlice (w:=2) s7_B s2_B s2_L (by decide +kernel)
theorem s7_S43 : SliceN true s7_R s7_T (0xf0f00000f0f00000f0f00000f0f0000,2,[0, 1, 3]) := mkSlice (w:=16) s7_B s4_B s4_L (by decide +kernel)
theorem s7_S44 : SliceN true s7_R s7_T (0xf0000000f0000000f0000000f0000,1,[0, 1]) := mkSlice (w:=16) s7_B s2_B s2_L (by decide +kernel)
theorem s7_S45 : SliceN true s7_R s7_T (0x440044004400440044004400440044,1,[2, 4]) := mkSlice (w:=2) s7_B s2_B s2_L (by decide +kernel)
theorem s7_S46 : SliceN true s7_R s7_T (0x3030000030300000303000003030000,1,[0, 3]) := mkSlice (w:=16) s7_B s2_B s2_L (by decide +kernel)
theorem s7_S47 : SliceN true s7_R s7_T (0x500050005000500050005000500050,1,[1, 4]) := mkSlice (w:=4) s7_B s2_B s2_L (by decide +kernel)
theorem s7_S48 : SliceN true s7_R s7_T (0xf0000000f0000000f0000000f00,1,[0, 1]) := mkSlice (w:=8) s7_B s2_B s2_L (by decide +kernel)
theorem s7_S49 : SliceN true s7_R s7_T (0xf0000000f0000000f0000000f0,1,[0, 1]) := mkSlice (w:=4) s7_B s2_B s2_L (by decide +kernel)
theorem s7_S50 : SliceN true s7_R s7_T (0x300030003000300030003000300030,1,[0, 4]) := mkSlice (w:=4) s7_B s2_B s2_L (by decide +kernel)
theorem s7_S51 : SliceN true s7_R s7_T (0x220022002200220022002200220022,1,[2, 4]) := mkSlice (w:=1) s7_B s2_B s2_L (by decide +kernel)
theorem s7_S52 : SliceN true s7_R s7_T (0x5000500050005000500050005000500,1,[1, 4]) := mkSlice (w:=8) s7_B s2_B s2_L (by decide +kernel)
theorem s7_S53 : SliceN true s7_R s7_T (0x4040404040404040404040404040404,1,[3, 4]) := mkSlice (w:=2) s7_B s2_B s2_L (by decide +kernel)
theorem s7_S54 : SliceN true s7_R s7_T (0xa000a000a000a000a000a000a000a,1,[1, 4]) := mkSlice (w:=1) s7_B s2_B s2_L (by decide +kernel)
theorem s7_S55 : SliceN true s7_R s7_T (0x3300000033000000330000003300,1,[0, 2]) := mkSlice (w:=8) s7_B s2_B s2_L (by decide +kernel)
theorem s7_S56 : SliceN true s7_R s7_T (0x550000005500000055000000550000,1,[1, 2]) := mkSlice (w:=16) s7_B s2_B s2_L (by decide +kernel)
theorem s7_S57 : SliceN true s7_R s7_T (0x5050000050500000505000005050,1,[1, 3]) := mkSlice (w:=4) s7_B s2_B s2_L (by decide +kernel)
theorem s7_S58 : SliceN true s7_R s7_T (0x3030000030300000303000003030,1,[0, 3]) := mkSlice (w:=4) s7_B s2_B s2_L (by decide +kernel)
theorem s7_S59 : SliceN true s7_R s7_T (0x5050000050500000505000005050000,1,[1, 3]) := mkSlice (w:=16) s7_B s2_B s2_L (by decide +kernel)
theorem s7_S60 : SliceN true s7_R s7_T (0x50005000500050005000500050005,1,[1, 4]) := mkSlice (w:=0) s7_B s1_B s1_L (by decide +kernel)
theorem s7_S61 : SliceN true s7_R s7_T (0x110011001100110011001100110011,1,[2, 4]) := mkSlice (w:=0) s7_B s1_B s1_L (by decide +kernel)
theorem s7_S62 : SliceN true s7_R s7_T (0x3000300030003000300030003000300,1,[0, 4]) := mkSlice (w:=8) s7_B s2_B s2_L (by decide +kernel)
theorem s7_S63 : SliceN true s7_R s7_T (0xc000c000c000c000c000c000c000c,1,[0, 4]) := mkSlice (w:=2) s7_B s2_B s2_L (by decide +kernel)
def s7_Z : List SliceD := [(0x55555555555555555555555555555555,7,[1, 2, 3, 4]),(0x33333333333333333333333333333333,7,[0, 2, 3, 4]),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f,7,[0, 1, 3, 4]),(0xff00ff00ff00ff00ff00ff00ff00ff,7,[0, 1, 2, 4]),(0xffff0000ffff0000ffff0000ffff,7,[0, 1, 2, 3]),(0x11111111111111111111111111111111,4,[2, 3, 4]),(0x3333000033330000333300003333,4,[0, 2, 3]),(0x5555000055550000555500005555,4,[1, 2, 3]),(0x3030303030303030303030303030303,4,[0, 3, 4]),(0x5050505050505050505050505050505,4,[1, 3, 4]),(0x1010101010101010101010101010101,1,[3, 4]),(0xf000f000f000f000f000f000f000f,4,[0, 1, 4]),(0xf0f00000f0f00000f0f00000f0f,4,[0, 1, 3]),(0xff000000ff000000ff000000ff,4,[0, 1, 2]),(0x550055005500550055005500550055,4,[1, 2, 4]),(0x33003300330033003300330033003300,2,[0, 2, 4]),(0xffff0000ffff0000ffff0000ffff0000,3,[0, 1, 2, 3]),(0x11110000111100001111000011110000,1,[2, 3]),(0x10101010101010101010101010101010,1,[3, 4]),(0x11001100110011001100110011001100,1,[2, 4]),(0x22222222222222222222222222222222,2,[2, 3, 4]),(0x2222000022220000222200002222,1,[2, 3]),(0xff000000ff000000ff000000ff0000,2,[0, 1, 2]),(0x2020202020202020202020202020202,1,[3, 4]),(0xcc000000cc000000cc000000cc,1,[0, 2]),(0xcccccccccccccccccccccccccccccccc,3,[0, 2, 3, 4]),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,2,[1, 3, 4]),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2,[0, 3, 4]),(0xa0a00000a0a00000a0a00000a0a,1,[1, 3]),(0xcccc0000cccc0000cccc0000cccc,2,[0, 2, 3]),(0x330033003300330033003300330033,4,[0, 2, 4]),(0x30003000300030003000300030003,1,[0, 4]),(0x44444444444444444444444444444444,2,[2, 3, 4]),(0xaa00aa00aa00aa00aa00aa00aa00aa,2,[1, 2, 4]),(0xf0f00000f0f00000f0f00000f0f0,2,[0, 1, 3]),(0xff00ff00ff00ff00ff00ff00ff00ff00,3,[0, 1, 2, 4]),(0x30303030303030303030303030303030,2,[0, 3, 4]),(0x33330000333300003333000033330000,2,[0, 2, 3]),(0x50505050505050505050505050505050,2,[1, 3, 4]),(0x55005500550055005500550055005500,2,[1, 2, 4]),(0x55550000555500005555000055550000,2,[1, 2, 3]),(0xaa000000aa000000aa000000aa,1,[1, 2]),(0xc0c00000c0c00000c0c00000c0c,1,[0, 3]),(0xf0f00000f0f00000f0f00000f0f0000,2,[0, 1, 3]),(0xf0000000f0000000f0000000f0000,1,[0, 1]),(0x440044004400440044004400440044,1,[2, 4]),(0x3030000030300000303000003030000,1,[0, 3]),(0x500050005000500050005000500050,1,[1, 4]),(0xf0000000f0000000f0000000f00,1,[0, 1]),(0xf0000000f0000000f0000000f0,1,[0, 1]),(0x300030003000300030003000300030,1,[0, 4]),(0x220022002200220022002200220022,1,[2, 4]),(0x5000500050005000500050005000500,1,[1, 4]),(0x4040404040404040404040404040404,1,[3, 4]),(0xa000a000a000a000a000a000a000a,1,[1, 4]),(0x3300000033000000330000003300,1,[0, 2]),(0x550000005500000055000000550000,1,[1, 2]),(0x5050000050500000505000005050,1,[1, 3]),(0x3030000030300000303000003030,1,[0, 3]),(0x5050000050500000505000005050000,1,[1, 3]),(0x50005000500050005000500050005,1,[1, 4]),(0x110011001100110011001100110011,1,[2, 4]),(0x3000300030003000300030003000300,1,[0, 4]),(0xc000c000c000c000c000c000c000c,1,[0, 4])]
theorem s7_Y : ∀ s ∈ s7_Z, SliceN true s7_R s7_T s := by
  unfold s7_Z
  simp only [List.forall_mem_cons]
  exact ⟨s7_S0,s7_S1,s7_S2,s7_S3,s7_S4,s7_S5,s7_S6,s7_S7,s7_S8,s7_S9,s7_S10,s7_S11,s7_S12,s7_S13,s7_S14,s7_S15,s7_S16,s7_S17,s7_S18,s7_S19,s7_S20,s7_S21,s7_S22,s7_S23,s7_S24,s7_S25,s7_S26,s7_S27,s7_S28,s7_S29,s7_S30,s7_S31,s7_S32,s7_S33,s7_S34,s7_S35,s7_S36,s7_S37,s7_S38,s7_S39,s7_S40,s7_S41,s7_S42,s7_S43,s7_S44,s7_S45,s7_S46,s7_S47,s7_S48,s7_S49,s7_S50,s7_S51,s7_S52,s7_S53,s7_S54,s7_S55,s7_S56,s7_S57,s7_S58,s7_S59,s7_S60,s7_S61,s7_S62,s7_S63,by simp⟩
def s7_C : List (Nat × List (Nat × Nat × Nat)) := [(0,[]),(1,[]),(2,[]),(3,[]),(4,[]),(2,[(1,0,1)]),(3,[(1,0,1)]),(4,[(1,0,1)]),(5,[]),(0,[(1,0,3)]),(1,[(1,0,3)]),(2,[(1,0,3),(1,1,3)]),(3,[(1,0,3),(1,1,3)]),(6,[]),(7,[]),(0,[(1,0,1)]),(1,[(1,0,1)]),(8,[]),(3,[(1,0,1),(1,2,4)]),(4,[(1,0,1),(1,2,4)]),(9,[]),(10,[]),(0,[(2,0,3)]),(4,[(3,0,1)]),(1,[(2,0,3)]),(0,[(1,1,2)]),(1,[(1,1,2)]),(11,[(1,0,1)]),(5,[(1,0,1)]),(11,[]),(4,[(1,2,3)]),(0,[(1,1,2),(1,1,3),(1,2,3)]),(1,[(1,1,2),(1,1,3),(1,2,3)]),(12,[]),(13,[]),(0,[(1,0,3),(1,2,3)]),(1,[(1,0,2),(1,2,3)]),(2,[(1,0,2),(1,1,3),(1,2,3)]),(3,[(1,1,3)]),(6,[(1,0,2)]),(14,[(1,0,2)]),(15,[]),(14,[]),(1,[(1,2,3),(1,0,4)]),(16,[]),(0,[(1,1,3),(1,2,3)]),(1,[(1,1,3),(1,2,3)]),(2,[(1,0,1),(1,2,3)]),(3,[(1,0,1),(1,2,3)]),(17,[]),(5,[(1,1,2)]),(5,[(1,0,2)]),(0,[(1,2,3),(3,1,3)]),(18,[]),(19,[]),(0,[(1,1,3),(3,2,3)]),(0,[(1,0,3),(1,1,3)]),(1,[(1,0,3),(1,1,4)]),(4,[(1,0,2)]),(20,[]),(4,[(3,0,2)]),(0,[(1,0,3),(1,1,4)]),(0,[(1,1,3),(1,0,4)]),(21,[]),(1,[(1,0,3),(1,1,3)]),(9,[(1,0,2)]),(22,[]),(23,[]),(4,[(1,1,2)]),(11,[(1,1,2)]),(0,[(1,0,1),(2,0,3)]),(4,[(1,1,2),(1,0,4)]),(2,[(0,1,3)]),(0,[(1,0,1),(1,0,3)]),(12,[(1,0,1)]),(8,[(2,0,2)]),(4,[(1,0,1),(1,1,2)]),(24,[]),(0,[(1,0,1),(1,0,2)]),(2,[(1,0,1),(1,2,4)]),(1,[(1,0,1),(1,0,2)]),(1,[(1,0,2),(3,0,1)]),(1,[(1,0,1),(3,0,2)]),(0,[(1,0,2),(3,0,1)]),(0,[(1,0,1),(3,0,2)]),(25,[]),(0,[(1,0,2),(2,0,1)]),(0,[(1,0,1),(2,0,2)]),(2,[(1,0,1),(1,3,4)]),(26,[]),(1,[(1,1,3),(3,0,3)]),(27,[]),(0,[(1,1,3),(3,0,3)]),(0,[(1,0,3),(3,1,3)]),(3,[(1,0,1),(1,3,4)]),(28,[]),(8,[(1,0,1)]),(1,[(1,0,1),(1,2,4)]),(9,[(1,0,1)]),(3,[(1,0,1),(3,2,4)]),(5,[(2,0,1)]),(5,[(2,0,2)]),(1,[(1,0,1),(3,3,4)]),(2,[(1,0,1),(3,3,4)]),(9,[(2,0,2)]),(29,[]),(2,[(1,1,2),(2,0,4)]),(2,[(1,1,2),(0,0,1)]),(2,[(1,1,2),(3,0,1)]),(30,[]),(1,[(1,1,2),(0,0,4)]),(2,[(1,1,2),(0,0,4)]),(3,[(1,1,2),(0,0,4)]),(31,[]),(9,[(3,0,1)]),(32,[]),(5,[(3,0,1)]),(9,[(2,0,1)]),(0,[(1,0,1),(1,2,4)]),(0,[(1,0,1),(3,2,4)]),(33,[]),(3,[(1,0,2),(1,1,4)]),(2,[(1,0,2),(1,1,4)]),(0,[(1,0,2),(1,1,4)]),(0,[(1,1,2),(1,0,4)]),(0,[(1,0,1),(1,3,4)]),(0,[(1,0,1),(3,3,4)]),(4,[(1,0,2),(1,1,4)]),(34,[]),(4,[(1,2,3),(0,0,4)]),(9,[(1,1,2)]),(2,[(1,2,3),(2,0,4)]),(3,[(1,2,3),(2,0,4)]),(35,[]),(4,[(1,2,3),(2,0,4)]),(13,[(2,0,2)]),(9,[(3,1,2)]),(9,[(2,1,2)]),(4,[(1,2,3),(2,0,1)]),(4,[(1,2,3),(3,0,1)]),(2,[(1,2,3)]),(3,[(1,2,3)]),(2,[(0,0,1),(1,2,3)]),(36,[]),(3,[(0,0,1),(1,2,3)]),(37,[]),(4,[(0,0,1),(1,2,3)]),(38,[]),(39,[]),(40,[]),(3,[(0,0,1),(3,2,3)]),(4,[(0,0,1),(2,2,3)]),(3,[(0,0,1),(2,2,3)]),(3,[(1,0,1),(3,2,3)]),(2,[(1,0,1),(3,2,3)]),(3,[(1,0,1),(2,2,3)]),(3,[(1,1,2),(0,0,3)]),(3,[(1,1,2),(1,0,3)]),(1,[(2,0,3),(1,1,2)]),(2,[(2,0,3),(1,1,2)]),(3,[(2,0,3),(1,1,2)]),(3,[(2,0,3),(3,1,2)]),(3,[(2,0,3),(2,1,2)]),(2,[(2,0,3),(2,1,2)]),(0,[(0,1,2)]),(4,[(0,2,3),(1,0,1)]),(4,[(0,2,3),(3,0,1)]),(5,[(0,0,1)]),(0,[(0,1,2),(1,0,3)]),(0,[(2,0,3),(0,1,2)]),(41,[]),(42,[]),(0,[(2,0,3),(2,1,2)]),(0,[(2,0,3),(3,1,2)]),(43,[]),(4,[(1,2,3),(1,0,1)]),(0,[(1,1,2),(1,0,3)]),(0,[(2,0,3),(1,1,2)]),(44,[]),(45,[]),(46,[]),(47,[]),(0,[(1,2,3)]),(1,[(1,2,3)]),(0,[(1,2,3),(2,0,4)]),(1,[(1,2,3),(2,0,4)]),(5,[(3,1,2)]),(5,[(2,1,2)]),(5,[(1,0,2),(1,1,2)]),(5,[(1,0,1),(1,1,2)]),(5,[(1,0,1),(1,0,2)]),(0,[(1,2,3),(1,1,4)]),(0,[(1,1,3),(1,2,4)]),(0,[(1,1,2),(1,3,4)]),(3,[(1,0,2),(1,3,4)]),(48,[]),(49,[]),(0,[(1,1,2),(1,2,3),(1,1,5)]),(0,[(1,1,2),(1,2,3),(2,3,4)]),(0,[(1,1,2),(1,1,3),(1,2,5)]),(0,[(1,1,2),(1,1,3),(2,3,4)]),(15,[(1,1,2)]),(4,[(1,0,3),(1,2,4)]),(11,[(1,0,2)]),(16,[(1,2,3)]),(3,[(1,0,3),(1,2,4)]),(12,[(1,0,2)]),(39,[(1,1,2)]),(0,[(1,1,3),(1,1,2),(1,2,4)]),(0,[(1,1,3),(1,1,2),(2,3,5)]),(0,[(1,1,2),(1,1,3),(2,2,5)]),(4,[(1,1,3),(1,0,3),(1,0,4)]),(3,[(0,0,3)]),(3,[(0,1,3)]),(0,[(1,0,2),(1,0,3)]),(14,[(2,0,2)]),(4,[(1,0,1),(1,0,3),(1,1,3)]),(8,[(1,1,2)]),(0,[(1,0,2),(1,1,3),(1,2,3)]),(30,[(1,1,2)]),(0,[(1,0,1),(1,1,3),(1,2,3)]),(0,[(1,0,1),(1,0,2),(1,2,3)]),(0,[(1,0,1),(1,0,2),(1,1,3)]),(4,[(1,1,3),(1,2,4)]),(4,[(1,1,2),(1,3,4)]),(4,[(1,1,3),(2,2,4)]),(4,[(1,1,2),(2,3,4)]),(4,[(1,1,3),(1,1,2)]),(1,[(1,1,3),(1,2,4)]),(16,[(1,1,2)]),(3,[(1,1,2),(1,2,3)]),(1,[(1,0,1),(1,1,3),(1,2,3)]),(3,[(1,2,3),(3,0,2)]),(50,[]),(51,[]),(52,[]),(0,[(1,1,3),(1,2,3),(3,0,2)]),(53,[]),(2,[(1,0,3),(1,2,4)]),(1,[(1,0,1),(1,3,4),(1,2,3)]),(54,[]),(1,[(1,0,1),(1,1,2),(1,2,3)]),(3,[(1,0,2)]),(1,[(1,0,2),(1,1,3),(1,2,3)]),(1,[(1,1,3),(1,2,3),(3,0,2)]),(0,[(1,2,3),(1,0,1),(1,3,5)]),(2,[(1,0,2),(1,2,3),(3,1,3)]),(1,[(1,0,2),(1,2,3),(3,1,3)]),(0,[(1,0,2),(1,1,2)]),(0,[(1,0,2),(1,1,2),(1,0,3)]),(0,[(2,0,3),(1,0,2),(3,1,2)]),(4,[(1,0,1),(1,1,3),(1,2,3)]),(2,[(1,1,3),(1,2,3),(3,0,2)]),(55,[]),(56,[]),(4,[(1,0,3),(3,2,3)]),(14,[(1,1,2)]),(2,[(1,1,2)]),(4,[(1,0,2),(1,1,3),(1,1,4)]),(2,[(1,1,2),(0,0,3)]),(4,[(1,0,2),(1,1,3),(1,0,5)]),(3,[(1,0,2),(0,1,3)]),(30,[(2,0,2)]),(3,[(1,0,3),(1,1,2),(1,3,5)]),(0,[(1,1,3)]),(3,[(1,0,2),(1,2,3)]),(1,[(1,0,2),(1,0,3),(1,2,3)]),(20,[(1,1,2)]),(4,[(1,1,3),(3,0,3)]),(4,[(1,0,3),(1,1,3)]),(4,[(1,0,3),(3,1,3)]),(7,[(1,0,2)]),(3,[(1,1,2),(3,0,1)]),(3,[(1,1,2),(2,0,4)]),(0,[(1,0,1),(1,1,3)]),(4,[(1,0,1),(1,2,3)]),(4,[(1,0,1),(3,2,3)]),(4,[(1,0,1),(2,2,3)]),(3,[(1,1,2),(2,0,3)]),(3,[(2,2,3)]),(3,[(0,2,3)]),(4,[(1,2,3),(1,0,1),(1,2,5)]),(57,[]),(58,[]),(4,[(1,0,2),(1,1,2),(1,0,5)]),(8,[(0,0,2)]),(0,[(2,0,3),(1,0,1)]),(0,[(2,0,3),(2,0,1)]),(8,[(1,0,2)]),(0,[(2,1,2),(0,0,3)]),(0,[(2,1,2),(1,0,3)]),(59,[]),(0,[(1,0,2),(1,0,3),(1,2,3)]),(30,[(1,0,2)]),(0,[(1,0,3),(1,2,3),(3,0,2)]),(0,[(1,0,2),(1,2,3),(3,0,3)]),(0,[(1,0,2),(1,0,3),(1,2,5)]),(0,[(1,0,3),(2,1,4)]),(4,[(1,0,1),(3,2,4)]),(0,[(1,0,3),(1,0,1),(3,3,5)]),(8,[(3,0,1)]),(3,[(0,0,1),(1,0,1),(3,2,5)]),(8,[(2,0,1)]),(3,[(0,0,1),(1,0,1),(1,2,5)]),(4,[(0,0,1),(1,0,1)]),(3,[(1,0,3)]),(0,[(0,0,3)]),(0,[(2,2,3)]),(30,[(1,0,1)]),(30,[(2,0,1)]),(14,[(2,0,1)]),(0,[(1,0,1),(0,0,3)]),(0,[(1,0,1),(2,1,3)]),(9,[(0,0,2)]),(0,[(1,0,1),(2,2,3)]),(14,[(1,0,1)]),(0,[(2,1,3)]),(60,[]),(61,[]),(14,[(0,0,2)]),(14,[(3,0,1)]),(14,[(3,1,2)]),(14,[(2,1,2)]),(0,[(0,2,3)]),(0,[(0,2,3),(2,0,3)]),(9,[(0,1,2)]),(0,[(0,2,3),(0,0,3)]),(7,[(1,0,1)]),(9,[(3,0,2)]),(0,[(1,1,3),(0,2,3)]),(0,[(0,1,3)]),(0,[(0,1,2),(1,1,2)]),(0,[(0,1,2),(1,1,2),(2,0,3)]),(0,[(0,1,2),(1,1,2),(0,0,3)]),(0,[(0,1,2),(1,1,2),(1,0,3)]),(7,[(1,1,2)]),(0,[(2,0,3),(0,1,3)]),(0,[(2,0,3),(1,1,2),(3,3,5)]),(62,[]),(0,[(1,2,3),(0,2,3)]),(0,[(0,2,3),(1,2,3)]),(0,[(0,2,3),(1,2,3),(2,0,5)]),(0,[(0,2,3),(1,2,3),(0,0,5)]),(5,[(0,1,2),(1,1,2)]),(63,[]),(0,[(1,1,2),(1,1,3)]),(5,[(1,1,2),(1,0,3)]),(40,[(1,1,2)]),(32,[(1,0,1)]),(40,[(1,0,2)]),(0,[(2,1,2),(2,0,3)]),(0,[(2,1,2),(1,0,1)]),(0,[(2,1,2),(1,0,1),(1,0,3)]),(0,[(2,0,3),(1,0,1),(1,1,2)]),(0,[(1,1,2),(1,0,2)]),(0,[(1,0,2),(1,1,3),(1,2,5)]),(0,[(1,1,3),(1,2,3),(0,0,1)]),(0,[(1,1,3),(1,2,3),(2,0,1)]),(9,[(2,1,2),(1,0,1)]),(9,[(2,1,2),(2,0,2)]),(5,[(0,1,2)]),(0,[(1,0,1),(1,0,2),(1,0,3)]),(9,[(1,0,1),(1,1,2)]),(30,[(2,1,2)]),(0,[(2,0,3),(1,0,1),(2,1,2)]),(11,[(3,0,2)]),(30,[(3,0,2)]),(14,[(3,0,2)]),(11,[(0,0,1),(1,0,1)]),(11,[(2,0,2)]),(11,[(2,1,2)]),(0,[(0,0,1),(1,0,1)]),(11,[(0,1,2)]),(0,[(0,0,1),(1,0,1),(1,3,5)]),(14,[(0,0,1)]),(11,[(3,1,2)]),(30,[(3,1,2)]),(12,[(3,0,1)]),(12,[(2,0,1)]),(7,[(2,0,1)]),(11,[(2,0,1)]),(11,[(3,0,1)]),(11,[(0,0,1)]),(7,[(3,1,2)]),(7,[(2,1,2)]),(0,[(1,1,2),(2,0,3)]),(11,[(0,0,2)]),(7,[(2,0,2)]),(11,[(1,0,2),(1,1,2)]),(9,[(1,0,1),(3,2,3)]),(0,[(2,0,3),(1,0,2),(2,1,3)]),(30,[(2,0,2),(1,0,1)]),(0,[(2,0,3),(1,0,2),(0,1,3)])]
def s7_t : Tabs := (s7_C.map (mkCut true s7_Z),[(5,4),(3,2),(3,1),(5,1),(9,8),(9,1),(17,16),(17,1),(6,4),(6,2),(10,8),(10,2),(18,16),(18,2),(12,8),(12,4),(20,16),(20,4),(24,16),(24,8),(10,16),(18,4),(24,0),(17,0),(19,2),(5,8),(19,8),(22,8),(17,4),(9,2),(20,8),(20,0),(7,4),(18,0),(19,1),(21,1),(25,1),(3,0),(12,0),(21,4),(22,4),(14,16),(7,1),(14,8)],[],[[],[1],[2,1],[3,2,1],[0,1],[0,2,1],[0,3,2,1],[1,0,2,1],[1,0,3,2,1],[2,1,0,3,2,1],[0,1,2,3],[0,1,2,1,3],[0,1,2,3,2,1],[1,2,3],[1,2,1,3],[1,2,3,2,1],[2,3],[2],[3],[3,2],[0,1,0,2],[0,1,2,1,0],[1,0,2],[1,2,1,0],[0],[2,3,2,1],[0,2,3,2,1],[0,2],[2,3,2],[0,1,2,1,0,3],[0,1,2,3,2,1,0],[1,2,1,0,3],[1,2,3,2,1,0],[2,1,0,3],[2,3,2,1,0],[2,1,0],[3,2,1,0],[2,1,0,3,2,1,0],[1,0],[1,0,3],[0,2,1,3,2],[0,1,3,2],[0,1,0,2,1,3],[2,1,3,2],[1,3,2],[1,0,2,1,3],[1,0,2,1,3,2],[0,1,0,2,3,2,1],[0,1,2,1,0,3,2,1],[0,3,2],[0,3],[1,0,2,3,2,1],[0,2,3],[1,2,1,0,3,2,1],[0,1,0,3],[0,1,2,3,2],[0,1,2],[2,1,3],[0,2,1,3],[0,1,3],[0,1,2,1],[1,3],[1,2,1],[1,2],[1,2,3,2],[0,1,0,2,1,3,2],[1,2,1,3,2],[1,3,2,1],[0,1,0,3,2,1],[0,1,3,2,1],[1,0,2,1,0,3,2,1],[1,0,2,1,3,2,1],[1,0,2,1,0]])
theorem s7_W : TabsP true s7_R s7_T s7_t := ⟨cutsGood s7_Y (by decide +kernel),by decide +kernel,by decide +kernel,by decide +kernel⟩
noncomputable def s7_D9 : List StD := [
([sw0,sw1,sw2,sw3,sw12],[[0,1,10000,30000,10001,10002],[0,10001,30001,10000,10003,2],[0,10000,30002,10004,10005,3],[0,10000,30003,10006,10007,4],[1,10002,30004,10008,10009,2],[1,10002,30005,10010,10011,3],[1,10002,30006,10012,10013,4],[2,10003,30007,10014,10015,3],[2,10003,30008,10016,10017,4],[3,10005,30009,10018,10019,4]])]
noncomputable def s7_D8 : List StD := [
([sw0,sw1,sw4,sw2,sw3,sw12],[[0,1],[0,1],[0,30010,10003,5],[0,30011,10005,6],[0,30012,10007,7],[0],[1,30013,10009,5],[1,30014,10011,6],[1,30015,10013,7],[5,8,2,30000,10003,30016,10014],[6,8,3,30017,10005,30018,10015],[7,8,4,30019,10007,30000,10017],[5,10003,30000,10014,10015,6],[5,10003,30018,10016,10017,7],[6,10005,30016,10018,10019,7]])]
noncomputable def s7_D7 : List StD := [
([sw0,sw1,sw2,sw3,sw13,sw14],[[9,10,30007],[9,30020,10003,11],[9,30021,10005,12],[9,4],[9,10,13,10007],[10,30022,10009,11],[10,30023,10011,12],[10,9,14,10013],[10,4],[11,10003,30007,10014,10015,12],[11,10009,30000,10003,30024,14,30025],[11,10003,30024,10009,30000,13,30026],[12,10011,30017,10005,30027,14,30003],[12,10005,30027,10011,30017,13,30006],[9,10]]),
([sw0,sw1,sw4,sw2,sw7,sw3,sw12],[[15,16],[16],[15,16,5],[17],[15,30011,10005,18],[15,30012,10007,19],[15],[16,15,5],[20],[16,30014,10011,18],[16,30015,10013,19],[5,8],[5],[18,8,30000,10005],[19,8,30018,10007],[8],[5,30016,10015,18],[5,30028,10017,19],[18,21,6,30000,10005,30018,10018],[19,21,7,30018,10007,30000,10019],[10005,18,10018,10019]]),
([sw0,sw1,sw2,sw7,sw3,sw12],[[15,5,16],[15,5,16],[15,17],[15,30029,10005,10001],[15,30030,10007,10001],[5,15,16],[16,20],[16,30031,10011,10002],[16,30032,10013,10002],[5,8],[5,30033,10015,10003],[5,30034,10017,10003],[30035,3,10018,30000,10005,30018,30009],[30036,4,10019,30018,10007,30000,30037],[30009,10005,10007,10018,10019,30035,30036]]),
([sw15,sw0,sw1,sw2,sw3,sw12],[[22,7,8,23],[22,7],[8,30038,10003,2],[8,30035,10005,3],[7,8,9],[22,7,8,24],[22,30024,10003,10001],[22,30027,10005,10001],[22,7,10006],[8,30000,10009,10002],[8,30017,10011,10002],[7,8,10012],[30000,10003,10005,10014,10015,30039,30033],[7,10017,10019],[7,10019,10017]]),
([sw0,sw1,sw4,sw2,sw3,sw10,sw12],[[25,26],[26],[25,5,30040],[25,6,30041],[25,30042,30010,27,10001],[25,30042,10007,10001],[25],[26,5,30043],[26,6,30044],[26,30045,30013,27,10002],[26,30045,10013,10002],[5,30016,30033,28,10014],[6,30018,30039,28,10015],[27,28,8,30007,30000,30019,30046,29],[30,28,30007,10007,30000,10017],[5,6],[6],[5,30016,10017,10014],[5],[6,30018,10019,10015],[7,27,30000,10017,30007,10007]])]
noncomputable def s7_D6 : List StD := [
([sw0,sw1,sw10,sw16,sw17],[[31,32,10000,30000,10001,10002],[31,10001,30000,10000,30019,29,30042],[31,10001,30018,10000,30017,33,30047],[31,10000,30016,10004,30000,34,30048],[32,10002,30024,10008,30049,29,30045],[32,10002,30050,10008,30027,33,30051],[32,10002,30052,10010,30024,34,30053],[29,33,4,30,34],[29,34,4,30,33],[33,34,3,30,29]]),
([sw0,sw1,sw2,sw5,sw14,sw17],[[35,36,30038],[35,30054,10003,37],[38],[35,30055,30056,39,10004],[35,10004,34,10005],[36,30038,10009,37],[36,30013,30044,40,10020],[34],[36,38,34,10013],[10009,37,10003,30050,30057],[10003,37,10009,30000,30026],[10003,37,41,30000,10014,30009],[39,40,42,43,41,44,13],[35,39],[36,38]]),
([sw0,sw1,sw4,sw2,sw3,sw16,sw17],[[45,46],[46],[45,30058,47],[45,30059,48],[45,30060,10001],[45,30056,10001],[45],[46,30057,47],[46,30061,48],[46,30062,10002],[46,30063,10002],[47,30033,49],[48,30039,49],[50,30035,33],[51,30038,34],[47,30000,48],[52],[47,48,53],[48,47,54],[55],[47,48]]),
([sw0,sw1,sw2,sw3,sw13,sw14,sw18],[[56,30045,57],[56,58,11],[56,59],[58],[56,57,59],[60],[57,30043,11],[57,10011],[57,56,14],[58],[57,61,30064],[11,10015],[11,14],[11,62,63],[14],[10011,59],[10015,10011],[10011,59],[56,57],[11],[57,20]]),
([sw0,sw1,sw2,sw3,sw13,sw19],[[64,30063,30007,65,10008],[11,30017,30005,51,10009],[66,65,10011,30021,67,10005,30018],[68],[30018,65,0,66,67,57,30055,10007],[64,10008,65,11],[64,30023,10011,10008],[64,66,61,10008],[33],[11,30035,10015,10009],[11,66,62,10009],[13],[10011,69,67,30004,10005,30003],[10005,10007,10011,30000,30041],[61,17,67]]),
([sw15,sw0,sw2,sw9,sw3,sw12],[[15,70,24],[2,8,71],[70,72,8],[8,30035,10005,29],[73,8],[70,30000,30017,74,10001],[70,10001,75,10002],[70,30024,10005,10001],[70,76,10006],[24],[77,10005,30017,53,10015,30039],[76,53,10021,75,10019],[10002,10005,30000,53,10015,30024],[74,75,10002,76,53,10012],[10005,76,10019,10017]]),
([sw0,sw1,sw2,sw7,sw3,sw20,sw12],[[78,79,80],[78,80,79],[81],[78,80,18],[82],[78,59],[79,78,80],[83],[80,78,18],[84],[80,85],[86],[79,30019,18],[79,18,30016],[79,10017],[18,79,30018],[79,18],[10019,59],[87],[18,10019],[10017,59]]),
([sw0,sw1,sw4,sw2,sw3,sw21,sw16],[[56,64],[64],[56,30005,88],[56,89],[90],[56,89],[56],[64,30002,88],[64,91],[92],[64,91],[88,30017,51],[51,89],[90],[51,88,89],[88,53],[88,51,53],[93],[48,89,10015],[94,53,95],[88,51]]),
([sw0,sw1,sw4,sw2,sw3,sw22,sw12],[[30000,85,89],[96],[79,97,28],[28,89],[30010],[28,89],[98],[89,85,97],[97,85],[30013],[97,85],[79,85,28],[28,85],[29],[28,85],[89,28,18],[99],[89,53],[100],[18,54],[7,85,30000]]),
([sw23,sw0,sw1,sw4,sw2,sw3,sw12],[[0,19,17],[19,20],[19,17],[19,8],[6,95,21],[51],[30000,77,95],[75],[101,102,103],[21,95],[19,30004,21],[104],[95,77,101],[21,105],[19,30001,21],[101,19,77],[21,95],[19,30000,21],[95,10015],[19,49],[19,49]]),
([sw24,sw0,sw1,sw2,sw3,sw25,sw12],[[106],[107,29,108],[106,109],[29,17],[30010],[28,30056,30030],[98,30063,110],[28,30017,111],[28,30000,112],[30000,28,113],[28,10007],[28,112,98],[28,98,112],[114],[28,115],[98,28,112],[116],[98,53],[117],[112,54],[113,115]]),
([sw0,sw1,sw2,sw7,sw3,sw22,sw12],[[118,79,97],[118,97,79],[96],[118,89],[30010],[118,89],[79,118,97],[98],[97,85],[30013],[97,85],[28],[79,53],[30016],[79,53],[30035,30018,89],[3],[10019,89],[119],[95,10019,120],[30036,89,30000]]),
([sw0,sw1,sw2,sw3,sw22,sw12],[[96,98,10000,18,85,10001,89],[96,28,10001,10000,121,59],[10000,98,18,89,122,10004],[30010,10006],[10000,98,30030,89,10007,30000,10013],[98,28,122,85,118,10003],[18,85,123,96,10005],[30013,10012],[95,96,10007,30032,85,10013,30024],[18,122,124],[30016,122,10016],[122,30034,10017,10003],[30018,18,10018],[18,30036,10019,10005],[4,30036,30000,85,10007]]),
([sw23,sw0,sw1,sw2,sw7,sw3,sw12],[[15,17],[17,95,20],[17,8],[4],[21,95],[125],[126,95],[126,127,103],[75],[21,95],[21,30004,127],[95,126,102],[104],[21,105],[95,30001,21],[101],[95,128],[21,30000,127],[21,95],[21,30000,127],[95,10019,10022]]),
([sw23,sw0,sw1,sw2,sw3,sw12],[[0,44,17,105],[17,44,20,95],[17,44,8,105],[3,44,30035,105,10005,30000,10018],[30018,30000,10007],[75,104,10000,105,95,19,10001],[75,101,10001,10000,127,63],[10000,10018,30004,95,10005,30018],[105,104,10000,44,30000,10006,19],[95,101,10002,126,128,10003,105],[10002,10005,30001,105,10011,30050],[95,75,19,30024,10012],[10003,95,30000,128,10015,30039,10005],[105,75,19,30038,10016],[105,19,10019,30035,10018]]),
([sw26,sw0,sw1,sw2,sw3,sw12,sw27],[[129],[130,10002],[30016],[30018],[30000],[30013],[130,10002],[131,128],[130,41,132],[130,44,128],[130,128,30000],[130,128],[10002,133],[10002,44],[10002,128],[130,128],[130,132,134],[135],[128,130,132],[136],[137]]),
([sw28,sw0,sw1,sw2,sw3,sw12,sw27],[[138],[139],[140,30016,41],[130,30018,141],[138,30000,41],[130,30046],[30000,130,41],[142,143],[130,41,144],[130,145,146],[130,41,30065],[41,147,130],[143,148,144],[41,149,146],[8,147,30046],[130,41,143],[130,143],[150],[144,41],[151],[152]]),
([sw0,sw1,sw4,sw2,sw3,sw12,sw27],[[30000,10001,10002],[139],[10001,30040,54],[10001,30041,53],[10001,30056,54],[10001,30010,0],[138],[10002,30043,54],[10002,30044,53],[10002,30063,54],[10002,30013,8],[54,30016,140],[53,30018,141],[139,30000,54],[8,30000,30046],[48,54],[47,53],[153],[48,54],[154],[155]]),
([sw29,sw0,sw1,sw2,sw3,sw25,sw12],[[156],[98,30013,17],[17,30016,28],[156,30018,98],[98,30056,30030],[157],[98,30063,158],[28,30017,159],[98,30000,160],[98,30000,10006],[98,10006,10023],[98,160,28],[28,98,160],[161],[28,115],[98,28,160],[162],[98,53],[163],[160,54],[4,115,30000]]),
([sw0,sw30,sw1,sw2,sw3,sw12],[[17],[17,19,104,10001],[17,127,101,10000],[10001,104,30010,95,10005,30018,10011],[19,89,10007,104,10024],[17,19,104],[17,19,101],[3,21,30002,95,10005,30018,10018],[19,89,10007,21,10019],[17,10002,126,10003],[17,30001,10011,10002],[17,19,10012],[17,30000,10015,10003],[17,19,10016],[19,10019,10007]]),
([sw15,sw0,sw1,sw31,sw2,sw3,sw12],[[164,165,166],[165,164],[3,30007,8],[167,77],[3,95,167],[168],[169,165,95],[8,30024,77],[167,170],[167,95],[165,66],[8,30000,95],[167,77],[167,171],[165,66],[172],[173],[165,30000,104],[30000,95,77],[165,66],[165,174]]),
([sw15,sw0,sw1,sw2,sw3,sw10,sw12],[[25,175,139],[175,25],[28,30016,20],[28,30018,3],[28,30007,29],[176],[177,175,158],[28,30027,178],[28,30024,178],[28,30024,178],[175,178],[28,30017,178],[28,30000,178],[28,30000,178],[175,178],[30000,54,53],[173],[175,53,10019],[172],[175,54,10017],[175,54,30000]]),
([sw29,sw32,sw0,sw1,sw2,sw3,sw12],[[0,30018,17],[156],[17,30054,117],[17,30059,100],[156,10005,117],[157],[0,30000,75],[117,100],[117,100],[28],[75,179],[117,30001,75],[100,30000,75],[117,10005],[117,180,10023],[117,179,100],[100,148,160],[100,179],[117,148,179],[117,181],[10005,180]]),
([sw33,sw0,sw1,sw2,sw3,sw12,sw17],[[182,183],[183,182],[50,77],[30018],[30000],[30016],[184,77,185],[50,170],[50,41,77],[50,44,77],[50,41,77],[50,77],[50,148,170],[50,44,170],[50,44,170],[77,41],[77,44],[77,41],[30000,44,41],[186],[187]])]
noncomputable def s7_D5 : List StD := [
([sw0,sw1,sw4,sw10,sw16,sw17],[[31,32],[32],[31,30049,10001],[31,30027,10001],[31,30024,10001],[31],[32,30019,10002],[32,30017,10002],[32,30000,10002],[188,30019,29],[189,30017,33],[190,30000,34],[6,191,153],[17,192,7],[6,193,17]]),
([sw0,sw1,sw10,sw34,sw16,sw17],[[31,10002],[31,29],[29],[31,194,195],[31,195,196],[10002,195],[32,10002,10012],[10002,196],[10002,195],[31],[29,197,198],[29,199,200],[30,194,42],[30,199,20],[29]]),
([sw0,sw1,sw10,sw16,sw35],[[31,30024,10002,201],[31,201,202,203,10005],[31,204,205,206,10025],[34],[10002,10005,207,30050,10008,30045],[10002,201,204,30024,10008,30051],[10008,17,10002,30000,30066],[202,203,204,201,191,205],[14,203,202,208,10005,209],[42,206,201,208,203,210]]),
([sw15,sw2,sw5,sw6,sw12],[[96,8,30038,10003],[8,211,212],[8,211,213],[214,8],[215,75,171,10003,30024,30017,10009],[10003,104,10009,30000,30027],[10003,216,10017,10026],[8],[171,215,216,10026,10017],[216,10026,10017]]),
([sw0,sw9,sw6,sw16,sw17],[[217,218,77,30043,10001,30010,10004],[219,220,77,30044,10001,30011,10000],[10001,221,10000,30017,30047],[77,222,10004,30000,30048,10001],[219,217,141,223,224,225,226],[223,217,227,219],[34,217,223,228,207,17,53],[33,219,224,77,229,109],[224,219,227,217],[77,17,230,217]]),
([sw0,sw1,sw36,sw6,sw16,sw17],[[218,30000,231],[232],[218,30041,233],[218,233,234],[218,30060,10000],[231,30043,235],[236],[231,30063,10010],[231,235,237],[130,30019,219],[218,234],[237,233],[234,235],[231,237],[234,233,235]]),
([sw0,sw1,sw36,sw10,sw18,sw17],[[31,170],[33],[31,170],[33],[31,238,89],[130,170],[239,128,240],[241,170,10010],[170,10010],[31,170],[33],[130,238,89],[242,170,148],[170,130],[130,89]]),
([sw0,sw1,sw2,sw5,sw19,sw17],[[243,30022,149],[149,30027,37],[244],[182,30056,10004],[65,10004,67],[243,245,37],[243,30013,181],[246],[243,149,115],[37,30016,179],[247],[37,149,181],[42,149,148],[65,149,67],[67,181]]),
([sw15,sw0,sw2,sw6,sw10,sw12],[[248,26],[98,30067,28],[28,248,213],[28,148,29],[249],[28,30000,171],[28,171,95],[28,30024,178],[28,178,171],[95,28,53],[250],[251,53,10027],[28,171],[95,178],[171,53,30000]]),
([sw0,sw1,sw2,sw5,sw14,sw27],[[149,30038,41],[149,30006,37],[252],[130,30004,253],[9,41,67],[41,30002,37],[217,30061,254],[246],[67,149,115],[37,41,254],[37,149,253],[255],[256,149,41],[9,149,67],[67,41,115]]),
([sw15,sw2,sw36,sw3,sw6,sw12],[[257,258,8],[8,258,259],[8,260,242],[8,260,261],[214],[8],[171,30000,170],[104,30017,10003],[170,10028,10019],[262,30024,10029],[104,171,170],[171,178],[8],[171,10019,10017],[170,10019,178]]),
([sw0,sw1,sw2,sw3,sw13,sw37],[[148,30007,145],[148,30005,178],[178,30004,53],[171],[0,145,67],[145,263,178],[145,148,178],[53,178,115],[10002],[263,148],[217,145,53],[10003],[263,148],[10005],[0,148,67]]),
([sw23,sw0,sw1,sw36,sw3,sw16],[[264,17],[17,20],[20,17],[265,95,149],[17,65,104],[149,95],[75],[149,95],[104,127,170],[104,95],[170,10011,53],[95,149],[104,95],[104,149,127],[95,149]]),
([sw0,sw1,sw2,sw5,sw13,sw38],[[148,30038,266],[148,267],[268],[269],[0,267],[266,115],[266,148,115],[266,115],[270],[40,148],[271,267],[20,148,10003],[268,148],[0,267],[0,148,267]]),
([sw29,sw1,sw2,sw5,sw25,sw12],[[98,30068,96],[96,30069,148],[156],[98,95],[157],[98,118],[118],[118],[118],[98,148,118],[118],[98,118],[98,95],[118],[95,148,118]]),
([sw24,sw1,sw2,sw5,sw25,sw12],[[98,29,272],[29,109],[273],[95],[98,30056,253],[98,118],[118],[118],[118],[98,253,118],[118],[98,118],[98,118],[118],[118]]),
([sw23,sw0,sw1,sw7,sw3,sw16],[[274,17],[17,20],[4],[181,95,21],[17,181],[181,95],[75],[21,95],[21,127,171],[104],[181,171,21],[95,181],[21,95],[21,127],[95,53]]),
([sw0,sw1,sw2,sw3,sw21,sw27],[[149,275,145],[149,30005,178],[149,30004,178],[139],[9,145,67],[145,30002,178],[145,30001,178],[138],[67,149,115],[66,275,54],[130,149,53],[276],[141,149,54],[277],[29,67,54]]),
([sw15,sw0,sw2,sw3,sw25,sw12],[[278,17,156],[17,181],[278,171,53],[22,181,95],[115],[171,30017,54],[53,30000,178],[22,171,95],[171,178],[171,53],[262],[77,53,10019],[75],[171,54,10017],[95,53,178]]),
([sw23,sw0,sw1,sw3,sw10,sw12],[[25,17],[17,20],[3,54],[279,54,280],[53],[254,281,170],[178,30024,282],[254,170],[281,178],[254,30000,283],[178,282],[281,254],[75],[281,10030,30035],[281,254]]),
([sw0,sw30,sw1,sw3,sw10,sw12],[[17],[17,281,77],[77,30006,282],[149,170],[281,234,10024],[17,281,20],[3,282,54],[149,77],[281,234,10019],[17,30000,170],[17,77],[17,254,281],[17],[281,10019,234],[281,149]]),
([sw15,sw2,sw36,sw9,sw3,sw12],[[17,284,181],[75,285],[17,284,181],[181,95,53],[73],[286],[287],[75,53],[75,53],[75,95,286],[104,95],[104,53],[75,53],[75,53],[95,174]]),
([sw29,sw32,sw1,sw36,sw3,sw12],[[0,170],[17,30059,117],[285],[117,10005],[288],[170,117],[117,170],[98],[170,181,75],[117,181],[10005,148,181],[75,179],[117,10005],[117,181],[10005,148,181]]),
([sw15,sw39,sw1,sw2,sw3,sw12],[[20,77,178],[178,20,289],[20,170,54],[242,253],[290],[75,77],[77,170,54],[177],[77,178],[178,30000,54],[178,10029,21],[170,178],[170,54],[170,10028,21],[10011,54,291]]),
([sw0,sw1,sw2,sw20,sw21,sw17],[[292,170],[292,170],[293],[253],[292,95],[95,77,54],[294],[295],[170,296,67],[174,170,10016],[235,170,10014],[170,54],[7,54,293],[7,95,174],[6,95,54]]),
([sw23,sw0,sw1,sw2,sw3,sw21],[[9,19,288],[19,297],[19,298],[174,95],[19,288],[149,19,95],[174,170,149],[149,95],[283],[174,299,234],[170,115,67],[282],[174,10015],[75,19,10031],[10015,174]]),
([sw28,sw4,sw2,sw3,sw22,sw12],[[10032],[95,30070,54],[96,30071,170],[30046],[95,30046,54],[54,170],[53,95],[300],[54,67],[95,54,170],[301],[96,53],[302],[95,54,303],[304,54,30000]]),
([sw23,sw0,sw1,sw2,sw3,sw13],[[0,288],[288,170,20],[288,170,54],[305,95,174],[0,288],[104,170],[174,170,149],[104,95],[77],[95,126],[170,126],[126],[170,126],[104,170,126],[126]]),
([sw40,sw0,sw1,sw4,sw2,sw3],[[0,77,67],[67,170,115],[22,67,306],[67,77,53],[307,95,54],[30000,77,170],[253],[115,170],[77,67,115],[149],[95,77,54],[67,115],[54,77],[53,67],[77,53,67]]),
([sw23,sw28,sw4,sw2,sw3,sw12],[[0,170,30007],[22,20,306],[20,170,149],[149,95],[65],[10032],[149,30038,95],[170,30038,149],[170,30038,104],[104,170,282],[254,95,21],[282,149],[170,282,95],[170,149],[95,149]]),
([sw23,sw0,sw1,sw2,sw3,sw12],[[0,77,17],[17,20],[17,77,149],[149,95],[65],[149,77,95],[149,170],[77,95,149],[77,174],[95,77,282],[170,171,75],[95,149],[77,282,95],[77,149],[95,149]]),
([sw0,sw1,sw2,sw7,sw3,sw41],[[181,18],[18],[18],[18],[181,18],[18],[18],[181,18],[18],[18],[18],[18],[18],[18],[181,18]]),
([sw42,sw1,sw2,sw3,sw25,sw12],[[98,77,17],[17,308,309],[98,96,77],[98,77,113],[98,157,77],[98,77,282],[181,98,53],[114],[113,115],[98,282],[310],[98,181],[117],[113,54],[113,181]]),
([sw24,sw1,sw2,sw3,sw22,sw12],[[98,77,96],[96,308],[98,96,77],[30030],[98,30010,77],[98,77,282],[181,98,53],[114],[282,115,53],[98,282],[310],[98,181],[117],[282,54,181],[14,181,10023]]),
([sw23,sw0,sw1,sw2,sw3,sw43],[[65,288],[288,65],[65,181],[181,282,149],[65],[181,77,170],[149,170],[282,95],[10023],[95,181],[181,115,53],[10033],[77,282,95],[10031],[30000,282,10022]]),
([sw44,sw1,sw2,sw3,sw25,sw12],[[98,77,17],[17,283],[98,253,77],[98,77,300],[98,113,77],[98,77,253],[283,98,181],[114],[282,115,53],[98,283],[310],[98,181],[117],[283,54,181],[14,181,30056]]),
([sw40,sw0,sw1,sw2,sw7,sw3],[[15,77,113],[70,115,311],[312,77,53],[104,115,313],[314,282,21],[282,77,170],[115,170],[180],[77,95,115],[95,77,282],[235],[53,115],[54],[77,53,95],[10022,115]]),
([sw29,sw1,sw2,sw3,sw22,sw12],[[282,77,170],[115,170],[282,95],[30030],[67],[95,282],[170,115,53],[114],[282,115,53],[77,282,95],[310],[77,53,98],[117],[282,54,315],[14,115,174]]),
([sw44,sw1,sw2,sw3,sw12,sw37],[[282,77,217],[217,283],[282,253,77],[77,174],[30010],[253,282,77],[283,115],[282,174],[30046],[77,282,253],[77,53,235],[30040],[282,174],[30041],[30056]]),
([sw0,sw1,sw2,sw3,sw12,sw45],[[282,77,253],[115,283,174],[282,253,77],[77,174],[30010],[253,282,77],[283,115],[282,115,174],[30013],[77,282,253],[77,53,235],[30016],[282,174],[30018],[30000]]),
([sw40,sw0,sw1,sw2,sw3,sw12],[[0,77,174],[174,282],[316,77,149],[174,282],[53],[282,77,283],[174,283],[77,253],[77,174],[174,77,282],[283,171],[282,174],[77,282,174],[77,149],[282,174]]),
([sw40,sw0,sw1,sw2,sw3,sw22],[[53,77,113],[53,282,115],[235,53],[315,282,235],[14],[282,77,253],[115,283,171],[53,253,77],[10023],[235,77,282],[53,115],[10033],[77,53,253],[10031],[10022]]),
([sw40,sw0,sw1,sw2,sw3],[[0,174,67,77,10001,113],[67,174,22,115,282,10002,317],[67,149,316,53,77,10003,318],[113,174,307,235,282,10005,21],[253,282,10000,77,10002,10001],[174,115,10001,10000,10003],[77,115,10001,253,67,10005,10004],[174,10003,282,77,10009],[10002,67,235,115,10011,10005],[77,174,10003,253,282,10015,10005]]),
([sw0,sw46,sw1,sw2,sw3,sw12],[[174],[282,77,253],[149,283,171],[282,253,77],[77,67,10024],[149,282],[149,77],[149,282],[0,67,30000],[253,282,77],[283,171],[282,149],[77,282,253],[77,149],[282,149]]),
([sw47,sw0,sw1,sw2,sw3,sw12],[[0,77,253],[149,20,319],[253,77],[282],[181],[253,77],[149,170],[77,253],[77,174],[253,77],[170,235],[170,149],[77,253],[77,149],[30000,149,235]]),
([sw0,sw1,sw2,sw3,sw22,sw12],[[253,77],[315,283,171],[77,253],[113],[253,67,315],[253,77],[315,171,283],[320],[67,115],[77,253],[310],[253,181,67],[117],[315,235],[14,67,30000]]),
([sw29,sw11,sw1,sw2,sw3,sw12],[[0,77,253],[253,77],[315,170],[77,253],[234],[315,320],[253,77],[283],[235,181],[253,77],[315,235],[170,179,21],[77,253],[77,181,235],[315,235]]),
([sw29,sw48,sw0,sw1,sw2,sw3],[[0,30000,67],[283],[235,10034,113],[113,10035,115],[113,10036,115],[0,10024,174],[174,115,306],[235,181],[174,235,181],[235,30063,180],[115,30017,174],[115,30000,178],[235,115,181],[181,235],[174,282]]),
([sw0,sw1,sw2,sw3,sw49,sw27],[[235,240],[256,283,174],[282,253,178],[235,174,283],[256,240],[235,282],[240,235],[282,240],[8,235,10002],[256,283,174],[235,256,253],[321],[256,235],[136],[256,240]]),
([sw26,sw50,sw1,sw2,sw3,sw12],[[30010],[235,10002],[170],[95],[240],[10002,235],[0,256,321],[0,282,253],[0,235,322],[235,282],[10002,235],[10002,178],[256,282,253],[235,256,253],[256,235]]),
([sw0,sw1,sw2,sw3,sw51,sw27],[[235,30046,253],[256,283,178],[178,253],[235,178,253],[256,253,30065],[235,282],[256,235],[282,178],[8,235,30046],[256,253],[235,256,253],[321],[256,235],[136],[256,322]]),
([sw0,sw1,sw2,sw3,sw52,sw12],[[315,170],[315,170],[282,67],[113],[315,67],[240,315,282],[315,115,67],[320],[170,115,67],[315,282,67],[310],[170,181,67],[315,282,117],[315,30000,282],[14,67,104]]),
([sw53,sw0,sw1,sw2,sw3,sw12],[[0,283,113],[42,315,320],[42,315,310],[42,283,117],[14,65,104],[283,170,315],[315,283,170],[282,95],[283,240,315],[95,315,282],[283,171],[170,179,21],[315,283,95],[170,181,240],[283,10019,315]]),
([sw28,sw4,sw2,sw3,sw12,sw27],[[10037],[256,30070,27],[27,30071,130],[256,30046,275],[256,30046,10002],[130,282],[256,253],[282,180],[8,282,30046],[256,282,130],[130,256,253],[321],[256,130,282],[136],[137]]),
([sw23,sw0,sw1,sw2,sw54,sw3],[[323,240],[324,325,326],[240,170,181],[30035],[240,282,30000],[181,240],[178,170,327],[178,30004,104],[282,95],[240,181],[240,30001,101],[240,171,283],[170,30000,104],[170,282,95],[180]]),
([sw0,sw1,sw2,sw3,sw55,sw19],[[65,30046,180],[180,30040,327],[65,10004,178],[65,180,10004],[65,180,10004],[65,327,282],[180,115],[327,65,178],[328],[65,282],[65,62],[62],[327,180],[62],[65,62]]),
([sw0,sw1,sw2,sw56,sw3,sw12],[[282,170],[115,170],[180],[282,95],[115,240],[95,282],[320],[170,115,283],[282,115,67],[310],[170,282,95],[170,181,240],[320,282,117],[313,115,30000],[282,10018]]),
([sw57,sw0,sw1,sw2,sw3,sw12],[[0,283,180],[22,282,178],[316,253,234],[307,283,180],[0,181,113],[283,171],[113,283],[282,253,113],[283,10007,10023],[253,282,77],[283,171],[282,149],[171,283],[253,149],[283,149]]),
([sw0,sw1,sw2,sw3,sw58,sw16],[[180,240,149],[180,30040,149],[149,195,178],[195,180],[195,180],[240,30043,51],[180,195,240],[195,240],[195,149],[180,53],[20,149,53],[170],[329,180,10015],[240,180,10036],[51,240]]),
([sw29,sw59,sw1,sw2,sw3,sw12],[[253],[117,170],[100,170],[117,95],[240],[117,170],[117,170,100],[117,95],[14,180],[117,119],[170,119],[170,119],[117,119],[117,119],[95,180]]),
([sw0,sw1,sw60,sw2,sw3,sw12],[[282,170],[180],[171,170,283],[282,95],[171,240,115],[149],[95,282],[170,171,283],[282,115,67],[20,170,310],[310,282,117],[306,240,30000],[170,282,171],[170,49],[282,49]]),
([sw61,sw0,sw1,sw2,sw3,sw12],[[0,77,180],[149,170],[149,77],[0,282,180],[240],[180,77],[180,170,149],[77,95,149],[77,180],[95,77,49],[180,235,170],[170,149],[77,54],[77,149],[95,180]]),
([sw62,sw0,sw1,sw2,sw3,sw12],[[0,283,180],[149,282],[149,42,330],[180,283],[0,256,322],[283,30000,149],[180,283],[149,253,113],[283,180],[253,282,137],[283,195,322],[282,149],[180,283],[253,149],[283,180]]),
([sw15,sw0,sw2,sw63,sw3,sw12],[[180,77],[20,77,167],[167,20,313],[180,95],[65],[180,170,167],[180,77],[77,95,167],[77,180],[167,77],[180,30000,77],[77,254],[180,167,170],[95,254],[95,180]]),
([sw15,sw0,sw1,sw2,sw3,sw64],[[180,77],[104,313],[104,77,149],[180,95],[104,65],[180,77],[180,170,149],[77,95,104],[77,180],[104,77,49],[180,171],[95,149],[180,30000,77],[77,149],[95,180]]),
([sw15,sw0,sw1,sw31,sw10,sw12],[[331,77,180],[332,333],[20,30007,28],[180,77],[334],[180,77],[77,30024,332],[332,170],[77,180],[28,30000,170],[180,77],[170,178],[10038],[104,30000,335],[77,180]]),
([sw15,sw65,sw0,sw1,sw2,sw3],[[8,30000,240],[137,240],[178,137,282],[240,10035,149],[240,10036,149],[8,10039,178],[8,10040,240],[149,215,336],[149,104,215],[149,240],[178,30027,149],[178,30024,149],[240,30017,49],[240,30000,49],[180,337,254]]),
([sw66,sw0,sw1,sw2,sw3,sw12],[[0,77,180],[22,20,306],[20,77,8],[180,282,49],[0,51,101],[282,77,170],[49,170],[77,338],[77,240,101],[49,77],[49,171],[282,149],[77,282,171],[77,49],[282,49]]),
([sw15,sw0,sw67,sw2,sw3,sw12],[[180,171],[22,20,313],[20,77,100],[180,171],[65],[180,171],[180,30024,100],[77,95,100],[171,180],[100,77],[180,171],[95,149],[180,54,77],[77,10021,104],[171,180]]),
([sw0,sw1,sw2,sw3,sw58,sw17],[[180,77],[180,170,50],[77,253],[50,180,253],[77,180],[50,77],[180,195,170],[50,170,195],[170,195],[180,253,77],[253,77],[77,253],[339,180,54],[186],[50,307]]),
([sw33,sw0,sw1,sw2,sw54,sw17],[[340,77,180],[341,342],[343,77],[30009],[171],[180,77],[180,170,341],[77,30024,341],[77,180],[343,77],[180,30000,170],[343,149,170],[77,30000,180],[77,149],[10022]])]
noncomputable def s7_D4 : List StD := [
([sw0,sw4,sw10,sw16,sw38],[[180],[188,30018,344],[189,30000,171],[345,344,95],[188,171],[189,344],[345,95],[344,346,171],[95,171,282],[95,344,282]]),
([sw0,sw1,sw10,sw16,sw68],[[180,171],[188,95],[171,180],[10000],[180,171],[95,347],[10008],[171,180],[20,180,282],[20,282]]),
([sw0,sw1,sw10,sw18,sw38],[[347,30000,180],[347,283,178],[171],[345,180,240],[180,235,178],[189,347,348],[170],[40,347,235],[240,347,283],[20,283]]),
([sw15,sw2,sw5,sw25,sw12],[[28,282,98],[28,171],[28,282,170],[240],[171,28,282],[116],[77,53,10026],[28,170],[282,10026,180],[170,53,149]]),
([sw23,sw0,sw6,sw10,sw12],[[248,171,178],[178,170],[349,171],[240],[347,171,170],[178,170,349],[171,178],[178,171,101],[170,178],[171,349]]),
([sw0,sw30,sw6,sw10,sw12],[[178],[347,170],[349,170],[171,240,10024],[347,170],[349,170],[248,240,10027],[240,171,101],[170,347],[170,349]]),
([sw15,sw39,sw9,sw3,sw12],[[8,171],[350,351,170],[100,253,315],[352],[350,8,170],[353],[171,178],[170,253],[170,178],[10011,54,291]]),
([sw0,sw9,sw6,sw16,sw35],[[218,30011,180],[220,95],[221,180,195],[77],[180,195,178],[195,349],[17,195,171],[95,180],[17,180,171],[17,54,315]]),
([sw15,sw36,sw6,sw10,sw12],[[178,171],[178,354,170],[8,171],[249],[104,171,170],[178,170,8],[171,178],[178,171,8],[170,178],[171,54,30000]]),
([sw4,sw36,sw6,sw16,sw17],[[195,171,180],[45,195,236],[195,170,50],[51,195,171],[130,171,170],[171,170,50],[98,355,77],[95,54,149],[170,171,51],[171,355,170]]),
([sw0,sw1,sw69,sw16,sw17],[[256,171,253],[256,253,171],[256,283,171],[256,253,67],[356,95,357,10041],[253,282,10042],[283,171],[256,253],[171,256,283],[256,171]]),
([sw15,sw65,sw0,sw2,sw6],[[8,171],[358,171,253],[358,10035,54],[359,358,95],[8,10026,178],[171,215],[359,171,360],[171,30000,54],[359,171,95],[359,54,282]]),
([sw0,sw9,sw6,sw14,sw27],[[54,171,180],[282,171,219],[54,171,253],[361,180,10001],[180,54,282],[253,219,362],[219,171],[282,54,180],[219,171],[219,171]]),
([sw0,sw1,sw70,sw18,sw17],[[282,170],[45,170],[171],[282,180,67],[180,282,178],[54,282,10043],[170,178],[42,170,54],[170,282,180],[42,282,54]]),
([sw0,sw1,sw7,sw10,sw41],[[282,170],[180],[315,170],[282,67],[320],[308,282,77],[170,65,67],[315,310],[54,282],[170,282,67]]),
([sw29,sw48,sw1,sw2,sw5],[[0,67],[282,10034,363],[54,10035,195],[77],[67,282,178],[67,262],[178,67,282],[54,282,195],[180,195,171],[178,282]]),
([sw15,sw71,sw9,sw3,sw12],[[262,308,171],[350,351,313],[308,171,180],[352],[262,171],[262,353,364],[171,180],[180,171],[170,178],[171,180]]),
([sw0,sw1,sw72,sw17,sw73],[[180,170,282],[191,170],[282,180,95],[365],[180,282,95],[170,178],[109,170,30013],[170,180],[321],[322]]),
([sw74,sw0,sw1,sw2,sw17],[[182,293,366],[293,40,367],[180,170,30016],[293,180],[293,170,40],[40,170],[40,293,95],[293,77],[293,40,170],[170,54]]),
([sw0,sw1,sw72,sw17,sw68],[[40,170],[40,170],[40,180,95],[366],[180,77],[170,40,293],[367],[170,180],[29,170,30016],[215]]),
([sw40,sw28,sw4,sw2,sw3],[[0,95,30007],[22,368,306],[368,77,149],[368,95,149],[10032],[95,30072,149],[77,30007,149],[180,77,54],[53,95],[95,54,77]]),
([sw75,sw0,sw1,sw10,sw12],[[25,29],[54,95,347],[29,25],[203],[347,95],[347,95],[322,180,195],[180,195,369],[95,347],[95,347]]),
([sw23,sw76,sw9,sw3,sw12],[[369,77,180],[370,371,372],[369,95,180],[373],[180,77],[77,95,104],[77,180],[180,282],[95,178],[95,180]]),
([sw23,sw0,sw9,sw77,sw12],[[369,77,180],[370,95,374],[369,77,180],[65],[180,77],[126,95],[77,180],[180,77],[95,178],[77,180]]),
([sw23,sw0,sw9,sw3,sw78],[[369,77,178],[178,95],[369,95,180],[369,77,104],[180,77],[77,95,104],[104,178,171],[178,171,180],[95,77,178],[77,180,95]]),
([sw79,sw0,sw1,sw2,sw3],[[0,77,67],[67,69,375],[67,77,376],[69,180,54],[282,77,253],[54,283,171],[77,253],[54,77],[283,171],[77,54]]),
([sw0,sw1,sw2,sw80,sw43],[[282,95],[171,283],[282,95],[377],[95,282],[283,171],[378],[95,282],[379],[34,282,54]]),
([sw23,sw0,sw1,sw2,sw81],[[180,171],[370,95,178],[370,77,149],[180,171],[180,171],[180,283],[178,95,149],[95,77,282],[180,171],[180,283]]),
([sw0,sw82,sw1,sw2,sw3],[[0,171,180],[282,171,283],[171,283],[282,253,77],[22,282,149],[149,253],[149,171],[253,282,77],[283,171],[171,282]]),
([sw40,sw0,sw1,sw2,sw3],[[0,171,180],[22,95,149],[149,77],[180,171],[180,171],[171,283],[149,95],[95,77,282],[180,171],[171,283]]),
([sw47,sw0,sw1,sw2,sw54],[[323,95],[283,171],[95,283],[10036],[283,95,171],[171,283],[283,30004,149],[95,282],[95,30001,180],[180,30000,77]]),
([sw0,sw1,sw7,sw72,sw17],[[282,171,283],[180],[171,283],[282,95],[380],[95,282],[283,171],[380,77,54],[34,282,30000],[171,282]]),
([sw23,sw0,sw1,sw3,sw72],[[369,171,178],[178,95],[369,171,30000],[369,77,54],[283,171],[178,95,282],[171,283],[178,171,283],[178,77,282],[171,283]]),
([sw0,sw1,sw2,sw52,sw17],[[282,171,283],[171,283],[381],[282,95],[95,282],[380],[283,171],[379],[171,282],[34,282,54]]),
([sw62,sw4,sw2,sw3,sw12],[[382,171,283],[171,335,383],[171,283,384],[171,54,137],[382,283],[382,253],[283,180],[137,283],[335,149],[283,180]]),
([sw15,sw0,sw63,sw10,sw12],[[369,171,283],[385,20,372],[369,171,180],[65],[385,171,180],[104,95],[171,180],[180,171],[95,347],[171,180]]),
([sw15,sw0,sw1,sw10,sw64],[[20,171,283],[104,313],[29,171,149],[20,65,104],[104,171,180],[104,95],[171,180],[180,171],[95,347],[171,149]]),
([sw83,sw4,sw2,sw3,sw12],[[0,98,114],[98,54,109],[114,109],[95,54,67],[114,77,54],[382,95,53],[54,67],[114,54,77],[114,53],[95,54,368]]),
([sw33,sw0,sw2,sw84,sw17],[[369,77,180],[369,77,349],[180,14,372],[271],[180,170,349],[349,77,170],[77,180],[180,77,262],[77,349],[170,180]]),
([sw33,sw0,sw1,sw72,sw17],[[369,109,386],[109,14],[369,77,149],[271],[387,77,262],[149,170],[77,180],[262,77],[262,347,170],[77,149]])]
noncomputable def s7_D3 : List StD := [
([sw4,sw10,sw18,sw38],[[388,170,283],[109,283,77],[345,170],[109,170,271],[20,283],[109,170,77]]),
([sw15,sw65,sw36,sw6],[[29,389,283],[358,283],[359,358,372],[390,391,392],[359,283],[359,283]]),
([sw40,sw0,sw63,sw10],[[20,283,180],[104,283,347],[180,77],[180,77],[178,283],[180,283,77]]),
([sw85,sw0,sw1,sw10],[[25,77,180],[104,170,347],[180,77],[180,77],[347,170],[180,77]]),
([sw47,sw0,sw1,sw72],[[325,77,180],[347,325,372],[325,77,180],[180,77],[347,170],[180,77]])]
def s7_D2 : List StD := []
theorem s7_I2 : LevelN true s7_T 2 s7_D2 := by intro s h; cases h
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem s7_C3x0 : levelOK true s7_T s7_t 2 (s7_D2.map Prod.fst) ((s7_D3.drop (0*16)).take 16) = true := by decide +kernel
theorem s7_I3 : LevelN true s7_T 3 s7_D3 := levelStep s7_B s7_W s7_I2 (chunks 16 s7_D3 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact s7_C3x0
  ))
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem s7_C4x0 : levelOK true s7_T s7_t 3 (s7_D3.map Prod.fst) ((s7_D4.drop (0*16)).take 16) = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem s7_C4x1 : levelOK true s7_T s7_t 3 (s7_D3.map Prod.fst) ((s7_D4.drop (1*16)).take 16) = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem s7_C4x2 : levelOK true s7_T s7_t 3 (s7_D3.map Prod.fst) ((s7_D4.drop (2*16)).take 16) = true := by decide +kernel
theorem s7_I4 : LevelN true s7_T 4 s7_D4 := levelStep s7_B s7_W s7_I3 (chunks 16 s7_D4 3 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact s7_C4x0
  · exact s7_C4x1
  · exact s7_C4x2
  ))
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem s7_C5x0 : levelOK true s7_T s7_t 4 (s7_D4.map Prod.fst) ((s7_D5.drop (0*16)).take 16) = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem s7_C5x1 : levelOK true s7_T s7_t 4 (s7_D4.map Prod.fst) ((s7_D5.drop (1*16)).take 16) = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem s7_C5x2 : levelOK true s7_T s7_t 4 (s7_D4.map Prod.fst) ((s7_D5.drop (2*16)).take 16) = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem s7_C5x3 : levelOK true s7_T s7_t 4 (s7_D4.map Prod.fst) ((s7_D5.drop (3*16)).take 16) = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem s7_C5x4 : levelOK true s7_T s7_t 4 (s7_D4.map Prod.fst) ((s7_D5.drop (4*16)).take 16) = true := by decide +kernel
theorem s7_I5 : LevelN true s7_T 5 s7_D5 := levelStep s7_B s7_W s7_I4 (chunks 16 s7_D5 5 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact s7_C5x0
  · exact s7_C5x1
  · exact s7_C5x2
  · exact s7_C5x3
  · exact s7_C5x4
  ))
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem s7_C6x0 : levelOK true s7_T s7_t 5 (s7_D5.map Prod.fst) ((s7_D6.drop (0*16)).take 16) = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem s7_C6x1 : levelOK true s7_T s7_t 5 (s7_D5.map Prod.fst) ((s7_D6.drop (1*16)).take 16) = true := by decide +kernel
theorem s7_I6 : LevelN true s7_T 6 s7_D6 := levelStep s7_B s7_W s7_I5 (chunks 16 s7_D6 2 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact s7_C6x0
  · exact s7_C6x1
  ))
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem s7_C7x0 : levelOK true s7_T s7_t 6 (s7_D6.map Prod.fst) ((s7_D7.drop (0*16)).take 16) = true := by decide +kernel
theorem s7_I7 : LevelN true s7_T 7 s7_D7 := levelStep s7_B s7_W s7_I6 (chunks 16 s7_D7 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact s7_C7x0
  ))
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem s7_C8x0 : levelOK true s7_T s7_t 7 (s7_D7.map Prod.fst) ((s7_D8.drop (0*16)).take 16) = true := by decide +kernel
theorem s7_I8 : LevelN true s7_T 8 s7_D8 := levelStep s7_B s7_W s7_I7 (chunks 16 s7_D8 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact s7_C8x0
  ))
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem s7_C9x0 : levelOK true s7_T s7_t 8 (s7_D8.map Prod.fst) ((s7_D9.drop (0*16)).take 16) = true := by decide +kernel
theorem s7_I9 : LevelN true s7_T 9 s7_D9 := levelStep s7_B s7_W s7_I8 (chunks 16 s7_D9 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact s7_C9x0
  ))
theorem s7_L : LowN true s7_R s7_T 10 := lowSearch s7_B s7_I9 (by decide +kernel)
def stopT : Nat := 0xfffffffefffefee8fffffffefffefee8
def stopR : List Nat := [0, 1, 2, 3, 4, 5]
def stopE : List (Nat × Nat × Nat) := [(0,2,3),(1,1,3),(2,1,5),(3,1,9),(4,1,17),(5,1,33)]
theorem stopB : baseOK stopT stopR stopE = true := by decide +kernel
theorem sliceCert0 : SliceN true stopR stopT (0xffffffff00000000ffffffff,10,[0, 1, 2, 3, 4]) := mkSlice (w:=0) stopB s7_B s7_L (by decide +kernel)
theorem sliceCert1 : SliceN true stopR stopT (0xffff0000ffff0000ffff0000ffff,10,[0, 1, 2, 3, 5]) := mkSlice (w:=0) stopB s7_B s7_L (by decide +kernel)
theorem sliceCert2 : SliceN true stopR stopT (0xff00ff00ff00ff00ff00ff00ff00ff,10,[0, 1, 2, 4, 5]) := mkSlice (w:=0) stopB s7_B s7_L (by decide +kernel)
theorem sliceCert3 : SliceN true stopR stopT (0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f,10,[0, 1, 3, 4, 5]) := mkSlice (w:=0) stopB s7_B s7_L (by decide +kernel)
theorem sliceCert4 : SliceN true stopR stopT (0x33333333333333333333333333333333,10,[0, 2, 3, 4, 5]) := mkSlice (w:=0) stopB s7_B s7_L (by decide +kernel)
theorem sliceCert5 : SliceN true stopR stopT (0x55555555555555555555555555555555,10,[1, 2, 3, 4, 5]) := mkSlice (w:=0) stopB s7_B s7_L (by decide +kernel)
theorem sliceCert6 : SliceN true stopR stopT (0xffff000000000000ffff,7,[0, 1, 2, 3]) := mkSlice (w:=0) stopB s5_B s5_L (by decide +kernel)
theorem sliceCert7 : SliceN true stopR stopT (0xff00ff0000000000ff00ff,7,[0, 1, 2, 4]) := mkSlice (w:=0) stopB s5_B s5_L (by decide +kernel)
theorem sliceCert8 : SliceN true stopR stopT (0xff000000ff000000ff000000ff,7,[0, 1, 2, 5]) := mkSlice (w:=0) stopB s5_B s5_L (by decide +kernel)
theorem sliceCert9 : SliceN true stopR stopT (0xf0f0f0f000000000f0f0f0f,7,[0, 1, 3, 4]) := mkSlice (w:=0) stopB s5_B s5_L (by decide +kernel)
theorem sliceCert10 : SliceN true stopR stopT (0xf0f00000f0f00000f0f00000f0f,7,[0, 1, 3, 5]) := mkSlice (w:=0) stopB s5_B s5_L (by decide +kernel)
theorem sliceCert11 : SliceN true stopR stopT (0xf000f000f000f000f000f000f000f,7,[0, 1, 4, 5]) := mkSlice (w:=0) stopB s5_B s5_L (by decide +kernel)
theorem sliceCert12 : SliceN true stopR stopT (0x333333330000000033333333,7,[0, 2, 3, 4]) := mkSlice (w:=0) stopB s5_B s5_L (by decide +kernel)
theorem sliceCert13 : SliceN true stopR stopT (0x3333000033330000333300003333,7,[0, 2, 3, 5]) := mkSlice (w:=0) stopB s5_B s5_L (by decide +kernel)
theorem sliceCert14 : SliceN true stopR stopT (0x330033003300330033003300330033,7,[0, 2, 4, 5]) := mkSlice (w:=0) stopB s5_B s5_L (by decide +kernel)
theorem sliceCert15 : SliceN true stopR stopT (0x3030303030303030303030303030303,7,[0, 3, 4, 5]) := mkSlice (w:=0) stopB s5_B s5_L (by decide +kernel)
theorem sliceCert16 : SliceN true stopR stopT (0x555555550000000055555555,7,[1, 2, 3, 4]) := mkSlice (w:=0) stopB s5_B s5_L (by decide +kernel)
theorem sliceCert17 : SliceN true stopR stopT (0x5555000055550000555500005555,7,[1, 2, 3, 5]) := mkSlice (w:=0) stopB s5_B s5_L (by decide +kernel)
theorem sliceCert18 : SliceN true stopR stopT (0x550055005500550055005500550055,7,[1, 2, 4, 5]) := mkSlice (w:=0) stopB s5_B s5_L (by decide +kernel)
theorem sliceCert19 : SliceN true stopR stopT (0x5050505050505050505050505050505,7,[1, 3, 4, 5]) := mkSlice (w:=0) stopB s5_B s5_L (by decide +kernel)
theorem sliceCert20 : SliceN true stopR stopT (0x11111111111111111111111111111111,7,[2, 3, 4, 5]) := mkSlice (w:=0) stopB s5_B s5_L (by decide +kernel)
theorem sliceCert21 : SliceN true stopR stopT (0xff00000000000000ff,4,[0, 1, 2]) := mkSlice (w:=0) stopB s3_B s3_L (by decide +kernel)
theorem sliceCert22 : SliceN true stopR stopT (0xf0f0000000000000f0f,4,[0, 1, 3]) := mkSlice (w:=0) stopB s3_B s3_L (by decide +kernel)
theorem sliceCert23 : SliceN true stopR stopT (0xf000f00000000000f000f,4,[0, 1, 4]) := mkSlice (w:=0) stopB s3_B s3_L (by decide +kernel)
theorem sliceCert24 : SliceN true stopR stopT (0xf0000000f0000000f0000000f,4,[0, 1, 5]) := mkSlice (w:=0) stopB s3_B s3_L (by decide +kernel)
theorem sliceCert25 : SliceN true stopR stopT (0x33330000000000003333,4,[0, 2, 3]) := mkSlice (w:=0) stopB s3_B s3_L (by decide +kernel)
theorem sliceCert26 : SliceN true stopR stopT (0x3300330000000000330033,4,[0, 2, 4]) := mkSlice (w:=0) stopB s3_B s3_L (by decide +kernel)
theorem sliceCert27 : SliceN true stopR stopT (0x33000000330000003300000033,4,[0, 2, 5]) := mkSlice (w:=0) stopB s3_B s3_L (by decide +kernel)
theorem sliceCert28 : SliceN true stopR stopT (0x30303030000000003030303,4,[0, 3, 4]) := mkSlice (w:=0) stopB s3_B s3_L (by decide +kernel)
theorem sliceCert29 : SliceN true stopR stopT (0x303000003030000030300000303,4,[0, 3, 5]) := mkSlice (w:=0) stopB s3_B s3_L (by decide +kernel)
theorem sliceCert30 : SliceN true stopR stopT (0x30003000300030003000300030003,4,[0, 4, 5]) := mkSlice (w:=0) stopB s3_B s3_L (by decide +kernel)
theorem sliceCert31 : SliceN true stopR stopT (0x55550000000000005555,4,[1, 2, 3]) := mkSlice (w:=0) stopB s3_B s3_L (by decide +kernel)
theorem sliceCert32 : SliceN true stopR stopT (0x5500550000000000550055,4,[1, 2, 4]) := mkSlice (w:=0) stopB s3_B s3_L (by decide +kernel)
theorem sliceCert33 : SliceN true stopR stopT (0x55000000550000005500000055,4,[1, 2, 5]) := mkSlice (w:=0) stopB s3_B s3_L (by decide +kernel)
theorem sliceCert34 : SliceN true stopR stopT (0x50505050000000005050505,4,[1, 3, 4]) := mkSlice (w:=0) stopB s3_B s3_L (by decide +kernel)
theorem sliceCert35 : SliceN true stopR stopT (0x505000005050000050500000505,4,[1, 3, 5]) := mkSlice (w:=0) stopB s3_B s3_L (by decide +kernel)
theorem sliceCert36 : SliceN true stopR stopT (0x50005000500050005000500050005,4,[1, 4, 5]) := mkSlice (w:=0) stopB s3_B s3_L (by decide +kernel)
theorem sliceCert37 : SliceN true stopR stopT (0x111111110000000011111111,4,[2, 3, 4]) := mkSlice (w:=0) stopB s3_B s3_L (by decide +kernel)
theorem sliceCert38 : SliceN true stopR stopT (0x1111000011110000111100001111,4,[2, 3, 5]) := mkSlice (w:=0) stopB s3_B s3_L (by decide +kernel)
theorem sliceCert39 : SliceN true stopR stopT (0x110011001100110011001100110011,4,[2, 4, 5]) := mkSlice (w:=0) stopB s3_B s3_L (by decide +kernel)
theorem sliceCert40 : SliceN true stopR stopT (0x1010101010101010101010101010101,4,[3, 4, 5]) := mkSlice (w:=0) stopB s3_B s3_L (by decide +kernel)
def certSlices : List SliceD := [(0xffffffff00000000ffffffff,10,[0, 1, 2, 3, 4]),
(0xffff0000ffff0000ffff0000ffff,10,[0, 1, 2, 3, 5]),
(0xff00ff00ff00ff00ff00ff00ff00ff,10,[0, 1, 2, 4, 5]),
(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f,10,[0, 1, 3, 4, 5]),
(0x33333333333333333333333333333333,10,[0, 2, 3, 4, 5]),
(0x55555555555555555555555555555555,10,[1, 2, 3, 4, 5]),
(0xffff000000000000ffff,7,[0, 1, 2, 3]),
(0xff00ff0000000000ff00ff,7,[0, 1, 2, 4]),
(0xff000000ff000000ff000000ff,7,[0, 1, 2, 5]),
(0xf0f0f0f000000000f0f0f0f,7,[0, 1, 3, 4]),
(0xf0f00000f0f00000f0f00000f0f,7,[0, 1, 3, 5]),
(0xf000f000f000f000f000f000f000f,7,[0, 1, 4, 5]),
(0x333333330000000033333333,7,[0, 2, 3, 4]),
(0x3333000033330000333300003333,7,[0, 2, 3, 5]),
(0x330033003300330033003300330033,7,[0, 2, 4, 5]),
(0x3030303030303030303030303030303,7,[0, 3, 4, 5]),
(0x555555550000000055555555,7,[1, 2, 3, 4]),
(0x5555000055550000555500005555,7,[1, 2, 3, 5]),
(0x550055005500550055005500550055,7,[1, 2, 4, 5]),
(0x5050505050505050505050505050505,7,[1, 3, 4, 5]),
(0x11111111111111111111111111111111,7,[2, 3, 4, 5]),
(0xff00000000000000ff,4,[0, 1, 2]),
(0xf0f0000000000000f0f,4,[0, 1, 3]),
(0xf000f00000000000f000f,4,[0, 1, 4]),
(0xf0000000f0000000f0000000f,4,[0, 1, 5]),
(0x33330000000000003333,4,[0, 2, 3]),
(0x3300330000000000330033,4,[0, 2, 4]),
(0x33000000330000003300000033,4,[0, 2, 5]),
(0x30303030000000003030303,4,[0, 3, 4]),
(0x303000003030000030300000303,4,[0, 3, 5]),
(0x30003000300030003000300030003,4,[0, 4, 5]),
(0x55550000000000005555,4,[1, 2, 3]),
(0x5500550000000000550055,4,[1, 2, 4]),
(0x55000000550000005500000055,4,[1, 2, 5]),
(0x50505050000000005050505,4,[1, 3, 4]),
(0x505000005050000050500000505,4,[1, 3, 5]),
(0x50005000500050005000500050005,4,[1, 4, 5]),
(0x111111110000000011111111,4,[2, 3, 4]),
(0x1111000011110000111100001111,4,[2, 3, 5]),
(0x110011001100110011001100110011,4,[2, 4, 5]),
(0x1010101010101010101010101010101,4,[3, 4, 5])]
theorem validSlices : ∀ s ∈ certSlices, SliceN true stopR stopT s := by
  unfold certSlices
  simp only [List.forall_mem_cons]
  exact ⟨sliceCert0,sliceCert1,sliceCert2,sliceCert3,sliceCert4,sliceCert5,sliceCert6,sliceCert7,sliceCert8,sliceCert9,sliceCert10,sliceCert11,sliceCert12,sliceCert13,sliceCert14,sliceCert15,sliceCert16,sliceCert17,sliceCert18,sliceCert19,sliceCert20,sliceCert21,sliceCert22,sliceCert23,sliceCert24,sliceCert25,sliceCert26,sliceCert27,sliceCert28,sliceCert29,sliceCert30,sliceCert31,sliceCert32,sliceCert33,sliceCert34,sliceCert35,sliceCert36,sliceCert37,sliceCert38,sliceCert39,sliceCert40,by simp⟩
end PEqualNP.Outside.L_meta_10393_aux

namespace PEqualNP.Outside.L_meta_10393_aux
def limb (width : Nat) (blocks : Array Nat) (i : Nat) : Nat :=
    (blocks[i / 32]?.getD 0 >>> (width * (i % 32))) % (1 <<< width)
def certOps : Nat → Nat → List (Nat × Nat × Nat)
  | 0, _ => []
  | k + 1, n => if n = 1 then [] else
    (n % 4, n / 4 % 16, n / 64 % 16) :: certOps k (n / 1024)
def certCut (n : Nat) : Nat × List (Nat × Nat × Nat) :=
  (n % 64, certOps 6 (n / 64))
def limbCut : Nat → Nat := limb 67 #[0xc20000000000000012c00000000000088248000000000000005d0000000000002208c00000000000044150000000000000002c0000000000000005b000000000000220960000000000000018000000000000000200000000000000005a0000000000000009200000000000000158000000000000002b80000000000000047000000000000000a00000000000000012000000000000000310000000000000005f000000000000000980000000000000016400000000000000278000000000000005c000000000000000aa0000000000000019c000000000000002a000000000000000660000000000000008c00000000000000194000000000000002f00000000000000068,0x9a420a80000000000000010c000000000248882400000000000010346000000000000206a800000000000040d3000000009b24a882080000000000000052000000000000264a80000000000004854000000009ac48882a00000000000000051000000000091a06a80000000000000010400000000024a8821000000000000000440000000000000008a000000000000441200000000000000031800000000000121540000000000922208c0000000001244411c000000000000002100000000004d2104b0000000000002208e0000000001244415000000009b24a882000000000000000053000000000000000940000000000000019000000000000000270000000000000004d,0x2649800000004490244150000000000269082500000001324c5215400000000009a242a800000000010448518000000000268882380000001364951042000000000000220980000000001324410400000000024a882180000000004c91040000000020c9aa42800000000000004c92c000000000000812a000000000000103490000000000002648c0000000000004853c000000000268882a000000000000132500000000000002208600000000000044d4400000009ac48882400000000004951040000000000089204a800001478d92544104000000000000882800000000004911050000000000092420a8000000000000441280000000a344a88210000000000001214c,0x2429a000000000125441040000000002648821800000014689510450000000248a2a2084000000050d1440d0c000000000000882700000000004d21052000000000000220840000000519324410000000000028b08218000051d364951040000000000090a04a8000000050d254410000000009b24a88218000000000411214700000002c992a20840000000000004c118000000000208992a0000000000001134700000000008a2088600000004194588508000000000000992900000000000013047000000028d12a20820000000519324410c00000009a2489922800000000000121470000000000002649200000000011340d5000000000000081a800000000000012146,0x9a4209000000000000048d1c0000000002488828800000016251510450000000284a2a208600000004d125441040000264b264a88210000051d30509324400000000009a2208c0000000000004c51c000000000268902900000000004951044000000028c92a208400000005192141108000028f1b24a8821000000000000121510000000000002068e0000000001244412400000000000098240000000000001214900000000000020292000000000124441080000000a324282220000000000001035100000000008a206a800000000012444130000000000000812400000000004d11048000000026492a208000000004d1244c910000026892226812180000000000013148,0xa1a4889a4288000000048d13485500000000000008123800000000048d024d00000000009a22096000000054f24441200000000000008222000000000050d104200000000009222086000000051a254410c00000000028a882180000001344911041000000000090a028c0000000001244412800000000024888268000000000001314d000000000000246a2000013449135441080000268a324281a10000000000001024c0000000000982649800000000012544114000000000000882900000001215161042000000026b12220a20000000000004c93c00000009928b0821800000000044d034b000000000091a26a80000143491134851400000000000098280000051d315093245,0xa3a60922468a0000000000004852000000000000090a2800000000051610450000000000922288a00000000014340d100000000a344a882200000001215161045000000024889a068400000004d1244091000000009ac488825000004c964c951041000000000000262a000001474c91440d0c00000000026890a80000000000001234a000000000098264a0000000000000485100000000000008820000000000050d1043000000000099220840000000001244511000000009228a882080000000000011354000000026892a2084000000050d234410800000009ac48882680000000004d12054000000000000260980000000000004c13400002648328b10a100000000000010348,0x2ca922208a00000004911340d0c00000009a22881a18000051e36495104300000a2ac992a20840000174d952344104000000090a8b0821800000000048d305200000a1a4889a0288000011340d458411400002488a24a8820000000000000110510000089a06a2c20840000134491324410c00000000020491a6000000000000132470000000000002209e00000000013484138000000000262992800000000004d521440000000000a2a208a000000041945885040000000a1a4a8820800000014349510420000000248a2a2086000000050d24441080000000ab2428222000000013449103450000083a8c9aa428000001478d92544114000028e9928a882080000000000012054,0xa1a428a0000000001458410800000008b20a992000000001364951045000000026a92a208000000004911440d1000000009028b082100000001464c503440000000268a2a208a000000050d244410c000028e9b44a88210000041d468d5214100000a3c6c92a20880000143515354410c000020eb266a90a08000050964c95104300000000009a220a200001474c91440d08000028e99226812180000000004092154000009a24899202880061337499154110400000000026890270012344d64c9510420000000000992048e0000000001434851000000000026a90a280000001325161045000000026c92a208800000004d5254410400000008b26480a000000001215161041,0x20ca2c4288000000051932441040000000a32648821000000014549510420000000286922268800001754991050d00000020ea346a90a00000045d065153240000009a28c92a20820000146593254410800002ec8828b1920800004c50651621410000098ac992a208200001234c545841140000000000008927800004d1424d51043000000000000240a000000000013240d4800000000024698a98000044d03516104300000a1a849922086000000044d034411800000000000080a3000000000044d214c000000000098a42a00000000001134851800a4260a126290a2800000000044d2150000000000091a249400521315093240510000000000000882200000000000010445,0x92420960000000001244412c00000000026908298000050d6548d104000000000009a4208c0000000001144c9500000000000008829800004c520516104100000a3a648a204880000000001348411c00000000024698aa0000051d314910244000009a2489aa208a000014350931485140000000002629824000000016590d1042000009a24899220880000000000004c92800002689226480a280000000004d12146000000000091a24a40000000001348412400000000026890a600000000004c90248000000024290220a800000000000044d3000000000024690a380000000004c5324c0000000000002208a00000000010548500000000000282822200000001434152140,0x9222882a42800000147449404410000002869328091a20000051d315093244000009a248992208a0000142519314c91400000000026890258013244d0251610450000000000002409000000000012444d3c00a4260a126290a20000000000001034f0030ea1a20a12648600000004c9314854c0000000000008129800000000000102460029098a84992208a000000000145841100000000a326a90a20000000165c414343000000026a92a208400000004c905485000000000a3242a02280000001434850140000000028c90a088600000004d1244411000000009a26a882180000001244510345000000026290220800000000519314111400000009228280a000000001434911345,0x90a02800000000001434111400000009a248992180000001464d521450000000264a2c2088000000048545841100000000b2a488821800000013449110400000000268922208600000004d1244411400000000028a8820000000013450503440000000286a12648a00001374914544104000028f0326a90a08000051d36495104500000a328d12a208a00001434193548500000024ea1a4a88200000050d6544123400000089a6c92c8086000017650532405000000246b264a88210000051d3251510450000000000002209a000017650d2140d100000268a324281a2000000000048d02520000091a62a2c208600001474c52440d140000286922268122800000000048d124e,0xa3a648a20280000000000134441240000268b2a4888228000051d324510345000000000089a028c0000134505204050000002629028b082100000000000011249000000000091a269e00001434510344100000000000206882300000000004c1324700000000009826494000000000134841340000000b0a8a9821000000000044910460000000000902469800001314c1458410c00000000026091a80000000000001324800000a3a60a12648a0000000001248c11c0000000000008124800004c91251610430028693a8089a4288004d127505354810c00000000026890260000000000001314600270a0a8499202880000000001304092000c3a8680a8499228014251d314c91045,0x248a2a2088000000048d45841080000000a1a2881a20000000000001134d000000022882220800000147859054c904000028f1b24a882000000000004d2104f00000a2ac992a2086000000000104485300000000b126a88200000049d434152140000009920ca2c42820000000000004854c00000000020890a80000045d32516104100000a3a64a2a208400001474c9454410c00002e9b2a248221000000016548d104000000bb26890a088800001764d1254411400000000026280a30000000000001234e000000000000226a000001424c5054850000000000026281a6000004d1424152140000008ba86902028000001134814584108000022e9928b0821800004d1424951040,0x98246a200000000013440944009a248b2a0489a18014350931481104500290992829822080004d1424d91044910000000000000982780000000004c9304700268922ca8826480004d124459058c91400c3a829928088200012844d2051610439ca82a3a40992028a000000048d314853c000000000264982900000000004c9134f00000000009a2408c0000000001314851800000009926289240000000000001104100000000008a208820000000001144811c00000009b20a90a000000001325161041000000028c99220880000000519324411400000008328b10a1800005d326455044100000ba64c8aa08840000000519324511000000008228a90a100000001454911042,0x89a609e000014651a254410800000000024888278000051564c951045000008ba64a2c208a00001425932544108000024889a6aa0210000045136496404400000a12c992a208a0000176451324110400002689b24b0821800004d1454d51043000000000000262980000000001234813800000000000089a4000005093149510400000098a40a2c208a00001425931548108000000091a8b0821800000000049130490000091a62a2c2088000017650d214111400000000026888250000000000491034c000009a24898a0488004d12444d02441140000248a1a2690a280000000000013051000008a2089922080000000048d134854c00000000022881a480000000004c5304c,0x29089a0ca12028000521314913548110009a248b2a6488200000000000452205400000000009a2428e004e141519204c91400a128e98a6480a200000000004510246000000000000246920000000001314c92400000009926290a78000000000485324900000000008a2068e00000000012444d1c000000000228822100000001464d6104300000a1a8a9aa2084000000051932451140000000b2e02a1a180000001658d11043000000000000240980000000491454411400000000026281a8800000010351531440000000208a2a628a00000004c5458410c00000000028a88208000051d3050932430000083a8d0aa6482000000051a2544100000000000226982a000000000044d3053,0x2469000001434990448d1000000009a26a88208000000000001125400000a1a4889a0280000000000000481240000248a1a2690a2000000000000130530000000000922609a00521314994048d0c00000000024698280000000113516104300000000009826492000000059543441080000284a3260992200000001564414340000000028c8826482000000048d134853c00000000022881238014349126456304400268a3a2492a608600000000010248d4000000000020491a480000000004493250000000000090220a80050d2444d054850000a1a8e892608820001324c5205161043000000000098a4298004d124419354850000a4246a0a0a90a00012850d144552040,0x228a2a648a0000000411454851000000000026a90a0000000011450d034300000002069a2828800000000011440d0000000000028a9821000004c164c152141000009228c9ac20840000124519358410c00000009ac4888238000050d454d51044000000000098a60a000000000013484144000028f0326b10a10000051e064c910400000091a0ca2c428400001764113588514000000000268882680000000004c9024e0000000000992049a000013251a2044100000028e98a4880a0000004c5235161042000009ba42a2c20860000143491254c10c000028e9928281a2000004d1464853045000000000081a02a200000000012440d4800000000000081280000040d345152142,0x9a2408e00509474c1314851400992628328b10a10012344d64c5520420026283a64a2c208400000000000048118009a24880a2a99220000000000412215400270a0a8c9026486004e141519204c91000a12eca1a209921801324dd41515204500000000009a242940000000001344812000a12eca1a0299228000000000001014a0000000000812468d1950d47409234411400000000028b08208000000146485044100000002868a2068400000000010450d140000000b2c86882280000001654c91040000000028d02a428200000005971050d100000000b2e20a1a280000519468951041000000026a92a20880000000001244414c00000008928b082180000001145153244,0x91a04940000000001234092c0000248a1a26812280000000004c912520024689a0ca2c428400000005932544104009c2249828b08210000000000491305000000a128c98a648800000004411340d18000000000264982800000000004d12050000009a2489aa40880000134491324410000000000000091a5800004d1244d52145000000000089a06980000000001104c13000a42629224a9821800000000048d2051000000000091a409a0050d24499354410c00000000026890a880000000004d11253000000000080a24a20000000000004c12400a1a288b20b19228011450d16416324500268922268aa40880050d2444d254410000a42609222690a28013451d204c51245,0xbb26890a808a0000104595144c904000028e9b44282220000051d36485044100000bb26890a088400001764d1214110c00000000026481278000000000001134a000009a2489aa048800000000000048d4000002649028b00a0800004de205160142000009228692a6086000010351932505100000000b226a882080000000004c9304e0000081acaa1a42880000104595434851400002069a28a90a18000040d345152144000009a28c90a06860000113519324090c0000228a3264812200000451464c90345000000000091a269a00000000013140d20000000000268902680000000004d102500000000000992069c00000004d135441000000248a3262812200000409344913144,0x8a204a80000000000004c150000028ab264a8820800000014688110400000000240a2c02820000142593254410400000000000091aa0000000000405214600000002ca822428800000004514340d100000000922868821800000012450d13440000000248a1a268a00000000014344100000028f0326b10a20000045d0651632410000083a8d1aa428800000004d6244414c00000009ac4888278000050d454d510450000000000924209000001425152544100000024ea342680a00000049d135160141000009928d02a428200001074c94580504000022e9928b08220000000000491305200000000009a204a40000132419458851000002eb93220a1a1000004c964c951045,0x99262980000000001324491c00000008926498a400000000000011349000000000091a249000000000011448d1c00000000024898a8000000000048d2149000000000091a42940000134515234850800002689226a90a1000005d943449024200264a3a62a12208a00000000010348d1800000000024689a4525305093141521450000000000902208e000000048d134493a06a4246a0a0a90a2cc938505464810140000000024698a429000000000012148d1c00000000022689248018750d2148110420030ea1a20a12648a00000000000050d000000000a3464882000000001065162140000000020ca2c428a00000004c9458410800000009aa4a882180000001354951045,0x268922268122080004913444d02441000099226a34408820001134c902516104100000a3a2099224860000000001304c91800000000026291a380000000004851346000000000092226900000000001214051c0098a4ea346080a00013149d30516104100262ba66c8120280004a11351a204410000942269028b082080000000004c101530023099206a2c208a00001474411340904000000000242902a00000000004c53046000000000099262900052131499404c9140000000a9e488825001874d110509324500000ba6ca90a0882000017650d254410800a1264b2a86882180124451304951040002489ba289822080004e114491304410000a128e98a6480a00000050964c550241,0x28c992048400001424c9454c51400000009a2648120800000000040d204c00000000008a2068c000000000134881340000000002068826000000000045103480000000000992069a00000000010448d3000000000020691a8000000000048d214b000000000089a2498004e1024c5458410800000000026090298012451d31495304300206992c982a42820049143499354410c0000000a9668882380000000004c9304b0000000000002029800000000000044d1800000000026880a3000000000048d3049000000000099206940000000001134053000000000022491a60011450d024553244002868a2048aa648800000000010444918000000000000902780000000004c9204b,0x992268e000012450d134050000002689224a8821800000014351502420000000286922048400000000012440d1c0000000002468123800000012444d2140000000026889a4282004c913409458410c0000226a1a4890a2800004494688110400000089204a2c2082000000044d03441400000000a322089a18018151d305093243000000000091a409800000005193150108000000099226892a00000000004c52349000000000092260980000000519314c108000024891a8a982280000000004c93051000000026299242a800000005191050d0000002849928a982200000000004c9304c00000002caa1a20800000134491354811400002489a264882000000001024491054,0x91a40a400000000013048130000000000260902800000001464412140000000028c90a08800000000001304093000000000000081a68000000000001234c000009a28a91a048800000000012140530000000000260812680000000000010251000000028c88242860000124519314050000000000026481a600000000004c90349000000028c8824686000012344d4584108000026489a8b082180000000004d1214d00286ba24c88264860000000001304091c00000000020681260000000000001024a000000000090a208c00000000013140d1800000000000091a300000001464411340000000000080a268c000000000123409300000000b2a2881a08000048d435150244,0x8388c9aa428000001071193548504000020e2326a90a10000041c464d52143000008388c9aa4288000014651a254410c000028ca344a88220000051564c95104400000000008a204920000000001148812000000000020910a400000001324c120540000000000922069e0000000001214414000000000020890a480000459064c91040000000000098a60a20000000001314c13400002648328b10a0000004c9065162143000009bc40a2c02860000000519104c90c0000000002688828000004c964c95104000000992c992a20860000132593254411000000008828b192000000001104d64240000000022092c86800000142593254411000000000020298a300000000004413050,0x89a069200000000011340d1c00000000024689a8800000000040d314c0000091a62a2c208400000000010448500000000000248992000000000004d1324100000000009a260820000000491344c91400002eaa34648820800005d93251610400000083a2ca2c648000000004d61448120000022e8328b19200000045d468c90140000009820ca2c42800000174c1935885080000000b264a88200000051e32516104100000a3c64a2c208400001478c9458410c00000009ac0890a40000051e064d62143000009228c9ac208800001245193584114000026f2344a8821000004de468951043000009bc8d12a2088000013791a2544114000020ea346a90a10000041d468d52143,0x2629a22482c8480004d12744d204410400000000022099200000000000001035300000000000022882000000000000411000000000ab26488200000000000516104000000000009a242a60000000001344853c0000000b2c868820000000016590d104100000002ca99220820000000595104c90400000009a28a8821000005cd4648504410000000000a0242880000000001034c53c00000000000098a780000000004c52140000000000000240a2000000000124441480000000a342090a1000005d93448504410000000208a2a42860000000001344414c00000000020689a5800000000048d1353000000026c822268600000000000040d280000000a2a2881a280000001344510345,0xa1a4889a2487434a114419134091400000000024889a50000050d244d5124400000a1a8a89a248800000000011244d24000028692226892200000000004c9124e00000a326498204840000000001234852000002868122b21200000000000001014b002689226c90a208a000000048d0348130000000089a068826000000000048d03460000000000812428e00000000011240528009c224a1a4080a000000000004c9134b98a40a3c20a2c6487424c507485454c11400a42629920b10a1001484c53249510420000000000902428e0050d4244d058850800a1a8489a4a882152523505034951040002908826498a048600521104c5204c904000000089240882a000000000044d2349,0x22691ac992a20840000147441134810c000028e882629820801385053251520450029098a849920280004c9474c54240500000000090242882a0000051d104c5324100264a3a62a1202880000000000004093c00000000024898a700000000004c92149000009ba84a0a2484000000000131449180000284a3262892080000000004493146000009ba82a1264880000134519214c90e649c282a324080a28000051d104c53040000009224682c868600000000013148d40009420690a8b08218011340d64c55024200000a3a42a1a04800000000000004491c00002869226a8921800000012344913460000091a2c922268000000000011244d30000024e8a28689a2000000000044d324f,0x29103a4291a26820048d134194588510008426e90a689220001314dd025160141002429bc40a2c02860000147441358810800000000024080aa000004c931516104300000a3a209926286004e1124c14584114000028e8826489a18013844903516104300000000008a2408c0000000001144094400000000024090a880187441324d12440002689222c99202880000134409158c90400002689b2428120801244d11641632450030993a2091a268000613274412344d040091a26b264a88220012344d64c9510450030e992209a248800000147441154c9040000260a1a4b20a0000004c1434564240000000000098220900050932595434411000a1264b2a8688228000050d424d52043,0x98246940000000001344812800000000022891a400000000004911349000000000089a429c00001435153040908000028692260812100000000004c92147002868ba48992028a0048143509314411400a446489a0488200014884113409324100000a3a2089260820044d474c12448514000028e88264982080134509124d510440026898a24a2a408a00000000010244144000028e88284992000000000004c53047000000000089a649800001374911444d100000000002648924800004dd2445112439ca488ba0889a048a00000000012344d2800002849922b20200000050932416414000262a3a60a12428a0050d2444d254411400000000000098290012344d468152141,0xa1ac59aa20840050d24499158c1140089a8f1928b08210011351e32516104300226a3c20a2c64840044d47841458c90c00a42249a24a98218000051d13496304100000a3a269aa4082004d124499158c11000000000026890a4800000000044931490000000000002028e00000000000048d3c0000000002028926800000013240d204b000000000092226a400000000000044928000026e89268812000000000004c9204600000922068ac648200001244d92140d040092268b2a0489a1801134d1244552044000009a2468ac4084000013448d25441080000000002069923800004dd2150d02400000000000992269c0000141593054490400002269828b082200000000004c12052,0x262982209c0000000001134c1300090a6f1028b08220000000000491034900000000009a242a40000000001304092c00000000024880a380000000004d1125000000000009a240920048d1348145841100000286a2a2688210000050d4140d1042000000026098a029200000000012444d3800002689226a90a00000000000491135100000000009a224a4000000000113485240000268a2a468121000004d1244d502420000000000922269a0000134491354490800000000000098a4800004d1264c50241002629ba04a2c208400505474da024410000002829a24b182080000505344d520410022683a8d1920280005221044d054c90400000000026080a780184c1d214c90341,0xa3a2089a0680000000050d45441000000000a1a2b20200000000143416414000000a1264a2a608a0000142519304c9140000000a2a86882000134491654c9104300000a126482c868a00001424c90590d1000002649a248882000000491344c9104300000992689222086000000050d258410000002489a2648822000004c934491104400000002868ac408000001244d1324411400002649a2488822800000014341621400000000286a1204800000000001324c540009a2489b24280a200000491344c901440000099268922028800001244d1324051400002649a24880a28000000000441034c0000000000822248e00001470d9254410000000000020891a4000000000048d034c,0x2408e0000000001134c94c0000000922869021800000014348d2042002869222692a2088000000050d454810c0000000a1a6a90210000044d4349121440000000224812208c000011449125441000000000a2a26882180000001314c11049000000028c8822482000000050535501040091a8e98a4aa0218000050d2349540440000000000812028c0000000001234c14400000009a282982080000491464c123450000000282a2a60820000000001344814400000009a282982100000000004c9304d00000992288222080000010344d4584108000020689a8b082180000509325153144000009a2489aa4288000011340d45841000000000a326081220000051d1044d0341,0x286a2a208400000004d135441080000000a32209020800004c54684120420000092206a2a628a000013451921409100000000a322089a0800004913444d0243000009226898a04880000000001234091800000009b2488120800000014349132430028693a289920288000000000132449440000268a126a892280000001264112340000000000089a24a000001345091344914009a2848b20689220000044d434910144000000026891a4284000011450d03441000089a648128b082180000001464410341000000000099242a20000000519304c9080000000a3260a12180000000004c9304a0000000280a1264800000000501434c90400a128e9826290a200000001455093043,0x27090a60a2c208400000005193044d000000000000008126801484c526411234300000002829aa0882000000059315409040091a26b262a812100000000004c102540000000000982649000000000012040518008424698a8b082100000000004c1234d00000002629aa088000000000012048d400000268a324091a28013451d214950343000009a28a9aa408a0000134515234811400000000024881a68000000136441344000000a1a489aa408a000000000103441200000000a1a0888210000000000001124800000a1a4c8a2468800001434991448d140000000a326089a1000000000048d205000286bb2288124686000014351523409100000000a1a0b20a1000000000040d3252,0x26892c608200000004d1354810400922869322b182200000001404c91044000000000000224a600001145193240500000026881a8a90a20000051d214d13045000000026489a42a800000000013444130000000090a8a80a00000041d3251610420000000000002029a00000004d92141100000000000264982980000000004c9024c000000000081264980000143451354410c000000090a8a88200000000126405044000000002428220280000000044d0440d00000026892206812200000001044d64240000000020892c86800000000411358850000000008224b18a000000001044563240000009a24889a40880000137491134090c000024e8226489a18000049d044513244,0x8ba46a2c20840000000001324c13c0000000002489828800000012340d205200000002488a224820000141593154090800000000022681a3000000014044d0340000009a28492a06880000000001144094c00000000024881a8800004d1454c10244000009a248982048800000000012444d500000000a2a2881a08000000134451034100000a1a4c82224860000000593254410c0000000a128a88200000000142515104100000b26848aa40840000000519324110000000000000099268000000142441044000000a1a8c882068600000004d14040d000000262a346480a0000004c523516104100000a3c6498a028000001478413148d04000028f00a6b102100000001464413141,0xbb22091a86800000132419458851400002269226aa02100000001144d64040000000028c98228800000174c99104c90000002e99322099208000000000412214c00000bb246882868000001174c945841080000000a026a90a20000050964c95014400000a12c992a02860000000595034850000002489a26a882100000001244d6104100000002489aa2082000010451935485040000208b2a6890a100000411654d1214300000822ca9a2428800001344912544100000024689a8b0822000004d1464413141000009a28c88262800000134519104c1100000286a0a6a80a20000050d414d50143000009a24898220880000134491304811000000008222b2120000004c564c550241,0x91a60a2c208800000005192544104000000099260902980000001324c1204f00000a1a8a982208800001245053140d0c00000000024288260000044902516104200000a3a62a0260880000145509254410000002629828b082200000000004c12054000000000098220a2000000000130441340000286a126488210000050d454d52144000009bc24a2c02860000000000004c138000028f0324299208000041d36485434000000002809ac428a00000000000044918000000089a4088200000000000001304a000000000090220920000000481458410c0000000a2a4888208000000000481234900000000009a2049a0000000001234c13800000000024898a780000000004913153,0xa3c208aa64820000000001304413c00002e983242982080000001325161040000000028c88264800000147841458c904000028f0828b19210000051e10516324300000a3c6d12a208a0000117419458c908000022e8328b19218000000000492104a0000083a8d1aa428a0000147499104d10400000009ac4888258000000135891104e000000026b12220a400001474d92544104000028e9b24a88210000051d36495104300000a3a6c92a2088000014550d354410c000028aa1a6a882200000515434d5104500000ba6ca88248840000000001134c13800000000024088268000051540415214400000ba6c292a0884000013788145841100000280b264a8822000004c5205161044,0x99206a600000000011450904000000000208a120000000000050914410000000000a12088000000000013140524000000000246812780000000005152141000000000090a088000000000012340d4c000000000246982a00000000004c9035400000002868a2608a000014349135441080000000a1a6a8821800000000049110410000000246a1a2084000000000135411040000000a1a4891a28000050d26411234300000000009a20682000000049134409100000000000009928800000000050d404000000a128c982648600000000000048d4800002689226a90218000000000515304100000002489a264880000000001214413800000000020891a48000051e064d62145,0x9a220a4000017641132451040000000a32048a2180000001464091442000000000082c648000001764d1104910400000000026a882000000001144164245000000022882c8488000000051920451100000000ab220922100000001244d1104000000002489a220860000000001258410000000009226888220000000000456204000000002489a2208a0000000001058850000000009a2289822000000000040d1349000009ba08922268400000000010344d34000000089a4881a1000000012440d13420000000226922068600000004910344d0c00000008a24881a200000001144910345000000000090a20920000000001404411000000000020698a880000451464c90342,0x286a0260880000000001204411800000000024280a800000000004490149000000000089a069c00000000013140d3c000000000226982900000000004c5305300000000009a2209c0000000001034c53800000000000098a700000000004811050000000028482220860000000491044410800000000024898298000000134501034400000000009a204a60000000001144110000000009a20881a200000000005013244000000028d0824282000000051931491100000000a32629222800000012151610400000000000a2a6088000000051910485040000208b2a6890a080000000004d62140000000000092c628000000000013140d2c00000000022b192000000000004c5034e,0x226a600000004514340d080000000a3420992080000001654413240000000020c90a86800000137419458850400000008828a992000000000000013253000000024c8828680000013751a25441040000000002488827000000016590d1044000000024c9aa20840000000559304851000000009228a88200000000132455024300000002648aa048400000004d50548510000000000268882780000001125161042000000028c90a80880000000589454410c00000009a28a882180000001345012144000000028499220840000000515354851000000009028b082200000001364811044000000000090220a60000000001204413c00000009aa40882200000001245011044,0x2209920800000016590d104300000002ac88264800000000559104c90400000000000090a700000000000012152000000000092c20840000000001158810800000000020b10a100000000004c91044000000000082c428a00000000010588510000000000228a022000000000048110440000000000002808800000004114548504000000000208a0a2000000000000121400000000000822828a000000051920451040000000a32408a21000000000050504450000000000002408000000000000044d3800000000000089a780000000000011352]
def certCutCodes : List Nat := (List.range 1658).map limbCut
def certCuts := certCutCodes.map certCut
def limbSep : Nat → Nat := limb 13 #[0x814103042610a2052032048224806202a01481410a022424441808902850300914092046030203810c08810a106041840c40a206,0x40308450582232110828048421202c0260070062181050824209084888842501420b404480e406088902420a4284180830417030,0x806c06904242608a0884128411809909d046827401a01d04a80541520260390128038484022423209900d044022412008504c424,0x91841e01c00a043821800600c40680480281180130096032230018102c12a00600c00a105080e207103400a80b212802600a207,0x409c0b083409908b1055069034046822c23283221484541530151140260114218049889414a42a09202302181280490288832113,0x9802c006803201880e0054029016009e07010b11304c423502380b10cc864132218843903842c418805803801541c08d0162829,0x87021611382e4034019]
def certSepCodes : List Nat := (List.range 198).map limbSep
def certSeps : List (Nat × Nat) := certSepCodes.map fun v => (v % 128,v / 128)
def certSwaps : Nat → Nat → List Nat
  | 0,_ => []
  | k+1,n => if n = 1 then [] else n % 8 :: certSwaps k (n / 8)
def limbPerm : Nat → Nat := limb 46 #[0xa3000000000051000000004b8c0000000025c00000000098c0000000004b0000000001300000000000900000014d4680000000a6a3000000029c68000000014d400000000538c0000000029c00000002d468000000016a30000000054680000000029a000000000a8c00000000053000000005c68000000002d4000000000c680000000005a0000000001500000000000a000000000b8c0000000005c00000000018c0000000000b00000000003000000000001,0x1463440000000a2d1000000028c680000000145a00000012e3440000000968c000000026344000000012d1000000004a3000000000251000000025c68000000012d4000000004c680000000025a0000000009500000000004a000000a6a3440000005346300000014e3440000000a68c000000028b8c0000000145c00000016a3440000000b46300000002a344000000014d100000000518c0000000028b00000002e3440000000168c000000006344000000002d1,0x28b463440000145a31a00000516a3440000028b463000000a2d468000000516a3000004b463440000025a31a0000009463440000004a2d1000000128c680000000945a00000096a3440000004b46300000012a344000000094d100000002518c0000000128b00000012d468000000096a30000000254680000000129a000000004a8c000000002530000053463440000029a31a000000a2e3440000005168c000000145c680000000a2d4000000b463440000005a31a,0x8500000000004200000000438c0000000021c00000000088c0000000004300000000011000000000008000128b463440000945a31a00002516a3440000128b463000004a2d468000002516a30000253463440000129a31a000004a2e3440000025168c000000945c680000004a2d4000004a6a3440000025346300000094e3440000004a68c000000128b8c0000000945c00000094d4680000004a6a3000000129c68000000094d400000002538c0000000129c,0x151a200000000a68800000002888c00000001443000000171a200000000b444000000031a20000000016880000000051100000000028800000002438c0000000121c00000000488c000000002430000000009100000000004800000084d468000000426a3000000109c68000000084d400000002138c0000000109c00000010d468000000086a30000000214680000000109a00000000428c00000000213000000021c68000000010d40000000044680000000021a,0x29a31a20000014d111a000005171a200000028b444000000a21c68000000510d4000005a31a20000002d111a000000a31a20000000516880000001444680000000a21a000000971a200000004b444000000131a200000000968800000002511000000001288000000121c68000000090d40000000244680000000121a00000000485000000000242000005351a200000029a223000000a71a200000005344400000014438c0000000a21c000000b51a200000005a223,0x94438c0000004a21c00000484d468000002426a3000000909c68000000484d400000012138c0000000909c000145a31a200000a2d111a000028b51a200000145a22300000510d468000002886a3000025a31a20000012d111a000004a31a20000002516880000009444680000004a21a000004b51a200000025a223000000951a200000004a68800000012888c0000000944300000090d468000000486a30000001214680000000909a00000002428c00000001213,0x10a344000000084d100000002118c0000000108b00000010e3440000000868c000000022344000000010d100000000423000000000211000000020b8c0000000105c00000000418c0000000020b00000000083000000000041000945a31a200004a2d111a000128b51a200000945a22300002510d468000012886a3000129a31a20000094d111a000025171a200000128b444000004a21c68000002510d4000025351a200000129a223000004a71a2000000253444,0x21351a200000109a223000004271a200000021344400000084438c0000004221c000004351a200000021a223000000851a200000004268800000010888c00000008443000000871a2000000043444000000111a20000000086880000000211100000000108800000010438c0000000821c00000002088c000000010430000000041100000000020800000426a3440000021346300000084e3440000004268c000000108b8c0000000845c00000086a34400000043463,0x90888c0000004844300000486a3440000024346300000090a344000000484d100000012118c0000000908b00014d111a200000a6888d1000028871a200000144344400000510e3440000028868c00002d111a20000016888d1000005111a2000000288688000000a22344000000510d1000004871a2000000243444000000911a20000000486880000001211100000000908800000090e3440000004868c000000122344000000090d100000002423000000001211,0x128871a200000944344400002510e3440000128868c000121351a200000909a223000024271a200000121344400000484438c0000024221c00002426a3440000121346300000484e3440000024268c000000908b8c0000004845c000a2d111a20000516888d1000144351a200000a21a22300002886a3440000144346300012d111a20000096888d1000025111a2000001288688000004a22344000002510d1000024351a200000121a223000004851a2000000242688,0x213463440000109a31a00000422e3440000021168c000000845c68000000422d40000043463440000021a31a000000846344000000422d1000000108c680000000845a00000082e3440000004168c000000106344000000082d1000000020a3000000001051000000105c68000000082d4000000020c680000000105a0000000041500000000020a004a2d111a20002516888d1000944351a200004a21a22300012886a3440000944346300094d111a200004a6888d1,0x8211100000004108800000410e3440000020868c000000822344000000410d100000010423000000008211000109a31a20000084d111a000021171a200000108b444000004221c68000002110d4000021a31a20000010d111a000004231a20000002116880000008444680000004221a000004171a200000020b444000000831a200000004168800000010511000000008288000000821c68000000410d40000001044680000000821a00000002085000000001042,0x121111a2000009088688000024222344000012110d1000121a31a20000090d111a000024231a20000012116880000048444680000024221a0000243463440000121a31a000004846344000002422d1000000908c680000004845a00084d111a20000426888d1000108871a200000844344400002110e3440000108868c00010d111a20000086888d1000021111a2000001088688000004222344000002110d1000020871a2000001043444000004111a2000000208688,0x2510d111a20012886888d1004a21a31a20002510d111a0009443463440004a21a31a00484d111a20002426888d1000908871a200004844344400012110e3440000908868c000909a31a20000484d111a000121171a200000908b444000024221c68000012110d40001213463440000909a31a00002422e3440000121168c000004845c68000002422d400510d111a20002886888d1000a21a31a20000510d111a0001443463440000a21a31a00090d111a20000486888d1,0x82888c0000004144300000410d468000002086a30000008214680000004109a00000010428c00000008213000108b463440000845a31a00002116a3440000108b46300000422d468000002116a3000020b463440000105a31a0000041463440000020a2d1000000828c680000004145a00000416a3440000020b46300000082a344000000414d100000010518c0000000828b00000082d468000000416a30000001054680000000829a000000020a8c00000001053,0x105111a2000008288688000020a22344000010510d1000104351a200000821a223000020851a200000104268800000410888c0000020844300002086a3440000104346300000410a344000002084d100000082118c0000004108b000845a31a20000422d111a000108b51a200000845a22300002110d468000010886a3000105a31a20000082d111a000020a31a20000010516880000041444680000020a21a000020b51a200000105a223000004151a200000020a688,0x2110d111a20010886888d1004221a31a20002110d111a0008443463440004221a31a00410d111a20002086888d1000821111a2000041088688000104222344000082110d1000821a31a20000410d111a000104231a20000082116880000208444680000104221a0001043463440000821a31a000020846344000010422d1000004108c680000020845a00422d111a20002116888d1000844351a200004221a22300010886a3440000844346300082d111a20000416888d1,0x828b8c0000004145c00000414d4680000020a6a3000000829c68000000414d400000010538c0000000829c12110d111a20090886888d1024221a31a20012110d111a0048443463440024221a31a02422d111a20012116888d1004844351a200024221a22300090886a34400048443463004845a31a20002422d111a000908b51a200004845a22300012110d468000090886a3000908b463440004845a31a00012116a3440000908b46300002422d468000012116a3,0x105171a200000828b444000020a21c68000010510d4000105351a200000829a223000020a71a200000105344400000414438c0000020a21c00002084d468000010426a3000004109c68000002084d400000082138c0000004109c000828b463440004145a31a00010516a3440000828b463000020a2d468000010516a30001053463440000829a31a000020a2e3440000105168c000004145c680000020a2d4000020a6a3440000105346300000414e3440000020a68c,0x20a2d111a20010516888d1004144351a200020a21a22300082886a3440004144346300414d111a200020a6888d1000828871a200004144344400010510e3440000828868c000821351a200004109a223000104271a200000821344400002084438c0000104221c00010426a3440000821346300002084e3440000104268c000004108b8c0000020845c004145a31a200020a2d111a000828b51a200004145a22300010510d468000082886a3000829a31a20000414d111a,0x82110d468000410886a3004108b463440020845a31a00082116a3440004108b46300010422d468000082116a310510d111a20082886888d1020a21a31a20010510d111a0041443463440020a21a31a02084d111a20010426888d1004108871a200020844344400082110e3440004108868c004109a31a20002084d111a000821171a200004108b444000104221c68000082110d40008213463440004109a31a00010422e3440000821168c000020845c68000010422d4,0x82110d111a20410886888d1104221a31a20082110d111a0208443463440104221a31a10422d111a20082116888d1020844351a200104221a22300410886a34400208443463020845a31a20010422d111a004108b51a200020845a223]
def certPermCodes : List Nat := (List.range 720).map limbPerm
def certPerms := certPermCodes.map (certSwaps 15)
def certTabs : Tabs := (certCuts.map (mkCut true certSlices),certSeps,[],certPerms)
set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
theorem certTabsValid : TabsP true stopR stopT certTabs := by
  exact ⟨cutsGood validSlices (by decide +kernel),by decide +kernel,by decide +kernel,by decide +kernel⟩
end PEqualNP.Outside.L_meta_10393_aux

namespace PEqualNP.Outside.L_meta_10393_aux
abbrev PackedState := List Nat × List Nat
structure HintIndex where
  cuts : Array CutV
  seps : Array (Nat × Nat)
  kws : Array KwD
  perms : Array (List Nat)
  next : Array (List Nat)
def hintIndex (n : List (List Nat)) (t : Tabs) : HintIndex :=
  ⟨t.cuts.toArray, t.seps.toArray, t.kws.toArray, t.perms.toArray, n.toArray⟩
def projectedHint (i : Nat) : Nat :=
  if i < 30000 then i else 30000 + (i - 30000) % 1024
def indexedHint (u : Bool) (k : Nat) (ix : HintIndex)
    (xs : List Nat) (a b z : Nat) (ka kb : Bool) (i : Nat) : Bool :=
  if i < 10000 then
    match ix.cuts[i]? with
    | some c => cutEval u k xs a b z ka kb c
    | none => false
  else if i < 20000 then
    match ix.seps[i - 10000]? with
    | some q => sepEval u xs a b z ka kb q
    | none => false
  else if i < 30000 then
    match ix.kws[i - 20000]? with
    | some q => !u && Nat.beq (kidN xs a b z ka kb).length (k+1) && kwList (kidN xs a b z ka kb) q
    | none => false
  else
    match ix.perms[(i - 30000) % 1024]?, ix.next[(i - 30000) / 1024]? with
    | some perm, some st => beqL (sortN ((kidN xs a b z ka kb).map (permN perm))) st
    | _, _ => false
private theorem hintNotLT {a b : Nat} (h : ¬ a < b) : Nat.blt a b = false :=
  Bool.eq_false_iff.mpr (fun e => h (Nat.blt_eq.mp e))
set_option maxRecDepth 100000 in
theorem indexedHint_sound {u k n t xs a b z ka kb i}
    (h : indexedHint u k (hintIndex n t) xs a b z ka kb i = true) :
    hintOK u k n t xs a b z ka kb (projectedHint i) = true := by
  by_cases h₁ : i < 10000
  · have h₃ : i < 30000 := by omega
    cases hg : t.cuts[i]? <;>
      simpa [indexedHint, hintIndex, projectedHint, hintOK, h₁, h₃, Nat.blt_eq.mpr h₁, hg] using h
  by_cases h₂ : i < 20000
  · have h₃ : i < 30000 := by omega
    cases hg : t.seps[i - 10000]? <;>
      simpa [indexedHint, hintIndex, projectedHint, hintOK, h₁, h₂, h₃,
        hintNotLT h₁, Nat.blt_eq.mpr h₂, hg] using h
  by_cases h₃ : i < 30000
  · cases hg : t.kws[i - 20000]? <;>
      simpa [indexedHint, hintIndex, projectedHint, hintOK, h₁, h₂, h₃,
        hintNotLT h₁, hintNotLT h₂, Nat.blt_eq.mpr h₃, hg] using h
  · let j := (i - 30000) % 1024
    have e₁ : Nat.blt (30000 + j) 10000 = false := hintNotLT (by omega)
    have e₂ : Nat.blt (30000 + j) 20000 = false := hintNotLT (by omega)
    have e₃ : Nat.blt (30000 + j) 30000 = false := hintNotLT (by omega)
    simp only [indexedHint, h₁, h₂, h₃, ite_false, hintIndex, List.getElem?_toArray] at h
    change hintOK u k n t xs a b z ka kb (if i < 30000 then i else 30000 + j) = true
    simp only [h₃, ite_false, hintOK, e₁, e₂, e₃, Bool.cond_false, Nat.add_sub_cancel_left]
    cases ev : t.perms[j]? with
    | none =>
      change t.perms[(i - 30000) % 1024]? = none at ev
      simp [ev] at h
    | some perm =>
      change t.perms[(i - 30000) % 1024]? = some perm at ev
      rw [ev] at h
      cases es : n[(i - 30000) / 1024]? with
      | none => simp [es] at h
      | some st =>
        rw [es] at h
        exact List.any_eq_true.mpr ⟨st, List.mem_of_getElem? es, h⟩
def packedSlot (kk : Bool × Bool) : Nat :=
  if kk.1 then if kk.2 then 0 else 1 else if kk.2 then 2 else 3
def packedDigit (word index : Nat) : Nat := (word >>> (24 * index)) % 16777216
def packedBank (defaults : List Nat) (word : Nat) : List Nat :=
  defaults.map projectedHint ++ (List.range 16).map (fun j => projectedHint (packedDigit word j))
def packedKid (u : Bool) (k : Nat) (ix : HintIndex) (defaults : List Nat)
    (xs : List Nat) (a b z word op : Nat) (kk : Bool × Bool) : Bool :=
  Nat.blt k (Nat.add (Nat.add xs.length (Nat.add (bl kk.1) (bl kk.2))) 0) ||
    (let i := packedDigit word (4 * op + packedSlot kk)
     if i = 0 then defaults.any (indexedHint u k ix xs a b z kk.1 kk.2)
     else indexedHint u k ix xs a b z kk.1 kk.2 i)
def usableDefaults (u : Bool) (ix : HintIndex) (xs defaults : List Nat) : List Nat :=
  defaults.filter fun i =>
    if 10000 ≤ i ∧ i < 20000 then
      match ix.seps[i - 10000]? with
      | some sep => xs.all (same u sep)
      | none => false
    else true
def packedPair (u : Bool) (k : Nat) (ix : HintIndex) (defaults s : List Nat)
    (p : Nat × Nat × List Nat) (word : Nat) : Bool :=
  let localDefaults := usableDefaults u ix p.2.2 defaults
  (opsOf u).all fun op =>
    let z := nb op p.1 p.2.1
    mem1 z s || Nat.beq z 0 || Nat.beq z full ||
      keeps.all (packedKid u k ix localDefaults p.2.2 p.1 p.2.1 z word op)
theorem packedPair_sound {u k n t defaults s p word}
    (h : packedPair u k (hintIndex n t) defaults s p word = true) :
    pairOK u k n t s p (packedBank defaults word) = true := by
  apply List.all_eq_true.mpr
  intro op hop
  have hh := List.all_eq_true.mp h op hop
  dsimp only at hh ⊢
  simp only [Bool.or_eq_true] at hh ⊢
  rcases hh with h | h
  · exact Or.inl h
  right
  apply List.all_eq_true.mpr
  intro kk hkk
  have hk := List.all_eq_true.mp h kk hkk
  simp only [packedKid, Bool.or_eq_true] at hk
  simp only [kidOK, Bool.or_eq_true]
  rcases hk with hcap | hk
  · exact Or.inl hcap
  right
  apply List.any_eq_true.mpr
  split at hk
  · obtain ⟨i, hi, hw⟩ := List.any_eq_true.mp hk
    exact ⟨_, List.mem_append_left _ (List.mem_map_of_mem (List.mem_filter.mp hi).1), indexedHint_sound hw⟩
  · have ho : op < 4 := by
      cases u <;> simp [opsOf] at hop <;> omega
    have hs : packedSlot kk < 4 := by
      obtain ⟨ka,kb⟩ := kk
      cases ka <;> cases kb <;> decide
    have hm : 4 * op + packedSlot kk ∈ List.range 16 := List.mem_range.mpr (by omega)
    exact ⟨_, List.mem_append_right _ (List.mem_map_of_mem hm), indexedHint_sound hk⟩
def packedZip (f : Nat × Nat × List Nat → Nat → Bool) : List (Nat × Nat × List Nat) → List Nat → Bool
  | [], _ => true
  | _ :: _, [] => false
  | p :: ps, word :: rest => f p word && packedZip f ps rest
theorem packedZip_sound {f g bank ps hs}
    (hf : ∀ p word, f p word = true → g p (bank word) = true)
    (h : packedZip f ps hs = true) : allZip g ps (hs.map bank) = true := by
  induction ps generalizing hs with
  | nil => rfl
  | cons p ps ih =>
    cases hs with
    | nil => contradiction
    | cons w ws =>
      obtain ⟨h₁,h₂⟩ := Bool.and_eq_true_iff.mp h
      exact Bool.and_eq_true_iff.mpr ⟨hf _ _ h₁, ih h₂⟩
def packedStateOK (u : Bool) (T : Nat) (k : Nat) (ix : HintIndex)
    (defaults : List Nat) (st : PackedState) : Bool :=
  asc st.1 && !(mem1 T st.1) &&
    packedZip (packedPair u k ix defaults st.1) (pairs st.1) st.2
theorem packedState_sound {u T k n t defaults st}
    (h : packedStateOK u T k (hintIndex n t) defaults st = true) :
    stOK u T t k n (st.1, st.2.map (packedBank defaults)) = true := by
  obtain ⟨hb,hc⟩ := Bool.and_eq_true_iff.mp h
  exact Bool.and_eq_true_iff.mpr ⟨hb, packedZip_sound (fun _ _ h => packedPair_sound h) hc⟩
def PackedLevel (u : Bool) (T k : Nat) (states : List PackedState) : Prop :=
  ∀ st ∈ states, Impossible u (W T) k (st.1.map W).toFinset
theorem packedLevelStep {u R T E t k prev st defaults}
    (hb : baseOK T R E = true) (ht : TabsP u R T t) (hn : PackedLevel u T k prev)
    (hc : packedStateOK u T k (hintIndex (prev.map Prod.fst) t) defaults st = true) :
    Impossible u (W T) (k+1) (st.1.map W).toFinset := by
  apply stStep hb ht _ (packedState_sound hc)
  intro s hs
  obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hs
  exact hn _ hq
theorem packedLevelAll {u R T E t k prev states defaults}
    (hb : baseOK T R E = true) (ht : TabsP u R T t) (hn : PackedLevel u T k prev)
    (hc : states.all (packedStateOK u T k (hintIndex (prev.map Prod.fst) t) defaults) = true) :
    PackedLevel u T (k+1) states := by
  intro st hs
  exact packedLevelStep hb ht hn (List.all_eq_true.mp hc st hs)
theorem packedAllChunks {α : Type} {states : List α} {f : α → Bool} (c n : Nat) (hc : 0 < c)
    (hl : states.length ≤ n * c)
    (h : ∀ i, i < n → ((states.drop (i*c)).take c).all f = true) : states.all f = true := by
  apply List.all_eq_true.mpr
  intro x hx
  obtain ⟨j,hj,rfl⟩ := List.getElem_of_mem hx
  have hi : j / c < n := (Nat.div_lt_iff_lt_mul hc).mpr (by omega)
  apply List.all_eq_true.mp (h _ hi)
  have eq : j / c * c + j % c = j := by rw [Nat.mul_comm]; exact Nat.div_add_mod j c
  refine List.mem_of_getElem? (i := j % c) ?_
  rw [List.getElem?_take_of_lt (Nat.mod_lt j hc), List.getElem?_drop, eq]
  exact List.getElem?_eq_getElem hj
theorem packedLowSearch {u R T E K D} (hB : baseOK T R E = true) (hI : PackedLevel u T K D)
    (h : (D.map Prod.fst).contains (R.map xN) = true) : LowN u R T (K+1) := by
  apply lowOf hB
  simp only [List.contains_eq_mem,decide_eq_true_eq] at h
  obtain ⟨q,hq,e⟩ := List.mem_map.mp h
  have found := hI q hq
  rw [e] at found
  simpa only [rootsW,List.map_map,Function.comp_def] using found
end PEqualNP.Outside.L_meta_10393_aux

namespace PEqualNP.Outside.L_meta_10393_aux
def shortWordTable : Array Nat := #[0xeeeeeeee00000000aaaafffe00000000aaaafefe00000000aaaaaafe00000000aaaaaaaa00000000a8a8a8fc0000000000ffffee000000000000fffe000000000000fefe000000000000eeee000000000000aafe000000000000aaaa00000000000000fe00000000000000ee00000000000000aa000000000000000e,0xfff00000fff00000ffee0000ffee0000fafa0000fafa0000eeeefff0fffe00000000fffffffe00000000fffffffa00000000fffffff000000000ffffffaa00000000fffffefe00000000fffffcfc00000000fffefffe00000000fffefefe00000000fffcfffc00000000fffafffa00000000fefefefe00000000eeeefffe,0xf0f0f0f0f0f0f000f0f0f0f0f0e0f0e0f0f0f0f0f0a0f0a0f0f0f0f0e0e0e0e00ff00ff00ff00f000ff00ff00fe00fe00ff00f000ff00f000fa00fa00fa00fa0000ffffffffeeee0000ffffffffaaaa0000ffff0000fffe0000ffff0000fefe0000ffff0000eeee0000fffe0000fffe0000fffc0000fffc0000fffa0000fffa,0xaaaaaaaafffefffeaaaaaaaaffaaffaaaaaaaaaafefefefeaaaaaaaaeeeefffeaaaaaaaaeeeeeeeeaaaaaaaaafaaafaaaaaaaaaaaaaafffeaaaaaaaaaaaafefeaaaaaaaaaaaaaafeaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa8aaaaaaa8aaaafffc8888888888888888333333333332333233333333323232320ffa0ffa0ffa0ffa,0xccccccccfffffffcccccccccffffffccccccccccffccffccccccccccfcfcfcfccccccccccfcccfccccccccccccccfcfcccccccccccccccccaaaafffffffffefeaaaaffffaaaafefeaaaafffeaaaafffeaaaafffaaaaafffaaaaaffaaaaaaffaaaaaabbbaaaaabbbaaaaaaaaafffffffeaaaaaaaafffffffaaaaaaaaaffffffaa,0xf0f0f0f0fafafafaf0f0f0f0f3f0f3f0f0f0f0f0f0f0fafaf0f0f0f0f0f0f0f0eeeefffeeeeefffeeeeeffeeeeeeffeeeeeeeeeefffffffeeeeeeeeefffefffeeeeeeeeeffeeffeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee0eaeaeaeaeaeaeaeadddcdddcdddcdddcdcdcdcdcdcdcdcdcccccfffcccccfffcccccffccccccffcc,0xfcfcfcfcfcfcfcfcfcccfcccfcccfcccfbfafbfafbfafbfafafafffafafafffafafafafafffafffafafafafafafafafaf8f8f8f8f8f8f8f8f3f3f3f0f3f3f3f0f3f2f3f2f3f2f3f2f3f0f3f0f3f0f3f0f2f2f2f2f2f2f2f2f1f1f1f0f1f1f1f0f0f0fffcf0f0fffcf0f0fffaf0f0fffaf0f0f0f0fffffff0f0f0f0f0fffefffe,0xffaaffaaffaaffeeffaaffaaffaaffaaff0fff0fff0eff0eff0fff0eff0fff0eff0fff0aff0fff0aff0fff00ff0fff00ff0eff0eff0eff0eff00ff00ffffffeeff00ff00fffefffeff00ff00ff0fff0aff00ff00ff00ffeeff00ff00ff00ff00ff000000ff000000fefefefefffffffefefefefefefefefefeeefeeefeeefeee,0xfff0fff0fff0eee0fff0f0f0fff0f0f0ffefffeeffefffeeffeeffeeffeeffeeffeeeeeeffeeeeeeffeaffeaffeaffeaffddffccffddffccffcfffceffcfffceffcfffccffcfffccffccffccffccffccffccccccffccccccffafffaeffafffaeffafffaaffafffaaffaeffaeffaeffaeffaaffaafffefffeffaaffaaffeeffee,0xffff0000ffff00aaffff0000ffff000affff0000ffff0000ffff0000fffe0000ffff000000000000fffefffefffefffefffcfffcfffcfffcfffafffafffefffefffafffafffafffafffafafafffafafafff5fff0fff5fff0fff3fff0fff3fff0fff1fff1fff1fff0fff0fff0fffffffefff0fff0fffefffefff0fff0fff0fff0,0xffffaaaafffffffaffffaaaafffffefeffffaaaaffffaaaaffffaaaafffcaaa8ffff8888ffff8888ffff00ffffff00eeffff00ffffff00aaffff00feffff00feffff00faffff00faffff00eeffff00eeffff00aaffff00aaffff000fffff000affff0000fffffffeffff0000fffffffcffff0000fffffefeffff0000ffff00ee,0xfffff5f0fffff5f0fffff3f3fffff0f0fffff0f0fffff0f0fffff0f0f0f0f0f0fffff000fffff000ffffeeeefffffffeffffeeeefffffefeffffeeeeffffeeeeffffeeeeeeeeeeeeffffddddffffdcdcffffcfcfffffccccffffccccfffffefeffffccccffffccccffffccccccccccccffffc0c0ffffc0c0ffffaaaafffffffe,0xffffffaaffffffeeffffffaaffffffaaffffffaaffaaffaaffffff0effffff0effffff0cffffff0cffffff00fffffffeffffff00ffffffeeffffff00ffffff44ffffff00ffffff00ffffff00ff00ff00ffffff0001010100fffffefefffffefefffffefefefefefefffffcfcfffffcfcfffffafafffffafafffffafafafafafa,0xffffffff000000eeffffffff00000000fffffffefffffffefffffffcfffffffcfffffffafffffffafffffffafffafffafffffff0fffffff0fffffff0fff0fff0ffffffeeffffffeeffffffeeffeeffeeffffffeaffffffeaffffffccffffffccffffffccffccffccffffffc0ffffffc0ffffffaeffffffaeffffffaafffffffe,0xffffffffccccfffcffffffffccccfcfcffffffffccccdddcffffffffccccdcdcffffffffccccccccffffffffaaaafffeffffffffaaaafefeffffffffaaaaaafeffffffffaaaaaaaaffffffff55555500ffffffff11101110ffffffff00fe00feffffffff0000fffeffffffff0000fff0ffffffff0000fefeffffffff0000eeee,0xfffffffffefefefefffffffffeeefeeefffffffffdfdfdfcfffffffffcfcfcfcfffffffffcccfcccfffffffffbfafbfafffffffffafafffafffffffffafafafafffffffff0f0f0f0fffffffff000f000ffffffffeeeefffeffffffffeeeeeeeeffffffffeee0eee0ffffffffdddddddcffffffffdddcdddcffffffffdcdcdcdc,0xffffffffffeeeeeeffffffffffeaffeaffffffffffccffccffffffffffccf0c0ffffffffffccccccffffffffffc0ffc0ffffffffffaeffaeffffffffffaaffeeffffffffffaaffaaffffffffffaacc88ffffffffffaaaaaaffffffffff55ff00ffffffffff0eff0effffffffff00ffeeffffffffff00ff00ffffffffff000000,0xffffffffffff3300ffffffffffff0e0effffffffffff0c0cffffffffffff0a0affffffffffff00fcffffffffffff00eeffffffffffff00aaffffffffffff0044ffffffffffff0000fffffffffffefffefffffffffffcfffcfffffffffffafffafffffffffffafafafffffffffff0fff0fffffffffff0f0f0ffffffffffeeffee,0xfffffffffffffff0ffffffffffffffeeffffffffffffffccffffffffffffffaaffffffffffffff00fffffffffffffefefffffffffffffcfcfffffffffffffafafffffffffffff0f0ffffffffffffeeeeffffffffffffccccffffffffffffc0c0ffffffffffffaafeffffffffffffaaaaffffffffffff8888ffffffffffff3330,0xfffffffffffffffefffffffffffffffcfffffffffffffffa]
def shortWire (i : Nat) : Nat :=
  let w := (shortWordTable[i/16]?.getD 0 >>> (64*(i%16))) % (1 <<< 64)
  w + (w <<< 64)
def shortWires : Nat → Nat → List Nat
  | 0, _ => []
  | n+1, s => shortWire (s%512) :: shortWires n (s >>> 9)
def readCutDelta (s : Nat) : Nat × Nat :=
  if (s >>> 0) % 2 = 0 then (0+(s >>> 1) % 4,s >>> 3) else
  if (s >>> 1) % 2 = 0 then (4+(s >>> 2) % 16,s >>> 6) else
  if (s >>> 2) % 2 = 0 then (20+(s >>> 3) % 64,s >>> 9) else
  if (s >>> 3) % 2 = 0 then (84+(s >>> 4) % 256,s >>> 12) else
  if (s >>> 4) % 2 = 0 then (340+(s >>> 5) % 256,s >>> 13) else
  (596+(s >>> 5) % 1024,s >>> 15)
def readChildDelta (s : Nat) : Nat × Nat :=
  if (s >>> 0) % 2 = 0 then (0+(s >>> 1) % 2,s >>> 2) else
  if (s >>> 1) % 2 = 0 then (2+(s >>> 2) % 16,s >>> 6) else
  if (s >>> 2) % 2 = 0 then (18+(s >>> 3) % 64,s >>> 9) else
  if (s >>> 3) % 2 = 0 then (82+(s >>> 4) % 128,s >>> 11) else
  if (s >>> 4) % 2 = 0 then (210+(s >>> 5) % 128,s >>> 12) else
  (338+(s >>> 5) % 512,s >>> 14)
def readPermRank (s : Nat) : Nat × Nat :=
  if (s >>> 0) % 2 = 0 then (0+(s >>> 1) % 8,s >>> 4) else
  if (s >>> 1) % 2 = 0 then (8+(s >>> 2) % 32,s >>> 7) else
  if (s >>> 2) % 2 = 0 then (40+(s >>> 3) % 64,s >>> 9) else
  if (s >>> 3) % 2 = 0 then (104+(s >>> 4) % 64,s >>> 10) else
  if (s >>> 4) % 2 = 0 then (168+(s >>> 5) % 64,s >>> 11) else
  (232+(s >>> 5) % 256,s >>> 13)
def shortPermTable : Array Nat := #[0x200301007e248104b1e02582048168031300681e260f0010991e8030840802490004061e01800800,0x9000f270f12d4bb174d5904a8484224d8a52d0bd0552d7083c0a09f03479049082e0a0269b002807,0x26c23940b93d94a02c257247f538913c9c65a5b1064974ccd30454b250050902d48c4807c2707132,0x2084390cf37007c0e6799849d72ca2760d2925353d0a31143d5ac814a65827939304b170c5103884,0x80186441576cc8a06cbf52160284296e5c52f846534c94456e439c8180131ed222e8494be5b38438,0x2c0bc218880fd24050e7748ac4c44194a01365512a4aa5a925098c016c93660476650f2c9e962659,0xc9884ad5020d3b4e16d571d16f1284f0b3344e8a61db779da1a571784fa4d1e3594d8110f5298f7,0x32834169d44a9cd92a445102a350636a0de2b8b76b54114e7042a4f109d371e567104b320507a16c,0x75e3da203b32dae6aa99342896ee5477061788db61cf905cfb290339093e29cdf3e0cf774c244942,0x5ca28809705beb50b095641134791a41ccc4262b0bc3a4150694470059b59164b6e9b4318e02d966,0x35d4fa5e1f59dbf57545162909d8fe65517765493a45e172b0b20591c63eacd268783167da36758a,0x588ab3bd969e9792b5379550440c853351d5491c58c8757cd619d16af5431488c3104c6f5cc8802e,0x6803e691a769578842318a5ea792c42bc3730d537595e129276150d1f51491cc50d62662dac65173,0x24c9202b8118c6859b3acea871807e036]
def shortPerm (i : Nat) : Nat :=
  (shortPermTable[i/32]?.getD 0 >>> (10*(i%32))) % 1024
def shortNexts : Nat → Nat → Nat → List Nat
  | 0,_,_ => []
  | n+1,p,s => let (d,r) := readChildDelta s
               let (m,t) := readPermRank r
               (30000+1024*(p+d)+shortPerm m) :: shortNexts n (p+d) t
def shortCuts (nn : Nat) : Nat → Nat → Nat → List Nat
  | 0,_,s => shortNexts nn 0 s
  | n+1,p,s => let (d,t) := readCutDelta s
               (p+d) :: shortCuts nn n (p+d+1) t
def localState (s : Nat) : PackedState :=
  let n := s%16
  let r := s >>> (4+9*n)
  let a := r >>> 1
  (shortWires n (s >>> 4),
   if r%2=1 then [2*a+1] else
     let bits := a % 4096
     let rest := a >>> 12
     let b := rest >>> bits
     (2*(rest % (1 <<< bits))) :: shortCuts ((b >>> 6) % 64) (b % 64) 0 (b >>> 12))
def local4g0 : List Nat := [0x8018144090aff6caccfc115,0x11c104880a32786b38e2565,0x93c359c714,0x42a2146bd431c430115,0x4c0424402b2d7c30520565,0x42a2146bd431c480115]
def local5g0 : List Nat := [0x821404409864d01639bcd4566,0x4b7d5352200dd14c5005d2980b1cd4565,0x92044480362f01639bcd4066,0x140e4c7c6680127003a2f0161264d4566,0x212201c11462f0161230d4566,0xb4401422162f146ca18de366,0x96044480364f01639bc6c066,0x8e101420962f1461218de366,0x12786b1cd4565,0x10c082840362f1563a64d4566,0x209200c09464f10639bcac366,0x92200c11162f1262218de366,0x13b8befdd35821c1380352886b1cde365,0x92044480362f12639bc6c066,0x10c082840362f014ea64d4066,0x960414203602bd59a686c156,0x100302881215febd599f8e8116,0x10c082840663701639a892366,0xa9a00500122f124aa18de366,0x434203821862efc4aa18de366,0x4261a0094d800724b1286b1cde366,0x180080022f0d6a1f8b80f6,0x8e042440362f126ca30de366,0x60400b0019bcc761264d40f6]
def local5g1 : List Nat := [0x300028009bcbd5c218fc116,0xb02085011645126ca18de366,0xa204850035bcd4672f5200f6,0x3cbf31fa801c28042531286b1cde366,0x13b000f001a2f0d6a1f8b8066,0x238403842462f126a230de366,0x8e100c10962f1261230de366,0x11c201c2125bcc76125cd40f6,0x416202c1185bcd45e9f8ac116,0x115082c0865bcce5ea18fc116,0xb020850116451261218de366,0x11c202c4125bcd45ea5d200f6,0xa9a00500122f124a218de366,0x1024122df8bd599f8e8116,0x12c105820a64f017bacca6366,0x273e2b002800a2f156ca18de366,0x826405021864f0d639c4de366,0x50b8a1c3af84150e00352786b38de365,0x140e5c7c00e4010de6a305200f5,0x138109900a64f1086b1cde366,0x9604342035bcd9599f8e2116,0x451400d3fcd08388b00048de6caccfc115,0xeaf46811802d06600824f0d6e31cde366,0x138109900a64f0d8631cde366]
def local5g2 : List Nat := [0x138109900a6632786b1cde366,0x10c0828406602bd59a647e366,0x8604142035eeb356a68e8116,0x41320281185eed4569d0e2116,0x8c08244035bcc74b9bc400f6,0x238209101464f0d639c4ac366,0x8e042440362f126ba30de366,0x28dcb1f9a0097801d2b7bacca6365,0x1003028812162cc75e9246c156,0x1003028812162cc72e1246c086,0x427140090ed500922f016e31cde546,0x153400f40005a5f176c218de366,0x349e9900389004a2e863f170ac276,0x4a4401379805a53176c218de366,0x1006049022262ac75e9247e366,0x100508840a45feb3569d058116,0x100302881215fed9599d06c116,0x9420142115bcdb43170400f6,0x8060450212602dc2e1246c346,0x204c122db6b33a170340f6,0x860414203647016397092366,0x8a042440364f026397092366,0x209101408c5bcb3569d0b8106,0x651279004c62806a2f016731cde546]
def local5g3 : List Nat := [0x19cfa9a50058134480aa2ed84ba18de366,0x116001caa80622ec348218de366,0x6051003c0004a2ed8431c4de366,0x29c00500124f2580b1ca4366,0x238405882464f016a31ca4366,0x860494203624c75e9247e366,0x101604902225f8d9599d06c116,0x98202c4115bcce43170400f6,0x100e08a04246249d431bc6c156,0x854428d7a743892430116,0x33648283e6da81163a5007a2f126ca18d4566,0x411400c0a862f1260a18d4566,0xa8049100362f125c218d4566,0x981044809658fc5ea18de366,0x1180c00a40111786b0520565,0x8604142035eec7599f8e2116,0x221202409462f1061240ac366,0xaa400c121656ff5ea18de366,0x10c082840662f015ea646c066,0x92044480362f124ea18d4066,0x100302881215fec75ea186c116,0x92044480364d015ea3c92366,0x860414203602bd4d1246c086,0x130109100a64f0d63a30de366]
def local5g4 : List Nat := [0xb42014211656fc60a18de366,0x9808488055bcd460a40d40f6,0x218105080c5bcd9599f8ac116,0x8604142035bcd963accfc116,0x86041420364eeb569d0e2076,0x100604902225f8c75ea186c116,0x20480a1d8eb33f170320f6,0x209101408c64b1780af4a6366,0x100c08a04246249d431a8ac156,0x1003028812158ebd431bc6c1b6,0x8a042440364f1063a30de366,0x10668146e4efc67811a01d528c0712580af4a6365,0x20480a1db2b33f170320f6,0x607f0b0028008b33f170320f5,0xa80491003656f75c218d4566,0x82140540b064d015ea18d4566,0x92045480362f015ea18d4066,0x43140240a862f1460a18de366,0x5d24068ffca04581d2500aa2f0d63a64d4566,0x230209101464f015c230de366,0x131101408a656f860a18de366,0x209101408c64b015eacca6366,0x434203821862efc5fa18de366,0x13008a1006608fc5ea18de366]
def local5g5 : List Nat := [0x803405812464ae75e9d0ac116,0x428221dee9d431a8240f6,0x2060224deec7599bc7e366,0x2050122dd6bd56a30e8116,0x2050122dd6ce5e9d0ac116,0x428214dbcbd431a8400f6,0x2050122dd6d9569d0ac116,0x40c418dbcc7481bc400f6,0x13408608065eec7612186c116,0x20500a1de8bd599f8e8116,0x43020a1018656fc61240ac366,0x12c105820a64f015eacca6366,0x10c0828406657177bacca6366,0x131400c0a2656ff60a4092366,0x443e33c08c01297805a4f0d6cb50de366,0x2044122df8c159ab4e8116,0x222b002800a2f07639f8de546,0x353fc0a2009a100522ec04ba18de366,0x7458007080322ed3481c4ac366,0x1ac002800a2ed6481bcac366,0x751002800a2ed8461bcac366,0x211400c0a462f1267230de366,0x118104880a65af860a4092366,0x238403842462f126a218a4366]
def local5g6 : List Nat := [0x130109100a64f0d63a18a4366,0x43020a1018656f85e9b492366,0x230209101460ece5f24092366,0x2060122df8c75e9247e366,0x20480a1df0d9599d06c116,0x428091dbcc143170400f6,0x20500a1de8d9599d06c116,0x40c214dbcd943170400f6,0x238209101465f2786b50de366,0x13c4018222656fc60a5c92366,0x118104880a5bcd460a5cb80f6,0x218105080c5bcd95c2186c116,0x8604142035bcd96a2b4e8116,0x204c0a1d84ad3a170320f6,0x2048224deec1599f8e8116,0x858428d7a74389386c116,0x204c0a1d66742e104320f6,0x1024224dee9d431bc7c116,0x1024224dee9d431bc88116,0x1024224dee9d431bc74116,0x2044122dd6ad3a1703c116,0x1028224deec760a186c116,0x2048224deedb599d06c116,0x822404813064b126ca18de366]
def local5g7 : List Nat := [0xa2048500362f016a338b80f6,0x8001eeeb612b4e8116,0x857c26801ccc0062572786b50de366,0x204c224deec25c2b4e8116,0x54b957fe400e3003a59278936492366,0x6ea00500122f0d6a24098366,0x1030122dd69d481587c116,0x1030122dd69d4815c6c116,0xdd400a001a2f0d6a240a4366,0x43020a101863ef860a4092366,0x1a80080022f0d6a24094366,0x2050428e02d45e9247e366,0x2050122dd6d95c1d06c116,0x40c418dbcc74c970400f6,0x1030122dd69d480d83c116,0x1030122dd69d4815888116,0x1030122dd69d481686c116,0x1028224dee9d431a874116,0x2050428e02ce5e98092366,0x20480a1d66973a170320f6,0x128203021262f126e2ccdc366,0x10b000e9003a4f26631bcac366,0x35002800a57286024092366,0x69400e9003a57286c1a892366]
def local5g8 : List Nat := [0xdb5001d080422f1563a64de546,0xb8403041165917481a892266,0xdb5001d080422f1569264de366,0x1028830e4517431f8b8276,0xdb5001d08042491563a64de366,0x80940440b06029d3f1bca8156,0x1220881185d6c72e1586c096,0x80340440b05d6bb481586c156,0x80940440b06029d451bc6c156,0x80340440b05f69d481586c156,0x13008604065eec7429bc6c116,0x80340440a85d6c7471586c116,0x80540640a85eec74b1246c116,0x8054044098622c7351246c116,0x2060224deec7351246c146,0x20500a1de8bd59ab4e8116,0xcd200500122f016cb5098366,0x100e04902225f89d481406c116,0x100e04b02225f89d481346c116,0x10280a1df09d481406c116,0x10280a1df09d481346c116,0x1028224dee9d4b9346c116,0x1028224dee9d4b9406c116,0x43740608285bcc260ae0e8116]
def local5g9 : List Nat := [0x1024122df89d4ba30e8116,0xc4540098cff80922f126e364dc366,0x105d4d004e42a808a2f126db64dc366,0x4d002800a57263f17092266,0x99002800a5725431706c276,0x1009a0091e9f8092572893b6092366,0x68a9a009a4800724b1789364dc366,0x882a9a009a4800092451789364dc366,0x84783a5004a96806a57276c25c92366,0x54d0029802a57276d24092366,0x8c00b001a4b126caccdc366,0x216001d080424f25631c4ac366,0x43f279003c002a56f86ca5892366,0xf49e400ec003a57136c9a892366,0x21240504245d6d4639706c096,0x80c40501306029d4c9bca8156,0x80c4058130602b14c9bc6c156,0x1031021dce9d4812460156,0x80e40501306149d4c9bc6c156,0x406402811864eb23a1bc6c076,0x403402409864abc3a1586c076,0x405402409864ec6351246c076,0x405402409864ec03a1246c076,0x1028224dee9d430d85a116]
def local5g10 : List Nat := [0x1c800800256f86da3892366,0x6cbe91003b002a4f26631c492366,0xd4fd56400e1003a57266b17092366,0x100302881215e89d481b86c156,0x100502d0211650bc3a1246c076,0x100302881215fc9d481246c156,0x100302881215e8c72e1246c096,0x1003028811164cbc3a1246c076,0x427140090ed50092490a6e31cde366,0x20340140a4616c72e1586c096,0x100302881215e8bb481246c156,0x1003028811164cc62e1246c076,0x1003028812161ec72e1246c096]
def local6g0 : List Nat := [0x3e7859f0b792bc2bf923ca99ebc1590b269832c4a20542021dcad86449c1a3054202f9e167c2de4af0afe48f2a67af05642c9a60cb128815080372aa0c0208a912ad330041028200e38a08c38e46d6bcda59dcfb09e17c0aa9bd50b87e95c4ca18d91ac884194513c4f23a66b44ad1b95332e70819659220459650dfa2f01639bcd4566,0x18be18f8acc3f983e54e5ff8bebc05cf07ff036881b0253cd1ba8964703a45e02d9639bcac367,0x4af2a7150a65896a1cab5017ef80631333ced8ad173833a03b8d66c8e9bc9aaaa2817240408757ad239c5a7208cc65c0c73b9a7519ec32105285b24f01639bcac366,0x10428088130ca202c7379a892367,0x218105080cc5e02dc639a892367,0x22720c5018c6d2e75442ac72e70674072a7b17d5223933838a7c723365b226d22a99c9a03525301639a892366,0x1240889006c5e02c7379706c067,0x1240889006c5dee9d431f8b8067,0x64f93be63f80c99e5749418b94dee2501d3798ebd4ca40ac0b7,0xf85bf9270684d1c205248009aa302549e4501639a892367,0xe664cdf197f12f04438dbde308d007b401b52e008979d7127adcaf160921534e3f210e4090852046508f991356113143de8085840e50c0231938bd9f585233907ba2f126ca18de366,0x54b913cbdfa82680349000972b02348a02d9639a892367,0x245f2efbaeab201500982372365403145e1ac248218de367,0x4bc110f04ef1c1400c09054000002b5c0c711de1eb9e51a92944021004140e0f238866b167398aa26b3895e76a9134205a22f1261218de366,0x143d2644f2b7c846a08d329482e01d45e02d9639a892047,0x306e19ea134112528c001645dbcce431f8b80f7,0x10c0828406c5e02d9639c492367,0x144090a006b798ebd4ca406c0f7,0x44d967f94bc9aa13d183538a317cb9c9650f9b270c3e225011c9348ab703b49e4b01639a892367,0x64d1a132433647e4b769440837890056312402b37966ad481d0ac117,0x2708091044c9602d9639a892367,0x5df540b34456dafd1a49018b2434a5f01d3799cbd431f8b80f7,0xc9610de0ffca60892d400d4a202d9639a892367,0x314dc9f930104489900c45e0e9d431f8b8067]
def local6g1 : List Nat := [0x143c2ff9d55630f5b0592413431f462550178902a4be2f01639a892367,0x41053b843a770872502adc2308c0846014d28148000005cb806ae14f6300aa3e63a35a2a470139010408d22510ca40f0ce08d10918c1081222217c551d16078555c15b0cb6170da105656104e52786b1cde365,0x3d638f30104c5f782f26ee4fb4e0344da70340c645d07a4001a8000a80069c8530d001102b0018000501eeb3569d0e2116,0x104880a0430c9e02c7389a892367,0x3ae12c01f82356973a943955079ef0af901d9738716e831e838836204600295172985934a73a11382166a3cc94849a4f01639c492366,0x402a4022c0184f0af737127cac08110d84102c58c073a8ef71ce7834e9388a530409bcd45ea406c0f6,0x47080a1048c9e02d4639a892367,0xeb25040bf080c11cbd4073490654de0ae29db84778f71d9a4130808210c6c78dc64195031ced59ca518d23304924f0d639a892366,0x2ef8b7612960d78ae365d61ed3d08408854418bbe300335d34a922aeb28301bcd45e9f8b80f6,0x4704122028ca64f01639a892367,0x12c0828406b797ab33f1d0e2117,0x100a40fe4df43918af8efb37028b108c3888cb2001a800231bcbd599f8e8116,0x19c651feedd99451582365298501749e02db639a892367,0x10428088130c9a02c73897092367,0x4604122028c9dbc9d431f8b8067,0x4704122028c9e02c73895892367,0x4224028128caa02c72e15892367,0x10c0828406caa02c73897092367,0x10c0828406c5e02dd6397092367,0xa855ae58e46e66319c14ff558a2c00104801028b239820255016397092366,0x10c0828406c5e02c72e1246c077,0x1140848806cadbc9d3a1bcd4027,0x10c0828406c5e02cc6397092367,0x1dbe6ba7b9efa6f321a15400ba20a02202544cc41baa932a82ea3d016397092366]
def local6g2 : List Nat := [0x2f714c9bd73c668670f972045171202333389746503a45e02d763970ac337,0x1240889006c9a02d76397092367,0x105680d8860cb1bc9d431f8b8067,0x20a101810cbfdcebd599d06c117,0x4704122028c9e20c72e15892367,0x2284030406b79b8ad481d0b80f7,0x4122028118b798ebd2b1246c157,0x10c0828406b798ebd4d240920b7,0xe6fd1f460059821401448a02d76397092367,0x46680a1048ca1bcb3569d0b80f7,0x228109100cca645016397092367,0x10c0828406b798ebd481246c157,0x1140848806c9e02d76397092367,0x4122028118b79b6b3569d0b80f7,0x10c0828406c5deebd3a1246c077,0xf99eb900b262e30e579e24f6501c5a125c54b802980301e9febd599d06c116,0x228109100cca602ce6397092367,0x113247133235231dcf1c033d73c7643108880d3db112242299c9a826a53076397092366,0xd187eba0dbdacbc1df26f4f49882c088a908b1a03801c1bcdc569d0b80f6,0x1240889006caa4d016397092367,0x10c0828406b798ebd4d1246c157,0x998192f2ee5cf43729a40939aaa423b4888892020231bcc75e9246c156,0x10c0828406c5dfebd3a1246c077,0x10c0828406c5e02c72e12470367]
def local6g3 : List Nat := [0x1140848806c5e02c96397092367,0x3dc5428cc2fc867d1f7c5669347d450aa0c5ca609405200b069dc878cea588e9603a235016397092366,0x1240889006c5e24c72e1246c067,0x1240889006c5dee74248d852067,0x1240889006c9e02c72e1246c067,0x11c0828406c5dbc9d4821870367,0x218105880cc5dbc9d4c9f8b8067,0x1181048806c5dbc9d3a1bc50067,0x2f714ca6b9e33abd87d2a2851601312222891746503e45e02d963970ac337,0x2704112024ca64b01639a892367,0x170410a022caa45016397092367,0x1140848806cadeebd3a1246c027,0x11c0828406c5dbc9d482186c077,0xea7e00d1000d440936480f1bc9d482186c076,0xfd877dfd87546005e7a73c43d9a44239b291549215c1088899827a2f01351a092366,0x4122028118b798ebd2c15892367,0x9f80794d2005e124b693600149bcc75e96092366,0x675795c8a045c185b49502045e02d9639a492367,0x29d9e9b9a8d40d047cec06049f02449e43016397092367,0xabbb65105e044a0c130901c45e02d56397092367,0x2af0d9f49d4822c8c855201b49202ce6397092367,0x269942f96baf2585062e13649de502345e02d96399492367,0x520364755434116161848d01e49639016397092367,0x1140848806c5e02d16397092367]
def local6g4 : List Nat := [0x2708091044c7602ce6397092367,0x9fe5b9ff94911822691204017379a8ce5ea40920b7,0x1384048822b799cbd4ca40920b7,0x54e49a00760054adbcce5ea40920b7,0x6426b68411220b6c401a48a1b076397092367,0x21b94d6410f9006495bcc2569d0b80f7,0x248111200cbf1bcbd599d06c117,0x7ccf5c804c56609b068183888c2bb0800800001900102110329f8bd599d06c116,0x4704122028c9e1b076397092367,0xba0d99ad15abb514062c38f15301b379a8c2569d0b80f7,0x268cdd2fea0260023499aa4301b3797ab34c9d06c117,0x346bb52ab2e7c26826842e8098d0174b645016397092367,0x2708091044c6202ce6397092367,0x33f8a0ec00b032cb41b02149e39016397092367,0x10c0828406b798ebd481247e367,0x82c4060430b79b2b33a1bc6c117,0x3d6882e82011687110123793a863f170400f7,0x1dbf8ce0a0094b00949dbcb33a1bc6c117,0x460800390043793a863f170240f7,0x1140848806cba2f016397092367,0x2708050844c9e1ace6397092367,0x2302099014b79a8c1569d0b80f7,0x12c101820ab79a8bd599d06c117,0x170410a022cba45016397092367]
def local6g5 : List Nat := [0x90a54802f1364001745e02d96397492367,0x2949f0d4d811622086d501e49633016397092367,0x1140848806c5e02cf6397092367,0x12c101820ab79a8bd599d07a367,0xb2201f30179459007850c8897a550243610303793a90431bc6c157,0x28e00c05d812ef8bf5a93c31aa8880301220038191411829a4f0d6717092366,0xc3d1707ae0efccf0411a402404b2b18159bcd4609d0b80f6,0x170210a012c9e21076397092367,0x12c0828406b79b2b33a1c46c117,0x117d005836f45cf9c1de39f4bac066864522219a32ac2b3c80090261bcd9599d06c116,0x170210a012c960f066397092367,0x170210a012cba4b076397092367,0xf2b0191e0efa0f019a08f22750126fb848191bcd9599d07a366,0xd2700dbf8005da4040400e9bc9d4c9d03a0f6,0x228109900cb79b8c2569d0b80f7,0x118105880ab793a9743170400f7,0x5ec0d2726fe43b6d2412223b1408298139bc9d43170400f6,0x1382089012b79aece5ea40920b7,0x202c0920444bfdf8bd599d06c117,0x170410a022ca24d016397092367,0x12c0828406b797ab34d1d06c117,0x138104880ab798ebd4b9246c157,0x168110a00ac5df0bd3a1246c077,0x238105080cb798ebd4c9247e367]
def local6g6 : List Nat := [0x12c0828406b797ab33b9d06c117,0x18cfcb7b3ea400f34a492d4800151bcc75e9247e366,0x12c0828406b797ab4599d06c117,0x12c0828406b797ab3409d07a367,0x8fe0df00688007d00a93648109bc9d482186c0d6,0x12c0828406b797ab9599d07a367,0x1aee09cf90edb49007d5b213800e9bc9d43188b80f6,0xb1af9a7e347ed5807d77bd7df3da8517000911186724503645e02bd4ca40ac367,0xa6930581712f102a632f8a7560bf24c7e4565c1e0cf92f02f8386983c2014a2983dc3294eb2986850c636b064204424b015ea40ac366,0x4422088118c9a02bd4815892367,0x10c0828406c5e02bd4d24092367,0x49824188b54881776131a74826bfdbb2729902e00584a112b95188b4082624d015ea4092366,0x1240889006c5e02bd481246c067,0x1240889006c5dbc9d48218d4067,0x871ed3b63c15f05608b096ab0154adf8c75ea18de367,0x5754f14e06f9e3928142204826e1e6001b4ecb3f7f6f36e0f6aa59900040b0080610061996a21528255b474e12890ef2053256fc5ea18de366,0x10622d133f80bfb548071a8fc77c674c8a35340011937a28603749645015ea4092367,0xd300b841dbcfd8e62680c684711602530283798ebd431bc6c117,0x2508050844c5e1abd4ba4092367,0x8f7e49042810083798eb34b9f8b80f7,0x2604112024c9602bd4ba4092367,0x144090a006b79b2c7599f8b80f7,0x35f4309b8df1ed1e197042c6039d0174be45015ea4092367,0xf5765117d0058304c01445e02db5ea4092367]
def local6g7 : List Nat := [0x14bbadbb93d33b2eab0823cce17c0174c22f015ea4092367,0x194e9b800138600a45deeb33a1bc6c077,0x2a7814261c3221a7e90f4f0ea23bc3c4603148800a23945932ce2999151282ca2f0d60a4092366,0x8235f997d87e8c1de48f0fa2863ca4222219b108008113a902a1bcd9599f8b80f6,0x98165644699ee2b3c6e10de95d4de28b9803401120bc88028082524b075ea4092366,0x1958161f8bc9b8eb78210b248026e318131bcc7611f8b80f6,0x160410a022c9a45015ea4092367,0x10c0828406b798ebd431c46c117,0xd30e2a0ebc6da23eabb4b8bbbae5940845b23232aac52bc880881182a1bcc75ea186c116,0x160410a022cc245015ea4092367,0x10c0828406c5deeb33a1c46c077,0x1c901cabd03a4bb6c1df2ca021eaa3080882a99c39910239bcc75ea187a366,0xeca3f93c002c8d90800c1bc9d482183a0f6,0xb27c8dc668d118a011f4ec988240131bc9d431a83e0f6,0x350e620059dc5f21036321099ab8c7106045320383793a90431a8ac157,0x260114200cc5e02bd431c4de367,0x3b70e9476bf8d5f6425fcb34f1038bc499480ea45015ea18de366,0x16925fcd8027d20061bcc75ea18d40f6,0x26020a1014c5e02dc5ea18de367,0x6ac3de56f0e78940b561ef2b7873c4a01c76cf9742b1e065832ed0ba7494181e22f015ea18d4566,0x10148030260c5e02bd461bcac367,0x8248030250c5e02c2481bcac367,0x60b63e05c76841f1fa6db5597f92bda86120614117853902e45e24c7481bcac367,0x2224018124c5e02c4481a892367]
def local6g8 : List Nat := [0x1240889006c5e029d481bc6c067,0x8428048150c5e28bd431a892367,0x2488030444c5e2ac7481a892367,0x1240889006c5e02bd431706c067,0x1240889006c5e029d431a8b8067,0x26020a1014c9e02d45ea18de367,0xa2ffd64aec9a00bb5080114ae4f015ea18de367,0x8228028150c5e02c1481c492367,0x2284030424c5e02c24b9a892367,0x2282028414b798ec1431a8b80f7,0x80a4018130b798ebd431586c117,0x2502112014c5e1ac1481a892367,0x1280860406b79b2b3481f8b80f7,0x2604112024c9602c1481a892367,0x1282030412b798ec25e9f8b80f7,0x4422088118c8a02db5ea4092367,0xddf9b7e91c5f51083842c90143798ec2481bcac0b7,0x874ce391e8de2de00ee9a08f0be8ec01945e24ce481a892367,0xd30981057e0d1144127324325108796032405f8d45ea18de367,0x1087c9e40139000a45e02d95e9a892047,0x14ef0ffc1081045e8262014405bcce599f8b80f7,0x1c732670647c56a8085d4408b0183adbcbd569d0ac117,0x1f38271e08262a1c7539cbf340c2d4c3900201830802800241d6bd569d0ac116,0x10428088160c8a24c7481a892367]
def local6g9 : List Nat := [0x460210a018c5e24c7481a892047,0x144090a006c5dbcd4639f8b80f7,0x10c0828406c5e24c7481c492367,0xd831a6b555c084241b130133798ec2481bc6c0f7,0x734aef19a0ff75017983b196c733d9de32e43438d2054cb796a3803145e24c74c9a892367,0x2704050824c5e24d4481a892367,0xd7e88129c0f7e454086242c25e0173799cb3481f8b80f7,0x35860c0e704f4a20312cc0044301e3797ab33f1d0ac117,0x2604112024c9624c7481a892367,0x144090a006b79a8c75e9f8b80f7,0x68fe53067f40123100a4b24f015ea4092367,0x98a0024e00745e1ac7431706c067,0x8604142030cadf0bd431a892367,0x4428028148c5e28c74617092367,0x1240889006c9e029d431706c067,0x20a101810cc5e2cc73f17092367,0x10c0828406c5e02c4481c492367,0x1140848806c5e2cc74617092367,0x1140848806cadee9d3a1bc6c027,0x10c0828406c5e029d481246c077,0x7bdb7b2b0239faeebbd47c65c1130012ac2bb19cd18a1982522f015e99c92366,0x2224018124c5e02843f17092367,0x6ffec7397a49988c0130910c3bba2b319bb82122f014217092366,0x25010c080cbdd8eb33a1bc6c117]
def local6g10 : List Nat := [0x218105080cc5e2ac74c9a892367,0x10c0828406bdd8eb33a1c46c117,0x2428018144c9e20c73f17092367,0x2704050824c5e28d43f17092367,0x1240889006c5e249d431706c067,0x218105080cc5e029d4c9706c067,0x9e21384ec4c8cac78b849701b7d924d1098b343a24e219d5980112a82aa2ef73f1a092366,0x8264048130b79b6b33a1a8b80f7,0x2182030414b79b8bd569d0b80f7,0x118104880ac5dee9d3a12450067,0x12c0889006c5dbc74378d852067,0x12c101820abfdd6bd599d06c117,0x2122018114b798ebd351246c157,0x170410a022cb24d016397092367,0x10c0828406c5e029d4812470367,0x101880a0460c053a90379586c157,0x48bf69c49f880250b00b4ae2f1260a4092367,0xdbf1168e5ae0efc841c102630174ae4f075ea4092367,0x86880c1050b7984bd569d0ac117,0x65b39b4a043a1700c45e24c7481a492367,0x37fdbbe93d137504494e001045e0ec74517092367,0x155c3ea89ba8226a100b45e14ce3f17092367,0x5572f8ca410ed00645e1cc73f17092367,0x155d394cdd410e6c00a4920ec73f17092367]
def local6g11 : List Nat := [0x53298b75ef196ce6c7f72851220187635402645e24c748170ac337,0x5dac64308fc152f3ee3b9fc2fe50a2c039117582602b45e1ac74c9a892367,0x8688060450c5e24c1431a892367,0x20a101810cc5e0ec74d17092367,0x1240889006cadee9d481246c067,0x218105080cc5e2ace3f17092367,0x228109100cca60ec73f17092367,0x32b1bd7a694107026301145e24c74819492367,0x217ef08fa920874b00945e0ec74117092367,0x2704050824c5e0ecb3f17092367,0x2428018144c5e12c73f17092367,0x2604112024c760ec73f17092367,0x107c070c3e2fa68045b12a0103798ec2481c4920b7,0x1382028412b798ec24b9bc920b7,0x1244018222b798ec4481bc920b7,0x1302089012b799cc2481bc920b7,0x1a000a0023f1bcc2569d0b80f7,0x144090a006bd1bcbd599d06c117,0xf9c17ae498d3e5105ee77fd01c38cc3b100201800281e9e8bd599d06c116,0x10448090260c960ec74617092367,0x3ad1c91f9abc5158224049c01349e0ece5ea4092367,0x76e798d39d7099ec20ed002b307f37094f2cf8d863b26ea51310c4011052645505bdc569ce6320a5483f256f860a4092366,0x9576406007800545e1ac74617092047,0x144090a006c9dbcc2569d0b80f7]
def local6g12 : List Nat := [0x1a41425e2e784beceb080c5e5ea220183798ec1481246c117,0x4708060848c5e24ce4617092367,0xd286e4a4c20ad00637982b34b9d0b80f7,0x11cd94bc1386c041c65000f3797ab3461d06c117,0x4604122028c9e0ec74617092367,0x144090a006b79b2c2569d0b80f7,0x334400b00249deeb33a1bc6c117,0x12c0828406c9deeb33a1c46c117,0x99e1df86d1043d8008495bcbd3a1586c117,0x82c4050230b79a8bd3a1586c117,0x12c101820ab79a8bd431d06c117,0x2708050844c9e1ace3f17092367,0x2302099014b79a8c15e9d0b80f7,0x352005c00545e02d95e97492367,0xe0fca4801d200745e02ce4017092367,0x2428018144c5e10c73f17092367,0x12c101820ab79a8bd431d07a367,0x2302091014b79a8c13a1a8b80f7,0x128108900ab793a99431d03a0f7,0x660aded02841c65000f3793a8635170400f7,0x104a80a0444ca1bcb33a1a8b80f7,0x13bda05043d80083793a8635170240f7,0x4400b0023f1d6bd599d06c117,0x29c005c00549e02c75e97492367]
def local6g13 : List Nat := [0x2424018124c5e0ec83f17092367,0x226fea4801d200745e0ec74017092367,0x1142018212b798ebd379247e367,0x43020a1018b79b2b33a1586c117,0x144090a006b793a9043170400f7,0x8b04001e00349dd69d3a1bc6c077,0x150210a012cb24f075ea4092367,0x10c0828406b79b2c7599d06c117,0x10c0828406c9dd69d3a1c46c077,0x94e20076000945e24c74817492367,0xdcfea4801d200745e0ec73f97092367,0x10c0828406b79b2c7599d07a367,0x5121bd16663d35a54d088d41f7286139124867502245e1ad4481a892367,0x40a0245bad7a9d3f1d0ac117,0x6ff1cbe38fc70f94c27e2179854d8811fe3d29ca6487269837ba4502945e24d9431a892367,0x10c0828406bdd669d3f1d0e2117,0x10128028160c5e02bd461c492367,0x4224028128c5e02c44617092367,0x1240889006cadbc9d481bc6c067,0x8648050250c5e2ac23f17092367,0x1340889006cadbc9d431a8b8067,0x4624028128c5e20c43a17092367,0x1340889006cbdbc9d431706c067,0x20a101810cc053a7e2e1246c087]
def local6g14 : List Nat := [0x10c0828406c5e2cc74d17092367,0x20060510242bfd8ebd3a1246c117,0x218105080cc5e2aac3a17092367,0x10c0828406c053a9a2e1246c087,0x218105080cc5ddaad3a17092367,0x4142030218c81d6ad3a17092367,0x10c0828406c057a9d481246c157,0x10c0828406c057a9d4d1246c157,0x20060510242bfd7a9d431d06c117,0x1140848806c5e02bd3a97092367,0x218105080cc5ddead3a17092367,0xf5738fe0588803d26de22501f49e02f759a18de367,0x1ddf34001d200745deeb33a1bc6c117,0xc1c261afc586a8411a6274601648a02ce5ea4092367,0x65c61b0488c11328400e4960ed76397092367,0x22f9c9e410a500645e02c15e99892367,0x8228028150c5e02c15699892367,0x15fbd2c80c10ed00645e028c4197092367,0x2224018124c5e028d3f17092367,0x50380c00a00245e1ac746170920b7,0x168110a00ac5df0bd3a1246c117,0x40a0245bd1d6bd599d06c117,0x441a0093a00945df8f76397892367,0x7c9750048d00845e02974197092367]
def local6g15 : List Nat := [0x200a0520442be18ebd3a1246c117,0x2122018114c5e02ad3e17092367,0x4090143af566742e0d8320f7,0x1284028422c5e1b013d97092367,0x1302089012c5e1aeb3d97092367,0x20140940844c353a90351246c157,0x101880a0460c053a90351246c157,0x200a1108148b1d667e2e1246c1b7,0x2122018114c5e02ad3c17092367,0x62ac3afa2bea310459066c01445e28c7481a892367,0x10c0828406b798ec4481c4920b7,0x20060510242bfde8bd599d06c117,0x1140848806c5e20c74617092047,0x1140848806c5e20c74d17092367,0x10c0828406b798ec4481246c117,0x1140848806c5e24d74617092367,0x118104880ab79b6b34b9d0b80f7,0x10c0828406b798ebd389246c157,0x1140848806c9e20c74617092367,0x43020a1018b79b8d9569d0b80f7,0x1271379ccb803d9fc3fdeabeed478d08b908965334c223301aaaadba82ea2f0d3d97092366,0x4090143b6566742e0d8320f7,0x217001b700421f85862d800cc00380800401e166742e0d8320f6,0x1140848806c053a8c2e1246c087]
def local6g16 : List Nat := [0x10c0828406b798ebd3b9246c117,0xfb7098e004bec3c9988c01b0910cd54e324329bb582522f013e17092366,0x8244050230bdda89d3a1bc6c117,0x10c0828406bdda89d3a1c46c117,0x1702089012c5e02883d97092367,0x7e39adf165b4003c800180a912d8181bc9d481f8920d6,0xc97c8dc66ad05924026422299032ab8881b9bc9d431708a0f6,0x1702089012c962f013d97092367,0x3ae563fdd39c31f8678f0d750d04a8bbcc113301a22252a024a4b013d97092366,0x7fb8c07c178acdc0027421839080280179bcb3539d0b80f6,0x10c0828406b798ebd409247a367,0x42b7d41060023798e7e2e124400f7,0x118104880ab798e972e124400f7,0x1c7e7bf33abb02244084b01749e2f015999892367,0x3f3c2de2ad40164388001645e02d9481a8920b7,0x101880a0460c053a9035124260b7,0x398a0d2009a4700d49e02ce5ea4092367,0x471a0076000945e02d4431706c0f7,0x2060245bad3a903f1d0ac117,0x10695c10760449804c01448a2f015e99892367,0x1cfecb91b2c8f4d5d830e20525c01a49e2f015699892367,0x1704048822c5e1b014197092367,0x460210a018b798e9035124420b7,0x80c8060450c49d69d3a1bc6c117]
def local6g17 : List Nat := [0x5ae8bef3ebb02244084b01749e2eeb6397892367,0x82a8060450c5d7a74351242c047,0x10128088160c053a7e2e124240f7,0x10428088160c053a90351247e367,0x10c0828406c057a9d481247e367,0x4d458c606cd52e040626400123dd849d431d06c117,0x200c0920444bf17a9d431d06c117,0x218105080cc057a9d4c9247e367,0x10c0828406bdd889d431d06c117,0x118104880ac057a9d4b9246c157,0x20181140848c493a86351246c157,0x40a0245bad8ebd3a1586c117,0xcfe54f81cd30f380a00f38be3342890325687402145e02c24c9a892367,0x4648030248c5e2ad43f17092367,0x1340889006cadee9d431706c067,0x40c0449bdd8e9d351246c157,0x1284028422c05eeb33b17092367,0x228109100cc056cad3a17092367,0x3c69f97b854d008fca511b01c45e24b348218de367,0x287a4df1d75c5246a08d82ddaa601d45e02d9639a8920b7,0x1488028442cadf0c75ea4092367,0x144090a006c5e02d4639706c0f7,0x2b6fb1a1267127b5944062dc0765401b3adce9d481d0ac117,0x3afc74fc4bcd55c373f2b7342620b10265847302545e24d93f1a892367]
def local6g18 : List Nat := [0x3f761e09e560ea089109c01148a25075ea4092367,0x2060245bad3a97481d0ac117,0x3ec05f0dff42deb9cfc96bcec2e68a1d22877ac01f4ae4f12639a892367,0x7b69f5df88f8821c1b00b4ae4d076397092367,0x10068028148c5dd6bd3a1586c117,0x1b3b6e0cf3abf25c08b2404ec01949e02f75999892367,0x3cdb79c7db1044865401045e1ad43f170920b7,0x16bb8e54fcd970224889301349e02bd5999892367,0xc1dcb99499a2b210711300d45e1a893f17092367,0x428851c053a8635124260b7,0xda7bdd8ecebe91e44f832e0c49202af401c49e02f75699892367,0x8421088118c89eec75699892367,0x2604112024c059cb53f17092367,0x57e04fde7c7d250424ba840133798ec24c9a8920b7,0x10428088160c8a1ad43f17092367,0x29deb9125b99fa9b8cb6109151d01145e24ce60a4092367,0x1ce07121fc00f022c8032b01749dd6c75e97892367,0x79c0f3ce8060878300945e1ad43f17092047,0x144090a006c5dbcc2609d0b80f7,0x357700830013ddbcc1599d06c117,0x40c0449bdd8e9d379247e367,0x2050449bdd3a97431d06c117,0x12deb9262cb1a0c84c7807edbc55d40e363dd28200403098490000281eec1599d06c116,0x2050449bdd829d431d06c117]
def local6g19 : List Nat := [0x428831b798e8635124420b7,0x40a0245c95d6bd3a1586c117,0x429061c5d6674351242c047,0x40a0245badb29d3a1586c117,0x818831b798e902e124400f7,0x3b7d56755b9dfc166cb830e4589301649e02bd5699892367,0x4422088118c8a02bd5699892367,0x60eab3ab5cc80cd1590c3895301045e1a873f17092367,0x2704050824c5e0e873f17092367,0x406c988821de00745df8c23a1706c0f7,0x1140848806c5e24d94617092367,0x3317015e381083911a0103798ec24c9706c0f7,0x1633c1418b80cf0102ec0880143797ab8431d06c117,0x4604122028c9e1ad43f17092367,0x144090a006b79a8ce5e9d0b80f7,0x31fbc525dcb9abc210714230114b645076397092367,0x829da2548023448d6301745df8c23a1706c067,0x92ff292007200545e1ace4617092367,0xb7fe21c5a4012700645e20d43f17092367,0x2d79dcaaf9b2e0448884b01449deeeb6397892367,0x8453504db2e78040a340d0123dd8ec13a1246c117,0x40a0143bd17a9d431d06c117,0x1702089012c9602b33d97092367,0x1302089012c9602eb3d97092367]
def local6g20 : List Nat := [0xd2239a25a6f24fc06c30eb8880123798ebd461246c117,0x4604122028c9e02b84617092367,0x144090a006b79b2b34b9d0b80f7,0x40a0143bd18ebd3a1246c117,0x8604142030cadf8c23f17092367,0x4122028118c5e2cb83a17092367,0x16e2dc71fbd7d4e27fd0b04124477ac01a45dfef75c1d0b8337,0x22a101810cc89febd3a1246c117,0x82a4048130b79aebd3a1246c117,0x4322028118b798eb82e1246c157,0x4628028148cadfeb83a17092367,0x2284038424b79b89d4b9d0b80f7,0x10c0828406cadbc9d4812470367,0x218105080ccadbc9d4c9706c067,0x118104880ac9dbc9d3a12450067,0x12c0889006b793a74378d856067,0x3316f1982ff19dcfa52450e40fd6301a45e20c746170ac337,0x40a0143bd1cebd599d06c117,0x8224048130c5e027c2e15892367,0x4090143acd20742e0d8320f7,0x1284028422c5e1a863d97092367,0x40c0143bd18e9d2e1246c157,0x160410a022badb2a43a17092367,0x218105080ccc5ce9d3a17092367]
def local6g21 : List Nat := [0x40c0143b9d8e9d2e1246c157,0x10c0828406c5e2cc43a17092367,0x10c0828406c058e9d2e1246c157,0x20a101810cb9d3a742e1246c087,0x10c0828406c5dba742e1246c1b7,0x20060510242c598e9d2e1246c157,0x20060510242c593a742e1246c087,0x10c0828406c5e02a13a17092367,0x218105080cbc9ce9d3a17092367,0x10c0828406c5e06c73c97092367,0x10c101820abad3a742e16c6c107,0x7ef7746b5ded6f054d0c488033b090204be2ec6481a892367,0x62eddf2b63084212a0890e001e4a22ec6481a892367,0xb1e1462fdba182322189091c2a4cc0254a22ec6379a892367,0x77fc2f58b99a5a561a189120e75401d4b62ed33f17092367,0x73878a9b2d1b021201455901a45ce86f2e1586c277,0xc7c28583e6eb68d04d0c4a7956c401c4b22ed33f17092367,0x101880a0460c053a902e15866157,0x10c0828406bdd3a863a0d858117,0x10c0828406bdd7a74248d82e077,0x10c101820ac5d66742e12484367,0x20c2043b798e862e124440b7,0x20140940844c353a7e2e1246c157,0x2284028424b793a7435170640f7]
def local6g22 : List Nat := [0x20a101810cc059c9d2e1246c157,0x2224018124c9a02e73d17092367,0x8224048130bddb69d3a1246c117,0x20120540842c1d8e9d2e1246c157,0x10060490222bdd8874248d82e077,0x218105080cc5db8742e12484367,0x20060510242bfd7a74248d848117,0x10c0828406c05ba9d2e1246c157,0x10c0828406c053a5c248d844157,0x200c0920444c558e9d2e1247e367,0x200a1108148bfd3a863a0d858117,0x20060510242bfdb29d3a1246c117,0x1284028422b79b6742e124400f7,0x100c08a0424b79b8742e1246c347,0x4088245b6d3a742e124340f7,0x20060510242c418e9d2e1246c157,0x20060510242bfd3a742e1246c087,0x10c0828406b798e5c248d82a087,0x20a101810cb798ead3a170920c7,0x1140848806c5e24a03a17092367,0x1140848806c9e02a03a17092367,0x118104880ab79669d3a170860f7,0x1140848806c5e04c73a97092367,0x1140848806cadeea03a17092367]
def local6g23 : List Nat := [0x218105080cbf5ce9d3a17092367,0x10c0828406c053a812e1246c157,0x10c0828406cadd29d3a17092367,0x10c101820ab79669d3a1706c107,0x78f0753b1bde1a9a861c801d40401f45d8c99481a892367,0x10e0f38781160426aa51101745d8c90389a892367,0xb6b4cdf6f560e0510c4c3b8129c02045d8c97379a892367,0x238ba37b33b3e5a88a218b00452ef502145da6993f17092367,0xec5d9b9d1e1a9a861d09250b01b45db08c3f17092367,0x2e2ece0f37bb074a187255285301d45db4863f17092367,0x100a8088150bdd8e73351246c117,0x1061061c5d5a903c17092367,0x10c0828406c5d7a742e16492367,0x10c0828406bdd8ec43a1246c117,0x40c0449bdd8e9d389246c157,0x218105080cc5e2adc3f17092367,0x10c0828406bddba9d3a1246c117,0x20060510242bd13a742e1246c087,0x10c0828406cadd09d3a17092367,0x1140848806bdd8eaa3a17092367,0x1061061c5d70903c17092367,0x10c0828406c5db2742e16492367,0x10c0828406c053a5c2d9246c107,0xa9d6676abbe9fe98a4ea421ab28a33e01e4adeece5ea4092367]
def local6g24 : List Nat := [0x1508048842cb1eec75ea4092367,0x86880c1050b797ab3569d0ac117,0x19f9e44fc225208b94d802501d45e02d96397c92367,0x79fce46e4e2682240344c01745e02d467170920b7,0x1140848806c5e02d763970920b7,0x10c0828406c05ee9d481247e367,0x55de53fa26804498c20103ddd69d4c9d06c117,0x200c0920444bf13a90431d06c117,0x933e6ea00b80b04201941deece5ea4092367,0x10428088160ca202c7481a892367,0x14a400e9000a45e02d94817c92367,0x75ca9f00c012d00645e02d446170920b7,0x1244018222c5e02d743170920b7,0x2354d00094e00945deec13a1246c117,0x2060143bd13a90431d06c117,0x60e7ce7b5379cd9d43431320539401a45e1b073d17092367,0x1140848806c5e21013d17092367,0x1fdd0b514411686620123793a90379406c117,0x2704112024c960f013d17092367,0xa1d37d6dbc43c044d0858c8c9501845e25073d17092367,0x118104880ac5e29013d17092367,0x3d0b514411686620123793a90379346c117,0x3e741bc7efb99bc3020e22300e45e0ef43d17092367,0x2122018114c5e20e73d17092367]
def local6g25 : List Nat := [0x7de50719a082e10083793a90351406c117,0x2704112024c960ee73d17092367,0xa1c13f25d99c9b411306200e45e0ef83d17092367,0x4122028118c5e28e73d17092367,0x105480c0860b793a90351346c117,0x101408c0824b79a87e2e124420b7,0x20140948844c353a7e2e124260b7,0x100c8090260bdd3a74379346c117,0x1439a9bfcee0e8e08388b00c48a0ef73d17092367,0x2050449bdd3a74351346c117,0x100a8088160bdd3a74359246c117,0x10148090260c053a8c2e124260b7,0x1140948806c053a8c2e1247e367,0x20c2043b798e862e1248c0b7,0x10c08a8406bdd7a742491c6c0d7,0x10c101820ab798e862e1246c0e7,0x10c101820ac05a89d2e1247e367,0x10468050260b798e8c2e124420b7,0x18527c420640063ad3a742e0d83c117,0x80c8050250bdd3a853a1bc6c117,0x8068048150bad3a8e3a1586c117,0x80a8048150bdd3a963a1246c117,0x80a8048150c453a74351246c117,0x100c8090260bdd3a74379406c117]
def local6g26 : List Nat := [0x2050449bdd3a74351406c117,0x100a8088160bdd3a74361246c117,0x242111200cb9d3a74351245a117,0x100c8090260bdd3a743792c6c117,0x2050449bdd3a743512c6c117,0x80a8048150bdd3a74351246c147,0x18e03d2ac0438700848a02f43d17092367,0x60f9385eae2f2c9c18531a00d4961ae73d17092367,0x199c2600500148a02f83d17092367,0x20140940844c353a7e2e1247e367,0x10c111820ac358e9d2e1247e367,0x200a0520442be1b29d3a1246c117,0x1284028422b7982742e124400f7,0x1140848806c053a8c2e1246c157,0x200c0920444bf17a742491c6c0d7,0x218105080cb798e992e1246c0e7,0x218105080cc05b89d2e1247e367,0x20060510242bfd66742e0d846117,0x10c0828406bdd3a74248d844117,0x1028851a74e8712e12430117,0x100a04a0422bdd8274248d82e077,0x1142018212c5d84742e12484367,0x1140848806b798e8c2e124440b7,0x1140848806c05ae9d2e1246c157]
def local6g27 : List Nat := [0x10c0828406b797a74248d844117,0x200c1110248bf13a863a0d858117,0x10c0828406c053a5c249186c0e7,0x54e76c9dc8984392b1b7066cbc9ce194463e8b4802d3a63c2c90a9a80d14020088008004104022006001043000811d1525c18e6d4d33c50f486f257278936492366,0xedb4de8266c39f3a2c26187041aa30194ae4b076717092367,0x86c80c1050b7984c1599d06c117,0x105880c0860b793a994b9d0ac117,0x43020a1018cbde8b83a17092367,0x29af79e7f35bf70efd45c0513023213118765403645de8c45c1d0b8337,0xca005001489f0bd3a1246c117,0x1342018212b798ec22e1247e367,0x5cc6308191e62f9220539480113793a90248d83c117,0x43020a1018b79b2b83a1246c117,0x144090a006b793a993a170400f7,0xa65335bf718f8f7ea911049100924f7ac02c49e2ef45c1d0b8337,0x2704112024cb64b076717092367,0x10c0828406b79b2d44e9d06c117,0x10c0828406b79b2d44e9d07a367,0x20c0143bd18ea13a17092367,0x14c0928406c493a742e16492367,0x100c08a0424b7984742e1246c0e7,0x40c0245bf18e9d2e1247e367,0x2050143be13a99431d06c117,0x40a0143c99e8bd3a1246c117]
def local6g28 : List Nat := [0x40a0143bd1b29d3a1246c117,0x818429b79b2742e124400f7,0x200a1108148be13a74248d85a117,0x40a0143bd13a74248d85c117,0x65a381ff7d7244608949c00d4960ed46717092367,0x45a2d6bbf720f937faa4441240f7ac01a49de8bd5c1d0b8337,0x40a0143c89e8bd3a1246c117,0x4624028128c5de8a83a17092367,0x2050143a7532742e0d8320f7,0x1142118212bf13a742e12484367,0x10c0828406cc9bc9d3a17092367,0x19f41e8f93c228268426811500040234b256f763a3892367,0x3f7e3a30d86ff938041343126c00316ec0264be4f17631a892367,0x83c74643a9ee7152443125b6f26ec0224a64f17631a892367,0xb1f14243b3bdc54c861ca88c90174a22e742e15892267,0xd1da6392d4f077543431360803202c0264b657056397092367,0x3a181dd1e2e032187006550154962e74379706c277,0x10148090160c053a8c2e15866157,0x77dd2241e3364d0838180924b0204adf0f763a3892367,0x438f518fc34a109aa980e101d49e2ec64b9a892367,0x4284f51af0411606279a4aa4a102349e2ec6389a892367,0x819061c5ce8712e15892267,0x442149c1cfc5420c0c5d83e66ea0204ae2ecd4617092367,0x52707bd426841ca24990174ae2ed63f17092367]
def local6g29 : List Nat := [0x80a8048130c9d3674351246c077,0x144090a006cae4d106397092367,0x40a0143c99cebd3a1246c117,0x1d7fcbc1060023dd3a74248d85a117,0x40a0143b9d3a74248d85c117,0x10c0828406bdd3a7d3a1246c117,0x10c111820abad3a742e12484367,0x248111000cab4e85c248d836087,0x10c0828406a74e85c2c9246c1b7,0x20302181050a74e85c248d836037,0x1140848806cbdbe9d3a17092367,0x43020a1018b793a74321246c117,0xa62dd6bc0ff9e7cadfe5081cad5c013449e89d4d1d0b8337,0x217826d70e3f94f35122063c4001593728602f4ae4cc62e15892367,0x57da1154ea73afea1d83160d69cd01a4b24ac63f17092367,0x1113399676389df485818b07bab401949e4cb73a17092367,0x44d80d6eb2f40f4811031e2001594738602e49e4cc62e15892367,0x1302089012b799c9d3a170920c7,0x20060510242c593a742e1246c157,0x218105080ccc5bc9d3a17092357,0x10c0828406b753a742e1246c1b7,0x10c0828406b793a742e1246c1b7,0x13a742e1246c1b6,0x627483e3fffa4d382164d898d01a4adf0c7471a892367]
def local6g30 : List Nat := [0x60849e73fe3a850421b622c7d01a4ade8c74597092367,0xc58022fb97d078b10b031e2005947381602e49e2ec63895892367,0x1029061c5ce8713797092267,0x56dc109bc1d5f750a3063c4110693728502f4ae1ec72e15892367,0x10c0828406cadc29d3a17092367,0x200a0520442be13a7d3a1246c117,0x20060510242bfd3a7d3a1246c117,0x200a1108148bfd3a741b0c458117,0x200a1108148be13a863a0d858117,0x20060510242c99febd3a1246c117,0x200a1108148bfd3a74248d85c117,0x20c0143bfd8ea13a17092367,0x1061061b913a9a2e1246c157,0x14c0928406cbd3a742e16492367,0x100c08a0424b79b8742e1246c0e7,0x20060510242bfce85c248d84a117,0x10c0828406b798ec42e1246c157,0x10c0828406cadfec43a17092367,0x43020a1018b79b8db4e9d0b80f7,0x1061061a75345c248d854157,0x1244118222c553a742e12484367,0x40c0143bfd8e9d2e1246c157,0x20302181050a74e85c248d836117,0x10060490222ae0e85c248d836087]
def local6g31 : List Nat := [0x10c0828406a74e8722e1246c1b7,0x20122108150c593a5c248d854157,0x200c0920444cc53a742e12484367,0x20060510242c5938742e1246c157,0x20060510242c58e85c248d84a157,0x10060490222b10e85c248d836087,0x2c7fb67002800938742e1246c156,0x20060510242cc93a742e1246c1b7,0x10060490222b74e85c248d836087,0x20060510242b8d3a742e1246c087,0x830851a74e871309246c117,0x4090143a74e85c278d8320f7,0x20a101810cb9d3a742e1248c0e7,0x20060510242ba93a742e1246c0e7,0x20a101810cb795a9d3a170920e7,0x20060510242bd53a742e1246c107,0x1118f1429e7973a3b60c5a1f9d0144b22ec64617092367,0x2428018124cba2ec63f17092367,0xc3025ef378dbe0b115d4a0c897a8541302060303793a90371586c157,0x46c5840f3ebe81c1092a6301149a2ec33a17092367,0x4628028128caa2eb73a17092367,0x1b6f443d9d85c1622bca0c797862143050283793a90381246c157,0x1448018222c5ce86f2e12490367,0xf3603a3839be4ab4862cf7305101b3798e5c2b1246c097]
def local6g32 : List Nat := [0x7247c89f4de0438700845ce8712e1246c277,0x110948f1c3e5cf852704366143cd01b49a2ec64617092367,0x8428048130cba2ec62e15892367,0x101880c0460bd93a902b1246c157,0xc5e29e761b5c6108625942412c50234a22ed8631a892367,0x146dd03ef367e1b4503831b4282716502249a2ec63897092367,0x49b0682078e1f2e7c293831a4171836502249a2ed66317092367,0x4428028128caa2ec62e15892367,0x85b01d5c29ec2e0b115d4a0c98b9a71302540603437976902b1246c157,0xac02778347fe8255c4e0c98b9a7023145360344018e5c2b1246c097,0x20060510222c9936742e1246c077,0x20181140848c493a742e15866157]
def local7g0 : List Nat := [0x23f043e1ef1ebe1efc3cfd0b269832c4a249383460a8404fb803181250124e0d182a10142c9a60cb128900f2c6618b93b120000117f76c0f6b537dca8c16494cd6840c41030830820c2102084e72a65837cea921d74ae38babeca1de30b677b6c6e99f0011861482174c83c861220e2194481c728018a00925a5893496d524c25c5092c114b0471c821020924f45e02c7379a892367,0x108fc3df1011ffc12fc404f7f8ac1608fbe007e202a5e68ea5e68e202a1f15829202b42ef5770b2fb8e3666b09a8c105950b87c0c41030cc0ea0c4204a841870cd0c70c61c43441c4187a66a270400411c104728b0411e58a48e14073a01df79d6985d471b6565420050801cb1c94c748708244f20745e02d9639a892367,0x50144e89c1097c40fd4054041608202fc031a9a5ceac80ac081678d076a7351ac5458cc57c3a1e2d3b6dcaa7141a010e0881a009259690e01630a01839938e4993132c842919110e73ef0f092440e92e18436d18c9e30a28c68e68cbac69a38a48a8b0a8a29220820a28c98a310324f01639a892366,0x150808a8405ab0b71378a840430b269832c4a212f76bce78e76e4ba8caa2454001e49a2eed7c56148ce423194b621ae7a4e1248bc058e712e15892368,0xb7923c15c542022a101092808a8405b0b269832c4a2054202901e58cc3172762024a0390000000a7fbb3275d843bec9dd0601250a0a50b1802081420071c50861c7201078cf0bea044137d31bab1030f6d72b6c0ca2a168a5ca8992962a360a2552cb91d2d42e570b4cb99b2cd48c32780c44ca1f31032978c38f21945e02c73897092367,0x83f1179f61d9039f7de194461690053741a3004203d1f785970e76a7e26399e02e172016092904124871020804131440410051c104230c30c69631131b54c30c71430c30c31d64c44c79830c31f5cc3cc18630c8e23062cb30c92130b24930c9603090ca3880c834a2153798ebd481246c0f7,0x35616f10105334c1288935a7a079dbd24aa6a049261000208ba0f114c54a88642d8331da0f28bc05aec72e15892368,0x2375eca1c54290622c1a01d01435b1984ec405e082843be9ee7be7d4dc8d8a1302227442088021004f57bae6c23194d729cd63acd433706344d03394a664c699a467a5295212a11f49a02c72e15892367,0x5a447b2f7101743bc4b8ab973c35e1a30404139d6828fc8649207859701ceacf24e93147a4915d432a841061860028c228000a00190128000a1c610e18610718438618420689f86078348318f7466d765814518934651071569610418c2c64d11b345e02d76397092367,0x7d16d1ba37057b28728c3328c3320c4584c147e432680001f785a72ddcc28bc6d3dcf7cfab36dca135105f28621819818804c18860660628412c249192cc44c221af3a240292fb82b4aa020e58829e30a30c3ae30eda898842420a714294510c1440e42238e7a4d016397092366,0x16122a022a1540466f6c022305f3ef6345659010c360c441906020c8400048c5e96aa12c4a5296a12c4a52972d093194a945263194a9c1263a5e7095010910115245e02c72e1246c067,0x28913011925b01486a0318a039a015006a3cddf3cedb09207190821089611187419a0689873199c679812019866e6d8ba8e549ca839484210b510145dbc9d431f8b8067,0x92b4d6c3288efc85334c12894c2c658214e082b016f3e75e14fc92f50992454899804290c6318390e869b8c5bc08709d10e5c595b1dea93781788bc05b2c72e15892368,0x16bad74466c1052dc4dc92a13a3b95b368066807405081985934658945066c6613b135c1056001317a93db3b6d42c47339c3a198cc78045506c0a41861c60461851830f30b2c63c2208b02daa89e401002cae99a500808c31c3210933d6b8f45175944f3de60f30c50c3ca292257bc938e7db38926068930c54c24d34d28f34a22b49e02c72e15892367,0x1acd614f97bd57df8f9f244fe24f7580358065800ddd06804296e83402106c0107fbb82791bfb829d500182c8d3101411627dd7191411a181e6da18c30a2954ca28a5d13c000c30b2d650b2cb6123830c300a0c03481071092022029a52022088ca2082242c81cb37966ad481d0b80f7,0xad866331581d0f9ec3c0ae82a188804c488890383aa56a6f46b20be8bc05b2c72e1246c338,0x4012d9fbe64f64f20fe85d460eb06499e00417494511825114c631a112a4ef40da3700ac010eb20141286f31d7a99481246c0b8,0x30148c05f5eca1c54290622e4188bae786b95b99bc938342a14440a084e72ad8059f90cb2a6c11d2b7a4b4e1ae433678773df29968f35b5367d38928340b205083092070182043441c470c108f070182043381c470c100000002f35836e31932daacac00280e608b1430a482285b5a90a70c81020c00257a37da5dd71551322449645016397092367,0x285e76f4932c081009a2404aaaa6aaf0aa8cc0968bc05aece6397092368,0x22c1e06e69c1dc504d0c4901e515603e95c5deebd3a1246c018,0x317813e402f99eb90098920284005f0160ce66e28fea739ed122124838409035481d7de10400001c65b68c00059500030011300010c0044c00044005c000000000001400000048028308138a28024b3464492402006081403403c00051401c514d2043797ab33a1bc6c117,0x32342a35d4d20effe8386fb696494344378d06204502918f2214370d095a000001a10a8bc3602ce6397092368,0xd48ebdc42a6f044725859da213a0c09425886661f2aa9072500153c00cee06ea6ef2fab01eb0b2daba6c82b030c70c214816414214051e00f1c33831c31864c72c78db8a17d06901cc7470418026421cf3877183494910411c11ca1c11c95c92565491b949602ce6397092367,0x3456430e98eb3c65c9c2a504c21702061104572b2e9ccb5aaf80b88bc05a8c72e1246c048]
def local7g1 : List Nat := [0x18a2029024ab12cb302412605103aa43fe5c05de5d5dc9c5515603028f9689022089c19840108421a8e430dc2da056f2942a094200942b8302630441120463a4210a5210e02b14837982b3569d0b80f7,0x41420302199645e02ce6397092368,0x31e55750064772b619127068c05fc98331477ee25e91434c2f94061000050003100005000002800a92840401104ac19840d0380f000090280a4310b1164b22f016397092367,0x10523167a462cf4d12a1c55d330b1a020c0fe1944c8ec02c781af5c05174db5d8ebe8c24e161b31a0a6021c60000c480878c50498d0be5aee9703c5b0e16d8c934c8c10412248e48c81e30e392a8e49a40a40820831428c28a42c290392390a0e29c48e624b076397092366,0xd86c12d98a30ec42c10604e6395f68e9b692edeeacb8125f294e70942009027294f3921914402873427280aa00421080813180b301242088120c2108424205e40802008ae1bcc2569d0b80f6,0x1f45b46e05f0483b85bd94354a843341c83098464068b31f93d9b16dc35d70fe762eaa3e8ee9a5d20c5114e8a0418822c62c20d114b30314002308b18b0833c52c90c784e58e8127d27196da0c350340a20328d34820855879710475320819649a45016397092367,0x62281bf33d6aa017b02d8338431ccff47147e4273fb6a24da76090253d6b659b62e8055a00200180000400b00000e0680004da005000880c310560300c7495e030140d8000490802312016c3797ab33a1c46c117,0x40263033f33d6aa012a007b211814c116189c45d35d55f5086eeb358b01a6e428c6828c004906528ea43ca24a20f3820a301980200c0401403180d3016e28460c84011830101de0bd8001004000ba1bcbd599d06c116,0xf99eb90084c1aa00ea008bb20c4e11c30b893c039a3a3bd2f916030b8330c8330c4210886312c343dc3a8d1068c87024c008c1408c2304c234480c8808601940180a3180a32940b2804210ba9bcbd599d07a366,0x1b647a0cdcb9e319c8defce8e01910b913310aa890010800800400111118000148109012000888800d009100908107f1bc9d3a1bc3a0f6,0xd585b97b8a69265080a49942029265080a499420251e2ee0d1892650809478bb8346249942022b973f1dff710fbf7890f6ee26d904a04c1548ad1c8147080182009078c6db2504b077caeae604e136cefaa710a0f5d30a680cd35d60d49279749435f58d34d81534f3cc32170c45189b45332368c30c9193104103cd40f21f45e02bd4815892367,0x2182c2052655e08d7327d84082d262311240568ae000017bd91c35c01c1646fd3c5afdb6de04550935162117084006a069c60060d698304f9413051c59051c538e5472cb5072478e285e81f74a64a1d37072086da20d4904420870872470872181b245e02bd4ba4092367,0x15fc122e45c11ae64fb2853ae059200b02bb834522480acb5c263b0000000bf597bd895e39acd15e96e3d614d4986912216890520d9404c08f28200238459e48419c44918cb4434249af324c040cfb043a38ce3438410448829240861028e288a2e28a38a288a8a20eca45015ea4092366,0x32af00c6511a00208802340a2e01ebdade305c79c9668009466394e73180b00804018471000410044018e7354a87b8b402a0d04c488b04921064080831840000002008042024400b81bcc7599f8b80f6,0x6bc538b000a8f177068c4932840547dfb75eee2ec174047630da31988410421224240042119c23bb2cc3c53254d14c2eab3b52e53d100e44be2f015ea4092367,0x22c59cc1984090fe007c80f953c23217c7ff82df128122c59cc19840cae7cf038fe5889cac14e60e29d4324473a8430fc622f847228612ec223744337060224203acba122301646893c780a26e0dca8a34b6322ac30a9a2f015ea18de366,0x1ef2b7c73c4b66f04d7302a5c0dcbb8560e58f52e06e4998380517f885f2dc9157786382f742a2acf037827cf677b078984baec75c75c624d70c820c39a53a284002790f8e00417de49d70514c68528a2c54181441051535851c735b1c92516491861c75171c820515514718845e02bd431a892367,0xcb40fe08d78269c23e282edeedd1005af3e5a0000f9eceed3ec731a9bc0ce62b5a9c8420108027b8e569d25ea48423168e6f59c4af62aaa52d0a584ca63190818cb10fb45e02c1481a892367,0x9018fff052bb3782082c11f7e08207fc0ffab78acbbe082ca11f1409635bd80f33b40084f1bce46fe415f16982ca089aca3441451031430c54041843c61082091ce1a9a0104830100004828b0411a79a55248c63621a181f79255d7026cc09a65161718218a2c60860825931d145e24c7481a892367,0x5431faa0a2b31a3959ca2ace6dcc373364f05f14092da5f05d4703f77305e0f7144a22dac0012638500ae8bc057a8c3f17092368,0x1c601fc03ee352bb33168daf698cca1b49e1cfa5e60efdda79cad214e17f6530017c17bbed7dc81cd73331f2d6299b0845ff43bb60dd9190831cac359dfa3a52a54eea319b8321063478629463a0cc73d4e611945e02c23f17092367,0x89f913f41fe56440dac1b0a59dbb0ab4b68cfce75e74771875dfccdc29210251d6b630812116b42000529d351ce93be874a61249cf151da718d29bd92229cf551cc610d3798ebd431706c0f7,0x85feb8b276643d99309fbe746560b19f828bf20e3ba0c2663a97837fadb3ad0c0c4b261000471a8a591a088adc9990a563da0f28bc4a02b33f17092368,0x17fc8df807d543feb5e9e576603318a73f26699982940635f0ae3ba0e1be3921fec501f828ef697c0789365bf3e0d5625c9993884007bb0e6c63211f8268a94bae918ca5958a423085599b93294634ea642084890c52d0a612d49e02b33f17092367]
def local7g2 : List Nat := [0x3dfccba8c15ef19dd01dd14b92a468305dd907073035fd35c42ca5e01348840848400000a4d3288c6b1b4841094e108487886360c4001ca1094b0314000f83798eb33a1a8b80f7,0x1988ffb1ca4c6cfc23b9ba4393aa043222008a9068d24af407a8bc05aeb33f17092368,0x158b88629eea192904a00a0a1339f990ef7000090f01a5cfdf43057e421f134dd0c4e088410084b1191e31d8692cbbc76faca23640c6a520e93c268abf8e294844510d10645e20c73f17092367,0x324e1a892106202d1ac20e2e1cde20e3c1c1c3424a840031c213b0ed8b8ea83ce5294e52ad2829089414422c8630c445e029d431706c067,0x7ce09571a3fc372b09ed60e1527127c6dcd25d3b0c3e440978a8f42d120749645e02b33f17092368,0x37f26793b913ae631840868463b98c610083c39e12f10e313b1c4441088318c4218824204810846508c04000801000219825a2a4b2c0d13b6a89a4ae33cec11f4ae4f015ea4092367,0x1198cca38cc0c5f5b35fe34b50c3e6058d634922b022e0848bc498e902e1246c338,0xcca3a4c66f1c61f60901ecc8b1b99b840771b99b1580d8e131e817c994db5224400cb80bc570daa10b1aa99e2872e8692601148bc498e902e15892368,0x20820b27b27b27b27a17b587e70b3e12fd917d25143c61241ee2b4e660960508a910900d46f31d8490379246c0b8,0x3dc12cf50eaba55e69ccd38215e15e48f9213ba0099642653077cf8e05656b2998019deaae03dc0606f33771aa4d2854412ba7071c61c31060c404054050100214948b30204e4c1a689d79a590a68a8e28607de0dd3037110c36d921814540834821620f18945e0ec74617092367,0xe7c13bce71c4b4ca66127e7de98e4a35026884c8844b0326cf4caa186cd60ac8bc1da8c73f17092368,0xf70493847937c83d14a737b202a186676d08d27f4d8f93e6ed0000a6f297ddb8a3d3bb25ad89e7c6308d06720ed61884ef375d48cbb9842ca8c749ed434f062108529a2633e060fb45e1ace3f17092367,0x1f786c821d00bc1af815feae9b084430e6c964b445206c8bc05a8b32e1246c048,0xa08ae1c131c42163d80ee21804f11ef2afe7b19c2302c99c8428ae0f4018008420284e0680090842028141098031088203801004210f037982b33a1a8b80f7,0x8791eeae6a36e808d68349589680508bc420ec73f17092368,0x2be15f46578a1f093f0826862e27d6a02c95bdd8ebd3a1246c018,0x7ce0989a13c1f5c2101a0e8402b64583ad30378055fcc5d9dd11e87a9811071b7a6b36aa4009440030180480e058260001cd00208001e00280221465280180040108001080201313797ab33a1586c117,0xdf9eda64b3a6b3a5b19f8c92b911f7478239ed5268c3c26782e268c666b63294100ac92c5e0ec73f17092368,0xdfd238e8ab3c3434676aa2ae4102427740a698a127cbb933cd94c18b8087e26e887bf5d18047c5b11a2642b0f0230b061108472a772cc7171aac31086819aa3a1a701e8842252420de31b5c310f4960ec73f17092367,0xd200dbd0d1a06793ffec79576722091488802d30a744e6d867608e8bc358e862e1246c048,0x18aa36171d16541105580ac0b2043bd8de52f577bacbc65c09279587084012060b2a1a57b8a908421084255188210c6409061244840da37984bd569d0b80f7,0x157c8c09e917f530a0f43b3152be0d54dc4fd8bc47c2618de63ff86884cb1a07842000dcb2c14c23502324e0ca83bdd8eb33f17092368,0xc6df3b64dff6391557804e717f04751dcec5e2be25fc26caf6c7137fa7a67183c2110800214d26360e18cea8bc6342d20fc95bdd8eb33f17092368,0x8ff933c15d6d37e477ce22af0c60140fa3c09e594ee99f237e2ac8cf884c26b02ddc41f5698edb5da67245c221001a28c6a52eca295b42ecc94b30918cc67d4c52c4a6e1d08765073c2e7210a5914e634cc71374adeeb33f17092367]
def local7g3 : List Nat := [0x35756eb5c1058e6897078252c022e49f72b0155b8bea1f03e87a4e1714f28c1e01b98a0a1ab12480ba8bc057a8c2e15892368,0x108500902a18bc417a742e15892368,0x41420302198bc0588ad3a17092368,0x1b60a5624c19edde0c29c0942ef3833c9a21c29c09119d6580117c01674e78dc8d29f46db463d503e100fc21745a72110b236d5ae375f18a54b0a294e77e4e52909321d29a24e6354c710a45e2aad3a17092367,0x248111200d8bc053a902e1246c068,0x248111200d8bb793a90431706c068,0x208501102c1934057a742e15892368,0x860414203197c5dd6ad3a17092368,0x2b327487c53c3da3940ed443bd1b75375c31c118fb34047f0dee5ee46f3b2e7859ba9a5ca0359574d0a21210f92084590a31b065a98e784ce21108d2186370cc52c4a60fb4bdd6ad3a17092367,0x248111200d8bc057a742e1246c068,0x248111200d8bb793a863a1a8b8068,0x41f0efd93ecde733aae2a9f28efaf2475802c8856644802ea897a342ad2b180ac8bc3602ad3f17092368,0x4cc133f9e1b963df5ee70e0c4c863c66000a2e44c928d008492c05d6ad3f17092368,0x306740deb1f3731d9967b6c86488c41a28b2848e6b0c06292c1d8eb33f17092368,0xcbe65f0f7ed1f67cbc6efb20ed6e4a8c1184a285270ec0466f31d84b33f170920b8,0xa7277d14de0f37c978158fd959e82c109a62244013186e7748c08e8bbf1e8ad3a17092368,0xd4eb9d9992df877057e2238021e6266a8c8e4b00628bbad88ad3a17092368,0x4309fc055f8a77d7a22aa482466002ec4890a05c8bc418e8c3f17092368,0x13ff257c29f47fea8268424880eb803495c05ee9d3a1a892018,0x670cbf0fbdb3f15514134063c52f00ac862605c8bb797a74351246c118,0x49833a4e49ce47e287ed753cdd98f0707feab79e6623cb3b9df4b7a9b2e37512c7c408400811b11b9e712cac4a900ce8bc35f8ad3a17092368,0x34c8be06da12c9f789b4abb681e1d7997e20e4d2a3b082498bc213b5cb625401120828cc0be6f31d7a74351246c118,0x8a042440318bc4970ad3a17092368,0x288121400d6f3657ab33a1706c0f8]
def local7g4 : List Nat := [0x10c101820a195bdd70ad3a17092368,0x35265938c146b5c7cb46f7cfd6030924ec007028a0586f3053a863a1a8b80f8,0x11bd787b9d71a6d76f3d47ac3e3b4d80c8a36425492a10ec05c9345df8ad3a17092368,0x4c3ff2c7e8ed5f67431a579cbe1ae83340c2c29470b2ce04c9545dd6ad3a17092368,0x617909d8974f1ccbf8ec906010680c10f22a460568bbdd3a74351246c078,0xaa2d8fd5c67533b0bd9ccc18fc308161146864a1260d42af006e9445dd6ad3a17092368,0x3dc162ea1d574130110c15e09ce8984c69a4c860af10c15d77e432a85178d1bbbde664f2a03d09c51c9a75d173204110100210808504c0481410c314b2098a180d7de74a70a6d449840619739a5536511c758f12e45e20c74617092367,0xd5e08f3813f9ce6616442ef83c69e1102dec3bbe39f06a2f230072d700791d21d04c3b1842200840420a5858a4218d1b99a7760ea514b229cc6998ec4bf295aca5a1526354c911a45e24b83a17092367,0x826de28fe6fcf001776c1bbbc74b9dbe5b96cd713844390a41d56d1291092931929420a5295d1294af614a582caa29000200232964c294b359467109379b2b33a1706c0f7,0x49022240198bc55f8ad3a17092368,0x218105080d6f31d7a74389246c118,0x117c00e96d800f047aec03af045eeeef2f7ecce5c11398e76db54ca28301485d8962440630a539d8d6b6146a1124358b5ae355a11342dd618063004284651833c8a1133798ebd3a1246c117,0x490222401995c5df8ad3a17092368,0xdfe9dbd361cddeb5da87375a122a7b3d06fb168a6394c34b8c3c43b0ba0f47ba72930b8c42528a57cca4230854a5088510423487b18c6754c21108b218a5894c73c8e61004adf8ad3a17092367,0xbbab20193ad21d64054c0e0d44f8028faee8b40904661166003393d55a5e66448f433b3455c540072000a3379a89d3a1a8b80f7,0x49022240199545df8ad3a17092368,0x218105080d8bbdd3a74389246c078,0x55e08212fd25f8190f411bbd658e3c00d7e30e2bad86bd3393380d525238a3e43040121801184a130c652050a0ace85acee221aa26029bd8353b2513d0897cc8852901084260982220444098c1318263060608cda2f013d97092366,0xc5d7e5d75da03745e0b8f9d83ad19396bf467ae06dca9c078ca08b0106d28425288421108421b14210e3a16c18063004273c0f42994a4a67249cef3a4841033798ebd3a1247a367,0xba4b6faee3455b33bae3a28dc91a10b018884223a02351726acf808e6f3517ab33a1706c0f8,0x5d25b78a705af0eb018e02816de5fa8e0033d11fe66e84204736d630a94002953400094b528318e77c4e63392631a08330c2218d2418a50ea379a8bd3a1706c0f7,0x658579dac707583370dfe055f5c739e1384084d55577110007009b000a6030114000c802208b3793a903a1243a0f7,0x1ac0fee18dc01297c8dc668d17426019068d414a5ad6f52a2a5a9c9510c6129525a98b5b46552a6a59c080a1010db3793a862e0d83e0f7,0x67368e3bf82380c9d91268646544aaa1200ee8c23008c8bb79a8c73f170920b8]
def local7g5 : List Nat := [0x99f32f4cc129c2f36c9cc7e9ec7943bf833ff58a03387222666009c893044acebb9740b295c05d6ad3f17092368,0x39997c3dfb47e2e2338e1bc83eb05362a08c3ca8898088f06c2375208c6f3658eb33f170920b8,0x13baa9bdaf54a39d32e23ffadb9aecc0e109aa0268045587268d08f609e93c5de8ad3a17092368,0x18620ff376d817fad60682431eb22aa222ec8466d00828bc36029d3f17092048,0x6ba075bdd04f4a7929216043227460012450ce88a07a8bb7984b33a1706c0f8,0x1cc54658c2c9abcd24e47dde62c28c040c3d96f520c05028a608c08c7bb793a863a1bc6c118,0x14198822bc5a5938a8ef742b786b29590ee684785ba6bbcd6c5206830b860f9b64c0850005801484000a420001c00000b88000294153988a00000a006000c421143dd3a863a1bc6c117,0x1599386fe76c75e44c2bc930f4b8cbcaa06ea6d66763c49e59c7abc79e12e12e433998d77cee19c658d07309381e433b128a63e172d40d8c9c10c95c9dd6ad3a17092368,0xdae07f32c6103408ebd3bc8f204538103151759e000001bc280ce60b240b86f2f53a863a1bc6c118,0x141058ef742a64732919057910d08fb03d6bbcd00f2208279a759d400140080047000003800c0012700001081e4188c00000800001080200fe3dd3a863a1c46c117,0x8c0824405197c9dd6ad3a17092368,0x218105080d6f2f53a863a1c46c118,0x38d280a1c1d6810c7ad8c8b2e788774573b744103d50033a3c55229d233b32005433734228246e0000110ab3797a9d431d06c117,0x236a9ed583a4c11d26152f903ef681904220b686f04d3405a93c99d6ad3a17092368,0x12814321f913e2c1d6813272f7e8cf5e671b637440e455114494d55228e244a42113700005544b4622c26110ab3797a9d431d07a367,0x209501408c16f27534863a1a8b80f8,0x8dd100e384fc43bb0c8f15fca9e27ea1007b218b839e9621aa58466010a5100e0be6f2752086351246c158,0x63f00eb9c2bc47a5db955e80db62e59477c2dfcee04189c2f7e81f51ccdd584d1a074a233a8b06bd642204c1a4c0ca8bc1d7a863f17092368,0x108500902a1963dd66ad3a17092368,0x248111200d8bc053a74379706c068,0x7354f32f6453877e1de1bc73fdc0117ee0f58f4a8c4130843180000a20953cee690a623160e095bad8ead3f17092368,0x12790ca5fb6de74b433379c2623ad84be9b0e36688058a3714c92e07c95c9602b33f17092368,0x10e1321de87fb8023fc85fa7f4eb0e956432b2c086547908aea960828bc355a863f17092368,0xb4755a11e7dc9e90ffbd913431e24492e0ac645006a8bb79a8863f170920b8]
def local7g6 : List Nat := [0xd27fb47a50967e10bf96e180883520000c2aa690e06c8bb79a8b33f170920b8,0x445382bf68f4de33767f3dfff84e018c2e94c4a32230e05c6f3517a863f170920b8,0x885005029192be166ad3a17092368,0x12eb3332f3375ff6232dfe8b0bc6dc86488c41e622a8ca46b4e093008292c059cb33f17092368,0x883e59e8433c435f95766104863e60d22e84a4500648bc353a863f17092048,0x288121400d8bb7984bd3a1706c0f8,0x12c3239a488347202e40de24f03688185d30081400ea642207675b793a903a1586c118,0xd704a9f8a53fc92592820b0c4bd0ed91d7208f8f796df2d7441c2ca307b900008006808003160180060240029c000014000001080200d73ad3a903a1586c117,0xcbe4dfc3dfb47340df75af5fbbd942fe0366d047160e00c40a7695300726f3517ab33f170920b8,0xe9d2ebf50a1ddae0f57caec3c4bbaee89df183f37a0e1c780802267b0ad9244f7409693bad84ad3a17092368,0x2ccfbc7b824989b88bf25283c1cf8a83c1cfc4bc00daf05d2851521a006ba107caadec1799863de006acee2fa3b7745903a3b2ccb27c50411421420850810820679802cc0c01ca1259234e252180858618924e00d2002126da41961f0dd30378470a1030d744820f21519f45e1ad43f17092367,0x1ada7b6c3ba4e5e17e17c3882c86342662448aea02c9007c913ad84ad3a17092368,0xc541c90c4de6bfb5a4bcf9aed613847a403188f89a8b6c326d44cd00868bc359c863f17092368,0x107fdc20355f963edbc791ff5e68d041a100004ca68eb206a8bc35d69d3f17092048,0x2e7030fd1d706fe2484886344010e2ca66805c8bb798474379706c0f8,0x123826a81c657e831302d739d14078ce53edb7d86ce7c6e63f0199bd6f3943d8f10cc1e60004323972834a97b222428e0ca92c0584ad3a17092368,0x45021220199140584ad3a17092368,0xa3f94283b047001b627a21bc1fe4aaaa408c3c244d61350e788a0746f31d8474379706c0f8,0x8a042440319144966ad3a17092368,0x288121400d6f31d84bd3a1706c0f8,0x3a0f5da1201870d836195c81783ff04d1040b12d8960014e0a460220906f2f53a863a1586c118,0x1b6937bfddafa74988c7dfd53d31c16441642685020eac05a94c89d6ad3a17092368,0x237c7a7a22b493f68345c031e212050eac6805a8bbf13a74379706c068,0x7b2f71012cce798ffc2988ff1e74f90c897203bbe39e04e38e5ecc69e40e4ba4ab902721946000c0208441110c64a53dd737986227a9e8b5b9c791ee7b294841e6d63dac10145e02b84617092367]
def local7g7 : List Nat := [0x170f9660818ce512ade88443e0941caa6e94fd8d66ab18b1a61c004131ed72d27520a0a28bc0570743897092368,0x58e2bde7067cc73afb02b7c50f9388ec083e4448c8b4e3120648bbf188ad3a17092368,0xbb8281c0b8a63cc10819102e3b3923867a058f97c8be75ec608f60f0efcc018a81a640108010c4420c98bda556842739d8584ca6315c5396342a105794e952d2a0f345dfeb83a17092367,0x22a3046747400670043d3c48bd17a78d3e627217118b10a41b50640014721e884e473a0e839da301060628eb51c213c4490c14adbc9d431706c067,0x860af027bf14eeaf31a5031a0466e90ac04a8bc418e8c2e15892368,0x34c8bc54dd5034050adb00a1d801aec07870d5ffc9c06a9384661133be302b98a435693024220c20c86f31d7a742b1246c118,0x8a042440318bc4970742e15892368,0x288121400d6f36566903a1706c0f8,0x10c0828406195bdd70742e15892368,0x288121400d6f3518e9d3a1a8b80f8,0x208501102c1934053a743897092368,0x248111200d95b793a74379706c068,0x10448090261973dd3a742e15892368,0x218105080d8bc0588743897092368,0x218105080d954053a743897092368,0x8244050231983adce9d3a17092368,0x1d949d4e26d889fff14258ab1eb2c002d7c0ba7052f90edb28ba0002041514c9133bc001002131966114ac28884690431b8620c84c5ce9d3a17092367,0x218105080d8bc053a742e1246c078,0x228109100d95b793a74379706c028,0x720ce8e42b9d1cca74d823eb7caeb0125fb2ba1b80e119719c44a154210c129481210294bd2e6ad6003190bb12939e7538d0739cf161ce7a58e251ce73c98710c45deea63a17092367,0x414203021980ba5ce9d3a17092368,0x32f09fa32d7daf15d6069c0dc75e1b4dc0c6711250864404b8bb167735772288f4494228877d7977e79aaca90af3bdce9d3a17092367,0x10394d73c17f8b75aea996c8c9f05bcee6e8a8122e5a64442a44d969530e09480bfdee9d3a170ac338,0x49022240198abfdce9d3a17092368]
def local7g8 : List Nat := [0x209901608c194b793a74379706c068,0x203101408c180a75205c2b1246c158,0x41420302197fb9d3a903a1246c118,0x824405023180a75345c2b1246c158,0x885005029195bfd3a742e15892368,0x45080608496f3713a903a1706c0f8,0x82440502316f31d3a5c2b1246c158,0x218105080d7fbdd3a903a1246c118,0x414203021980a75347e2e1246c158,0x46b97b90094600e831d24e8489df930678a87d78162fcdc993082a828f2f18f9bda8f3ab159c0e9318ec318ee3b4a55c8623204109080044e70da4053a7e2e1246c157,0x22840304256f35d7ab33a170920b8,0x18b89c90efe2c2d37331f735a1e882e0500e824ac054883f1ce9d3a17092368,0x109900c08a18ab793a74379706c0f8,0x104880a046196bf1ce9d3a17092368,0x4902224019963f1ce9d3a17092368,0x104880a04616f3713a74379706c0f8,0x41420302196f31d3a7e2e1246c158,0x41420302198bb9d3a742e1246c078,0x104440a75063a3900eb7c10024003f367ecd9de45cd65520a34aa5b54cb9192c9a50da2060544452842e39c8479ce0040e70bc4053a9a2e1246c157,0x1ae0b04a08a5b1c684a94078d0ad6b6f19a05893ed933600b00700430c00800530200a000300913fd3a903a1246c117,0x860414203197bd1ce9d3a17092368,0x2b32630d11f258ab1e8231f621bd80def76e216b89bdac6fe8a4990002092e6aa244218d8329ced394c6718a420c6f1a0e781d06344c80dd4bde89d3a17092367,0x68c3f5d068c88f81080c182a3e0ee2ef4c4ed9e7643944641722108e1108f39090404210acc10858a0842d28521884030b9379b89d3a1706c0f7,0x43020a101998c55ce9d3a17092368]
def local7g9 : List Nat := [0x218105080d6f31d3a9a2e1246c158,0x24c0cdfc100cdcdbc38b97bc35eb666e69a3b890a6e31d064188442ce769d6851cee3a90939de74b2010962529c481a0080df3798e9d2e1246c157,0x218105080d8bbfd3a742e1246c078,0x263dc104f3d439d1cfac8df5dcbcaeed0dcb6b369321a2850214642294223044b580073b2a7a4cf28b4ee3a4883a52f3a46a3a5300cf45e02a03a17092367,0x218105080d8bc053a742e12470368,0x41420302198bba5ce9d3a17092368,0x1d7e3b6ee5ab5f813ebddcde5ee9f1776b97f61c369b0990c0ce224a24c850129154c284bc674c0423364422c82129c94a52a530ca0bc3c5ce9d3a17092367,0x248111200d8bc493a742e1246c068,0x248111200d8bb78e85c248d852068,0x248111200d95bdd3a742e1246c068,0x218105080d8bb793a903a12470368,0x43020a10198bb793a993a1706c068,0x23020910158bb793a742e12450068,0x64e535ef05fe2dd6baa749e573382fe744f35109124686001c600e20c5b8b75300a693c05ee9d3a170ac338,0x69b960180e6123203d459a510f6d05c68c75f4ab01a26898a58127408c42820e78460bc7bb1d3a74351246c118,0x450212201994c0584ad3a17092368,0x490222401998bf1ce9d3a17092368,0x228109100d95bdd3a742e1246c028,0x218105080d8bb793a903a1246c078,0x3000dc4e3dc9ee1eace08a0344045775500000000a60000000b6090802240440331109b3793a903a1246c077,0x218105080d7bb1d3a74389246c118,0x708c28470b4f347530d588e9b08e025bf070faafeb88e1ca849320e10908d81021318a573ca1084263108b2140018c63510631b0a30e83dd66a93a17092367,0x82440502316f31d3a5c2c15892368,0xafcf31c0efc4700ce067f80bc09eb9ed67189085f7003333b637a115e556237766c68447766d690009f3798e9d2e16092367]
def local7g10 : List Nat := [0x54e76e6026020bb0053e19445a40fbe114f9b39a3d524044ec6191c42394a5118491144338c670a06429863280e001c28014a60008018003b553132e66338cfbd13032a46330cd1654adeec75ea4092367,0x231182e1415395e0cb19714be7b4b0b36189c6e86ee4b441120ee2258bd1a2360de92c5e02c73f17092368,0x20922ba5f7b4553bf13c65c9c2a53618aea040ee227f3d89090c76c9348da0de8bc05a8c72e1246c0b8,0x20282318af34c15a5102008bf127c40d8488145e300c6360dc358da31806318c0318e8398c030020078c0810c2340d091946819c12398113206350c084108815b3ddd69d3a1bc6c117,0x89923a771062cae1125d64b7df3d5e4f8dc7a65d47f84442c58644443c7e0fa4a584c571520be93c95cead3a17092368,0x450212201994c5dcead3a17092368,0x20a101810c16f27520863a1bc6c118,0x7ee3b99c37c6c6745ed332982bcb3fde192ae868a54466a830e33420c39ca73b60b492c058eb33f17092368,0x1049a9d06b80e6b8f257eb4f9c7d91268c44461ad942a2e926d067609c8bc05a8862e1246c0b8,0x48e09832b8a33dd6abdc08d3ef66682ffc7407875b08e3cc2261b0a6780e1749209492b9d84ad3a17092368,0x889006049194b9d66ad3a17092368,0x20b101810c16f27520863a1586c118,0xa3ba52de2af96131a0afba0d428268148e596550c0d28a2607680bdd3a74351246c118,0x82440502318b3adce9d3a17092368,0xa1e0820be782086e74d3a73621fd05f823ec66bf1aad08a6c51b08021084610848408020200a1084a50d8d530574085419c85110590085a14042108461084274b92f14145e0f013d17092367,0xa1e0820be782090e55667553a3bf915f9f7e3eb0a780ec5131082108c0018063104830ca2244045309ee688ec1156108421084441244a0f145e0ee73d17092367,0xc398721d2ff10f51b6f062720fe1307a08c366244892e16b50c0746f3657ab33a17076368,0x25021120156f35182b33a170920b8,0x109559e11fd57df01d69afe36f2cc23185852546a0022f0c06e6f35184ad3a170920b8,0x82840604316f37166ad3a170920b8,0x6ccd5f1f4ba1227c16ae8ee420f4ea64289300c0606f2750c7e2e124420b8,0x44acf55f7cb70264f86bd6f6a4e106812222c66a450e06e92b7984ad3a170920b8,0x889006049194b7966ad3a170920b8,0x5eab1bf47423dfaec172c14a107d4e824267300a0666f2750c7e2e124260b8]
def local7g11 : List Nat := [0x14e1b0dc1719997e02eaa1b60c7a8644012866c230e07e92c5e02a53a17092368,0x29e3a63c1e37198eff5ee68f0e0608360445200a20e90c07492c05d6a53a17092368,0x10ec3c970f6be378a9dc9de284a106a80429032624ec06e86bc1ce9d3a17092368,0x82440502317d3adce9d3a17092368,0x2156786c0b285e3f759cb86d53450441f444d000ea6920628bb7984b83a170920b8,0x21820304158bb7988b33a170920b8,0x202901204c180a750c5c248d8260b8,0x5d00977258230ffeeffa4c27ec019108862a9564b00d2e06e933dd66ad3a17092368,0x1809cef4421cf89b84f66b524d421156d0d2ea842464040806f2750c7e2e1246c158,0x218203041580b793a862e1247e368,0x622325598b91c7eece2ca69a041a2330c00e64a0680727bb793a973a1246c118,0x63ae972b8d3ee15141828634e50c0a82604c893793a74351246c118,0x2a82d503cdc72acebc2cd2424fc86e3841a5143500f0008005007000011ea210410030d00c90b06000a74053a862e1247e367,0x254ba092c403848c8365140b31a4bf8ca7f9684404900a321563480c60001e00000e68160031200280031813214003800090108080000f23dd3a973a1246c117,0x101500902a17ba74e873351246c118,0x208900a04c16f31d0c5c248d8420b8,0x3cd774b45c6d47ba159014431ec31228eaa640062893dd3a74351246c118,0x104900a04a18bacce85c248d82c048,0x576b2dd77c9aaf83c538a8540e106aa46608452244cf007e95c5deeab3a17092368,0x2dd47b4fb2fc3c53844a2506342668822e2ad00648bc49eeab3a17092368,0x97fd8cb755e3bdc7058773422911058604450600c20ae07693c05eeab3a17092368,0x20ec726cbf6d878a21ca5d2876106a0884410252644ec07e92bedce9d3a17092368,0xeec656cbead774d8a791022882ef084444c62a05c88bd1ce9d3a17092368,0xf3c995b2fab65c6625c6628744130713c1351805289badce9d3a17092368]
def local7g12 : List Nat := [0x8996f5766e9b38e33f9d5bae49f1cfe8a4a244187ac68824678066f175208e93c5dd6a53a17092368,0x749b9dc5a6e96335cf9bf0bc0f1cf0b4a0b061a24400e6c94b7300728bbf1d6a53a17092368,0x6aeac8c56779b8ce269bedaef91c4716e68ee8460e2e0223400c40b296f008492bddd6a53a17092368,0x8741e49c7d1fef8e078a31c9de024a145860227032422cea07686bb9ce9d3a17092368,0x490222401983bb9ce9d3a17092368,0x82440502317cbadce9d3a17092368,0x23fcfbed7203fbef0bd91ee0ee4b2880c1146a467006ec29520666f36582b33a170920b8,0x7df0dee573ec917c9beae34e0c59273a94e03e93b7982b33a170920b8,0x9223faac11927d03e0e46062e88007356804c86be1e89d3a17092368,0x2cee585c093715034062ec9e09d54404c7e3793a993a1706c0f8,0x29022140157c3793a903a1246c118,0xd705066253a5ea8ab1874b58d91978d2e171a55c954584182c307842c3842100020480000196018008000aa000020004070000680840e73e13a903a1246c117,0x10c0828406195be1e89d3a17092368,0x346aee17dc68d9dc09775798a2186a343652f0c8060666f3093a993a1706c0f8,0x60e23a4af143a5143238d30e5ffe0a1511818798917340eca0420260866f3053a903a1246c118,0x218105080d893dd3a74389246c118,0x105080c08616f3653a74351246c118,0x218105080d6f3653a903a1246c118,0x49022240198b3f1ce9d3a17092368,0x53c678b71f076de1ae341831a4866010488a44ce07a92c5e029f3a17092368,0x29c53e2ce7e0d33a2bf4503161b7c0885c04a92c05d69f3a17092368,0x218105080d6f3653a903a1247a368,0xfbe033871783cfec070280a211753026a4ec800606f274e86a2e124400f8,0x826e1c5e1039a0a440a18d0ec2846a00486f274e86a2e124240f8]
def local7g13 : List Nat := [0x12bae6e4798d55a1010d249249f06ada00687c3dd3a903a1246c118,0x202501102c180a75187e2e1246c158,0x29080508458bc49ee9e3a17092368,0x4575e0fcbcc7cd38b14d831a220a04662222ce29008a95c5dd69f3a17092368,0x4902224019913b1ce9d3a17092368,0x346e3dbe9e29b7d03e9140e0c6a842204644422f0c07e92bb9ce9d3a17092368,0x208501102c16f2750c7e2e1247e368,0x21820304156f31d3a862e1247e368,0x55053af6e39572dd0026fd49e4371c39905104600f0800090022eb3205010c0040d007a000500707000af4053a992e1247e367,0x11102d07660294371a113bf36f063249a4804130a0c42c00025c00200a780082040d19c00000c028000080000c53dd3a9a3a1246c117,0x288121400d95bfde89d3a17092368,0x218105080d6f3653a74389246c118,0x114b38123e3460805eee0eeafa3c1e607227a4c60ba03346364842042420a542cc6699673b8eb428c6799473c0ea644001a4240d2379b29d3a1246c117,0x288121400d893d1e69d3a17092368,0x288121400d8b449e89d3a17092368,0x14e3aec9e40327e67fde4c6cb813ba03c4062a10c880088225555c7555da56b11348877e79aafa9220a0379b29d3a1247a367,0x43020a10196f3713a993a1706c0f8,0x23020910156f2752e742e124400f8,0x42fc00d9eadee0fa87bec3c87a22892280cd88a988ab777a77d9777eb76f2031c7450803793a742e124400f7,0x4c500302898bbfde8ad3a17092368,0x228109100d80a75348c2e1246c158,0x30c100caa0c7473e3886f8220c05bf7073590bf2cd0e894145978d5a25297255361ce94c9a84252422e2311941084a57a9400414a0d54053a8c2e1246c157,0x25021120156f36d82b33a170920b8,0x40140a408857fbe13a903a1246c118]
def local7g14 : List Nat := [0x490222401994c55ce9d3a17092368,0x218105080d6f3113a903a1246c118,0x228109100d6f31d3a8c2e1246c158,0x288121400d8bbd13a742e1246c078,0x43020a10196f31d3a992e1247e368,0x218105080d6f27522903a1246c118,0x218105080d6f2f53a773a1246c118,0x29bbcc73cf401fbd5bdd5d7eb943a1be4ed67189086c200042ce769d6851cee3a90c084b0294e23106841cef3a4000c73798e9d2e1247e367,0x218105080d6f27530903a1247a368,0x218105080d6f2f53a813a1247a368,0xfbc213d5bdc5c85c8ddede08a0306808b998811000000b70000800c70600a3350550442209c3793a903a1246c0d7,0x1750bda2381c3e050f90c185d448457005410776622000600a0000b90803307b3793a74319706c0f7,0x3b60ae4580bc15c59e65856cc4e8024d2881017930c1f1f7858b81d911f10c62008002006000c4210c6218800202cea2e4c346edaa66a34022284410842633cc52a0a712e4ae45076397092367,0x35b0e6b1acf44203801abccc7a36c42a9ccc2c89c9e30cfa6e536d478f98950cc540bc308ad87449ae4a8a0e08bc49b2742e15892368,0x4c69c13ef8d07e1b480634026246444eb08c0748bbd188b83a17092368,0x1f3822989b82537009b018e0874f803afc8ddadcc1f8eab605990b102d5a40006200089c007000d400123000f001400240320c4108013280002000010d3797ab83a1246c117,0x10bd10e37220519f52a9b7ea6e39160e2e042044440e92a1094d609c93c5de8b83a17092368,0x1939e884581c059a14df0908b1d767247cce732ccb7d9bc7338f3ccbf2cb5d060730534dc002802001019a5a559884789ae94ad66798cd398d84214a340c671cc84b1090fc49de8b83a17092367,0x824b0161d800df2c5a84fd9bca0f9f3ca8b2281c8dacb464800004649111110710533e222233330943793a994b9d0b80f7,0x2a9c71d39a12251f407e2db9faa185a2005004006001198003703030006c3f13a742e1247e367,0x1ae08ac1283a1c911a17171a1487d93c62fd23a058b1fe2d290030070b0052040080c00620000a000953d13a903a1246c117,0x400c0a204857a31d3a742e1246c118,0x400c0a20485883d13a742e1246c118,0xe464603721de74519f75daaf7b2cb4c8c24243124e60ca806492c89f8ad3a17092368]
def local7g15 : List Nat := [0x65c722287e23cdfc122f1b5cd7c99f8fb16b77e53c68fa23a8fd44a1a29e0077acebd8551208a80bf184ad3a17092368,0xc9c8046df6a1ce53cfef8cc37890c516248e91264ac05a913f184ad3a17092368,0x298f355674df8033bf98c548064c400690334f6ca06c8bbfd70743897092368,0x82440502318bbd13a9a3a17092368,0x1a62a0b0c4e44e09a9f049cfca3f2aaa9a0308104c0257356962900188e3790c0b46f31d70742e1246c118,0x2b4e0c80ee689693b0145f96ff9e404c0e377950d2ea48200646f2f53a8c3a1246c118,0x10c0828406195bd13a743897092368,0x288121400d6f3653a993a1706c0f8,0x894f52cfff8430313511a202a83bd13a742e1246c118,0x7751fe85f0456a6808f67c9820307a274e8712e1246c158,0x414203021983bfd3a742e1246c118,0x82440502317a27534742e1246c158,0x413ce0a37a2131c00a3fc3bd8df76b04060daa822818c94a94a62c8b69ce6719465a1067994658c4520a11000210b83d13a742e1246c157,0x8244050231933793a9a3a17092368,0x104480902616f35d3a742e1246c118,0x10448090261973793a743897092368,0x82440502316f2e13a742e1246c158,0x22840304256f3093a742e1247e368,0x5ddcc6308118fe87f27126c0512293b35790248a6ce00706f274e85c248d83c118,0x20b101810c16f27532903a1586c118,0x248111200d95b793a902e1246c068,0x860414203197bd13a742e15892368,0xc5c5bd169df16eb5d6bc97d39e4a7beead091240018400860b7530ec092883dde89d3a170ac338,0x14e74ba5c6e47ea3f54584062c9267273a90405c7c39d3a903a1246c118]
def local7g16 : List Nat := [0x202501102c180a75185c2b1246c158,0x22840304256f31d3a6f2e1247e368,0x86041420316f3653a742b1246c118,0x288121400d6f27520742e124400f8,0x2dca6534ef8b75aeb5f689d40d13ebb460a112344485c244ec7ab97530094893dde89d3a170ac338,0x29f80c6d6f1375dab14018f200f04a2c6805893b793a74351246c078,0x490222401994c89f8ad3a17092368,0x218105080d93b793a74389246c078,0x218105080d6f3658e9d3a1246c118,0x218105080d6f3658e9d3a1247a368,0x22842304257e3ad3a742e1247e368,0x40c02877a39d3a903a1246c118,0x2c8ad1f5a4a18984a5a40308839d3a742e1246c118,0xa604c798d3b47fadc59f66caf5041a0046aaed30805a8bbfd88742e15892368,0x401422102917fa74e85c2b1246c158,0x82840604318abad3a742e1247e368,0x218105080d7fbdd3a74248d858118,0x12fc1d8406171a30402e3f6822a040b1161511181721121a19312121120c0b3121224100a13dd3a74248d858117,0x41420302198b39d3a742e1246c118,0x414203021973a74e85c248d848118,0x248111200d933793a742e1246c078,0x401422102918b274e85c2b1246c158,0x41420302198b39d3a742e1246c158,0x20f1709e82848014dff99ebbec1018321a450317273a10b3a94c398cd294ee3a0ea398422904f8000108c62114820d139d3a742e1246c157]
def local7g17 : List Nat := [0x218105080d953793a742e1246c078,0x104880a046198b793a743797092358,0x8244050231993793a742e15892368,0x82440502316ea74e85c2b1246c1b8,0x82440502316f274e85c2b1246c1b8,0x8b0474736df84d27692c179b98c2c426012203260160103074401030755548540cb090a00a2274e85c2b1246c1b7,0x41420302196f2b4e85c248d82e078,0x22840304256f274e86f2e12484368,0x82440502316f274e85c2b1246c088,0x248111200d97b793a742e1246c068,0x885005029180b853a742e15892368,0x218203041575a74e85c2491c6c0d8,0x82440502316f27524742e15892368,0x22840304256f274e86f2e1246c0e8,0x248111200d6f274e85c248d856068,0x400c0a204854ea40e85c248d8320f8,0x6a14f92c558231f60cfea3f0d8c85164612acf0804a893d13a9a3a17092368,0x4de4de9cf865faa770c7c932a53ea9fe71f6ed400482240e6668d513ebd9b608a6f35d8e9d3a1c4b8338,0x4030228109189274e85c2b1246c158,0x69d115c0d9cc82c494fb2205527c17d741ea6268a05620b90014a54a8c24f4350e19506418cb11d06418cc09c4adbe9d3a17092367,0x218105080d95b793a742e12470368,0x218105080d6f3753a743897092368,0x104100f11029c0928e6185d070f71a738700752fc3abf23c7a16e9b059e45ab4680130a1c10a5e122a051ae2713246087379ba9d3a17092367,0x8b4ef8b745ad781ff940d6042a9feeafe4d768c40a248c00110e13290983dc56ad80ae893d13a903a170ac338]
def local7g18 : List Nat := [0x1075de886739ccb21cfddbe29ea6f9772aa148ced95172a8240600767ba74e85c2b1246c158,0x404482102c14ea40e85c2b1246c1b8,0x88500502918bb853a742e15892368,0x218105080d95b793a742e1246c078,0x218105080d6f31d3a742e1246c038,0x248111200d893ddc09d3a17092368,0x82440502316f2e13a742e16092368,0x86041420317a3893a742e15892368,0x82440502316f274e8722e15892368,0x401812408898abf13a742e1247e368,0x401422102917fbe13a74248d858118,0x200525f83b080e98d1a6ffb59408121121b1a311514112112171621211209082108e3e13a74248d858117,0x400c0a204857fbd13a903a1246c118,0x60225f83b080d4e346080647d0282a11312b115140117161109080603fd3a74248d858117,0x400c0a20485883fd3a742e1246c118,0x400c0a204857fa74e85c248d846118,0x400c0a204858b3d13a742e1246c118,0x400c0a204857a274e85c248d848118,0x2a71dbb8e9b2b1260cfadd090031ffacff3b514270048005900612dcb33a0303030006f4553a742e1247e367,0x400c0a204857fb1d3a742e1246c118,0x400c0a204858b3fd3a742e1246c118,0x400c0a204857fa74e85c248d848118,0x218105080d8bbfd88743897092368,0x218105080d7fa74e8712e1246c158]
def local7g19 : List Nat := [0x177050304aa530263cc6983b1667322053983ece48e31b1d00a7f8043fc8dc35ef6e831e9a122e0008008003004431939bd2f2c2c28a994ad346c9a98ce3cb08b9cef0de45dfec43a17092367,0x218105080d7fa7534742e1246c158,0xa0d0374a63cc1de8709e884866fd1df834c72773b706d84d05154b130cc69b8e7518cf4a56634108618c2090606c8000ad3fd3a742e1246c157,0x218105080d8bbfd3a9a3a17092368,0x218105080d953793a9a3a17092368,0x218105080d6f3113a742e1246c158,0x43020a10196f3713a742e1247e368,0x218105080d6f31d88742e1246c118,0x218105080d6f3753a742e1246c118,0x218105080d6f274e85c248d844118,0x218105080d80a7534712e1246c158,0x218105080d6f31d3a712e1246c158,0x218105080d95bfd3a743897092368,0x288121400d6f371b29d3a1706c0f8,0x402442102a18b274e8712e1246c158,0x400c0a204858b3d13a742e1246c158,0x43020a101998b793a993a17092358,0x218105080d993793a743897092368,0x218105080d6ea74e8712e1246c1b8,0x218105080d6f274e8712e1246c1b8,0x8e8e4030653e215e1315f8c86b398c2c52a112241211440011449911448832eab6c7d508e274e8712e1246c1b7,0x200c09204456f2e0e85c248d82e078,0x24880304456f27532742e12484368,0x218105080d6f274e8712e1246c088]
def local7g20 : List Nat := [0x228109100d97b793a742e1246c028,0x400c0a204858b3fd3a742e1246c158,0x218105080d8b27534742e1246c158,0x105067a2120032f09e88480157f08cf3a7f1783b0182cc22631486d2950e39d2f3195021160085910824593a742e1246c157,0x218105080d8b379ba9d3a17092368,0x218105080d6f3753a742e1246c158,0x218105080d8bc593a9a3a17092368,0x43020a101998b79b89d3a17092358,0x218105080d993793a9a3a17092368,0x218105080d6ea7534742e1246c1b8,0x218105080d6f27534742e1246c1b8,0x3a390085891029c09c6fc262bf190d6732640f00100730085009600a42100b3c5d6e407d27534742e1246c1b7,0x5275389b43a2a93a9c4da1d2d91048debe001acf3c79836a0ae491ea1c1628b027300a0200601002008b4c5bc9d3a17092357,0x218105080d99379ba9d3a17092368,0x440a7024a00f6440a7024a02f9f003cdfc77207306cc01da54388978d5012e210584c9bc9d3a17092367,0x218105080d6f3753a742e1246c1b8,0xe8e402100491029c092b35f098afc64365b8c1650fc281a4aa32c801098168dc579a040713753a742e1246c1b7,0x677e1315c3692c164359c7182c12f2123242379736a635853b0130043009300a3008300a63793a742e1246c1b7,0x119f10af098ae1b4960bcdcc61601f1111331137112a912e932d312211261325b2a029089119934432ccaa3ba07713a742e1246c1b6,0x200c09204456f310e85c248d82e078,0x43020a10196f3713a742e12484368,0x218105080d6f27534742e1246c088,0x218105080d6f274e85c248d844158,0x218105080d6f28d3a742e1246c158]
def local7g21 : List Nat := [0x473ff0f8f0cf718999eb82c1234373635023230104300730063005303131820923793a742e12484367,0x218105080d6f274e85c248d82a088,0x14067fe00f874773b7c36502923b040090b4a96953d0f5390e5350d5310c54111200043884730c66284250cc3793a742e1246c087,0x860414203197b793a742e15492368,0x218105080d97b793a742e1246c008,0x218105080d8bb793a742e1246c088,0x218105080d80b853a743897092368,0x401812408897e274e85c2491c6c0d8,0x218105080d6f3653a742e16492368,0x43020a10196f27532742e1246c0e8,0x228109100d6f274e85c248d85e028,0x400c0a204856ca74e85c248d8320f8,0x43020a10196f2893a742e1247e368,0x218105080d6f31d42742e1246c118,0x218105080d6f3293a742e1246c118,0x43020a10196f274e85c248d8420e8,0x38710ff881b248bff6cf1f6e3e60093735caba1d822a0223004201873b170296842188738547698d1334693bcc6919e241dc634cce0e9405c29d3a17092367,0x218105080d6f2c13a742e1247e368,0x1102aac310b77c00477c637784598b9039a5b058874491a4601e471001018a002c6001c40212082122a0a33793a742e16492367,0x218105080d6f274e85c249186c0e8,0x347fb9788272b78b7037a6775124c348200287392b52d2d5352c5312f529303a947280054084831086184230c73793a742e1246c0e7,0x20e05dd44fbea008fe66d100a81580ffd8004c3793a742e12472367,0x82440502316f274e85c2c95892368,0x218105080d6f3153a742e1246c118]
def local7g22 : List Nat := [0xc05b14661f9f741a300420059f02dde0281f85943f180004080002420001430000b1000060400001e000200018000140001000035c0107274e85c248d8320f7,0x218105080d95b793a742e1246e368,0x218105080d8bb793a742e12472368,0x218105080d8bb853a742e1246c078,0x38741847722053a96adfa95bf0b787bd2bc7b82cd0454072a0084014a9210a42be0b2a82529cec194a843445298ce0b245dc29d3a17092367,0x218105080d95b793a742e1246c038,0x18624ff5389540d8abe10ff88f79dbadcf9354366aa4514ec03182494a5ac39d2942129110c6319cb318cf51825318c682cc6345460e8449c09d3a17092367,0x218105080d6f274e8723897092368,0x8814ed408617cf87575c7d43a6c1628d1110627202011001102283229522a40793793a743917092367,0x248111200d813ddc09d3a17092368,0x20033f8b978017fd3c1f590404555775500000000a60000000b609008224044011330a33793a7e3a170920d7,0x288c34fdd3eadf80e46e3352e88a04008e8c888c88973052999b88e8988f89a99d44610903793a742e1446c0f7,0x23020910156f2bd3a742e16092368,0x218105080d6f31d5c742e1247a368,0x218105080d6f3413a742e1247a368,0x23020910156f274e85c249146c108,0x218105080d6f2e93a742e16092368,0x218105080d6f274e85c2d9246c108,0x697f72f116f84f94e50eea20586904004fdd55555555cbaaceaa9f7aa760068228344331130a03793a742e1246c107,0x2dbc4de50eea239f5004f1261477430035005100188770006b3793a742e12478367,0x218105080d8bb793a742e1246c058,0x43020a1019733793a742e1246c0a8,0x82440502316f274e85c2b1246c108,0x83e2f1e586d86904000c999b999b6a666a663673598530033223544551150a03793a742e1246c1c7]
def local7g23 : List Nat := [0x63cab2012010340363a006f93163f0dbe62fd16a020ec6134a210801084a5284a1114331c86671585440b424486695653bca1084a6084212a8a91114b22ec63f17092367,0x11b24d0050044e00defb392391b99b5a7ca649a902218446318003048b1299a07cc501198071084018840280818c6030c605812321c640fb49a2eb73a17092367,0x82440502319345ce85c2b1246c278,0x401702662194afa231002d7eeb72794e900910a26014480480704400281404908028180588422184418dee83441108a028084200021080011a45ce85c2b1246c277,0x46e8a01e242471adde88493996565f72794e948110a2385114045604003b4e07808a0206b024c1029345d78742e15892368,0x4d1b82082c1010a180a1b9f0459fdd6e4f29926a408861552b8a665053119a118c60000030241202011010840180f0288418c603020058c6321c6411d49a2ec62e15892367,0xa949aa492dca4d522d4cb5c4eae5fb73e78e6ea3224782a7e6dc4fa1597120866f3653a9a3a170ac338,0x45080608456f3753a903a170ac338,0xad4d6a4c505a8bfb8d4fbe005bfc4dc41e1454008249f14a90f81dab61022280c21b8c0ce6f27520742e15866158,0x82440502318bb953a742e15892368,0x86041420316f27526742e15892368,0x218105080d6f31d3a742e1246c0c8,0x218105080d8bba53a742e12470368,0x218105080d953793a742e12470368]
def local8g0 : List Nat := [0x1ecbd9438a840424a02d585b89bc542022a101092808a840424a02e820a164d3065894480796330c5c9d896085c3e3deadefb9d90d6e49648a0165437589d1061d0145184044187401046101105110041147f843f9e04f473fadc7f083fbd88000d44c0eb6c9e60040c3d07c4ebaba250c7082cc8c8ebeaa640882cf8ce8a12ce34434a6d734d1121cd29c58d34734834a75534d20d34a4cd28924930430979a30c1111cc25f64c30730830981830c20c30950c24a28a28a24934a24a3f345e02c72e15892367,0x209570f61ae5eead8641a34944080928810126f047933e18f20132c2b137c09ec17094015f26405c3c673cadd5f63456e7dc03c49da24e082082082082001152143d3300014100110b103d3300010128208208f08208208a0820823c20820821820b106da6606f06eaa50610c88167880c209109c0820b206b9e407006ca230620c77d57470c208d09b08209a65760904330904e0434090420820820821820820822490d42432490d324339e45e02ce6397092367,0x4580be4580be40235cbd99b943996250a846a8c3200c677094015f26020233f4db0cf1e99d9418ec36c8addcb9f9c10a58418428220429610210c00068b2444a5092f0a634b8ae0c4b6b0d2c63a300ef8a530a8ae8c3b2a0c48e99200000a21028c21631040881021040879020fd245016397092366,0xabce19cb16cc4324d1188009a231004218ead69e4706e0b031e46130461304421086630ea123981984905046630ec12b561a04af48485410e2100421004010840108429084210a2210ba1bcb3569d0b80f6,0x8971572e786b80df32780b8eb9478bb83462499420251e2ee0d18926508081060a9ffbe07c487b771760b31339a4209c30619e30440a5d210429000c20f48000830619e40209c5ce314eb034a41af2e446594fac5c239502a3d0312ca834c418d26448592da45c4392e223944a050ffa2f015ea4092366,0x6810bfc46fcfb95053ff2f70d021a053df277f0d029a256b9b3b88638e71b71917681b259557f63904237fa174b794576a26b01b2835da673e8413c308320d08308526e08500332d00300310d005b09acc4aaa682670c69230e614696216124679d2603067dc3030c83430ce14a21068a28504104a30a21360a28828a2162882c32c445b2cb0c514434514b24b11464b2c404104b2c45cb10a20a11528b1c832b45e02b33f17092367,0x1570f7191a40240215c59ea0f8ab900b372870ee24f4eca90090089be04f6591d150067c98c300c1f91ba4bc09d8784688a05309d050c70001430821c40430041c00400c61851c50cd1c614308208610a0cc1080ed1acaa81a50e44620df11e71a1070cb1d81c70ee1aba671a60e34210e011d6d91070c91d71c70d65544c61c34870c20820881031080c20821c70cf1c31c70ce1c330945e0ec73f17092367,0x6ae09acd608b72f7b28552c3352c336102c204f44302e3ae5af8b3f0171d78e2c12cac7c57f9ab83bf178795b24e793416f895100d810ada52fc0d7712715b283c5aa9b227270240d36d42f248410c41431038e38eb18bc860e3aaab12aa38e618c9870007def9df40160f3b699e009a271beb96220619863c65c18a29c73e75e29e7d951ea29050a1e7c531e618d1879c73671e9248a36d68a69c34a68a31ce89863862271ce9c8a082091e8246208bc057a742e15892368,0x12e5c928e21fc110f8205ca396730ee9251cd3e0b40fbc7760d0a28593becf2bc4adfc5020d54467da744600052ff11c12f21f5c19a68b8c05114d19e5a8a02b980183903882182218a0868e50f80e50e4117dd6d959701652751410410548d40cdcf30c524512e1529323279e820f468041141144141107be79ec4478821452ce9471c708214d1452f0945224f28bbdd70ad3a17092368,0x47f825dc10433c33c138f59b76cd90583a14e05b0e6ef149fecbce0cf7429c033ae800633c29e33777287375edf0ed6591514d9457561d44c21c11c53c11c0ac32aa0c00caa472289c79a521f9088ca36280a1c624710410928919674924624919b2461c430718618e28e11778e38430c11c3041843c61c71521c72cb2c55612cb1471c72cb15a2c52462456092d118c10c15930b40430245df8ad3a17092367,0x570e0826336f741d025b04e0502cc3ac53ca7b03c37bc6ddddd65c018a04069f2a4294948942010472092a527686d688d09b9c092a029c010842100e2131808b007488e711ce713e6738842108e7148e2380e2830e012ce731c62398c3104421044738ae711c071598700845114422753797ab33a1706c0f7,0x1938275e44e75e44e65ce9db47300c0a87e0997700dbb02924bc71d5b990a80c001ed1c920ef53bb02d3db8c3934b9555536cae127c460033be0ee28f60f333998c06ab61c844889d2ab000e3a034638e300016a0000028a40710a28600062600000211c085c94f9401bc013c934a00000001000001e792492f6c2683463083000005a40000000658aae5f6b4492c135ee26a1c418818000062200006782cedc001636492c9355342f0c060893c5dd6ad3a17092368,0x164ec9c13af227692f1c756e645a3bcb3c83bd4ed1cd24ff24795abaf46d8edd70460819cfae700eff30035c39f56acce9f616ab61db6e5d69014908b0431ca04e495b12aea220a4898b52388b94e22484e00000b0cf0ce0c40c41037c40e734524914000034e34561d34d1492456c91440c4156109443a0c1ca28730b30765e30c1c000028a1dc2871031075c42930c91491da24a1852f049dd6ad3a17092367,0x141f47793b568816d10127742b6e852ad746804a609efabbd9a996d35da66b0083cc8841082408f81568222048488c613cc20842402007b82d30081a11846034d1308880216029410280a228192294461180e314620842a084210e42108421084210842108421084212383793a863a1a8b80f7,0x11b24c7b1760c0083802b980320071f6e6d1871ce2d54676f62e4c6c162a6c006444c800521084188421088611369b273834914e1ea7d5cd144c8421084218ca418ce334421084632cc81091043cc661902e69345dd6ad3a17092368,0x53fc14f94df2f7835f02794bf1c72dfcf5ca4f86b288c4012d7c59f9abc11e04e3ee7026767330b221ee8fe60f28be34f3c61111702abd4e255036b3618b40001a0f0305c39fab1da4d7dfd10dd52708104277bc39dfcf1163879ac7a5bd6d2657021820860006041181242bb38a28af4a89620858800080cfd030c34131e28a98a30e3b358e70ed5238001408250228aa8a38c32c30e410dd841a43951048619218000a2ae29030cc0c40e3a83905f880bdd66ad3a17092368,0x6bf242bf887c17ae8a8d53fa07dd2576c9a7c8b917547ebb059a7de24fc13d76233d04203ef8e9361f8aef98715cabde92e11d672b80d278012af84ed171f623a63e0618818410e485a6600070830858830828e11010c164ce385f70c6da30218608600165695548c58c55034e54cc4a0c84831c49c300000c08c2903022bea3cea0b3800000cd9810430400032a30c8ae30c31ed0c53a913dd66ad3a17092368,0x2b3f0443e08177573c128e8a02633f207a233f2079357f2abf73a80daf442033996507955773e4b51b6d35c0708139b4f20db301184b0c20818410615344f34ac0a28001a6a521a6ae28e70b19e38f14239e08a2963c039a40e3be68e40ed8e3aae8e49248ec8e3a668e5143b838eb3c3a08203b438ea1a39861852261447a8bbdd70742e15892368,0x2d22f9e4af8800796016480d9fec3a06f1c8ac1661816612d9ce4ccc18db5980bb0ff1a539ed11e774d8502b972c38048434844da6d045f71e74560764218651530d2965ce3c92034d1780a74e8712e15892369,0x2de48f880a08c656f9a62022001761f123e57fcadccdca1c6ca79d38f3ce5c89e06e8385e52cd6abf2bbe56fc58f8aff387acc090001aafd8796c36d29cf6881b84c42012614a15e0041018a28c21030838018e00a2924ae496083be9963702105b6b9e1784082492f13602104596f9768471d05272c74731c492c127165b659c52a6190d4628649398492c926165b859882669b1566a46cb41a492d126965ba59a7a25b28bc053a743897092368,0x1eb86ba9628eca1519d118801d7446200d5d1188016606b35f0db4f1748f6b05f38c7451521026969a6a230818601a68411630658c69a60801820411c72471e514514bb8514530d9451499c514528794514514cbc514534e94514a9c51452c79481428a5151c450a41051524251028a514f9c50a41051501e51009248208e3825846f31d7a742e1246c0f8,0x81c5bc6600da8e933a39fda6c11c539cc1b2c168b2dfd9943c566355514115030cb98a500596a90a82ae653c468535f21212e850259017fbdd3a742e15892369,0xcb68fa2c5c4305714cca00ad6409b2b84df25f6f3a7d4c49bcb1592c11b2d6aa000cb7f67931574c75dccc264cd13421040851370c00004a8f841101000109924a049018820c2b831e2b428829c21030a2b240a31ae8a2ae2aa29228a89028e398f0a2b02ac29228a91029451439650e40a883dd3a742e15892368,0x1cc639c7cb6e1c51f097d644a9628ed9db3887e41b6b30169bd9e6af6a2e0576673428cea81b618cd90070be65f31d86dee9b327f5d451b9a420948238238258a48a19428a1d003604f30a7ca28414710a31c340c861c908a41a43ed3ce9408e08e08618a18a49428628e98e3a2b0e38e92a398e0a48628a18c30aa0ac0ab8a2a038a4928a3adce9d3a17092368]
def local8g1 : List Nat := [0x1db6db60a179c738e95893067b764302cfd33c78e39bbbe0e284b156e80001c4f004de11dc95c4dc61c588309a3b165a4d8a810c9049043a6841f9d09835e59038562c314b14820570816254f0c73c728a1dd2871475058d334308d08618278608509214708c1e02410c90490431451492436c90c81480d820944528728364a24e1c60860da1891022b8455ce9d3a17092367,0x154158fe333180fce89143a360774485dc4284fb3c270d9b06028081c7400c80085641a489deb2991000200844a5c96b6295294952a6a53daa4a94a4a95452a0d5312a4214ac5d4862547558e8429556a9023184229443948bbdd3a742e1246c068,0x1a098a0c2d0660da0097404ee0d821e1216712801afd3ddd9c95e4ee7b048c0240f46104211402251364559575038056159ff9405034a5814a9296a54d4b5d0a548d234a5294d5298ad2f625cc4b5894f4e740508098c3428bb793a74379706c068,0x64e0240db8bd5b5f88da86cd62da7cb3f86c171d709fc49e5b0de906f993c1f9aacaba9ff2cbe28c7cade6b05d2372fccd500d016372e6f2482088c920848620d10a7840e01617c501d0d315605950c6d739009a54b7183d1884452780bdd3a742e15892369,0x2baa754e0a2cdb83326e7240c3a558b085264902480040e2db83385a8e28c39f96df4408ace8e4f67393330636c54d8239ad69168f1eee9ddd7cb9b92592ec1512b6893a10440438e30da0411810c31a6a669871ca1c6660e58d184e09625b65755220001a6c06ca00619c74274c19621863a6482247b771e924f4491a6ae69e71cc1c79862a61e4928a0e5e8228bf1a269ac9a81c734720618b1881451449e5125d695bdd3a742e15892368,0x69b4c0bf0d3eec2c93cfc20a8420426c081c4806dad2116440ccc68c2ad20d60711daf0b3e26e06f091d1995262030592a71c29c70619c70208219a0871011890bf00869ac9ad9863463871c580588bba58869a99a598628616082514504504c3c504514a9a51452c61451491652251411414f31411454881451529e50c39209248241052e6f31d3a74379706c0f8,0x48c29e80280241dcb92bdb391bceb24e8b81406b9f2c93b1073bd888ec037fe0b8a74e7d8d52500091144241020c21040c0822080820861883081863020882020820820820c43c23825be088a08ac62c02827bc08890898208208200208221421262e62ce8420c20c8a020c10c082092088702202082082082e08d08d88c88684208c182045a292c5dcead3a17092368,0x24614f40140172e4af6ce46eab506f446760021a2e054ce0f7fe6bc31d87efa00a0444dc7318e1094c2320c5310e421c29200a2210bcda20256442977487899810a2108448084a421482709a3388e938ce10a462408ab1092328437154561504918853108641692b9d66ad3a17092368,0x244382160a09ce892d4686778b921b09f06e5701d502e390f84c464c402488461d1231a1260e4c75cce54964780aebb0e2ec11e44a9a96553418c32d127bb9d3a742e15892369,0xa0822820a2632cf9f79b70208111b0e0b94ae127ca1dd61aebb26113514638dd64080e026304e1384c135c96205950868b78841104c11182b5c02d318c6318c17054908c61384e3394a1304a530841984325842188423666f30966ad3a170920b8,0x5041057e04fd9631f20514241e076852bbace5f199535618b2e05401085c3185a41a28a9b1674a4a8920ca898f033c2b1176f30966742e1246c0b9,0x208901204c2ff7c3adce9d3a17092369,0x1030acb338064040f8651169051e673c674c45c9be43d27bf6600887158841884222044b066103c11b96450381000009021354d084210841208202c0a0244210888110420340c0200038002e07fbadce9d3a17092368,0x80880a08c45823101900eb0b74a20ec68cadc560106a1709103cda52ecb5994ba2d245194032a0652940329725c1405000a0801e500ca0194a029625294ae2b463280450958c2940a05d490592730c84200c65acc621064318a3ee7bb793a74351246c118,0x29f82be20285e52e0880a08c5c61eb4a20ec68cb1c5649a85c88408af510ad414e4c894421004000a001000278040100001000058000001400004000045108401000248040009001000200040008e2000e20000e000000340020c0200003108c23000208400080022643dd3a74351246c117,0x1160ffdfbc114049c9bec2eb955582f5a279a001420714541c210b4e10ac41530a398c92326260408f3382552780bdd3a742e1246c339,0x1299d63927f15b2c6374088c256103035a145c18d6acf77f2b17c9844d855413ca8e000227001650290f8270e63468ba096326a60d0933482d8de6a2f566742e1246c0b9,0xeb863d0bcf649833c93067833e157e09f8f60dc51ea58a3f48614c5218534797257578122d3bc0935caae00060069f024d93117cc5c87d345eee6ecf35731f538ace2fa078bc01a7c23d0e369ce9bc3369a12288d8ae245041c30703061029404849850400886444000680211887e3520d7cf40817601c83180c0036ed991f7815d041c102840205c356281a333c74e0902280920204081026c08f023d8055c090870a097805a1910b001808150696292c6532b545cc270204a814a65c86bf1ce9d3a17092368,0xe4863cc96103621d72483f12aa6d486ff1e317e0dec6814a0b0a2e8e25489e2512043a2870000071a4241d93204e76ac2a10d7c3adce9d3a17092369,0x4330efb10e2ad26c881b1d90380d4fe30f6d822845b8f8859614d45c0a7bb7f963f15dfd2b30169baa06d369b0e711e0399ba2dd7030542ad2a931008d15b4e005816802007921221121145591566426128524820ca1c0192450448b8c34c2be2923ce3c6c2470c31231251231473c71caba71c72ce1d5041121145144104b24929b64924a8d1249a492893d1ce9d3a17092368,0x19c90eb13bfd73f36f083436bc29b6d8aca5dd62608108125c188821211813adcd50cd03152f2a9132c8225177e3ad3a742e1246c049,0x34d416409010e02832c85241817796031a931a9bba339b7a8f4dc4dca73222a080801c8ff60e2ee44db36e52b01a0381b01084000a021415050842012420000980601801268004010008800f00388400601846081804018c45114a22d63946f2753274379706c0f8,0x1b38871af0d92eab4c6603367e7bfd7458cc14890045d8444d57004446a6d860189147c3adce9d3a17092369,0x39d75f8a7239e84b9db4d282fd681809a38d10400001d80a170ed68e414d2b80bad3a742e1246c019]
def local8g2 : List Nat := [0x833155ac6b44010142015852c45a5ba86b0074498d072c3990244b4ad31a132b7e55758022122e8220aa31bb142e26da828a40003ef0001c04001a00a78000a68000a78000a00003000000093400000000002ca8002e60a000280022c8000000080050129448418239248048000121248030020020800c30031658c30820020c3005706f2752074351246c118,0x4050463e9018b032e3460805ef16f42f24d751058f99a31958331566180000000004400000100000000000020000000700000000000000050000001200000000000080000800003c000000e00040000042000400000084000800022d3dd3a74389246c117,0x209867d9867da28b4dbb500b3aefcbbf853f20807258ab0463ec9600597f80e66e8b2deb2a4c9855a5101b1524e2c01a40820238a031b78c85f31c74c0410480c80c82035c80c30c328128128a0582810c11c33852451041092456491480c815320948328128550a25104d10d10514534d11a3442032045483500ca04a11628d3c11441c52ba449e89d3a17092367,0x69a0a09f7020fcb16a2b4038108a7f0f6476075c77a704713729928b208051d90831908326f69d5264090b11ce289c40000c8021a0528125004210804110c22104420a041104411044138e410880209ea2004c210841508219044088421080200845114422293793a993a1706c0f7,0xedb631e0a5624e51803b776eed5c3a2c2e8bd8a62395893a5624f06109098cffbe99e3c77bb8bc777142596d0b77f83aa2a6f0cc679824a70fe38005411429410268851808948cb8d41d39cf3a082a8258e482396592b352b0187226492dccc90446a124c50941142941380942145022020949124a24945147c0514520f944568abf1ce9d3a17092368,0x41141935a2079c3e6342070415974c6846329bafd6186c526630400187e331763171000e0b3000703204804b000090000b0000004980050007ac0000013600150020b0000d0281a00464118010040002c010000542008294082940542004046f2752074389246c118,0x20c504a6b440161a301987ac6843b2e98d08d63ba77abb82f14dd6ca383031309288352d4a18caa1b365d64a351d471a107a20e00014303e007bc15780a078107402487b80a181b1035a0b3405034083a01343520000005dd4cc03dd008e0e080638008318000100400001004002503793a903a1246c117,0x3d7aa283d001868dc6097fcab904ca29ff6473857e28e7ae7355f30116c62324d00c3e58c4a42c0b741b542960586094a1894221084210842108521084210842109e5108493814c03720a6003082e3090200148400442108424b00c7016b04d6008161284a08156808842108422523793a903a1247a367,0x61e5128f9d8009c0f676fc27391bd5dd0691c052a19228821771202822012002002b02021002101711001c010201a00022222500002d0223232212026001111001e01210224241121021aa3793a742e1243a0f7,0x1ec5dd0050043b20716602ec241404d62205c0f848280e76724723733721dbbface75fa60c62ae1306d1428c9d410801851420030020060c30810c01411830c502510c92211f00c51c01d04c55b06610a8e112000a49a01e04a4d904c2983041805860071c02cb0461804060061803860041805c60092402080461804460061803c60090070003491c02e545de8b83a17092367,0x40411014118cce6982512cbeb5e9efab6d5162059344c213c8283c5010040000420002000000078005004000a801000290040008001300200058008001580200040008421090600800018400038000000d000220880008001080012313d13a742e1246c117,0x113c17daa284c1bc1bdcb913c51d8a07123db15ce0c89044c0b6777397947558fb9db97f11ce00e531c7a612d55904458005948618e1d344ed8410408e102832280e80e0028030849261860844d29050a820d2120a79ef467be11e6047c4820c2078411d01659cb1c72881c91c71e74269a72e71caa072271c79a5a66964a680bd13a743897092368,0x1304c69a2549e664833e0729f1998f6aa003174271c06d2000629c00009805b94f4a01ecde6227518743897092369,0xc10456eba08f89bd5e98e8387b92e0615664996c3adbf1075d7147ed8cd16f314af55042409e9503e11aa0209ca80016f3a58829049819451418e18a69a28a71c294c38d9419419419a6a469471c99c50000cb3230c68c72030c50cbb430c68c71e30c50c32230c40c6f35d3a743897092368,0x504507422b49f7344a3bc121bcf2fc73d8642f1382c288444c6a100052b6522b3dc64a4fd084000360280a0065e0002b2002f0001e000016900188800f00000a00130241d498e0704a8400840280003d4a01c630a96002940684006b403f86f27518742e1246c118,0x61915d61915d61915907d8acc9a8721c958db833848725636e0cfa7d4e25503629c6c3fc5151c2a9a48150268aeaa842c67c680778f0458c106108a9020a20dc0dd3185096964113595486d7493383e5126f3653a742e15892369,0x17bf2f3e02f057e13b980320095e8dbcaf730064003327f9239e399b0ced637cb15e3113931e0c84180022104408c611800111422c36cf2ccd5cb2ee2c8d40000221044000a5818a55150118c23000052c4a6000cb324a5394c33a92c89d6ad3a17092368,0x129f40515e56e56b5dd693c0906b13a3900e0424728545258ab0463ef15ef8d656002fa6bee9ea9bcb23029458e871a301d05a6d651c5d52c208529e8808402df36020e0d841124f119493303c9177a27520742e15892369,0x31710c15e039f6079271c9608ec6e57e9decdcc7902078844780464c44dab11f562c169107bbd13a742e15892369,0x1ae0a0a2c0624e81a581c9d1a15ac00571a15cdc5ca6ebf5c7ead322c9a01e7f78b5aaa002c8005d600341801c0a02900059400001158013064007a800000125801406800828000000e0018006c61280a50012200840018c03004200803d46f27520742b1246c118,0x5b8096a3827472a81719976e74720339cc180725823bd96d968b56109414234c9ce741f01904e959ccab1e6382684730b14d44f6dc299127bbd13a742e15892369,0x18716e3a3927e9a1aadb40844b060eb426b30178f6f3a78e7258ab0463ef078aff165b65c2ad2a8a4b39266c230ff5ba9089994aaa78280d828088a55a32849508ba50551108c2904470c63222843528421ca418c8e9ce7449087a5084414839ce661cc37c893d13a742e15892368,0x20a2c130b425b804d6e20421ae042c9811fca7bd3b6386c999114114146d6483a50a3d0e2084e93bc000000749e01084210818101084890840cce40908d3908471c8b212c3194a4090a509084218c30c6f27532903a1706c0f8,0x208901204c2ff7a39d3a742e1246c119]
def local8g3 : List Nat := [0x202202823195289a901339a66679cb816798f56d9a85881864215dc2153c21458214b821084800848100020a828421881080810c430080e10842168581004251908018c2318400184130484220463080637c7a39d3a742e1246c118,0x125456098446981475f9dca3abb9bb82056811c98d0383c7559dea72e0118de6227534742e15892369,0x204a63ccf65b1d6817558fb0ee056fddc85f50720395080019601610ad2252e521eb3981ad017fa74e8712e15892369,0x208901204c2de6ea74e8712e15892369,0x631a84cde8873bc99cbdf67d3158415754102150aa4d5262d70745ed29c611904030904024218de4e9d0e25c2b1246c159,0x40440596504625b202cbcd30d4a204070739702cf79a6cd3594102b09ba4a889726b18a781421080000016050842000000340cad004001e07000000c422080010013048201008200042da7fb9d3a742e1246c118,0x104880a0462de6ea7534742e15892369,0x10410403ca6220588816e049463fbb9d972378a3b2073ee27077e47f18f5470460317730caea67c303ef0003a19ea8a320b1a3a2b9c404a040b810810620810c216106584934c0410610c10e492126db210418430439451449851233c6f3753a742e15892368,0x104880a0462de4ea68e85c2b1246c159,0x1418e8e5d02d812149de88557a211600e8e734d9b2325454805489129504100d5e249279eb92aaac1259c73a49c5a273c71671e5a8712a1c73249c73671e72a82071cd1271ce1c79caa69a682c9a093e3c710e18000618410620658c09428a48619c69044071a69c6020c271861c4d26f274e85c2b1246c158,0x410a0220583266f27520742e15892369,0x55360a7444f60c808c12684865a12213e13fc2dee86f8d21d228a6c2194a105189e56c002eb001e0c0000000009ac00a80000001458016000000022000a1211bdd3080010c40401a402c4202420d812901ca0e00e702d6ed014e001c070003d46f274e86f2e1247e368,0x1a64dc10208928e614842402a11bc1387824ec80f9cd304a20b7d47650621255436f4041442304d01e51539a88174135b2dc5816104570594933c40211067c780220c0c918528420de63a74e85c2b1246c119,0x1545a826a41bc881447b431eafa9c4aa06c838003fd6ff9b9227119186d09c5845ea24893620d8358a71335c2a480f828264de6ca7534742e15892369,0x1364e6371a06826e24be121c74486689165e90f9acb1c1ded299ccd25401634f93b0f71584799e84236aa0a82751d4a8a94f6a941504ea3a95252a0d518ca0a83bd29060acea71d4356466329586a8c029c0021c034693b793a742e1246c068,0x542d62bcad8747309e4b15608c7d8377dbb3356956104105145c0010a80846a4cd4a8aa464bd6c3a60d750225127a27520742e15892369,0x40b8eb3812b1c3714708817ebf5389540d9170057e7dd31fc4f280c1348a081089c232146370df223109991aa598208de6ea7520742e15892369,0x2803186b8240e803afb1984ec424eeefc25e88f2ab9208180b36d20a81314c8136b8147c18ab5c2740ca4118241176f274e85c2b1246c079,0x450212201b2b6f31d3a742e1246c029,0x218105080c32b6f274e8712e15892369,0x510242801ade6ca7520742e1246c0f9,0x8088088088082202c12c12823130f34c1289f5e0ddfaa6f5450548d9f47b9ec7e1b26c1aa608434080000801304a0e0100048100045e02800b028001042308001001a0604029e7fbd13a742e1246c118,0x2022020a08c4dc10030f9a6094408002f117ac79a03080b3248941c4641c08b000000180000005001800000040000000e000000034000000a00000024000000000000088000000f00000038000000000000000001e53fd3a742e1246c117,0x43020a101ade6227534743897092369]
def local8g4 : List Nat := [0x40440424a8495092a2b084c2234c0a2cce38e8387b8d3fe78287d6782c1c492042082c050fb13e290e8000d0c030e192212090410514106d90c90506416f38d1609011609043041600071e99c41091c596620a98410a185966a2b9a410b1a5963ae6f3113a9a3a17092368,0x4115075220538e3cd1285ce0806f7b6e37b500c649350201a76738d3aca4e75e000001c7002340016003ce004aa002c0081c009d80059c0a05c0440020000e008022000a1004c00302030400698034c6f27534742e1246c118,0x44f0456818b4490a40942531e60ee47cb913c0dd06531e60ed5beee72f0a7f6924c213eb558fb16947440ada9bf6ff628f08abd01a3a0001813cd2a420920218c08c88a02600c00a00420844711030a30d08d00a3b4bba38ea0c31c30e6184b6c3c492a8c31e3125966b8cbe69ab0c32031a5143da80bfd3a743897092368,0x43020a101ade6ea7534743897092369,0x2082080788814e84948812543391029ce9d070f71a781c0c2b91c41eb1c4674f04633dca348a8a86c0fbce8403821ab8831cc0c42ca9008a28a20828a30828e7a4c8e20830c1864a09b448820c3186148a8d9420830c5962f46f3753a743897092368,0x43020a101ade4ea68e8712e1246c159,0x2831d1c805501401a240501411bbd10906bd1091ede4ce5ee7395c2c14031821414e840808abe51471cf9461453853661ef3a79871461452a5228b071c69a514b14924c9c72699452e52083471ca285403cb20e18000228661609830c5000142041425082142104445082144820c65124944b86f274e8712e1246c158,0x10c082840632f6f3653a742e15892369,0x8208201ea820aaa88814e048ac8814e04a2440a7024dbd070f71a73870af119d3c118cf126828b68ac71430000be1bcd063bae0e108208d86d0620629492c28619c28c5a6b8c18678c418a304061a04126aac921868922de6f3753a9a3a17092368,0x10410410403ba440a7024ab2f41c3dc69ce1c01f3382df137883b53dac47e31ea8e08c67b9c4168a3a181f79d70001b1820834420d60821040d21035c41030c30c51494c52581450c92430c930328a21428864a2832080c32100c920d24b2c754b1da2cb0c71c30c73c324738920704823d379ba9d3a17092367,0x20a0c7472010b1004202d91029c0936f7a2120045e88480003ce70b0e3cc1dc8319548202c850c30e33a3383952bc50c3203124a8c1230c88c71cab270c32431e7acd1e30c98c618bb660ce1124640638e08003e30808c08414030808c08a2c231608c2820c431a28c4346f27534742e1246c158,0x20a0c013070f7a212000ef2671a7019cd366ab9d6a284d5243482012b7614a5394e751cea51eca394f08c0f18c2f181e06394ef93cf293f1279df33c1f5814eb72cee72f2e59d6d3c17483d6979745433dde6d0c19c0a2946719c512947019c922946f19c2e2946b25b3793a742e1246c157,0x29820949aa550454826bc528b15993186455d816f81250159f8125005b220536fd4e26d0e9540d8631cf2c0b27b4cf6c8e194c19ed9e94c10d942c09cc44e9508d285f76406205b64a06000a09043a44208a09863c6440940965be5c608c10e3c03c811c21c23751c21042641c618a187165aa59c38eb0e71249e19e1b959e19042e41e618c187965b259e38ed0e79a69a49c69257c97b793a742e15892368,0x54e3829c0988bcc29038e84800268480373d0ddd21d203844052cc8201c863421b3021786e10860c0866108431604340842193021a842363066ef0c4185415942c084270072139c271074139c28487614202c63b010856c08421705c170424046f27532742e1247e368,0x43020a101ade63a74e8712e1246c119,0x29704531c1b134f820004ff81f058183609a08263184d0798633b800000090040101c0002801004070000b0040201d830200d010a02800000000000000000000002d26f274ee742e1246c118,0x2aa9c70446fba120002fdddf492392d66831e780d14274830dacaa410085ad295a56152c2a506ca0a561a5434a06f4084210a5618cc3188711084210842108d694a52359a1de6f4680c2053d2308c22a352308c25891230ad284a16e7232e4050c0851208507084212523793a742e1247e367,0x18d07e080197b33d4728c8119e04085d5555aa55995000000000000000b00000000000000000c000000000000000000000d0000000000a009004000e0408010108070303070602020601cf3793a742e1246c077,0x6982d24e9044940844060c35069e08064f04003be6982510200cbc61f89a13853bcd911826d208003a2500e102ec77247a43869249124a49145144a2512926980986f429868a2c2299c73272692aa80a86fc4a868a2d22a9c73672a928a00a09046a088a2e22a1c73a728bca28b6812015d940a28069a8a34a331a41071d51d390084582098b0208c8025bc6f31d3a742e1246c118,0x10c08284062de6eb653a742e15892369,0x33a820c207d0ac112501c1c49403ad80d0e044f822ae3d6f532b15440834f94ad6c6681903a2d92a6709c2739ce739de709c2739ce739e18b9e8e3d5a7b28e53eca2218421a0427e95b793a742e1246c028,0x43020a101b176f274e8712e1246c079,0x280a80988c71301a2446171f0401f7406770dbf2ee0ce311dc5c69dd19c041081c7e318c6334c6332c633cd030120324c94c4c0580cb32d7230140328ca54ea6a6cd9e1b45be0a209c42238421a042cc8bb793a742e1246c078,0x2b015601b15806d4e76c15824a016bd7644e6908814e38fc4da1d03618c724932804ab8ba78a87042eeb24bd40be92b40d25040c30e38415605405344e1040020965bc5c208209a6be6c40882186406462141941b72141965a459469a99a518628614492786786e4a786596a9679a6ac69e618b987a289c29c2bb31c2965b059c69ac9a71863461c82057895b793a743897092368]
def local8g5 : List Nat := [0x45a2dc092910b41c6c02d7b0071ee83460084016740bf8afdce2d38a22381a985088990a8a93e63c60411861851461859661879e492484484d38484492a224924aa912492b20492492212236e922124ae892492c244924b281299230c4804812464803001864930224861864930a448641049312049008e70a08a68e5686f3653a742e1246c0f8,0x21f70f00a03dc3b39102bcda83dc3ea553ee58fc9a4c7df6658e6cf0b6ee162059fc02098e7105092a105704aa407296daa9c05b2b84a84142108427018e1384a80216063011600c1304810902131426304c60ccc1300c17b0c00982608c2118426284c6098c1a18260183061801084212793ddc09d3a17092367,0x173f045591427b9d0003fe1cfd2b9538b6387904803972522246044a4cf0000002c0300c060000c00c03018e048140700a1084000002008001080010240d0842040422c06f27502742e1247a368,0x555032b6bbe008194f3a7d6fcd8bfa09eb9ae59ed655208041d673ac840908121030204840908121031204210846b39ce71acccad253330610108418461110841856709d414202e4042108421084a52ace53a4ad695ed284a5084a508421094812393793a742e16092367,0x62e86e740011f2873974a78edd44834ba202043a528426b44a63140108021000200040009c010042008400080010002780421084010000100006000000200008001080012c00400006010030000880c04882008122388a0280e2208621808025a3793a742e1246c0d7,0x52fc5510880344609118fa6addc68060d0070f0bca583c4dbbb4a20402079fff939d8acadc76eda0e86518608055488a22228820a289041009e40269a68a68ae3c68a69aa1e69a6aa71a69a68a68aebe68a69ab1e69a6ae71a12298438f4013811c330e38059679ed1f21649271cd9d2921069041146048a280080d14080c79ec1e81c73272041058e6f31d3a742e1247a368,0x51c75a0876780206440ba9c0efabbee5d59379486912e8208039f0848908490d0919ab430c0018c421b10e629134048408484094214350f2108439ce73a1a8810842042108427584e2e06f274e85c2c15892368,0x154fae1ac600a7fa2310024740ff90fb0e46e3350402e88408018025892c92492c9249a69aa924c249a49329269a69aa924d249a49369263a4b0e8a430a01631618a38e924e2690e492924ea6912a26426b90410924f24990820924fa49a021c79421809469a90490502499a68450e6f274e85c248d83e0f8,0x50150150116c5316c532994ca6a996b5aff45a65f8b388182763d2d670853ad28c02a5cf7485ff0a80ec290e8221842c0ac0008421705a318421084e109a0678421084610842a09c21c5c210e6c1ad02138433084210c4210864109823946f27534903a170ac338,0xd1da805debdf1a9004ece6616446ceb4f39cae6689b451250541802d28ead76c76a6454a7a9b863a53cb214af0a218408190c708d280ac348de4ea40e85c2b1246c159,0x54042610fc4bb171208447bba00480e410680b68744bc99e39fbb8839a824198020008a524882084a2212702d8272872a78a78a79e79e7b078a78a79e79e7b2186700700e1d11618041071cb1d01061871cb9d0983bef0e18468618c506700700d1c80071c91c81c72672083a2084a08bb793a742e12470368,0x490222401b176f27520742e1246c069]
def local9g0 : List Nat := [0x4b8ab87b2e786b97b2b73372870ee56c3224e0d182a10128e28c323ee00c604940582000a3f19c86f347d05339e2a8020448a28800600811218620018028048618a14a010e2a044110ea813e090f260cc00eca404610ed2214008eda009039844e00cb1e04810cb9c14208cc1a09031640e3143915a2f016397092366,0x23d8bba00a008a3e12f3c78e3d730064010ef2c659126b6ec0b76e6d1871ccd413a18c103be069e258976f7f5cb5b916ac8b8dcea7401111400c00900c004818abc104622d00fb2a0272128a022528f91e2ae009ae902820d85f2262898dd28f25c3c00044400000002ca2c44da2cb10b2c45cb10b2c458b10000240000e20e0946ce38200000c30264c08c30260c08b10b0952cc1c430945dd6ad3a17092367,0x29f2f7d0050045b973c04298866fdc6b40140154b65b010abff97df0171d776f3a78abbc3a30e391437147078120a6c39c11cc19ab40065ffc798ab4dccc5c2e8321754a41208e5904024fa499d724f8399df038410438e412590390496592c9649248239609209210411a68ed1a3964963a859a312209b93a1596375a21228bb0fa959e17d828e019595552014208592596d9739621228a68e69ae1b41a28e712704eca71c11c39c13d19c70471c142704592584a9672611a39a12c69c90418619e49e1bf31e78678e78704879e19e78711e1964961ae59e88668e686c1a7a0184104104186704184a4c80bdd3a742e15892368,0x30be077ec1f981f8808978e3ee5e2a7e4a24404346a1794bb4cf39e704174e44f9f700704f0e704f1d17492402ab338d99cf18ad3028354d19c000097c33fda3faf3c6048d12a478e5861012c810e10630c310208208808208209c860f0d6c087981961700208789608209d062eecea287a018df680208709588209552dd020821200c49230820820c30820c31248cc1231248cb9234e1cc18404b20418418c30c2082084086882082091c0028f81142026f0048c480912e9430c30c31020820820820830c308208b08208208a8820c208608308208222e0820892a7c3adce9d3a17092368,0x670c78670c78808abe42f38cb314d1719675d249014f4cf1e22e117c5ddcd9eac50960800bfea5c75d59c61de602e08e934582c766a55846431070c00c49e52da90b844420744a261998c688429f7042c66cb0410440850851425c50851425450820821013c12080582012080562010813827870c41c31c31020821c71141c41c71131c41421444451cd0880481122073012ce3f1ce9d3a17092367,0x68d411892402240721cad205e58055022ceff4a70372182e27290cd14107192942129424a229101424e01598119052401280a388c6038c03180d300421044108441086010842178421084210842c3042158421086e108421b04230842309421084a508444110212413793a74379706c0f7,0x1776120a02c241405848280b16710304dc09a4f28387b853ce9d775f7e9623e716db3df3a180a170b2c0086159236242a55052c628462358524460451413a50451413850408208e95004f08e0128d204d01201030811620601451450c30610c13450001450c30011a680f9a01a680f1a03611a10601450610611411403251a204082082082b82082082a8209e082082094082982082082682082082c02082082b0209c082082094082802082082682082082082a0208289e6f27518743897092368,0x21e68f880880a073ec404063a3935690081459006accebb78bbce9e30f092c11a3a7ffd95d6c9668b9688346e00409018610328e5c910ef825acf0330e4c708f0024aae82592e1620820208601018218251402850051402650038e11010251010e102308208590402c90402490402c1040250e400402b9440038239023440828a28a41022040841021e40840040869440020a28a3902b640a2082084102a440a4102a240a40040a71440028820820828a6082888747bbd13a742e15892368,0x14054050304d404440b11029a3b1668950b165c99c8de74dc62ae0ce0ce6bb8998a48286df7810a074221c21b0001c06802406401830c30000000c00140130c30c01430c70120090110041001002001000001400c500300e00d5d500020c00000000001000f61600020b000000000000280009c4de4ea68e8712e15892369,0x935015015015011102f3f45aa365c99c8de74e1d9038b3016231b87c06333d8ecd7415a3a08a15439320e10f140fba10e3131c2f383124100a44024100a0402000014500994014500894002082080182388202c88202488202c082022861861822024021821802024001822080aa2022080a82027b420808809008200809400269a088202b88088202b0809cd8820220240208020250009658258268261668277a6f27534742e15892368,0x50463c9006900484334c12890e08a33b7d9394c992866086aab440e4ae7042e705edfbc01000010001c0000006c00718010070e0040178001d000168001c80010000100001004019380108001a8020006800800100020004010066e00420006e008001b002000400080010040180001880070001e01c080001d0200408822010052002c18003180042002b0a5200240b5802a08c6000c0a50027d26f274e85c2b1246c118,0x34c10ae2b01ba4ded300204502421251bd56e66e2f03a41004495c9102f25bf103e682cc24892a92657789b40d8636649feccf9c85c327b74176234200c12c0121235f7c05580410f842082115084235d08387ec0e80cf9c801c0249555895c0928a3cf8cfc4a52c505505bf850555579550f3df3d40824cdacddd0343343ab634334355134da153513c634da4f3462d145134d08d4423643453459ad34534d69534d35b3cd61860d51658d94d30d327b8d30d35c54d34d74f3524923545d75d66575900cde63a74e8712e15892369,0x5dd4054054054050304d4054054042622053916440a7228387b8d3853ce9c79f13157c18018ccf7ca269b8d90261e420f6881895d344c18840f6553ca40e30c0c830230c0c6302000008242040f0800e3c403ee8e00a0820820b830000c08001248099201248081202cc92482300302004100596028580596022580bb459608c00c50079e00000001a680a9a01a68091a030d9a68230031801c70000000000000071a6f27534743897092368,0x177501501501501091029c09d1a0e1ee34e70e14f3a71e790bc660587f157c18018ccf63b243acc40b551c69430038e181e0031469227dd1461040551011040511016441071c15870471c148705a4070410412492172482492132486cf24120804120c04b2ca60b28b2ca50b29c38b04a28104a34120a08826c3793a9a3a17092367,0xa08c69200505dcd304a2040138200fb298a08648a9dc083cba9494a949547ca925002890000050000b000038000a8000000005a4000000078000001c00000000000624000000088000002000000000000000006a400000009800000240000000000000000480080001800004000170000300002004200040210002018c001802100060084000806300070e6f274e8712e1246c118,0x11014118c407a0b39a60944080919eb893cb6d335288249aee041c84528845288c4758a201a4035a08b40d6820d028807ac0f7826f03de093c000000a201c9039c0ab80e7028e000000000002aca3b360d60e032380cdcc01802008060180a028060180401006025b3793a742e1246c117,0xbeca6537d828b29162820280202c505b7066afda421e04940be0494231d9039f49220535b70670f5389b4aa06c31ba24dfbc388cc733c5125b243ba806c5523051646276b9e580271a68f11a3861869243c690e51450e38e39e79521e50e38e39450e39418e61dd8dd5860da09cf006e00d8df5ec00800c10468e69b29b41a10e10490e9253254a410e28a79479f39f51e2949a683c9a09a64a64a105a9a64a068e6a0c1a9a03a43a4832926b8e7947a0d1e9965228a2a288bea22a284284230dca2842268e6a2d9aa223a43a48b8928b0e7947a2e9ea2a5208208208a29a08a09da6f3653a742e15892368,0x424a9c65988082611c1a5102025606f2f8cc683e51f5d441a5f528e7528e935d21084210842160421085610842108421085c10842168421084223a80a508044d414910033581388c0208421088220842108827501450210082008401e800421084210842125b3793a742e1247a367,0x135a082d41e04c053011b000b60047c316ba04286e8340214380f75754731fa8550802c1150202060a3189a66086269a6988602b566cb2026989869981aaa86e2a180000626026480a2803aa0018618618002a180190606424190406f101904084081c11104081901901b0a90186400406ca840019060641e190406f9019040c40c1c319040c1901901b4a90186400406da84001861861ae41029040749028651441011010745441051410671c40640732a4067068a24004073a84008863868068063863865865863869f86f27520742e1246c0f8,0x50102ce8014d635280b9eaf0170478eb316710304abd4e255037880bbe2cf89782ea67b8483b4c460154a258c82668893847c43c47840830c45c45800000001191180c30c30c300a0c04458454058051810440441440c40431011042c414110110428414115b15a1c71c41440cd1050c41121051044c41471c57457010411051033041431045041441151050410479011ccd0de4ea6920742e15892369,0x4c432d3802a7446200b0905003b0afefcf3b7c1e238ecd820180010353c66084c130cd108ccc3159c614cc332ac330ccb30cc3019b600cc3326c330cca30ce97dcc310cd310cc319a6330c6698cd69b0d335a6bb4cc3110d410cc321a8330c86a0cd6a34d435a8cb506404cf635906342f6346a6b43e6a82b6b43d6ac2232509088c231cc7089069e8bb793a742e1246c068,0x3562ec523524802b5d8d4021eac5d8a46a4903d43f9ab0f62ec35e290d635236492804d96f313e12e2ae30c8a02e3acfa2d38121b11f987f043e10fc13f963c49e3ce650085425427f913f11cafd0d74a5268069228884c8010043059c53264891226689131c1698ca20264a90382800c18d1a6069f062040d9b626df903844e115d08e11346911a386cda3367078f3a10e845f0ce84346921a3a6cda53674912243ce121e601d41b3c14d9718c03042449a34d103a121c39b36d50bb0e645522b400ce931cc8a022449c38e0e3c122c59d3ae4ebd167889e22ca21e2268d263478d9b4e6cf1e0c78336807831c38a8e1e3a7559d3c50a1f2c7cb338a7cb1a34a0d1f366d49b3e7c41f10de09f1070e2c387ce9d5a74f972e5ca1e2e517ed176f27520742e15892369]
def local10g0 : List Nat := [0xa3e12f1c7819f0abe42f70ca230b4802e19446169005a4c5e35a673c6113a622e05a298b767127e5ccc0ac5c28ae17411021c514406404975a0610898170a504a71906208a7d60892942660466d806308679508919324a1922830c30821411c50850471c13870471c13470471c13070410440871011010c30c82024480882024080882023c808704708b1c80012f13adce9d3a17092367,0x24a0212501150808a84043b1667454200565c99cf191bce988b8a9cef38ac30c0035810c1b25c84923c64963c45864be03cd860085c003ad0800a3c2038c8a014504c14114504b94114504b14102082482082a82082582082a0208238208298208240410410408208208408408211e08408211c08408211a08430c30c10211410430c30208c90230208c88230208c80230410410408c50c10410410430c6043047b86f274e8712e15892368,0x5d9139a612501092808a840454201941c3dc69c29e74e3cf39722781b926b4e779c058341a5dc2b0672631c71621c91612421de6da5c21c625f7195862441607585441482014880482013c804820130804000028a05328128a05028128a04d2810c30c104104b2c350b0cb2c344b0cb2c338b0c10410430c10430012973793a743897092367,0x8405046219a78651185a40068d3fc606f1375017d170a2986d4a0854a0b1786054a0b13762d365802100420005e00800170020005a0080220082000a40100028804000a00104400a80038000a80e020000a00804000098100184a228061184c13006224f3793a742e1246c0f7,0x12924c11ac6a50009ac6a5002802c3229f45a0b500105c759c091437147088141d5e02e08f1d662ce20609ba9c4aa06ea409cc691845340a0c0b42545859d68a5e22123b8b95e10a425c0b8dc40a9a64b69929a64b49920820a0802ea00a0802e20092492492082992092223a8da5a20c1a5b0d9d818c38fd8a07400d85757238e00a5969929a722732659279e8028212a13a0782a284bea12a284bca12a286a8693150a28692992992b26a124a00a04ae82809271c72aa9d0aa72aa9d02a72aa98a987474aaa987264a67309aa71280281cca0a9409249249271ca127129ee6f27520742e15892368]
def local11g0 : List Nat := [0x124ca010a8405c09280be8b4802fa2d2009972673c6112379d311702994e02ebb85d405f6d15a2e4a9092488c928888a24784928780a2077c80496c069604014a7006551400887406140801877805d318010410e10410410d10410410c10410410b1040c41030c34830c30c34430c30c34030c30c33c30c41041040c41041042c23793a742e15892367]
def local12g0 : List Nat := [0x2ec89cd268f3178d471e04f0e6610b8e32c8800ea02fa0b3c6940003301032200b1010b0204af0806e0106d2046c0946b2804a01049204480944728c4618929bc9d3a17092366]
end PEqualNP.Outside.L_meta_10393_aux

namespace PEqualNP.Outside.L_meta_10393_aux
abbrev SepMask := Nat × Nat
def agreement (bank : Nat) (m : SepMask) : Nat := bank ^^^ (bank &&& (m.1 ^^^ m.2))
def sepCode (pick : Nat → Nat) (m : Nat) : Nat := if m = 0 then 0 else 10000 + (pick (Nat.log2 m) % 10000)
def fastChoice (cuts : List Nat) (pick : Nat → Nat) (test : Nat → Bool) (i m : Nat) : Bool :=
  if i ≠ 0 then test i else if m = 0 then cuts.any test else test (sepCode pick m)
theorem fastChoice_sound {cuts pick test i m} (h : fastChoice cuts pick test i m = true) :
    ∃ j, (j = i ∨ j ∈ cuts ∨ j < 20000) ∧ test j = true := by
  by_cases hi : i = 0
  · by_cases hm : m = 0
    · have hc : cuts.any test = true := by simpa [fastChoice, hi, hm] using h
      obtain ⟨j,hj,hv⟩ := List.any_eq_true.mp hc
      exact ⟨j,Or.inr (Or.inl hj),hv⟩
    · have hs : sepCode pick m < 20000 := by unfold sepCode; split <;> omega
      exact ⟨_,Or.inr (Or.inr hs), by simpa [fastChoice,hi,hm] using h⟩
  · exact ⟨i,Or.inl rfl, by simpa [fastChoice, hi] using h⟩
def fastKid (cuts : List Nat) (pick : Nat → Nat) (u : Bool) (k : Nat) (ix : HintIndex)
    (xs : List Nat) (a b z word op all am bm : Nat) (kk : Bool × Bool) : Bool :=
  Nat.blt k (Nat.add (Nat.add xs.length (Nat.add (bl kk.1) (bl kk.2))) 0) ||
    (let i := packedDigit word (4 * op + packedSlot kk)
     let m := if kk.1 then all &&& am else all
     let m := if kk.2 then m &&& bm else m
     fastChoice cuts pick (indexedHint u k ix xs a b z kk.1 kk.2) i m)
def fastPair (cuts : List Nat) (masks : Nat → SepMask) (pick : Nat → Nat) (bank : Nat) (u : Bool) (k : Nat) (ix : HintIndex) (s : List Nat)
    (p : Nat × Nat × List Nat) (word : Nat) : Bool :=
  let a := masks p.1
  let b := masks p.2.1
  let common := p.2.2.foldl (fun v e => v &&& agreement bank (masks e)) bank
  (opsOf u).all fun op =>
    let z := nb op p.1 p.2.1
    mem1 z s || Nat.beq z 0 || Nat.beq z full ||
      (let zm := agreement bank (nb op a.1 b.1, nb op a.2 b.2)
       keeps.all (fastKid cuts pick u k ix p.2.2 p.1 p.2.1 z word op (common &&& zm) (agreement bank a) (agreement bank b)))
def fastBank (cuts : List Nat) (word : Nat) : List Nat :=
  (cuts.map projectedHint ++ (List.range 20000).map projectedHint) ++ (List.range 16).map (fun j => projectedHint (packedDigit word j))
theorem fastPair_sound {cuts masks pick bank u k n t s p word}
    (h : fastPair cuts masks pick bank u k (hintIndex n t) s p word = true) :
    pairOK u k n t s p (fastBank cuts word) = true := by
  apply List.all_eq_true.mpr
  intro op hop
  have hh := List.all_eq_true.mp h op hop
  dsimp only at hh ⊢
  simp only [Bool.or_eq_true] at hh ⊢
  rcases hh with h | h
  · exact Or.inl h
  right
  apply List.all_eq_true.mpr
  intro kk hkk
  have hk := List.all_eq_true.mp h kk hkk
  simp only [fastKid, Bool.or_eq_true] at hk
  simp only [kidOK, Bool.or_eq_true]
  rcases hk with hc|hk
  · exact Or.inl hc
  right
  apply List.any_eq_true.mpr
  obtain ⟨j, hj, hv⟩ := fastChoice_sound hk
  rcases hj with rfl | hj | hj
  · have ho : op < 4 := by cases u <;> simp [opsOf] at hop <;> omega
    have hs : packedSlot kk < 4 := by obtain ⟨a,b⟩ := kk; cases a <;> cases b <;> decide
    have hm : 4 * op + packedSlot kk ∈ List.range 16 := List.mem_range.mpr (by omega)
    exact ⟨_,List.mem_append_right _ (List.mem_map_of_mem hm), indexedHint_sound hv⟩
  · exact ⟨_,List.mem_append_left _ (List.mem_append_left _ (List.mem_map_of_mem hj)), indexedHint_sound hv⟩
  · exact ⟨_,List.mem_append_left _ (List.mem_append_right _ (List.mem_map_of_mem (List.mem_range.mpr hj))), indexedHint_sound hv⟩
def fastState (cuts : List Nat) (masks : Nat → SepMask) (pick : Nat → Nat) (bank : Nat) (u : Bool) (T k : Nat) (ix : HintIndex)
    (st : PackedState) : Bool :=
  asc st.1 && !(mem1 T st.1) && packedZip (fastPair cuts masks pick bank u k ix st.1) (pairs st.1) st.2
theorem fastState_sound {cuts masks pick bank u T k n t st}
    (h : fastState cuts masks pick bank u T k (hintIndex n t) st = true) :
    stOK u T t k n (st.1, st.2.map (fastBank cuts)) = true := by
  obtain ⟨hb,hc⟩ := Bool.and_eq_true_iff.mp h
  exact Bool.and_eq_true_iff.mpr ⟨hb,packedZip_sound (fun _ _ h => fastPair_sound h) hc⟩
theorem fastLevelAll {cuts masks pick bank u R T E t k prev states}
    (hb : baseOK T R E = true) (ht : TabsP u R T t) (hn : PackedLevel u T k prev)
    (hc : states.all (fastState cuts masks pick bank u T k (hintIndex (prev.map Prod.fst) t)) = true) :
    PackedLevel u T (k+1) states := by
  intro st hs
  apply stStep hb ht _ (fastState_sound (List.all_eq_true.mp hc st hs))
  intro s hs
  obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hs
  exact hn _ hq
theorem fastLevelBy {cuts : PackedState → List Nat} {masks pick bank u R T E t k prev states}
    (hb : baseOK T R E = true) (ht : TabsP u R T t) (hn : PackedLevel u T k prev)
    (hc : states.all (fun st => fastState (cuts st) masks pick bank u T k
      (hintIndex (prev.map Prod.fst) t) st) = true) : PackedLevel u T (k+1) states := by
  intro st hs
  apply stStep hb ht _ (fastState_sound (List.all_eq_true.mp hc st hs))
  intro s hs
  obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hs
  exact hn _ hq
def localOK (masks : Nat → SepMask) (pick : Nat → Nat) (bank : Nat) (u : Bool)
    (T k : Nat) (ix : HintIndex) (st : PackedState) : Bool :=
  fastState st.2 masks pick bank u T k ix (st.1, List.replicate (pairs st.1).length 0)
theorem localLevelAll {masks pick bank u R T E t k prev states}
    (hb : baseOK T R E = true) (ht : TabsP u R T t) (hn : PackedLevel u T k prev)
    (hc : states.all (localOK masks pick bank u T k (hintIndex (prev.map Prod.fst) t)) = true) :
    PackedLevel u T (k+1) states := by
  intro st hs
  have hh := fastState_sound (List.all_eq_true.mp hc st hs)
  apply stStep hb ht _ hh
  intro s hs
  obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hs
  exact hn _ hq
end PEqualNP.Outside.L_meta_10393_aux

namespace PEqualNP.Outside.L_meta_10393_aux
def sixBank : Nat := 0x111111e177e76e8011717fe111e7ee8010f17fe077e7ee8001101fe015e1ee80007011e077e5ee802030226033e3ee8011717f617761668
def sixSepIndex (j : Nat) : Nat := (0xb500000098000000200000009e0000001f00000019b00607000000004d005e710900af902c574c2a00007d5f17001536004b3461003500000000000000000000a3000000990094a7230000003d004fa0695441514355455d00000000a90000000d000000149f0b0a000068771a64164e00523f50005300000000000000000000c500000000aeadab33000000a800889324565c6340483b380000000000009d8110002b9a32473158000067661e6e1b260029283700460000000000000000000000000000a200000070000000000000008fc3b38a183c2e5a00000000000000008c00c400131d2d3e0000000022213a3000600001000800000000000000000000000000000000acb2bf0000000000000084000000877f114a000000000000b19574009b925b800f270000aa0085b41c2f007e04250002000000000000000000c200000000000000a1be00000000000091000000890000820e000000000000009c8e00006d598b830c0000009786968d12007b7a05000300000000000000000000ba000000bd00bcbb6f000000b700b9b86ab673723900444200000000a500c1c06b00a6a4750076490000000078007c6200006c650079000000 >>> (8 * j)) % 256
def sixMasks (v : Nat) : SepMask :=
  ((v &&& 0xffffffffffffffff) * 0x1000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001,
    (if v.testBit 0 then 0xffffffffffffffff else 0) |||
    (if v.testBit 1 then 0xffffffffffffffff0000000000000000 else 0) |||
    (if v.testBit 2 then 0xffffffffffffffff00000000000000000000000000000000 else 0) |||
    (if v.testBit 4 then 0xffffffffffffffff000000000000000000000000000000000000000000000000 else 0) |||
    (if v.testBit 8 then 0xffffffffffffffff0000000000000000000000000000000000000000000000000000000000000000 else 0) |||
    (if v.testBit 16 then 0xffffffffffffffff00000000000000000000000000000000000000000000000000000000000000000000000000000000 else 0) |||
    (if v.testBit 32 then 0xffffffffffffffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 else 0))
end PEqualNP.Outside.L_meta_10393_aux

namespace PEqualNP.Outside.L_meta_10393_aux
structure DelayIndex where
  cut : Nat → Option CutV
  sep : Nat → Option (Nat × Nat)
  kw : Nat → Option KwD
  perm : Nat → Option (List Nat)
  next : Nat → Option (List Nat)
def indexedDelay (u : Bool) (k : Nat) (ix : DelayIndex)
    (xs : List Nat) (a b z : Nat) (ka kb : Bool) (i : Nat) : Bool :=
  if i < 10000 then
    match ix.cut i with
    | some c => cutEval u k xs a b z ka kb c
    | none => false
  else if i < 20000 then
    match ix.sep (i - 10000) with
    | some q => sepEval u xs a b z ka kb q
    | none => false
  else if i < 30000 then
    match ix.kw (i - 20000) with
    | some q => !u && Nat.beq (kidN xs a b z ka kb).length (k+1) && kwList (kidN xs a b z ka kb) q
    | none => false
  else
    match ix.perm ((i - 30000) % 1024), ix.next ((i - 30000) / 1024) with
    | some perm, some st => beqL (sortN ((kidN xs a b z ka kb).map (permN perm))) st
    | _, _ => false
def rawLookup (v : List Nat) {α : Type} (f : Nat → α) : Nat → Option α :=
  let a := v.toArray
  fun j => a[j]?.map f
def delayOf (ix : HintIndex) : DelayIndex where
  cut := fun i => ix.cuts[i]?
  sep := fun i => ix.seps[i]?
  kw := fun i => ix.kws[i]?
  perm := fun i => ix.perms[i]?
  next := fun i => ix.next[i]?
def delayCert (codes : List Nat) : DelayIndex where
  cut := rawLookup certCutCodes (fun v => mkCut true certSlices (certCut v))
  sep := rawLookup certSepCodes (fun v => (v%128,v/128))
  kw := fun _ => none
  perm := rawLookup certPermCodes (certSwaps 15)
  next := rawLookup codes (fun v => (localState v).1)
set_option maxRecDepth 100000 in
theorem asDelay (u k d xs a b z ka kb i) :
    indexedDelay u k (delayOf d) xs a b z ka kb i = indexedHint u k d xs a b z ka kb i := by
  by_cases h₁ : i < 10000
  · cases hg : d.cuts[i]? <;> simp only [indexedDelay,indexedHint,delayOf,h₁,ite_true,hg]
  by_cases h₂ : i < 20000
  · cases hg : d.seps[i-10000]? <;> simp only [indexedDelay,indexedHint,delayOf,h₁,h₂,ite_true,ite_false,hg]
  by_cases h₃ : i < 30000
  · cases hg : d.kws[i-20000]? <;> simp only [indexedDelay,indexedHint,delayOf,h₁,h₂,h₃,ite_true,ite_false,hg]
  · cases hg : d.perms[(i-30000)%1024]? <;> cases ht : d.next[(i-30000)/1024]? <;>
      simp only [indexedDelay,indexedHint,delayOf,h₁,h₂,h₃,ite_false,hg,ht]
theorem dRawEq (f : Nat → α) (xs : List Nat) : rawLookup xs f = fun i => (xs.map f).toArray[i]? := by
  funext i
  simp [rawLookup,List.getElem?_map]
theorem dRawEq2 (f : Nat → α) (g : α → β) (xs : List Nat) :
    rawLookup xs (fun v => g (f v)) = fun i => ((xs.map f).map g).toArray[i]? := by
  funext i
  simp [rawLookup,List.getElem?_map,Function.comp_def]
set_option maxRecDepth 100000 in
theorem rawDecodedIdx (raw : List Nat) :
    delayCert raw = delayOf (hintIndex ((raw.map localState).map Prod.fst) certTabs) := by
  exact congrArg₂ (fun c p => DelayIndex.mk c (rawLookup certSepCodes (fun v => (v%128,v/128)))
      (fun _ => none) (rawLookup certPermCodes (certSwaps 15)) p)
    (dRawEq2 certCut (mkCut true certSlices) certCutCodes)
    (dRawEq2 localState Prod.fst raw) |>.trans (by
      simp only [delayOf,hintIndex,certTabs,certCuts,certSeps,certPerms,Tabs.cuts,Tabs.seps,Tabs.kws,Tabs.perms]
      rw [dRawEq (fun v => (v%128,v/128)) certSepCodes, dRawEq (certSwaps 15) certPermCodes]
      rfl)
theorem delayVerified (u k raw xs a b z ka kb i) :
    indexedDelay u k (delayCert raw) xs a b z ka kb i =
      indexedHint u k (hintIndex ((raw.map localState).map Prod.fst) certTabs) xs a b z ka kb i := by
  rw [rawDecodedIdx, asDelay]
def queryCode {α : Type} (n : Nat) (entry : Nat → Nat) (f : Nat → α) (i : Nat) : Option α :=
    if i<n then some (f (entry i)) else none
def lookupCut {α : Type} (f : Nat → α) : Nat → Option α := queryCode 1658 limbCut f
def lookupSep {α : Type} (f : Nat → α) : Nat → Option α := queryCode 198 limbSep f
def lookupPerm {α : Type} (f : Nat → α) : Nat → Option α := queryCode 720 limbPerm f
def limbRaw : Nat → Array (List Nat)
  | 4 => #[local4g0]
  | 5 => #[local5g0,local5g1,local5g2,local5g3,local5g4,local5g5,local5g6,local5g7,local5g8,local5g9,local5g10]
  | 6 => #[local6g0,local6g1,local6g2,local6g3,local6g4,local6g5,local6g6,local6g7,local6g8,local6g9,local6g10,local6g11,local6g12,local6g13,local6g14,local6g15,local6g16,local6g17,local6g18,local6g19,local6g20,local6g21,local6g22,local6g23,local6g24,local6g25,local6g26,local6g27,local6g28,local6g29,local6g30,local6g31,local6g32]
  | 7 => #[local7g0,local7g1,local7g2,local7g3,local7g4,local7g5,local7g6,local7g7,local7g8,local7g9,local7g10,local7g11,local7g12,local7g13,local7g14,local7g15,local7g16,local7g17,local7g18,local7g19,local7g20,local7g21,local7g22,local7g23]
  | 8 => #[local8g0,local8g1,local8g2,local8g3,local8g4,local8g5]
  | 9 => #[local9g0]
  | 10 => #[local10g0]
  | 11 => #[local11g0]
  | 12 => #[local12g0]
  | _ => #[]
def limbNext (lev i : Nat) := (limbRaw lev)[i/24]?.bind (fun xs => xs[i%24]?)
theorem queryModel {α : Type} (n : Nat) (g : Nat → Nat) (f : Nat → α) :
    queryCode n g f = rawLookup ((List.range n).map g) f := by
  funext i
  by_cases hi : i < n
  · simp [queryCode,rawLookup,List.getElem?_map,List.getElem?_eq_getElem,hi]
  · have eq : (List.range n)[i]? = none := List.getElem?_eq_none (by simpa using Nat.le_of_not_gt hi)
    simp [queryCode,rawLookup,List.getElem?_map,hi,eq]
def limbRawList (n lev : Nat) := (List.range n).map (fun i => (limbNext lev i).getD 0)
def limbIdxAt (n k : Nat) : DelayIndex where
  cut := lookupCut (fun v => mkCut true certSlices (certCut v))
  sep := lookupSep (fun v => (v%128,v/128))
  kw := fun _ => none
  perm := lookupPerm (certSwaps 15)
  next := queryCode n (fun i => (limbNext k i).getD 0) (fun v => (localState v).1)
theorem limbModel (n lev : Nat)
    (hc : certCutCodes = (List.range 1658).map limbCut)
    (hs : certSepCodes = (List.range 198).map limbSep)
    (hp : certPermCodes = (List.range 720).map limbPerm) :
    limbIdxAt n lev = delayCert (limbRawList n lev) := by
  unfold limbIdxAt delayCert limbRawList lookupCut lookupSep lookupPerm
  rw [hc,hs,hp]
  simp only [queryModel]
def limbCount : Nat → Nat
  | 4 => 6
  | 5 => 253
  | 6 => 780
  | 7 => 566
  | 8 => 132
  | 9 => 22
  | 10 => 5
  | 11 => 1
  | 12 => 1
  | _ => 0
def limbRows (k : Nat) : List PackedState := (limbRawList (limbCount k) k).map localState
end PEqualNP.Outside.L_meta_10393_aux

namespace PEqualNP.Outside.L_meta_10393_aux
def fForce {α : Type} (w : Nat) (k : Nat → α) : α :=
 @Nat.rec (fun _ => α) (k 0) (fun n _=>k (Nat.succ n)) w
theorem fForce_eq {α : Type} (w : Nat) (k : Nat → α) : fForce w k=k w:=by
  cases w <;> rfl
def fForceWords {α : Type} (ws : List Nat) (k : List Nat → α) : α :=
 (List.rec (motive:=fun _=>(List Nat → α) → α) (fun f=>f [])
 (fun w _ next f=>fForce w (fun v=>next (fun rest=>f (v :: rest)))) ws) k
theorem fForceWords_eq {α : Type} (ws : List Nat) (k : List Nat → α) :
    fForceWords ws k=k ws:=by
  induction ws generalizing k with
  | nil=>rfl
  | cons w ws ih =>
    change fForce w (fun v=>fForceWords ws (fun rest=>k (v :: rest)))=_
    rw [fForce_eq,ih]
end PEqualNP.Outside.L_meta_10393_aux

namespace PEqualNP.Outside.L_meta_10393_aux
def tapeAll {α : Type} (fs : α → Nat → Option Nat) : List α → Nat → Option Nat
  | [], t => some t
  | a::as, t => (fs a t).bind (tapeAll fs as)
def tapePair (cuts : Array Nat) (width : Nat) (k : Nat) (ix : DelayIndex)
    (s : List Nat) (p : Nat × Nat × List Nat) : Nat → Option Nat :=
  let a := sixMasks p.1
  let b := sixMasks p.2.1
  let common := p.2.2.foldl (fun v w => v &&& agreement sixBank (sixMasks w)) sixBank
  tapeAll (fun op t =>
    let z := nb op p.1 p.2.1
    if mem1 z s || Nat.beq z 0 || Nat.beq z full then some t else
    let both := common &&& agreement sixBank (nb op a.1 b.1,nb op a.2 b.2)
    tapeAll (fun kk v =>
      if Nat.blt k (Nat.add p.2.2.length (Nat.add (bl kk.1) (bl kk.2))) then some v else
      let m := if kk.1 then both &&& agreement sixBank a else both
      let m := if kk.2 then m &&& agreement sixBank b else m
      if m != 0 then some v else
      (cuts[v % (2 ^ width)]?).bind (fun code =>
        if indexedDelay true k ix p.2.2 p.1 p.2.1 z kk.1 kk.2 code then some (v >>> width) else none)
    ) keeps t
  ) (opsOf true)
def tapeState (T k : Nat) (ix : DelayIndex) (st : PackedState) (t : Nat) : Bool :=
  fForceWords st.1 fun ws => fForceWords st.2 fun cs =>
    let width := max 1 (Nat.log2 (2*cs.length-2))
    asc ws && !(mem1 T ws) && (tapeAll (tapePair cs.toArray width k ix ws) (pairs ws) t).isSome
end PEqualNP.Outside.L_meta_10393_aux

namespace PEqualNP.Outside.L_meta_10393_aux
structure SignedRooms (S : Finset Sig) (T : Sig) where
  orientation : Sig → Bool
  owns : Sig → Row → Row → Prop
  total : ∀ p n, bit p T = true → bit n T = false → ∃ v, owns v p n
  valid : ∀ {v p n}, owns v p n → v ∈ S ∧ bit p v = orientation v ∧ bit n v = !(orientation v)
  unique : ∀ {v w p n}, owns v p n → owns w p n → v = w
  rect : ∀ {v p n p' n'}, owns v p n → owns v p' n' → owns v p n'
theorem signedRoomLeaf (T : Sig) : Nonempty (SignedRooms {T} T) := by
  refine ⟨⟨fun _ => true,fun v p n => v = T ∧ bit p T = true ∧ bit n T = false,?_,?_,?_,?_⟩⟩
  · intro p n hp hn
    exact ⟨T,rfl,hp,hn⟩
  · rintro v p n ⟨rfl,hp,hn⟩
    exact ⟨by simp,hp,hn⟩
  · rintro v w p n ⟨rfl,_⟩ ⟨rfl,_⟩
    rfl
  · rintro v p n p' n' ⟨rfl,hp,_⟩ ⟨_,_,hn⟩
    exact ⟨rfl,hp,hn⟩
def signedAt (d : Fin 4) (a b : Bool) : Bool :=
  if d.val=0 then a && b else if d.val=1 then a || b else if d.val=2 then a && !b else !a && b
def roomPick (d : Fin 4) (o pa na : Bool) : Bool :=
  (if o = decide (d.val = 1) then pa else na) == (decide (d.val = 1) ^^ decide (d.val = 3))
theorem roomPick_valid : ∀ (d : Fin 4) (o pa na pb nb : Bool),
    signedAt d pa pb = o → signedAt d na nb = !o →
      if roomPick d o pa na then pa = (o ^^ decide (d.val=3)) ∧ na = !(o ^^ decide (d.val=3))
      else pb = (o ^^ decide (d.val=2)) ∧ nb = !(o ^^ decide (d.val=2)) := by
  decide +kernel
theorem bitSignedAt (r : Row) (d : Fin 4) (a b : Sig) :
    bit r (bin d.val a b) = signedAt d (bit r a) (bit r b) := by
  unfold bin signedAt
  split_ifs <;> simp [bit]
theorem signedFork {T : Sig} {U : Finset Sig} {a b : Sig} (d : Fin 4)
    (hab : a ≠ b) (ha : a ∉ U) (hb : b ∉ U) (hz : bin d.val a b ∉ U)
    (H : SignedRooms (insert (bin d.val a b) U) T) : Nonempty (SignedRooms (insert a (insert b U)) T) := by
  classical
  let z := bin d.val a b
  let o := H.orientation z
  let win := fun (p n : Row) => if roomPick d o (bit p a) (bit n a) then a else b
  let dir := fun v : Sig => if v=a then o ^^ decide (d.val=3) else if v=b then o ^^ decide (d.val=2) else H.orientation v
  let own := fun (v : Sig) (p n : Row) => (v ∈ U ∧ H.owns v p n) ∨ (H.owns z p n ∧ v = win p n)
  have winU (p n : Row) : win p n ∉ U := by
    dsimp [win]
    split <;> assumption
  refine ⟨⟨dir,own,?_,?_,?_,?_⟩⟩
  · intro p n hp hn
    obtain ⟨v,hv⟩ := H.total p n hp hn
    rcases Finset.mem_insert.mp (H.valid hv).1 with e | hm
    · change v = z at e
      subst v
      exact ⟨win p n,Or.inr ⟨hv,rfl⟩⟩
    · exact ⟨v,Or.inl ⟨hm,hv⟩⟩
  · intro v p n hv
    rcases hv with ⟨hm,hv⟩ | ⟨hv,rfl⟩
    · have hav : v ≠ a := fun h => ha (h ▸ hm)
      have hbv : v ≠ b := fun h => hb (h ▸ hm)
      exact ⟨Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hm),by simpa [dir,hav,hbv] using (H.valid hv).2⟩
    · obtain ⟨_,hp,hn⟩ := H.valid hv
      change bit p (bin d.val a b) = o at hp
      change bit n (bin d.val a b) = !o at hn
      rw [bitSignedAt] at hp hn
      have pick := roomPick_valid d o _ _ _ _ hp hn
      cases e : roomPick d o (bit p a) (bit n a)
      · simpa [win,e,dir,Ne.symm hab] using pick
      · simpa [win,e,dir] using pick
  · intro v w p n h1 h2
    rcases h1 with ⟨vU,hv⟩ | ⟨hv,rfl⟩ <;> rcases h2 with ⟨wU,hw⟩ | ⟨hw,rfl⟩
    · exact H.unique hv hw
    · exact absurd (show z ∈ U by rw [←H.unique hv hw]; exact vU) hz
    · exact absurd (show z ∈ U by rw [←H.unique hw hv]; exact wU) hz
    · rfl
  · intro v p n p' n' h1 h2
    rcases h1 with ⟨vU,hv⟩ | ⟨hv,e1⟩ <;> rcases h2 with ⟨wU,hw⟩ | ⟨hw,e2⟩
    · exact Or.inl ⟨vU,H.rect hv hw⟩
    · exact absurd (e2 ▸ vU) (winU p' n')
    · exact absurd (e1 ▸ wU) (winU p n)
    · refine Or.inr ⟨H.rect hv hw,?_⟩
      by_cases h : o = decide (d.val=1)
      · simpa only [win,roomPick,if_pos h] using e1
      · simpa only [win,roomPick,if_neg h] using e2
theorem signedLiveSize {u target k S} (h : Live u target k S) : S.card ≤ k+1 := by
  induction h using Live.ind with
  | stop hp => simp
  | @binary k U a b d hd ha hb hab hf _ ih =>
    have hu : bin d a b ∉ U := fun hm => hf (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hm))
    rw [Finset.card_insert_of_notMem hu] at ih
    have h1 := Finset.card_insert_le (a := a) (s := insert b U)
    have h2 := Finset.card_insert_le (a := b) (s := U)
    omega
theorem signedTight {T : Sig} {k : Nat} {S : Finset Sig} (run : Live true T k S) (tight : S.card=k+1) :
    Nonempty (SignedRooms S T) := by
  induction k generalizing S with
  | zero =>
    obtain ⟨rfl,_⟩ := run
    exact signedRoomLeaf T
  | succ k ih =>
    obtain ⟨U,a,b,d,hd,rfl,_,_,hab,hfresh,tail⟩ := run
    have fresh : bin d a b ∉ U := fun h => hfresh (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem h))
    have li := signedLiveSize tail
    rw [Finset.card_insert_of_notMem fresh] at li
    have le1 := Finset.card_insert_le a (insert b U)
    have le2 := Finset.card_insert_le b U
    have ha : a ∉ U := by
      intro h
      rw [Finset.insert_eq_of_mem (Finset.mem_insert_of_mem h : a ∈ insert b U)] at tight
      omega
    have hb : b ∉ U := by
      intro h
      rw [Finset.insert_eq_of_mem h] at tight le1
      omega
    have eq : (insert (bin d a b) U).card=k+1 := by
      rw [Finset.card_insert_of_notMem fresh]
      omega
    obtain ⟨H⟩ := ih tail eq
    have dlt : d < 4 := by rcases hd with h|⟨_,h⟩ <;> omega
    exact signedFork ⟨d,dlt⟩ hab ha hb fresh H
end PEqualNP.Outside.L_meta_10393_aux

namespace PEqualNP.Outside.L_meta_10393_aux
def swRow (q j : Nat) : Row := ⟨(q >>> (1 + 7*j)) % 128, Nat.mod_lt _ (by decide)⟩
def swCell (T : Nat) (p n : Row) : Bool := T.testBit p.val && !(T.testBit n.val)
def swFind (l : List Nat) (p n : Row) : Nat :=
  (l.find? fun x => x.testBit p.val != x.testBit n.val).getD 0
def swOnly (l : List Nat) (p n : Row) (a : Nat) : Bool :=
  l.all fun x => (x.testBit p.val == x.testBit n.val) || Nat.beq x a
def swCross (T : Nat) (l : List Nat) (p n pa na pb nb : Row) : Bool :=
  let a := swFind l p na
  let b := swFind l p nb
  swCell T p na && swCell T pa n && swCell T p nb && swCell T pb n &&
    swOnly l p na a && swOnly l pa n a && swOnly l p nb b && swOnly l pb n b && !(Nat.beq a b)
def swReverse (T : Nat) (l : List Nat) (p n p' n' : Row) : Bool :=
  let a := swFind l p n
  swCell T p n && swCell T p' n' && swOnly l p n a && swOnly l p' n' a &&
    (a.testBit p.val != a.testBit p'.val)
def signedWitness (T : Nat) (l : List Nat) (q : Nat) : Bool :=
  if q % 2 = 0 then swCross T l (swRow q 0) (swRow q 1) (swRow q 2) (swRow q 3) (swRow q 4) (swRow q 5)
  else swReverse T l (swRow q 0) (swRow q 1) (swRow q 2) (swRow q 3)
theorem swOnlyOwn {T a : Nat} {l : List Nat} {p n : Row}
    (H : SignedRooms (l.map W).toFinset (W T)) (cell : swCell T p n = true) (forced : swOnly l p n a = true) :
    H.owns (W a) p n := by
  obtain ⟨hp,hn⟩ := Bool.and_eq_true_iff.mp cell
  obtain ⟨v,hv⟩ := H.total p n (by rw [bit_W]; exact hp) (by rw [bit_W]; simpa only [Bool.not_eq_true'] using hn)
  obtain ⟨sv,hp',hn'⟩ := H.valid hv
  obtain ⟨x,hx,rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp sv)
  have diff : x.testBit p.val ≠ x.testBit n.val := by
    rw [bit_W] at hp' hn'
    rw [hp',hn']
    cases H.orientation (W x) <;> decide
  have sel := List.all_eq_true.mp forced x hx
  simp only [Bool.or_eq_true,beq_iff_eq] at sel
  rcases sel with h|h
  · exact False.elim (diff h)
  · rw [Nat.eq_of_beq_eq_true h] at hv
    exact hv
theorem swFindBound {l : List Nat} (lt : ∀ x ∈ l, x < 2^128) (p n : Row) : swFind l p n < 2^128 := by
  unfold swFind
  cases h : l.find? (fun x => x.testBit p.val != x.testBit n.val) with
  | none => exact Nat.two_pow_pos _
  | some x => exact lt x (List.mem_of_find?_eq_some h)
theorem swCrossElim {T : Nat} {l : List Nat} {p n pa na pb nb : Row}
    (lt : ∀ x ∈ l, x < 2^128) (H : SignedRooms (l.map W).toFinset (W T)) (h : swCross T l p n pa na pb nb = true) : False := by
  simp only [swCross,Bool.and_eq_true,Bool.not_eq_true'] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨c1,c2⟩,c3⟩,c4⟩,a1⟩,a2⟩,b1⟩,b2⟩,ne⟩ := h
  have wa := H.rect (swOnlyOwn H c1 a1) (swOnlyOwn H c2 a2)
  have wb := H.rect (swOnlyOwn H c3 b1) (swOnlyOwn H c4 b2)
  have eq := W_inj (swFindBound lt _ _) (swFindBound lt _ _) (H.unique wa wb)
  rw [eq,Nat.beq_refl] at ne
  contradiction
theorem swReverseElim {T : Nat} {l : List Nat} {p n p' n' : Row}
    (H : SignedRooms (l.map W).toFinset (W T)) (h : swReverse T l p n p' n' = true) : False := by
  simp only [swReverse,Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨c1,c2⟩,o1⟩,o2⟩,conflict⟩ := h
  have h1 := (H.valid (swOnlyOwn H c1 o1)).2.1
  have h2 := (H.valid (swOnlyOwn H c2 o2)).2.1
  rw [bit_W] at h1 h2
  have eq := h1.trans h2.symm
  simp [eq] at conflict
theorem signedWitness_sound {T k : Nat} {l : List Nat} (nd : (l.map W).Nodup) (size : l.length=k+1)
    (lt : ∀ x ∈ l, x < 2^128) (q : Nat) (h : signedWitness T l q = true) : Impossible true (W T) k (l.map W).toFinset := by
  intro k' hk run
  have lb := signedLiveSize run
  rw [List.toFinset_card_of_nodup nd,List.length_map] at lb
  obtain ⟨H⟩ := signedTight run (by rw [List.toFinset_card_of_nodup nd,List.length_map]; omega)
  unfold signedWitness at h
  split at h
  · exact swCrossElim lt H h
  · exact swReverseElim H h
def signedLeaf (T k : Nat) (l : List Nat) (q : Nat) : Bool :=
  Nat.beq l.length (k+1) && decide (l.map W).Nodup && l.all (fun x => Nat.blt x (2^128)) && signedWitness T l q
theorem signedLeaf_sound {T k l q} (h : signedLeaf T k l q = true) : Impossible true (W T) k (l.map W).toFinset := by
  simp only [signedLeaf,Bool.and_eq_true,Nat.beq_eq,decide_eq_true_eq,List.all_eq_true,Nat.blt_eq] at h
  exact signedWitness_sound h.1.1.2 h.1.1.1 h.1.2 q h.2
end PEqualNP.Outside.L_meta_10393_aux

namespace PEqualNP.Outside.L_meta_10393_aux
def shortCheck (k : Nat) (st : PackedState) : Bool :=
  match st.2 with
  | [] => false
  | h :: bank =>
    if h % 2 = 1 then signedLeaf stopT (k+1) st.1 (h/2)
    else tapeState stopT k (limbIdxAt (limbCount k) k) (st.1, bank) (h/2)
def shortChunk (k i : Nat) : Bool :=
  (((limbRows k).drop (i*64)).take 64).all (shortCheck (k-1))
end PEqualNP.Outside.L_meta_10393_aux

namespace PEqualNP.Outside.L_meta_10393_aux
def SepModel (masks : Nat → SepMask) (pick : Nat → Nat) (bank : Nat) (t : Tabs) : Prop :=
  ∀ j, bank.testBit j = true → ∃ q, t.seps[pick j]? = some q ∧ pick j < 10000 ∧
    ∀ v, (masks v).1.testBit j = v.testBit q.1 ∧ (masks v).2.testBit j = v.testBit q.2
private theorem agree_bits {bank j : Nat} {pair : SepMask} (h : (agreement bank pair).testBit j = true) :
    bank.testBit j = true ∧ pair.1.testBit j = pair.2.testBit j := by
  simp only [agreement,Nat.testBit_xor,Nat.testBit_and] at h
  cases hb : bank.testBit j <;> cases hp : pair.1.testBit j <;> cases hn : pair.2.testBit j <;>
    simp_all
private theorem nb_reads {op a b c d i j : Nat} (h : a.testBit i = c.testBit j)
    (g : b.testBit i = d.testBit j) : (nb op a b).testBit i = (nb op c d).testBit j := by
  unfold nb
  cases Nat.beq op 0 <;> cases Nat.beq op 1 <;> cases Nat.beq op 2 <;>
    simp [Nat.testBit_and,Nat.testBit_or,Nat.testBit_xor,h,g]
private theorem fold_agree {f : Nat → Nat} (xs : List Nat) (acc j : Nat)
    (h : (xs.foldl (fun v x => v &&& f x) acc).testBit j = true) :
    acc.testBit j = true ∧ ∀ v ∈ xs, (f v).testBit j = true := by
  induction xs generalizing acc with
  | nil => exact ⟨h, by simp⟩
  | cons x xs ih =>
    obtain ⟨hg,hr⟩ := ih _ h
    obtain ⟨ha,hx⟩ := Bool.and_eq_true_iff.mp ((Nat.testBit_and ..).symm ▸ hg)
    refine ⟨ha,?_⟩
    intro v hv
    rcases List.mem_cons.mp hv with rfl | hv
    · exact hx
    · exact hr _ hv
def survivors (masks : Nat → SepMask) (bank : Nat) (rest : List Nat) (a b op : Nat)
    (ka kb : Bool) : Nat :=
  let pa := masks a
  let pb := masks b
  let shared := rest.foldl (fun v w => v &&& agreement bank (masks w)) bank
  let both := shared &&& agreement bank (nb op pa.1 pb.1, nb op pa.2 pb.2)
  let withA := if ka then both &&& agreement bank pa else both
  if kb then withA &&& agreement bank pb else withA
set_option maxRecDepth 100000 in
theorem surviving_sep {masks pick bank t k n rest a b op ka kb}
    (model : SepModel masks pick bank t)
    (h : survivors masks bank rest a b op ka kb ≠ 0) :
    indexedHint true k (hintIndex n t) rest a b (nb op a b) ka kb
      (sepCode pick (survivors masks bank rest a b op ka kb)) = true := by
  let key := survivors masks bank rest a b op ka kb
  let j := key.log2
  have hit : key.testBit j = true := Nat.testBit_log2 h
  let shared := rest.foldl (fun v w => v &&& agreement bank (masks w)) bank
  let za := nb op (masks a).1 (masks b).1
  let zb := nb op (masks a).2 (masks b).2
  have bits : shared.testBit j = true ∧
      (agreement bank (za,zb)).testBit j = true ∧
      (ka = true → (agreement bank (masks a)).testBit j = true) ∧
      (kb = true → (agreement bank (masks b)).testBit j = true) := by
    cases ka <;> cases kb <;>
      simp only [key, survivors, Bool.false_eq_true, eq_self, ite_false, ite_true,
        Nat.testBit_and,Bool.and_eq_true] at hit <;>
      dsimp only [shared,za,zb] <;> tauto
  obtain ⟨bankBit,hr⟩ := fold_agree rest bank j bits.1
  obtain ⟨q,hq,small,reads⟩ := model j bankBit
  have same_raw (v : Nat) (hv : (agreement bank (masks v)).testBit j = true) :
      same true q v = true := by
    have e := (agree_bits hv).2
    rw [(reads v).1, (reads v).2] at e
    simpa [same] using e
  have e := (agree_bits bits.2.1).2
  have ea := nb_reads (op:=op) (reads a).1 (reads b).1
  have eb := nb_reads (op:=op) (reads a).2 (reads b).2
  have gz : same true q (nb op a b) = true := by
    simpa [same] using ea.symm.trans (e.trans eb)
  have hs : sepEval true rest a b (nb op a b) ka kb q = true := by
    have ha := bits.2.2.1
    have hb := bits.2.2.2
    have rr : rest.all (same true q) = true := List.all_eq_true.mpr (fun v hv => same_raw v (hr _ hv))
    cases ka <;> cases kb <;> simp_all [sepEval,same_raw]
  have e1 : ¬ 10000 + pick j < 10000 := by omega
  have e2 : 10000 + pick j < 20000 := by omega
  change indexedHint true k (hintIndex n t) rest a b (nb op a b) ka kb (sepCode pick key) = true
  have eq : sepCode pick key = 10000 + pick j := by
    simp [sepCode,show key ≠ 0 from h, Nat.mod_eq_of_lt small, j]
  simpa [eq,indexedHint,hintIndex,e1,e2,hq] using hs
end PEqualNP.Outside.L_meta_10393_aux

namespace PEqualNP.Outside.L_meta_10393_aux
def repWide : Nat → Nat
  | 0 => 0
  | k+1 => 2^64 * repWide k + 1
theorem rep_bit (v : Nat) (hv : v < 2^64) (k j : Nat) (hj : j < 64*k) :
    (v * repWide k).testBit j = v.testBit (j%64) := by
  induction k generalizing j with
  | zero => omega
  | succ k ih =>
    have e : v * repWide (k+1) = 2^64 * (v*repWide k) + v := by change v * (2^64 * repWide k + 1) = _; ring
    rw [e,Nat.testBit_two_pow_mul_add _ hv]
    split
    next h => exact congrArg (fun r => v.testBit r) (Nat.mod_eq_of_lt h).symm
    next h =>
      have hh : j-64 < 64*k := by omega
      rw [ih _ hh,show (j-64)%64 = j%64 by omega]
def negRow : Nat → Nat
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 4
  | 4 => 8
  | 5 => 16
  | _ => 32
def negFlags (f : Fin 7 → Bool) : Nat :=
  (if f 0 then 0xffffffffffffffff else 0) |||
  (if f 1 then 0xffffffffffffffff0000000000000000 else 0) |||
  (if f 2 then 0xffffffffffffffff00000000000000000000000000000000 else 0) |||
  (if f 3 then 0xffffffffffffffff000000000000000000000000000000000000000000000000 else 0) |||
  (if f 4 then 0xffffffffffffffff0000000000000000000000000000000000000000000000000000000000000000 else 0) |||
  (if f 5 then 0xffffffffffffffff00000000000000000000000000000000000000000000000000000000000000000000000000000000 else 0) |||
  (if f 6 then 0xffffffffffffffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 else 0)
set_option maxRecDepth 48000 in
set_option maxHeartbeats 0 in
theorem negFlag_bits : ∀ (f : Fin 7 → Bool) (j : Fin 448),
    (negFlags f).testBit j.val = f ⟨j.val / 64, by omega⟩ := by decide +kernel
set_option maxRecDepth 48000 in
set_option maxHeartbeats 0 in
theorem index_reads : ∀ j : Fin 448, sixBank.testBit j.val = true →
    certSeps[sixSepIndex j.val]? = some (j.val % 64,negRow (j.val / 64)) ∧ sixSepIndex j.val < 10000 := by decide +kernel
theorem sixModel : SepModel sixMasks sixSepIndex sixBank certTabs := by
  intro j h
  have jb : j < 448 := by
    by_contra! hb
    have hB : sixBank < 2^448 := by decide +kernel
    have := Nat.testBit_lt_two_pow (hB.trans_le (Nat.pow_le_pow_right Nat.zero_lt_two hb))
    simp_all
  let r : Fin 448 := ⟨j,jb⟩
  have ri := index_reads r h
  refine ⟨_,ri.1,ri.2,?_⟩
  intro v
  constructor
  · change ((v &&& (2^64-1)) * repWide 7).testBit j = v.testBit (j%64)
    rw [Nat.and_two_pow_sub_one_eq_mod,rep_bit _ (Nat.mod_lt _ (by decide : 0 < 2^64)) 7 _ (by omega),
      Nat.testBit_mod_two_pow]
    simp [Nat.mod_lt j (by decide : 0 < 64)]
  · let f : Fin 7 → Bool := fun i => v.testBit (negRow i.val)
    change (negFlags f).testBit j = v.testBit (negRow (j / 64))
    exact negFlag_bits f r
end PEqualNP.Outside.L_meta_10393_aux

namespace PEqualNP.Outside.L_meta_10393_aux
def acceptPair (cuts : List Nat) (masks : Nat → SepMask) (bank k : Nat) (ix : HintIndex)
    (s : List Nat) (p : Nat × Nat × List Nat) : Bool :=
  let a := masks p.1
  let b := masks p.2.1
  let common := p.2.2.foldl (fun v w => v &&& agreement bank (masks w)) bank
  (opsOf true).all fun op =>
    let z := nb op p.1 p.2.1
    mem1 z s || Nat.beq z 0 || Nat.beq z full ||
      (let zm := agreement bank (nb op a.1 b.1,nb op a.2 b.2)
       let both := common &&& zm
       keeps.all fun kk =>
         Nat.blt k (Nat.add (Nat.add p.2.2.length (Nat.add (bl kk.1) (bl kk.2))) 0) ||
         (let am := if kk.1 then both &&& agreement bank a else both
          let m := if kk.2 then am &&& agreement bank b else am
          m != 0 || cuts.any (indexedHint true k ix p.2.2 p.1 p.2.1 z kk.1 kk.2)))
theorem acceptPair_sound {cuts masks pick bank t k n s p} (model : SepModel masks pick bank t)
    (h : acceptPair cuts masks bank k (hintIndex n t) s p = true) :
    fastPair cuts masks pick bank true k (hintIndex n t) s p 0 = true := by
  apply List.all_eq_true.mpr
  intro op hop
  have hh := List.all_eq_true.mp h op hop
  dsimp only at hh ⊢
  simp only [Bool.or_eq_true] at hh ⊢
  rcases hh with base | hkids
  · exact Or.inl base
  right
  apply List.all_eq_true.mpr
  intro kk hkk
  have hk := List.all_eq_true.mp hkids kk hkk
  simp only [Bool.or_eq_true] at hk
  unfold fastKid
  rw [Bool.or_eq_true]
  rcases hk with cap | marked
  · exact Or.inl cap
  right
  let m := survivors masks bank p.2.2 p.1 p.2.1 op kk.1 kk.2
  let test := indexedHint true k (hintIndex n t) p.2.2 p.1 p.2.1 (nb op p.1 p.2.1) kk.1 kk.2
  change fastChoice cuts pick test (packedDigit 0 _) m = true
  change (m != 0) = true ∨ cuts.any test = true at marked
  have zero (j : Nat) : packedDigit 0 j = 0 := by simp [packedDigit, Nat.shiftRight_eq_div_pow]
  rw [zero]
  by_cases hm : m = 0
  · simpa [fastChoice,hm] using marked
  · have hh : test (sepCode pick m) = true := surviving_sep model hm
    simpa [fastChoice,hm] using hh
theorem zip_zeroes {f : Nat × Nat × List Nat → Nat → Bool} (ps : List (Nat × Nat × List Nat))
    (h : ∀ p ∈ ps, f p 0 = true) : packedZip f ps (List.replicate ps.length 0) = true := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    simp only [List.length_cons,List.replicate_succ,packedZip,Bool.and_eq_true]
    exact ⟨h p List.mem_cons_self,ih (fun x hx => h x (List.mem_cons_of_mem _ hx))⟩
def acceptState (masks : Nat → SepMask) (bank T k : Nat) (ix : HintIndex) (st : PackedState) : Bool :=
  asc st.1 && !(mem1 T st.1) && (pairs st.1).all (acceptPair st.2 masks bank k ix st.1)
theorem acceptState_sound {masks pick bank t k n T st} (mod : SepModel masks pick bank t)
    (h : acceptState masks bank T k (hintIndex n t) st = true) :
    localOK masks pick bank true T k (hintIndex n t) st = true := by
  obtain ⟨a,b⟩ := Bool.and_eq_true_iff.mp h
  exact Bool.and_eq_true_iff.mpr ⟨a,zip_zeroes _ (fun p hp => acceptPair_sound mod (List.all_eq_true.mp b p hp))⟩
theorem acceptLevelAll {masks pick bank R T E t k prev states} (model : SepModel masks pick bank t)
    (hb : baseOK T R E = true) (ht : TabsP true R T t) (hn : PackedLevel true T k prev)
    (hc : states.all (acceptState masks bank T k (hintIndex (prev.map Prod.fst) t)) = true) :
    PackedLevel true T (k+1) states := by
  apply localLevelAll (pick:=pick) (masks:=masks) (bank:=bank) hb ht hn
  exact List.all_eq_true.mpr (fun st h => acceptState_sound model (List.all_eq_true.mp hc st h))
end PEqualNP.Outside.L_meta_10393_aux

namespace PEqualNP.Outside.L_meta_10393_aux
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem tapeAll_all {α} {fs : α → Nat → Option Nat} {xs : List α} {t e : Nat}
    (h : tapeAll fs xs t = some e) : ∀ a ∈ xs, ∃ v u, fs a v = some u := by
  induction xs generalizing t with
  | nil => simp
  | cons a xs ih =>
    cases ha : fs a t with
    | none => simp [tapeAll,ha] at h
    | some r =>
      have hx : tapeAll fs xs r = some e := by simpa only [tapeAll,ha,Option.bind_some] using h
      intro a' ha'
      rcases List.mem_cons.mp ha' with rfl|hm
      · exact ⟨t,r,ha⟩
      · exact ih hx a' hm
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem tapePair_sound (cs : List Nat) (w k : Nat) (d : DelayIndex) (j : HintIndex)
    (eqD : ∀ xs a b z ka kb i, indexedDelay true k d xs a b z ka kb i = indexedHint true k j xs a b z ka kb i)
    (s : List Nat) (p : Nat × Nat × List Nat) (t e : Nat)
    (h : tapePair cs.toArray w k d s p t = some e) :
    acceptPair cs sixMasks sixBank k j s p = true := by
  unfold tapePair at h
  unfold acceptPair
  apply List.all_eq_true.mpr
  intro op hop
  obtain ⟨t',e',ho⟩ := tapeAll_all h op hop
  dsimp only at ho ⊢
  rw [Bool.or_eq_true]
  split at ho
  next hb => exact Or.inl hb
  next _ =>
    right
    apply List.all_eq_true.mpr
    intro kk hk
    obtain ⟨u,v,hc⟩ := tapeAll_all ho kk hk
    rw [Bool.or_eq_true]
    split at hc
    next cap => exact Or.inl cap
    next _ =>
      right
      rw [Bool.or_eq_true]
      let m := survivors sixMasks sixBank p.2.2 p.1 p.2.1 op kk.1 kk.2
      let z := nb op p.1 p.2.1
      let chk := indexedDelay true k d p.2.2 p.1 p.2.1 z kk.1 kk.2
      change (if m != 0 then some u else (cs.toArray[u % 2^w]?).bind
          (fun code => if chk code then some (u >>> w) else none)) = some v at hc
      change (m != 0) = true ∨ cs.any (indexedHint true k j p.2.2 p.1 p.2.1 z kk.1 kk.2) = true
      by_cases sep : (m != 0) = true
      · exact Or.inl sep
      right
      rw [if_neg sep] at hc
      cases hr : cs.toArray[u % 2^w]? with
      | none => simp only [hr,Option.bind_none,reduceCtorEq] at hc
      | some code =>
        simp only [hr,Option.bind_some] at hc
        by_cases hit : chk code = true
        · apply List.any_eq_true.mpr
          refine ⟨code,?_,?_⟩
          · apply List.mem_of_getElem? (i:=u % 2^w)
            simpa using hr
          · exact (eqD _ _ _ _ _ _ _).symm.trans hit
        · simp only [if_neg hit,reduceCtorEq] at hc
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem tapeState_sound {T k d pick n tabs st t}
    (model : SepModel sixMasks pick sixBank tabs)
    (eqD : ∀ xs a b z ka kb i, indexedDelay true k d xs a b z ka kb i =
        indexedHint true k (hintIndex n tabs) xs a b z ka kb i)
    (h : tapeState T k d st t = true) :
    localOK sixMasks pick sixBank true T k (hintIndex n tabs) st = true := by
  apply acceptState_sound model
  unfold tapeState at h
  rw [fForceWords_eq,fForceWords_eq] at h
  obtain ⟨head,tail⟩ := Bool.and_eq_true_iff.mp h
  apply Bool.and_eq_true_iff.mpr
  refine ⟨head,List.all_eq_true.mpr ?_⟩
  obtain ⟨e,hv⟩ := Option.isSome_iff_exists.mp tail
  intro p hp
  obtain ⟨v,u,hp'⟩ := tapeAll_all hv p hp
  exact tapePair_sound _ _ _ _ _ eqD _ _ _ _ hp'
end PEqualNP.Outside.L_meta_10393_aux

namespace PEqualNP.Outside.L_meta_10393_aux
theorem shortBefore : PackedLevel true stopT 3 (limbRows 3) := by intro s hs; cases hs
theorem shortIndex_agrees (k xs a b z ka kb i) :
    indexedDelay true k (limbIdxAt (limbCount k) k) xs a b z ka kb i =
      indexedHint true k (hintIndex ((limbRows k).map Prod.fst) certTabs) xs a b z ka kb i := by
  unfold limbRows
  rw [limbModel _ _ rfl rfl rfl]
  exact delayVerified true k _ xs a b z ka kb i
theorem shortStep {k : Nat} {D : List PackedState} (hn : PackedLevel true stopT k (limbRows k))
    (hc : D.all (shortCheck k) = true) : PackedLevel true stopT (k+1) D := by
  intro st hs
  have checked := List.all_eq_true.mp hc st hs
  obtain ⟨ws,hints⟩ := st
  cases hints with
  | nil => simp [shortCheck] at checked
  | cons h bank =>
    by_cases leaf : h%2 = 1
    · simp only [shortCheck,leaf] at checked
      exact signedLeaf_sound checked
    · simp only [shortCheck,leaf] at checked
      have verified := tapeState_sound sixModel (shortIndex_agrees k) checked
      have one : PackedLevel true stopT (k+1) [(ws,bank)] := by
        apply localLevelAll (k:=k) (prev:=limbRows k) (masks:=sixMasks) (pick:=sixSepIndex) (bank:=sixBank) stopB certTabsValid hn
        simpa only [List.all_cons,List.all_nil,Bool.and_true] using verified
      exact one (ws,bank) (by simp)
end PEqualNP.Outside.L_meta_10393_aux

namespace PEqualNP.Outside.L_meta_10393_aux
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem local4part0 : shortChunk 4 0 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem local5part0 : shortChunk 5 0 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem local5part1 : shortChunk 5 1 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem local5part2 : shortChunk 5 2 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem local5part3 : shortChunk 5 3 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem local6part0 : shortChunk 6 0 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem local6part1 : shortChunk 6 1 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem local6part2 : shortChunk 6 2 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem local6part3 : shortChunk 6 3 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem local6part4 : shortChunk 6 4 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem local6part5 : shortChunk 6 5 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem local6part6 : shortChunk 6 6 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem local6part7 : shortChunk 6 7 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem local6part8 : shortChunk 6 8 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem local6part9 : shortChunk 6 9 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem local6part10 : shortChunk 6 10 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem local6part11 : shortChunk 6 11 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem local6part12 : shortChunk 6 12 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem local7part0 : shortChunk 7 0 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem local7part1 : shortChunk 7 1 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem local7part2 : shortChunk 7 2 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem local7part3 : shortChunk 7 3 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem local7part4 : shortChunk 7 4 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem local7part5 : shortChunk 7 5 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem local7part6 : shortChunk 7 6 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem local7part7 : shortChunk 7 7 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem local7part8 : shortChunk 7 8 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem local8part0 : shortChunk 8 0 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem local8part1 : shortChunk 8 1 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem local8part2 : shortChunk 8 2 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem local9part0 : shortChunk 9 0 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem local10part0 : shortChunk 10 0 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem local11part0 : shortChunk 11 0 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem local12part0 : shortChunk 12 0 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem localValidated4 : PackedLevel true stopT 4 (limbRows 4) := by
  apply shortStep shortBefore
  apply packedAllChunks 64 1 (by decide) (by decide +kernel)
  intro i hi
  interval_cases i
  · exact local4part0
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem localValidated5 : PackedLevel true stopT 5 (limbRows 5) := by
  apply shortStep localValidated4
  apply packedAllChunks 64 4 (by decide) (by decide +kernel)
  intro i hi
  interval_cases i
  · exact local5part0
  · exact local5part1
  · exact local5part2
  · exact local5part3
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem localValidated6 : PackedLevel true stopT 6 (limbRows 6) := by
  apply shortStep localValidated5
  apply packedAllChunks 64 13 (by decide) (by decide +kernel)
  intro i hi
  interval_cases i
  · exact local6part0
  · exact local6part1
  · exact local6part2
  · exact local6part3
  · exact local6part4
  · exact local6part5
  · exact local6part6
  · exact local6part7
  · exact local6part8
  · exact local6part9
  · exact local6part10
  · exact local6part11
  · exact local6part12
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem localValidated7 : PackedLevel true stopT 7 (limbRows 7) := by
  apply shortStep localValidated6
  apply packedAllChunks 64 9 (by decide) (by decide +kernel)
  intro i hi
  interval_cases i
  · exact local7part0
  · exact local7part1
  · exact local7part2
  · exact local7part3
  · exact local7part4
  · exact local7part5
  · exact local7part6
  · exact local7part7
  · exact local7part8
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem localValidated8 : PackedLevel true stopT 8 (limbRows 8) := by
  apply shortStep localValidated7
  apply packedAllChunks 64 3 (by decide) (by decide +kernel)
  intro i hi
  interval_cases i
  · exact local8part0
  · exact local8part1
  · exact local8part2
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem localValidated9 : PackedLevel true stopT 9 (limbRows 9) := by
  apply shortStep localValidated8
  apply packedAllChunks 64 1 (by decide) (by decide +kernel)
  intro i hi
  interval_cases i
  · exact local9part0
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem localValidated10 : PackedLevel true stopT 10 (limbRows 10) := by
  apply shortStep localValidated9
  apply packedAllChunks 64 1 (by decide) (by decide +kernel)
  intro i hi
  interval_cases i
  · exact local10part0
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem localValidated11 : PackedLevel true stopT 11 (limbRows 11) := by
  apply shortStep localValidated10
  apply packedAllChunks 64 1 (by decide) (by decide +kernel)
  intro i hi
  interval_cases i
  · exact local11part0
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem localValidated12 : PackedLevel true stopT 12 (limbRows 12) := by
  apply shortStep localValidated11
  apply packedAllChunks 64 1 (by decide) (by decide +kernel)
  intro i hi
  interval_cases i
  · exact local12part0
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem signedThirteen : LowN true stopR stopT 13 :=
  packedLowSearch stopB localValidated12 (by decide +kernel)
end PEqualNP.Outside.L_meta_10393_aux

namespace PEqualNP.Outside.L_meta_10393_aux.SevenRoot
open PEqualNP.CircuitLowerBounds
def sevenT : Nat := 0xfffffffffffffffefffffffefffefee8
def sevenR : List Nat := [0,1,2,3,4,5,6]
def sevenE : List (Nat × Nat × Nat) := [(0,2,3),(1,1,3),(2,1,5),(3,1,9),(4,1,17),(5,1,33),(6,1,65)]
theorem sevenB : baseOK sevenT sevenR sevenE = true := by decide +kernel
def sevenSlices : List SliceD := [(0x55555555555555555555555555555555,13,[1,2,3,4,5,6]),(0x33333333333333333333333333333333,13,[0,2,3,4,5,6]),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f,13,[0,1,3,4,5,6]),(0xff00ff00ff00ff00ff00ff00ff00ff,13,[0,1,2,4,5,6]),(0xffff0000ffff0000ffff0000ffff,13,[0,1,2,3,5,6]),(0xffffffff00000000ffffffff,13,[0,1,2,3,4,6]),(0xffffffffffffffff,13,[0,1,2,3,4,5])]
theorem sevenSlice0 (hl : LowN true stopR stopT 13) : SliceN true sevenR sevenT (0x55555555555555555555555555555555,13,[1,2,3,4,5,6]) :=
  mkSlice (w:=0) sevenB stopB hl (by decide +kernel)
theorem sevenSlice1 (hl : LowN true stopR stopT 13) : SliceN true sevenR sevenT (0x33333333333333333333333333333333,13,[0,2,3,4,5,6]) :=
  mkSlice (w:=0) sevenB stopB hl (by decide +kernel)
theorem sevenSlice2 (hl : LowN true stopR stopT 13) : SliceN true sevenR sevenT (0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f,13,[0,1,3,4,5,6]) :=
  mkSlice (w:=0) sevenB stopB hl (by decide +kernel)
theorem sevenSlice3 (hl : LowN true stopR stopT 13) : SliceN true sevenR sevenT (0xff00ff00ff00ff00ff00ff00ff00ff,13,[0,1,2,4,5,6]) :=
  mkSlice (w:=0) sevenB stopB hl (by decide +kernel)
theorem sevenSlice4 (hl : LowN true stopR stopT 13) : SliceN true sevenR sevenT (0xffff0000ffff0000ffff0000ffff,13,[0,1,2,3,5,6]) :=
  mkSlice (w:=0) sevenB stopB hl (by decide +kernel)
theorem sevenSlice5 (hl : LowN true stopR stopT 13) : SliceN true sevenR sevenT (0xffffffff00000000ffffffff,13,[0,1,2,3,4,6]) :=
  mkSlice (w:=0) sevenB stopB hl (by decide +kernel)
theorem sevenSlice6 (hl : LowN true stopR stopT 13) : SliceN true sevenR sevenT (0xffffffffffffffff,13,[0,1,2,3,4,5]) :=
  mkSlice (w:=0) sevenB stopB hl (by decide +kernel)
theorem sevenValid (hl : LowN true stopR stopT 13) : ∀ s ∈ sevenSlices, SliceN true sevenR sevenT s := by
  unfold sevenSlices
  simp only [List.forall_mem_cons]
  exact ⟨sevenSlice0 hl,sevenSlice1 hl,sevenSlice2 hl,sevenSlice3 hl,sevenSlice4 hl,sevenSlice5 hl,sevenSlice6 hl,by simp⟩
def sevenCuts : List (Nat × List (Nat × Nat × Nat)) := [(0,[]),(1,[]),(2,[]),(3,[]),(4,[]),(5,[]),(6,[])]
def sevenTab : Tabs := (sevenCuts.map (mkCut true sevenSlices),[(5,4),(3,1),(3,0),(3,2),(5,1),(5,0),(9,1),(9,0),(17,1),(17,0),(33,1),(33,0),(65,1),(65,0),(6,2),(10,2),(18,2),(34,2),(66,2),(12,4),(20,4),(36,4),(68,4),(24,8),(40,8),(72,8),(48,16),(80,16),(96,32)],[],[])
theorem sevenTabOK (hl : LowN true stopR stopT 13) : TabsP true sevenR sevenT sevenTab :=
  ⟨cutsGood (sevenValid hl) (by decide +kernel),by decide +kernel,by decide +kernel,by decide +kernel⟩
def rootState : StD := (sevenR.map xN, [[0,1,10000,10001,10002],[0,2,10003,10004,10005],[0,3,10003,10006,10007],[0,4,10003,10008,10009],[0,5,10003,10010,10011],[0,6,10003,10012,10013],[1,2,10001,10014,10004],[1,3,10001,10015,10006],[1,4,10001,10016,10008],[1,5,10001,10017,10010],[1,6,10001,10018,10012],[2,3,10004,10019,10006],[2,4,10004,10020,10008],[2,5,10004,10021,10010],[2,6,10004,10022,10012],[3,4,10006,10023,10008],[3,5,10006,10024,10010],[3,6,10006,10025,10012],[4,5,10008,10026,10010],[4,6,10008,10027,10012],[5,6,10010,10028,10012]])
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem rootCheck : stOK true sevenT sevenTab 13 [] rootState = true := by decide +kernel
theorem signedFifteen (hl : LowN true stopR stopT 13) : LowN true sevenR sevenT 15 := by
  apply lowOf sevenB
  have h := stStep sevenB (sevenTabOK hl) (by simp) rootCheck
  simpa only [rootState,sevenR,rootsW,List.map_map,Function.comp_def] using h
def target : (Fin 7 → Bool) → Bool := (fun x : Fin 7 → Bool => decide (2 ≤ ((List.ofFn x).count true)))
def theInputs : List Sig := rootsW [0,1,2,3,4,5,6]
def graph : Sig := W sevenT
theorem graph_proper : proper graph := (baseOK_ok sevenB).prop
def sample (r : Row) (i : Fin 7) : Bool := bit r (theInputs.getD i.val zero)
theorem theList : List.ofFn (fun i : Fin 7 => theInputs.getD i.val zero) = theInputs := rfl
theorem sampled (r : Row) : List.ofFn (sample r) = theInputs.map (bit r) := by
  rw [←theList,List.map_ofFn]
  rfl
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem theTable : ∀ r : Row, bit r graph = target (sample r) := by unfold target; decide +kernel
theorem theEval (C : Circuit) (h : PEqualNP.MetaComplexity.FanInTwo C)
    (i : Nat) (r : Row) : bit r ((execute C.gates theInputs).getD i zero) =
      (C.wires (List.ofFn (sample r))).getD i false := by
  rw [←b_read,execute_bits _ _ _ (fun g hg => (h g hg).1),sampled]
  rfl
theorem physical (u : Bool) (C : Circuit) (legal : PEqualNP.MetaComplexity.FanInTwo C)
    (mono : u=false → ∀ g ∈ C.gates, isNot g=false)
    (computes : ∀ x : Fin 7 → Bool, C.eval (List.ofFn x)=target x) :
    ∃ k, k ≤ C.gates.countP (fun g => !isNot g) ∧ Live u graph k theInputs.toFinset := by
  have b := baseOK_ok sevenB
  have goalEq : (execute C.gates theInputs).getD C.output zero = graph := by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    let r : Row := ⟨j,hj⟩
    exact (theEval C legal C.output r).trans ((computes (sample r)).trans (theTable r).symm)
  have out := get_rep (u:=u) (execute C.gates theInputs) C.output
  rw [goalEq] at out
  unfold Repr at out
  have pg : bit 0 graph = false := by
    change bit 0 (W sevenT) = false
    have := b.plain
    unfold plainWord at this
    simpa using this
  rw [nrm_id pg] at out
  obtain ⟨k,S,hk,run,sub⟩ := extract (u:=u) C.gates theInputs legal mono graph_proper
    (out.resolve_right (fun h => h graph_proper))
  have ns : theInputs.all plainWord = true := b.plainR
  rw [nrm_map ns] at sub
  have eq : S = theInputs.toFinset := by
    ext a
    constructor
    · exact fun h => List.mem_toFinset.mpr (sub a h)
    · intro ha
      obtain ⟨r,s,hd,iso⟩ := b.ess a (List.mem_toFinset.mp ha)
      exact raw_required run theInputs a sub r s hd iso
  exact ⟨k,hk,eq ▸ run⟩
theorem excludes {u : Bool} {L : Nat} (low : LowN u [0,1,2,3,4,5,6] sevenT L) : ∀ k, k < L → ¬Live u graph k theInputs.toFinset := by
  intro k small run
  have steps := list_run run theInputs (by decide +kernel) rfl
  obtain ⟨q, bank, built, hit, limit⟩ := contraction (observe_proper graph_proper)
    steps (theInputs.map observe) Reach.start (fun _ h => Or.inl h)
  have bound := low q bank built hit
  omega
theorem paidFifteen (hl : LowN true stopR stopT 13) (C : Circuit) (fan : PEqualNP.MetaComplexity.FanInTwo C)
    (computes : ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = target x) : 15 ≤ C.gates.countP (fun g => !isNot g) := by
  obtain ⟨k,hk,run⟩ := physical true C fan (by simp) computes
  by_contra h
  exact excludes (signedFifteen hl) k (by omega) run
theorem noCircuit (lowSix : LowN true stopR stopT 13)
    (mono : ∀ C : Circuit, PEqualNP.MetaComplexity.Monotone2 C →
       (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = target x) → 16 ≤ C.size) :
    ¬ PEqualNP.MetaComplexity.HasCircuitSize 7 target 15 := by
  rintro ⟨C,fan,small,correct⟩
  classical
  by_cases only : ∀ g ∈ C.gates, isNot g = false
  · have hm : PEqualNP.MetaComplexity.Monotone2 C := by
      intro g hg
      obtain ⟨ops,inputs⟩ := fan g hg
      refine ⟨?_,inputs⟩
      rcases ops with h | h | h
      · exact Or.inl h
      · exact Or.inr h
      · have hn := only g hg
        change g.op = .not at h
        simp [isNot,h] at hn
    have h := mono C hm correct
    omega
  · push Not at only
    obtain ⟨g,hg,hop⟩ := only
    have lt : C.gates.countP (fun q => !isNot q) < C.gates.length := by
      rcases Nat.lt_or_ge (C.gates.countP (fun q => !isNot q)) C.gates.length with h|h
      · exact h
      · have eq := List.countP_eq_length.mp (Nat.le_antisymm List.countP_le_length h) g hg
        cases hn : isNot g <;> simp_all
    have bound := paidFifteen lowSix C fan correct
    change C.gates.length ≤ 15 at small
    omega
end PEqualNP.Outside.L_meta_10393_aux.SevenRoot

namespace PEqualNP.Outside.L_meta_10393_aux

namespace ThresholdSixBound.Leaf5459
def zeroGate (k : Fin 4) (a b : Bool) : Bool :=
  match k.val with
  | 0 => a && b
  | 1 => a || b
  | 2 => a && !b
  | _ => !a && b
theorem zeroGate_canalizes :
    ∀ k : Fin 4,
      (∃ b c : Bool, ∀ a : Bool, zeroGate k a b = c) ∧
      (∃ a c : Bool, ∀ b : Bool, zeroGate k a b = c) := by
  decide
abbrev Formula (n : Nat) := BinaryTree (Sum (Fin n) Bool)
def formEval {n : Nat} : Formula n → (Fin n → Bool) → Bool
  | .nil, _ => false
  | .node (.inl i) _ _, x => x i
  | .node (.inr false) l r, x => formEval l x || formEval r x
  | .node (.inr true) l r, x => formEval l x && formEval r x
def singleInput {n : Nat} (i : Fin n) : Fin n → Bool :=
  fun j => decide (j = i)
def pairInput {n : Nat} (i j : Fin n) : Fin n → Bool :=
  fun k => decide (k = i ∨ k = j)
def formOcc {n : Nat} : Formula n → Fin n → Nat
  | .nil, _ => 0
  | .node (.inl j) _ _, i => if j = i then 1 else 0
  | .node (.inr _) l r, i => formOcc l i + formOcc r i
open scoped BigOperators
def cCube {α : Type*} [Fintype α] [DecidableEq α]
    (s : Finset α) (b : α → Bool) : Finset (α → Bool) :=
  Fintype.piFinset fun a => if a ∈ s then {b a} else Finset.univ
theorem cCubeMember {α : Type*} [Fintype α] [DecidableEq α]
    (s : Finset α) (b f : α → Bool) :
    f ∈ cCube s b ↔ ∀ a ∈ s, f a = b a := by
  simp only [cCube, Fintype.mem_piFinset]
  constructor
  · intro h a ha
    simpa only [ite_eq_left ha, Finset.mem_singleton] using h a
  · intro h a
    by_cases ha : a ∈ s
    · simpa only [ite_eq_left ha, Finset.mem_singleton] using h a ha
    · simp only [ite_eq_right ha, Finset.mem_univ]
theorem cCubeCard {α : Type*} [Fintype α] [DecidableEq α]
    (s : Finset α) (b : α → Bool) :
    (cCube s b).card = ∏ a : α, if a ∈ s then 1 else 2 := by
  rw [cCube, Fintype.card_piFinset]
  apply Finset.prod_congr rfl
  intro a ha
  by_cases hs : a ∈ s <;> simp [hs]
theorem cCubeVolume {α : Type*} [Fintype α] [DecidableEq α]
    (s : Finset α) (b : α → Bool) :
    (cCube s b).card * 2 ^ s.card = 2 ^ Fintype.card α := by
  rw [cCubeCard]
  have hs : (∏ a : α, if a ∈ s then 2 else 1) = 2 ^ s.card := by simp
  rw [← hs, ← Finset.prod_mul_distrib]
  have he : (∏ a : α, (if a ∈ s then 1 else 2) * (if a ∈ s then 2 else 1)) =
      ∏ _a : α, 2 := by
    apply Finset.prod_congr rfl
    intro a ha
    by_cases h : a ∈ s <;> simp [h]
  rw [he]
  simp
section Generic
variable {α : Type} {β : Type}
def UC (G : Fin 4 → α → α → α) (A : Fin 4 → Prop) : ℕ → (α → Prop) → α → Prop
  | 0, S, f => S f
  | t + 1, S, f => UC G A t S f ∨
      ∃ k a b, A k ∧ S a ∧ S b ∧ UC G A t (fun w => w = G k a b ∨ S w) f
theorem UC_monoS (G : Fin 4 → α → α → α) (A : Fin 4 → Prop) :
    ∀ (t : ℕ) (S S' : α → Prop) (f : α), (∀ w, S w → S' w) → UC G A t S f → UC G A t S' f
  | 0, _, _, f, h, hu => h f hu
  | t + 1, S, S', f, h, hu => by
    rcases hu with hu | ⟨k, a, b, hk, ha, hb, hu⟩
    · exact Or.inl (UC_monoS G A t S S' f h hu)
    · exact Or.inr ⟨k, a, b, hk, h a ha, h b hb,
        UC_monoS G A t _ _ f (fun w hw => hw.imp id (h w)) hu⟩
theorem UC_le {G : Fin 4 → α → α → α} {A : Fin 4 → Prop} {t t' : ℕ} {S : α → Prop} {f : α}
    (h : t ≤ t') (hu : UC G A t S f) : UC G A t' S f := by
  induction h with
  | refl => exact hu
  | step _ ih => exact Or.inl ih
theorem UC_gate {G : Fin 4 → α → α → α} {A : Fin 4 → Prop} {t : ℕ} {S : α → Prop} {f : α}
    (k : Fin 4) (a b : α) (hk : A k) (ha : S a) (hb : S b)
    (hu : UC G A t (fun w => w = G k a b ∨ S w) f) : UC G A (t + 1) S f :=
  Or.inr ⟨k, a, b, hk, ha, hb, hu⟩
theorem UC_map {G : Fin 4 → α → α → α} {G' : Fin 4 → β → β → β} {A : Fin 4 → Prop} (e : α → β)
    (he : ∀ k a b, e (G k a b) = G' k (e a) (e b)) :
    ∀ (t : ℕ) (S : α → Prop) (S' : β → Prop) (f : α), (∀ w, S w → S' (e w)) →
      UC G A t S f → UC G' A t S' (e f)
  | 0, _, _, f, h, hu => h f hu
  | t + 1, S, S', f, h, hu => by
    rcases hu with hu | ⟨k, a, b, hk, ha, hb, hu⟩
    · exact Or.inl (UC_map e he t S S' f h hu)
    · refine Or.inr ⟨k, e a, e b, hk, h a ha, h b hb, UC_map e he t _ _ f ?_ hu⟩
      intro w hw
      rcases hw with rfl | hw
      · exact Or.inl (he k a b)
      · exact Or.inr (h w hw)
def TR (G : Fin 4 → α → α → α) (C : Fin 4 → α → α → Prop) (ys : List α) (t : ℕ)
    (ws : List α) : Prop :=
  ∀ P : ℕ → List α → Prop, P 0 ys →
    (∀ s xs zs, List.Perm xs zs → P s xs → P s zs) →
    (∀ s a b r (k : Fin 4) (u : ℕ), C k a b →
      P s (List.replicate (u + 1) (G k a b) ++ r) → P (s + 1) (a :: b :: r)) →
    P t ws
section Run
variable {G : Fin 4 → α → α → α} {C : Fin 4 → α → α → Prop} {ys : List α}
theorem TR.done : TR G C ys 0 ys := fun _ d _ _ => d
theorem TR.perm {s : ℕ} {xs zs : List α} (p : List.Perm xs zs) (h : TR G C ys s xs) :
    TR G C ys s zs := fun P d q st => q s xs zs p (h P d q st)
theorem TR.step {s : ℕ} {a b : α} {r : List α} (k : Fin 4) (u : ℕ) (hc : C k a b)
    (h : TR G C ys s (List.replicate (u + 1) (G k a b) ++ r)) :
    TR G C ys (s + 1) (a :: b :: r) := fun P d q st => st s a b r k u hc (h P d q st)
theorem TR.ind {P : ℕ → List α → Prop} {t : ℕ} {ws : List α} (h : TR G C ys t ws)
    (d : P 0 ys)
    (p : ∀ s xs zs, List.Perm xs zs → TR G C ys s xs → P s xs → P s zs)
    (st : ∀ s a b r (k : Fin 4) (u : ℕ), C k a b →
      TR G C ys s (List.replicate (u + 1) (G k a b) ++ r) →
      P s (List.replicate (u + 1) (G k a b) ++ r) → P (s + 1) (a :: b :: r)) : P t ws :=
  (h (fun s xs => TR G C ys s xs ∧ P s xs) ⟨TR.done, d⟩
    (fun s xs zs hp hx => ⟨TR.perm hp hx.1, p s xs zs hp hx.1 hx.2⟩)
    (fun s a b r k u hc hx => ⟨TR.step k u hc hx.1, st s a b r k u hc hx.1 hx.2⟩)).2
theorem TR.inv {t : ℕ} {ws : List α} (h : TR G C ys t ws) :
    (t = 0 → List.Perm ws ys) ∧
    (∀ s, t = s + 1 → ∃ (k : Fin 4) (u : ℕ) (a b : α) (r : List α), C k a b ∧
      List.Perm ws (a :: b :: r) ∧ TR G C ys s (List.replicate (u + 1) (G k a b) ++ r)) := by
  refine TR.ind (P := fun t ws => (t = 0 → List.Perm ws ys) ∧
    (∀ s, t = s + 1 → ∃ (k : Fin 4) (u : ℕ) (a b : α) (r : List α), C k a b ∧
      List.Perm ws (a :: b :: r) ∧ TR G C ys s (List.replicate (u + 1) (G k a b) ++ r))) h
    ⟨fun _ => List.Perm.refl _, fun s hs => by omega⟩ ?_ ?_
  · intro s xs zs hp _ ih
    refine ⟨fun h0 => hp.symm.trans (ih.1 h0), fun s' hs => ?_⟩
    obtain ⟨k, u, a, b, r, hc, hq, hr⟩ := ih.2 s' hs
    exact ⟨k, u, a, b, r, hc, hp.symm.trans hq, hr⟩
  · intro s a b r k u hc hr _
    refine ⟨fun h0 => by omega, fun s' hs => ?_⟩
    have : s = s' := by omega
    subst this
    exact ⟨k, u, a, b, r, hc, List.Perm.refl _, hr⟩
theorem TR.len {t : ℕ} {ws : List α} (h : TR G C ys t ws) : ws.length ≤ t + ys.length := by
  refine TR.ind (P := fun t ws => ws.length ≤ t + ys.length) h (by simp) ?_ ?_
  · intro s xs zs hp _ ih
    rw [← hp.length_eq]; exact ih
  · intro s a b r k u _ _ ih
    simp only [List.length_append, List.length_replicate, List.length_cons] at ih ⊢
    omega
theorem TR.monoC {C' : Fin 4 → α → α → Prop} (hC : ∀ k a b, C k a b → C' k a b) {t : ℕ}
    {ws : List α} (h : TR G C ys t ws) : TR G C' ys t ws :=
  TR.ind (P := fun t ws => TR G C' ys t ws) h TR.done (fun _ _ _ hp _ ih => TR.perm hp ih)
    (fun _ _ _ _ k u hc _ ih => TR.step k u (hC _ _ _ hc) ih)
end Run
def strictC (G : Fin 4 → α → α → α) (z : α) (A : Fin 4 → Prop) (I : α → Prop) :
    Fin 4 → α → α → Prop :=
  fun k a b => A k ∧ I a ∧ I b ∧ a ≠ b ∧ G k a b ≠ a ∧ G k a b ≠ b ∧ G k a b ≠ z
theorem normalize [DecidableEq α] (G : Fin 4 → α → α → α) (z : α) (A : Fin 4 → Prop)
    (I : α → Prop) (hI : ∀ k a b, I a → I b → I (G k a b))
    (hz1 : ∀ k b, G k z b = z ∨ G k z b = b) (hz2 : ∀ k a, G k a z = z ∨ G k a z = a)
    (hd : ∀ k a, G k a a = z ∨ G k a a = a) :
    ∀ (t : ℕ) (S : α → Prop) (f : α), (∀ w, S w → I w) → f ≠ z → UC G A t S f →
      ∃ t', t' ≤ t ∧ ∃ ws : List α, (∀ w ∈ ws, S w ∧ w ≠ z) ∧
        TR G (strictC G z A I) [f] t' ws
  | 0, S, f, _, hf, hu => ⟨0, le_rfl, [f], by simpa using ⟨hu, hf⟩, TR.done⟩
  | t + 1, S, f, hS, hf, hu => by
    rcases hu with hu | ⟨k, a, b, hk, ha, hb, hu⟩
    · obtain ⟨t', ht, ws, hws, hr⟩ := normalize G z A I hI hz1 hz2 hd t S f hS hf hu
      exact ⟨t', by omega, ws, hws, hr⟩
    · obtain ⟨t', ht, ws, hws, hr⟩ := normalize G z A I hI hz1 hz2 hd t _ f (by
        rintro w (rfl | hw)
        · exact hI k a b (hS a ha) (hS b hb)
        · exact hS w hw) hf hu
      by_cases hg : S (G k a b)
      · refine ⟨t', by omega, ws, fun w hw => ⟨?_, (hws w hw).2⟩, hr⟩
        rcases (hws w hw).1 with rfl | h
        · exact hg
        · exact h
      by_cases hc : G k a b ∈ ws
      · have hgz : G k a b ≠ z := (hws _ hc).2
        have hga : G k a b ≠ a := fun h => hg (by rw [h]; exact ha)
        have hgb : G k a b ≠ b := fun h => hg (by rw [h]; exact hb)
        have hab : a ≠ b := by
          rintro rfl
          rcases hd k a with h | h
          · exact hgz h
          · exact hga h
        have haz : a ≠ z := by
          rintro rfl
          rcases hz1 k b with h | h
          · exact hgz h
          · exact hgb h
        have hbz : b ≠ z := by
          rintro rfl
          rcases hz2 k a with h | h
          · exact hgz h
          · exact hga h
        obtain ⟨u, hu1⟩ : ∃ u, List.count (G k a b) ws = u + 1 :=
          ⟨List.count (G k a b) ws - 1, by have := List.count_pos_iff.2 hc; omega⟩
        have hperm : ws.Perm (List.replicate (u + 1) (G k a b) ++ ws.filter (· ≠ G k a b)) := by
          rw [← hu1, ← List.filter_eq]
          have := List.filter_append_perm (fun x => decide (x = G k a b)) ws
          refine this.symm.trans ?_
          simp
        refine ⟨t' + 1, by omega, a :: b :: ws.filter (· ≠ G k a b), ?_,
          TR.step k u ⟨hk, hS a ha, hS b hb, hab, hga, hgb, hgz⟩ (TR.perm hperm hr)⟩
        intro w hw
        simp only [List.mem_cons, List.mem_filter, decide_eq_true_eq] at hw
        rcases hw with rfl | rfl | ⟨hw, hne⟩
        · exact ⟨ha, haz⟩
        · exact ⟨hb, hbz⟩
        · rcases (hws w hw).1 with h | h
          · exact absurd h hne
          · exact ⟨h, (hws w hw).2⟩
      · refine ⟨t', by omega, ws, fun w hw => ⟨?_, (hws w hw).2⟩, hr⟩
        rcases (hws w hw).1 with rfl | h
        · exact absurd hw hc
        · exact h
theorem TR.map {G : Fin 4 → α → α → α} {G' : Fin 4 → β → β → β} {C : Fin 4 → α → α → Prop}
    {C' : Fin 4 → β → β → Prop} (e : α → β) (he : ∀ k a b, e (G k a b) = G' k (e a) (e b))
    (hC : ∀ k a b, C k a b → C' k (e a) (e b)) {ys : List α} {t : ℕ} {ws : List α}
    (h : TR G C ys t ws) : TR G' C' (ys.map e) t (ws.map e) := by
  refine TR.ind (P := fun t ws => TR G' C' (ys.map e) t (ws.map e)) h TR.done
    (fun _ _ _ hp _ ih => TR.perm (hp.map e) ih) ?_
  intro s a b r k u hc _ ih
  rw [List.map_append, List.map_replicate, he] at ih
  exact TR.step k u (hC _ _ _ hc) ih
theorem TR.rel {G : Fin 4 → α → α → α} {A : Fin 4 → Prop} (R : α → α → Prop)
    (hR : ∀ k a a' b b', R a a' → R b b' → R (G k a b) (G k a' b')) {ys : List α} {t : ℕ}
    {ws : List α} (h : TR G (fun k _ _ => A k) ys t ws) :
    ∀ ws', List.Forall₂ R ws ws' →
      ∃ ys', List.Forall₂ R ys ys' ∧ TR G (fun k _ _ => A k) ys' t ws' := by
  refine TR.ind (P := fun t ws => ∀ ws', List.Forall₂ R ws ws' →
      ∃ ys', List.Forall₂ R ys ys' ∧ TR G (fun k _ _ => A k) ys' t ws') h
    (fun ws' hw => ⟨ws', hw, TR.done⟩) ?_ ?_
  · intro s xs zs hp _ ih zs' hz
    obtain ⟨xs', hx, hp'⟩ := List.perm_comp_forall₂ hp hz
    obtain ⟨ys', hy, hr⟩ := ih xs' hx
    exact ⟨ys', hy, TR.perm hp' hr⟩
  · intro s a b r k u hc _ ih ws' hw
    obtain ⟨a', t1, ha, ht1, rfl⟩ := List.forall₂_cons_left_iff.1 hw
    obtain ⟨b', r', hb, hr', rfl⟩ := List.forall₂_cons_left_iff.1 ht1
    have h1 : List.Forall₂ R (List.replicate (u + 1) (G k a b) ++ r)
        (List.replicate (u + 1) (G k a' b') ++ r') := by
      refine List.rel_append ?_ hr'
      generalize u + 1 = n
      induction n with
      | zero => exact List.Forall₂.nil
      | succ n ih => exact List.Forall₂.cons (hR k a a' b b' ha hb) ih
    obtain ⟨ys', hy, hrun⟩ := ih _ h1
    exact ⟨ys', hy, TR.step k u hc hrun⟩
end Generic
def MonoA : Fin 4 → Prop := fun k => k.val < 2
theorem mono_cases (k : Fin 4) (hk : MonoA k) : k=0 ∨ k=1 := by fin_cases k <;> simp_all [MonoA]
end ThresholdSixBound.Leaf5459
namespace ThresholdSixBound.Six
open Leaf5459 PEqualNP.Outside.L_meta_10393_aux
abbrev BF := (Fin 6 → Bool) → Bool
def gF (k : Fin 4) (a b : BF) : BF := fun x => zeroGate k (a x) (b x)
def var (i : Fin 6) : BF := fun x => x i
def ThrL (V : Fin 6 → Prop) (F : BF) : Prop :=
  (∀ i, V i → F (singleInput i) = false) ∧ ∀ i j, V i → V j → i ≠ j → F (pairInput i j) = true
def target (x : Fin 6 → Bool) : Bool := decide (2 ≤ (List.ofFn x).count true)
def MonoF (w : BF) : Prop := ∀ x y, (∀ i, x i = true → y i = true) → w x = true → w y = true
theorem gF_and (a b : BF) : gF 0 a b = fun p => a p && b p := rfl
theorem gF_or (a b : BF) : gF 1 a b = fun p => a p || b p := rfl
def sample (r : Row) (i : Fin 6) : Bool := bit r (W (xN i.val))
def sem (f : BF) : Wire Row := fun r => f (sample r)
theorem initialCov (w : BF) (hw : ∃ i, w = var i) :
    Available true ((rootsW stopR).map observe) (sem w) := by
  obtain ⟨i,rfl⟩ := hw
  apply Or.inl
  apply List.mem_map.mpr
  refine ⟨W (xN i.val),?_,rfl⟩
  apply List.mem_map.mpr
  exact ⟨i.val,(by fin_cases i <;> decide),rfl⟩
theorem simulate (m : Nat) (S : BF → Prop) (f : BF) (hu : UC gF MonoA m S f)
    (p : Nat) (bank : List (Wire Row)) (rb : Reach true ((rootsW stopR).map observe) p bank)
    (supply : ∀ w, S w → Available true bank (sem w)) :
    ∃ p' bank', Reach true ((rootsW stopR).map observe) p' bank' ∧
      Available true bank' (sem f) ∧ p' ≤ p+m := by
  induction m generalizing S f p bank with
  | zero => exact ⟨p,bank,rb,supply f hu,by omega⟩
  | succ m ih =>
    rcases hu with old | ⟨k,a,b,hk,ha,hb,run⟩
    · obtain ⟨j,ws,hr,ht,le⟩ := ih S f old p bank rb supply
      exact ⟨j,ws,hr,ht,by omega⟩
    · let op := decide (k=1)
      have eq : sem (gF k a b) = combine op (sem a) (sem b) := by
        rcases mono_cases k hk with rfl | rfl <;> rfl
      have next := Reach.two op rb (supply _ ha) (supply _ hb)
      have supp : ∀ w, (w = gF k a b ∨ S w) → Available true (combine op (sem a) (sem b)::bank) (sem w) := by
        rintro w (rfl | orig)
        · exact Or.inl (by simp [eq])
        · exact available_cons _ (supply _ orig)
      obtain ⟨j,ws,hr,ht,le⟩ := ih _ f run (p+1) _ next supp
      exact ⟨j,ws,hr,ht,by omega⟩
def SixLow := LowN true stopR stopT 13
theorem ucLower (lb : SixLow) (hu : UC gF MonoA 12 (fun w => ∃ i, w = var i) target) : False := by
  obtain ⟨k,ws,rb,ht,le⟩ := simulate 12 _ _ hu 0 _ Reach.start initialCov
  have eq : ∀ r : Row, sem target r = bit r (W stopT) := by decide +kernel
  have ee : sem target = observe (W stopT) := funext eq
  rw [ee] at ht
  have bot := lb k ws rb ht
  omega
theorem uc_mono : ∀ m (S : BF → Prop) f, (∀ w, S w → MonoF w) →
    UC gF MonoA m S f → MonoF f
  | 0,_,f,hs,h => hs f h
  | m+1,S,f,hs,h => by
    rcases h with ho | ⟨k,a,b,hk,ha,hb,ho⟩
    · exact uc_mono m S f hs ho
    · refine uc_mono m _ f ?_ ho
      rintro w (rfl | hw)
      · intro x y hxy hx
        rcases mono_cases k hk with rfl | rfl
        · rw [gF_and] at hx ⊢
          exact Bool.and_eq_true_iff.mpr
            ⟨hs _ ha x y hxy (Bool.and_eq_true_iff.mp hx).1,hs _ hb x y hxy (Bool.and_eq_true_iff.mp hx).2⟩
        · rw [gF_or] at hx ⊢
          simp only [Bool.or_eq_true] at hx ⊢
          exact hx.imp (hs _ ha x y hxy) (hs _ hb x y hxy)
      · exact hs _ hw
theorem M6 (lb : SixLow) {f : BF} (h : ThrL (fun _ => True) f)
    (hu : UC gF MonoA 12 (fun w => ∃ i, w = var i) f) : False := by
  have mono := uc_mono 12 _ f (by rintro w ⟨i,rfl⟩; exact fun _ _ hxy => hxy i) hu
  have small : ∀ x : Fin 6 → Bool, target x = false →
      ∃ i : Fin 6, ∀ j, x j = true → singleInput i j = true := by decide +kernel
  have large : ∀ x : Fin 6 → Bool, target x = true →
      ∃ i j : Fin 6, i ≠ j ∧ ∀ k, pairInput i j k = true → x k = true := by decide +kernel
  have ef : f = target := by
    funext x
    cases e : target x with
    | true =>
      obtain ⟨i,j,hn,p⟩ := large x e
      exact mono _ _ p (h.2 i j trivial trivial hn)
    | false =>
      obtain ⟨i,p⟩ := small x e
      cases v : f x with
      | false => rfl
      | true => exact Bool.noConfusion ((h.1 i trivial).symm.trans (mono _ _ p v))
  rw [ef] at hu
  exact ucLower lb hu
end ThresholdSixBound.Six

namespace ThresholdSixBound.Seven
open Leaf5459
open PEqualNP.MetaComplexity PEqualNP.CircuitLowerBounds
abbrev BF := (Fin 7 → Bool) → Bool
def gF (k : Fin 4) (a b : BF) : BF := fun x => zeroGate k (a x) (b x)
def var (i : Fin 7) : BF := fun x => x i
def zF : BF := fun _ => false
def rst (p : Fin 7) (a : BF) : BF := fun x => a (Function.update x p false)
def ThrL (V : Fin 7 → Prop) (F : BF) : Prop :=
  (∀ i, V i → F (singleInput i) = false) ∧
    ∀ i j, V i → V j → i ≠ j → F (pairInput i j) = true
theorem gF_zero_left (k : Fin 4) (b : BF) : gF k zF b = zF ∨ gF k zF b = b := by
  fin_cases k
  · exact Or.inl (funext fun x => by simp [gF, zF, zeroGate])
  · exact Or.inr (funext fun x => by simp [gF, zF, zeroGate])
  · exact Or.inl (funext fun x => by simp [gF, zF, zeroGate])
  · exact Or.inr (funext fun x => by simp [gF, zF, zeroGate])
theorem gF_zero_right (k : Fin 4) (a : BF) : gF k a zF = zF ∨ gF k a zF = a := by
  fin_cases k
  · exact Or.inl (funext fun x => by simp [gF, zF, zeroGate])
  · exact Or.inr (funext fun x => by simp [gF, zF, zeroGate])
  · exact Or.inr (funext fun x => by simp [gF, zF, zeroGate])
  · exact Or.inl (funext fun x => by simp [gF, zF, zeroGate])
theorem gF_self (k : Fin 4) (a : BF) : gF k a a = zF ∨ gF k a a = a := by
  fin_cases k
  · exact Or.inr (funext fun x => by simp [gF, zeroGate])
  · exact Or.inr (funext fun x => by simp [gF, zeroGate])
  · exact Or.inl (funext fun x => by simp [gF, zF, zeroGate])
  · exact Or.inl (funext fun x => by simp [gF, zF, zeroGate])
theorem gF_zero_zero (k : Fin 4) : gF k zF zF = zF := by
  fin_cases k <;> exact funext fun x => by simp [gF, zF, zeroGate]
theorem upd_single {i p : Fin 7} (h : i ≠ p) :
    Function.update (singleInput i) p false = singleInput i := by
  funext m
  by_cases hm : m = p
  · subst hm; simp [singleInput, Ne.symm h]
  · simp [Function.update_of_ne hm]
theorem upd_pair {i j p : Fin 7} (hi : i ≠ p) (hj : j ≠ p) :
    Function.update (pairInput i j) p false = pairInput i j := by
  funext m
  by_cases hm : m = p
  · subst hm; simp [pairInput, Ne.symm hi, Ne.symm hj]
  · simp [Function.update_of_ne hm]
theorem rst_var_self (p : Fin 7) : rst p (var p) = zF :=
  funext fun x => by simp [rst, var, zF]
theorem rst_var_ne {i p : Fin 7} (h : i ≠ p) : rst p (var i) = var i :=
  funext fun x => by simp [rst, var, Function.update_of_ne h]
theorem var_inj {i j : Fin 7} (h : var i = var j) : i = j := by
  have := congrFun h (singleInput i)
  exact (by simpa [var, singleInput] using this : j = i).symm
theorem TRF_det {C : Fin 4 → BF → BF → Prop} {ys : List BF} {s : ℕ} {ws : List BF}
    (h : TR gF C ys s ws) (x x' : Fin 7 → Bool) :
    (∀ w ∈ ws, w x = w x') → ∀ y ∈ ys, y x = y x' := by
  refine TR.ind (P := fun _ ws => (∀ w ∈ ws, w x = w x') → ∀ y ∈ ys, y x = y x') h
    (fun h => h) ?_ ?_
  · intro s xs zs hp _ ih hz
    exact ih fun t ht => hz t (hp.mem_iff.1 ht)
  · intro s a b r k u _ _ ih hz
    apply ih
    intro t ht
    rcases List.mem_append.1 ht with ht | ht
    · rw [List.eq_of_mem_replicate ht]
      show zeroGate k (a x) (b x) = zeroGate k (a x') (b x')
      rw [hz a (by simp), hz b (by simp)]
    · exact hz t (by simp [ht])
def dcount (p : Fin 7) (ws : List BF) : ℕ := ws.countP fun w => decide (rst p w = zF)
theorem dcount_cons (p : Fin 7) (a : BF) (l : List BF) :
    dcount p (a :: l) = dcount p l + if rst p a = zF then 1 else 0 := by
  simp [dcount, List.countP_cons]
theorem dcount_rep (p : Fin 7) (n : ℕ) (g : BF) (r : List BF) :
    dcount p (List.replicate n g ++ r) = (if rst p g = zF then n else 0) + dcount p r := by
  simp only [dcount, List.countP_append, List.countP_replicate]
  split_ifs <;> simp_all
theorem pot_dead {A : Fin 4 → Prop} (p : Fin 7) {F : BF} (hF : rst p F ≠ zF) {s : ℕ}
    {ws : List BF} (h : TR gF (fun k _ _ => A k) [F] s ws) :
    dcount p ws ≤ s ∧ ∀ S : BF → Prop, (∀ w ∈ ws, rst p w ≠ zF → S (rst p w)) →
      UC gF A (s - dcount p ws) S (rst p F) := by
  refine TR.ind (P := fun s ws => dcount p ws ≤ s ∧ ∀ S : BF → Prop,
    (∀ w ∈ ws, rst p w ≠ zF → S (rst p w)) → UC gF A (s - dcount p ws) S (rst p F)) h ?_ ?_ ?_
  · refine ⟨by simp [dcount, hF], fun S hS => ?_⟩
    have : dcount p [F] = 0 := by simp [dcount, hF]
    rw [this]
    exact hS F (by simp) hF
  · intro s xs zs hp _ ih
    have hc : dcount p zs = dcount p xs := (hp.countP_eq _).symm
    rw [hc]
    exact ⟨ih.1, fun S hS => ih.2 S fun w hw => hS w (hp.mem_iff.1 hw)⟩
  · intro s a b r k u hk _ ih
    obtain ⟨ih1, ih2⟩ := ih
    have hg : rst p (gF k a b) = gF k (rst p a) (rst p b) := rfl
    rw [dcount_rep] at ih1 ih2
    rw [dcount_cons, dcount_cons]
    have hmem : ∀ (S : BF → Prop), (∀ w ∈ a :: b :: r, rst p w ≠ zF → S (rst p w)) →
        ∀ w ∈ r, rst p w ≠ zF → S (rst p w) := fun S hS w hw => hS w (by simp [hw])
    by_cases ha : rst p a = zF <;> by_cases hb : rst p b = zF
    · have hgz : rst p (gF k a b) = zF := by rw [hg, ha, hb, gF_zero_zero]
      simp only [hgz, ha, hb, ite_true] at ih1 ih2 ⊢
      refine ⟨by omega, fun S hS => UC_le (by omega) (ih2 S ?_)⟩
      intro w hw hwz
      rcases List.mem_append.1 hw with hw | hw
      · exact absurd (List.eq_of_mem_replicate hw ▸ hgz) hwz
      · exact hmem S hS w hw hwz
    · by_cases hgz : rst p (gF k a b) = zF
      · simp only [hgz, ha, hb, ite_true, ite_false] at ih1 ih2 ⊢
        refine ⟨by omega, fun S hS => UC_le (by omega) (ih2 S ?_)⟩
        intro w hw hwz
        rcases List.mem_append.1 hw with hw | hw
        · exact absurd (List.eq_of_mem_replicate hw ▸ hgz) hwz
        · exact hmem S hS w hw hwz
      · have hgb : rst p (gF k a b) = rst p b := by
          rcases gF_zero_left k (rst p b) with h | h
          · exact absurd (by rw [hg, ha, h]) hgz
          · rw [hg, ha, h]
        simp only [hgz, ha, hb, ite_true, ite_false] at ih1 ih2 ⊢
        refine ⟨by omega, fun S hS => UC_le (by omega) (ih2 S ?_)⟩
        intro w hw hwz
        rcases List.mem_append.1 hw with hw | hw
        · rw [List.eq_of_mem_replicate hw, hgb]
          exact hS b (by simp) hb
        · exact hmem S hS w hw hwz
    · by_cases hgz : rst p (gF k a b) = zF
      · simp only [hgz, ha, hb, ite_true, ite_false] at ih1 ih2 ⊢
        refine ⟨by omega, fun S hS => UC_le (by omega) (ih2 S ?_)⟩
        intro w hw hwz
        rcases List.mem_append.1 hw with hw | hw
        · exact absurd (List.eq_of_mem_replicate hw ▸ hgz) hwz
        · exact hmem S hS w hw hwz
      · have hga : rst p (gF k a b) = rst p a := by
          rcases gF_zero_right k (rst p a) with h | h
          · exact absurd (by rw [hg, hb, h]) hgz
          · rw [hg, hb, h]
        simp only [hgz, ha, hb, ite_true, ite_false] at ih1 ih2 ⊢
        refine ⟨by omega, fun S hS => UC_le (by omega) (ih2 S ?_)⟩
        intro w hw hwz
        rcases List.mem_append.1 hw with hw | hw
        · rw [List.eq_of_mem_replicate hw, hga]
          exact hS a (by simp) ha
        · exact hmem S hS w hw hwz
    · by_cases hgz : rst p (gF k a b) = zF
      · simp only [hgz, ha, hb, ite_true, ite_false] at ih1 ih2 ⊢
        refine ⟨by omega, fun S hS => UC_le (by omega) (ih2 S ?_)⟩
        intro w hw hwz
        rcases List.mem_append.1 hw with hw | hw
        · exact absurd (List.eq_of_mem_replicate hw ▸ hgz) hwz
        · exact hmem S hS w hw hwz
      · simp only [hgz, ha, hb, ite_false] at ih1 ih2 ⊢
        refine ⟨by omega, fun S hS => ?_⟩
        have h1 := ih2 (fun w => w = gF k (rst p a) (rst p b) ∨ S w) (by
          intro w hw hwz
          rcases List.mem_append.1 hw with hw | hw
          · exact Or.inl (by rw [List.eq_of_mem_replicate hw, hg])
          · exact Or.inr (hmem S hS w hw hwz))
        have h2 := UC_gate k (rst p a) (rst p b) hk (hS a (by simp) ha) (hS b (by simp) hb) h1
        exact UC_le (by omega) h2
theorem ex_third : ∀ p q : Fin 7, ∃ r, r ≠ p ∧ r ≠ q := by decide
theorem thr_rst {F : BF} (hF : ThrL (fun _ => True) F) (p : Fin 7) :
    (∀ j, rst p F (singleInput (p.succAbove j)) = false) ∧
    (∀ j j', j ≠ j' → rst p F (pairInput (p.succAbove j) (p.succAbove j')) = true) := by
  refine ⟨fun j => ?_, fun j j' hj => ?_⟩
  · show F (Function.update (singleInput (p.succAbove j)) p false) = false
    rw [upd_single (Fin.succAbove_ne p j)]
    exact hF.1 _ trivial
  · show F (Function.update (pairInput (p.succAbove j) (p.succAbove j')) p false) = true
    rw [upd_pair (Fin.succAbove_ne p j) (Fin.succAbove_ne p j')]
    exact hF.2 _ _ trivial trivial fun h => hj (Fin.succAbove_right_injective h)
theorem thr_rst_ne {F : BF} (hF : ThrL (fun _ => True) F) (p : Fin 7) : rst p F ≠ zF := by
  intro h
  have := (thr_rst hF p).2 0 1 (by decide)
  rw [h] at this
  exact Bool.noConfusion this
theorem thr_ne_zero {F : BF} (hF : ThrL (fun _ => True) F) : F ≠ zF := by
  intro h
  have := hF.2 0 1 trivial trivial (by decide)
  rw [h] at this
  exact Bool.noConfusion this
theorem to_run {A : Fin 4 → Prop} {F : BF} (hF : ThrL (fun _ => True) F) {t : ℕ}
    (hu : UC gF A t (fun w => ∃ i, w = var i) F) :
    ∃ t', t' ≤ t ∧ ∃ ws : List BF, (∀ w ∈ ws, ∃ i, w = var i) ∧
      TR gF (fun k _ _ => A k) [F] t' ws := by
  obtain ⟨t', ht, ws, hws, hr⟩ := normalize gF zF A (fun _ => True) (fun _ _ _ _ _ => trivial)
    gF_zero_left gF_zero_right gF_self t _ F (fun _ _ => trivial) (thr_ne_zero hF) hu
  exact ⟨t', ht, ws, fun w hw => (hws w hw).1, TR.monoC (fun _ _ _ h => h.1) hr⟩
theorem gF_and (a b : BF) : gF 0 a b = fun p => a p && b p := rfl
theorem gF_or (a b : BF) : gF 1 a b = fun p => a p || b p := rfl
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
def gv (g : Gate) (W : List BF) : BF :=
  fun x => g.op.eval (g.inputs.map fun i => (W.getD i zF) x)
def wiresF : List Gate → List BF → List BF
  | [], W => W
  | g :: gs, W => wiresF gs (W ++ [gv g W])
theorem getD_map_x (W : List BF) (i : ℕ) (x : Fin 7 → Bool) :
    (W.map fun w => w x).getD i false = (W.getD i zF) x := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases W[i]? <;> rfl
theorem wires_eq (x : Fin 7 → Bool) : ∀ (gs : List Gate) (W : List BF),
    gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
      (W.map fun w => w x) = (wiresF gs W).map fun w => w x
  | [], W => rfl
  | g :: gs, W => by
    simp only [List.foldl_cons, wiresF]
    rw [← wires_eq x gs (W ++ [gv g W])]
    congr 1
    simp only [List.map_append, List.map_cons, List.map_nil, gv, getD_map_x]
theorem getD_mem (W : List BF) (i : ℕ) : W.getD i zF ∈ W ∨ W.getD i zF = zF := by
  rw [List.getD_eq_getElem?_getD]
  rcases h : W[i]? with _ | a
  · exact Or.inr rfl
  · exact Or.inl (List.mem_of_getElem? h)
def target (x : Fin 7 → Bool) : Bool := decide (2 ≤ (List.ofFn x).count true)
theorem targetThr : ThrL (fun _ => True) target := by
  constructor <;> decide +kernel
def proj (p : Fin 7) (w : BF) : Six.BF := fun y => w (p.insertNth false y)
theorem projVar (p : Fin 7) (j : Fin 6) : proj p (var (p.succAbove j)) = Six.var j := by
  funext y
  simp [proj, var, Six.var]
theorem projectThr : ∀ p : Fin 7, Six.ThrL (fun _ => True) (proj p (rst p target)) := by
  unfold Six.ThrL
  decide +kernel
theorem transfer {A : Fin 4 → Prop} (low : ℕ)
    (lb : ∀ (f : Six.BF), Six.ThrL (fun _ => True) f →
      ∀ k : ℕ, UC Six.gF A k (fun w => ∃ i, w = Six.var i) f → low ≤ k)
    {s : ℕ} {ws : List BF}
    (h : TR gF (fun k _ _ => A k) [target] s ws)
    (hw : ∀ w ∈ ws, ∃ i, w = var i) : low+2 ≤ s := by
  have hF := targetThr
  rcases s with _ | s
  · have hp := (TR.inv h).1 rfl
    obtain ⟨i, hi⟩ := hw target (hp.mem_iff.2 (by simp))
    have := hF.1 i trivial
    rw [hi] at this
    simp [var, singleInput] at this
  · obtain ⟨k, u, a, b, r, -, hp, hr⟩ := (TR.inv h).2 s rfl
    obtain ⟨p, rfl⟩ := hw a (hp.mem_iff.2 (by simp))
    obtain ⟨q, rfl⟩ := hw b (hp.mem_iff.2 (by simp))
    have hcnt : dcount p ws = dcount p (var p :: var q :: r) := hp.countP_eq _
    have key : 2 ≤ dcount p ws := by
      rw [hcnt, dcount_cons, dcount_cons]
      by_cases hpq : p = q
      · subst hpq; simp [rst_var_self]
      by_cases hmem : var p ∈ r
      · have : 1 ≤ dcount p r := by
          unfold dcount
          exact List.countP_pos_iff.2 ⟨var p, hmem, by simp [rst_var_self]⟩
        simp only [rst_var_self, ite_true]
        omega
      exfalso
      have hrv : ∀ w ∈ r, ∃ i, i ≠ p ∧ w = var i := by
        intro w hw'
        obtain ⟨i, hi⟩ := hw w (hp.mem_iff.2 (by simp [hw']))
        refine ⟨i, ?_, hi⟩
        rintro rfl
        exact hmem (hi ▸ hw')
      obtain ⟨β, c, hβ⟩ := (zeroGate_canalizes k).1
      cases β
      · obtain ⟨r₀, hr1, hr2⟩ := ex_third p q
        have hd := TRF_det hr (pairInput p r₀) (singleInput r₀) (by
          intro w hw'
          rcases List.mem_append.1 hw' with hw' | hw'
          · rw [List.eq_of_mem_replicate hw']
            have e1 : var q (pairInput p r₀) = false := by
              simp [var, pairInput, Ne.symm hpq, Ne.symm hr2]
            have e2 : var q (singleInput r₀) = false := by simp [var, singleInput, Ne.symm hr2]
            show zeroGate k (var p _) (var q _) = zeroGate k (var p _) (var q _)
            rw [e1, e2, hβ, hβ]
          · obtain ⟨i, hi, rfl⟩ := hrv w hw'
            simp [var, pairInput, singleInput, hi]) target (by simp)
        rw [hF.1 r₀ trivial, hF.2 p r₀ trivial trivial (Ne.symm hr1)] at hd
        exact Bool.noConfusion hd
      · have hd := TRF_det hr (pairInput p q) (singleInput q) (by
          intro w hw'
          rcases List.mem_append.1 hw' with hw' | hw'
          · rw [List.eq_of_mem_replicate hw']
            have e1 : var q (pairInput p q) = true := by simp [var, pairInput]
            have e2 : var q (singleInput q) = true := by simp [var, singleInput]
            show zeroGate k (var p _) (var q _) = zeroGate k (var p _) (var q _)
            rw [e1, e2, hβ, hβ]
          · obtain ⟨i, hi, rfl⟩ := hrv w hw'
            simp [var, pairInput, singleInput, hi]) target (by simp)
        rw [hF.1 q trivial, hF.2 p q trivial trivial hpq] at hd
        exact Bool.noConfusion hd
    obtain ⟨h1, h2⟩ := pot_dead p (thr_rst_ne hF p) h
    have h3 := h2 (fun w => ∃ j, w = var (p.succAbove j)) (by
      intro w hw' hwz
      obtain ⟨i, rfl⟩ := hw w hw'
      by_cases hi : i = p
      · subst hi; exact absurd (rst_var_self i) hwz
      · obtain ⟨j, hj⟩ := Fin.exists_succAbove_eq hi
        exact ⟨j, by rw [rst_var_ne hi, hj]⟩)
    have mapped := UC_map (G' := Six.gF) (proj p) (fun _ _ _ => rfl)
      _ _ (fun w => ∃ i, w = Six.var i) _
      (by rintro w ⟨i, rfl⟩; exact ⟨i, projVar p i⟩) h3
    have hh := lb _ (projectThr p) _ mapped
    omega
end ThresholdSixBound.Seven
namespace ThresholdSixBound.OneShare
open Leaf5459
open scoped BigOperators
def wOcc {n : Nat} (x : Fin n → Bool) : Formula n → Nat
  | .nil => 0
  | .node (.inl i) _ _ => (x i).toNat
  | .node (.inr _) l r => wOcc x l + wOcc x r
def gCut {n d : Nat} (X : Fin d → Fin n → Bool) (l r : Formula n) (i : Fin d) : Option Bool :=
  match formEval l (X i), formEval r (X i) with
  | true,false => some false
  | false,true => some true
  | _,_ => none
def gCuts {n d : Nat} (X : Fin d → Fin n → Bool) : Formula n → List (Fin d → Option Bool)
  | .nil => []
  | .node (.inl _) _ _ => []
  | .node (.inr false) l r => gCuts X l ++ gCuts X r
  | .node (.inr true) l r => gCut X l r :: (gCuts X l ++ gCuts X r)
def width {d : Nat} (L : List (Fin d → Option Bool)) (i : Fin d) := L.countP (fun c => (c i).isSome)
theorem weight_bound {n d : Nat} (X : Fin d → Fin n → Bool) (t : Formula n) (i : Fin d) :
    width (gCuts X t) i + (formEval t (X i)).toNat ≤ wOcc (X i) t := by
  induction t with
  | nil => simp [width,gCuts,formEval,wOcc]
  | node a l r hl hr =>
    cases a with
    | inl j => simp [width,gCuts,formEval,wOcc]
    | inr op =>
      cases op <;> cases el : formEval l (X i) <;> cases er : formEval r (X i) <;>
        simp [width,gCuts,formEval,gCut,wOcc,el,er,List.countP_append] at * <;> omega
def FormulaSeparates {d : Nat} (L : List (Fin d → Option Bool)) (i j : Fin d) :=
  ∃ c ∈ L, (c i = some false ∧ c j = some true) ∨ (c i = some true ∧ c j = some false)
theorem generalized_separator {n d : Nat} (X : Fin d → Fin n → Bool) (t : Formula n) (i j : Fin d)
    (hp : formEval t (fun k => X i k || X j k) = true)
    (hi : formEval t (X i) = false) (hj : formEval t (X j) = false) :
    FormulaSeparates (gCuts X t) i j := by
  induction t with
  | nil => simp [formEval] at hp
  | node a l r hl hr =>
    cases a with
    | inl k =>
      change X i k = false at hi
      change X j k = false at hj
      change X i k || X j k = true at hp
      simp [hi,hj] at hp
    | inr op =>
      cases op with
      | false =>
        simp only [formEval, Bool.or_eq_true] at hp
        simp only [formEval, Bool.or_eq_false_iff] at hi hj
        rcases hp with hp | hp
        · obtain ⟨c, hc, hs⟩ := hl hp hi.1 hj.1
          exact ⟨c, by simp [gCuts, hc], hs⟩
        · obtain ⟨c, hc, hs⟩ := hr hp hi.2 hj.2
          exact ⟨c, by simp [gCuts, hc], hs⟩
      | true =>
        simp only [formEval, Bool.and_eq_true] at hp
        have liftL (hli : formEval l (X i) = false)
            (hlj : formEval l (X j) = false) :
            ∃ c ∈ gCuts X (.node (.inr true) l r),
              (c i = some false ∧ c j = some true) ∨
              (c i = some true ∧ c j = some false) := by
          obtain ⟨c, hc, hs⟩ := hl hp.1 hli hlj
          exact ⟨c, by simp [gCuts, hc], hs⟩
        have liftR (hri : formEval r (X i) = false)
            (hrj : formEval r (X j) = false) :
            ∃ c ∈ gCuts X (.node (.inr true) l r),
              (c i = some false ∧ c j = some true) ∨
              (c i = some true ∧ c j = some false) := by
          obtain ⟨c, hc, hs⟩ := hr hp.2 hri hrj
          exact ⟨c, by simp [gCuts, hc], hs⟩
        cases eli : formEval l (X i) with
        | false =>
          cases elj : formEval l (X j) with
          | false => exact liftL eli elj
          | true =>
            have erj : formEval r (X j) = false := by
              simpa [formEval, elj] using hj
            cases eri : formEval r (X i) with
            | false => exact liftR eri erj
            | true =>
              refine ⟨gCut X l r, by simp [gCuts], Or.inr ?_⟩
              simp [gCut, eli, elj, eri, erj]
        | true =>
          have eri : formEval r (X i) = false := by
            simpa [formEval, eli] using hi
          cases erj : formEval r (X j) with
          | false => exact liftR eri erj
          | true =>
            have elj : formEval l (X j) = false := by
              simpa [formEval, erj] using hj
            refine ⟨gCut X l r, by simp [gCuts], Or.inl ?_⟩
            simp [gCut, eli, elj, eri, erj]
theorem pack {d : Nat} (I : Finset (Fin d)) (L : List (Fin d → Option Bool))
    (denom : Nat) (weights : Fin d → Nat)
    (bound : ∀ i ∈ I, 2 ^ width L i * weights i ≤ denom)
    (sep : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → FormulaSeparates L i j) : I.sum weights ≤ denom := by
  classical
  let s (i : Fin d) : Finset (Fin L.length) := Finset.univ.filter fun k => ((L.get k) i).isSome
  let b (i : Fin d) (k : Fin L.length) := ((L.get k) i).getD false
  have hcard (i) : (s i).card = width L i := by
    simpa [s,width,List.ofFn_get] using (List.countP_ofFn (List.get L) (fun c => (c i).isSome)).symm
  have disj : (I : Set (Fin d)).PairwiseDisjoint (fun i => cCube (s i) (b i)) := by
    intro i hi j hj hn
    apply Finset.disjoint_left.mpr
    intro f hfi hfj
    obtain ⟨c,hc,hs⟩ := sep i hi j hj hn
    obtain ⟨k,hk⟩ := List.mem_iff_get.mp hc
    have ei := cCubeMember (s i) (b i) f |>.mp hfi k
    have ej := cCubeMember (s j) (b j) f |>.mp hfj k
    rcases hs with ⟨hi,hj⟩ | ⟨hi,hj⟩ <;> simp [s,b,hk,hi,hj] at ei ej <;> simp_all
  let vol := 2 ^ Fintype.card (Fin L.length)
  have tot : I.sum (fun i => (cCube (s i) (b i)).card) ≤ vol := by
    rw [← Finset.card_biUnion disj]
    simpa [vol] using Finset.card_le_univ (I.biUnion (fun i => cCube (s i) (b i)))
  have each (i) (hi : i ∈ I) : vol * weights i ≤ (cCube (s i) (b i)).card * denom := by
    change 2 ^ Fintype.card (Fin L.length) * weights i ≤ _
    rw [← cCubeVolume (s i) (b i), Nat.mul_assoc,hcard]
    exact Nat.mul_le_mul_left _ (bound i hi)
  have ht := Finset.sum_le_sum each
  rw [← Finset.mul_sum, ← Finset.sum_mul] at ht
  have hh := ht.trans (Nat.mul_le_mul_right denom tot)
  have hv : 0 < vol := Nat.pow_pos (by decide)
  exact Nat.le_of_mul_le_mul_left hh hv
theorem monotone_eval {n} (t : Formula n) {x y : Fin n → Bool}
    (hle : ∀ i, x i = true → y i = true) (hx : formEval t x = true) :
    formEval t y = true := by
  induction t with
  | nil => cases hx
  | node a l r hl hr =>
    cases a with
    | inl i => exact hle _ hx
    | inr op =>
      cases op
      · simp only [formEval, Bool.or_eq_true] at hx ⊢
        exact hx.elim (fun h => Or.inl (hl h)) (fun h => Or.inr (hr h))
      · simp only [formEval, Bool.and_eq_true] at hx ⊢
        exact ⟨hl hx.1, hr hx.2⟩
end ThresholdSixBound.OneShare

namespace ThresholdSixBound.Leaf5459
theorem map_perm_cons {β γ : Type} (f : β → γ) {l : List β} {a : γ} {r : List γ}
    (h : (l.map f).Perm (a :: r)) :
    ∃ x l', l.Perm (x :: l') ∧ f x = a ∧ (l'.map f).Perm r := by
  have ha : a ∈ l.map f := h.mem_iff.2 (by simp)
  obtain ⟨x, hx, rfl⟩ := List.mem_map.1 ha
  obtain ⟨l₁, l₂, rfl⟩ := List.append_of_mem hx
  refine ⟨x, l₁ ++ l₂, List.perm_middle, rfl, ?_⟩
  have h1 := (List.perm_middle (a := x) (l₁ := l₁) (l₂ := l₂)).map f
  exact (h1.symm.trans h).cons_inv
end ThresholdSixBound.Leaf5459
namespace ThresholdSeven
open ThresholdSixBound ThresholdSixBound.Leaf5459 ThresholdSixBound.OneShare
def delta (b x : Bool) : Bool := if b then false else x
def joinO {n} (op : Bool) : Option (Formula n) → Option (Formula n) → Option (Formula n)
  | some a,some b => some (.node (.inr op) a b)
  | some a,none => if op then some a else none
  | none,some b => if op then some b else none
  | none,none => none
def erase {n} (b : Fin n → Bool) : Formula n → Option (Formula n)
  | .nil => some .nil
  | .node (.inl i) _ _ => if b i then none else some (.node (.inl i) .nil .nil)
  | .node (.inr op) l r => joinO op (erase b l) (erase b r)
def oval {n} (t : Option (Formula n)) (x : Fin n → Bool) := t.elim true (fun f => formEval f x)
def charged {n} (x : Fin n → Bool) (t : Option (Formula n)) := t.elim 0 (wOcc x)
def bot {n : ℕ} : Fin n → Bool := fun _ => false
def supB {n} (x y : Fin n → Bool) := fun k => x k || y k
def Below {n} (x y : Fin n → Bool) := ∀ i, x i = true → y i = true
theorem erase_eval {n} (b x : Fin n → Bool) (h : Below b x) (t : Formula n) :
    oval (erase b t) x = formEval t x := by
  induction t with
  | nil => rfl
  | node a l r hl hr =>
    cases a with
    | inl i =>
      cases e : b i <;> simp_all [erase,oval,formEval,Below]
    | inr op =>
      cases op <;> cases a : erase b l <;> cases c : erase b r <;>
        simp_all [erase,joinO,oval,formEval]
theorem erase_charge {n} (b x : Fin n → Bool) (t : Formula n) :
    charged x (erase b t) ≤ wOcc (fun i => delta (b i) (x i)) t := by
  induction t with
  | nil => rfl
  | node a l r hl hr =>
    cases a with
    | inl i => cases e : b i <;> simp [erase,charged,wOcc,e,delta]
    | inr op =>
      cases op <;> cases a : erase b l <;> cases c : erase b r <;>
        simp_all [erase,joinO,charged,wOcc] <;> omega
def rcuts {n d} (b : Fin n → Bool) (X : Fin d → Fin n → Bool) (t : Formula n) :=
  (erase b t).elim [] (gCuts X)
theorem rcharge {n d} (b : Fin n → Bool) (X : Fin d → Fin n → Bool) (t : Formula n)
    (i : Fin d) (h : Below b (X i)) :
    width (rcuts b X t) i + (delta (formEval t b) (formEval t (X i))).toNat ≤
      wOcc (fun j => delta (b j) (X i j)) t := by
  have b0 : Below b b := fun _ h => h
  have A := erase_eval b b b0 t
  have B := erase_eval b (X i) h t
  have K := erase_charge b (X i) t
  cases e : erase b t with
  | none => simp [e,oval] at A; simp [rcuts,e,delta,← A,width]
  | some q =>
    simp only [e,oval,Option.elim_some] at A B
    simp only [e,charged,Option.elim_some] at K
    have W := weight_bound X q i
    simp only [rcuts,e,Option.elim_some]
    have D : (delta (formEval t b) (formEval t (X i))).toNat ≤ (formEval t (X i)).toNat := by
      cases formEval t b <;> cases formEval t (X i) <;> decide
    rw [B] at W
    omega
theorem rsep {n d} (b : Fin n → Bool) (X : Fin d → Fin n → Bool) (t : Formula n)
    (i j : Fin d) (bi : Below b (X i)) (bj : Below b (X j))
    (hp : formEval t (supB (X i) (X j)) = true)
    (hi : formEval t (X i) = false) (hj : formEval t (X j) = false) :
    FormulaSeparates (rcuts b X t) i j := by
  have b2 : Below b (supB (X i) (X j)) := fun k h => by simp [supB,bi k h]
  have p := (erase_eval _ _ b2 t).trans hp
  have h := (erase_eval _ _ bi t).trans hi
  have k := (erase_eval _ _ bj t).trans hj
  cases e : erase b t with
  | none => simp [e,oval] at h
  | some q =>
    simp only [e,oval,Option.elim_some] at p h k
    exact (show FormulaSeparates (rcuts b X t) i j from by
      simpa [rcuts,e] using (generalized_separator X q i j p h k))
theorem wVar {n} (t : Formula n) (i : Fin n) :
    wOcc (singleInput i) t = formOcc t i := by
  induction t with
  | nil => rfl
  | node a l r hl hr =>
    cases a with
    | inl j => by_cases h : j=i <;> simp [singleInput,wOcc,formOcc,h]
    | inr op => simp [wOcc,formOcc,hl,hr]
theorem wLast {n} (t : Formula (n+1)) (x : Fin n → Bool) (v : Bool) :
    wOcc (Fin.snoc x v) t =
      wOcc (Fin.snoc x false) t + v.toNat * formOcc t (Fin.last n) := by
  induction t with
  | nil => simp [wOcc,formOcc]
  | node a l r hl hr =>
    cases a with
    | inl j => induction j using Fin.lastCases <;> simp [wOcc,formOcc,Fin.snoc,Fin.lastCases_last,Fin.lastCases_castSucc]
    | inr op => simp only [wOcc,formOcc,hl,hr,Nat.mul_add]; omega
theorem ws1 (t : Formula 8) (i : Fin 7) (b : Bool) :
    wOcc (Fin.snoc (singleInput i) b) t =
      formOcc t i.castSucc + b.toNat * formOcc t (Fin.last 7) := by
  rw [wLast]
  congr 1
  rw [← wVar]
  have h : ∀ i : Fin 7, (Fin.snoc (singleInput i) false : Fin 8 → Bool) = singleInput i.castSucc := by decide
  rw [h]
theorem ws2 (t : Formula 9) (i : Fin 7) (b c : Bool) :
    wOcc (Fin.snoc (Fin.snoc (singleInput i) b) c) t =
      formOcc t i.castSucc.castSucc + b.toNat * formOcc t (Fin.last 7).castSucc +
      c.toNat * formOcc t (Fin.last 8) := by
  induction t with
  | nil => simp [wOcc,formOcc]
  | node a l r hl hr =>
    cases a with
    | inr op => simp only [wOcc,formOcc,hl,hr,Nat.mul_add]; omega
    | inl j =>
      generalize_proofs
      exact (show ∀ (i : Fin 7) (j : Fin 9) (b c : Bool),
        ((Fin.snoc (Fin.snoc (singleInput i) b) c : Fin 9 → Bool) j).toNat =
        (if j=i.castSucc.castSucc then 1 else 0) +
        b.toNat*(if j=(Fin.last 7).castSucc then 1 else 0) +
        c.toNat*(if j=Fin.last 8 then 1 else 0) by decide +kernel) i j b c
end ThresholdSeven
namespace ThresholdSeven
open ThresholdSixBound ThresholdSixBound.Leaf5459 ThresholdSixBound.OneShare
abbrev V := Fin 7
abbrev X := V → Bool
def inG (H : Formula 7) (x : X) : Fin 8 → Bool := Fin.snoc x (formEval H x)
def inQ (H : Formula 7) (G : Formula 8) (x : X) : Fin 9 → Bool :=
  Fin.snoc (inG H x) (formEval G (inG H x))
def B (H : Formula 7) (i : V) := formEval H (singleInput i)
def C (H : Formula 7) (G : Formula 8) (i : V) := formEval G (inG H (singleInput i))
def baseG (a : Bool) : Fin 8 → Bool := Fin.snoc bot a
def baseC (a b : Bool) (G : Formula 8) := b || formEval G (baseG a)
def baseQ (a b : Bool) (G : Formula 8) : Fin 9 → Bool := Fin.snoc (baseG a) (baseC a b G)
def active (a b : Bool) (H : Formula 7) (G : Formula 8) (i : V) : Prop :=
  (a = true → B H i = true) ∧ (b = true → C H G i = true)
theorem belowBot {n} (x : Fin n → Bool) : Below bot x := by simp [Below,bot]
theorem belowLast {n} {x y : Fin n → Bool} {p q : Bool}
    (h : Below x y) (k : p = true → q = true) : Below (Fin.snoc x p) (Fin.snoc y q) := by
  intro i
  induction i using Fin.lastCases <;> simp_all [Fin.snoc_last, Fin.snoc_castSucc,Below]
theorem belowX {n} (i j : Fin n) : Below (singleInput i) (pairInput i j) := by
  intro k hk
  simp [singleInput] at hk
  simp [pairInput,hk]
theorem belowY {n} (i j : Fin n) : Below (singleInput j) (pairInput i j) := by
  intro k hk
  simp [singleInput] at hk
  simp [pairInput,hk]
theorem sup_in {n} (i j : Fin n) : supB (singleInput i) (singleInput j) = pairInput i j := by
  funext k
  by_cases h : k=i <;> simp [supB,singleInput,pairInput,h]
theorem sup_snoc {n} (x y : Fin n → Bool) (u v : Bool) :
    supB (Fin.snoc x u) (Fin.snoc y v) = Fin.snoc (supB x y) (u || v) := by
  funext i
  induction i using Fin.lastCases <;> simp [supB]
theorem delta_snoc {n} (x y : Fin n → Bool) (u v : Bool) :
    (fun i => delta ((Fin.snoc x u : Fin (n+1) → Bool) i) ((Fin.snoc y v : Fin (n+1) → Bool) i)) =
    Fin.snoc (fun i => delta (x i) (y i)) (delta u v) := by
  funext i
  induction i using Fin.lastCases <;> simp
theorem val0 {n} (t : Formula n) : formEval t bot = false := by
  induction t with
  | nil => rfl
  | node a l r hl hr => cases a with
    | inl i => rfl
    | inr op => cases op <;> simp [formEval,hl,hr]
theorem bg_ok {a b H G i} (hi : active a b H G i) : Below (baseG a) (inG H (singleInput i)) :=
  belowLast (belowBot _) hi.1
theorem bc_ok {a b H G i} (hi : active a b H G i) : baseC a b G = true → C H G i = true := by
  intro h
  have dis : b = true ∨ formEval G (baseG a) = true := by simpa [baseC] using h
  rcases dis with h | h
  · exact hi.2 h
  · exact monotone_eval G (bg_ok hi) h
theorem bq_ok {a b H G i} (hi : active a b H G i) : Below (baseQ a b G) (inQ H G (singleInput i)) :=
  belowLast (bg_ok hi) (bc_ok hi)
def ch (a : Bool) (H : Formula 7) : List (V → Option Bool) :=
  if a then [] else rcuts bot singleInput H
def cg (a b : Bool) (H : Formula 7) (G : Formula 8) : List (V → Option Bool) :=
  if b then [] else rcuts (baseG a) (fun i => inG H (singleInput i)) G
def cq (a b : Bool) (H : Formula 7) (G : Formula 8) (Q : Formula 9) : List (V → Option Bool) :=
  rcuts (baseQ a b G) (fun i => inQ H G (singleInput i)) Q
def layers (a b : Bool) (H : Formula 7) (G : Formula 8) (Q : Formula 9) :=
  ch a H ++ cg a b H G ++ cq a b H G Q
theorem gap : ∀ p q r : Bool, (p = true → r = true) → (q = true → r = true) →
    r ≠ (p || q) → p = false ∧ q = false ∧ r = true := by decide
theorem rootSep (a b : Bool) (H : Formula 7) (G : Formula 8) (Q : Formula 9) (i j : V)
    (iy : active a b H G i) (jy : active a b H G j)
    (loi : formEval Q (inQ H G (singleInput i)) = false)
    (loj : formEval Q (inQ H G (singleInput j)) = false)
    (hi : formEval Q (inQ H G (pairInput i j)) = true) :
    FormulaSeparates (layers a b H G Q) i j := by
  have h1 := monotone_eval H (belowX i j)
  have h2 := monotone_eval H (belowY i j)
  by_cases eH : formEval H (pairInput i j) = (B H i || B H j)
  · have se : supB (inG H (singleInput i)) (inG H (singleInput j)) = inG H (pairInput i j) := by
      rw [inG,inG,inG,sup_snoc,sup_in,eH]; rfl
    have g1 := monotone_eval G (belowLast (belowX i j) h1)
    have g2 := monotone_eval G (belowLast (belowY i j) h2)
    by_cases eG : formEval G (inG H (pairInput i j)) = (C H G i || C H G j)
    · have se' : supB (inQ H G (singleInput i)) (inQ H G (singleInput j)) = inQ H G (pairInput i j) := by
        rw [inQ,inQ,inQ,sup_snoc,se,eG]; rfl
      obtain ⟨c,hc,ep⟩ := rsep (baseQ a b G) (fun k => inQ H G (singleInput k)) Q i j
        (bq_ok iy) (bq_ok jy) (se' ▸ hi) loi loj
      exact ⟨c,List.mem_append_right _ hc,ep⟩
    · change (C H G i = true → formEval G (inG H (pairInput i j)) = true) at g1
      change (C H G j = true → formEval G (inG H (pairInput i j)) = true) at g2
      have vals : C H G i = false ∧ C H G j = false ∧ formEval G (inG H (pairInput i j)) = true := by
        exact gap _ _ _ g1 g2 eG
      have bb : b=false := by cases b <;> simp_all [active]
      obtain ⟨c,hc,ep⟩ := rsep (baseG a) (fun k => inG H (singleInput k)) G i j
        (bg_ok iy) (bg_ok jy) (se ▸ vals.2.2) vals.1 vals.2.1
      have mem : c ∈ cg a b H G := by simpa [cg,bb] using hc
      exact ⟨c,List.mem_append_left _ (List.mem_append_right _ mem),ep⟩
  · change (B H i = true → formEval H (pairInput i j) = true) at h1
    change (B H j = true → formEval H (pairInput i j) = true) at h2
    have vals : B H i = false ∧ B H j = false ∧ formEval H (pairInput i j) = true := by
      exact gap _ _ _ h1 h2 eH
    have aa : a=false := by cases a <;> simp_all [active]
    obtain ⟨c,hc,ep⟩ := rsep bot singleInput H i j (belowBot _) (belowBot _)
      (sup_in i j ▸ vals.2.2) vals.1 vals.2.1
    have mem : c ∈ ch a H := by simpa [ch,aa] using hc
    exact ⟨c,List.mem_append_left _ (List.mem_append_left _ mem),ep⟩
end ThresholdSeven
namespace ThresholdSeven
open ThresholdSixBound ThresholdSixBound.Leaf5459 ThresholdSixBound.OneShare
abbrev hraw (H : Formula 7) (i : V) := formOcc H i
abbrev graw (G : Formula 8) (i : V) := formOcc G i.castSucc
abbrev qraw (Q : Formula 9) (i : V) := formOcc Q i.castSucc.castSucc
abbrev gh (G : Formula 8) := formOcc G (Fin.last 7)
abbrev qh (Q : Formula 9) := formOcc Q (Fin.last 7).castSucc
abbrev qg (Q : Formula 9) := formOcc Q (Fin.last 8)
theorem chargeH (H : Formula 7) (i : V) :
    width (ch false H) i + (B H i).toNat ≤ hraw H i := by
  have h := rcharge bot singleInput H i (belowBot _)
  rw [val0] at h
  change width (rcuts bot singleInput H) i + (formEval H (singleInput i)).toNat ≤
    wOcc (singleInput i) H at h
  simpa [ch,B,wVar] using h
theorem chargeG {a b : Bool} {H : Formula 7} {G : Formula 8} {i : V} (iy : active a b H G i) :
    width (cg a false H G) i + (delta (formEval G (baseG a)) (C H G i)).toNat ≤
      graw G i + (delta a (B H i)).toNat * gh G := by
  have h := rcharge (baseG a) (fun k => inG H (singleInput k)) G i (bg_ok iy)
  have e : (fun j => delta (baseG a j) (inG H (singleInput i) j)) =
      Fin.snoc (singleInput i) (delta a (B H i)) := by
    exact delta_snoc bot (singleInput i) a (B H i)
  rw [e,ws1] at h
  exact h
theorem chargeQ {a b : Bool} {H : Formula 7} {G : Formula 8} (Q : Formula 9) {i : V}
    (iy : active a b H G i) :
    width (cq a b H G Q) i ≤ qraw Q i + (delta a (B H i)).toNat * qh Q +
      (delta (baseC a b G) (C H G i)).toNat * qg Q := by
  have h := rcharge (baseQ a b G) (fun k => inQ H G (singleInput k)) Q i (bq_ok iy)
  have e : (fun j => delta (baseQ a b G j) (inQ H G (singleInput i) j)) =
      Fin.snoc (Fin.snoc (singleInput i) (delta a (B H i))) (delta (baseC a b G) (C H G i)) := by
    unfold baseQ inQ
    rw [delta_snoc]
    have eg : (fun j => delta (baseG a j) (inG H (singleInput i) j)) =
        Fin.snoc (singleInput i) (delta a (B H i)) := delta_snoc bot (singleInput i) a (B H i)
    rw [eg];rfl
  rw [e,ws2] at h
  exact (Nat.le_add_right ..).trans h
theorem gzero (G : Formula 8) : formEval G (baseG false) = false := by
  have e : baseG false = bot := by decide
  rw [e,val0]
theorem ch_true (H : Formula 7) (i : V) : width (ch true H) i = 0 := rfl
theorem cg_true (a : Bool) (H : Formula 7) (G : Formula 8) (i : V) : width (cg a true H G) i = 0 := rfl
theorem widthLimits (H : Formula 7) (G : Formula 8) (Q : Formula 9)
    (cost : ∀ i, hraw H i + graw G i + qraw Q i ≤ 2)
    (costH : gh G + qh Q ≤ 2) (costG : qg Q ≤ 2) :
    ∀ a b i, active a b H G i → width (layers a b H G Q) i ≤
      (if a || b then 1 else 2) + (if !a then (B H i).toNat else 0) +
        (if !b then (C H G i).toNat else 0) := by
  intro a b i iy
  have raw := cost i
  have h := chargeH H i
  have g := chargeG iy
  have q := chargeQ Q iy
  have yn : active false false H G i := by simp [active]
  have g0 := chargeG yn
  rw [gzero] at g0
  have s1 := iy.1
  have s2 := iy.2
  change _ + _ ≤ _ at h
  simp only [layers,width,List.countP_append]
  change width (ch a H) i + width (cg a b H G) i + width (cq a b H G Q) i ≤ _
  cases a <;> cases b <;> cases eH : B H i <;> cases eG : C H G i <;>
    cases gbase : formEval G (baseG true) <;>
    simp only [eH,eG,baseC,gzero,gbase,ch_true,cg_true,Bool.false_or,Bool.or_true,Bool.true_or,delta,ite_true,ite_false,
      Bool.toNat_false,Bool.toNat_true,Nat.zero_mul,Nat.one_mul,Bool.not_false,Bool.not_true,
      Bool.false_eq_true,Bool.true_eq_false,Nat.add_zero,Nat.zero_add] at h g q g0 s1 s2 ⊢
  all_goals first | exact False.elim (s1 trivial) | exact False.elim (s2 trivial) | omega
end ThresholdSeven
namespace ThresholdSeven
open ThresholdSixBound ThresholdSixBound.Leaf5459 ThresholdSixBound.OneShare
def mass (a b p q : Bool) : Nat :=
  match a,b with
  | false,false => (if p then 1 else 2) * (if q then 1 else 2)
  | true,false => if p then (if q then 1 else 2) else 0
  | false,true => if q then (if p then 1 else 2) else 0
  | true,true => if p && q then 1 else 0
def room (a b : Bool) : Nat := match a,b with
  | false,false => 16
  | true,true => 2
  | _,_ => 4
theorem fitted : ∀ a b p q : Bool, (a = true → p = true) → (b = true → q = true) →
    2^((if a || b then 1 else 2) + (if !a then p.toNat else 0) +
      (if !b then q.toNat else 0)) * mass a b p q ≤ room a b := by decide
theorem total_mass : ∀ p q : Bool,
    mass false false p q + mass false true p q + mass true false p q + mass true true p q = 4 := by decide
theorem inactive : ∀ a b p q : Bool, ¬ ((a=true → p=true) ∧ (b=true → q=true)) →
    mass a b p q = 0 := by decide
theorem twoShare (H : Formula 7) (G : Formula 8) (Q : Formula 9)
    (cost : ∀ i, hraw H i + graw G i + qraw Q i ≤ 2)
    (costH : gh G + qh Q ≤ 2) (costG : qg Q ≤ 2)
    (lo : ∀ i : V, formEval Q (inQ H G (singleInput i)) = false)
    (hi : ∀ i j : V, i≠j → formEval Q (inQ H G (pairInput i j)) = true) : False := by
  classical
  let f (a b : Bool) (i : V) := mass a b (B H i) (C H G i)
  have hb (a b : Bool) : (Finset.univ.sum (f a b)) ≤ room a b := by
    let I := Finset.univ.filter (active a b H G)
    have S : Finset.univ.sum (f a b) = I.sum (f a b) := by
      symm
      apply Finset.sum_subset (Finset.subset_univ I)
      intro x _ hx
      have ex : ¬ active a b H G x := by simpa [I] using hx
      exact inactive a b (B H x) (C H G x) ex
    rw [S]
    apply pack I (layers a b H G Q) (room a b)
    · intro i h
      have h' := (Finset.mem_filter.mp h).2
      have w := widthLimits H G Q cost costH costG a b i h'
      exact (Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by decide : 0<2) w)).trans
        (fitted a b _ _ h'.1 h'.2)
    · intro i h j h' hn
      exact rootSep a b H G Q i j (Finset.mem_filter.mp h).2 (Finset.mem_filter.mp h').2
        (lo i) (lo j) (hi i j hn)
  have add : Finset.univ.sum (f false false) + Finset.univ.sum (f false true) +
      Finset.univ.sum (f true false) + Finset.univ.sum (f true true) = 28 := by
    simp only [← Finset.sum_add_distrib]
    calc
      _ = Finset.univ.sum (fun _ : V => (4:Nat)) := Finset.sum_congr rfl (fun i _ => total_mass _ _)
      _ = 28 := by decide
  have h00 := hb false false
  have h01 := hb false true
  have h10 := hb true false
  have h11 := hb true true
  simp only [room] at h00 h01 h10 h11
  omega
end ThresholdSeven
namespace ThresholdSixBound.SevenExtract
open Leaf5459
abbrev Fn := Seven.BF
abbrev GateRun (ys : List Fn) (s : ℕ) (ws : List Fn) :=
  TR Seven.gF (fun k _ _ => MonoA k) ys s ws
def ev {n : ℕ} (q : (Fin 7 → Bool) → Fin n → Bool) (t : Formula n) : Fn :=
  fun x => formEval t (q x)
def occ {n : ℕ} (ts : List (Formula n)) (i : Fin n) : ℕ := (ts.map (fun t => formOcc t i)).sum
def disjoinForest {n : ℕ} : List (Formula n) → Formula n
  | [] => .nil
  | t :: ts => .node (.inr false) t (disjoinForest ts)
def leaf {n : ℕ} (i : Fin n) : Formula n := .node (.inl i) .nil .nil
def graft {n : ℕ} (k : Fin 4) (a b : Formula n) : Formula n :=
  .node (.inr (decide (k = 0))) a b
theorem graft_ev {n} (q : (Fin 7 → Bool) → Fin n → Bool) (k : Fin 4) (hk : MonoA k)
    (a b : Formula n) : ev q (graft k a b) = Seven.gF k (ev q a) (ev q b) := by
  rcases mono_cases k hk with rfl | rfl <;> rfl
theorem occ_graft {n} (k : Fin 4) (a b : Formula n) (i : Fin n) :
    formOcc (graft k a b) i = formOcc a i + formOcc b i := rfl
theorem permOcc {n} {a b : List (Formula n)} (h : a.Perm b) (i : Fin n) :
    occ a i = occ b i := (h.map _).sum_eq
theorem consOcc {n} (a : Formula n) (b : List (Formula n)) (i : Fin n) :
    occ (a::b) i = formOcc a i + occ b i := rfl
theorem combineOcc {n} {ts zs us : List (Formula n)} {a b : Formula n}
    (h1 : ts.Perm (a::zs)) (h2 : zs.Perm (b::us)) (k : Fin 4) (i : Fin n) :
    occ ts i = occ (graft k a b :: us) i := by
  rw [permOcc h1,consOcc,permOcc h2,consOcc,consOcc,occ_graft]
  omega
theorem overEval {n} (ts : List (Formula n)) (q : (Fin 7 → Bool) → Fin n → Bool)
    (x : Fin 7 → Bool) : formEval (disjoinForest ts) (q x) = (ts.map (ev q)).any (fun f => f x) := by
  induction ts with
  | nil => rfl
  | cons a ts ih => simp [disjoinForest,formEval,List.any_cons,ev,ih]
theorem overOcc {n} (ts : List (Formula n)) (i : Fin n) : formOcc (disjoinForest ts) i = occ ts i := by
  induction ts with
  | nil => rfl
  | cons a ts ih => simp [disjoinForest,formOcc,consOcc,ih]
theorem permAny {xs ys : List Fn} (h : xs.Perm ys) (x : Fin 7 → Bool) :
    xs.any (fun f => f x) = ys.any (fun f => f x) := by
  rw [Bool.eq_iff_iff]
  simp only [List.any_eq_true]
  exact ⟨fun ⟨a,ha,hv⟩ => ⟨a,h.mem_iff.mp ha,hv⟩,
         fun ⟨a,ha,hv⟩ => ⟨a,h.mem_iff.mpr ha,hv⟩⟩
theorem plain {n} (q : (Fin 7 → Bool) → Fin n → Bool) {ys ws : List Fn} {s : ℕ}
    (h : GateRun ys s ws) :
    ∀ ts : List (Formula n), (ts.map (ev q)).Perm ws → ws.length = s + ys.length →
      ∃ t : Formula n, (∀ x, ev q t x = ys.any (fun f => f x)) ∧ ∀ i, formOcc t i = occ ts i := by
  refine TR.ind (P := fun s ws => ∀ ts : List (Formula n), (ts.map (ev q)).Perm ws →
    ws.length = s + ys.length → ∃ t : Formula n,
    (∀ x, ev q t x = ys.any (fun f => f x)) ∧ ∀ i, formOcc t i = occ ts i) h ?_ ?_ ?_
  · intro ts hp _
    exact ⟨disjoinForest ts,fun x => (overEval ts q x).trans (permAny hp x),overOcc ts⟩
  · intro s xs zs hp _ ih ts hm hl
    exact ih ts (hm.trans hp.symm) (by rw [hp.length_eq]; exact hl)
  · intro s a b r k u hk hr ih ts hm hl
    have hn := TR.len hr
    simp only [List.length_append,List.length_replicate,List.length_cons] at hn hl
    obtain rfl : u = 0 := by omega
    obtain ⟨ta,t₁,hp1,rfl,h1⟩ := map_perm_cons (ev q) hm
    obtain ⟨tb,t₂,hp2,rfl,h2⟩ := map_perm_cons (ev q) h1
    obtain ⟨t,ht,ho⟩ := ih (graft k ta tb :: t₂)
      (by rw [List.map_cons,graft_ev q k hk]; exact h2.cons _)
      (by simp only [List.length_append,List.length_replicate]; omega)
    exact ⟨t,ht,fun i => (ho i).trans (combineOcc hp1 hp2 k i).symm⟩
def lift {n : ℕ} :  Formula n → Formula (n+1)
  | .nil => .nil
  | .node (.inl i) _ _ => leaf i.castSucc
  | .node (.inr b) l r => .node (.inr b) (lift l) (lift r)
theorem liftEval {n : ℕ} (t : Formula n) (x : Fin n → Bool) (v : Bool) :
    formEval (lift t) (Fin.snoc x v) = formEval t x := by
  induction t with
  | nil => rfl
  | node a l r hl hr =>
    cases a with
    | inl i =>
      change (Fin.snoc x v : Fin (n+1) → Bool) i.castSucc = x i
      rw [Fin.snoc_castSucc]
    | inr b => cases b <;> simp [lift,formEval,hl,hr]
theorem liftOcc {n : ℕ} (t : Formula n) (i : Fin n) :
    formOcc (lift t) i.castSucc = formOcc t i := by
  induction t with
  | nil => rfl
  | node a l r hl hr =>
    cases a with
    | inl k => simp [lift,leaf,formOcc]
    | inr b => simp [lift,formOcc,hl,hr]
theorem liftLast {n : ℕ} (t : Formula n) : formOcc (lift t) (Fin.last n) = 0 := by
  induction t with
  | nil => rfl
  | node a l r hl hr =>
    cases a with
    | inl k => simp only [lift,leaf,formOcc,if_neg (Fin.castSucc_ne_last k)]
    | inr b => simp only [lift,formOcc,hl,hr,Nat.zero_add]
theorem occLift {n : ℕ} (ts : List (Formula n)) (i : Fin n) : occ (ts.map lift) i.castSucc = occ ts i := by
  induction ts with
  | nil => rfl
  | cons a ts ih => simp only [List.map_cons,consOcc,liftOcc,ih]
theorem occLiftLast {n : ℕ} (ts : List (Formula n)) : occ (ts.map lift) (Fin.last n) = 0 := by
  induction ts with
  | nil => rfl
  | cons a ts ih => simp only [List.map_cons,consOcc,liftLast,ih,Nat.zero_add]
def extended {n : ℕ} (q : (Fin 7 → Bool) → Fin n → Bool) (h : Formula n)
    (x : Fin 7 → Bool) : Fin (n+1) → Bool := Fin.snoc (q x) (ev q h x)
theorem mapLift {n : ℕ} (q : (Fin 7 → Bool) → Fin n → Bool) (ts : List (Formula n)) (h : Formula n) :
    (ts.map lift).map (ev (extended q h)) = ts.map (ev q) := by
  induction ts with
  | nil => rfl
  | cons a ts ih => simp only [List.map_cons,ih]; rw [show ev (extended q h) (lift a) = ev q a from funext (fun x => liftEval a (q x) _)]
def Shared {n : ℕ} (q : (Fin 7 → Bool) → Fin n → Bool) (ys : List Fn) (ts : List (Formula n)) : Prop :=
  ∃ H : Formula n, ∃ P : Formula (n+1), (∀ x, formEval P (extended q H x) = ys.any (fun f => f x)) ∧
    (∀ i : Fin n, formOcc P i.castSucc + formOcc H i = occ ts i) ∧ formOcc P (Fin.last n) ≤ 2
theorem oneShare {n : ℕ} (q : (Fin 7 → Bool) → Fin n → Bool) {ys ws : List Fn} {s : ℕ} (h : GateRun ys s ws) :
    ∀ ts : List (Formula n), (ts.map (ev q)).Perm ws → s + ys.length ≤ ws.length + 1 → Shared q ys ts := by
  refine TR.ind (P := fun s ws => ∀ ts : List (Formula n), (ts.map (ev q)).Perm ws →
    s + ys.length ≤ ws.length + 1 → Shared q ys ts) h ?_ ?_ ?_
  · intro ts hp _
    refine ⟨.nil,lift (disjoinForest ts),?_,?_,by rw [liftLast]; decide⟩
    · intro x
      exact (liftEval (disjoinForest ts) (q x) _).trans ((overEval ts q x).trans (permAny hp x))
    · intro i
      simp [liftOcc,formOcc,overOcc]
  · intro s xs zs hp _ ih ts hm hl
    exact ih ts (hm.trans hp.symm) (by rw [hp.length_eq]; exact hl)
  · intro s a b r k u hk hr ih ts hm hl
    have hn := TR.len hr
    simp only [List.length_append,List.length_replicate,List.length_cons] at hn hl
    obtain ⟨ta,t₁,hp1,rfl,h1⟩ := map_perm_cons (ev q) hm
    obtain ⟨tb,t₂,hp2,rfl,h2⟩ := map_perm_cons (ev q) h1
    let H := graft k ta tb
    have hH : ev q H = Seven.gF k (ev q ta) (ev q tb) := graft_ev q k hk ta tb
    have hu : u = 0 ∨ u = 1 := by omega
    rcases hu with rfl | rfl
    · obtain ⟨K,P,he,ho,hf⟩ := ih (H :: t₂)
        (by rw [List.map_cons,hH]; exact h2.cons _)
        (by simp only [List.length_append,List.length_replicate]; omega)
      exact ⟨K,P,he,fun i => (ho i).trans (combineOcc hp1 hp2 k i).symm,hf⟩
    · let leafZ := leaf (Fin.last n)
      let ts' := leafZ :: leafZ :: t₂.map lift
      have hez : ev (extended q H) leafZ = ev q H := by
        funext x
        change (Fin.snoc (q x) (ev q H x) : Fin (n+1) → Bool) (Fin.last n) = _
        rw [Fin.snoc_last]
      have hmap : (ts'.map (ev (extended q H))).Perm
          (List.replicate (1+1) (Seven.gF k (ev q ta) (ev q tb)) ++ r) := by
        change (ev (extended q H) leafZ :: ev (extended q H) leafZ :: (t₂.map lift).map (ev (extended q H))).Perm _
        rw [hez,hH,mapLift]
        exact (h2.cons _).cons _
      obtain ⟨P,he,ho⟩ := plain (extended q H) hr ts' hmap (by
        simp only [List.length_append,List.length_replicate]; omega)
      refine ⟨H,P,he,?_,?_⟩
      · intro i
        rw [ho,combineOcc hp1 hp2 k i]
        simp only [ts',leafZ,leaf,consOcc,formOcc,H,if_neg (Ne.symm (Fin.castSucc_ne_last i)),Nat.zero_add]
        rw [occLift t₂ i]
        omega
      · rw [ho]; simp only [ts',leafZ,leaf,consOcc,formOcc,ite_true]; rw [occLiftLast t₂]
end ThresholdSixBound.SevenExtract
namespace ThresholdSixBound.SevenExtract
open Leaf5459
open ThresholdSeven
def Shared2 (ys : List Fn) (ts : List (Formula 7)) := ∃ (H : Formula 7) (G : Formula 8) (Q : Formula 9),
  (∀ x, formEval Q (inQ H G x) = ys.any (fun f => f x)) ∧
  (∀ i : Fin 7, hraw H i + graw G i + qraw Q i = occ ts i) ∧ gh G + qh Q ≤ 2 ∧ ThresholdSeven.qg Q ≤ 2
theorem extractForest {ys ws : List Fn} {s : ℕ} (h : GateRun ys s ws) :
    ∀ ts : List (Formula 7), (ts.map formEval).Perm ws → s + ys.length ≤ ws.length + 2 → Shared2 ys ts := by
  refine TR.ind (P := fun s ws => ∀ ts : List (Formula 7), (ts.map formEval).Perm ws →
    s + ys.length ≤ ws.length + 2 → Shared2 ys ts) h ?_ ?_ ?_
  · intro ts hp _
    refine ⟨.nil,.nil,lift (lift (disjoinForest ts)),?_,?_,?_,?_⟩
    · intro x
      exact (liftEval _ (inG .nil x) _).trans ((liftEval _ x _).trans ((overEval ts id x).trans (permAny hp x)))
    · intro i
      simp [hraw,graw,qraw,liftOcc,formOcc,overOcc]
    · simp only [gh,qh,formOcc,liftOcc,liftLast]; decide
    · simp only [ThresholdSeven.qg,liftLast]; decide
  · intro s xs zs hp _ ih ts hm hl
    exact ih ts (hm.trans hp.symm) (by rw [hp.length_eq]; exact hl)
  · intro s a b r k u hk hr ih ts hm hl
    have hn := TR.len hr
    simp only [List.length_append,List.length_replicate,List.length_cons] at hn hl
    obtain ⟨ta,t₁,hp1,rfl,h1⟩ := map_perm_cons formEval hm
    obtain ⟨tb,t₂,hp2,rfl,h2⟩ := map_perm_cons formEval h1
    let H := graft k ta tb
    have hH : formEval H = Seven.gF k (formEval ta) (formEval tb) := graft_ev id k hk ta tb
    have hu : u = 0 ∨ u = 1 ∨ u = 2 := by omega
    rcases hu with rfl | rfl | rfl
    · obtain ⟨H',G,Q,he,ho,hb,hc⟩ := ih (H :: t₂)
        (by rw [List.map_cons,hH]; exact h2.cons _)
        (by simp only [List.length_append,List.length_replicate]; omega)
      exact ⟨H',G,Q,he,fun i => (ho i).trans (combineOcc hp1 hp2 k i).symm,hb,hc⟩
    · let z := leaf (Fin.last 7)
      let ts' := z :: z :: t₂.map lift
      have ez : ev (extended id H) z = formEval H := by
        funext x
        change (Fin.snoc x (formEval H x) : Fin 8 → Bool) (Fin.last 7) = _
        rw [Fin.snoc_last]
      have hm' : (ts'.map (ev (extended id H))).Perm
          (List.replicate (1+1) (Seven.gF k (formEval ta) (formEval tb)) ++ r) := by
        change (ev (extended id H) z :: ev (extended id H) z :: (t₂.map lift).map (ev (extended id H))).Perm _
        rw [ez,hH,mapLift]
        exact (h2.cons _).cons _
      obtain ⟨G,Q,he,ho,hg⟩ := oneShare (extended id H) hr ts' hm' (by
        simp only [List.length_append,List.length_replicate]; omega)
      refine ⟨H,G,Q,he,?_,?_,hg⟩
      · intro i
        have u := ho i.castSucc
        rw [combineOcc hp1 hp2 k i,consOcc]
        simp only [ts',z,leaf,consOcc,formOcc,if_neg (Ne.symm (Fin.castSucc_ne_last i)),Nat.zero_add,occLift] at u
        change formOcc H i + formOcc G i.castSucc + formOcc Q i.castSucc.castSucc = formOcc H i + occ t₂ i
        omega
      · have u := ho (Fin.last 7)
        simp only [ts',z,leaf,consOcc,formOcc,ite_true,occLiftLast] at u
        change formOcc G (Fin.last 7) + formOcc Q (Fin.last 7).castSucc ≤ 2
        omega
    · let G : Formula 8 := leaf (Fin.last 7)
      let zH : Formula 9 := leaf (Fin.last 7).castSucc
      let zG : Formula 9 := leaf (Fin.last 8)
      let ts' := zG :: zG :: zH :: (t₂.map lift).map lift
      let enc := extended (extended id H) G
      have gval (x : Fin 7 → Bool) : formEval G (extended id H x) = formEval H x := by
        change (Fin.snoc x (formEval H x) : Fin 8 → Bool) (Fin.last 7) = _
        rw [Fin.snoc_last]
      have ezh : ev enc zH = formEval H := by
        funext x
        change (Fin.snoc (extended id H x) (ev (extended id H) G x) : Fin 9 → Bool) (Fin.last 7).castSucc = _
        rw [Fin.snoc_castSucc]
        exact gval x
      have ezg : ev enc zG = formEval H := by
        funext x
        change (Fin.snoc (extended id H x) (ev (extended id H) G x) : Fin 9 → Bool) (Fin.last 8) = _
        rw [Fin.snoc_last]
        exact gval x
      have hm' : (ts'.map (ev enc)).Perm
          (List.replicate (2+1) (Seven.gF k (formEval ta) (formEval tb)) ++ r) := by
        change (ev enc zG :: ev enc zG :: ev enc zH :: ((t₂.map lift).map lift).map (ev enc)).Perm _
        rw [ezh,ezg,hH]
        unfold enc
        rw [mapLift,mapLift]
        exact ((h2.cons _).cons _).cons _
      obtain ⟨Q,he,ho⟩ := plain enc hr ts' hm' (by
        simp only [List.length_append,List.length_replicate]; omega)
      refine ⟨H,G,Q,he,?_,?_,?_⟩
      · intro i
        rw [combineOcc hp1 hp2 k i,consOcc]
        have no1 : (Fin.last 7 : Fin 8) ≠ i.castSucc := Ne.symm (Fin.castSucc_ne_last i)
        have no2 : (Fin.last 8 : Fin 9) ≠ i.castSucc.castSucc := Ne.symm (Fin.castSucc_ne_last i.castSucc)
        have no3 : (Fin.last 7).castSucc ≠ i.castSucc.castSucc := fun h => no1 (Fin.castSucc_inj.mp h)
        simp only [hraw,graw,qraw,ho,ts',zH,zG,G,leaf,consOcc,formOcc,occLift,
          if_neg no1,if_neg no2,if_neg no3,Nat.zero_add,Nat.add_zero,H]
      · have non : (Fin.last 8 : Fin 9) ≠ (Fin.last 7).castSucc := Ne.symm (Fin.castSucc_ne_last _)
        simp only [gh,qh,G,zH,zG,leaf,ts',consOcc,formOcc,ho,occLift,occLiftLast,
          ite_true,if_neg non,Nat.add_zero,Nat.zero_add]; decide
      · have non : (Fin.last 7).castSucc ≠ (Fin.last 8 : Fin 9) := Fin.castSucc_ne_last _
        simp only [ThresholdSeven.qg,zH,zG,leaf,ts',consOcc,formOcc,ho,occLiftLast,
          ite_true,if_neg non,Nat.add_zero,Nat.zero_add]; decide
theorem inputOcc (idx : List (Fin 7)) (i : Fin 7) : occ (idx.map leaf) i = idx.count i := by
  induction idx with
  | nil => rfl
  | cons j js ih => simp [consOcc,leaf,formOcc,List.count_cons,ih]; split_ifs <;> omega
theorem extract {ys : List Fn} {s} {idx : List (Fin 7)} (h : GateRun ys s (idx.map Seven.var))
    (hc : s + ys.length ≤ idx.length + 2) (hi : ∀ i, idx.count i ≤ 2) :
    ∃ (H : Formula 7) (G : Formula 8) (Q : Formula 9),
      (∀ x, formEval Q (inQ H G x) = ys.any (fun f => f x)) ∧
      (∀ i, hraw H i + graw G i + qraw Q i ≤ 2) ∧ gh G + qh Q ≤ 2 ∧ ThresholdSeven.qg Q ≤ 2 := by
  have hm : ((idx.map leaf).map formEval).Perm (idx.map Seven.var) := by
    rw [List.map_map]; exact List.Perm.refl _
  obtain ⟨H,G,Q,he,ho,hg,hq⟩ := extractForest h (idx.map leaf) hm (by simpa using hc)
  exact ⟨H,G,Q,he,fun i => (ho i).le.trans ((inputOcc idx i) ▸ hi i),hg,hq⟩
end ThresholdSixBound.SevenExtract

namespace ThresholdSixBound.Seven
open Leaf5459
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
abbrev MR (ys : List BF) (s : ℕ) (ws : List BF) : Prop := TR gF (fun k _ _ => MonoA k) ys s ws
def outF (ys : List BF) : BF := fun x => ys.any fun y => y x
def otop (x : Fin 7) : BF := fun p => decide (∃ i, i ≠ x ∧ p i = true)
theorem top_elim (O : BF) :
    ∀ (m : ℕ) (S : BF → Prop) (F : BF), (∀ w, S w → ∀ p, w p = true → O p = true) → F ≠ O →
      UC gF MonoA m (fun w => w = O ∨ S w) F → UC gF MonoA m S F
  | 0, S, F, _, hF, hu => by
    rcases hu with h | h
    · exact absurd h hF
    · exact h
  | m + 1, S, F, hS, hF, hu => by
    rcases hu with hu | ⟨k, a, b, hk, ha, hb, hu⟩
    · exact Or.inl (top_elim O m S F hS hF hu)
    · have hle : ∀ w, (w = O ∨ S w) → ∀ p, w p = true → O p = true := by
        rintro w (rfl | hw) p hp
        · exact hp
        · exact hS w hw p hp
      have free : (gF k a b = O ∨ S (gF k a b)) → UC gF MonoA (m + 1) S F := by
        intro hg
        refine Or.inl (top_elim O m S F hS hF (UC_monoS gF MonoA m _ _ F ?_ hu))
        rintro w (rfl | hw)
        · exact hg
        · exact hw
      by_cases hao : a = O
      · subst hao
        apply free
        rcases mono_cases k hk with rfl | rfl
        · have : gF 0 a b = b := by
            rw [gF_and]
            funext p
            cases hbp : b p
            · simp
            · simp [hle b hb p hbp]
          rw [this]; exact hb
        · have : gF 1 a b = a := by
            rw [gF_or]
            funext p
            cases hbp : b p
            · simp
            · simp [hle b hb p hbp]
          rw [this]; exact Or.inl rfl
      by_cases hbo : b = O
      · subst hbo
        apply free
        rcases mono_cases k hk with rfl | rfl
        · have : gF 0 a b = a := by
            rw [gF_and]
            funext p
            cases hap : a p
            · simp
            · simp [hle a ha p hap]
          rw [this]; exact ha
        · have : gF 1 a b = b := by
            rw [gF_or]
            funext p
            cases hap : a p
            · simp
            · simp [hle a ha p hap]
          rw [this]; exact Or.inl rfl
      have ha' : S a := ha.resolve_left hao
      have hb' : S b := hb.resolve_left hbo
      refine UC_gate k a b hk ha' hb' (top_elim O m _ F ?_ hF (UC_monoS gF MonoA m _ _ F ?_ hu))
      · rintro w (rfl | hw) p hp
        · rcases mono_cases k hk with rfl | rfl
          · rw [gF_and] at hp
            simp only [Bool.and_eq_true] at hp
            exact hS a ha' p hp.1
          · rw [gF_or] at hp
            simp only [Bool.or_eq_true] at hp
            rcases hp with hp | hp
            · exact hS a ha' p hp
            · exact hS b hb' p hp
        · exact hS w hw p hp
      · rintro w (rfl | rfl | hw)
        · exact Or.inr (Or.inl rfl)
        · exact Or.inl rfl
        · exact Or.inr (Or.inr hw)
theorem outF_true (ys : List BF) (p : Fin 7 → Bool) :
    outF ys p = true ↔ ∃ y ∈ ys, y p = true := by
  simp [outF]
theorem outF_congr (ys : List BF) (p p' : Fin 7 → Bool) (h : ∀ y ∈ ys, y p = y p') :
    outF ys p = outF ys p' := by
  rw [Bool.eq_iff_iff, outF_true, outF_true]
  constructor
  · rintro ⟨y, hy, hp⟩; exact ⟨y, hy, by rw [← h y hy]; exact hp⟩
  · rintro ⟨y, hy, hp⟩; exact ⟨y, hy, by rw [h y hy]; exact hp⟩
theorem or_chain : ∀ (ys : List BF) (y : BF), MR [outF (y :: ys)] ys.length (y :: ys)
  | [], y => by
    have : outF [y] = y := funext fun x => by simp [outF]
    rw [this]
    exact TR.done
  | y2 :: rest, y => by
    have h := or_chain rest (gF 1 y y2)
    have e : outF (gF 1 y y2 :: rest) = outF (y :: y2 :: rest) :=
      funext fun x => by simp [outF, gF_or, Bool.or_assoc]
    rw [e] at h
    exact TR.step (r := rest) 1 0 (by simp [MonoA]) h
theorem complete_run (y0 : BF) (yt : List BF) {s : ℕ} {ws : List BF} (h : MR (y0 :: yt) s ws) :
    MR [outF (y0 :: yt)] (s + yt.length) ws := by
  refine TR.ind (P := fun s ws => MR [outF (y0 :: yt)] (s + yt.length) ws) h ?_ ?_ ?_
  · rw [Nat.zero_add]; exact or_chain yt y0
  · intro s xs zs hp _ ih; exact TR.perm hp ih
  · intro s a b r k u hc _ ih
    have e : s + 1 + yt.length = s + yt.length + 1 := by omega
    rw [e]
    exact TR.step k u hc ih
theorem frame (h0 : BF) {ys : List BF} {s : ℕ} {ws : List BF} (h : MR ys s ws) :
    MR (h0 :: ys) s (h0 :: ws) := by
  refine TR.ind (P := fun s ws => MR (h0 :: ys) s (h0 :: ws)) h TR.done ?_ ?_
  · intro s xs zs hp _ ih; exact TR.perm (hp.cons h0) ih
  · intro s a b r k u hc _ ih
    have p1 : (a :: b :: h0 :: r).Perm (h0 :: a :: b :: r) :=
      List.perm_middle (l₁ := [a, b])
    have p2 : (h0 :: (List.replicate (u + 1) (gF k a b) ++ r)).Perm
        (List.replicate (u + 1) (gF k a b) ++ h0 :: r) := List.perm_middle.symm
    exact TR.perm p1 (TR.step k u hc (TR.perm p2 ih))
def XI (x : Fin 7) (w : BF) : Prop := ∀ p b, w (Function.update p x b) = w p
def MonoF (w : BF) : Prop :=
  ∀ p q : Fin 7 → Bool, (∀ i, p i = true → q i = true) → w p = true → w q = true
def InvX (x : Fin 7) (w : BF) : Prop := XI x w ∧ MonoF w ∧ w (fun _ => false) = false
theorem InvX_gate {x : Fin 7} {k : Fin 4} (hk : MonoA k) {a b : BF} (ha : InvX x a)
    (hb : InvX x b) : InvX x (gF k a b) := by
  rcases mono_cases k hk with rfl | rfl
  · refine ⟨fun p v => ?_, fun p q hpq h => ?_, ?_⟩
    · show (a _ && b _) = (a _ && b _)
      rw [ha.1 p v, hb.1 p v]
    · rw [gF_and] at h ⊢
      simp only [Bool.and_eq_true] at h ⊢
      exact ⟨ha.2.1 p q hpq h.1, hb.2.1 p q hpq h.2⟩
    · show (a _ && b _) = false
      rw [ha.2.2]; rfl
  · refine ⟨fun p v => ?_, fun p q hpq h => ?_, ?_⟩
    · show (a _ || b _) = (a _ || b _)
      rw [ha.1 p v, hb.1 p v]
    · rw [gF_or] at h ⊢
      simp only [Bool.or_eq_true] at h ⊢
      exact h.imp (ha.2.1 p q hpq) (hb.2.1 p q hpq)
    · show (a _ || b _) = false
      rw [ha.2.2, hb.2.2]; rfl
theorem InvX_var {x m : Fin 7} (h : m ≠ x) : InvX x (var m) :=
  ⟨fun p v => by simp [var, Function.update_of_ne h], fun p q hpq hp => hpq m hp, rfl⟩
theorem mono_comm {k : Fin 4} (hk : MonoA k) (a b : BF) : gF k a b = gF k b a := by
  rcases mono_cases k hk with rfl | rfl
  · rw [gF_and, gF_and]; funext p; exact Bool.and_comm _ _
  · rw [gF_or, gF_or]; funext p; exact Bool.or_comm _ _
theorem upd_single_true (i x : Fin 7) :
    Function.update (singleInput i) x true = pairInput i x := by
  funext m
  by_cases hm : m = x
  · subst hm; simp [pairInput]
  · simp [singleInput, pairInput, hm]
theorem single_eq_upd (x : Fin 7) :
    singleInput x = Function.update (fun _ => false) x true := by
  funext m
  by_cases hm : m = x
  · subst hm; simp [singleInput]
  · simp [singleInput, hm]
theorem outF_rel (b' : BF) (p : Fin 7 → Bool) (hb : b' p = false) :
    ∀ (ys ys' : List BF), List.Forall₂ (fun w w' => ∀ q, b' q = false → w q = w' q) ys ys' →
      outF ys p = outF ys' p
  | _, _, List.Forall₂.nil => rfl
  | _, _, List.Forall₂.cons h t => by
    have ih := outF_rel b' p hb _ _ t
    simp only [outF, List.any_cons] at ih ⊢
    rw [h p hb, ih]
def SUc (x : Fin 7) (y0 : BF) (yt : List BF) (s : ℕ) (r : List BF) : Prop :=
  ((if otop x ∈ r then 2 else 3) ≤ s + yt.length ∧
    ∀ S : BF → Prop, (∀ w ∈ r, S w) → S (otop x) →
      UC gF MonoA (s + yt.length - (if otop x ∈ r then 2 else 3)) S
        (rst x (outF (y0 :: yt)))) ∨
  ∃ (c : ℕ) (h0 : BF) (ys' : List BF) (s' : ℕ), s = s' + 1 ∧ ys'.length = yt.length + 1 ∧
    ThrL (fun _ => True) (outF (h0 :: ys')) ∧
    MR (h0 :: ys') s' (List.replicate (c + 1) (var x) ++ r)
theorem SU (x : Fin 7) (y0 : BF) (yt : List BF)
    (hF : ThrL (fun _ => True) (outF (y0 :: yt))) :
    ∀ (s : ℕ) (r : List BF), MR (y0 :: yt) s (var x :: r) → (∀ w ∈ r, InvX x w) →
      SUc x y0 yt s r := by
  intro s
  induction s with
  | zero =>
    intro r h _
    exfalso
    have hp := (TR.inv h).1 rfl
    have hm : var x ∈ y0 :: yt := hp.mem_iff.1 (by simp)
    have h1 : outF (y0 :: yt) (singleInput x) = true :=
      (outF_true _ _).2 ⟨var x, hm, by simp [var, singleInput]⟩
    rw [hF.1 x trivial] at h1
    exact Bool.noConfusion h1
  | succ s ih =>
    intro r h hinv
    obtain ⟨k, u, a, b, r₁, hk, hp, hr⟩ := (TR.inv h).2 s rfl
    have consume : ∀ b' : BF, r.Perm (b' :: r₁) → gF k a b = gF k (var x) b' →
        SUc x y0 yt (s + 1) r := by
      intro b' hrp hg
      unfold SUc
      rw [hg] at hr
      have hb' : InvX x b' := hinv b' (hrp.mem_iff.2 (by simp))
      have hr1 : ∀ w ∈ r₁, InvX x w := fun w hw => hinv w (hrp.mem_iff.2 (by simp [hw]))
      have sens : ∀ i, i ≠ x → gF k (var x) b' (pairInput i x) =
          gF k (var x) b' (singleInput i) → False := by
        intro i hi hgg
        have hd := TRF_det hr (pairInput i x) (singleInput i) (by
          intro w hw
          rcases List.mem_append.1 hw with hw | hw
          · rw [List.eq_of_mem_replicate hw]; exact hgg
          · rw [← upd_single_true]
            exact (hr1 w hw).1 _ _)
        have h2 := outF_congr _ _ _ hd
        rw [hF.1 i trivial, hF.2 i x trivial trivial hi] at h2
        exact Bool.noConfusion h2
      have hbx : ∀ i, i ≠ x → b' (pairInput i x) = b' (singleInput i) := fun i _ => by
        rw [← upd_single_true]; exact hb'.1 _ _
      have hv1 : ∀ i, var x (pairInput i x) = true := fun i => by simp [var, pairInput]
      have hv2 : ∀ i, i ≠ x → var x (singleInput i) = false := fun i hi => by
        simp [var, singleInput, Ne.symm hi]
      rcases mono_cases k hk with rfl | rfl
      · left
        have hone : ∀ i, i ≠ x → b' (singleInput i) = true := by
          intro i hi
          by_contra hc
          have hc' : b' (singleInput i) = false := by simpa using hc
          apply sens i hi
          rw [gF_and]
          show (var x _ && b' _) = (var x _ && b' _)
          rw [hbx i hi, hc', hv2 i hi]; simp
        have hbo : b' = otop x := by
          funext p
          rw [← hb'.1 p false]
          by_cases hex : ∃ i, i ≠ x ∧ p i = true
          · obtain ⟨i, hi, hpi⟩ := hex
            have : otop x p = true := by simp only [otop, decide_eq_true_eq]; exact ⟨i, hi, hpi⟩
            rw [this]
            refine hb'.2.1 (singleInput i) _ ?_ (hone i hi)
            intro m hm
            have : m = i := by simpa [singleInput] using hm
            subst this
            rw [Function.update_of_ne hi]; exact hpi
          · have : otop x p = false := by simp only [otop, decide_eq_false_iff_not]; exact hex
            rw [this]
            have hz : Function.update p x false = fun _ => false := by
              funext m
              by_cases hm : m = x
              · subst hm; simp
              · rw [Function.update_of_ne hm]
                by_contra hc
                exact hex ⟨m, hm, by simpa using hc⟩
            rw [hz]; exact hb'.2.2
        have hmem : otop x ∈ r := hrp.mem_iff.2 (by simp [hbo])
        have hdead : rst x (gF 0 (var x) b') = zF := by
          funext p
          show (var x _ && b' _) = false
          simp [var]
        have hc := complete_run y0 yt hr
        obtain ⟨hd1, hd2⟩ := pot_dead x (thr_rst_ne hF x) hc
        rw [dcount_rep] at hd1 hd2
        simp only [hdead, ite_true] at hd1 hd2
        simp only [hmem, ite_true]
        refine ⟨by omega, fun S hS _ => UC_le (by omega) (hd2 S ?_)⟩
        intro w hw hwz
        rcases List.mem_append.1 hw with hw | hw
        · exact absurd (List.eq_of_mem_replicate hw ▸ hdead) hwz
        · have : rst x w = w := funext fun p => (hr1 w hw).1 p false
          rw [this]
          exact hS w (hrp.mem_iff.2 (by simp [hw]))
      · right
        have hzero : ∀ i, b' (singleInput i) = false := by
          intro i
          by_cases hi : i = x
          · subst hi
            rw [single_eq_upd, hb'.1]; exact hb'.2.2
          · by_contra hc
            have hc' : b' (singleInput i) = true := by simpa using hc
            apply sens i hi
            rw [gF_or]
            show (var x _ || b' _) = (var x _ || b' _)
            rw [hbx i hi, hc', hv1 i]; simp
        have hrel : List.Forall₂ (fun w w' => ∀ q, b' q = false → w q = w' q)
            (List.replicate (u + 1) (gF 1 (var x) b') ++ r₁)
            (List.replicate (u + 1) (var x) ++ r₁) := by
          refine List.rel_append ?_ (List.forall₂_same.2 fun _ _ _ _ => rfl)
          generalize u + 1 = n
          induction n with
          | zero => exact List.Forall₂.nil
          | succ n ihn =>
            refine List.Forall₂.cons (fun q hq => ?_) ihn
            show (var x q || b' q) = var x q
            rw [hq]; simp
        obtain ⟨ys', hy, hrun⟩ := TR.rel (A := MonoA)
          (fun w w' => ∀ q, b' q = false → w q = w' q)
          (fun k a a' b b' ha hb q hq => by
            show zeroGate k (a q) (b q) = zeroGate k (a' q) (b' q)
            rw [ha q hq, hb q hq]) hr _ hrel
        refine ⟨u, b', ys', s, rfl, ?_, ⟨fun i _ => ?_, fun i j _ _ hij => ?_⟩, ?_⟩
        · have := hy.length_eq
          simpa using this.symm
        · have e := outF_rel b' (singleInput i) (hzero i) _ _ hy
          have h3 : outF (b' :: ys') (singleInput i) =
              (b' (singleInput i) || outF ys' (singleInput i)) := by simp [outF]
          rw [h3, hzero i, ← e, hF.1 i trivial]; rfl
        · have h3 : outF (b' :: ys') (pairInput i j) =
              (b' (pairInput i j) || outF ys' (pairInput i j)) := by simp [outF]
          rw [h3]
          cases hbp : b' (pairInput i j)
          · have e := outF_rel b' (pairInput i j) hbp _ _ hy
            rw [← e, hF.2 i j trivial trivial hij]; rfl
          · rfl
        · have p1 : (b' :: (List.replicate (u + 1) (var x) ++ r₁)).Perm
              (List.replicate (u + 1) (var x) ++ r) :=
            List.perm_middle.symm.trans (List.Perm.append_left _ hrp.symm)
          exact TR.perm p1 (frame b' hrun)
    by_cases hax : a = var x
    · subst hax
      exact consume b hp.cons_inv rfl
    by_cases hbx : b = var x
    · subst hbx
      have hp' : (var x :: r).Perm (var x :: a :: r₁) := hp.trans (List.Perm.swap _ _ _)
      exact consume a hp'.cons_inv (mono_comm hk a (var x))
    have hx1 : var x ∈ r₁ := by
      have : var x ∈ a :: b :: r₁ := hp.mem_iff.1 (by simp)
      simp only [List.mem_cons] at this
      rcases this with h1 | h1 | h1
      · exact absurd h1.symm hax
      · exact absurd h1.symm hbx
      · exact h1
    obtain ⟨l₁, l₂, rfl⟩ := List.append_of_mem hx1
    have hr2 : r.Perm (a :: b :: (l₁ ++ l₂)) := by
      have p1 : (a :: b :: (l₁ ++ var x :: l₂)).Perm (var x :: a :: b :: (l₁ ++ l₂)) :=
        List.perm_middle (l₁ := a :: b :: l₁)
      exact (hp.trans p1).cons_inv
    have ha : InvX x a := hinv a (hr2.mem_iff.2 (by simp))
    have hb : InvX x b := hinv b (hr2.mem_iff.2 (by simp))
    have hsub : ∀ w ∈ l₁ ++ l₂, w ∈ r := fun w hw => hr2.mem_iff.2 (by simp [List.mem_append.1 hw])
    have p2 : (List.replicate (u + 1) (gF k a b) ++ (l₁ ++ var x :: l₂)).Perm
        (var x :: (List.replicate (u + 1) (gF k a b) ++ (l₁ ++ l₂))) := by
      rw [← List.append_assoc, ← List.append_assoc]
      exact List.perm_middle
    have hinv2 : ∀ w ∈ List.replicate (u + 1) (gF k a b) ++ (l₁ ++ l₂), InvX x w := by
      intro w hw
      rcases List.mem_append.1 hw with hw | hw
      · rw [List.eq_of_mem_replicate hw]; exact InvX_gate hk ha hb
      · exact hinv w (hsub w hw)
    have hih := ih _ (TR.perm p2 hr) hinv2
    unfold SUc at hih ⊢
    rcases hih with ⟨hA1, hA2⟩ | ⟨c, h0, ys', s', hs', hl, hthr, hrun⟩
    · left
      by_cases hgo : gF k a b = otop x
      · have hm : otop x ∈ List.replicate (u + 1) (gF k a b) ++ (l₁ ++ l₂) := by
          rw [hgo]; simp
        simp only [hm, ite_true] at hA1 hA2
        refine ⟨by split_ifs <;> omega, fun S hS hSo => ?_⟩
        refine UC_le (by split_ifs <;> omega) (hA2 S ?_ hSo)
        intro w hw
        rcases List.mem_append.1 hw with hw | hw
        · rw [List.eq_of_mem_replicate hw, hgo]; exact hSo
        · exact hS w (hsub w hw)
      · have hiff : otop x ∈ List.replicate (u + 1) (gF k a b) ++ (l₁ ++ l₂) → otop x ∈ r := by
          intro hm
          rcases List.mem_append.1 hm with hm | hm
          · exact absurd (List.eq_of_mem_replicate hm).symm hgo
          · exact hsub _ hm
        have hcc : (if otop x ∈ r then 2 else 3) ≤
            (if otop x ∈ List.replicate (u + 1) (gF k a b) ++ (l₁ ++ l₂) then 2 else 3) := by
          by_cases h1 : otop x ∈ List.replicate (u + 1) (gF k a b) ++ (l₁ ++ l₂)
          · simp [h1, hiff h1]
          · simp only [h1, ite_false]; split_ifs <;> omega
        refine ⟨by omega, fun S hS hSo => ?_⟩
        have h1 := hA2 (fun w => w = gF k a b ∨ S w) (by
          intro w hw
          rcases List.mem_append.1 hw with hw | hw
          · exact Or.inl (List.eq_of_mem_replicate hw)
          · exact Or.inr (hS w (hsub w hw))) (Or.inr hSo)
        have h2 := UC_gate k a b hk (hS a (hr2.mem_iff.2 (by simp)))
          (hS b (hr2.mem_iff.2 (by simp))) h1
        exact UC_le (by omega) h2
    · right
      refine ⟨c, h0, ys', s' + 1, by omega, hl, hthr, ?_⟩
      have p3 : (List.replicate (c + 1) (var x) ++ r).Perm
          (a :: b :: (List.replicate (c + 1) (var x) ++ (l₁ ++ l₂))) := by
        refine (List.Perm.append_left _ hr2).trans ?_
        exact List.perm_middle.trans (List.Perm.cons a List.perm_middle)
      have p4 : (List.replicate (c + 1) (var x) ++
          (List.replicate (u + 1) (gF k a b) ++ (l₁ ++ l₂))).Perm
          (List.replicate (u + 1) (gF k a b) ++
            (List.replicate (c + 1) (var x) ++ (l₁ ++ l₂))) :=
        List.perm_append_comm_assoc _ _ _
      subst hs'
      exact TR.perm p3.symm (TR.step k u hk (TR.perm p4 hrun))
theorem vars_list : ∀ (ws : List BF), (∀ w ∈ ws, ∃ i, w = var i) →
    ∃ idx : List (Fin 7), ws = idx.map var
  | [], _ => ⟨[], rfl⟩
  | w :: ws, h => by
    obtain ⟨i, rfl⟩ := h w (by simp)
    obtain ⟨idx, rfl⟩ := vars_list ws fun w hw => h w (by simp [hw])
    exact ⟨i :: idx, rfl⟩
theorem len_counts : ∀ (idx : List (Fin 7)),
    idx.length = idx.count 0 + idx.count 1 + idx.count 2 + idx.count 3 + idx.count 4 + idx.count 5 + idx.count 6
  | [] => rfl
  | j :: idx => by
    have ih := len_counts idx
    fin_cases j <;> simp <;> omega
theorem outF_perm {ys ys' : List BF} (h : ys.Perm ys') (p : Fin 7 → Bool) :
    outF ys p = outF ys' p := h.any_eq
theorem restrict_thr (p : Fin 7) (F : BF) (ht : ThrL (fun _ => True) F) :
    Six.ThrL (fun _ => True) (proj p (rst p F)) := by
  have single : ∀ (p : Fin 7) (j : Fin 6),
      Function.update (p.insertNth false (singleInput j)) p false = singleInput (p.succAbove j) := by
    decide +kernel
  have pair : ∀ (p : Fin 7) (j k : Fin 6),
      Function.update (p.insertNth false (pairInput j k)) p false = pairInput (p.succAbove j) (p.succAbove k) := by
    decide +kernel
  refine ⟨fun j _ => ?_, fun j k _ _ hjk => ?_⟩
  · simpa only [proj,rst,single] using ht.1 (p.succAbove j) trivial
  · simpa only [proj,rst,pair] using ht.2 (p.succAbove j) (p.succAbove k)
      trivial trivial (fun eq => hjk (Fin.succAbove_right_injective eq))
theorem fiveLower (lb : Six.SixLow) (p : Fin 7) (F : BF) (ht : ThrL (fun _ => True) F) {k : Nat}
    (h : UC gF MonoA k (fun w => ∃ j, w = var (p.succAbove j)) (rst p F)) : 13 ≤ k := by
  have mapped := UC_map (G' := Six.gF) (proj p) (fun _ _ _ => rfl)
    _ _ (fun w => ∃ i, w = Six.var i) _
    (by rintro w ⟨i, rfl⟩; exact ⟨i, projVar p i⟩) h
  by_contra he
  exact Six.M6 lb (restrict_thr p F ht) (UC_le (by omega) mapped)
theorem count_le_dead (p : Fin 7) : ∀ idx : List (Fin 7), idx.count p ≤ dcount p (idx.map var)
  | [] => by simp [dcount]
  | j::js => by
    have ih := count_le_dead p js
    by_cases e : j=p
    · subst j
      simp [List.count_cons,dcount_cons,rst_var_self,ih]
    · simp [List.count_cons,e, dcount_cons]
      split <;> omega
theorem atMostTwo (lb : Six.SixLow) (y : BF) (ys : List BF) (idx : List (Fin 7)) (s : Nat)
    (h : MR (y::ys) s (idx.map var)) (hsize : s+ys.length=15)
    (thr : ThrL (fun _ => True) (outF (y::ys))) (p : Fin 7) :
    idx.count p ≤ 2 := by
  have closed := complete_run y ys h
  obtain ⟨h1,h2⟩ := pot_dead p (thr_rst_ne thr p) closed
  have hh := h2 (fun w => ∃ j, w = var (p.succAbove j)) (by
    intro w hw hz
    obtain ⟨i,_,rfl⟩ := List.mem_map.mp hw
    by_cases hi : i=p
    · subst i; exact False.elim (hz (rst_var_self p))
    · obtain ⟨j,hj⟩ := Fin.exists_succAbove_eq hi
      exact ⟨j,by rw [rst_var_ne hi,hj]⟩)
  have bound := fiveLower lb p _ thr hh
  have := count_le_dead p idx
  omega
def ImpossibleShared : Prop := ∀ (y : BF) (ys : List BF) (s : Nat) (idx : List (Fin 7)),
  MR (y::ys) s (idx.map var) → s+(y::ys).length ≤ idx.length+2 → (∀ i, idx.count i ≤ 2) →
  ThrL (fun _ => True) (outF (y::ys)) → False
theorem GS6 (lb : Six.SixLow) (one : ImpossibleShared) : ∀ (s : ℕ) (y0 : BF) (yt : List BF) (ws : List BF), MR (y0 :: yt) s ws →
    (∀ w ∈ ws, ∃ i, w = var i) → s + yt.length = 15 →
    ThrL (fun _ => True) (outF (y0 :: yt)) → False := by
  intro s
  induction s using Nat.strong_induction_on with
  | _ s ih =>
    intro y0 yt ws h hw hs hF
    have hlen := TR.len h
    obtain ⟨idx, rfl⟩ := vars_list ws hw
    have hpres : ∀ i, i ∈ idx := by
      intro i
      by_contra hi
      obtain ⟨j, hj, -⟩ := ex_third i i
      have hd := TRF_det h (pairInput i j) (singleInput j) (by
        intro w hw'
        obtain ⟨m, hm, rfl⟩ := List.mem_map.1 hw'
        have : m ≠ i := fun e => hi (e ▸ hm)
        simp [var, pairInput, singleInput, this])
      have h2 := outF_congr _ _ _ hd
      rw [hF.1 j trivial, hF.2 i j trivial trivial (Ne.symm hj)] at h2
      exact Bool.noConfusion h2
    simp only [List.length_map, List.length_cons] at hlen
    by_cases hall : ∀ i, 2 ≤ idx.count i
    · have hc := len_counts idx
      have h0 := hall 0
      have h1 := hall 1
      have h2 := hall 2
      have h3 := hall 3
      have h4 := hall 4
      have h5 := hall 5
      have h6 := hall 6
      apply one y0 yt s idx h _ (atMostTwo lb y0 yt idx s h hs hF) hF
      simp only [List.length_cons]
      omega
    · obtain ⟨x, hx⟩ := not_forall.1 hall
      have hx1 : idx.count x = 1 := by
        have := List.count_pos_iff.2 (hpres x)
        omega
      have hp : (idx.map var).Perm (var x :: (idx.erase x).map var) :=
        (List.perm_cons_erase (hpres x)).map var
      have hnx : x ∉ idx.erase x := by
        intro hm
        have := List.count_pos_iff.2 hm
        rw [List.count_erase_self] at this
        omega
      have hinv : ∀ w ∈ (idx.erase x).map var, InvX x w := by
        intro w hw'
        obtain ⟨m, hm, rfl⟩ := List.mem_map.1 hw'
        exact InvX_var fun e => hnx (e ▸ hm)
      have hsu := SU x y0 yt hF s _ (TR.perm hp h) hinv
      unfold SUc at hsu
      rcases hsu with ⟨hA1, hA2⟩ | ⟨c, h0, ys', s', hs', hl, hthr, hrun⟩
      · have hno : otop x ∉ (idx.erase x).map var := by
          intro hm
          obtain ⟨m, -, he⟩ := List.mem_map.1 hm
          obtain ⟨j, hj1, hj2⟩ := ex_third m x
          have h5 := congrFun he (singleInput j)
          have h6 : var m (singleInput j) = false := by simp [var, singleInput, Ne.symm hj1]
          have h7 : otop x (singleInput j) = true := by
            simp only [otop, decide_eq_true_eq]
            exact ⟨j, hj2, by simp [singleInput]⟩
          rw [h6, h7] at h5
          exact Bool.noConfusion h5
        simp only [hno, ite_false] at hA1 hA2
        have h6 := hA2 (fun w => w = otop x ∨ ∃ j, w = var (x.succAbove j)) (by
          intro w hw'
          obtain ⟨m, hm, rfl⟩ := List.mem_map.1 hw'
          have hmx : m ≠ x := fun e => hnx (e ▸ hm)
          obtain ⟨j, hj⟩ := Fin.exists_succAbove_eq hmx
          exact Or.inr ⟨j, by rw [hj]⟩) (Or.inl rfl)
        have h7 := top_elim (otop x) _ (fun w => ∃ j, w = var (x.succAbove j)) _ (by
          rintro w ⟨j, rfl⟩ p hp'
          simp only [otop, decide_eq_true_eq]
          exact ⟨x.succAbove j, Fin.succAbove_ne x j, hp'⟩) (by
          intro he
          have h8 := (thr_rst hF x).1 0
          rw [he] at h8
          have h9 : otop x (singleInput (x.succAbove 0)) = true := by
            simp only [otop, decide_eq_true_eq]
            exact ⟨x.succAbove 0, Fin.succAbove_ne x 0, by simp [singleInput]⟩
          rw [h9] at h8
          exact Bool.noConfusion h8) h6
        have hb := fiveLower lb x _ hF h7
        omega
      · refine ih s' (by omega) h0 ys' _ hrun ?_ (by omega) hthr
        intro w hw'
        rcases List.mem_append.1 hw' with hw' | hw'
        · exact ⟨x, List.eq_of_mem_replicate hw'⟩
        · obtain ⟨m, -, rfl⟩ := List.mem_map.1 hw'
          exact ⟨m, rfl⟩
theorem mono_sixteen (lb : Six.SixLow) (one : ImpossibleShared) (s : Nat)
    (h : UC gF MonoA s (fun w => ∃ i, w = var i) target) : 16 ≤ s := by
  obtain ⟨u,hu,ws,hw,hr⟩ := to_run targetThr h
  have h12 := transfer 13 (A := MonoA) (fun f hf k hk => by
    by_contra he
    exact Six.M6 lb hf (UC_le (by omega) hk)) hr hw
  by_contra he
  have eq : u=15 := by omega
  have ee : outF [target] = target := by funext x; simp [outF]
  exact GS6 lb one u target [] ws hr hw (by simp [eq]) (by rw [ee]; exact targetThr)
end ThresholdSixBound.Seven
namespace ThresholdSixBound.Seven
open Leaf5459
theorem sharedImpossible : ImpossibleShared := by
  intro y ys s idx run small count thr
  obtain ⟨H,G,Q,he,cost,hH,hG⟩ := SevenExtract.extract run small count
  apply ThresholdSeven.twoShare H G Q cost hH hG
  · intro i
    rw [he]
    exact thr.1 i trivial
  · intro i j hn
    rw [he]
    exact thr.2 i j trivial trivial hn
theorem monotoneLowerBound (lb : Six.SixLow) {s : ℕ} (h : UC gF MonoA s (fun w => ∃ i, w = var i) target) : 16 ≤ s :=
  mono_sixteen lb sharedImpossible s h
end ThresholdSixBound.Seven
namespace ThresholdSixBound.Seven
open Leaf5459 PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
def trueF : BF := fun _ => true
def memC (S : BF → Prop) (w : BF) := w = zF ∨ w = trueF ∨ S w
theorem monoGateForm (g : Gate) (W : List BF)
    (hop : g.op ∈ ({GateOp.and,GateOp.or} : Set GateOp))
    (hl : g.inputs.length ≤ 2) :
    gv g W = zF ∨ gv g W = trueF ∨
    (∃ a, (a ∈ W ∨ a = zF) ∧ gv g W = a) ∨
    (∃ k a b, MonoA k ∧ (a ∈ W ∨ a=zF) ∧ (b ∈ W ∨ b=zF) ∧ gv g W = gF k a b) := by
  rcases g with ⟨op,ins⟩
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hop
  rcases ins with _|⟨i,_|⟨j,_|rest⟩⟩
  · rcases hop with rfl|rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inl rfl
  · rcases hop with rfl|rfl <;> refine Or.inr (Or.inr (Or.inl ⟨_,getD_mem W i,?_⟩)) <;>
      funext x <;> simp [gv,GateOp.eval]
  · rcases hop with rfl|rfl
    · exact Or.inr (Or.inr (Or.inr ⟨0,_,_,by simp [MonoA],getD_mem W i,getD_mem W j,
        funext (fun x => by simp [gv,gF,zeroGate,GateOp.eval])⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨1,_,_,by simp [MonoA],getD_mem W i,getD_mem W j,
        funext (fun x => by simp [gv,gF,zeroGate,GateOp.eval])⟩))
  · simp at hl
theorem monoNext {g W S} (hop : g.op ∈ ({GateOp.and,GateOp.or} : Set GateOp))
    (hl : g.inputs.length ≤ 2) (hW : ∀ w ∈ W, memC S w) :
    memC S (gv g W) ∨ ∃ k a b, MonoA k ∧ S a ∧ S b ∧ gv g W = gF k a b := by
  have read (a) (ha : a ∈ W ∨ a = zF) : memC S a := ha.elim (hW _) (fun ha => Or.inl ha)
  rcases monoGateForm g W hop hl with q|q|⟨a,ha,q⟩|⟨k,a,b,hk,ha,hb,q⟩
  · exact Or.inl (Or.inl q)
  · exact Or.inl (Or.inr (Or.inl q))
  · rw [q]; exact Or.inl (read a ha)
  · rcases read a ha with e|e|sa
    · rw [q,e]
      rcases gF_zero_left k b with z|same
      · exact Or.inl (Or.inl z)
      · rw [same]; exact Or.inl (read b hb)
    · rw [q,e]
      rcases mono_cases k hk with rfl|rfl
      · have red : gF 0 trueF b = b := by funext x; simp [gF_and,trueF]
        rw [red]; exact Or.inl (read b hb)
      · have red : gF 1 trueF b = trueF := by funext x; simp [gF_or,trueF]
        exact Or.inl (Or.inr (Or.inl red))
    · rcases read b hb with e|e|sb
      · rw [q,e]
        rcases gF_zero_right k a with z|same
        · exact Or.inl (Or.inl z)
        · rw [same]; exact Or.inl (Or.inr (Or.inr sa))
      · rw [q,e]
        rcases mono_cases k hk with rfl|rfl
        · have red : gF 0 a trueF = a := by funext x; simp [gF_and,trueF]
          rw [red]; exact Or.inl (Or.inr (Or.inr sa))
        · have red : gF 1 a trueF = trueF := by funext x; simp [gF_or,trueF]
          exact Or.inl (Or.inr (Or.inl red))
      · exact Or.inr ⟨k,a,b,hk,sa,sb,q⟩
theorem monoTrans : ∀ (gs : List Gate) (W : List BF) (S : BF→Prop),
    (∀ g∈gs, g.op ∈ ({GateOp.and,GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2) →
    (∀ w∈W, memC S w) → ∀ o : ℕ,
    memC (UC gF MonoA gs.length S) ((wiresF gs W).getD o zF)
  | [], W, S, _, hW, o => by
    rcases getD_mem W o with q|q
    · exact hW _ q
    · exact Or.inl q
  | g::gs,W,S,legal,hW,o => by
    have hg:=legal g (by simp)
    have hr: ∀ g∈gs, g.op ∈ ({GateOp.and,GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 :=
      fun v hv => legal v (List.mem_cons_of_mem _ hv)
    rcases monoNext hg.1 hg.2 hW with free | ⟨k,a,b,hk,ha,hb,eq⟩
    · have th:=monoTrans gs (W++[gv g W]) S hr (by
        intro w hw; rcases List.mem_append.mp hw with old|new
        · exact hW _ old
        · rwa [List.mem_singleton.mp new]) o
      rcases th with h|h|h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (UC_le (Nat.le_succ _) h))
    · have th:=monoTrans gs (W++[gv g W]) (fun w=>w=gF k a b ∨ S w) hr (by
        intro w hw; rcases List.mem_append.mp hw with old|new
        · exact (hW _ old).imp id (fun z => z.imp id Or.inr)
        · rw [List.mem_singleton.mp new]; exact Or.inr (Or.inr (Or.inl eq))) o
      rcases th with h|h|h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (UC_gate k a b hk ha hb h))
theorem circuitSevenLower (lb : Six.SixLow) (C : Circuit) (ok : Monotone2 C)
    (spec : ∀ x : Fin 7→Bool, C.eval (List.ofFn x) = target x) : 16 ≤ C.size := by
  have eq : (wiresF C.gates (List.ofFn var)).getD C.output zF = target := by
    funext x
    rw [← spec x, ← getD_map_x, ← wires_eq]
    simp only [Circuit.eval,Circuit.wires,List.map_ofFn]
    rfl
  have h := monoTrans C.gates (List.ofFn var) (fun w=>∃ i, w=var i) ok (by
    intro w hw
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hw
    exact Or.inr (Or.inr ⟨i,rfl⟩)) C.output
  rw [eq] at h
  rcases h with z|t|h
  · exact False.elim (thr_ne_zero targetThr z)
  · have bad := congrFun t (fun _ => false)
    exact Bool.noConfusion bad
  · exact monotoneLowerBound lb h
end ThresholdSixBound.Seven

end PEqualNP.Outside.L_meta_10393_aux

theorem PEqualNP.Outside.L_meta_10393 : (¬ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => decide (2 ≤ ((List.ofFn x).count true))) 15)) := by
  exact PEqualNP.Outside.L_meta_10393_aux.SevenRoot.noCircuit PEqualNP.Outside.L_meta_10393_aux.signedThirteen (PEqualNP.Outside.L_meta_10393_aux.ThresholdSixBound.Seven.circuitSevenLower PEqualNP.Outside.L_meta_10393_aux.signedThirteen)
