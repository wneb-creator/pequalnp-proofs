import PEqualNP.Defs
-- Fixing vertex 5 to zero saves one gate. On the eleven remaining vertices
-- a monotone circuit needs at least eighteen gates. Even with free inversions
-- a circuit needs at least seventeen binary gates.
-- The live-circuit, restriction and rectangle arguments adapt project proofs
-- L-meta-670 and L-meta-9818. The graph and all finite tables are specific to this proof.
namespace PEqualNP.Outside.L_meta_9752
namespace Engine
open PEqualNP.CircuitLowerBounds
abbrev Sig := BitVec 2048
def zero : Sig := 0
def one : Sig := BitVec.allOnes 2048
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
def bit (i : Fin 2048) (a : Sig) : Bool := a.getLsbD i.val
theorem bit_zero (i) : bit i zero = false := by simp [bit,zero]
theorem bit_one (i) : bit i one = true := by unfold bit one; rw [BitVec.getLsbD_allOnes]; simp
theorem bit_neg (i) (a : Sig) : bit i (neg a) = !(bit i a) := by simp [bit,neg,i.isLt]
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
theorem get_rep {u} (w : List Sig) (i : Nat) : Repr u (w.map (nrm u)) (w.getD i zero) := by
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
theorem extract {u target} (gs : List Gate) (w : List Sig)
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
abbrev Row := Fin 2048
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
def inputs : List Sig := [0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00,0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000,0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000,0xffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000000000000000000000000000000000000,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000]
def graph : Sig := 0xfffffffefffffffefffffffefffffffefffffffefffffffefffffffefffffffefffffffefffffffefffffffefffefffefffffffefffffffefffffffefffefffefffffffefffffffefffffffefffffffefffffffefffffffefffffefefffffefefffffffafffffffafffffffafffafffafffffffafffffffafffffafafafafafafffffffefffffffefffffffefffffffefffffffefffffffefffffffefffffffefffffffefffffffefffffffefffefffeffffffeeffffffeeffffffeeffeeffeefffffffefffffffcfffffffefffffffcfffffffefffffffcfffffefefffffcfcfffffffafffffff0fffffffafff0fff0ffffffaaffffff00ffffaaaa00000000
def sample (r : Row) (j : Fin 11) := bit r (inputs.getD j.val zero)
def edge (x : Fin 11 → Bool) : Bool :=
  (x 0 && x 5) || (x 0 && x 9) || (x 0 && x 10) || (x 1 && x 8) || (x 1 && x 9) || (x 2 && x 7) || (x 2 && x 8) || (x 2 && x 10) || (x 3 && x 6) || (x 3 && x 7) || (x 3 && x 9) || (x 4 && x 5) || (x 4 && x 6) || (x 4 && x 8)
theorem edge_table : ∀ r : Row, bit r graph = edge (sample r) := by decide +kernel
theorem graph_proper : proper graph := by unfold proper; decide +kernel
theorem input_list : List.ofFn (fun j : Fin 11 => inputs.getD j.val zero) = inputs := rfl
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
abbrev Move := Sig × Sig × Row
def shifted (d r : Row) : Row :=
  if h : r.val < 2048-d.val then ⟨d.val+r.val,by omega⟩ else ⟨r.val-(2048-d.val),by omega⟩
def backwards (d : Row) : Row := Fin.ofNat 2048 (2048-d.val)
def rowMove (m : Move) (r : Row) : Row :=
  if bit r m.1 then shifted m.2.2 r else if bit r m.2.1 then shifted (backwards m.2.2) r else r
def mux (m a b : Sig) := (m &&& a) ||| (~~~m &&& b)
def wordMove (m : Move) (a : Sig) :=
  mux m.1 (a.rotateRight m.2.2.val) (mux m.2.1 (a.rotateRight (backwards m.2.2).val) a)
theorem bit_shift (d r : Row) (a : Sig) : bit r (a.rotateRight d.val) = bit (shifted d r) a := by
  unfold bit
  rw [BitVec.getLsbD_rotateRight_of_lt d.isLt]
  by_cases h : r.val < 2048-d.val <;> simp [shifted,h,r.isLt]
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
  (List.range 11).filterMap fun i => if m.testBit i then some (i,inputs.getD i zero) else none
def vars (m : Nat) := (selected m).map Prod.snd
def varsX (m : Nat) := vars m
def vertex (m j : Nat) := if m.testBit j then inputs.getD j zero else zero

def graphGoal (m : Nat) : Sig :=
  let x := vertex m
  (x 0 &&& x 5) ||| (x 0 &&& x 9) ||| (x 0 &&& x 10) ||| (x 1 &&& x 8) ||| (x 1 &&& x 9) ||| (x 2 &&& x 7) ||| (x 2 &&& x 8) ||| (x 2 &&& x 10) ||| (x 3 &&& x 6) ||| (x 3 &&& x 7) ||| (x 3 &&& x 9) ||| (x 4 &&& x 5) ||| (x 4 &&& x 6) ||| (x 4 &&& x 8)
def subcube (z o : Nat) : Sig :=
  if z &&& o != 0 then zero else
    (List.range 11).foldl (fun w i => if z.testBit i then w &&& ~~~(inputs.getD i zero)
      else if o.testBit i then w &&& inputs.getD i zero else w) one
def fixRows (z o : Nat) : List Move :=
  (List.range 11).filterMap fun j =>
    let x := inputs.getD j zero
    let step := Fin.ofNat 2048 (1 <<< j)
    if z.testBit j then some (zero,x,step)
    else if o.testBit j then some (~~~x,zero,step) else none
def swapRows (v : Nat) : Move :=
  let i := v &&& 15
  let j := v >>> 4
  let a := inputs.getD i zero
  let b := inputs.getD j zero
  let d := (1 <<< j)-(1 <<< i)
  (a &&& ~~~b,b &&& ~~~a,Fin.ofNat 2048 d)
def supportPairs (_t mask : Nat) : List (Sig × Row × Row) :=
  (selected mask).map fun (i,a) => (a,0,Fin.ofNat 2048 (1 <<< i))
def graphPairs (m hints : Nat) : List (Sig × Row × Row) :=
  (selected m).map fun (i,a) =>
    let r := 1 <<< ((hints >>> (4*i)) &&& 15)
    (a,Fin.ofNat 2048 r,Fin.ofNat 2048 (r ||| (1 <<< i)))
def properB (T : Sig) := T != zero && T != one
theorem proper_of (T : Sig) (h : properB T = true) : proper T := by
  simpa only [properB,proper,Bool.and_eq_true,bne_iff_ne] using h
abbrev ColumnInfo := Nat × Nat × Nat × Nat × Nat
def colFree (m z o : Nat) := m ^^^ (m &&& (z ||| o))
def chartGoal (m : Nat) : Sig := graphGoal m
def rawMask (m : Nat) (c : ColumnInfo) : Nat := m % 2048+2048*(c.1/2048)
def colCheck (m : Nat) (c : ColumnInfo) (prior : Nat → Nat) : Bool :=
  let (z,o,q,s,L) := c
  let ms := fixRows z o
  let raw := rawMask m c
  let free := colFree raw (z % 2048) o
  let G := movedWord ms (chartGoal m)
  let xs := supportPairs (z/2048+80) s
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
  let free := colFree raw (z % 2048) o
  let G := movedWord ms (chartGoal m)
  let xs := supportPairs (z/2048+80) s
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
abbrev Bits := BitVec 320
abbrev Signals := Bits × Bits
abbrev Decor := Sig × Signals
def ofRows {n : Nat} (r : Fin n → Row) (v : Sig) : BitVec n :=
  (BitVec.ofBoolListLE (List.ofFn (fun i => bit (r i) v))).cast List.length_ofFn
theorem ofRows_bit {n : Nat} (r : Fin n → Row) (v : Sig) (i : Fin n) :
    (ofRows r v).getLsbD i.val = bit (r i) v := by
  simp only [ofRows,BitVec.getLsbD_cast,BitVec.getLsbD_ofBoolListLE,List.getD_eq_getElem?_getD,List.getElem?_ofFn]
  simp [i.isLt]
def pairSig (r s : Fin 320 → Row) (a : Sig) : Signals := (ofRows r a,ofRows s a)
def properPairs (T : Sig) (r s : Fin 320 → Row) :=
  ∀ i, bit (r i) T = true ∧ bit (s i) T = false
theorem pair_sep {T r s} (h : properPairs T r s) : Sep T 320 r s (pairSig r s) := by
  exact ⟨h,fun a i => ⟨ofRows_bit _ _ _,ofRows_bit _ _ _⟩⟩
def faithful (r s : Fin 320 → Row) (x : Decor) := x.2 = pairSig r s x.1
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
    let a := ws.getD (bits &&& 31) defaultDecor
    let b := ws.getD ((bits >>> 5) &&& 31) defaultDecor
    decodeBank k (bits >>> 12) (ws++[dbin ((bits >>> 10) &&& 3) a b])
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
def asRow (cols : Nat → Bits) (i : Fin 320) : Row :=
  (BitVec.ofBoolListLE (List.ofFn (fun j : Fin 11 => (cols j.val).getLsbD i.val))).toFin.cast
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
theorem coordinate9 : ∀ r : Row, bit r (inputs.getD 9 zero) = r.val.testBit 9 := by decide +kernel
theorem coordinate10 : ∀ r : Row, bit r (inputs.getD 10 zero) = r.val.testBit 10 := by decide +kernel
theorem input_coords : ∀ (j : Fin 11) (r : Row), bit r (inputs.getD j.val zero) = r.val.testBit j.val := by
  intro j
  fin_cases j
  · exact coordinate0
  · exact coordinate1
  · exact coordinate2
  · exact coordinate3
  · exact coordinate4
  · exact coordinate5
  · exact coordinate6
  · exact coordinate7
  · exact coordinate8
  · exact coordinate9
  · exact coordinate10
theorem asRow_bit (cols : Nat → Bits) (i : Fin 320) (j : Fin 11) :
    bit (asRow cols i) (inputs.getD j.val zero) = (cols j.val).getLsbD i.val := by
  rw [input_coords]
  change (BitVec.ofBoolListLE (List.ofFn (fun h : Fin 11 => (cols h.val).getLsbD i.val))).getLsbD j.val = _
  simp only [BitVec.getLsbD_ofBoolListLE,List.getD_eq_getElem?_getD,List.getElem?_ofFn]
  simp [j.isLt]
def rawDecor (m : Nat) (p q : Nat → Bits) : List Decor :=
  (selected m).map (fun (j,a) => (a,p j,q j))
theorem selected_entry {m j a} (h : (j,a) ∈ selected m) :
    j<11 ∧ a=inputs.getD j zero := by
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
  (x 0 &&& x 5) ||| (x 0 &&& x 9) ||| (x 0 &&& x 10) ||| (x 1 &&& x 8) ||| (x 1 &&& x 9) ||| (x 2 &&& x 7) ||| (x 2 &&& x 8) ||| (x 2 &&& x 10) ||| (x 3 &&& x 6) ||| (x 3 &&& x 7) ||| (x 3 &&& x 9) ||| (x 4 &&& x 5) ||| (x 4 &&& x 6) ||| (x 4 &&& x 8)
theorem bit_vertex (m : Nat) (v : Nat → Bits) (i : Fin 320) (j : Fin 11) :
    bit (asRow v i) (vertex m j.val) =
    ((if m.testBit j.val then v j.val else 0) : Bits).getLsbD i.val := by
  by_cases hh : m.testBit j.val = true
  · simpa [vertex,hh] using asRow_bit v i j
  · simp [vertex,hh,bit_zero]
theorem bit_liftGoal (m : Nat) (v : Nat → Bits) (i : Fin 320) :
    bit (asRow v i) (graphGoal m) = (liftGoal m v).getLsbD i.val := by
  have pos (j : Nat) (hj : j<11) : (vertex m j).getLsbD (asRow v i).val = ((if m.testBit j then v j else 0) : Bits).getLsbD i.val := bit_vertex m v i ⟨j,hj⟩
  simp only [bit,graphGoal,liftGoal,BitVec.getLsbD_and,BitVec.getLsbD_or]
  simp only [pos 0 (by decide),pos 1 (by decide),pos 2 (by decide),pos 3 (by decide),pos 4 (by decide),pos 5 (by decide),pos 6 (by decide),pos 7 (by decide),pos 8 (by decide),pos 9 (by decide),pos 10 (by decide)]
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
    if (rs ||| column d z.2) != BitVec.allOnes 320 then true else
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
  have be : ((restCov (coverage (!u) ws) (column (!u) a.2) (column (!u) b.2) ka kb ||| column (!u) z.2) != BitVec.allOnes 320) = false := by
    simpa using sep
  change (if (restCov (coverage (!u) ws) (column (!u) a.2) (column (!u) b.2) ka kb ||| column (!u) z.2) != BitVec.allOnes 320 then true else if !properB z.1 || ws.any (fun v => v.1==z.1) then true else _) = true at test
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
  by_cases hj : j<11
  · let i : Fin 11 := ⟨j,hj⟩
    have hm : inputs.getD i.val zero ∈ inputs := by
      rw [← input_list]
      exact List.mem_ofFn.mpr ⟨i,rfl⟩
    exact (input_coords i r).symm.trans ((h _ hm).trans (input_coords i s))
  · have le : 2048 ≤ 2^j := by
      change 2^11 ≤ 2^j
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
abbrev Forest := Nat × Nat × (Nat → Bits × Bits) × List ColumnInfo × List (List Nat) ×
  (Nat → Packing) × (Nat → Nat → Option (Nat × Nat))
def Forest.mask (g : Forest) : Nat := g.1
def Forest.mode (g : Forest) : Bool := !(g.1.testBit 12)
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
theorem chart_bit (m : Nat) (v : Nat → Bits) (i : Fin 320) :
    bit (asRow v i) (chartGoal m) = (chartSamples m v).getLsbD i.val := by
  exact bit_liftGoal m v i
theorem chart_pairs {m : Nat} {p q : Nat → Bits}
    (hp : chartSamples m p = BitVec.allOnes 320) (hq : chartSamples m q = 0) :
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
def forestRecord (tab : Packing) (_raw i : Nat) :=
  let (_,_,_,_,_,_,_,words) := tab
  words (2*i)
def storedDepth (_g : Forest) (depth : Nat) := depth
def readNode (g : Forest) (k i : Nat) : Nat × List Decor × List Decor :=
  let raw := wiresOf g
  let (_,depth,_,_,_,_,_,data) := g.levels k
  let len := 12*storedDepth g depth
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
    let more := chosenSteps bank (ops >>> 12) (paid >>> 1) n
    if paid &&& 1 == 0 then more else
      (getFieldV ops 10 2,(bank.getD (ops &&& 31) defaultDecor).1,
        (bank.getD (getFieldV ops 5 5) defaultDecor).1) :: more
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
def decodeHints (cw d : Nat) : Nat → Nat → List (Nat × Nat)
  | 0,_ => []
  | n+1,x => (x % (1 <<< cw),(x >>> cw) % (1 <<< d)) ::
      decodeHints cw d n (x >>> (cw+d))
def forestHints (tab : Packing) (_raw i : Nat) :=
  let (_,depth,cw,_,_,_,_,words) := tab
  let data := words (2*i+1)
  decodeHints cw depth (data % 256) (data >>> 8)
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

def graphValid (g : Forest) (prior : Nat → Nat) :=
  (chartSamples g.mask (fun j => (g.samples j).1) == BitVec.allOnes 320) &&
  (chartSamples g.mask (fun j => (g.samples j).2) == 0) &&
  g.cols.all (fun c => colCheck g.mask c prior) &&
  g.autos.all (fun p => autoOK (targetOf g) (p.map swapRows))
def indexedRoot (g : Forest) (k i : Nat) (ws : List Sig) :=
  decide (i < (g.levels k).1) && sameWords (stateSet g k i) ws
def Known (u : Bool) (entries : List (Nat × Nat)) := ∀ e ∈ entries, Lower u (varsX e.1) (graphGoal e.1) e.2
theorem baseKnown : Known true [] := by simp [Known]
theorem known_down {u es} (h : Known true es) : Known u es := fun e he => lower_down (h e he)
def lanePlace (v : Nat) (upper : Nat) := 2^321*upper+v
def combineLanes {α : Type} (f : α → Bits) : List α → Nat
  | [] => 0
  | x::xs => lanePlace (f x).toNat (combineLanes f xs)
def units : Nat → Nat
  | 0 => 0
  | n+1 => lanePlace 1 (units n)
theorem laneSmall (x : Bits) : x.toNat < 2^321 :=
  lt_trans x.isLt (by decide +kernel)
theorem place_and (a b : Bits) (u v : Nat) :
    lanePlace a.toNat u &&& lanePlace b.toNat v = lanePlace (a &&& b).toNat (u &&& v) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [lanePlace,Nat.testBit_and,Nat.testBit_two_pow_mul_add _ (laneSmall _)]
  by_cases h : i<321 <;> simp only [h,ite_true,ite_false,BitVec.toNat_and,Nat.testBit_and]
theorem place_or (a b : Bits) (u v : Nat) :
    lanePlace a.toNat u ||| lanePlace b.toNat v = lanePlace (a ||| b).toNat (u ||| v) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [lanePlace,Nat.testBit_or,Nat.testBit_two_pow_mul_add _ (laneSmall _)]
  by_cases h : i<321 <;> simp only [h,ite_true,ite_false,BitVec.toNat_or,Nat.testBit_or]
theorem place_xor (a b : Bits) (u v : Nat) :
    lanePlace a.toNat u ^^^ lanePlace b.toNat v = lanePlace (a ^^^ b).toNat (u ^^^ v) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [lanePlace,Nat.testBit_xor,Nat.testBit_two_pow_mul_add _ (laneSmall _)]
  by_cases h : i<321 <;> simp only [h,ite_true,ite_false,BitVec.toNat_xor,Nat.testBit_xor]
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
def fullMarks (r packed : Nat) := ((packed+r) >>> 320) &&& r
theorem unit_bit (n i : Nat) (hi : i<n) : (units n).testBit (321*i) = true := by
  induction n generalizing i with
  | zero => omega
  | succ n ih =>
    rw [units,lanePlace,Nat.testBit_two_pow_mul_add _ (by decide +kernel : 1 < 2^321)]
    cases i with
    | zero => simp
    | succ i =>
      have di : 321*(i+1)-321=321*i := by omega
      have ge : ¬321*(i+1)<321 := by omega
      simp only [ge,ite_false,di]
      exact ih _ (by omega)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem guardBit (a : Bits) : (a.toNat+1).testBit 320 = (a==BitVec.allOnes 320) := by
  by_cases h : a=BitVec.allOnes 320
  · subst a
    decide +kernel
  · have lim := a.isLt
    have ne : a.toNat ≠ 2^320-1 := by
      intro eq
      apply h
      apply BitVec.eq_of_toNat_eq
      simpa only [BitVec.toNat_allOnes] using eq
    have lt : a.toNat+1<2^320 := by omega
    rw [Nat.testBit_eq_false_of_lt lt]
    exact (beq_eq_false_iff_ne.mpr h).symm
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem mark_at {α} (f : α → Bits) (xs : List α) (i : Nat) (hi : i<xs.length) :
    (fullMarks (units xs.length) (combineLanes f xs)).testBit (321*i) =
      (f xs[i]==BitVec.allOnes 320) := by
  simp only [fullMarks,Nat.testBit_and,Nat.testBit_shiftRight,unit_bit _ _ hi,Bool.and_true]
  induction xs generalizing i with
  | nil => simp at hi
  | cons a xs ih =>
    simp only [combineLanes,List.length_cons,units,lanePlace]
    have sum (u v x : Nat) : 2^321*u+x+(2^321*v+1)=2^321*(u+v)+(x+1) := by omega
    rw [sum,Nat.testBit_two_pow_mul_add _ (show (f a).toNat+1<2^321 from by have := (f a).isLt; omega)]
    have hi' : i < xs.length+1 := hi
    cases i with
    | zero => simpa using guardBit (f a)
    | succ i =>
      have ge : ¬321*(i+1)+320<321 := by omega
      have di : 321*(i+1)+320-321=321*i+320 := by omega
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
    ((mask &&& 1 == 0) || f x) && onMarks f (mask >>> 321) xs
theorem marked_ok {α} (f : α → Bool) (mask : Nat) (xs : List α) (i : Nat) (hi : i<xs.length)
    (bitOn : mask.testBit (321*i)=true) (ok : onMarks f mask xs=true) : f xs[i]=true := by
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
      apply ih (mask:=mask >>> 321) (i:=i) (by simpa using hi) _ ok.2
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
def validSwap (v : Nat) : Bool := and (Nat.ble ((v &&& 15)+1) (v >>> 4)) (Nat.ble ((v >>> 4)+1) 11)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem swap_table : ∀ v : Fin 176, validSwap v.val=true → ∀ t : Fin 11, swapIdx v.val t.val<11 ∧
    wordMove (swapRows v.val) (inputs.getD t.val zero) = inputs.getD (swapIdx v.val t.val) zero := by decide +kernel
theorem swap_input {v t : Nat} (hv : validSwap v=true) (ht : t<11) : swapIdx v t<11 ∧
    wordMove (swapRows v) (inputs.getD t zero) = inputs.getD (swapIdx v t) zero := by
  have lt : v<176 := by
    simp only [validSwap,Bool.and_eq_true,Nat.ble_eq,Nat.shiftRight_eq_div_pow] at hv
    omega
  exact swap_table ⟨v,lt⟩ hv ⟨t,ht⟩
def idxOf (perm : List Nat) (t : Nat) : Nat := perm.foldl (fun t v => swapIdx v t) t
theorem idx_move {perm : List Nat} (ok : perm.all validSwap=true) {t : Nat} (ht : t<11) :
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
  | n+1,bits,ws => force (zN ((bits >>> 10) &&& 3) (ws.getD (bits &&& 31) 0) (ws.getD ((bits >>> 5) &&& 31) 0))
      fun z => decodeN n (bits >>> 12) (ws++[z])
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
  let len := 12*depth
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
      if len>k then true else if combField xs[q] (!u) ka kb op i j != BitVec.allOnes 320 then true
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
    by_cases hit : combField xs[q] (!u) ka kb op i j = BitVec.allOnes 320
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
def kwWord (T : Sig) (ws : List Sig) (k value : Nat) : Bool :=
  let a := ws.getD (value % 16) zero
  let b := ws.getD ((value >>> 4) % 16) zero
  let row := fun i : Nat => Fin.ofNat 2048 ((value >>> (8+11*i)) % 2048)
  decide (k+1=ws.toFinset.card) && decide (a≠b) &&
    kwWireB ws T a (row 0) (row 2) && kwWireB ws T b (row 0) (row 3) &&
    kwWireB ws T a (row 4) (row 1) && kwWireB ws T b (row 5) (row 1)
theorem kwWord_sound {T ws k v} (h : kwWord T ws k v=true) : Impossible false T k ws.toFinset := by
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
def kwTest (g : Forest) (k a n : Nat) (data : Nat → Nat) :=
  (List.range n).all fun j => kwWord (targetOf g) (stateSet g k (a+j)) k (data j)
theorem mixedCut {g k a n data} (mode : g.mode=false) (h : kwTest g k a n data=true) :
    CutRow g k a n := by
  intro j lo hi
  right
  rw [mode]
  have hh := List.all_eq_true.mp h (j-a) (List.mem_range.mpr (by omega))
  have sum : a+(j-a)=j := by omega
  change kwWord _ (stateSet g k (a+(j-a))) k _=true at hh
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
theorem mixedLower {g prior i hints} (low : ∀ q, Lower g.mode (varsX q) (graphGoal q) (prior q))
    (geom : graphValid g prior = true) (blocks : mixedTables g g.cap)
    (idx : indexedRoot g g.cap i (vars g.mask) = true) (hp : properB (targetOf g) = true)
    (ess : checkEssential (targetOf g) (vars g.mask) (graphPairs g.mask hints) = true)
    (all : (graphPairs g.mask hints).map Prod.fst = vars g.mask) :
    Lower g.mode (vars g.mask) (targetOf g) (g.cap+1) := by
  apply lower_impossible (proper_of _ hp) (essential_plain ess).1 (essential_plain ess).2 _ (mixedRoot low geom blocks (Nat.le_refl _) idx)
  intro a ha
  apply essential_ok ess a
  rw [all]
  exact List.mem_toFinset.mpr ha
structure FreeRooms (S : Finset Sig) (T H : Sig) where
  owns : Sig → Row → Row → Prop
  total : ∀ p n, bit p T=true → bit n T=false →
    (bit p H=true ∧ bit n H=false) ∨ ∃ v, owns v p n
  valid : ∀ {v p n}, owns v p n → v∈S ∧ bit p v=true ∧ bit n v=false
  unique : ∀ {v w p n}, owns v p n → owns w p n → v=w
  rect : ∀ {v p n p' n'}, owns v p n' → owns v p' n → owns v p n

structure SingleFactor (S : Finset Sig) (T : Sig) where
  inner : Finset Sig
  outer : Finset Sig
  pivot : Sig
  cover : inner ∪ outer = S
  apart : Disjoint inner outer
  inside : KWRooms inner pivot
  outside : FreeRooms outer T pivot
def freeFrom {S T} (D : KWRooms S T) (h : Sig) : FreeRooms S T h where
  owns := D.owns
  total p n hp hn := Or.inr (D.total p n hp hn)
  valid := D.valid
  unique := D.unique
  rect := D.rect
def freeHide {S T h} (D : FreeRooms S T h) : FreeRooms (S.erase h) T h where
  owns v p n := v≠h ∧ D.owns v p n
  total := by
    intro p n hp hn
    rcases D.total p n hp hn with yes | ⟨v,hv⟩
    · exact Or.inl yes
    · by_cases eq : v=h
      · exact Or.inl (eq ▸ (D.valid hv).2)
      · exact Or.inr ⟨v,eq,hv⟩
  valid := by
    rintro v p n ⟨ne,hv⟩
    exact ⟨Finset.mem_erase.mpr ⟨ne,(D.valid hv).1⟩,(D.valid hv).2⟩
  unique := fun h1 h2 => D.unique h1.2 h2.2
  rect := fun a b => ⟨a.1,D.rect a.2 b.2⟩
def factorOfTree {S T} (D : KWRooms S T) : SingleFactor S T where
  inner := S
  outer := ∅
  pivot := T
  cover := by simp
  apart := by simp
  inside := D
  outside := {
    owns := fun _ _ _ => False
    total := fun p n hp hn => Or.inl ⟨hp,hn⟩
    valid := fun h => h.elim
    unique := fun h _ => h.elim
    rect := fun h _ => h.elim }
def freeFork {h : Sig} {U : Finset Sig} {T a b : Sig} {d : Nat} (d01 : d=0 ∨ d=1)
    (ha : a∉U) (hb : b∉U) (hz : bin d a b∉U)
    (H : FreeRooms (insert (bin d a b) U) T h) : FreeRooms (insert a (insert b U)) T h := by
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
    rcases H.total p n hp hn with closed | ⟨v,hv⟩
    · exact Or.inl closed
    right
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
theorem supportSide {A B U : Finset Sig} {a b z : Sig}
    (e : A∪B=insert z U) (disj : Disjoint A B) (za : z∈A)
    (freshA : a∉insert z U) (freshB : b∉insert z U) (freshZ : z∉U) :
    (insert a (insert b (A.erase z))) ∪ B=insert a (insert b U) ∧
    Disjoint (insert a (insert b (A.erase z))) B ∧ a∉A.erase z ∧ b∉A.erase z := by
  have hb : z∉B := fun h => Finset.disjoint_left.mp disj za h
  have allmem (w : Sig) : w∈A∨w∈B ↔ w=z∨w∈U := by
    rw [←Finset.mem_union,←Finset.mem_insert,e]
  have aout : a∉A ∧ a∉B := by
    have h : a∉A∪B := by rw [e]; exact freshA
    simpa using h
  have bout : b∉A ∧ b∉B := by
    have h : b∉A∪B := by rw [e]; exact freshB
    simpa using h
  refine ⟨?_,?_,fun h => aout.1 (Finset.mem_of_mem_erase h),fun h => bout.1 (Finset.mem_of_mem_erase h)⟩
  · ext w
    have m := allmem w
    by_cases eq : w=z
    · subst w; simp [freshZ,hb]
    · simp only [Finset.mem_union,Finset.mem_insert,Finset.mem_erase] at *
      tauto
  · apply Finset.disjoint_left.mpr
    intro w hw hwB
    rcases Finset.mem_insert.mp hw with rfl | hw
    · exact aout.2 hwB
    rcases Finset.mem_insert.mp hw with rfl | hw
    · exact bout.2 hwB
    exact Finset.disjoint_left.mp disj (Finset.mem_of_mem_erase hw) hwB
def factorExpand {U T a b d} (hd : d=0 ∨ d=1)
    (freshA : a∉insert (bin d a b) U) (freshB : b∉insert (bin d a b) U)
    (freshZ : bin d a b∉U) (F : SingleFactor (insert (bin d a b) U) T) :
    SingleFactor (insert a (insert b U)) T := by
  classical
  let z := bin d a b
  by_cases inn : z∈F.inner
  · obtain ⟨eq,apart,ha,hb⟩ := supportSide F.cover F.apart inn freshA freshB freshZ
    have old : KWRooms (insert z (F.inner.erase z)) F.pivot := by
      rw [Finset.insert_erase inn]; exact F.inside
    exact ⟨_,F.outer,F.pivot,eq,apart,kwFork hd ha hb (by simp [z]) old,F.outside⟩
  · have out : z∈F.outer := by
      have m : z∈F.inner∪F.outer := by rw [F.cover]; exact Finset.mem_insert_self _ _
      exact (Finset.mem_union.mp m).resolve_left inn
    obtain ⟨eq,apart,ha,hb⟩ := supportSide ((Finset.union_comm _ _).trans F.cover) F.apart.symm out freshA freshB freshZ
    have old : FreeRooms (insert z (F.outer.erase z)) T F.pivot := by
      rw [Finset.insert_erase out]; exact F.outside
    exact ⟨F.inner,_,F.pivot,(Finset.union_comm _ _).trans eq,apart.symm,F.inside,
      freeFork hd ha hb (by simp [z]) old⟩
def factorKeep {U T a b d} (hd : d=0 ∨ d=1) (ab : a≠b) (hb : b∉U)
    (fresh : bin d a b∉insert a (insert b U)) (H : KWRooms (insert (bin d a b) U) T) :
    SingleFactor (insert a (insert b U)) T := by
  let z := bin d a b
  have za : z≠a := by
    intro eq
    apply fresh
    exact Finset.mem_insert.mpr (Or.inl eq)
  have zU : z∉U := fun h => fresh (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem h))
  have set0 : (insert z U).erase a = insert z (U.erase a) := by
    ext v
    simp only [Finset.mem_erase,Finset.mem_insert]
    by_cases eq : v=z
    · subst v; simp [za]
    · tauto
  have H0 : FreeRooms (insert z (U.erase a)) T a := set0 ▸ freeHide (freeFrom H a)
  have H1 := freeFork hd (show a∉U.erase a by simp)
    (fun m => hb (Finset.mem_of_mem_erase m)) (fun m => zU (Finset.mem_of_mem_erase m)) H0
  have eq : insert a (insert b (U.erase a))=insert a (insert b U) := by
    ext v
    simp only [Finset.mem_insert,Finset.mem_erase]
    tauto
  have H1' : FreeRooms (insert a (insert b U)) T a := eq ▸ H1
  refine ⟨{a},(insert a (insert b U)).erase a,a,?_,?_,kwLeaf a,freeHide H1'⟩
  · ext v; simp only [Finset.mem_union,Finset.mem_singleton,Finset.mem_erase,Finset.mem_insert]; tauto
  · simp
theorem oneShare {T k S} (r : Live false T k S) (budget : k≤S.card) :
    Nonempty (SingleFactor S T) := by
  induction k generalizing S with
  | zero =>
    obtain ⟨rfl,_⟩ := r
    exact ⟨factorOfTree (kwLeaf T)⟩
  | succ k ih =>
    obtain ⟨U,a,b,d,hd,rfl,_,_,ab,fresh,tail⟩ := r
    let z := bin d a b
    have zU : z∉U := fun m => fresh (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem m))
    have size := kwWidth tail
    have zcard : (insert z U).card=U.card+1 := Finset.card_insert_of_notMem zU
    change (insert z U).card ≤ k+1 at size
    have hd01 : d=0 ∨ d=1 := by rcases hd with q | ⟨q,_⟩ <;> simp_all <;> omega
    by_cases ain : a∈U
    · rw [Finset.insert_eq_of_mem (Finset.mem_insert_of_mem ain : a∈insert b U)] at budget
      by_cases bin' : b∈U
      · rw [Finset.insert_eq_of_mem bin'] at budget; omega
      · rw [Finset.card_insert_of_notMem bin'] at budget
        obtain ⟨H⟩ := kwTight tail (by change (insert z U).card=k+1; omega)
        exact ⟨factorKeep hd01 ab bin' fresh H⟩
    · by_cases bin' : b∈U
      · rw [Finset.insert_eq_of_mem bin',Finset.card_insert_of_notMem ain] at budget
        obtain ⟨H⟩ := kwTight tail (by change (insert z U).card=k+1; omega)
        have comm : bin d b a=z := by
          rcases hd01 with eq | eq <;> subst d <;> simp [z,bin,BitVec.and_comm,BitVec.or_comm]
        have H' : KWRooms (insert (bin d b a) U) T := by simpa only [comm] using H
        have fr : bin d b a∉insert b (insert a U) := by simpa only [comm,Finset.insert_comm] using fresh
        have F := factorKeep hd01 ab.symm ain fr H'
        exact ⟨by simpa only [Finset.insert_comm] using F⟩
      · have an : a∉insert b U := by simp [ain,ab]
        rw [Finset.card_insert_of_notMem an,Finset.card_insert_of_notMem bin'] at budget
        obtain ⟨F⟩ := ih tail (by change k≤(insert z U).card; omega)
        have neA : a≠z := fun e => fresh (Finset.mem_insert.mpr (Or.inl e.symm))
        have neB : b≠z := fun e => fresh (Finset.mem_insert_of_mem (Finset.mem_insert.mpr (Or.inl e.symm)))
        have fa : a∉insert z U := fun h => (Finset.mem_insert.mp h).elim neA ain
        have fb : b∉insert z U := fun h => (Finset.mem_insert.mp h).elim neB bin'
        exact ⟨factorExpand hd01 fa fb zU F⟩
theorem factorForced {S : Finset Sig} {T : Sig} (F : SingleFactor S T) (p n : Row)
    (hp : bit p T=true) (hn : bit n T=false)
    (none : ∀ v∈F.outer, bit p v=true → bit n v=false → False) :
    bit p F.pivot=true ∧ bit n F.pivot=false := by
  rcases F.outside.total p n hp hn with h | ⟨v,hv⟩
  · exact h
  · exact False.elim (none v (F.outside.valid hv).1 (F.outside.valid hv).2.1 (F.outside.valid hv).2.2)
theorem factorOuterOwn {S : Finset Sig} {T : Sig} (F : SingleFactor S T) {a p n} (ao : a∈F.outer)
    (one : onlyWire S T a p n) : F.outside.owns a p n := by
  rcases F.outside.total p n one.1 one.2.1 with hpivot | ⟨w,hw⟩
  · obtain ⟨w,hw⟩ := F.inside.total p n hpivot.1 hpivot.2
    obtain ⟨wi,wp,wn⟩ := F.inside.valid hw
    have ws : w∈S := F.cover ▸ Finset.mem_union_left _ wi
    have eq := one.2.2 w ws wp wn
    rw [eq] at wi
    exact False.elim (Finset.disjoint_left.mp F.apart wi ao)
  · obtain ⟨wo,wp,wn⟩ := F.outside.valid hw
    have ws : w∈S := F.cover ▸ Finset.mem_union_right _ wo
    have eq := one.2.2 w ws wp wn
    exact eq ▸ hw
theorem outerCannotCross {S : Finset Sig} {T : Sig} (F : SingleFactor S T) {a b p n pa pb na nb}
    (aout : a∈F.outer) (bout : b∈F.outer)
    (different : a≠b) (A : onlyWire S T a p na) (B : onlyWire S T b p nb)
    (C : onlyWire S T a pa n) (D : onlyWire S T b pb n) : False :=
  different (F.outside.unique (F.outside.rect (factorOuterOwn F aout A) (factorOuterOwn F aout C))
    (F.outside.rect (factorOuterOwn F bout B) (factorOuterOwn F bout D)))
theorem innerCannotCross {S : Finset Sig} {T : Sig} (F : SingleFactor S T) {a b p n pa pb na nb}
    (different : a≠b) (A : onlyWire F.inner F.pivot a p na) (B : onlyWire F.inner F.pivot b p nb)
    (C : onlyWire F.inner F.pivot a pa n) (D : onlyWire F.inner F.pivot b pb n) : False :=
  different (F.inside.unique (F.inside.rect (kwOwn F.inside A) (kwOwn F.inside C))
    (F.inside.rect (kwOwn F.inside B) (kwOwn F.inside D)))
theorem innerSource {S : Finset Sig} {T : Sig} (F : SingleFactor S T) {v p n}
    (hv : v∈F.inner) (only : onlyWire S T v p n) : onlyWire F.inner F.pivot v p n := by
  have h : bit p F.pivot=true ∧ bit n F.pivot=false := by
    apply factorForced F p n only.1 only.2.1
    intro w wo hp hn
    have ws : w∈S := F.cover ▸ Finset.mem_union_right _ wo
    have eq := only.2.2 w ws hp hn
    exact Finset.disjoint_left.mp F.apart hv (eq ▸ wo)
  refine ⟨h.1,h.2,?_⟩
  intro w wi hp hn
  exact only.2.2 w (F.cover ▸ Finset.mem_union_left _ wi) hp hn
theorem hornRule {S : Finset Sig} {T : Sig} (F : SingleFactor S T) {a b c p n pa na}
    (ar : onlyWire S T a p na) (br : onlyWire S T b pa n) (cr : onlyWire S T c p n)
    (ia : a∈F.inner) (ib : b∈F.inner) : c∈F.inner := by
  have ah := innerSource F ia ar
  have bh := innerSource F ib br
  obtain ⟨w,hw⟩ := F.inside.total p n ah.1 bh.2.1
  obtain ⟨wi,wp,wn⟩ := F.inside.valid hw
  have ws : w∈S := F.cover ▸ Finset.mem_union_left _ wi
  exact (cr.2.2 w ws wp wn) ▸ wi
theorem parityRule {S : Finset Sig} {T : Sig} (F : SingleFactor S T) {a b p n pa pb na nb}
    (hs : a∈S) (ht : b∈S) (ne : a≠b)
    (h1 : onlyWire S T a p na) (h2 : onlyWire S T b p nb)
    (h3 : onlyWire S T a pa n) (h4 : onlyWire S T b pb n) :
    ((a∈F.inner ∧ b∈F.inner) ∨ (a∉F.inner ∧ b∉F.inner)) → False := by
  rintro (⟨ia,ib⟩ | ⟨oa,ob⟩)
  · exact innerCannotCross F ne (innerSource F ia h1) (innerSource F ib h2)
      (innerSource F ia h3) (innerSource F ib h4)
  · rw [←F.cover,Finset.mem_union] at hs ht
    exact outerCannotCross F (hs.resolve_left oa) (ht.resolve_left ob) ne h1 h2 h3 h4
def colorPoint (v : Fin 11 → Bool) : Row :=
  (BitVec.ofBoolListLE (List.ofFn v)).toFin.cast (by simp [List.length_ofFn])
theorem color_bit (v : Fin 11 → Bool) (i : Fin 11) :
    bit (colorPoint v) (inputs.getD i.val zero) = v i := by
  rw [input_coords]
  change (BitVec.ofBoolListLE (List.ofFn v)).getLsbD i.val = _
  simp only [BitVec.getLsbD_ofBoolListLE,List.getD_eq_getElem?_getD,List.getElem?_ofFn]
  simp [i.isLt]
def colorField (d j : Nat) : Fin 11 := Fin.ofNat 11 ((d >>> (1+4*j)) % 16)
def colorRow (d j : Nat) : Row := Fin.ofNat 2048 ((d >>> (13+11*j)) % 2048)
def colorWire (ws : List Sig) (names : Nat) (j : Fin 11) : Sig :=
  ws.getD ((names >>> (4*j.val)) % 16) zero
def colorRule (ws : List Sig) (T : Sig) (names d : Nat) : Bool :=
  let a := colorWire ws names (colorField d 0)
  let b := colorWire ws names (colorField d 1)
  let c := colorWire ws names (colorField d 2)
  let r := colorRow d
  if d.testBit 0 then
    (decide (a ∈ ws) && decide (b ∈ ws) && decide (a ≠ b)) &&
    (kwWireB ws T a (r 0) (r 2) && kwWireB ws T b (r 0) (r 3) &&
      kwWireB ws T a (r 4) (r 1) && kwWireB ws T b (r 5) (r 1))
  else kwWireB ws T a (r 0) (r 2) && kwWireB ws T b (r 3) (r 1) &&
    kwWireB ws T c (r 0) (r 1)
def constraintWord (d : Nat) : Sig :=
  let x := fun j => inputs.getD (colorField d j).val zero
  if d.testBit 0 then x 0 ^^^ x 1 else ~~~(x 0 &&& x 1) ||| x 2
def colorTruth {ws : List Sig} {T : Sig} (F : SingleFactor ws.toFinset T)
    (names : Nat) (i : Fin 11) := decide (colorWire ws names i ∈ F.inner)
theorem parity_bit {A B : Prop} [Decidable A] [Decidable B]
    (h : ¬ ((A ∧ B) ∨ (¬A ∧ ¬B))) : (decide A ^^ decide B) = true := by
  by_cases a : A <;> by_cases b : B <;> simp_all
theorem horn_bit {A B C : Prop} [Decidable A] [Decidable B] [Decidable C]
    (h : A → B → C) : (!(decide A && decide B) || decide C) = true := by
  by_cases a : A <;> by_cases b : B <;> simp_all
theorem bit_xor (r : Row) (a b : Sig) : bit r (a ^^^ b) = (bit r a ^^ bit r b) :=
  BitVec.getLsbD_xor
theorem rule_valid {ws T names d} (F : SingleFactor ws.toFinset T)
    (h : colorRule ws T names d = true) :
    bit (colorPoint (colorTruth F names)) (constraintWord d) = true := by
  have bits (i) := color_bit (colorTruth F names) (colorField d i)
  by_cases flag : d.testBit 0 = true
  · simp only [colorRule,flag,ite_true,Bool.and_eq_true,decide_eq_true_eq] at h
    have rule := parityRule F (List.mem_toFinset.mpr h.1.1.1) (List.mem_toFinset.mpr h.1.1.2) h.1.2
      (kwWireB_sound h.2.1.1.1) (kwWireB_sound h.2.1.1.2) (kwWireB_sound h.2.1.2) (kwWireB_sound h.2.2)
    simp only [constraintWord,flag,ite_true]
    rw [bit_xor,bits,bits]
    exact parity_bit rule
  · simp only [colorRule,if_neg flag,Bool.and_eq_true] at h
    have rule := hornRule F (kwWireB_sound h.1.1) (kwWireB_sound h.1.2) (kwWireB_sound h.2)
    simp only [constraintWord,if_neg flag]
    change bit _ (prime true (neg (prime false _ _)) _) = true
    rw [bit_prime,bit_neg,bit_prime]
    change (!(bit _ _ && bit _ _) || bit _ _) = true
    rw [bits,bits,bits]
    exact horn_bit rule
def colorSet : List Nat → Sig
  | [] => one
  | d::ds => constraintWord d &&& colorSet ds
theorem color_set {ws T names} (F : SingleFactor ws.toFinset T) (ds : List Nat)
    (h : ds.all (colorRule ws T names) = true) :
    bit (colorPoint (colorTruth F names)) (colorSet ds) = true := by
  induction ds with
  | nil => exact bit_one _
  | cons d ds ih =>
    simp only [List.all_cons,Bool.and_eq_true] at h
    change bit _ (prime false _ _) = true
    rw [bit_prime,rule_valid F h.1,ih h.2]
    rfl
def colorCheck (ws : List Sig) (T : Sig) (k names : Nat) (ds : List Nat) :=
  decide (k ≤ ws.toFinset.card) && ds.all (colorRule ws T names) && (colorSet ds == zero)
theorem color_sound {ws T k names ds} (h : colorCheck ws T k names ds=true) :
    Impossible false T k ws.toFinset := by
  simp only [colorCheck,Bool.and_eq_true,decide_eq_true_eq,beq_iff_eq] at h
  intro n le run
  obtain ⟨F⟩ := oneShare run (le.trans h.1.1)
  have ok := color_set F ds h.1.2
  rw [h.2,bit_zero] at ok
  contradiction
def colorRange (g : Forest) (k a n : Nat) (ds : Nat → Nat × List Nat) :=
  (List.range n).all fun i =>
    colorCheck (stateSet g k (a+i)) (targetOf g) k (ds i).1 (ds i).2
theorem colorCut {g k a n ds} (mode : g.mode=false)
    (h : colorRange g k a n ds=true) : CutRow g k a n := by
  intro j lo hi
  right
  rw [mode]
  have hh := List.all_eq_true.mp h (j-a) (List.mem_range.mpr (by omega))
  have eq : a+(j-a)=j := by omega
  change colorCheck (stateSet g k (a+(j-a))) _ _ _ _=true at hh
  rw [eq] at hh
  exact color_sound hh
def neighbor670 (i : Fin 11) : Nat := [5,8,7,6,5,0,3,2,1,0,0].getD i.val 0
def absentRow670 (i : Fin 11) : Row := Fin.ofNat 2048 (1 <<< neighbor670 i)
def presentRow670 (i : Fin 11) : Row := Fin.ofNat 2048 ((1 <<< i.val) ||| (1 <<< neighbor670 i))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem requiredInputs :
    (∀ i : Fin 11, bit (absentRow670 i) graph ≠ bit (presentRow670 i) graph) ∧
    (∀ i j : Fin 11, i ≠ j →
      bit (absentRow670 i) (inputs.getD j.val zero) =
      bit (presentRow670 i) (inputs.getD j.val zero)) := by decide +kernel
theorem twoRoots (C : Circuit) (legal : PEqualNP.MetaComplexity.FanInTwo C)
    (computes : PEqualNP.MetaComplexity.circuitFun 11 C = edge) (small : C.size ≤ 17) :
    ∃ (u : Bool) (k : Nat), k ≤ (if u then 16 else 17) ∧ Live u graph k inputs.toFinset := by
  have goalEq : (execute C.gates inputs).getD C.output zero = graph := by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    let r : Row := ⟨j,hj⟩
    exact (table_eval C legal C.output r).trans ((congrFun computes (sample r)).trans (edge_table r).symm)
  have len : C.gates.length ≤ 17 := small
  have mode : ∃ u : Bool, (u=false → ∀ g ∈ C.gates, isNot g=false) ∧ C.gates.countP (fun g => !isNot g) ≤ (if u then 16 else 17) := by
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
  have idx (a : Sig) (ha : a ∈ inputs) : ∃ i : Fin 11, inputs.getD i.val zero = a := by
    rw [←input_list] at ha
    exact List.mem_ofFn.mp ha
  have eq : S = inputs.toFinset := by
    ext a
    constructor
    · exact fun h => List.mem_toFinset.mpr (sub a h)
    · intro ha
      obtain ⟨i,rfl⟩ := idx a (List.mem_toFinset.mp ha)
      apply raw_required run inputs (inputs.getD i.val zero) sub (absentRow670 i) (presentRow670 i)
        (requiredInputs.1 i)
      intro v hv hn
      obtain ⟨j,rfl⟩ := idx v hv
      apply requiredInputs.2 i j
      rintro rfl
      exact hn rfl
  exact ⟨u,k,hk.trans count,eq ▸ run⟩
theorem directSplit
    (m : ∀ k, k ≤ 17 → ¬Live false graph k inputs.toFinset)
    (s : ∀ k, k ≤ 16 → ¬Live true graph k inputs.toFinset) :
    ¬ PEqualNP.MetaComplexity.HasCircuitSize 11 edge 17 := by
  rintro ⟨C,legal,small,computes⟩
  obtain ⟨mode,k,hk,run⟩ := twoRoots C legal (funext computes) small
  cases mode
  · exact m k hk run
  · exact s k hk run
def orderLaw (S : Finset Sig) (T : Sig) (f : Sig → Nat) :=
  (∀ {a b p n na nb pa pb}, a ≠ b →
    onlyWire S T a p na → onlyWire S T b p nb →
    onlyWire S T a pa n → onlyWire S T b pb n → f a ≠ f b) ∧
  (∀ {a b c p n na pb}, onlyWire S T a p na → onlyWire S T b pb n →
    onlyWire S T c p n → f a = f b → f c ≤ f a)
theorem only_value {k S T v p n} (run : Live false T k S) (h : onlyWire S T v p n) :
    v∈S ∧ bit p v=true ∧ bit n v=false := by
  obtain ⟨w,hw,hp,hn⟩ := mono_row_difference run rfl h.1 h.2.1
  exact h.2.2 w hw hp hn ▸ ⟨hw,hp,hn⟩
def gateList (a b : Sig) (U : Finset Sig) := [a,b].filter fun t => decide (t∈U)
def gateMap (a b z v : Sig) := if v=a ∨ v=b then z else v
def gateColor (a b z : Sig) (U : Finset Sig) (f : Sig → Nat) (v : Sig) :=
  let kept := gateList a b U
  if v∈kept then kept.idxOf v else kept.length+f (gateMap a b z v)
theorem gate_kept {a b v U} :
    v∈gateList a b U ↔ (v=a ∨ v=b) ∧ v∈U := by simp [gateList]
theorem gate_mem {a b z v : Sig} {U : Finset Sig} (h : v∈insert a (insert b U)) :
    gateMap a b z v ∈ insert z U := by
  by_cases eq : v=a ∨ v=b
  · simp [gateMap,eq]
  · simp_all [gateMap]
theorem mono_bin_bit {d} (hd : allowed false d) (a b : Sig) (r : Row) :
    bit r (bin d a b) = if d=0 then bit r a && bit r b else bit r a || bit r b := by
  rcases allowed_four hd with rfl | rfl | ⟨h,_⟩ | ⟨h,_⟩
  · simp [bit,bin]
  · simp [bit,bin]
  · contradiction
  · contradiction
theorem gate_only {a b d U T v p n} (hd : allowed false d)
    (unused : v∉gateList a b U) (h : onlyWire (insert a (insert b U)) T v p n) :
    onlyWire (insert (bin d a b) U) T (gateMap a b (bin d a b) v) p n := by
  refine ⟨h.1,h.2.1,?_⟩
  intro w hw hp hn
  rcases Finset.mem_insert.mp hw with rfl | hw
  · rw [mono_bin_bit hd] at hp hn
    have sep : (bit p a=true ∧ bit n a=false) ∨ (bit p b=true ∧ bit n b=false) := by
      by_cases op : d=0 <;> cases u : bit p a <;> cases v : bit n a <;> cases x : bit p b <;>
        cases y : bit n b <;> simp_all
    have eq : v=a ∨ v=b := by
      rcases sep with ⟨x,y⟩ | ⟨x,y⟩
      · exact Or.inl (h.2.2 a (by simp) x y).symm
      · exact Or.inr (h.2.2 b (by simp) x y).symm
    simp [gateMap,eq]
  · obtain rfl := h.2.2 w (by simp [hw]) hp hn
    have ne : ¬(w=a ∨ w=b) := fun eq => unused (gate_kept.mpr ⟨eq,hw⟩)
    simp [gateMap,ne]
theorem gate_share_eq {a b z U f v w} (hv : v∈gateList a b U)
    (eq : gateColor a b z U f v = gateColor a b z U f w) : v=w := by
  have bound := List.idxOf_lt_length_of_mem hv
  by_cases hw : w∈gateList a b U
  · simp only [gateColor,if_pos hv,if_pos hw] at eq
    exact (List.idxOf_inj hv).mp eq
  · simp only [gateColor,if_pos hv,if_neg hw] at eq
    omega
theorem gate_cross {a b d U T k p n na nb pa pb} (hd : allowed false d) (hab : a≠b)
    (run : Live false T k (insert (bin d a b) U)) (prev : Live false T (k+1) (insert a (insert b U)))
    (ua : a∉gateList a b U)
    (A : onlyWire (insert a (insert b U)) T a p na) (B : onlyWire (insert a (insert b U)) T b p nb)
    (C : onlyWire (insert a (insert b U)) T a pa n) (D : onlyWire (insert a (insert b U)) T b pb n) : False := by
  have Zp := (only_value run (gate_only hd ua C)).2.1
  have Zn := (only_value run (gate_only hd ua A)).2.2
  simp only [gateMap,true_or,ite_true,mono_bin_bit hd] at Zp Zn
  by_cases op : d=0
  · simp [op] at Zp
    exact hab (C.2.2 b (by simp) Zp.2 (only_value prev D).2.2).symm
  · simp [op] at Zn
    exact hab (A.2.2 b (by simp) (only_value prev B).2.1 Zn.2).symm
theorem order_live {k S T} (h : Live false T k S) :
    ∃ (count : Nat) (f : Sig → Nat), count+S.card ≤ k+2 ∧ (∀ v∈S, f v<count) ∧ orderLaw S T f := by
  induction k generalizing S with
  | zero =>
    obtain ⟨rfl,properT⟩ := h
    refine ⟨1,fun _ => 0,by simp,by simp,?_,by simp⟩
    intro a b p n na nb pa pb ne A B C D
    have e := (only_value (Live.stop (u:=false) properT) A).1
    have j := (only_value (Live.stop (u:=false) properT) B).1
    simp only [Finset.mem_singleton] at e j
    exact (ne (e.trans j.symm)).elim
  | succ k ih =>
    obtain ⟨U,a,b,d,hd,rfl,ha,hb,hab,fresh,tail⟩ := h
    let z := bin d a b
    let kept := gateList a b U
    have prev := Live.binary hd ha hb hab fresh tail
    obtain ⟨count,f,mass,bound,law⟩ := ih tail
    have hzu : z∉U := fun m => fresh (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem m))
    rw [Finset.card_insert_of_notMem hzu] at mass
    have size : kept.length + (insert a (insert b U)).card = U.card+2 := by
      by_cases x : a∈U <;> by_cases y : b∈U <;>
        simp [kept,gateList,x,y,hab,Finset.card_insert_of_notMem] <;> omega
    refine ⟨kept.length+count,gateColor a b z U f,by omega,?_,?_,?_⟩
    · intro v hv
      by_cases u : v∈kept
      · have m := List.idxOf_lt_length_of_mem u
        change (if v∈kept then kept.idxOf v else _) < _
        rw [if_pos u]
        omega
      · have m := bound _ (gate_mem (z:=z) hv)
        change (if v∈kept then kept.idxOf v else _) < _
        rw [if_neg u]
        exact Nat.add_lt_add_left m _
    · intro v w p n na nb pa pb vw A B C D eq
      have uv : v∉kept := fun u => vw (gate_share_eq u eq)
      have uw : w∉kept := fun u => vw (gate_share_eq u eq.symm).symm
      have same : f (gateMap a b z v) = f (gateMap a b z w) := by
        change (if v∈kept then _ else kept.length+_) = (if w∈kept then _ else kept.length+_) at eq
        rw [if_neg uv,if_neg uw] at eq
        omega
      by_cases ne : gateMap a b z v ≠ gateMap a b z w
      · exact law.1 ne (gate_only hd uv A) (gate_only hd uw B)
          (gate_only hd uv C) (gate_only hd uw D) same
      · have vS := (only_value prev A).1
        have wS := (only_value prev B).1
        have vz : v≠z := fun e => fresh (show z∈_ from e ▸ vS)
        have wz : w≠z := fun e => fresh (show z∈_ from e ▸ wS)
        have pair : (v=a ∧ w=b) ∨ (v=b ∧ w=a) := by
          by_cases va : v=a ∨ v=b <;> by_cases wa : w=a ∨ w=b <;> simp_all [gateMap] <;> grind
        rcases pair with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
        · exact gate_cross hd hab tail prev uv A B C D
        · exact gate_cross hd hab tail prev uw B A D C
    · intro v w t p n na pb A B C eq
      have ident (e : v=w) : t=v := by
        subst w
        exact (C.2.2 v (only_value prev A).1 (only_value prev A).2.1 (only_value prev B).2.2).symm
      by_cases uv : v∈kept
      · rw [ident (gate_share_eq uv eq)]
      by_cases uw : w∈kept
      · rw [ident (gate_share_eq uw eq.symm).symm]
      have same : f (gateMap a b z v) = f (gateMap a b z w) := by
        change (if v∈kept then _ else kept.length+_) = (if w∈kept then _ else kept.length+_) at eq
        rw [if_neg uv,if_neg uw] at eq
        omega
      change (if t∈kept then kept.idxOf t else kept.length+_) ≤ (if v∈kept then _ else kept.length+_)
      rw [if_neg uv]
      by_cases ut : t∈kept
      · rw [if_pos ut]
        have lim := List.idxOf_lt_length_of_mem ut
        omega
      · rw [if_neg ut]
        exact Nat.add_le_add_left (law.2 (gate_only hd uv A) (gate_only hd uw B) (gate_only hd ut C) same) _
def rankRule (d : Nat) (f : Fin 11 → Nat) : Prop :=
  let v := fun j => f (colorField d j)
  if d.testBit 0 then v 0 ≠ v 1 else v 0=v 1 → v 2≤v 0
theorem rank_rule {ws T names d f} (h : colorRule ws T names d=true)
    (law : orderLaw ws.toFinset T f) :
    rankRule d (fun i => f (colorWire ws names i)) := by
  by_cases flag : d.testBit 0=true
  · simp only [rankRule,colorRule,flag,ite_true,Bool.and_eq_true,decide_eq_true_eq] at h ⊢
    exact law.1 h.1.2 (kwWireB_sound h.2.1.1.1) (kwWireB_sound h.2.1.1.2)
      (kwWireB_sound h.2.1.2) (kwWireB_sound h.2.2)
  · simp only [rankRule,colorRule,if_neg flag,Bool.and_eq_true] at h ⊢
    exact law.2 (kwWireB_sound h.1.1) (kwWireB_sound h.1.2) (kwWireB_sound h.2)
def layerCovers (lo : Nat) (f : Fin 11 → Nat) (t : Nat) :=
  ∀ i, f i<t → lo.testBit i.val=true
def layerBits (lo : Nat) (f : Fin 11 → Nat) (t : Nat) (i : Fin 11) :=
  !lo.testBit i.val && decide (f i=t)
def layerRule (lo d : Nat) : Sig :=
  let x := fun j => inputs.getD (colorField d j).val zero
  let pair := neg (prime false (x 0) (x 1))
  if d.testBit 0 then pair else
    if lo.testBit (colorField d 2).val then one else prime true pair (x 2)
theorem layer_rule {lo d f t} (h : rankRule d f) (cov : layerCovers lo f t) :
    bit (colorPoint (layerBits lo f t)) (layerRule lo d)=true := by
  have eval (j) := color_bit (layerBits lo f t) (colorField d j)
  by_cases flag : d.testBit 0=true
  · simp only [rankRule,flag,ite_true] at h
    simp only [layerRule,flag,ite_true,bit_neg,bit_prime,Bool.false_eq_true,ite_false,eval]
    cases x : layerBits lo f t (colorField d 0) <;> cases y : layerBits lo f t (colorField d 1) <;> simp_all
    simp only [layerBits,Bool.and_eq_true,decide_eq_true_eq] at x y
    exact h (x.2.trans y.2.symm)
  · simp only [rankRule,if_neg flag] at h
    simp only [layerRule,if_neg flag]
    by_cases old : lo.testBit (colorField d 2).val=true
    · rw [if_pos old,bit_one]
    · rw [if_neg old]
      simp only [bit_prime,ite_true,bit_neg,Bool.false_eq_true,ite_false,eval]
      cases x : layerBits lo f t (colorField d 0) <;> cases y : layerBits lo f t (colorField d 1) <;> simp_all
      simp only [layerBits,Bool.and_eq_true,decide_eq_true_eq] at x y
      have le := h (x.2.trans y.2.symm)
      have ge : ¬ f (colorField d 2)<t := by
        intro lt
        have hit := cov _ lt
        simp [old] at hit
      simp [layerBits,old,show f (colorField d 2)=t by omega]
def layerWords (lo : Nat) : List Nat → Sig
  | [] => one
  | d::ds => prime false (layerRule lo d) (layerWords lo ds)
theorem layer_words {lo f t} (ds : List Nat) (h : ∀d∈ds, rankRule d f) (cov : layerCovers lo f t) :
    bit (colorPoint (layerBits lo f t)) (layerWords lo ds)=true := by
  induction ds with
  | nil => exact bit_one _
  | cons d ds ih =>
    rw [layerWords,bit_prime,layer_rule (h d (by simp)) cov,ih (fun e he => h e (by simp [he]))]
    rfl
def cubeParts (mask : Nat) : List (Fin 11) → Sig
  | [] => one
  | i::is => if mask.testBit i.val then cubeParts mask is else
      prime false (neg (inputs.getD i.val zero)) (cubeParts mask is)
theorem cube_parts {x : Fin 11 → Bool} (mask : Nat) (is : List (Fin 11))
    (h : bit (colorPoint x) (cubeParts mask is)=true) :
    ∀ i∈is, x i=true → mask.testBit i.val=true := by
  induction is with
  | nil => simp
  | cons j js ih =>
    by_cases hm : mask.testBit j.val=true
    · rw [cubeParts,if_pos hm] at h
      intro i hi hx
      rcases List.mem_cons.mp hi with rfl | hi
      · exact hm
      · exact ih h i hi hx
    · rw [cubeParts,if_neg hm,bit_prime,bit_neg,color_bit] at h
      simp only [Bool.false_eq_true,ite_false,Bool.and_eq_true,Bool.not_eq_true'] at h
      intro i hi hx
      rcases List.mem_cons.mp hi with rfl | hi
      · simp_all
      · exact ih h.2 i hi hx
def cubeWord (mask : Nat) := cubeParts mask (List.finRange 11)
def layerUpper (lo : Nat) : List Nat → Sig
  | [] => zero
  | a::as => if lo &&& a = lo then prime true (cubeWord a) (layerUpper lo as) else layerUpper lo as
theorem upper_choice {lo f t} (as : List Nat) (cov : layerCovers lo f t)
    (ok : bit (colorPoint (layerBits lo f t)) (layerUpper lo as)=true) :
    ∃ a∈as, layerCovers a f (t+1) := by
  induction as with
  | nil => rw [layerUpper,bit_zero] at ok; contradiction
  | cons a as ih =>
    have follow (h : bit (colorPoint (layerBits lo f t)) (layerUpper lo as)=true) : ∃ v∈a::as, layerCovers v f (t+1) := by
      obtain ⟨v,hv,cv⟩ := ih h
      exact ⟨v,List.mem_cons_of_mem _ hv,cv⟩
    by_cases sub : lo &&& a=lo
    · rw [layerUpper,if_pos sub,bit_prime] at ok
      rcases Bool.or_eq_true_iff.mp ok with hit | tail
      · refine ⟨a,by simp,?_⟩
        intro i hi
        by_cases old : lo.testBit i.val=true
        · have z := congrArg (fun v : Nat => v.testBit i.val) sub
          simpa only [Nat.testBit_and,old,Bool.true_and] using z
        · have ge : ¬ f i<t := fun lt => old (cov i lt)
          have yes : layerBits lo f t i=true := by simp [layerBits,old,show f i=t by omega]
          exact cube_parts a (List.finRange 11) hit i (by simp) yes
      · exact follow tail
    · rw [layerUpper,if_neg sub] at ok
      exact follow ok
def layerStep (ds : List Nat) (lo : Nat) (hi : List Nat) :=
  (prime false (layerWords lo ds) (neg (layerUpper lo hi)) == zero)
theorem layer_step {ds lo hi f t} (laws : ∀d∈ds,rankRule d f) (cov : layerCovers lo f t)
    (ok : layerStep ds lo hi=true) : ∃ a∈hi, layerCovers a f (t+1) := by
  have eq := beq_iff_eq.mp ok
  have chk := congrArg (bit (colorPoint (layerBits lo f t))) eq
  rw [bit_prime,bit_neg,bit_zero,layer_words ds laws cov] at chk
  apply upper_choice hi cov
  simpa using chk
def finalPair (lo d : Nat) := d.testBit 0 && !lo.testBit (colorField d 0).val && !lo.testBit (colorField d 1).val
def layerScan (ds lo : List Nat) : List (List Nat) → Bool
  | [] => lo.all fun a => ds.any (finalPair a)
  | hi::tail => (lo.all fun a => layerStep ds a hi) && layerScan ds hi tail
theorem layer_scan {ds f} (laws : ∀d∈ds,rankRule d f) (ls : List (List Nat))
    {lo t} (covered : ∃a∈lo,layerCovers a f t) (bound : ∀i, f i<t+ls.length+1)
    (ok : layerScan ds lo ls=true) : False := by
  induction ls generalizing lo t with
  | nil =>
    obtain ⟨a,ha,ca⟩ := covered
    obtain ⟨d,hd,yes⟩ := List.any_eq_true.mp (List.all_eq_true.mp ok a ha)
    simp only [finalPair,Bool.and_eq_true,Bool.not_eq_true'] at yes
    have top (i : Fin 11) (no : a.testBit i.val=false) : f i=t := by
      have small : f i<t+1 := by simpa using bound i
      have big : ¬ f i<t := by intro lt; have hh := ca i lt; simp [no] at hh
      omega
    have diff := laws d hd
    simp only [rankRule,yes.1.1,ite_true] at diff
    exact diff ((top _ yes.1.2).trans (top _ yes.2).symm)
  | cons l ls ih =>
    obtain ⟨a,ha,ca⟩ := covered
    have both := Bool.and_eq_true_iff.mp ok
    apply ih (t:=t+1) (layer_step laws ca (List.all_eq_true.mp both.1 a ha)) _ both.2
    intro i
    have z := bound i
    simp only [List.length_cons] at z
    omega
abbrev OrderPage := Nat × List Nat × Nat × List (List Nat)
def orderCheck (ws : List Sig) (T : Sig) (k : Nat) (book : OrderPage) :=
  let (names,ds,start,ls) := book
  decide (k+2 ≤ ws.toFinset.card+ls.length+1) &&
    (List.finRange 11).all (fun i => decide (colorWire ws names i ∈ ws)) &&
    ds.all (colorRule ws T names) && layerScan ds [start] ls
theorem order_sound {ws T k page} (ok : orderCheck ws T k page=true) : Impossible false T k ws.toFinset := by
  rcases page with ⟨names,ds,start,ls⟩
  simp only [orderCheck,Bool.and_eq_true,decide_eq_true_eq,List.all_eq_true] at ok
  intro n le run
  obtain ⟨count,f,mass,bound,law⟩ := order_live run
  apply layer_scan (f:=fun i => f (colorWire ws names i)) (fun d hd => rank_rule (ok.1.2 d hd) law)
    ls (t:=0) (lo:=[start]) ⟨start,by simp,by simp [layerCovers]⟩ _ ok.2
  intro i
  have use := (ok.1.1.2 _ (List.mem_finRange i))
  have less := bound _ (List.mem_toFinset.mpr use)
  have size := ok.1.1.1
  omega
def orderRange (g : Forest) (k a n : Nat) (pages : Nat → OrderPage) :=
  (List.range n).all fun i => orderCheck (stateSet g k (a+i)) (targetOf g) k (pages i)
theorem orderCut {g k a n pages} (mode : g.mode=false) (ok : orderRange g k a n pages=true) :
    CutRow g k a n := by
  intro j lo hi
  right
  rw [mode]
  have hh := List.all_eq_true.mp ok (j-a) (List.mem_range.mpr (by omega))
  have eq : a+(j-a)=j := by omega
  change orderCheck (stateSet g k (a+(j-a))) _ _ _=true at hh
  rw [eq] at hh
  exact order_sound hh
def padColumn (n v : Nat) : Bits :=
  BitVec.ofNat 320 (v + if v % 2=1 then (1 <<< 320)-(1 <<< n) else 0)
theorem lowerHint {u raw T a b} (h : Lower u raw T a) (le : b ≤ a) : Lower u raw T b :=
  fun p bank hr hit => le.trans (h p bank hr hit)
def treeData (p n v : Nat) :=
  let row := fun base i => (base >>> (11*((v >>> (8+5*i)) % 32))) % 2048
  v % 256 + (row p 0 <<< 8) + (row n 1 <<< 19) + (row n 2 <<< 30) +
    (row n 3 <<< 41) + (row p 4 <<< 52) + (row p 5 <<< 63)
def ruleData (p n v : Nat) :=
  let row := fun base i => (base >>> (11*((v >>> (13+5*i)) % 32))) % 2048
  v % 8192 + (row p 0 <<< 13) + (row n 1 <<< 24) + (row n 2 <<< 35) +
    (row (if v.testBit 0 then n else p) 3 <<< 46) + (row p 4 <<< 57) + (row p 5 <<< 68)
theorem countFace {u m L} (hints : Nat)
    (hp : properB (graphGoal m)=true)
    (ess : checkEssential (graphGoal m) (varsX m) (graphPairs m hints)=true)
    (enough : L ≤ (List.map Prod.fst (graphPairs m hints)).toFinset.card - 1) :
    Lower u (varsX m) (graphGoal m) L :=
  lowerHint (lower_count (proper_of _ hp) (graphPairs m hints) ess) enough
theorem dropFace {u m q a L} (fixed hints : Nat) (prior : Lower u (varsX q) (graphGoal q) a)
    (mapped : checkLift (fixRows fixed 0) (graphGoal m) (varsX m) (varsX q) (graphGoal q) (graphPairs fixed hints)=true)
    (hm : properB (graphGoal m)=true) (hq : properB (graphGoal q)=true)
    (enough : L ≤ a + (List.map Prod.fst (graphPairs fixed hints)).toFinset.card) :
    Lower u (varsX m) (graphGoal m) L :=
  lowerHint (lift_ok mapped (proper_of _ hm) (proper_of _ hq) prior) enough
abbrev Face (u : Bool) (m L : Nat) := Lower u (varsX m) (graphGoal m) L
def tableWord (xs : Array Nat) (i : Nat) := xs.getD (i%8) 0
def tablePair (xs : Array (Nat × Nat)) (i : Nat) := xs.getD (i%8) (0,0)
def tableBits (xs : Array (Bits × Bits)) (i : Nat) := xs.getD (i%8) (0,0)
def readRules (pos neg width : Nat) (rules : Nat → Nat) : Nat → Nat → List Nat
  | 0,_ => []
  | n+1,v => ruleData pos neg (rules (v % (1 <<< width))) :: readRules pos neg width rules n (v >>> width)
def readPanel (pos neg rw pw : Nat) (rules programs : Nat → Nat) (rec : Nat) :=
  let program := programs (rec % (1 <<< pw))
  (rec >>> pw,readRules pos neg rw rules (program % 16) (program >>> 4))
theorem consFace {u m L es} (h : Face u m L) (tail : Known u es) : Known u ((m,L)::es) := by
  intro e he
  rcases List.mem_cons.mp he with rfl | h'
  · exact h
  · exact tail e h'
def smallSlot (h buckets slots iw pw : Nat) (disp slotsAt : Nat → Nat) : Option (Nat × Nat) :=
  let slot := (h/buckets+disp (h%buckets))%slots
  let val := slotsAt slot
  if val=0 || (val >>> (iw+pw)) != (h/(buckets*slots))%8 then none
  else some (val % (1 <<< iw)-1,(val >>> iw)%(1 <<< pw))
def variableSlot (blocks : Nat → Nat × Nat) (i : Nat) :=
  let b := blocks (i/16)
  let offsets := b.1 >>> (12*(i%16))
  let start := offsets % 4096
  (b.2 >>> start) % (1 <<< ((offsets >>> 12)%4096 - start))
def bookData (d fw mw : Nat) (fronts masks codes costs : Nat → Nat) (j : Nat) :=
  let i := j/2
  if j%2=1 then costs i else
    let code := codes i
    fronts (code % (1 <<< fw)) + ((code >>> (fw+mw)) <<< (12*(d-1))) +
      (masks ((code >>> fw)%(1 <<< mw)) <<< (12*d))
noncomputable def bandTest (g : Forest) (k a n ar : Nat) :=
  header g k a n ar && rowCut g k a n ar 0 ar
theorem bandTest_sound {g k a n ar} (ok : bandTest g k a n ar=true) :
    block g k a n=true :=
  cutsBlock (Bool.and_eq_true_iff.mp ok).1 (Bool.and_eq_true_iff.mp ok).2
noncomputable def bandCells (g : Forest) (k a n ar : Nat) (splitBand : Bool) :=
  if splitBand then bandTest g k a (n/2) ar && bandTest g k (a+n/2) (n-n/2) ar
  else bandTest g k a n ar
theorem bandCut {g k a n} (ar : Nat) (splitBand : Bool) (ok : bandCells g k a n ar splitBand=true) :
    CutRow g k a n := by
  apply checkedRow
  cases splitBand
  · exact bandTest_sound ok
  · have both := Bool.and_eq_true_iff.mp ok
    have all := block_merge (bandTest_sound both.1) (bandTest_sound both.2)
    simpa only [Nat.add_sub_of_le (Nat.div_le_self n 2)] using all
def readGroup (n pad : Nat) : Nat → Nat → List Nat
  | 0,_ => []
  | s+1,x => (pad+x % (1 <<< n)) :: readGroup n pad s (x >>> n)
def readGroups (n pad : Nat) : Nat → Nat → List (List Nat)
  | 0,_ => []
  | s+1,x =>
    let len := x % 64
    readGroup n pad len (x >>> 6) :: readGroups n pad s (x >>> (6+n*len))
def orderPage (pos neg w : Nat) (bank : Nat → Nat) (n q names clauses groups : Nat) : OrderPage :=
  let pad := 2048-(1 <<< n)
  (names,readRules pos neg w bank (clauses % 128) (clauses >>> 7),pad,readGroups n pad (q-1) groups)

namespace B209_4
def entries : List (Nat × Nat) := []
theorem prior : Known true entries := known_down baseKnown
def samples : Nat → Bits × Bits := (fun i => (if i<8 then tableBits #[(padColumn 10 0x1f,padColumn 10 0x20a),(padColumn 10 0x0,padColumn 10 0x0),(padColumn 10 0x0,padColumn 10 0x0),(padColumn 10 0x0,padColumn 10 0x0),(padColumn 10 0x3e0,padColumn 10 0x120),(padColumn 10 0x7f,padColumn 10 0x54),(padColumn 10 0x380,padColumn 10 0x218),(padColumn 10 0x0,padColumn 10 0x0)] i else tableBits #[(padColumn 10 0x0,padColumn 10 0x0),(padColumn 10 0x0,padColumn 10 0x0),(padColumn 10 0x0,padColumn 10 0x0)] i))
def cols : List ColumnInfo := []
def data3 : Nat → Nat := (fun i => tableWord #[0xf,0x0] i)
def levels : Nat → Packing
  | 3 => (1,0,1,0,0,0,0,data3)
  | _ => (0,0,0,0,0,0,0,fun _ => 0)
def index : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def book : Forest := ⟨113,3,samples,cols,[[],[96,84]],levels,index⟩
theorem geometry : graphValid book (boundsBefore entries) = true := by decide +kernel
set_option maxRecDepth 16000 in
theorem row3_0 : CutRow book 3 0 1 := bandCut 4 false (by decide +kernel)
theorem band3 : CutRow book 3 0 1 := row3_0
theorem checked : mixedTables book 3 := by
  intro k hk
  interval_cases k
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact band3
end B209_4
theorem h209_4 : Face true 113 4 :=
  mixedLower (g:=B209_4.book) (i:=0) (hints:=67436549)
    (before_sound B209_4.entries B209_4.prior) B209_4.geometry B209_4.checked
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem h216_4 : Face true 120 4 := carry_of (swaps:=[101,48,32,16]) (by decide +kernel) h209_4
theorem h408_4 : Face true 216 4 := carry_of (swaps:=[101,117,64,48,32,16]) (by decide +kernel) h209_4

namespace B473_7
def entries : List (Nat × Nat) := [(120,4),(113,4),(216,4)]
theorem prior : Known true entries := (consFace h216_4 (consFace h209_4 (consFace h408_4 (known_down baseKnown))))
def samples : Nat → Bits × Bits := (fun i => (if i<8 then tableBits #[(padColumn 36 0x191c603ff,padColumn 36 0x90d60153),(padColumn 36 0x0,padColumn 36 0x0),(padColumn 36 0x0,padColumn 36 0x0),(padColumn 36 0x27e07c300,padColumn 36 0x23a02d30a),(padColumn 36 0xc60787c00,padColumn 36 0x860280400),(padColumn 36 0x787807fff,padColumn 36 0x707007aac),(padColumn 36 0x807ff8000,padColumn 36 0x5d50030),(padColumn 36 0xff8000000,padColumn 36 0xdc02020c0)] i else tableBits #[(padColumn 36 0x0,padColumn 36 0x0),(padColumn 36 0x0,padColumn 36 0x0),(padColumn 36 0x0,padColumn 36 0x0)] i))
def cols : List ColumnInfo := [(129,0,120,0,4),(0,128,113,8,5),(0,1,216,32,5)]
def data6 : Nat → Nat := (fun i => tableWord #[0x3f,0x1803] i)
def levels : Nat → Packing
  | 6 => (1,0,2,0,0,0,0,data6)
  | _ => (0,0,0,0,0,0,0,fun _ => 0)
def index : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def book : Forest := ⟨249,6,samples,cols,[[],[112,83,100]],levels,index⟩
theorem geometry : graphValid book (boundsBefore entries) = true := by decide +kernel
set_option maxRecDepth 16000 in
theorem row6_0 : CutRow book 6 0 1 := bandCut 6 false (by decide +kernel)
theorem band6 : CutRow book 6 0 1 := row6_0
theorem checked : mixedTables book 6 := by
  intro k hk
  interval_cases k
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact band6
end B473_7
theorem h473_7 : Face true 249 7 :=
  mixedLower (g:=B473_7.book) (i:=0) (hints:=855990277)
    (before_sound B473_7.entries B473_7.prior) B473_7.geometry B473_7.checked
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem h476_7 : Face true 252 7 := carry_of (swaps:=[117,67,32,16]) (by decide +kernel) h473_7
theorem h594_4 : Face true 306 4 := carry_of (swaps:=[133,117,101,16]) (by decide +kernel) h209_4
theorem h658_4 : Face true 338 4 := carry_of (swaps:=[133,117,16]) (by decide +kernel) h209_4
theorem h598_5 : Face true 310 5 := dropFace 4 4299491456 h594_4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem h721_5 : Face true 369 5 := carry_of (swaps:=[65,132,98,50,16,80]) (by decide +kernel) h598_5

namespace B723_7
def entries : List (Nat × Nat) := [(113,4),(306,4),(338,4),(369,5)]
theorem prior : Known true entries := (consFace h209_4 (consFace h594_4 (consFace h658_4 (consFace h721_5 (known_down baseKnown)))))
def samples : Nat → Bits × Bits := (fun i => (if i<8 then tableBits #[(padColumn 37 0x198d803ff,padColumn 37 0x985c0153),(padColumn 37 0x1e1f202300,padColumn 37 0xa0b22b30a),(padColumn 37 0x0,padColumn 37 0x0),(padColumn 37 0x0,padColumn 37 0x0),(padColumn 37 0x603ffc00,padColumn 37 0x202b0400),(padColumn 37 0x780c03fff,padColumn 37 0x700803aac),(padColumn 37 0x1800ffc000,padColumn 37 0x1802d40030),(padColumn 37 0x0,padColumn 37 0x0)] i else tableBits #[(padColumn 37 0x1fff000000,padColumn 37 0x15d40000c0),(padColumn 37 0x0,padColumn 37 0x0),(padColumn 37 0x0,padColumn 37 0x0)] i))
def cols : List ColumnInfo := [(256,2,113,0,4),(65,0,306,0,4),(32,1,338,0,4),(2,0,369,0,5)]
def data6 : Nat → Nat := (fun i => tableWord #[0x3f,0xd204] i)
def data5 : Nat → Nat := (fun i => tableWord #[0x6f882,0x0] i)
def levels : Nat → Packing
  | 5 => (1,1,2,0,0,0,0,data5)
  | 6 => (1,0,2,0,0,0,0,data6)
  | _ => (0,0,0,0,0,0,0,fun _ => 0)
def index : Nat → Nat → Option (Nat × Nat)
  | 6 => fun v => (if v=5342971937700010185 then some (0,0) else none)
  | _ => fun _ => none
def book : Forest := ⟨371,6,samples,cols,[[],[16,133]],levels,index⟩
theorem geometry : graphValid book (boundsBefore entries) = true := by decide +kernel
set_option maxRecDepth 16000 in
theorem row6_0 : CutRow book 6 0 1 := bandCut 6 false (by decide +kernel)
theorem band6 : CutRow book 6 0 1 := row6_0
set_option maxRecDepth 16000 in
theorem row5_0 : CutRow book 5 0 1 := bandCut 6 false (by decide +kernel)
theorem band5 : CutRow book 5 0 1 := row5_0
theorem checked : mixedTables book 6 := by
  intro k hk
  interval_cases k
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact band5
  · exact band6
end B723_7
theorem h723_7 : Face true 371 7 :=
  mixedLower (g:=B723_7.book) (i:=0) (hints:=4362403973)
    (before_sound B723_7.entries B723_7.prior) B723_7.geometry B723_7.checked
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem h730_7 : Face true 378 7 := carry_of (swaps:=[101,48,32]) (by decide +kernel) h723_7
theorem h854_7 : Face true 438 7 := carry_of (swaps:=[112,16,132,80,97,32]) (by decide +kernel) h723_7
theorem h910_7 : Face true 462 7 := carry_of (swaps:=[118,133,66,16]) (by decide +kernel) h473_7
theorem h918_7 : Face true 470 7 := carry_of (swaps:=[112,132,80,97,32]) (by decide +kernel) h723_7
theorem h922_7 : Face true 474 7 := carry_of (swaps:=[133,16]) (by decide +kernel) h473_7
theorem h396_4 : Face true 204 4 := carry_of (swaps:=[117,67,32,16]) (by decide +kernel) h209_4
theorem h660_4 : Face true 340 4 := carry_of (swaps:=[133,117,32,16]) (by decide +kernel) h209_4
theorem h664_4 : Face true 344 4 := carry_of (swaps:=[134,101,117,48,32,16]) (by decide +kernel) h209_4
theorem h217_5 : Face true 121 5 := dropFace 8 50683909 h209_4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem h668_5 : Face true 348 5 := carry_of (swaps:=[133,117,32,16]) (by decide +kernel) h217_5
theorem h780_4 : Face true 396 4 := carry_of (swaps:=[134,117,48,64,32,16]) (by decide +kernel) h209_4
theorem h788_4 : Face true 404 4 := carry_of (swaps:=[101,134,117,64,32,16]) (by decide +kernel) h209_4

namespace B924_8
def entries : List (Nat × Nat) := [(204,4),(216,4),(340,4),(344,4),(348,5),(396,4),(404,4)]
theorem prior : Known true entries := (consFace h396_4 (consFace h408_4 (consFace h660_4 (consFace h664_4 (consFace h668_5 (consFace h780_4 (consFace h788_4 (known_down baseKnown))))))))
def samples : Nat → Bits × Bits := (fun i => (if i<8 then tableBits #[(padColumn 38 0x0,padColumn 38 0x0),(padColumn 38 0x0,padColumn 38 0x0),(padColumn 38 0x27cd8f860,padColumn 38 0x23c48786a),(padColumn 38 0x1d6027007f,padColumn 38 0x1568050033),(padColumn 38 0x2183381f80,padColumn 38 0x2081380a80),(padColumn 38 0x0,padColumn 38 0x0),(padColumn 38 0xe03c01fff,padColumn 38 0xa12c0554c),(padColumn 38 0x3003ffe000,padColumn 38 0x2003b28600)] i else tableBits #[(padColumn 38 0x3ffc000000,padColumn 38 0x1d40040010),(padColumn 38 0x0,padColumn 38 0x0),(padColumn 38 0x0,padColumn 38 0x0)] i))
def cols : List ColumnInfo := [(272,0,204,0,4),(260,0,216,0,4),(136,0,340,0,4),(132,0,344,0,4),(128,0,348,0,5),(80,0,396,0,4),(72,0,404,0,4)]
def data7 : Nat → Nat := (fun i => tableWord #[0x3f,0xd43306] i)
def data6 : Nat → Nat := (fun i => tableWord #[0x7f420,0x401,0x7f460,0x0] i)
def data5 : Nat → Nat := (fun i => tableWord #[0xaf886420,0x0] i)
def levels : Nat → Packing
  | 5 => (1,2,3,0,0,0,0,data5)
  | 6 => (2,1,3,0,0,0,0,data6)
  | 7 => (1,0,3,0,0,0,0,data7)
  | _ => (0,0,0,0,0,0,0,fun _ => 0)
def index : Nat → Nat → Option (Nat × Nat)
  | 6 => fun v => (if v=5688551321472505468 then some (0,0) else none)
  | 7 => fun h => smallSlot h 3 13 2 4 (fun i => (((fun i => tableWord #[0x7] i)) (i/16) >>> (3*(i%16))) % 8) (fun i => (((fun i => tableWord #[0x40800a5d9a6896ba00610018b4a] i)) (i/16) >>> (9*(i%16))) % 512)
  | _ => fun _ => none
def book : Forest := ⟨476,7,samples,cols,[[],[67,135],[50,134],[50,66,134,118],[66,50,118,134],[66,118],[98,115,132],[98,131,116],[114,99,132,67,50],[114,131,100],[130,99,116],[130,115,100,67,66]],levels,index⟩
theorem geometry : graphValid book (boundsBefore entries) = true := by decide +kernel
set_option maxRecDepth 16000 in
theorem row7_0 : CutRow book 7 0 1 := bandCut 6 false (by decide +kernel)
theorem band7 : CutRow book 7 0 1 := row7_0
set_option maxRecDepth 16000 in
theorem row6_0 : CutRow book 6 0 2 := bandCut 7 false (by decide +kernel)
theorem band6 : CutRow book 6 0 2 := row6_0
set_option maxRecDepth 16000 in
theorem row5_0 : CutRow book 5 0 1 := bandCut 6 false (by decide +kernel)
theorem band5 : CutRow book 5 0 1 := row5_0
theorem checked : mixedTables book 7 := by
  intro k hk
  interval_cases k
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact band5
  · exact band6
  · exact band7
end B924_8
theorem h924_8 : Face true 476 8 :=
  mixedLower (g:=B924_8.book) (i:=0) (hints:=9177556736)
    (before_sound B924_8.entries B924_8.prior) B924_8.geometry B924_8.checked
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem h727_8 : Face true 375 8 := dropFace 4 4362406021 h723_7 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem h982_8 : Face true 502 8 := carry_of (swaps:=[33,132,112,82,97,48]) (by decide +kernel) h727_8
theorem h596_4 : Face true 308 4 := carry_of (swaps:=[133,117,101,32,16]) (by decide +kernel) h209_4
theorem h774_4 : Face true 390 4 := carry_of (swaps:=[101,134,117,50,66,16]) (by decide +kernel) h209_4
theorem h860_7 : Face true 444 7 := carry_of (swaps:=[132,64,84,115,96,32,16]) (by decide +kernel) h473_7

namespace B990_11
def entries : List (Nat × Nat) := [(120,4),(204,4),(216,4),(252,7),(306,4),(308,4),(338,4),(378,7),(390,4),(438,7),(444,7),(462,7),(470,7),(474,7),(476,8)]
theorem prior : Known true entries := (consFace h216_4 (consFace h396_4 (consFace h408_4 (consFace h476_7 (consFace h594_4 (consFace h596_4 (consFace h658_4 (consFace h730_7 (consFace h774_4 (consFace h854_7 (consFace h860_7 (consFace h910_7 (consFace h918_7 (consFace h922_7 (consFace h924_8 (known_down baseKnown))))))))))))))))
def samples : Nat → Bits × Bits := (fun i => (if i<8 then tableBits #[(padColumn 125 0x0,padColumn 125 0x0),(padColumn 125 0x60618c3e1f800001c40101c0000c00,padColumn 125 0x2020881c45090421c50140c0514c08),(padColumn 125 0x818610c7e00e073e07c60e0003f000,padColumn 125 0x821046a202010a00460f04819012),(padColumn 125 0x70e0060f8001038c3f8180ffffc0000,padColumn 125 0x2060060f840001042a8080651fe6020),(padColumn 125 0x1810187f000061c0fc0027f0001fffff,padColumn 125 0x800003d00004040fc00029000047483),(padColumn 125 0x1f80000001ff00003800001fffff,padColumn 125 0x41780109401bf00001804011b8b7c),(padColumn 125 0x1fe00000007e0000003fffffe00000,padColumn 125 0x19e00000001e0000003469ae000040),(padColumn 125 0x1fe0000000007fffffffc00000000000,padColumn 125 0x1ce0000000007de6b117808008000180)] i else tableBits #[(padColumn 125 0x1fffffffffff80000000000000000000,padColumn 125 0x17df5d42a11800000022000030000200),(padColumn 125 0x0,padColumn 125 0x0),(padColumn 125 0x0,padColumn 125 0x0)] i))
def cols : List ColumnInfo := [(386,4,120,0,4),(384,6,120,0,4),(274,32,204,0,4),(272,34,204,0,4),(294,0,216,0,4),(292,2,216,0,4),(256,6,120,128,5),(256,2,252,0,7),(196,8,306,0,4),(202,0,308,0,4),(194,8,308,0,4),(44,128,338,0,4),(36,128,338,8,5),(132,0,378,0,7),(24,96,390,0,4),(16,96,390,8,5),(68,8,306,128,5),(66,8,308,128,5),(72,0,438,0,7),(66,0,444,0,7),(16,32,462,0,7),(40,0,470,0,7),(36,0,474,0,7),(34,0,476,0,8),(0,34,204,272,6),(0,6,120,384,6),(0,2,252,256,8)]
def data10 : Nat → Nat := (fun i => tableWord #[0xff,0x7a49b705] i)
def data9 : Nat → Nat := (fun i => (if i<8 then tableWord #[0x1fe420,0x3742c858706,0x1fe460,0xf5d9cad50707,0x1fece0,0x674cad5c706,0x1ff441,0x3512c104] i else (if i<16 then tableWord #[0x1ff461,0x1a5ce41650107,0x1ff4a1,0x38102,0x1ff4e1,0x5c700504,0x1ff462,0x4d441538a06] i else tableWord #[0x1ff4c2,0x24b02,0x1ff4e2,0x51740754a06,0x1ff4e3,0xc1875375ce20309] i)))
def data8 : Nat → Nat := (fun i => (if i<16 then (if i<8 then tableWord #[0x3fc441420,0x1a45a8104,0x2fe868420,0x135a0403,0x3ee883420,0x268302,0x3ee4a4420,0x40302] i else tableWord #[0x2fed01460,0x1b0202,0x2fe428ce0,0xc8502,0x2fe468ce0,0x15cc8303,0x3ee883ce0,0x301] i) else (if i<24 then tableWord #[0x2bf8c8441,0x14bb8603,0x2df8a8462,0x43b8f03,0x3fe4a3420,0xbb402,0x3fe4c2460,0x0] i else (if i<32 then tableWord #[0x3fe462ce0,0x4da1703,0x3fe4c2ce0,0x0,0x3fe4a3ce0,0xbb402,0x3fe4c3ce0,0x1a1702] i else tableWord #[0x3fe4c5ce0,0x3501,0x2ffd034e2,0xc1702] i))))
def data7 : Nat → Nat := (fun i => (if i<8 then tableWord #[0x4ee509883ce0,0x0,0x6fc868441420,0x8d01,0x7ec883441420,0x8d01,0x5ee4a9883420,0x0] i else tableWord #[0x6ee883428ce0,0x0,0x5de8a9462ce0,0x0,0x5fad224c5ce0,0x0] i))
def levels : Nat → Packing
  | 7 => (7,3,5,0,0,0,0,data7)
  | 8 => (18,2,5,0,0,0,0,data8)
  | 9 => (11,1,5,0,0,0,0,data9)
  | 10 => (1,0,5,0,0,0,0,data10)
  | _ => (0,0,0,0,0,0,0,fun _ => 0)
def index : Nat → Nat → Option (Nat × Nat)
  | 8 => fun h => smallSlot h 4 15 3 1 (fun i => (((fun i => tableWord #[0x30] i)) (i/16) >>> (2*(i%16))) % 4) (fun i => (((fun i => tableWord #[0x1580000188e01fb0c06f8f545c4] i)) (i/16) >>> (7*(i%16))) % 128)
  | 9 => fun h => smallSlot h 9 31 5 1 (fun i => (((fun i => tableWord #[0x7600485] i)) (i/16) >>> (3*(i%16))) % 8) (fun i => (((fun i => tableWord #[0x824040000e482ca290005140083000be0f8d,0x18d2431e57395d063853d56ec0020b19c8] i)) (i/16) >>> (9*(i%16))) % 512)
  | 10 => fun h => smallSlot h 7 28 4 1 (fun i => (((fun i => tableWord #[0x2007c] i)) (i/16) >>> (3*(i%16))) % 8) (fun i => (((fun i => tableWord #[0xbc300880000d2000000c70000f85a,0xc9e275b3b1a6776104ea05b4] i)) (i/16) >>> (8*(i%16))) % 256)
  | _ => fun _ => none
def book : Forest := ⟨510,10,samples,cols,[[],[81,98,115,132]],levels,index⟩
theorem geometry : graphValid book (boundsBefore entries) = true := by decide +kernel
set_option maxRecDepth 16000 in
theorem row10_0 : CutRow book 10 0 1 := bandCut 8 false (by decide +kernel)
theorem band10 : CutRow book 10 0 1 := row10_0
set_option maxRecDepth 16000 in
theorem row9_0 : CutRow book 9 0 3 := bandCut 8 false (by decide +kernel)
set_option maxRecDepth 16000 in
theorem row9_3 : CutRow book 9 3 8 := bandCut 9 false (by decide +kernel)
theorem combine9_0_11 : CutRow book 9 0 11 := @joinRow book 9 0 3 8 row9_0 row9_3
theorem band9 : CutRow book 9 0 11 := combine9_0_11
set_option maxRecDepth 16000 in
theorem row8_0 : CutRow book 8 0 10 := bandCut 8 false (by decide +kernel)
set_option maxRecDepth 16000 in
theorem row8_10 : CutRow book 8 10 8 := bandCut 9 false (by decide +kernel)
theorem combine8_0_18 : CutRow book 8 0 18 := @joinRow book 8 0 10 8 row8_0 row8_10
theorem band8 : CutRow book 8 0 18 := combine8_0_18
set_option maxRecDepth 16000 in
theorem row7_0 : CutRow book 7 0 1 := bandCut 7 false (by decide +kernel)
set_option maxRecDepth 16000 in
theorem row7_1 : CutRow book 7 1 6 := bandCut 8 false (by decide +kernel)
theorem combine7_0_7 : CutRow book 7 0 7 := @joinRow book 7 0 1 6 row7_0 row7_1
theorem band7 : CutRow book 7 0 7 := combine7_0_7
theorem checked : mixedTables book 10 := by
  intro k hk
  interval_cases k
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact band7
  · exact band8
  · exact band9
  · exact band10
end B990_11
theorem h990_11 : Face true 510 11 :=
  mixedLower (g:=B990_11.book) (i:=0) (hints:=4886718336)
    (before_sound B990_11.entries B990_11.prior) B990_11.geometry B990_11.checked
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem h1227_7 : Face true 619 7 := carry_of (swaps:=[148,64,65,67,83,97,128]) (by decide +kernel) h723_7
theorem h1235_7 : Face true 627 7 := carry_of (swaps:=[147,131,84,50,33,113,96]) (by decide +kernel) h473_7
theorem h1241_8 : Face true 633 8 := carry_of (swaps:=[151,117,133,16,32]) (by decide +kernel) h924_8
theorem h1242_7 : Face true 634 7 := carry_of (swaps:=[149,133,117,67,16]) (by decide +kernel) h473_7
theorem h1355_7 : Face true 683 7 := carry_of (swaps:=[148,113,67,131,97,80]) (by decide +kernel) h723_7
theorem h1434_7 : Face true 730 7 := carry_of (swaps:=[149,101,134,117,65,49,16,32]) (by decide +kernel) h723_7
theorem h853_7 : Face true 437 7 := carry_of (swaps:=[132,100,50,82,112]) (by decide +kernel) h473_7
theorem h855_8 : Face true 439 8 := dropFace 2 4832167813 h853_7 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem h1498_8 : Face true 762 8 := carry_of (swaps:=[146,66,64,84,128,98,113,48]) (by decide +kernel) h855_8
theorem h1499_11 : Face true 763 11 := carry_of (swaps:=[148,65,49,116,131,32,81,96]) (by decide +kernel) h990_11
theorem h461_6 : Face true 237 6 := dropFace 33 587228933 h396_4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem h858_6 : Face true 442 6 := carry_of (swaps:=[131,82,114,48,66,96,16]) (by decide +kernel) h461_6
theorem h593_4 : Face true 305 4 := carry_of (swaps:=[134,118]) (by decide +kernel) h209_4
theorem h599_6 : Face true 311 6 := dropFace 6 4295297157 h593_4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem h984_6 : Face true 504 6 := carry_of (swaps:=[65,32,132,80,114,97,48]) (by decide +kernel) h599_6
theorem h985_8 : Face true 505 8 := carry_of (swaps:=[65,33,132,81,98,49,112]) (by decide +kernel) h855_8

namespace B987_10
def entries : List (Nat × Nat) := [(249,7),(371,7),(378,7),(442,6),(474,7),(504,6),(216,4),(505,8)]
theorem prior : Known true entries := (consFace h473_7 (consFace h723_7 (consFace h730_7 (consFace h858_6 (consFace h922_7 (consFace h984_6 (consFace h408_4 (consFace h985_8 (known_down baseKnown)))))))))
def samples : Nat → Bits × Bits := (fun i => (if i<8 then tableBits #[(padColumn 75 0x30c1881c018007fff,padColumn 75 0x10c0880c418002a87),(padColumn 75 0x33c3f01000060101800,padColumn 75 0x1141501100862921812),(padColumn 75 0x0,padColumn 75 0x0),(padColumn 75 0x4c03027fe007fe06000,padColumn 75 0x4403023da0028e46024),(padColumn 75 0xc0c6007f803f8000,padColumn 75 0x4086001100008000),(padColumn 75 0xf00780780003fffff,padColumn 75 0xe00700700003f5578),(padColumn 75 0xf0008007ffffc00000,padColumn 75 0xb0000005ee57080040),(padColumn 75 0x70000fff80000000000,padColumn 75 0x30000dc203000000180)] i else tableBits #[(padColumn 75 0x7ffff00000000000000,padColumn 75 0x6ebaa00400004000600),(padColumn 75 0x0,padColumn 75 0x0),(padColumn 75 0x0,padColumn 75 0x0)] i))
def cols : List ColumnInfo := [(256,2,249,0,7),(8,128,371,0,7),(129,0,378,0,7),(0,128,371,8,8),(65,0,442,0,6),(32,1,474,0,7),(3,0,504,0,6),(0,3,216,288,6),(2,0,505,0,8)]
def data9 : Nat → Nat := (fun i => tableWord #[0xff,0x84150206] i)
def data8 : Nat → Nat := (fun i => tableWord #[0x1ff4a3,0x0,0x1ff8a3,0x4cc703] i)
def levels : Nat → Packing
  | 8 => (2,1,4,0,0,0,0,data8)
  | 9 => (1,0,4,0,0,0,0,data9)
  | _ => (0,0,0,0,0,0,0,fun _ => 0)
def index : Nat → Nat → Option (Nat × Nat)
  | 9 => fun v => (if v=5983076478365830632 then some (1,0) else (if v=6463100887286636623 then some (0,0) else none))
  | _ => fun _ => none
def book : Forest := ⟨507,9,samples,cols,[[],[16,133]],levels,index⟩
theorem geometry : graphValid book (boundsBefore entries) = true := by decide +kernel
set_option maxRecDepth 16000 in
theorem row9_0 : CutRow book 9 0 1 := bandCut 8 false (by decide +kernel)
theorem band9 : CutRow book 9 0 1 := row9_0
set_option maxRecDepth 16000 in
theorem row8_0 : CutRow book 8 0 2 := bandCut 9 false (by decide +kernel)
theorem band8 : CutRow book 8 0 2 := row8_0
theorem checked : mixedTables book 9 := by
  intro k hk
  interval_cases k
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact band8
  · exact band9
end B987_10
theorem h987_10 : Face true 507 10 :=
  mixedLower (g:=B987_10.book) (i:=0) (hints:=5150957701)
    (before_sound B987_10.entries B987_10.prior) B987_10.geometry B987_10.checked
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem h1502_10 : Face true 766 10 := carry_of (swaps:=[149,133,117,67,16,32]) (by decide +kernel) h987_10
theorem h1619_8 : Face true 819 8 := carry_of (swaps:=[151,101,133,49,32]) (by decide +kernel) h924_8
theorem h1690_8 : Face true 858 8 := carry_of (swaps:=[118,151,134,66,33,49]) (by decide +kernel) h924_8
theorem h926_9 : Face true 478 9 := dropFace 2 4882589568 h924_8 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem h1754_9 : Face true 890 9 := carry_of (swaps:=[50,146,67,33,132,99,82,113]) (by decide +kernel) h926_9
theorem h65_1 : Face true 33 1 := countFace 5 (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem h144_1 : Face true 80 1 := carry_of (swaps:=[101,64,48,32,16]) (by decide +kernel) h65_1
theorem h81_2 : Face true 49 2 := countFace 327685 (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem h729_7 : Face true 377 7 := carry_of (swaps:=[101,133,48,32,16]) (by decide +kernel) h723_7
theorem h1089_2 : Face true 545 2 := carry_of (swaps:=[144,128,112,64,100,80]) (by decide +kernel) h81_2
theorem h1091_4 : Face true 547 4 := carry_of (swaps:=[149,133,117,101,50,33,16,64]) (by decide +kernel) h209_4
theorem h1097_4 : Face true 553 4 := carry_of (swaps:=[149,133,117,101,48,64]) (by decide +kernel) h209_4
theorem h1161_4 : Face true 585 4 := carry_of (swaps:=[149,133,117,67]) (by decide +kernel) h209_4
theorem h1162_4 : Face true 586 4 := carry_of (swaps:=[149,133,117,67,16]) (by decide +kernel) h209_4
theorem h1176_4 : Face true 600 4 := carry_of (swaps:=[150,134,101,117,64,48,32,16]) (by decide +kernel) h209_4
theorem h1539_4 : Face true 771 4 := carry_of (swaps:=[149,134,117,50,33,65]) (by decide +kernel) h209_4
theorem h1546_4 : Face true 778 4 := carry_of (swaps:=[149,134,117,48,64,16]) (by decide +kernel) h209_4
theorem h514_1 : Face true 258 1 := carry_of (swaps:=[133,117,101,16]) (by decide +kernel) h65_1
theorem h1611_7 : Face true 811 7 := carry_of (swaps:=[148,116,67,99,81,128]) (by decide +kernel) h723_7
theorem h1625_7 : Face true 825 7 := carry_of (swaps:=[117,151,133,101,48,64]) (by decide +kernel) h473_7
theorem h1626_7 : Face true 826 7 := carry_of (swaps:=[149,134,117,48,64,16]) (by decide +kernel) h473_7
theorem h1675_7 : Face true 843 7 := carry_of (swaps:=[64,144,16,113,67,131,81,96]) (by decide +kernel) h723_7

namespace B1755_12
def entries : List (Nat × Nat) := [(33,1),(80,1),(113,4),(120,4),(305,4),(49,2),(306,4),(338,4),(344,4),(371,7),(377,7),(378,7),(545,2),(547,4),(553,4),(585,4),(586,4),(600,4),(619,7),(633,8),(634,7),(771,4),(778,4),(258,1),(811,7),(819,8),(825,7),(826,7),(843,7),(858,8)]
theorem prior : Known true entries := (consFace h65_1 (consFace h144_1 (consFace h209_4 (consFace h216_4 (consFace h593_4 (consFace h81_2 (consFace h594_4 (consFace h658_4 (consFace h664_4 (consFace h723_7 (consFace h729_7 (consFace h730_7 (consFace h1089_2 (consFace h1091_4 (consFace h1097_4 (consFace h1161_4 (consFace h1162_4 (consFace h1176_4 (consFace h1227_7 (consFace h1241_8 (consFace h1242_7 (consFace h1539_4 (consFace h1546_4 (consFace h514_1 (consFace h1611_7 (consFace h1619_8 (consFace h1625_7 (consFace h1626_7 (consFace h1675_7 (consFace h1690_8 (known_down baseKnown)))))))))))))))))))))))))))))))
def samples : Nat → Bits × Bits := (fun i => (if i<8 then tableBits #[(padColumn 128 0xe0e021f31f01ee060f0f00f0080ffff,padColumn 128 0x202000f34e003e8601af60d00002251),(padColumn 128 0x701c603e03e001f80f003003001e00,padColumn 128 0x20082836412000a84fa43a03049e04),(padColumn 128 0x0,padColumn 128 0x0),(padColumn 128 0x30006181c00c01018300003ffc00e000,padColumn 128 0x2000408140048981810000135a08e808),(padColumn 128 0xc18181fe000001fe040fffc00fff0000,padColumn 128 0x408081fc210000320003388000210000),(padColumn 128 0x1fe000000fe0007f000000fffffff,padColumn 128 0x17e000000fc0007e000000fdeddae),(padColumn 128 0x1fe0000000f000007fffffff0000000,padColumn 128 0x97e0000008b100006fcc72ca0101030),(padColumn 128 0x0,padColumn 128 0x0)] i else tableBits #[(padColumn 128 0xfe000000000ffffff800000000000000,padColumn 128 0xbe080000000edfcd50800000c00000c0),(padColumn 128 0xfffffffffff000000000000000000000,padColumn 128 0xcdcd9350890000100000080000600100),(padColumn 128 0x0,padColumn 128 0x0)] i))
def cols : List ColumnInfo := [(848,10,33,0,1),(792,66,33,0,1),(808,3,80,0,1),(528,265,0,98,2),(776,2,113,0,4),(771,0,120,0,4),(769,2,120,0,4),(592,10,33,256,2),(578,8,305,0,4),(576,10,49,256,3),(577,8,306,0,4),(552,1,338,0,4),(546,1,344,0,4),(520,1,338,32,5),(520,0,371,0,7),(514,1,344,32,5),(514,0,377,0,7),(513,0,378,0,7),(26,320,545,0,2),(280,64,547,0,4),(82,256,553,0,4),(306,0,585,0,4),(50,256,585,0,4),(273,32,586,0,4),(291,0,600,0,4),(272,0,619,0,7),(258,0,633,0,8),(257,0,634,0,7),(24,98,0,769,2),(56,64,771,0,4),(81,32,778,0,4),(24,65,258,544,3),(80,0,811,0,7),(72,0,819,0,8),(66,0,825,0,7),(65,0,826,0,7),(48,0,843,0,7),(33,0,858,0,8)]
def data11 : Nat → Nat := (fun i => tableWord #[0xff,0x216a503] i)
def data10 : Nat → Nat := (fun i => (if i<8 then tableWord #[0x1ff420,0xc28028e466822508,0x1ff460,0x61b48480d32787a509,0x1ffc60,0x10a01a94819464c7a40a,0x1ff4a0,0x5a4044d214a4c62309] i else (if i<16 then tableWord #[0x1ff4e0,0x348030e156929108,0x1ffce0,0x2038d20089441108,0x1ff0e3,0x2064d241c5501108,0x1ff4e3,0x30903394d0e49690110a] i else tableWord #[0x1ff8e3,0x848194844d251c58ba00b] i)))
def data9 : Nat → Nat := bookData 2 3 3 (fun i => (((fun i => tableWord #[0x4e04e3ce04a0c604208e3460] i)) (i/16) >>> (12*(i%16))) % 4096) (fun i => (((fun i => tableWord #[0x3fffbff7bfffebfaef] i)) (i/16) >>> (10*(i%16))) % 1024) (fun i => (((fun i => tableWord #[0xce04128108e8693a1a8a8692a1a868691a1a84869121a4e0492812460491012408262200,0x4a8751a1d4c05138e34e86d0a1b8e8613a188a8612a18888a238e04e3834058c61811860,0x4a3dd38f44e5c138f04a1c118704e5ca38f24e3ca28f24a3cb18b2462c93a1940867401e,0xd00d940368a3d628f7] i)) (i/16) >>> (18*(i%16))) % 262144) (variableSlot (fun i => tablePair #[(0x27c24f22a2172041de1ca17d13811d0ef0cb0b5078064038000,0xa0689928602cc8c782c12858150b0284144c601304c0be0e0638260a141a30133051b23250f060b088160a0700882050602e88830602460205f1c13259a0d0c07c0002d191e130c05e199da0d1e0c06),(0x1fe1e01ab19517014b13811c0e70ba09507104d02701400a000,0x210a1d03a528e820408834624059200a0c04c8690060241402d1e0c039928a0306860370183c784c1664a3c1609a4a3c1809a4a1e3c0900688860241e0280601),(0x22120c1ef1c91a418716713b1170fc0e10c60ab07d04902d000,0x110f029918781c63a3c1a09e0f241104f910e81d2878b81e8882830782e828307825060f03c0a1e078143c0e028681c62612141a0b43c082c40220da3c1807411130a0c05),(0x6c057032015000,0x8878179943c44126461e0710f02)] i))
def data8 : Nat → Nat := (fun i => (if i<24 then (if i<8 then tableWord #[0x4fe128440420,0x0,0x4fe128460420,0x1e01,0x47f8e9448420,0x0,0x4ef889468420,0x1e0402] i else (if i<16 then tableWord #[0x4fb4498a8420,0x1301,0x4fed09ce0460,0x0,0x4f7128461460,0x0,0x4efd244a8460,0x1701] i else tableWord #[0x4efd244e8460,0x0,0x4fbd224a8ce0,0x1301,0x7fc461460420,0x24a1702,0x4ff869448420,0x0] i)) else (if i<32 then tableWord #[0x67f4e58e8420,0xd01,0x5df8a9462420,0x0,0x5fb4498e3420,0x0,0x5fbd224e5420,0x0] i else (if i<40 then tableWord #[0x6ef888461460,0x11b01,0x6ef8884a1460,0x0,0x7774e54e3460,0xf01,0x6ef8884e3460,0x0] i else tableWord #[0x6ef4e5888460,0xd01,0x4ff4e98a8460,0x0,0x4ff5098a3ce0,0x0,0x5efd245004e3,0x0] i))))
def data7 : Nat → Nat := (fun i => tableWord #[0xcaf8c9888461460,0x0,0xaebd424e5888460,0x0] i)
def levels : Nat → Packing
  | 7 => (2,4,6,0,0,0,0,data7)
  | 8 => (24,3,6,0,0,0,0,data8)
  | 9 => (52,2,6,0,0,0,0,data9)
  | 10 => (9,1,6,0,0,0,0,data10)
  | 11 => (1,0,6,0,0,0,0,data11)
  | _ => (0,0,0,0,0,0,0,fun _ => 0)
def index : Nat → Nat → Option (Nat × Nat)
  | 8 => fun v => (if v=7025981528652627411 then some (1,0) else (if v=5611940961228524796 then some (0,0) else none))
  | 9 => fun h => smallSlot h 12 43 5 4 (fun i => (((fun i => tableWord #[0x990221a4001806b] i)) (i/16) >>> (5*(i%16))) % 32) (fun i => (((fun i => tableWord #[0xa10c0f401e07000216e5100063380b00021100020cf30,0xe44014e04c1221543533560300500001726f000000002609,0x26e41343120d618e0600a40860ec32] i)) (i/16) >>> (12*(i%16))) % 4096)
  | 10 => fun h => smallSlot h 48 173 6 4 (fun i => (((fun i => tableWord #[0x1e061082e0200c328424,0x46428948e0784100520,0x812218089010b5065c6] i)) (i/16) >>> (5*(i%16))) % 32) (fun i => (((fun i => (if i<8 then tableWord #[0xb5980015688577762050038805a5a0000000cad00150c2d29434,0xc00c020ccf912617a083b32807a0d9a7784cc3108e800210b816,0x60640948b0068a12700e1d1e6668ad09e02a41884ee046059432,0x2169180066000c378000834c86004f40b95800b0085118000049,0x27291c08e5c6c6d0892d132000a8c90a88dc534002707c25b00a,0x4348001de31b3e38c9a2909853f10e3a6432000916d0ad8a2000,0x26800000199d60b92bc00080d127801a03ce1401080010a4882,0xe50f16fadedadc7233bf1078120007a6603a000211a652542c94] i else tableWord #[0x36ba1ac12400070ed8780269330000000000c28000703c48a80e,0xa14800355b044000148a145cb3a4ac8d28440004278000368000,0x114d3544bda42819cd469c4000000c1767a0c66257] i))) (i/16) >>> (13*(i%16))) % 8192)
  | 11 => fun h => smallSlot h 14 48 4 4 (fun i => (((fun i => tableWord #[0x10040080020f3805c0140] i)) (i/16) >>> (6*(i%16))) % 64) (fun i => (((fun i => tableWord #[0xa49d1521844a8d98c9a505000e880000084569bc1823,0x24ad84348001234474158634b01000000a0cd0800207,0x8a9c04b3062ae34218a16560628c00185a6309901009] i)) (i/16) >>> (11*(i%16))) % 2048)
  | _ => fun _ => none
def book : Forest := ⟨891,11,samples,cols,[[],[49,134],[16,133],[16,48,133,101],[48,16,101,133],[48,101],[80,97,131,148],[80,129,99,148],[96,81,131,148,49,16],[96,129,83,148],[128,81,99,148],[128,97,83,148,49,48]],levels,index⟩
theorem geometry : graphValid book (boundsBefore entries) = true := by decide +kernel
set_option maxRecDepth 16000 in
theorem row11_0 : CutRow book 11 0 1 := bandCut 8 false (by decide +kernel)
theorem band11 : CutRow book 11 0 1 := row11_0
set_option maxRecDepth 16000 in
theorem row10_0 : CutRow book 10 0 9 := bandCut 9 false (by decide +kernel)
theorem band10 : CutRow book 10 0 9 := row10_0
set_option maxRecDepth 16000 in
theorem row9_0 : CutRow book 9 0 2 := bandCut 8 false (by decide +kernel)
set_option maxRecDepth 16000 in
theorem row9_2 : CutRow book 9 2 33 := bandCut 9 true (by decide +kernel)
set_option maxRecDepth 16000 in
theorem row9_35 : CutRow book 9 35 17 := bandCut 10 false (by decide +kernel)
theorem combine9_0_35 : CutRow book 9 0 35 := @joinRow book 9 0 2 33 row9_0 row9_2
theorem combine9_0_52 : CutRow book 9 0 52 := @joinRow book 9 0 35 17 combine9_0_35 row9_35
theorem band9 : CutRow book 9 0 52 := combine9_0_52
set_option maxRecDepth 16000 in
theorem row8_0 : CutRow book 8 0 10 := bandCut 8 false (by decide +kernel)
set_option maxRecDepth 16000 in
theorem row8_10 : CutRow book 8 10 14 := bandCut 9 false (by decide +kernel)
theorem combine8_0_24 : CutRow book 8 0 24 := @joinRow book 8 0 10 14 row8_0 row8_10
theorem band8 : CutRow book 8 0 24 := combine8_0_24
set_option maxRecDepth 16000 in
theorem row7_0 : CutRow book 7 0 2 := bandCut 8 false (by decide +kernel)
theorem band7 : CutRow book 7 0 2 := row7_0
theorem checked : mixedTables book 11 := by
  intro k hk
  interval_cases k
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact band7
  · exact band8
  · exact band9
  · exact band10
  · exact band11
end B1755_12
theorem h1755_12 : Face true 891 12 :=
  mixedLower (g:=B1755_12.book) (i:=0) (hints:=4345651333)
    (before_sound B1755_12.entries B1755_12.prior) B1755_12.geometry B1755_12.checked
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem h477_8 : Face true 253 8 := dropFace 4 587556613 h473_7 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem h1863_8 : Face true 935 8 := carry_of (swaps:=[67,147,132,49,114,97,80]) (by decide +kernel) h477_8
theorem h725_7 : Face true 373 7 := carry_of (swaps:=[33]) (by decide +kernel) h723_7
theorem h732_7 : Face true 380 7 := carry_of (swaps:=[101,16,49,32]) (by decide +kernel) h723_7
theorem h845_6 : Face true 429 6 := carry_of (swaps:=[50,131,99,114]) (by decide +kernel) h461_6
theorem h981_8 : Face true 501 8 := carry_of (swaps:=[132,97,82,49,112]) (by decide +kernel) h855_8
theorem h988_9 : Face true 508 9 := carry_of (swaps:=[50,67,132,99,114,81]) (by decide +kernel) h926_9

namespace B989_11
def entries : List (Nat × Nat) := [(113,4),(120,4),(204,4),(237,6),(249,7),(305,4),(308,4),(340,4),(373,7),(377,7),(369,5),(380,7),(396,4),(429,6),(437,7),(444,7),(476,8),(501,8),(505,8),(508,9)]
theorem prior : Known true entries := (consFace h209_4 (consFace h216_4 (consFace h396_4 (consFace h461_6 (consFace h473_7 (consFace h593_4 (consFace h596_4 (consFace h660_4 (consFace h725_7 (consFace h729_7 (consFace h721_5 (consFace h732_7 (consFace h780_4 (consFace h845_6 (consFace h853_7 (consFace h860_7 (consFace h924_8 (consFace h981_8 (consFace h985_8 (consFace h988_9 (known_down baseKnown)))))))))))))))))))))
def samples : Nat → Bits × Bits := (fun i => (if i<8 then tableBits #[(padColumn 102 0x1a18003011830e060003fff,padColumn 102 0xa19001011814e860001691),(padColumn 102 0x0,padColumn 102 0x0),(padColumn 102 0x3e07e39c1e1e070180380e00,padColumn 102 0x140361080a0a07818ab10e04),(padColumn 102 0x6c0460020e1e0c801ffc03000,padColumn 102 0x44046400040404800b3e03408),(padColumn 102 0x3900781c40fe010ffe00ffc000,padColumn 102 0x1000080400fc00093400004000),(padColumn 102 0x780007f0001f00000ffffff,padColumn 102 0x700007e0001e00000ffa96e),(padColumn 102 0x1f8001f800001ffffff000000,padColumn 102 0x1b8001b800001b6c94c020030),(padColumn 102 0x3e00001ffffffe000000000000,padColumn 102 0x3800001e539094001000040040)] i else tableBits #[(padColumn 102 0x3fffffe0000000000000000000,padColumn 102 0x27e19400000000000010000180),(padColumn 102 0x0,padColumn 102 0x0),(padColumn 102 0x0,padColumn 102 0x0)] i))
def cols : List ColumnInfo := [(268,128,113,0,4),(385,4,120,0,4),(260,128,113,8,5),(256,128,113,12,6),(304,1,204,0,4),(273,32,204,0,4),(272,0,237,0,6),(264,4,113,128,5),(260,0,249,0,7),(196,8,305,0,4),(76,128,305,0,4),(193,8,308,0,4),(64,128,305,12,6),(168,1,340,0,4),(136,4,113,256,5),(136,0,373,0,7),(132,0,377,0,7),(4,128,369,8,6),(129,0,380,0,7),(0,128,369,12,7),(112,1,396,0,4),(81,32,396,0,4),(80,32,396,1,5),(80,0,429,0,6),(72,0,437,0,7),(65,0,444,0,7),(32,1,476,0,8),(8,0,501,0,8),(1,4,120,384,6),(4,0,505,0,8),(1,0,508,0,9),(0,1,476,32,9)]
def data10 : Nat → Nat := (fun i => tableWord #[0xff,0x1fe4431a06] i)
def data9 : Nat → Nat := (fun i => (if i<8 then tableWord #[0x1ff441,0x1c4ba00b05,0x1ff461,0xde8920105,0x1ffc61,0x177d938505,0x1ff4a1,0x3a24103] i else (if i<16 then tableWord #[0x1ff4a3,0x4c725504,0x1ff8a3,0x679f44161507,0x1ff4c3,0x313a48a05,0x1ff8c3,0x75b79f01506] i else tableWord #[0x1ff4c5,0x6fa08b04,0x1ff4e5,0xd231463a21908] i)))
def data8 : Nat → Nat := (fun i => (if i<8 then tableWord #[0x2bf8c8441,0x3f7a02,0x27f8e8461,0x3f7a02,0x2fd4288c3,0x1601,0x2fbd024c5,0x3f7a02] i else (if i<16 then tableWord #[0x2ff8a8461,0x0,0x3df4e54a3,0x1701,0x2ff4e84a3,0x0,0x3df4c58a3,0x605df03] i else tableWord #[0x2ffd034e5,0x7f01] i)))
def levels : Nat → Packing
  | 8 => (9,2,5,0,0,0,0,data8)
  | 9 => (10,1,5,0,0,0,0,data9)
  | 10 => (1,0,5,0,0,0,0,data10)
  | _ => (0,0,0,0,0,0,0,fun _ => 0)
def index : Nat → Nat → Option (Nat × Nat)
  | 9 => fun h => smallSlot h 4 16 4 1 (fun i => (((fun i => tableWord #[0x191] i)) (i/16) >>> (3*(i%16))) % 8) (fun i => (((fun i => tableWord #[0x560000f364e728830062c109a5a6] i)) (i/16) >>> (8*(i%16))) % 256)
  | 10 => fun h => smallSlot h 6 21 4 1 (fun i => (((fun i => tableWord #[0xb20336] i)) (i/16) >>> (4*(i%16))) % 16) (fun i => (((fun i => tableWord #[0xc645b407b322c10955000068d600d2c4,0x196a000083] i)) (i/16) >>> (8*(i%16))) % 256)
  | _ => fun _ => none
def book : Forest := ⟨509,10,samples,cols,[[],[50,134]],levels,index⟩
theorem geometry : graphValid book (boundsBefore entries) = true := by decide +kernel
set_option maxRecDepth 16000 in
theorem row10_0 : CutRow book 10 0 1 := bandCut 8 false (by decide +kernel)
theorem band10 : CutRow book 10 0 1 := row10_0
set_option maxRecDepth 16000 in
theorem row9_0 : CutRow book 9 0 10 := bandCut 9 false (by decide +kernel)
theorem band9 : CutRow book 9 0 10 := row9_0
set_option maxRecDepth 16000 in
theorem row8_0 : CutRow book 8 0 4 := bandCut 8 false (by decide +kernel)
set_option maxRecDepth 16000 in
theorem row8_4 : CutRow book 8 4 5 := bandCut 9 false (by decide +kernel)
theorem combine8_0_9 : CutRow book 8 0 9 := @joinRow book 8 0 4 5 row8_0 row8_4
theorem band8 : CutRow book 8 0 9 := combine8_0_9
theorem checked : mixedTables book 10 := by
  intro k hk
  interval_cases k
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact band8
  · exact band9
  · exact band10
end B989_11
theorem h989_11 : Face true 509 11 :=
  mixedLower (g:=B989_11.book) (i:=0) (hints:=9177491205)
    (before_sound B989_11.entries B989_11.prior) B989_11.geometry B989_11.checked
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem h1879_11 : Face true 951 11 := carry_of (swaps:=[66,148,50,100,49,82,129,112]) (by decide +kernel) h989_11
theorem h1882_8 : Face true 954 8 := carry_of (swaps:=[64,144,50,116,83,130,96,16]) (by decide +kernel) h477_8
theorem h1950_12 : Face true 990 12 := carry_of (swaps:=[65,67,112,100,147,80,129,32]) (by decide +kernel) h1755_12
theorem h839_6 : Face true 423 6 := carry_of (swaps:=[131,49,114,97]) (by decide +kernel) h461_6
theorem h597_5 : Face true 309 5 := carry_of (swaps:=[133,117,101,32,48]) (by decide +kernel) h217_5
theorem h469_6 : Face true 245 6 := carry_of (swaps:=[83,115,67,32,96]) (by decide +kernel) h461_6

namespace B983_10
def entries : List (Nat × Nat) := [(113,4),(245,6),(371,7),(373,7),(390,4),(423,6),(437,7),(438,7),(470,7)]
theorem prior : Known true entries := (consFace h209_4 (consFace h469_6 (consFace h723_7 (consFace h725_7 (consFace h774_4 (consFace h839_6 (consFace h853_7 (consFace h854_7 (consFace h918_7 (known_down baseKnown))))))))))
def samples : Nat → Bits × Bits := (fun i => (if i<8 then tableBits #[(padColumn 78 0x601800618ce0007fff,padColumn 78 0x2818002184ec002aa3),(padColumn 78 0x37909fc0060100201800,padColumn 78 0x12800b44064188ae1808),(padColumn 78 0xe0199ff200c06000,padColumn 78 0xa0088a9202c46012),(padColumn 78 0x0,padColumn 78 0x0),(padColumn 78 0x81f00261803ffff8000,padColumn 78 0x1300a0180333008000),(padColumn 78 0x1e00007e00c00ffffff,padColumn 78 0x1c00007c00800ff555c),(padColumn 78 0xe000038000fff000000,padColumn 78 0x6000118000ccc000060),(padColumn 78 0x3000003ffff000000000,padColumn 78 0x30020237756010080180)] i else tableBits #[(padColumn 78 0x3fffffc0000000000000,padColumn 78 0x2d6c5400000000100600),(padColumn 78 0x0,padColumn 78 0x0),(padColumn 78 0x0,padColumn 78 0x0)] i))
def cols : List ColumnInfo := [(256,6,113,128,5),(256,2,245,0,6),(4,128,371,0,7),(130,0,373,0,7),(16,96,390,1,5),(16,64,423,0,6),(66,0,437,0,7),(65,0,438,0,7),(32,1,470,0,7)]
def data9 : Nat → Nat := (fun i => tableWord #[0xff,0x537128607] i)
def data8 : Nat → Nat := (fun i => tableWord #[0x1fd461,0x8002,0x1fdce1,0x5f0003,0x1ff4e3,0x142603] i)
def data7 : Nat → Nat := (fun i => tableWord #[0x2fd468ce1,0x0,0x3dd8a3ce1,0x0] i)
def data6 : Nat → Nat := (fun i => tableWord #[0x4dd5098a3ce1,0x0] i)
def levels : Nat → Packing
  | 6 => (1,3,4,0,0,0,0,data6)
  | 7 => (2,2,4,0,0,0,0,data7)
  | 8 => (3,1,4,0,0,0,0,data8)
  | 9 => (1,0,4,0,0,0,0,data9)
  | _ => (0,0,0,0,0,0,0,fun _ => 0)
def index : Nat → Nat → Option (Nat × Nat)
  | 7 => fun v => (if v=7180117499260788955 then some (0,0) else none)
  | 8 => fun v => (if v=7400630320253988423 then some (1,0) else (if v=6262894976702743078 then some (0,0) else none))
  | 9 => fun h => smallSlot h 2 9 2 1 (fun i => (((fun i => tableWord #[0x0] i)) (i/16) >>> (1*(i%16))) % 2) (fun i => (((fun i => tableWord #[0x163066000e80] i)) (i/16) >>> (6*(i%16))) % 64)
  | _ => fun _ => none
def book : Forest := ⟨503,9,samples,cols,[[],[112,97,82,132]],levels,index⟩
theorem geometry : graphValid book (boundsBefore entries) = true := by decide +kernel
set_option maxRecDepth 16000 in
theorem row9_0 : CutRow book 9 0 1 := bandCut 8 false (by decide +kernel)
theorem band9 : CutRow book 9 0 1 := row9_0
set_option maxRecDepth 16000 in
theorem row8_0 : CutRow book 8 0 2 := bandCut 8 false (by decide +kernel)
set_option maxRecDepth 16000 in
theorem row8_2 : CutRow book 8 2 1 := bandCut 9 false (by decide +kernel)
theorem combine8_0_3 : CutRow book 8 0 3 := @joinRow book 8 0 2 1 row8_0 row8_2
theorem band8 : CutRow book 8 0 3 := combine8_0_3
set_option maxRecDepth 16000 in
theorem row7_0 : CutRow book 7 0 2 := bandCut 8 false (by decide +kernel)
theorem band7 : CutRow book 7 0 2 := row7_0
set_option maxRecDepth 16000 in
theorem row6_0 : CutRow book 6 0 1 := bandCut 7 false (by decide +kernel)
theorem band6 : CutRow book 6 0 1 := row6_0
theorem checked : mixedTables book 9 := by
  intro k hk
  interval_cases k
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact band6
  · exact band7
  · exact band8
  · exact band9
end B983_10
theorem h983_10 : Face true 503 10 :=
  mixedLower (g:=B983_10.book) (i:=0) (hints:=4899276677)
    (before_sound B983_10.entries B983_10.prior) B983_10.geometry B983_10.checked
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem h1289_4 : Face true 649 4 := carry_of (swaps:=[149,101,134,117,67]) (by decide +kernel) h209_4
theorem h1290_4 : Face true 650 4 := carry_of (swaps:=[149,101,134,117,67,16]) (by decide +kernel) h209_4
theorem h1292_4 : Face true 652 4 := carry_of (swaps:=[150,134,117,67,32,16]) (by decide +kernel) h209_4
theorem h1351_6 : Face true 679 6 := carry_of (swaps:=[147,131,82,49,32,97,112]) (by decide +kernel) h461_6
theorem h1357_7 : Face true 685 7 := carry_of (swaps:=[150,134,117,66,32,48]) (by decide +kernel) h473_7
theorem h1293_5 : Face true 653 5 := carry_of (swaps:=[149,101,134,117,66,50]) (by decide +kernel) h217_5
theorem h1487_10 : Face true 751 10 := carry_of (swaps:=[148,67,131,114,97,80]) (by decide +kernel) h983_10
theorem h1501_11 : Face true 765 11 := carry_of (swaps:=[150,134,117,66,32,48]) (by decide +kernel) h989_11
theorem h1607_7 : Face true 807 7 := carry_of (swaps:=[101,149,134,117,33,32,65,48]) (by decide +kernel) h473_7
theorem h1751_11 : Face true 887 11 := carry_of (swaps:=[147,132,48,82,97,112]) (by decide +kernel) h990_11
theorem h1799_7 : Face true 903 7 := carry_of (swaps:=[147,132,66,49,82,97,112]) (by decide +kernel) h473_7
theorem h1871_11 : Face true 943 11 := carry_of (swaps:=[66,50,147,65,99,114,129,80]) (by decide +kernel) h989_11
theorem h861_8 : Face true 445 8 := carry_of (swaps:=[134,117,48,64,32]) (by decide +kernel) h477_8
theorem h1105_4 : Face true 561 4 := carry_of (swaps:=[150,134,118,64]) (by decide +kernel) h209_4
theorem h1369_7 : Face true 697 7 := carry_of (swaps:=[150,134,64]) (by decide +kernel) h473_7
theorem h1621_7 : Face true 821 7 := carry_of (swaps:=[151,133,101,32,48]) (by decide +kernel) h473_7
theorem h1805_7 : Face true 909 7 := carry_of (swaps:=[64,147,132,66,99,82,112]) (by decide +kernel) h473_7
theorem h1820_7 : Face true 924 7 := carry_of (swaps:=[144,131,116,83,96,32,16]) (by decide +kernel) h473_7
theorem h796_5 : Face true 412 5 := carry_of (swaps:=[101,134,117,64,32,16]) (by decide +kernel) h217_5

namespace B1885_11
def entries : List (Nat × Nat) := [(396,4),(404,4),(437,7),(444,7),(445,8),(561,4),(685,7),(697,7),(305,4),(821,7),(825,7),(909,7),(924,7),(412,5)]
theorem prior : Known true entries := (consFace h780_4 (consFace h788_4 (consFace h853_7 (consFace h860_7 (consFace h861_8 (consFace h1105_4 (consFace h1357_7 (consFace h1369_7 (consFace h593_4 (consFace h1621_7 (consFace h1625_7 (consFace h1805_7 (consFace h1820_7 (consFace h796_5 (known_down baseKnown)))))))))))))))
def samples : Nat → Bits × Bits := (fun i => (if i<8 then tableBits #[(padColumn 80 0x33839e1c7018c3000fff,padColumn 80 0x21010e0c7408c32004e7),(padColumn 80 0x0,padColumn 80 0x0),(padColumn 80 0x4c005821fe6303f40380,padColumn 80 0x44005c209e2101b40392),(padColumn 80 0x801c60c18084fc080c00,padColumn 80 0x102041c00054084e04),(padColumn 80 0x6781060107000ff000,padColumn 80 0x278102000700011000),(padColumn 80 0x78003801f8000fffff,padColumn 80 0x58003001f0000eeb18),(padColumn 80 0x0,padColumn 80 0x0),(padColumn 80 0xf8001c001fffff00000,padColumn 80 0xb80018001deaa408020)] i else tableBits #[(padColumn 80 0xf00001fffe0000000000,padColumn 80 0xb00000dd600030000040),(padColumn 80 0xfffffe00000000000000,padColumn 80 0x4e625000080000830000),(padColumn 80 0x0,padColumn 80 0x0)] i))
def cols : List ColumnInfo := [(560,1,396,0,4),(41,512,404,0,4),(520,0,437,0,7),(513,0,444,0,7),(512,0,445,0,8),(392,4,561,0,4),(268,128,561,0,4),(272,0,685,0,7),(260,0,697,0,7),(132,8,305,512,5),(136,0,821,0,7),(132,0,825,0,7),(48,0,909,0,7),(33,0,924,0,7),(0,1,412,544,7)]
def data10 : Nat → Nat := (fun i => tableWord #[0xff,0x38ac27bd08] i)
def data9 : Nat → Nat := (fun i => tableWord #[0x1ff420,0x502,0x1ff440,0x2392104,0x1ff4a0,0x602] i)
def data8 : Nat → Nat := (fun i => tableWord #[0x27f8e8440,0x0] i)
def levels : Nat → Packing
  | 8 => (1,2,4,0,0,0,0,data8)
  | 9 => (3,1,4,0,0,0,0,data9)
  | 10 => (1,0,4,0,0,0,0,data10)
  | _ => (0,0,0,0,0,0,0,fun _ => 0)
def index : Nat → Nat → Option (Nat × Nat)
  | 9 => fun v => (if v=6857493274592517248 then some (0,0) else none)
  | 10 => fun h => smallSlot h 7 28 2 4 (fun i => (((fun i => tableWord #[0x47100a] i)) (i/16) >>> (4*(i%16))) % 16) (fun i => (((fun i => tableWord #[0x3054b00604000003c4e1f5b0fc1b4ce1,0x41d2a2f4e3700363a2004a8a200] i)) (i/16) >>> (9*(i%16))) % 512)
  | _ => fun _ => none
def book : Forest := ⟨957,10,samples,cols,[[],[67,149,135],[32,133,151],[32,67,117,152],[48,66,117],[48,66,32,149,135,117],[64,50,32,133,151,117],[64,50,152],[80,114,131,148],[80,114,147,132,64,50,32],[112,82,131,148,50,64,32],[112,82,147,132],[128,146,83,116,50,64,67],[128,146,115,84],[144,130,83,116],[144,130,115,84,64,50,67]],levels,index⟩
theorem geometry : graphValid book (boundsBefore entries) = true := by decide +kernel
set_option maxRecDepth 16000 in
theorem row10_0 : CutRow book 10 0 1 := bandCut 8 false (by decide +kernel)
theorem band10 : CutRow book 10 0 1 := row10_0
set_option maxRecDepth 16000 in
theorem row9_0 : CutRow book 9 0 3 := bandCut 9 false (by decide +kernel)
theorem band9 : CutRow book 9 0 3 := row9_0
set_option maxRecDepth 16000 in
theorem row8_0 : CutRow book 8 0 1 := bandCut 8 false (by decide +kernel)
theorem band8 : CutRow book 8 0 1 := row8_0
theorem checked : mixedTables book 10 := by
  intro k hk
  interval_cases k
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact band8
  · exact band9
  · exact band10
end B1885_11
theorem h1885_11 : Face true 957 11 :=
  mixedLower (g:=B1885_11.book) (i:=0) (hints:=9127163653)
    (before_sound B1885_11.entries B1885_11.prior) B1885_11.geometry B1885_11.checked
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem h1359_8 : Face true 687 8 := carry_of (swaps:=[152,117,67,32]) (by decide +kernel) h855_8
theorem h1373_8 : Face true 701 8 := carry_of (swaps:=[150,134,64]) (by decide +kernel) h477_8
theorem h1631_10 : Face true 831 10 := dropFace 12 4295334021 h1619_8 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem h1806_8 : Face true 910 8 := carry_of (swaps:=[134,150,50,65]) (by decide +kernel) h924_8
theorem h1823_10 : Face true 927 10 := carry_of (swaps:=[152,117,101,67,32]) (by decide +kernel) h1631_10
theorem h1883_11 : Face true 955 11 := carry_of (swaps:=[64,144,116,83,33,129,96]) (by decide +kernel) h989_11
theorem h1886_11 : Face true 958 11 := carry_of (swaps:=[146,64,84,115,98,128,16]) (by decide +kernel) h989_11

namespace B1887_13
def entries : List (Nat × Nat) := [(308,4),(404,4),(438,7),(445,8),(553,4),(687,8),(697,7),(701,8),(819,8),(831,10),(910,8),(927,10),(943,11),(951,11),(955,11),(957,11),(958,11)]
theorem prior : Known true entries := (consFace h596_4 (consFace h788_4 (consFace h854_7 (consFace h861_8 (consFace h1097_4 (consFace h1359_8 (consFace h1369_7 (consFace h1373_8 (consFace h1619_8 (consFace h1631_10 (consFace h1806_8 (consFace h1823_10 (consFace h1871_11 (consFace h1879_11 (consFace h1883_11 (consFace h1885_11 (consFace h1886_11 (known_down baseKnown))))))))))))))))))
def samples : Nat → Bits × Bits := (fun i => (if i<8 then tableBits #[(padColumn 105 0x38830a068060610180003ffff,padColumn 105 0x18810a02c060210180001550f),(padColumn 105 0x411c34790c780206004003000,padColumn 105 0x10042804280226144103022),(padColumn 105 0x18600b80013818c07fe800c000,padColumn 105 0x8200b80002808402a6820c044),(padColumn 105 0x60000c1801c0213f8010030000,padColumn 105 0x2000040801d000048010430088),(padColumn 105 0x18006f0001e0041c0001ffc0000,padColumn 105 0x8002f000120001c00001040000),(padColumn 105 0x70001e0007e00001fffffff,padColumn 105 0x50001c0007c00001efaaaf0),(padColumn 105 0x0,padColumn 105 0x0),(padColumn 105 0x78001e00007fffffe0000000,padColumn 105 0x580016000077bb5580800300)] i else tableBits #[(padColumn 105 0x1ff80001fffff80000000000000,padColumn 105 0x17700001d6d95000c0000000c00),(padColumn 105 0x1ffffffe0000000000000000000,padColumn 105 0x1de66aa00002000000603000000),(padColumn 105 0x0,padColumn 105 0x0)] i))
def cols : List ColumnInfo := [(137,512,308,2,5),(43,512,404,0,4),(41,512,404,2,5),(521,0,438,0,7),(514,0,445,0,8),(150,256,553,0,4),(148,256,553,2,5),(272,0,687,0,8),(262,0,697,0,7),(258,0,701,0,8),(12,128,819,0,8),(128,0,831,0,10),(0,128,819,12,10),(17,32,910,0,8),(16,32,910,1,9),(32,0,927,0,10),(0,32,910,17,10),(16,0,943,0,11),(8,0,951,0,11),(4,0,955,0,11),(2,0,957,0,11),(1,0,958,0,11)]
def data12 : Nat → Nat := (fun i => tableWord #[0x1ff,0xb94df1ad14d09] i)
def data11 : Nat → Nat := (fun i => tableWord #[0x3ff107,0x2fc0b30f4070c809,0x3ff507,0x50b30fb31cced74cad0c814110,0x3ff907,0x2c2cc3d0c32d430070880d] i)
def data10 : Nat → Nat := (fun i => tableWord #[0x5fdd21507,0x3a84e5b428106,0x7fdd21507,0x2430103,0x5ff509907,0x2430103] i)
def data9 : Nat → Nat := (fun i => tableWord #[0x9fdd41509907,0x0] i)
def levels : Nat → Packing
  | 9 => (1,3,5,0,0,0,0,data9)
  | 10 => (3,2,5,0,0,0,0,data10)
  | 11 => (3,1,5,0,0,0,0,data11)
  | 12 => (1,0,5,0,0,0,0,data12)
  | _ => (0,0,0,0,0,0,0,fun _ => 0)
def index : Nat → Nat → Option (Nat × Nat)
  | 10 => fun v => (if v=6519371802217686780 then some (0,0) else none)
  | 11 => fun v => (if v=8213273995398048448 then some (2,0) else (if v=8521536674887730965 then some (1,0) else (if v=6519371802217686780 then some (0,0) else none)))
  | 12 => fun h => smallSlot h 2 8 2 1 (fun i => (((fun i => tableWord #[0x1] i)) (i/16) >>> (1*(i%16))) % 2) (fun i => (((fun i => tableWord #[0x174408a3] i)) (i/16) >>> (6*(i%16))) % 64)
  | _ => fun _ => none
def book : Forest := ⟨959,12,samples,cols,[[],[32,67,117,152],[48,66,117],[64,50,152]],levels,index⟩
theorem geometry : graphValid book (boundsBefore entries) = true := by decide +kernel
set_option maxRecDepth 16000 in
theorem row12_0 : CutRow book 12 0 1 := bandCut 9 false (by decide +kernel)
theorem band12 : CutRow book 12 0 1 := row12_0
set_option maxRecDepth 16000 in
theorem row11_0 : CutRow book 11 0 3 := bandCut 10 false (by decide +kernel)
theorem band11 : CutRow book 11 0 3 := row11_0
set_option maxRecDepth 16000 in
theorem row10_0 : CutRow book 10 0 1 := bandCut 9 false (by decide +kernel)
set_option maxRecDepth 16000 in
theorem row10_1 : CutRow book 10 1 2 := bandCut 10 false (by decide +kernel)
theorem combine10_0_3 : CutRow book 10 0 3 := @joinRow book 10 0 1 2 row10_0 row10_1
theorem band10 : CutRow book 10 0 3 := combine10_0_3
set_option maxRecDepth 16000 in
theorem row9_0 : CutRow book 9 0 1 := bandCut 9 false (by decide +kernel)
theorem band9 : CutRow book 9 0 1 := row9_0
theorem checked : mixedTables book 12 := by
  intro k hk
  interval_cases k
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact band9
  · exact band10
  · exact band11
  · exact band12
end B1887_13
theorem h1887_13 : Face true 959 13 :=
  mixedLower (g:=B1887_13.book) (i:=0) (hints:=4832196485)
    (before_sound B1887_13.entries B1887_13.prior) B1887_13.geometry B1887_13.checked
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem h1935_11 : Face true 975 11 := carry_of (swaps:=[148,64,131,114,97,80]) (by decide +kernel) h990_11
theorem h1759_13 : Face true 895 13 := dropFace 4 4345653381 h1755_12 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem h2011_13 : Face true 1019 13 := carry_of (swaps:=[148,131,114,97,80]) (by decide +kernel) h1759_13
theorem h2013_13 : Face true 1021 13 := carry_of (swaps:=[148,131,114,97,80]) (by decide +kernel) h1887_13
theorem h2014_13 : Face true 1022 13 := carry_of (swaps:=[132,147,82,97,112]) (by decide +kernel) h1759_13

namespace B2015_15
def entries : List (Nat × Nat) := [(249,7),(252,7),(305,4),(306,4),(308,4),(380,7),(390,4),(404,4),(423,6),(476,8),(462,7),(309,5),(503,10),(509,11),(547,4),(553,4),(585,4),(627,7),(633,8),(649,4),(650,4),(652,4),(679,6),(685,7),(653,5),(751,10),(763,11),(765,11),(253,8),(807,7),(819,8),(826,7),(858,8),(887,11),(891,12),(903,7),(935,8),(943,11),(951,11),(957,11),(959,13),(975,11),(990,12),(1019,13),(1021,13),(1022,13)]
theorem prior : Known true entries := (consFace h473_7 (consFace h476_7 (consFace h593_4 (consFace h594_4 (consFace h596_4 (consFace h732_7 (consFace h774_4 (consFace h788_4 (consFace h839_6 (consFace h924_8 (consFace h910_7 (consFace h597_5 (consFace h983_10 (consFace h989_11 (consFace h1091_4 (consFace h1097_4 (consFace h1161_4 (consFace h1235_7 (consFace h1241_8 (consFace h1289_4 (consFace h1290_4 (consFace h1292_4 (consFace h1351_6 (consFace h1357_7 (consFace h1293_5 (consFace h1487_10 (consFace h1499_11 (consFace h1501_11 (consFace h477_8 (consFace h1607_7 (consFace h1619_8 (consFace h1626_7 (consFace h1690_8 (consFace h1751_11 (consFace h1755_12 (consFace h1799_7 (consFace h1863_8 (consFace h1871_11 (consFace h1879_11 (consFace h1885_11 (consFace h1887_13 (consFace h1935_11 (consFace h1950_12 (consFace h2011_13 (consFace h2013_13 (consFace h2014_13 (known_down baseKnown)))))))))))))))))))))))))))))))))))))))))))))))
def samples : Nat → Bits × Bits := (fun i => (if i<8 then tableBits #[(padColumn 166 0x10840030305000030f0300600c06403000007ffff,padColumn 166 0x10840010305000010f0300200c024830000055287),(padColumn 166 0x10009c0c1a0e0ec101bc000300080c0008003000,padColumn 166 0x880c020406410094000314080c0488203012),(padColumn 166 0x2600000f01c0000020640d8e3fe1030001000c000,padColumn 166 0x2200000f01c000002024048a1461030091040c024),(padColumn 166 0xc808f60ffe030700c0780011c01803fffe0070000,padColumn 166 0x40003203fe010300ca780001c01001521e0870040),(padColumn 166 0x3007307f0000c1810ff80321e0001fc0003ff80000,padColumn 166 0x1002107faa40400007380201e80003400002080000),(padColumn 166 0x3f8000000001f000003e0001e000003fffffff,padColumn 166 0x2f8000000001e000003c0001c000003df2ad78),(padColumn 166 0x7c000000001fe000003c00001ffffffc0000000,padColumn 166 0x4c0000000014c000000c0000064aace00000180),(padColumn 166 0xf800000000fe00000003fffffe00000000000000,padColumn 166 0xd800000000ee00000003b742b801000000000600)] i else tableBits #[(padColumn 166 0x3f0000000000fffffffffc00000000000000000000,padColumn 166 0x2d000a000080b9e9b8c52800100000007001040800),(padColumn 166 0x3fffffffffff000000000000000000000000000000,padColumn 166 0x3ae7bc52c010000000000000802002008006000000),(padColumn 166 0x0,padColumn 166 0x0)] i))
def cols : List ColumnInfo := [(772,2,249,0,7),(769,2,252,0,7),(718,0,305,0,4),(710,8,305,0,4),(709,8,306,0,4),(707,8,308,0,4),(203,512,308,0,4),(646,8,305,64,5),(643,8,308,64,5),(643,0,380,0,7),(568,65,390,0,4),(107,512,404,0,4),(536,64,423,0,6),(547,0,476,0,8),(546,1,476,0,8),(528,1,462,32,8),(514,8,309,192,7),(520,0,503,0,10),(514,0,509,0,11),(284,192,547,0,4),(212,256,553,2,5),(182,256,585,0,4),(268,128,627,0,7),(386,4,633,0,8),(358,16,649,0,4),(118,256,649,0,4),(357,16,650,0,4),(116,256,649,2,5),(355,16,652,0,4),(112,256,649,6,6),(280,68,547,128,5),(280,64,679,0,6),(338,0,685,0,7),(259,16,652,96,6),(258,16,653,96,7),(272,0,751,0,10),(264,4,627,128,8),(260,0,763,0,11),(258,0,765,0,11),(256,2,253,512,9),(152,64,807,0,7),(72,128,819,4,9),(197,0,826,0,7),(165,0,858,0,8),(136,0,887,0,11),(132,0,891,0,12),(56,64,903,0,7),(88,0,935,0,8),(24,64,935,0,8),(80,0,943,0,11),(72,0,951,0,11),(66,0,957,0,11),(64,0,959,0,13),(48,0,975,0,11),(33,0,990,0,12),(4,0,1019,0,13),(2,0,1021,0,13),(1,0,1022,0,13)]
def data14 : Nat → Nat := (fun i => tableWord #[0x3ff,0xd384b1ca6b7608] i)
def data13 : Nat → Nat := (fun i => tableWord #[0x7ff483,0x18315b486a3f1db6b20a,0x7ff503,0x228d5ed649bb1608,0x7ff523,0x71479959265b7b1109] i)
def data12 : Nat → Nat := (fun i => (if i<8 then tableWord #[0xbbf8ca483,0xf83132d2e6f6ed2e08,0xff7503483,0x24306632edf6230508,0xfbf8ca483,0x32e6d2f9f821ed2e08,0xbff50a483,0x243023f92966b22a0e65b518050d] i else (if i<16 then tableWord #[0xbff90a483,0x3709ed66f9572e07,0xbffd44503,0x320da671f61c1607,0xfff50a483,0x24b23230231e1c07,0xfff528483,0x128151ab266edf611230a] i else tableWord #[0xfff544503,0x24303223081906,0xfff524503,0xf240600052eedf611230a,0xfff504523,0x11ad0220edf6012e91630a] i)))
def data11 : Nat → Nat := (fun i => (if i<16 then (if i<8 then tableWord #[0x13bfd6650a483,0xb2822ae2e04,0x1fe7524503483,0xe1c02,0x1fb78ca503483,0x7e45c0303,0x1ef7528503483,0x7e43a0303] i else tableWord #[0x1bbf50b8ca483,0x3e1c02,0x1bbf5288ca483,0x1edda82808e605,0x1bbf50a8ca483,0x803c1c03,0x1bbfd6650a483,0xbc101803] i) else (if i<24 then tableWord #[0x13ff52b50a483,0x27180cc0e1c05,0x13ff92b50a483,0x161302,0x13ff52b90a483,0x6b0181c03,0x17bfd66544503,0x360502] i else tableWord #[0x13ff52bd44503,0x13898280b04,0x1fbf5288ca483,0x84c8602204] i)))
def data10 : Nat → Nat := (fun i => tableWord #[0x3ce7528524503483,0x501c02,0x2bbdd815288ca483,0x0,0x3bbdd815288ca483,0xe601] i)
def levels : Nat → Packing
  | 10 => (3,4,6,0,0,0,0,data10)
  | 11 => (14,3,6,0,0,0,0,data11)
  | 12 => (11,2,6,0,0,0,0,data12)
  | 13 => (3,1,6,0,0,0,0,data13)
  | 14 => (1,0,6,0,0,0,0,data14)
  | _ => (0,0,0,0,0,0,0,fun _ => 0)
def index : Nat → Nat → Option (Nat × Nat)
  | 11 => fun h => smallSlot h 2 10 2 2 (fun i => (((fun i => tableWord #[0x1] i)) (i/16) >>> (1*(i%16))) % 2) (fun i => (((fun i => tableWord #[0xdf3c400880] i)) (i/16) >>> (7*(i%16))) % 128)
  | 12 => fun h => smallSlot h 7 29 4 2 (fun i => (((fun i => tableWord #[0x2981] i)) (i/16) >>> (2*(i%16))) % 4) (fun i => (((fun i => tableWord #[0x42326824e847342e00005320d6e058028e00,0x1e6ca017c400007548400a9f280143] i)) (i/16) >>> (9*(i%16))) % 512)
  | 13 => fun h => smallSlot h 7 23 4 2 (fun i => (((fun i => tableWord #[0x5008150] i)) (i/16) >>> (4*(i%16))) % 16) (fun i => (((fun i => tableWord #[0xa482f1469ab802240003912c9d5b112328c1,0x20e0a00017980186] i)) (i/16) >>> (9*(i%16))) % 512)
  | 14 => fun h => smallSlot h 2 14 2 2 (fun i => (((fun i => tableWord #[0x0] i)) (i/16) >>> (1*(i%16))) % 2) (fun i => (((fun i => tableWord #[0x310001b424e00cd3] i)) (i/16) >>> (7*(i%16))) % 128)
  | _ => fun _ => none
def book : Forest := ⟨1023,14,samples,cols,[[],[32,67,117,152],[80,97,114,131,148],[112,97,82,147,132]],levels,index⟩
theorem geometry : graphValid book (boundsBefore entries) = true := by decide +kernel
set_option maxRecDepth 16000 in
theorem row14_0 : CutRow book 14 0 1 := bandCut 10 false (by decide +kernel)
theorem band14 : CutRow book 14 0 1 := row14_0
set_option maxRecDepth 16000 in
theorem row13_0 : CutRow book 13 0 3 := bandCut 11 false (by decide +kernel)
theorem band13 : CutRow book 13 0 3 := row13_0
set_option maxRecDepth 16000 in
theorem row12_0 : CutRow book 12 0 1 := bandCut 10 false (by decide +kernel)
set_option maxRecDepth 16000 in
theorem row12_1 : CutRow book 12 1 5 := bandCut 11 false (by decide +kernel)
set_option maxRecDepth 16000 in
theorem row12_6 : CutRow book 12 6 5 := bandCut 12 false (by decide +kernel)
theorem combine12_0_6 : CutRow book 12 0 6 := @joinRow book 12 0 1 5 row12_0 row12_1
theorem combine12_0_11 : CutRow book 12 0 11 := @joinRow book 12 0 6 5 combine12_0_6 row12_6
theorem band12 : CutRow book 12 0 11 := combine12_0_11
set_option maxRecDepth 16000 in
theorem row11_0 : CutRow book 11 0 1 := bandCut 10 false (by decide +kernel)
set_option maxRecDepth 16000 in
theorem row11_1 : CutRow book 11 1 12 := bandCut 11 false (by decide +kernel)
set_option maxRecDepth 16000 in
theorem row11_13 : CutRow book 11 13 1 := bandCut 12 false (by decide +kernel)
theorem combine11_0_13 : CutRow book 11 0 13 := @joinRow book 11 0 1 12 row11_0 row11_1
theorem combine11_0_14 : CutRow book 11 0 14 := @joinRow book 11 0 13 1 combine11_0_13 row11_13
theorem band11 : CutRow book 11 0 14 := combine11_0_14
set_option maxRecDepth 16000 in
theorem row10_0 : CutRow book 10 0 2 := bandCut 10 false (by decide +kernel)
set_option maxRecDepth 16000 in
theorem row10_2 : CutRow book 10 2 1 := bandCut 11 false (by decide +kernel)
theorem combine10_0_3 : CutRow book 10 0 3 := @joinRow book 10 0 2 1 row10_0 row10_2
theorem band10 : CutRow book 10 0 3 := combine10_0_3
theorem checked : mixedTables book 14 := by
  intro k hk
  interval_cases k
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact band10
  · exact band11
  · exact band12
  · exact band13
  · exact band14
end B2015_15
theorem h2015_15 : Face true 1023 15 :=
  mixedLower (g:=B2015_15.book) (i:=0) (hints:=4882524037)
    (before_sound B2015_15.entries B2015_15.prior) B2015_15.geometry B2015_15.checked
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem h2389_7 : Face true 1205 7 := carry_of (swaps:=[164,148,64,128,116,50,82,96]) (by decide +kernel) h473_7
theorem h2445_7 : Face true 1229 7 := carry_of (swaps:=[165,149,118,133,66]) (by decide +kernel) h473_7
theorem h2521_8 : Face true 1273 8 := carry_of (swaps:=[162,146,100,83,130,112]) (by decide +kernel) h477_8
theorem h2524_8 : Face true 1276 8 := carry_of (swaps:=[162,146,50,67,64,84,99,114,128,16]) (by decide +kernel) h477_8
theorem h2525_11 : Face true 1277 11 := carry_of (swaps:=[168,134,150,117,48,64,32]) (by decide +kernel) h1885_11
theorem h2631_7 : Face true 1319 7 := carry_of (swaps:=[166,101,149,134,117,66,16,48]) (by decide +kernel) h473_7
theorem h2643_7 : Face true 1331 7 := carry_of (swaps:=[160,48,147,128,64,100,50,33,113,80]) (by decide +kernel) h473_7
theorem h2645_8 : Face true 1333 8 := carry_of (swaps:=[166,118,151,101,133,33,50,16,64]) (by decide +kernel) h924_8
theorem h2646_7 : Face true 1334 7 := carry_of (swaps:=[160,144,112,16,132,80,97,32]) (by decide +kernel) h723_7
theorem h2710_7 : Face true 1366 7 := carry_of (swaps:=[160,144,112,132,80,97,32]) (by decide +kernel) h723_7
theorem h2903_11 : Face true 1463 11 := carry_of (swaps:=[166,150,117,66,48]) (by decide +kernel) h990_11
theorem h2974_11 : Face true 1502 11 := carry_of (swaps:=[165,118,149,66]) (by decide +kernel) h990_11
theorem h2895_10 : Face true 1455 10 := carry_of (swaps:=[166,150,117,66,48]) (by decide +kernel) h987_10
theorem h3023_11 : Face true 1519 11 := dropFace 64 4882196357 h2895_10 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem h3030_9 : Face true 1526 9 := dropFace 1088 2203926726528 h854_7 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem h3035_11 : Face true 1531 11 := carry_of (swaps:=[166,117,66,48]) (by decide +kernel) h3023_11
theorem h3037_13 : Face true 1533 13 := carry_of (swaps:=[163,65,50,132,83,146,97,112]) (by decide +kernel) h1887_13
theorem h3143_7 : Face true 1575 7 := carry_of (swaps:=[133,168,149,117,101,50,32,64]) (by decide +kernel) h723_7
theorem h3155_7 : Face true 1587 7 := carry_of (swaps:=[134,168,150,118,64]) (by decide +kernel) h723_7
theorem h3291_11 : Face true 1659 11 := carry_of (swaps:=[161,148,33,116,99,32,81,128]) (by decide +kernel) h990_11
theorem h3341_8 : Face true 1677 8 := carry_of (swaps:=[134,168,150,50,16,64]) (by decide +kernel) h924_8
theorem h3342_7 : Face true 1678 7 := carry_of (swaps:=[160,64,147,132,66,99,82,112,16]) (by decide +kernel) h473_7
theorem h3399_8 : Face true 1703 8 := carry_of (swaps:=[66,162,32,148,33,100,82,113,128]) (by decide +kernel) h855_8
theorem h3339_7 : Face true 1675 7 := carry_of (swaps:=[64,164,16,145,112,67,131,97,80]) (by decide +kernel) h723_7
theorem h3407_11 : Face true 1711 11 := carry_of (swaps:=[66,164,50,147,64,99,114,81,128]) (by decide +kernel) h990_11
theorem h3471_11 : Face true 1743 11 := carry_of (swaps:=[163,65,145,64,131,114,81,96]) (by decide +kernel) h990_11
theorem h3486_10 : Face true 1758 10 := carry_of (swaps:=[167,118,134,149,65,49,16,32]) (by decide +kernel) h987_10
theorem h3335_7 : Face true 1671 7 := carry_of (swaps:=[164,48,144,132,66,49,82,113,96]) (by decide +kernel) h473_7
theorem h3531_9 : Face true 1771 9 := carry_of (swaps:=[152,166,50,32,64]) (by decide +kernel) h3030_9
theorem h3543_11 : Face true 1783 11 := carry_of (swaps:=[152,118,101,165,64,48,32]) (by decide +kernel) h3023_11
theorem h3545_10 : Face true 1785 10 := carry_of (swaps:=[163,65,64,84,131,114,97,144]) (by decide +kernel) h1631_10
theorem h3549_13 : Face true 1789 13 := carry_of (swaps:=[163,65,64,84,131,114,97,144]) (by decide +kernel) h1887_13
theorem h3550_11 : Face true 1790 11 := carry_of (swaps:=[152,166,50,64]) (by decide +kernel) h3023_11
theorem h3591_8 : Face true 1799 8 := carry_of (swaps:=[135,134,167,150,16,64,49,32]) (by decide +kernel) h924_8
theorem h3606_7 : Face true 1814 7 := carry_of (swaps:=[64,161,148,113,100,128,81,32]) (by decide +kernel) h723_7
theorem h3667_9 : Face true 1843 9 := carry_of (swaps:=[50,161,147,67,100,83,32,113,128]) (by decide +kernel) h926_9
theorem h3671_12 : Face true 1847 12 := carry_of (swaps:=[65,164,116,49,100,50,130,81,144]) (by decide +kernel) h1755_12
theorem h3807_15 : Face true 1919 15 := carry_of (swaps:=[162,48,49,148,83,114,97,128]) (by decide +kernel) h2015_15
theorem h3854_9 : Face true 1934 9 := carry_of (swaps:=[67,50,161,148,84,115,130,97]) (by decide +kernel) h926_9
theorem h3855_12 : Face true 1935 12 := carry_of (swaps:=[134,166,117,66,48,16]) (by decide +kernel) h1755_12
theorem h3862_8 : Face true 1942 8 := carry_of (swaps:=[16,64,32,164,145,100,112,130,81,48]) (by decide +kernel) h727_8
theorem h3911_10 : Face true 1959 10 := carry_of (swaps:=[65,67,163,33,116,99,146,81,128]) (by decide +kernel) h1631_10
theorem h3935_15 : Face true 1983 15 := carry_of (swaps:=[67,64,161,50,116,83,146,97,128]) (by decide +kernel) h2015_15
theorem h3999_15 : Face true 2015 15 := carry_of (swaps:=[65,33,160,116,131,146,97,80]) (by decide +kernel) h2015_15
theorem h472_5 : Face true 248 5 := carry_of (swaps:=[100,83,112,32,16]) (by decide +kernel) h217_5
theorem h980_6 : Face true 500 6 := carry_of (swaps:=[33,132,112,82,97,48]) (by decide +kernel) h599_6
theorem h1481_6 : Face true 745 6 := carry_of (swaps:=[148,65,116,129,98,49,80]) (by decide +kernel) h599_6
theorem h1496_6 : Face true 760 6 := carry_of (swaps:=[146,33,65,64,84,128,114,97,48]) (by decide +kernel) h599_6
theorem h1949_11 : Face true 989 11 := carry_of (swaps:=[118,134,149,66,50]) (by decide +kernel) h989_11
theorem h2009_10 : Face true 1017 10 := carry_of (swaps:=[148,131,114,97,80]) (by decide +kernel) h1631_10
theorem h2012_10 : Face true 1020 10 := carry_of (swaps:=[32,64,16,50,148,131,82,113,96]) (by decide +kernel) h1631_10
theorem h2316_4 : Face true 1164 4 := carry_of (swaps:=[166,150,134,117,48,64,32,16]) (by decide +kernel) h209_4
theorem h2565_4 : Face true 1285 4 := carry_of (swaps:=[165,149,134,117,50,66]) (by decide +kernel) h209_4
theorem h2580_4 : Face true 1300 4 := carry_of (swaps:=[166,101,149,134,117,64,32,16]) (by decide +kernel) h209_4
theorem h2641_5 : Face true 1329 5 := carry_of (swaps:=[163,147,128,84,115,96]) (by decide +kernel) h217_5
theorem h2769_6 : Face true 1393 6 := carry_of (swaps:=[160,16,145,64,132,113,98,49,80]) (by decide +kernel) h599_6
theorem h2885_6 : Face true 1445 6 := carry_of (swaps:=[164,65,66,145,116,97,130,49,80]) (by decide +kernel) h599_6
theorem h916_5 : Face true 468 5 := carry_of (swaps:=[132,84,115,96,32,16]) (by decide +kernel) h217_5
theorem h2972_9 : Face true 1500 9 := carry_of (swaps:=[161,66,67,145,100,115,130,81]) (by decide +kernel) h926_9
theorem h3077_4 : Face true 1541 4 := carry_of (swaps:=[101,166,149,134,117,50,32,64]) (by decide +kernel) h209_4
theorem h3665_6 : Face true 1841 6 := carry_of (swaps:=[33,161,146,84,113,98,49,128]) (by decide +kernel) h599_6
theorem h3805_13 : Face true 1917 13 := carry_of (swaps:=[66,162,50,33,148,115,82,97,128]) (by decide +kernel) h1887_13
theorem h3869_11 : Face true 1949 11 := carry_of (swaps:=[135,133,118,166,149,64,32]) (by decide +kernel) h989_11
theorem h3917_10 : Face true 1965 10 := carry_of (swaps:=[67,64,161,50,116,83,146,97,128]) (by decide +kernel) h1631_10
theorem h3925_10 : Face true 1973 10 := carry_of (swaps:=[161,84,115,146,97,128]) (by decide +kernel) h1631_10
theorem h863_9 : Face true 447 9 := dropFace 10 4832196485 h853_7 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem h3932_9 : Face true 1980 9 := carry_of (swaps:=[49,67,50,164,64,84,115,130,145,96]) (by decide +kernel) h863_9
theorem h3933_13 : Face true 1981 13 := carry_of (swaps:=[67,64,161,50,116,83,146,97,128]) (by decide +kernel) h1887_13
theorem h3997_13 : Face true 2013 13 := carry_of (swaps:=[65,33,160,116,131,146,97,80]) (by decide +kernel) h1887_13
theorem h4045_11 : Face true 2029 11 := dropFace 352 9177163525 h3341_8 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem h4053_11 : Face true 2037 11 := carry_of (swaps:=[149,118,134,165,66,50]) (by decide +kernel) h4045_11
theorem h4057_11 : Face true 2041 11 := carry_of (swaps:=[168,134,150,117,48,64,32]) (by decide +kernel) h4045_11
theorem h4060_11 : Face true 2044 11 := carry_of (swaps:=[117,151,166,133,32,50,64,16]) (by decide +kernel) h4045_11

namespace B4061_15
def entries : List (Nat × Nat) := [(248,5),(476,8),(500,6),(561,4),(600,4),(633,8),(652,4),(745,6),(760,6),(305,4),(957,11),(989,11),(1017,10),(1020,10),(1021,13),(1164,4),(1285,4),(1300,4),(1333,8),(113,4),(1329,5),(1393,6),(1445,6),(468,5),(1500,9),(1533,13),(1541,4),(1677,8),(1789,13),(1841,6),(1917,13),(1949,11),(1965,10),(1973,10),(1980,9),(1981,13),(2013,13),(2029,11),(2037,11),(2041,11),(2044,11)]
theorem prior : Known true entries := (consFace h472_5 (consFace h924_8 (consFace h980_6 (consFace h1105_4 (consFace h1176_4 (consFace h1241_8 (consFace h1292_4 (consFace h1481_6 (consFace h1496_6 (consFace h593_4 (consFace h1885_11 (consFace h1949_11 (consFace h2009_10 (consFace h2012_10 (consFace h2013_13 (consFace h2316_4 (consFace h2565_4 (consFace h2580_4 (consFace h2645_8 (consFace h209_4 (consFace h2641_5 (consFace h2769_6 (consFace h2885_6 (consFace h916_5 (consFace h2972_9 (consFace h3037_13 (consFace h3077_4 (consFace h3341_8 (consFace h3549_13 (consFace h3665_6 (consFace h3805_13 (consFace h3869_11 (consFace h3917_10 (consFace h3925_10 (consFace h3932_9 (consFace h3933_13 (consFace h3997_13 (consFace h4045_11 (consFace h4053_11 (consFace h4057_11 (consFace h4060_11 (known_down baseKnown))))))))))))))))))))))))))))))))))))))))))
def samples : Nat → Bits × Bits := (fun i => (if i<8 then tableBits #[(padColumn 164 0xd83067348831c0c83001810c0c600f000007ffff,padColumn 164 0x902043148810c0483000890c04644f0000010951),(padColumn 164 0x0,padColumn 164 0x0),(padColumn 164 0x6004399cb00018300fe360e0fc18070001000f800,padColumn 164 0x400020149000183005a12020541807a101024e804),(padColumn 164 0x821801e0011ce1c30c04071f032007fffe0070000,padColumn 164 0x820801e00014a1430c00011d012011365a0474008),(padColumn 164 0x1060ce00066f0203f01887e0003ff8001fff80000,padColumn 164 0x10404e00042f0201d01007e000339800025080000),(padColumn 164 0xf0000070001c0000f80003c000001ffffffff,padColumn 164 0xb000005000180000f000038000001daf6f6ae),(padColumn 164 0x7f0000078000e0001f000003ffffffe00000000,padColumn 164 0x170000018000a00007000002c466c9800008030),(padColumn 164 0x380000038000300001ffffffc000000000000000,padColumn 164 0x180000028000200001edec2a80080000008000c0)] i else tableBits #[(padColumn 164 0x1c000000c00003ffffe0000000000000000000000,padColumn 164 0xc000000400001ce2a40000400000002000000300),(padColumn 164 0xe0000000fffffc000000000000000000000000000,padColumn 164 0x60000000b76a50000080000030010000003000000),(padColumn 164 0xffffffff000000000000000000000000000000000,padColumn 164 0x9278c14a00008000400004080000000c10c000400)] i))
def cols : List ColumnInfo := [(773,1024,248,0,5),(1569,0,476,0,8),(1033,512,500,0,6),(1480,4,561,0,4),(421,1024,600,0,4),(1412,0,633,0,8),(1408,4,633,0,8),(1377,16,652,0,4),(1044,256,745,0,6),(261,1024,760,0,6),(1156,8,305,576,6),(1088,0,957,0,11),(1056,0,989,0,11),(1028,0,1017,0,10),(1025,0,1020,0,10),(1024,1,476,544,10),(1024,0,1021,0,13),(865,16,1164,0,4),(752,8,1285,0,4),(696,64,1285,0,4),(233,512,1300,0,4),(704,8,1333,0,8),(648,4,113,1280,6),(644,8,1329,64,6),(524,128,1393,0,6),(536,64,1445,0,6),(576,8,1333,128,9),(552,1,468,1024,6),(545,0,1500,0,9),(544,1,476,1024,9),(512,0,1533,0,13),(440,64,1541,0,4),(384,4,633,1024,9),(288,16,1677,64,9),(256,0,1789,0,13),(76,128,1841,0,6),(128,0,1917,0,13),(96,0,1949,0,11),(80,0,1965,0,10),(68,8,1329,640,7),(72,0,1973,0,10),(64,8,1333,640,10),(65,0,1980,0,9),(64,0,1981,0,13),(32,1,476,1536,10),(32,0,2013,0,13),(16,0,2029,0,11),(0,16,1677,352,11),(8,0,2037,0,11),(0,8,1333,704,11),(4,0,2041,0,11),(0,4,633,1408,11),(1,0,2044,0,11),(0,1,476,1568,11)]
def data14 : Nat → Nat := (fun i => tableWord #[0x3ff,0x2b40b92d7a207] i)
def data13 : Nat → Nat := (fun i => tableWord #[0x7ff020,0x5cbd8314bace0508,0x7ff420,0x5cbd83117ace8608,0x7ff820,0xb97b053ad00107] i)
def data12 : Nat → Nat := (fun i => (if i<8 then tableWord #[0xbfb44a020,0x291c0503,0xbfbc4a020,0x281c0503,0xbdf4aa020,0x2a1c0503,0x9ff92a420,0xeb1d0603] i else (if i<16 then tableWord #[0xffe840420,0xaf6f2c5a8605,0xfff062020,0x2e2f31323335280e08140a,0xfff462020,0x2e2f302a29170707,0xfff862020,0x2e2f313428180707] i else tableWord #[0xfff462420,0x2f8c6533290f619d55860a,0xfff862420,0xb38c3233342f6f1d9d030a,0xfff862820,0x31353034160706] i)))
def data11 : Nat → Nat := (fun i => (if i<16 then (if i<8 then tableWord #[0x1bdf0624aa020,0x16a3459834041f06,0x1bdf4624aa020,0xa82e0703,0x1bdf8624aa020,0x300702,0x1bdf5624aa020,0x461302] i else tableWord #[0x1bdf9624aa020,0x4e1f02,0x13ff56a062020,0x5e31198d4101406,0x13ffd6a462020,0x170a02e0704,0x17df8ab462020,0x4c28178a4141106] i) else (if i<24 then tableWord #[0x13ff54b862020,0x170c4300704,0x1ffc861840420,0x2ced20003,0x19ff46292a420,0x12c660f99c3dc2d507,0x19ff86292a420,0x3bc360303] i else tableWord #[0x13ff16a462420,0x5e31198d4320406,0x13ffd4b862420,0xc0121203,0x13ff54b862820,0x2c0702] i)))
def data10 : Nat → Nat := (fun i => tableWord #[0x29df52c0624aa020,0x0,0x23df96c4624aa020,0x0,0x29df8ac46292a420,0x0] i)
def levels : Nat → Packing
  | 10 => (3,4,6,0,0,0,0,data10)
  | 11 => (15,3,6,0,0,0,0,data11)
  | 12 => (11,2,6,0,0,0,0,data12)
  | 13 => (3,1,6,0,0,0,0,data13)
  | 14 => (1,0,6,0,0,0,0,data14)
  | _ => (0,0,0,0,0,0,0,fun _ => 0)
def index : Nat → Nat → Option (Nat × Nat)
  | 11 => fun v => (if v=9929661444464347610 then some (2,0) else (if v=9829307312780417369 then some (1,0) else (if v=6332180413049684947 then some (0,0) else none)))
  | 12 => fun h => smallSlot h 8 31 4 5 (fun i => (((fun i => tableWord #[0x6c6bc8] i)) (i/16) >>> (3*(i%16))) % 8) (fun i => (((fun i => tableWord #[0x406d0be0a000001e0ce04a1460301540b00060fa07a02000,0xc09e0e42ad01000c1c208c0d413805908] i)) (i/16) >>> (12*(i%16))) % 4096)
  | 13 => fun h => smallSlot h 8 30 4 5 (fun i => (((fun i => tableWord #[0x884c1a8800] i)) (i/16) >>> (5*(i%16))) % 32) (fun i => (((fun i => tableWord #[0x825a15005a0aa0900000800000006500020b075211204606,0xe4581200741a202908a1830a803000001c1b107000] i)) (i/16) >>> (12*(i%16))) % 4096)
  | 14 => fun h => smallSlot h 8 36 2 5 (fun i => (((fun i => tableWord #[0x3e9100800] i)) (i/16) >>> (5*(i%16))) % 32) (fun i => (((fun i => tableWord #[0xf4f9164cc1d0d0a6268b16da9908000029b08800,0xc87b3caa82005cb001bb6ad92,0xe8c0000203] i)) (i/16) >>> (10*(i%16))) % 1024)
  | _ => fun _ => none
def book : Forest := ⟨2045,14,samples,cols,[[],[67,149,135],[50,134,169],[50,66,165,134,118,149],[66,50,149,118,134,165],[66,165,118],[32,133,151],[32,67,117,152],[32,48,133,101,151,167],[32,48,64,165,101,118,152],[32,64,48,117,150,134,168],[32,64,165,150,118,133],[48,32,101,133,167,151],[48,32,66,117,134,166,150],[48,101,167],[48,64,149,101,135,167],[48,66,117,166],[48,66,32,149,166,135,117],[64,32,50,101,117,165,152],[64,32,133,118,150,165],[64,48,101,149,167,135],[64,150,168],[64,50,32,133,166,151,117],[64,50,166,152]],levels,index⟩
theorem geometry : graphValid book (boundsBefore entries) = true := by decide +kernel
set_option maxRecDepth 16000 in
theorem row14_0 : CutRow book 14 0 1 := bandCut 10 false (by decide +kernel)
theorem band14 : CutRow book 14 0 1 := row14_0
set_option maxRecDepth 16000 in
theorem row13_0 : CutRow book 13 0 3 := bandCut 11 false (by decide +kernel)
theorem band13 : CutRow book 13 0 3 := row13_0
set_option maxRecDepth 16000 in
theorem row12_0 : CutRow book 12 0 4 := bandCut 10 false (by decide +kernel)
set_option maxRecDepth 16000 in
theorem row12_4 : CutRow book 12 4 1 := bandCut 11 false (by decide +kernel)
set_option maxRecDepth 16000 in
theorem row12_5 : CutRow book 12 5 6 := bandCut 12 false (by decide +kernel)
theorem combine12_0_5 : CutRow book 12 0 5 := @joinRow book 12 0 4 1 row12_0 row12_4
theorem combine12_0_11 : CutRow book 12 0 11 := @joinRow book 12 0 5 6 combine12_0_5 row12_5
theorem band12 : CutRow book 12 0 11 := combine12_0_11
set_option maxRecDepth 16000 in
theorem row11_0 : CutRow book 11 0 15 := bandCut 11 false (by decide +kernel)
theorem band11 : CutRow book 11 0 15 := row11_0
set_option maxRecDepth 16000 in
theorem row10_0 : CutRow book 10 0 3 := bandCut 10 false (by decide +kernel)
theorem band10 : CutRow book 10 0 3 := row10_0
theorem checked : mixedTables book 14 := by
  intro k hk
  interval_cases k
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact band10
  · exact band11
  · exact band12
  · exact band13
  · exact band14
end B4061_15
theorem h4061_15 : Face true 2045 15 :=
  mixedLower (g:=B4061_15.book) (i:=0) (hints:=9177491205)
    (before_sound B4061_15.entries B4061_15.prior) B4061_15.geometry B4061_15.checked
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

namespace B4063_17
def entries : List (Nat × Nat) := [(252,7),(378,7),(438,7),(462,7),(470,7),(474,7),(476,8),(502,8),(510,11),(619,7),(627,7),(633,8),(634,7),(683,7),(730,7),(762,8),(763,11),(766,10),(819,8),(858,8),(890,9),(891,12),(935,8),(951,11),(954,8),(990,12),(1023,15),(1205,7),(1229,7),(1273,8),(1276,8),(1277,11),(1319,7),(1331,7),(1333,8),(1334,7),(1366,7),(1463,11),(1502,11),(1519,11),(1526,9),(1531,11),(1533,13),(1575,7),(1587,7),(1659,11),(1677,8),(1678,7),(1703,8),(1675,7),(1711,11),(1743,11),(1758,10),(1671,7),(1771,9),(1783,11),(1785,10),(1789,13),(1790,11),(1799,8),(1814,7),(1843,9),(1847,12),(1919,15),(1934,9),(1935,12),(1942,8),(1959,10),(1983,15),(2015,15),(2045,15)]
theorem prior : Known true entries := (consFace h476_7 (consFace h730_7 (consFace h854_7 (consFace h910_7 (consFace h918_7 (consFace h922_7 (consFace h924_8 (consFace h982_8 (consFace h990_11 (consFace h1227_7 (consFace h1235_7 (consFace h1241_8 (consFace h1242_7 (consFace h1355_7 (consFace h1434_7 (consFace h1498_8 (consFace h1499_11 (consFace h1502_10 (consFace h1619_8 (consFace h1690_8 (consFace h1754_9 (consFace h1755_12 (consFace h1863_8 (consFace h1879_11 (consFace h1882_8 (consFace h1950_12 (consFace h2015_15 (consFace h2389_7 (consFace h2445_7 (consFace h2521_8 (consFace h2524_8 (consFace h2525_11 (consFace h2631_7 (consFace h2643_7 (consFace h2645_8 (consFace h2646_7 (consFace h2710_7 (consFace h2903_11 (consFace h2974_11 (consFace h3023_11 (consFace h3030_9 (consFace h3035_11 (consFace h3037_13 (consFace h3143_7 (consFace h3155_7 (consFace h3291_11 (consFace h3341_8 (consFace h3342_7 (consFace h3399_8 (consFace h3339_7 (consFace h3407_11 (consFace h3471_11 (consFace h3486_10 (consFace h3335_7 (consFace h3531_9 (consFace h3543_11 (consFace h3545_10 (consFace h3549_13 (consFace h3550_11 (consFace h3591_8 (consFace h3606_7 (consFace h3667_9 (consFace h3671_12 (consFace h3807_15 (consFace h3854_9 (consFace h3855_12 (consFace h3862_8 (consFace h3911_10 (consFace h3935_15 (consFace h3999_15 (consFace h4061_15 (known_down baseKnown))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
def samples : Nat → Bits × Bits := (fun i => (if i<8 then tableBits #[(padColumn 293 0x101cc3077878183c0f0103c103e38000000380f003e0e00180e0f00c3800fc00203fffff,padColumn 293 0x482010858080c030000c100e3a4085000d4f293a2e000c8e0f0063940f408000452c3),(padColumn 293 0x20600000046000c030021c023c3c0060060c01003c00fe00010300004003000040003000,padColumn 293 0x202000000460008020020c0218340020020401001c006a0001034080401320104101300a),(padColumn 293 0x1c0800438878063000000003c3fc00081f8f00603c7ff00661e03ffc3801c00018003c000,padColumn 293 0x800000200180210000004abc3fc1000098500200c4f70022020119c3a01c4841a013c010),(padColumn 293 0x1e00031800f8018400403ce03fc000070e00007803f800000861fc0030001ffffe003c0000,padColumn 293 0x604120804f8108000000c600f4002010200027ca3fac04000001c001000050e9e223e0020),(padColumn 293 0xf0020cf0006000380c0ffc00000781001007ffc000001907e000003ffe00003ffc00000,padColumn 293 0x900004f210200010040ffe81280480000001b34000401007e4081000e60000014400000),(padColumn 293 0xf00000000000ff00000000000001ff80000000001f8000003c00000003ffffffff,padColumn 293 0xb00000000000bf00000000000001ff00000000001f0000003800000003ebbbad3c),(padColumn 293 0x3f0000000003ff0000000000001ffe000000000001e00000003ffffffffc00000000,padColumn 293 0x1700000000027f0000000000001dfe000000000000600000002f319af16000000040),(padColumn 293 0x3c000000007fc0000000000007fe000000000000001ffffffffc00000000000000000,padColumn 293 0xc000000006fc0000000000007ee000000000000001d5fce2e6000200000000000180)] i else tableBits #[(padColumn 293 0xffc00000007f8000000000000007ffffffffffffffffe00000000000000000000000000,padColumn 293 0x1406dc00004005d8280a280000000037df65abe4cb23089400008804000000818000200600),(padColumn 293 0x1ff00000000007ffffffffffffffff80000000000000000000000000000000000000000000,padColumn 293 0x19d800000000077733ccf19330a308400180c000000010000010000800040000010c000800),(padColumn 293 0x1ffffffffffff8000000000000000000000000000000000000000000000000000000000000,padColumn 293 0x1f3ffb38cef200000000000000001000000000000000001800001000000000020010000000)] i))
def cols : List ColumnInfo := [(1793,2,252,0,7),(645,1024,378,0,7),(1609,0,438,0,7),(1584,1,462,0,7),(1576,1,470,0,7),(1572,1,474,0,7),(1570,1,476,0,8),(1552,1,462,32,8),(1545,0,502,0,8),(1540,1,474,32,8),(1538,1,476,32,9),(1537,0,510,0,11),(1424,4,619,0,7),(1416,4,627,0,7),(1414,0,633,0,8),(1410,4,633,0,8),(1409,4,634,0,7),(389,1024,634,0,7),(1364,0,683,0,7),(293,1024,730,0,7),(1296,4,619,128,8),(1288,4,627,128,8),(1282,4,633,128,9),(261,1024,762,0,8),(1284,0,763,0,11),(1281,0,766,0,10),(1100,128,819,0,8),(165,1024,858,0,8),(133,1024,890,0,9),(1156,0,891,0,12),(1048,64,935,0,8),(1096,0,951,0,11),(69,1024,954,0,8),(1057,0,990,0,12),(1024,0,1023,0,15),(840,2,1205,0,7),(816,2,1229,0,7),(772,2,1273,0,8),(769,2,1276,0,8),(770,0,1277,0,11),(768,2,1277,0,11),(720,8,1319,0,7),(708,8,1331,0,7),(706,8,1333,0,8),(705,8,1334,0,7),(681,0,1366,0,7),(644,8,1331,64,8),(580,8,1331,128,8),(578,8,1333,128,9),(584,0,1463,0,11),(560,1,462,1024,8),(552,1,470,1024,8),(548,1,474,1024,8),(546,1,476,1024,9),(545,0,1502,0,11),(528,8,1319,192,9),(528,1,462,1056,9),(528,0,1519,0,11),(516,8,1331,192,9),(514,8,1333,192,10),(521,0,1526,0,9),(520,1,470,1056,9),(516,1,474,1056,9),(516,0,1531,0,11),(514,1,476,1056,10),(514,0,1533,0,13),(408,64,1575,0,7),(332,128,1587,0,7),(400,4,619,1024,8),(392,4,627,1024,8),(386,4,633,1024,9),(385,4,634,1024,8),(388,0,1659,0,11),(354,16,1677,0,8),(353,16,1678,0,7),(337,32,1678,0,7),(280,64,1703,0,8),(324,16,1675,32,8),(322,16,1677,32,9),(321,16,1678,32,8),(336,0,1711,0,11),(289,16,1678,64,8),(304,0,1743,0,11),(289,0,1758,0,10),(264,16,1671,96,9),(276,0,1771,0,9),(272,4,619,1152,9),(260,16,1675,96,9),(258,16,1677,96,10),(257,16,1678,96,9),(264,4,627,1152,9),(264,0,1783,0,11),(262,0,1785,0,10),(258,4,633,1152,10),(257,4,634,1152,9),(258,0,1789,0,13),(257,0,1790,0,11),(184,64,1799,0,8),(233,0,1814,0,7),(204,0,1843,0,9),(76,128,1843,0,9),(200,0,1847,0,12),(128,0,1919,0,15),(81,32,1934,0,9),(112,0,1935,0,12),(105,0,1942,0,8),(88,0,1959,0,10),(24,64,1959,0,10),(64,0,1983,0,15),(32,0,2015,0,15),(2,0,2045,0,15)]
def data16 : Nat → Nat := (fun i => tableWord #[0x7ff,0x8b36dd9ba09dd17d0e50b] i)
def data15 : Nat → Nat := (fun i => (if i<8 then tableWord #[0xfff440,0x5f651ce8e5500beeec1d46210c,0xfff460,0x1d68df9d27e8ee4021650a,0xfff500,0x6031e6ec485040e55f210a,0xfff520,0x1d68e6ec65289de84121e50b0c] i else tableWord #[0xfff528,0x5f216865a2edece6e818a1e5280d] i))
def data14 : Nat → Nat := bookData 2 3 3 (fun i => (((fun i => tableWord #[0x520a0118294440] i)) (i/16) >>> (11*(i%16))) % 2048) (fun i => (((fun i => tableWord #[0x7fffdffbffbfffffaffb3ff] i)) (i/16) >>> (13*(i%16))) % 8192) (fun i => (((fun i => tableWord #[0x52b6a42da50b6b589a52049401294b8242d850b621ad846b614010480411810d612652c0,0x90bc948b2502c920b2d62c94a30523c140f0483c24adb52b6d4a2bd636d40ebd626e4ada,0x502d148f3522cd4a32] i)) (i/16) >>> (18*(i%16))) % 262144) (variableSlot (fun i => tablePair #[(0x50a4b34393d038233b2ed2b227420b1cf1781330f00b2059000,0x2c074d1df2ee77d02b0304d05f2c177d0674c0f0c6066fc86ca1b63d01d341753121b2b7c56060bb1e8341906b21b283c23bf9db282fd02b0303d8f4195305d6fd940c110fa3ca5d2006c1bd1e5207b0ba1b06b1e81d860d121f287fd8460305d8f41a0ba300d83588ec84d0e50e8c08c0609b1e82ef97d8480303f4d15df2c75d00607f4192bb1d728181b45e6f6fb33be8d0f945013ec10fb8bbe50e7a03a0609),(0x6d26846255904c446f3f439532c29623f1bb16510e0b7057000,0x30084ca9818340142d08fed0382e900620b4c0ac0a150974ca402c42ed03c690adbe5c90cd6ca9810b03b0e884d065a0154790b4c274d6400e7b8bae86e80e436516e7a042656e90060091684d8b40ec383d9088c30d0f62a08c060de243682ec60391d20394081562d0d00c1005e1b72976420d0bb11d2ec71d03bae900d6590dfb8541490b9442cfb3cc5ecefa3ca600304d82fc847668f311bd864cefa051e5030777e6f64873be8147940c13603a682e97a3019298ac26ffa030bb3016e43067284d81d967d06af2903d8530785580e9a3be5dcefa0560609),(0x1c11340b9072000,0x162d03b72903d9651b3401c9d147966c980fb03174060bb5090902302b14394081be81ff94bdec230141ec5a0305d680a0629805aa056060c)] i))
def data13 : Nat → Nat := bookData 3 5 5 (fun i => (((fun i => tableWord #[0x52846092b46052b46090b460482460d6246052844094b44086b44050044050350050046050b44046b440480440460440,0x52344048344052246050246052046050344090b440522500d62500] i)) (i/16) >>> (24*(i%16))) % 16777216) (fun i => (((fun i => tableWord #[0xfffb6fff3ff5ffdff6ffdcffe7ffbffbff6dffbffa9bfe3ff9dfe7fe,0xffffdffbfffeffefff7ff] i)) (i/16) >>> (14*(i%16))) % 16384) (fun i => (((fun i => tableWord #[0x90b2861aca1462206430e088c38140cc048330242ca088b2812088018b19462c0494c10e3b02218b00462c00,0x42c5324b10c52c4310b16c18b42d4b10ad82393605495284a148d285034a120d2850c41f610e6d8339a1aca6,0x4838a14921252384920e1248380d4120748379940de15047824adc552b7154a1b152c4436054f52863b6210d,0x528a594929690b8594b27592b8554ae1592b82d4ae0b90b82d42e0b524829409f44827d1209e452c9cd4a253,0x524ad54a2ab90baac62eab504aa9412b8524acd4a2b750394548e1044c9b11320c] i)) (i/16) >>> (22*(i%16))) % 4194304) (variableSlot (fun i => tablePair #[(0x3162e72b729223e2181e01bb18315d1380ea0bd08d05d030000,0x2762021e64824422b0089582794448180fc56118363e80d6e543c231d01cc903d85602f1160605f40550301ec0397286a8782dca03a9207e81160603fa2181645a09b21b941ed0842180c09f47ca1a81e09908ba3200c0937e51100604fa15d1900604),(0x4474033b93643232d82b628920c1cc18212a0b508805d02d000,0x7d14c060540141683502b8ad68530050c40f636515adf0bed00282d0881f4530041503103580ec5d0a0400482d07bc160b40ececa1a11e0963e8da03bc87e508e182a3ec118060cf5d0fb1a81180606e01887440975e50101fe80843217621796350342377204382efdc0bbd0a8c2c01bca1774330c01104b87064c1e092c06617c1e09743d04d2b04),(0x4a24404063bb36e32b2e82a626e2181eb1b416611c0a9055000,0x221974408701c901e5114030997438158c90041600acf299d2e8660083fa21c080409740d1281fca0f0602299c0183740401685d0a41306bb794409000d1281aed3b0f4c9434176158168b00cee58d50c08bd0c15683025bfa2182ad0605fa3e517bec0a0460141e8fa3e50984f1180507b1f46d02ed319087612951b280c1740b1f43302e951b280c116198d94560bdd00282d08),(0x4fd4a646240e39c34e3002bf27e2091c819b1440ec0bf04b000,0x158c8768094a81682b0142321977651002a00c1a856168100160bc960b423c2a0d8963683a05e0d42f4d40d0bba0560c057b212b0141ee81583015ec84ac0507aa2edbea0054018355176df5002a00c1a506c0ba1e5d04c0aaa01ba2501a1755401742a3180306bb2e85401827a3650f20b0c23072005088ec3cd960b77e400a80308a8670640802540386c4b1b41d10c06a0aa0c1605d8090a8c845d0a80407),(0x32f2ec28e25822a1f01a31601000db0a2060000,0x4e5210f0371643e06f0a84a10b2605a4ecd80e027c0dc590f8dd05dd0e85e500121c0e83c0e0dd058c2ba6c0ad0e2381c03c72181684c1643a06d8462e53ad1c8705a2ed4009f288f0281d61e8794340001762400e0960bc2d06d80fbe87a098174082586209)] i))
def data12 : Nat → Nat := bookData 4 5 5 (fun i => (((fun i => tableWord #[0x52450344052848344052394b44042c90b46050394b44048390b44048350b44048350044018b48044086b48044090c46044048346044090b46044018b46044052894b44048394b440,0x50352250044c90b46090b52246052450246052848246092b48246052b48246090b48246018b482460482520460] i)) (i/16) >>> (36*(i%16))) % 68719476736) (fun i => (((fun i => tableWord #[0xe7ff5fff7ff67fda7ffcbff9dfe3ffaf7f7efb7fe6ff6efed9ffa9fed3bf,0x36fff5ff9fff9fffbfedffefff5f3feffefbbf] i)) (i/16) >>> (15*(i%16))) % 32768) (fun i => (((fun i => tableWord #[0x44c6314b56b52852e335208cd3aa531098cd3a6334c850311e4304642d2964308448318d41042da108633400,0x92d7494b5d2d8db490b6b25a18c64369050da4140a7052893f6862e8cd801411ed5247ad4a1e092d729235a5,0x14925948cb614931752ccdb68635528c52432d4da874e432d350cb4f636f242d8ca4b2d2] i)) (i/16) >>> (22*(i%16))) % 4194304) (variableSlot (fun i => tablePair #[(0x33c2f52a227023e20c1d81a417d14d1300f30d70bb08904a000,0xd85300925406941a0da83b07a22e85d0084b01f50174199ab04f29d837678413d06c32ee1b04bca0e0064c904c4311427e0604f284fc0c07022004b21a096494602ac51806a5180102d35050145158015742183221809fa0d47e508c018172312e3c252a06e0606),(0x2be28c2672431fe1cf1b119315f12c0e20a308a07003e010000,0x2501602a85d04b01542b01f63742d01f9ba24c1401b03741bc276374a00260b0bc0582c2f0160b3300e81f024301006c14004a31b970e45a1765001b0e65d0346ef2002fa6ec0ad1bb02ec5e53d66ec138174dde5d04d801),(0x1fd1df1ad18917b14711f1060e10c80af096067000,0x11691c017a04c0580ba09403808007c00c3c874374a002530174a001f81000ac0550ac07e04002f02001761680bc8745006e82551501601205e0800e8a003c09)] i))
def data11 : Nat → Nat := (fun i => (if i<8 then tableWord #[0xc3bf94c8cd48350b440,0x9e501,0xeff442e90c483460440,0x0,0xcffc48d42d90c460440,0x0,0xd3bf5288cd48394b440,0x64001] i else (if i<16 then tableWord #[0xb3fddc152848394b440,0xde501,0xf0ff52852450394b440,0x1bb01,0xc7fdd8d42d90b482460,0x45a01,0x87ff5ae92c90b482460,0x2804002] i else tableWord #[0xe4ff52890c92b482460,0x54004002,0x87ff1cd48c44c90b460,0x2804002] i)))
def data10 : Nat → Nat := (fun i => tableWord #[0x153bdde15288cd48394b440,0x0] i)
def levels : Nat → Packing
  | 10 => (1,6,7,0,0,0,0,data10)
  | 11 => (10,5,7,0,0,0,0,data11)
  | 12 => (45,4,7,0,0,0,0,data12)
  | 13 => (76,3,7,0,0,0,0,data13)
  | 14 => (36,2,7,0,0,0,0,data14)
  | 15 => (5,1,7,0,0,0,0,data15)
  | 16 => (1,0,7,0,0,0,0,data16)
  | _ => (0,0,0,0,0,0,0,fun _ => 0)
def index : Nat → Nat → Option (Nat × Nat)
  | 11 => fun v => (if v=10514651931723972104 then some (0,0) else none)
  | 12 => fun h => smallSlot h 5 17 4 3 (fun i => (((fun i => tableWord #[0xe2] i)) (i/16) >>> (2*(i%16))) % 4) (fun i => (((fun i => tableWord #[0x2585e110a008000000074f860038361c01c4f55,0x208] i)) (i/16) >>> (10*(i%16))) % 1024)
  | 13 => fun h => smallSlot h 25 88 6 3 (fun i => (((fun i => tableWord #[0x1900d10700588a0f3a6a,0x2025b2242] i)) (i/16) >>> (5*(i%16))) % 32) (fun i => (((fun i => tableWord #[0x54d41782008ea117c9e2be0fe1de29b4421b0005538158aa,0x20201c000000e0ac19c0361f000c23106a018a8c21424c04,0x951000a8f64600089b028a2cc0ed4a06a00001ec06647c0c,0xdcca1300002df9a000e1400062500020500020700001a000,0x822251a59e27218ca5a2a01679be125ca626c0960dd58e0b,0xc50b46f49e9a408a1014c4a0] i)) (i/16) >>> (12*(i%16))) % 4096)
  | 14 => fun h => smallSlot h 54 203 7 3 (fun i => (((fun i => tableWord #[0x4013214100000c6050008384,0x166020002045810204a2f0828006,0x3c701000039a084c04b0604000,0x78a501c000] i)) (i/16) >>> (7*(i%16))) % 128) (fun i => (((fun i => (if i<8 then tableWord #[0xc1470b12472340004b1e810c1909a90e5a62ac69d54130870000,0x65de2f4000d0a7567090021c4a4624029275440a02830882a41f,0x800000022615560ce22dcc321e304c16c68de0e40eb08844b,0x810509c8611344959ab40004a861ff2d751608e90184c800012c,0x3a300004074c71048000c47e609ac7a7bcbea95524f179846,0x94ce0ac843809343b0d441ac3ea0db73086cf3480f0000000000,0x200fa880001d6beb291e000208c0ca093eb000014bc000c48,0x51a8002998000b05800183a829a22b05991a23141514e1834000] i else tableWord #[0x366400100ef99e02cd64000a4864a113200021ed230990000,0x69f800286850800000008858a5719b0bb076431e0174ec00000c,0x21800190e0000a5000000000080bb4e684c000a11606022e000,0xc96d61f281c2db4aa09780c414d542013a6e49a617e03c266000,0x248082a2711900dc0000000118300000c0d] i))) (i/16) >>> (13*(i%16))) % 8192)
  | 15 => fun h => smallSlot h 26 93 6 3 (fun i => (((fun i => tableWord #[0x4055400120c00001c0a8c000,0x53104000381006] i)) (i/16) >>> (6*(i%16))) % 64) (fun i => (((fun i => tableWord #[0xe01a08a0d000a0fe07000c5ec1a42340cd23c8495af96,0x45c016595643a1c000a2081025f21b41e29fa05a1400044d,0xc9ee9a000000000448a85802b0c41fc89b16000000695119,0x618299d5b703a19087064a88096788000b1aa0e000915012,0x90b215021cdbe8380ba6281d003052e0a604ea1c11c86,0x246000a13624609c22c1765bf59000e45543406] i)) (i/16) >>> (12*(i%16))) % 4096)
  | 16 => fun h => smallSlot h 5 28 3 3 (fun i => (((fun i => tableWord #[0xe2] i)) (i/16) >>> (2*(i%16))) % 4) (fun i => (((fun i => tableWord #[0xba000a60092213b2000000266c14298f2912,0x39200000000169001080143] i)) (i/16) >>> (9*(i%16))) % 512)
  | _ => fun _ => none
def book : Forest := ⟨2047,16,samples,cols,[[],[66,165,118],[32,67,117,152],[32,48,64,165,101,118,152],[48,101,167],[48,66,117,166],[64,32,50,101,117,165,152],[64,50,166,152]],levels,index⟩
theorem geometry : graphValid book (boundsBefore entries) = true := by decide +kernel
set_option maxRecDepth 16000 in
theorem row16_0 : CutRow book 16 0 1 := bandCut 11 false (by decide +kernel)
theorem band16 : CutRow book 16 0 1 := row16_0
set_option maxRecDepth 16000 in
theorem row15_0 : CutRow book 15 0 5 := bandCut 12 false (by decide +kernel)
theorem band15 : CutRow book 15 0 5 := row15_0
set_option maxRecDepth 16000 in
theorem row14_0 : CutRow book 14 0 2 := bandCut 11 false (by decide +kernel)
set_option maxRecDepth 16000 in
theorem row14_2 : CutRow book 14 2 21 := bandCut 12 false (by decide +kernel)
set_option maxRecDepth 16000 in
theorem row14_23 : CutRow book 14 23 13 := bandCut 13 false (by decide +kernel)
theorem combine14_0_23 : CutRow book 14 0 23 := @joinRow book 14 0 2 21 row14_0 row14_2
theorem combine14_0_36 : CutRow book 14 0 36 := @joinRow book 14 0 23 13 combine14_0_23 row14_23
theorem band14 : CutRow book 14 0 36 := combine14_0_36
set_option maxRecDepth 16000 in
theorem row13_0 : CutRow book 13 0 6 := bandCut 11 false (by decide +kernel)
set_option maxRecDepth 16000 in
theorem row13_6 : CutRow book 13 6 33 := bandCut 12 true (by decide +kernel)
set_option maxRecDepth 16000 in
theorem row13_39 : CutRow book 13 39 29 := bandCut 13 true (by decide +kernel)
set_option maxRecDepth 16000 in
theorem row13_68 : CutRow book 13 68 8 := bandCut 14 false (by decide +kernel)
theorem combine13_0_39 : CutRow book 13 0 39 := @joinRow book 13 0 6 33 row13_0 row13_6
theorem combine13_39_37 : CutRow book 13 39 37 := @joinRow book 13 39 29 8 row13_39 row13_68
theorem combine13_0_76 : CutRow book 13 0 76 := @joinRow book 13 0 39 37 combine13_0_39 combine13_39_37
theorem band13 : CutRow book 13 0 76 := combine13_0_76
set_option maxRecDepth 16000 in
theorem row12_0 : CutRow book 12 0 2 := bandCut 11 false (by decide +kernel)
set_option maxRecDepth 16000 in
theorem row12_2 : CutRow book 12 2 14 := bandCut 12 false (by decide +kernel)
set_option maxRecDepth 16000 in
theorem row12_16 : CutRow book 12 16 29 := bandCut 13 true (by decide +kernel)
theorem combine12_0_16 : CutRow book 12 0 16 := @joinRow book 12 0 2 14 row12_0 row12_2
theorem combine12_0_45 : CutRow book 12 0 45 := @joinRow book 12 0 16 29 combine12_0_16 row12_16
theorem band12 : CutRow book 12 0 45 := combine12_0_45
set_option maxRecDepth 16000 in
theorem row11_0 : CutRow book 11 0 1 := bandCut 11 false (by decide +kernel)
set_option maxRecDepth 16000 in
theorem row11_1 : CutRow book 11 1 9 := bandCut 12 false (by decide +kernel)
theorem combine11_0_10 : CutRow book 11 0 10 := @joinRow book 11 0 1 9 row11_0 row11_1
theorem band11 : CutRow book 11 0 10 := combine11_0_10
set_option maxRecDepth 16000 in
theorem row10_0 : CutRow book 10 0 1 := bandCut 11 false (by decide +kernel)
theorem band10 : CutRow book 10 0 1 := row10_0
theorem checked : mixedTables book 16 := by
  intro k hk
  interval_cases k
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact band10
  · exact band11
  · exact band12
  · exact band13
  · exact band14
  · exact band15
  · exact band16
end B4063_17
theorem h4063_17 : Face true 2047 17 :=
  mixedLower (g:=B4063_17.book) (i:=0) (hints:=4882524037)
    (before_sound B4063_17.entries B4063_17.prior) B4063_17.geometry B4063_17.checked
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem m473_7 : Face false 249 7 := lowerHint (lower_down h473_7) (by decide)
theorem m922_7 : Face false 474 7 := lowerHint (lower_down h922_7) (by decide)
theorem m924_8 : Face false 476 8 := lowerHint (lower_down h924_8) (by decide)
theorem m926_9 : Face false 478 9 := lowerHint (lower_down h926_9) (by decide)
theorem m1241_8 : Face false 633 8 := lowerHint (lower_down h1241_8) (by decide)
theorem m1242_7 : Face false 634 7 := lowerHint (lower_down h1242_7) (by decide)
theorem m209_4 : Face false 113 4 := lowerHint (lower_down h209_4) (by decide)
theorem m658_4 : Face false 338 4 := lowerHint (lower_down h658_4) (by decide)
theorem m217_5 : Face false 121 5 := lowerHint (lower_down h217_5) (by decide)
theorem m595_5 : Face false 307 5 := carry_of (swaps:=[133,117,101,33,16,48]) (by decide +kernel) m217_5
theorem m723_7 : Face false 371 7 := lowerHint (lower_down h723_7) (by decide)
theorem m1619_8 : Face false 819 8 := lowerHint (lower_down h1619_8) (by decide)
theorem m1755_12 : Face false 891 12 := lowerHint (lower_down h1755_12) (by decide)
theorem m1950_12 : Face false 990 12 := lowerHint (lower_down h1950_12) (by decide)
theorem m1631_10 : Face false 831 10 := lowerHint (lower_down h1631_10) (by decide)
theorem m2010_10 : Face false 1018 10 := carry_of (swaps:=[16,49,148,131,114,81,96]) (by decide +kernel) m1631_10
theorem m216_4 : Face false 120 4 := lowerHint (lower_down h216_4) (by decide)
theorem m408_4 : Face false 216 4 := lowerHint (lower_down h408_4) (by decide)
theorem m396_4 : Face false 204 4 := lowerHint (lower_down h396_4) (by decide)
theorem m476_7 : Face false 252 7 := lowerHint (lower_down h476_7) (by decide)
theorem m774_4 : Face false 390 4 := lowerHint (lower_down h774_4) (by decide)
theorem m596_4 : Face false 308 4 := lowerHint (lower_down h596_4) (by decide)
theorem m910_7 : Face false 462 7 := lowerHint (lower_down h910_7) (by decide)
theorem m918_7 : Face false 470 7 := lowerHint (lower_down h918_7) (by decide)
theorem m983_10 : Face false 503 10 := lowerHint (lower_down h983_10) (by decide)
theorem m988_9 : Face false 508 9 := lowerHint (lower_down h988_9) (by decide)
theorem m594_4 : Face false 306 4 := lowerHint (lower_down h594_4) (by decide)
theorem m989_11 : Face false 509 11 := lowerHint (lower_down h989_11) (by decide)
theorem m730_7 : Face false 378 7 := lowerHint (lower_down h730_7) (by decide)
theorem m727_8 : Face false 375 8 := lowerHint (lower_down h727_8) (by decide)
theorem m990_11 : Face false 510 11 := lowerHint (lower_down h990_11) (by decide)
theorem m991_12 : Face false 511 12 := dropFace 2 4882524037 m989_11 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem m1227_7 : Face false 619 7 := lowerHint (lower_down h1227_7) (by decide)
theorem m1235_7 : Face false 627 7 := lowerHint (lower_down h1235_7) (by decide)
theorem m1292_4 : Face false 652 4 := lowerHint (lower_down h1292_4) (by decide)
theorem m1289_4 : Face false 649 4 := lowerHint (lower_down h1289_4) (by decide)
theorem m1290_4 : Face false 650 4 := lowerHint (lower_down h1290_4) (by decide)
theorem m1487_10 : Face false 751 10 := lowerHint (lower_down h1487_10) (by decide)
theorem m1497_9 : Face false 761 9 := carry_of (swaps:=[146,50,100,131,82,16,112]) (by decide +kernel) m926_9
theorem m1499_11 : Face false 763 11 := lowerHint (lower_down h1499_11) (by decide)
theorem m1501_11 : Face false 765 11 := lowerHint (lower_down h1501_11) (by decide)
theorem m987_10 : Face false 507 10 := lowerHint (lower_down h987_10) (by decide)
theorem m1502_10 : Face false 766 10 := lowerHint (lower_down h1502_10) (by decide)
theorem m1751_11 : Face false 887 11 := lowerHint (lower_down h1751_11) (by decide)
theorem m1759_13 : Face false 895 13 := lowerHint (lower_down h1759_13) (by decide)
theorem m1806_8 : Face false 910 8 := lowerHint (lower_down h1806_8) (by decide)
theorem m1871_11 : Face false 943 11 := lowerHint (lower_down h1871_11) (by decide)
theorem m1879_11 : Face false 951 11 := lowerHint (lower_down h1879_11) (by decide)
theorem m1885_11 : Face false 957 11 := lowerHint (lower_down h1885_11) (by decide)
theorem m1886_11 : Face false 958 11 := lowerHint (lower_down h1886_11) (by decide)
theorem m1887_13 : Face false 959 13 := lowerHint (lower_down h1887_13) (by decide)
theorem m1934_9 : Face false 974 9 := carry_of (swaps:=[148,84,131,114,97]) (by decide +kernel) m926_9
theorem m1935_11 : Face false 975 11 := lowerHint (lower_down h1935_11) (by decide)
theorem m1951_13 : Face false 991 13 := carry_of (swaps:=[152,117,67,32]) (by decide +kernel) m1759_13
theorem m1999_12 : Face false 1007 12 := carry_of (swaps:=[148,131,114,97,80]) (by decide +kernel) m991_12
theorem m735_9 : Face false 383 9 := dropFace 12 4345653381 m723_7 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem m2006_9 : Face false 1014 9 := carry_of (swaps:=[33,132,147,82,97,112]) (by decide +kernel) m735_9
theorem m2007_12 : Face false 1015 12 := carry_of (swaps:=[132,147,82,97,112]) (by decide +kernel) m991_12
theorem m2011_13 : Face false 1019 13 := lowerHint (lower_down h2011_13) (by decide)
theorem m2013_13 : Face false 1021 13 := lowerHint (lower_down h2013_13) (by decide)

namespace M2015_16
def entries : List (Nat × Nat) := [(113,4),(120,4),(216,4),(204,4),(249,7),(252,7),(338,4),(371,7),(390,4),(308,4),(462,7),(470,7),(474,7),(476,8),(503,10),(508,9),(509,11),(510,11),(478,9),(511,12),(619,7),(627,7),(633,8),(634,7),(652,4),(649,4),(650,4),(751,10),(761,9),(763,11),(765,11),(766,10),(819,8),(307,5),(887,11),(891,12),(895,13),(910,8),(943,11),(951,11),(957,11),(958,11),(959,13),(974,9),(975,11),(990,12),(991,13),(1007,12),(1014,9),(1015,12),(1019,13),(1021,13)]
theorem prior : Known false entries := (consFace m209_4 (consFace m216_4 (consFace m408_4 (consFace m396_4 (consFace m473_7 (consFace m476_7 (consFace m658_4 (consFace m723_7 (consFace m774_4 (consFace m596_4 (consFace m910_7 (consFace m918_7 (consFace m922_7 (consFace m924_8 (consFace m983_10 (consFace m988_9 (consFace m989_11 (consFace m990_11 (consFace m926_9 (consFace m991_12 (consFace m1227_7 (consFace m1235_7 (consFace m1241_8 (consFace m1242_7 (consFace m1292_4 (consFace m1289_4 (consFace m1290_4 (consFace m1487_10 (consFace m1497_9 (consFace m1499_11 (consFace m1501_11 (consFace m1502_10 (consFace m1619_8 (consFace m595_5 (consFace m1751_11 (consFace m1755_12 (consFace m1759_13 (consFace m1806_8 (consFace m1871_11 (consFace m1879_11 (consFace m1885_11 (consFace m1886_11 (consFace m1887_13 (consFace m1934_9 (consFace m1935_11 (consFace m1950_12 (consFace m1951_13 (consFace m1999_12 (consFace m2006_9 (consFace m2007_12 (consFace m2011_13 (consFace m2013_13 (known_down baseKnown)))))))))))))))))))))))))))))))))))))))))))))))))))))
def samples : Nat → Bits × Bits := (fun i => (if i<8 then tableBits #[(padColumn 168 0xfffc0000000000000000000000000003fff,padColumn 168 0xad42b50ad42b50ad42b50ad42b50ad42b50ad42b5),(padColumn 168 0x3fff00000000003fff000000000000000000000,padColumn 168 0x1fc07f01fc07f01fc07f01fc07f01fc07f01fc07f),(padColumn 168 0xfffc0000003fff00000000000000,padColumn 168 0x303cc0f303cc0f303cc0f303cc0f303cc0f303cc0f),(padColumn 168 0xfffc00000000000000000fffc0000003fff0000000,padColumn 168 0x60c183060c183060c183060c183060c183060c183),(padColumn 168 0x3fff00000000000000fffc000fffc000,padColumn 168 0x504541150454115045411504541150454115045411),(padColumn 168 0xfffffff,padColumn 168 0xa52a94aa52a94aa52a94aa52a94aa52a94aa52a94a),(padColumn 168 0xfffffff0000000,padColumn 168 0xa9b2a6ca9b2a6ca9b2a6ca9b2a6ca9b2a6ca9b2a6c),(padColumn 168 0xfffffff00000000000000,padColumn 168 0xc9c3270c9c3270c9c3270c9c3270c9c3270c9c3270)] i else tableBits #[(padColumn 168 0x3ffffffffff000000000000000000000,padColumn 168 0x8e023808e023808e023808e023808e023808e02380),(padColumn 168 0xffffffffffc0000000000000000000000000000000,padColumn 168 0xf003c00f003c00f003c00f003c00f003c00f003c00),(padColumn 168 0x0,padColumn 168 0x0)] i))
def cols : List ColumnInfo := [(904,6,113,0,4),(897,6,120,0,4),(804,3,216,0,4),(786,1,204,32,5),(772,3,216,32,5),(772,2,249,0,7),(769,2,252,0,7),(556,129,338,0,4),(524,128,371,0,7),(536,65,390,32,5),(579,8,308,128,5),(560,1,462,0,7),(552,1,470,0,7),(548,1,474,0,7),(546,1,476,0,8),(528,1,462,32,8),(520,0,503,0,10),(516,1,474,32,8),(515,0,508,0,9),(514,1,476,32,9),(514,0,509,0,11),(513,0,510,0,11),(512,1,478,32,10),(512,0,511,0,12),(400,4,619,0,7),(268,128,627,0,7),(390,0,633,0,8),(386,4,633,0,8),(385,4,634,0,7),(355,16,652,0,4),(326,16,649,32,5),(325,16,650,32,5),(259,16,652,96,6),(272,0,751,0,10),(262,0,761,0,9),(258,4,633,128,9),(260,0,763,0,11),(258,0,765,0,11),(257,0,766,0,10),(76,128,819,0,8),(132,8,307,576,7),(136,0,887,0,11),(132,0,891,0,12),(128,0,895,0,13),(81,32,910,0,8),(80,0,943,0,11),(72,0,951,0,11),(66,0,957,0,11),(65,0,958,0,11),(64,0,959,0,13),(17,32,974,0,9),(48,0,975,0,11),(36,1,474,512,8),(33,0,990,0,12),(32,0,991,0,13),(16,0,1007,0,12),(3,8,308,704,7),(9,0,1014,0,9),(8,0,1015,0,12),(4,0,1019,0,13),(2,0,1021,0,13)]
def plus : Nat := 0x41080900910208408440840a012018021
def minus : Nat := 0x1f02904c8850e0928212388618930cc11c1701f
def orderBank : Nat → Nat := (fun i => (((fun i => (if i<40 then (if i<16 then (if i<8 then tableWord #[0x822da43830c0086816ec40009a23a88000168088620009a23b10800b680ece253ada72020d4eb69c80a353ada7202040056810a8414a5aa00185c2c68500a5001d810929800560424860015a009a1006c6882065,0x5a05ba1000859082a84121a22829400b68028e6822da43828c00769d6a02a121a25839400b60426e8001da75b89208b690e0a10005a13a9000086816a8200210428aa000b68108a4002904293a800b6810ce6,0xb025a14828400568028a60005a02aa100046912e200009810921acc669d40a10005a13a90800560426a80005a12a991048688a08300216420b280016856e640005a13b188001684884201b1a20821c00760426c8,0x7081a14021400b01d04a832a1a41018dc2c68500c70021a02a28a1466a8c081a121a25828c00b68026a492a1a95828c0016848a620005a15a90ac0968520e1000da24b9800026892e4020b1a11821400b60424a6,0x1d8109218008680a6820025aa4281000b59ce2ec002da03a28800b61d06ec4121a22818c001684a8420011a4528821466a8c0a10005a05a988005681086453ada7201840016808a82822da43820d4eb69c8063,0x4c12a10800a410a2a64120c22820c008300a8a20005a1329000026894e400011a45388006c68820a9001d810a4280056802ae80021a01341800568152e200210a59338000684ea02002d6738aa0004690ca20,0xda23a102cc669d40e170b1a140424008590850e0015810a3a800260428ca002da00aca00016844c860005a154a08001684d0820009a25498800469152420011a434108008410a4ca0015a001a0000669d2a20,0x2964214b8007608690c002d810a4a800b68111280021a05cc18002688d0620005a13a10010c41c206500158741ab0008680aac420b1a11819400760864a600110210a18003680f0c40005a13c21000b61d04a8] i else tableWord #[0x4c02a18a08b690e10553ada72039400b680f124002da023c900016848e840009a23c1900026888e640019a74c88000b21d04a88519aa30304003688ec6220b1a118325048688a0e78519aa3040c00a410a72e,0x1407411a0001680a86200118219aa00056810ca60011821921a84868960a54121222820c001480a8620005212a1080056910a24b319a75028c00b31cc2a800216421218004690c842000da201901c646890085,0xda25290000561d0468002d204229090c49c60650005a13a1080026894a20000da022a0a848689612732a1a41031c00b31cc33000290211cb0007408470c00110211bb00056806ce80005a05ca980056911068,0x70b1a140314ca86904083001d8219320003688ea400011a44a90208b690e08553ada72019400a59084a6002da021a900056a52a208209a43820400368932800009a24c98000469132400021a05aa1000a410a4a6,0x21a75b9900016854a400005a1229080036894e60b319a75048c00842967120005a15ca1800760864a8002da03a2800056816a6200150009a10ca8690408500298219ba000760866c80015a009a90008480a8a2,0x2d210029a1466a8c0830015a0529880046914a42002d004229000869d2a400015a4420900036808ec40005a023a91048688a0650009a23a1080026894a40001487411a000869d6a4271b122402140054910824,0x11821a3b000740842a8001d8309298009424a2a6002da021a800086808680002c8741bb000a40844ea00098109aa000560424a60011a44a88208b690e0810009a2220814eb69c80a1001182192a00086812cae,0x7191a24029400021d046a0015a04b23800561d048a000da24b13800b6810ac4000564209a00096a86804b025a148305c6c68900c700250928aa00056914a400021a72a99000b68086a232a1241020c00568068a4] i) else (if i<24 then tableWord #[0x5211210acc669d40c170b1a140214003680ea80000da022181c2c40500a520b1a11829c00760866ca001d021132800b4810ce600110210aa000760424c60005a1229000026888a200009a2221085496a8004b,0xb025a14848400868006a00001a1220080086812a800005a02ba9800b11ce0a8000087411a0008410a486002982192980054810864001d8219218002688ea420431a7081940016854e6000296420a98002688ca20,0xda03b2880086812ec0002902113a000b48068e60015204329800168448424121a228216cc669d408b01b1a20810d048688a0a30005a12a90a082690e0a114a5aa001be84868960c30021a001ab9c2c4050085,0x11a44b0b800669d2c0e61b1a54029406c6942065001986092980046910a0471b1a24029400460c24860015a40989000b6a8ea2070a9a14029400551d048a7091a14031cca869040a50021a012b100016844a64,0x1da75a8900086016a84002daa3a108ca831040639319a950284001680ea62000da23a90800b40028e60015000a298001680aa6e0021a052a000056814a600015a032a00001684ec42002da01a31000b680eac2,0x5a05b1b8000304a8020005a0229880006848a02002d210031800b60424c60005a12ba1800168152a2002d880929800922504a80005a12210000b68068e60011a4320800056816a82002da022280ca86904065,0xda001a380074ac0ec600112b03a980096a90ce40025aa1a39000b21d04ca00212d4b93000b4840ec6000923038980046912c0e0005a05298800869c064000150042190008680af06000da054b0ac0768520a1,0x2da02228806c30820650015a0521a9048688a0610021a001228005680046a001d2b02a100044ac0a640015a001228003680046a00152802a100024a00a64822da43830400868006ce0015a001ab8008410a2ca] i else (if i<32 then tableWord #[0x820da43830c00b19ce2ec70b1214031e1464a8c0c18519aa3033c005680ccae000da033238001680cc6e0005a133138001680aa620015a0092280026888620a121a25820c004691480a00296420aa0001410a468,0x2431271821c00548068a600210a58a29c6c6ad00a5002164202a000869ca842000185191a00036810a84000da009a1000868048a20015a41a0911686a8a08300190528aa00054010a84622da53828684768960e5,0x2cc730bb00016854e620005a133189c2468500a500212012289048488a0a30005202a988001484aa420005a133100004690cc200005a1531000046914c20a025a34833c0074ad2eac00112b4ba300074b52e2c,0x35a1aa1023c008680aace0021a01233800742c4ec800110b13aa0001430ae6a002daa43390001684484e00210d2b92800b6a8ece2002daa22b880074344e2800290428aa00016814a60b319a75038e1466a8c0c3,0x5a032980003694ca40000da222108003688ca408209a43830c00b11ce2ec01b1020821e84860960e5412182282940086016ec40005805ba10001600aa840005815b990001604aa64001d875b8911686a8a0af,0x21a011a10003680e8620019052921a8a861160a545a18a2819684168960a3002d2a4209000a40842a6002589412a00095a4e2a8622da53828c000688ea62000da03a988002688ca408229a43828c00868026a4,0xda24a900007208690c0010821a3b000a59482a60029a221a88003688e8420011a2529800046954a200029a23a28800762c26c88229a43830c90c69c6087001d8309b20008590828600152019a100036888840,0x5a132938004690ca2e0019a94b3800046912c2014a5aa00286c096a120a120b1a11821c00568068a60011a44201000022504680005a0221828a869160a30005a12990a082690e083002c4738aa000b40026a4] i else tableWord #[0x14074122800868088a292a1a95833c0016856c4e001da75b0b80074356e2c0015a94b3800094290a04000504289a0001590826a0015a001a80003680ea829319a95033c009324ceca0005a0531b80016854c4e,0x112a4ba300054840e860025aa42b90000684a8e2001da75b00800561d08f00015a0443a000869d2e60b305a75028c001329426a0005a1529080056812a600029821a4b000b6806d280005a042991c2c40500c7,0x25aa3b3800074b40e060005a13b100002688ec20b025a84833c00b11ce0ca00290428b2000062024e6002d2803b180026892c2e002d2d038980016816c62001d2d4b832c0968520cf002d8741328005680068e,0x2d2b02810005691080220b1a11818d048688a08132a1a41018400460862860029aa19a8800568066820001a82a28000b4b40a040005a12a08000040842680015a043290002688062e0021a02ab0800b4ac0e26,0x290428218001681484a002d8108a1000560422640005a1520a80083354a280015a009188002689480a0005a029900001684a62070b1a14020c00561d02680029aa4228800568108620009a201028008680a680,0x9a24a90000830026a40014c009a10001680ea6000210428a18002688042a002d2b0289000a6a8e8a0001d2d02810002688e8200001a82a2880006a046a2002d2d0289000a6a888a0001d28028128486896081,0x9a2520a80073354a087519ab301ad048688a043822da4381854eb69c804100210a589a0005680c64a0010cb5292000531cca460009a2318a8005324ca26001da75a00800a410a4a800050a591a80016816a64,0x19a711a880036ac88a0001d8d1a81890c69c606b0431a70812c0056202a840009880a99000869ca8a20021a711a8800b6342a240011a419828ca8690404300290428a1800a590808600290210a100044084264] i))) else (if i<64 then (if i<48 then tableWord #[0x5213b188002488ec42000561539800025894e400011645388000859080ca001d0210b20002688cc2e002ccd338b0004690cc0e2331a7181ac0cc69c204b0015a019a2800462c6a8600118b0aa100004084246,0x21802a288001600a8620005812a10a08b6b0e0a1002daa42890005680ea800020ea5933882c4846087b31987503840016054e60000982539000046114e20822d243830d4eb49c80a3b319675038400b480ece2,0x1d8b1929800868046a2000dab3a90090c69c60658229a43828400261d046a0021a019a90003680ea600005a012188008430a2a85385a72020400809080a8000d04289a00056806684001da72a009168628a083,0x2d203c49000b4808f24000d203c3100034808ec400052023a90001484f08400052123a10002488f0640009222399000358932800009624c98000459132400019674c88000859ce04a001569380a8000688ea60,0x11a4018b80044980e260005a04b1b800a48c0ec6000d2b4b931c6c48900c741212228294ca84904085002d202ab90008480aac40021272a9900056814ea0000da053a0208b490e10553ad2720396c095852121,0x4a12a1080096a8ece20025aa22b880074b40e260019a70183800a4ac0e06a025a64833c5296b0006f00212c4bab000b59ce2ca000da04b2380034b12e8c00292603b180064980ea60025ac42b900096b068e4,0x216012b100015816e840005615b9900015844a64000da0332880026894e420009a2331080035892e600009624b90000659d2e20820da43828482c30460850014c009a91048288a0830020a02a288001280a862,0xda032a00008600aac400210c2bb2800669caa0e0021a021a0a1436a8c0a10014673022806c5882065002d6009a900055802684002d202a2880056814a80a1216258394ca859040a5b02561483840085816ec4] i else (if i<56 then tableWord #[0x11a532881048488a08532a1241019400740844a60011021121800848046a48511aa3028400061d046a0015880921800469026240029aa4281188b690e0a37519aa3028400659082a8001da009a900014804862,0x29851929800a69066a40010cc500a80036914a60000da5529021466b0c0a1001985192a000641442a80014c9300a8003690ca800015a432881d466acc0a100196520aa000859ce24a0020c730128000688ca60,0x21605aa09c644890085820da438205c6c48900a500152042a1000831ca8427191224031c0036888a62a121a258314ca76904065000da04b1b800a38844c6001ce21129800438844860009a24b13800868046a4,0x19a75a81000b48066a4000da05a98a8a869160a5002905112980064144486001da71189000a414a4a600202a58a2800869c464271a922402161436a8c081002d47412a000551d0468a121625828cd685a84063,0x21a05b290003688eae2000da2223880046146e26000da232b800056914c408229a43820e1446a8c081002d4738aa000a40844a6001d02112191686a8a065b305a750284004429646a00210c2921800b680a6a4,0x118309aa28a069160a500200a59228002688864233a582403ae04961c60e7a281a45831400b48066ce00200a592b0005480668e00290429320003029646c001d821ba980046086e860015244293800869c46e4,0x2924422900056250428622da53820dd466acc08100156938922cc569d40e10004ea592380012a9408e00118b09aa21456a8c0c1002d4738bb1047688a0a553a9a72028c00a390a4ea0020e42932800a60c26e8,0x20442143800111084ae000da223a1090469c60c9329da41031e80968d21210028e211cb0007388470c0010e211bb000020868ac0021a71321800962464a661b125402161466b0c08100210c58a280066146486] i else tableWord #[0xd6001a380034a92e8c00290210b200024840e86000d624b138003588064e0009624b0b800068448e20005a15b10800659d2c0e0009a253081047688a0e75389a72039680969921210028e429cb800a110852e,0xb025a84820400b21d048a001487411a8009424a286000d224a9200056810a640000285a0280056a5282070a9a14031c82c3046065002cc019a900053006684b025614833e42b4a800e700216001ab80035812c8e,0x2daa42092080690e081002c07382a000868026840005a03a18186469500850029860929800a60c24a60014874122800b6a8882000290528a9800840026840005a03a1880044110824b091a1402964a86a56083,0x1da252a01c6468900c77519ab3030400521d06ac6209a53820c006594828600144938921c6c6ad00857101a25828e882690e0a1822dac38204008029628a00296420298008430a286000c4b3a128002588ea28,0x1102112a000342d646c00212d481b00056810ea60021a012390005225064e0015a44391800869d6c64001d2d480b0003688ee620009a23b90800769d6c240021a74b1800056a52c40001da74b08000332d404a,0x2d8809ba000342d624a00212d4812800069d6a620001a74a981c6468900e792a1a958316082690e0e3b025a84830400b21d06ce002c4738b3800521d06ae00216420ba8009424a4ca001d8219ba000942444c8,0xda04ba80ca831040830020c0122880013044842822d24382854eb49c80810005213a900002488ea20a11da25849ecc569d41230020ea59c480013a966b20004aa50ac800869d7286000da254a0ac096a120e1,0x296420bb000a60866ea0011021132800560426c8002cc01ab9800b30028e60014c00a31800b300ace4002cc012b90001300ac840004c12b1900013044a64002da0233880016848c620009a2231080056812ec0] i)) else (if i<72 then tableWord #[0x24cd338280086812ca07519ab302bc0056814c8e0010cb53a3000332d4e4c0011a4530b80073354e2c000da24b10082c30460a701b0c20821d048308a0c532a0c4102954eb69c80c314a5aa0020400a410a4ec,0x53acc72020c00130088620005013a90800130488420001013a80800748400c60011a4330b8000684cc0e0024cd338321466b0c0af000da0532380033314e8c0004cc539b0000324ce6a0020cd539300043314e2c,0x156920ba8009424aeca000da05b2380094244ec80001092b9a8001684aa4e00210d5b930008424ae4a00250d2b8280056812ca001a9a2081945226a80061001d410929800550424860014410021a08b410e0a3,0xb01da148386083690e0a3538da72020c00819082a8001d0b593380646882065001c8109298005204248601b1020819400b4010ce6001da74a880001680ec620001a12a8380096a90c040001a13b009c2068500a5,0x4120c32820d4eb6a0808100118319218003414a248001cc12a28800762c24a6000dab3a90890c69c60850009874122800051ce26a0009880921800868068a40011a4428900096a8ea021491aa00184005621048a,0x2091a118324ca169040c79319a95048dd466acc1030024c930cc000a088472c001c2211c3000408846ec0019a94c881048308a085001905292a000059ce26a0004c02a19000768806a00000c12a01000068cea02,0xa2a1845828d168628a0630021805aa08008600a682001504420900056914a207091a140426083690e105002c87424c000b19ce530002d21004a8001680f0a40021a054c080096a86c080001a12b818000684f004,0x2c6738aa2cc661d40a385190a3020c0056014a6200118452908004410c842a29d8458296cc569d40a15389a72018c008429648a0028e4292980081108286001d875a892c0960520a10011844a90000661d2a20] i else (if i<80 then tableWord #[0x4ca509b000059ce46a000564211a000268888e4001d0d5b93000b680eac40009a253388002688cae20019092b8a0004690ca420009a24b380000418ae080011a44b10000669d2c2070910140216083690e083,0x2d0042b1000b40026c400250d2b8200056812c80a121a25833d048688a08f822da4382954eb69c8085b319a75030e1466a8c0a30021a02a2b800742d6eac002cc730b2800a414aec80019052baa000859084a8,0x11a453908004690cc420011a44b90000669d2e2000102a509a800a6a88624001da74a901c204050085708101402940086816cae002c074132800b09ce2ca00156920ba0009424aec80001092b9a0001684a84e,0x622da438215d466a8c083000167391a000b680e8a4001da001a0010c41c2087822da4383154eb69c80a5002964213a800859084ca002da022b900016808a840005a13b1900016848a640015a053a880016814e82,0x212021a00001484e84000256920aa00044b1202a0015a74aa014eb6a08065002da121a900056854a628229a4382161446a8c083002c8730aa010c69c2087a2a1a4583951686a8a0a5002daa3b1080056912e40,0x1da10a1a800442c2a4800140742118007604286200118b0a908000684a40a0021a700a00009434aa0400042a509aac0568520a10015a04aa024a76a560a35389a7201840093a4a2a653ad272018400b48086a0,0x29a02bc9800a6804d260029a03c49000a6808f2445a1aa2818e84068960a3622da43820400959ce0a800190428a18006590808613a0014021d0686aca04b02b1a9080ae00861c208314a5aa00084001684a48a,0x2da01349800b6a8f064002daa2399000669d72260019a72b89800a6a88e240021a74ca000006857206001da74c9024c669d4123a025a14848400931cc3300029810a4a800a68111280029a01b4a000a6802b28] i else tableWord #[0x11686a8a0e735a1aa1031ecc169d4123b01da1484840040a942f2000c2a50b4800742c470c00110b11bb000b680af26] i)))))) (i/16) >>> (42*(i%16))) % 4398046511104)
def orderClauses : Nat → Nat := (fun i => (if i<96 then (if i<48 then (if i<24 then (if i<8 then tableWord #[0x2222460100012204c058038e02428847ea2043e3f009968006878010fb43a3e8030014380ecb38962cc0550da0,0x4563fc0012204c490038e02425a9150fd45204d142271fc0087d96900c0051303b44a890241664462f0069f,0x918bf062000930be2e6388b91712e05bc5e8e12dc5b415a342d85ad19a324628c092a2f45c8b5161d,0x2008f493a3c4765dcbb23a2ea5d11ca3846e8d91a8f,0x2009149397c2f65e9221792f090d212414808fd1f0f,0xf01081903a03c040340a6044128180400a00801c05c0380f82d04809c050420460d80b80b0660c8161e,0x25049d2817c2fa93d2724d49892d2524949091d230f,0x2000981e8072ee5d8399752e89552a2534a4944718f] i else (if i<16 then tableWord #[0x200124720432f65e92d9792f0968272594b095d2b0f,0x2fc2640b00702600c0125e4ba3004c0974b8054068f,0x1344a40482f00a988c0a61300980bf9010c297c728f,0x4a1369834d89ad352694d099d332654c8609318e,0x4a0c18494e810cbea734e49c53826f3049b8c20e,0x9f13d82607a01cc28734f49e53c2774ec9d4718e,0x50aa101303d00ea0cc2a820e6a054027f4fc9f4718f,0x103a82607a058038130e826c0303b090054068e] i else tableWord #[0xc58bf062000930be2e6388c51705146245ea8920a620820e605661c60a8850e6189292a50c40c811d,0x1e02103207549a925226302504c0221dc310180400a00801c1380b80707603e0b412027520a3c0ba8e51aa3145a1,0x18d5300640e8c401e0214b98c094130088770c430c968c213a4189612b01c1d81202701408c0b80b52ca554a20,0xf0848210324c8078340941307410820e060100e70200700713103e0909800a25e08c0592e0660c8161e,0x2660840c81d31e0201a0e931c044128180400a00801c05c0380f82d04809c050420460d80b80b0660c8161f,0xf01099003a03c04034532044128180400a00801c05c0380f82d04809c050420460d80b80b0660c8161e,0x80001319102600c010060020ec4f048534054068f,0x4d43a82607a01c9a0740e60181da9b090054068e] i)) else (if i<32 then tableWord #[0x103a82607aa707e0740e60181d896090054068e,0x2141e15001600e04c018023243154fa9e53a0549b0f,0x80001301600e64c0180200c0041d89e090054068f,0x103a83d02ca9552074546a881d896216055508e,0x7e0dc2183e1d827c090440283181a8eb1d41e40d0f,0x8000ca01600ea980180200c0041d89e0900549b0f,0x1390000980b0070263b49c0060020ec4f09626e2f00690,0x27a4f05f0161dc4eccc99832e659539952184e8068f] i else (if i<40 then tableWord #[0x5580981eaab00e04d550735520181d99a5504e89b0f,0x3380981e81600e04ccdaaf0e60181daae12cab4718f,0x21a0001c8e433a0c0278120700502283518e1e40d0f,0x98c88073263b4012b2002ac44f0485602f0068f,0x80001301600e04c0180200c0041d89e090054068f,0x101880017c058640ee0060accb12a218054068e,0xc40012617c388828e6056304c312525440c810e,0xda20c2c0a810429d612c1196205600ca14c2003f86c14a1f8520ef1461f42b86b0d41f0348a20ac1ec2a8a1192280342bf57caf55e2bb574ae55c2b70a819c330650f419031ab656aad159b7] i else tableWord #[0xb28cfac959003c0406e10a128260110c430c6109d20c4b09599e58eb196280a10802d622c31981682c9e,0x3460100001b012438230e03443f4d081e59ab30018021f6b2c0093f3400301482227c16c281b,0x2d95b001018800036438230e0242b5d6b2d55a832169ad20060ac7dad15a05a4a093f59e5016702927c694d220,0x918bf0620000780810a5c8b88252de2f47096e2da0acb616b1e0b796e8a95b850866adb5b469cd31d,0x80017101600e04c0180200c00570ae05be054068f,0xb90bf1aa1e2388828e6056b8cd49a821e40c810e,0x80004c81600e04c0180200c0046009812e054068f,0x10188001e2058640ee0060acd590f218054068e] i))) else (if i<72 then (if i<56 then tableWord #[0x3580004cae500e04c0180200c0046009812e054068f,0x7842410af35e46c4d82f10946bc7410820e060100e7020071782ef5dcbb5762eb35c6b5752e95d0b9d731f,0x5f0264151b30600097baf65ea2604baf4364338550f,0x80004c84602600c010060023004c09728616c880f,0x1350002657d1345f200c010060023004c09728616c8810,0x4283c01b0121180f0030043140602904416c280e,0x7e1001503e22227c090441e4bec55945288338238f,0x3806fc5f83100003c0408537c6f57e8253782f4dd9462086e8159b93706dc781b636a6d0a10cd5f869cd31f] i else (if i<64 then tableWord #[0x100001b0121180f0030040040602904416c280e,0xc69c939071c078080dc2142504c0221dc310180400a08314825651ce32fe38a710e19c201408ce080b2241682ca1,0x1e021032074078080dc2142504c0221dc310180400a00801c1380b80707603e0b41202701408c0b80b2241682ca1,0x2660840c81d396020370e9394044128180400a00801c05c0380f82d04809c050420460d80b80b2241682c9f,0x4e40001b0121180f0ed2700040614939a730280e,0x27a4f0788461dc4eccc99832e6ad801955fe738880f,0x60802581b02006009808012940301482239e16c2810,0x22674404b0903cc21839d00025280630639ec14280f] i else tableWord #[0xc398681b0121180f30c616c28e9914202748280e,0x1d5012c51898ed004c49888013a8030a48226207318791,0x4f4188001e2c698cb182760ad8b90f62c7398a8e,0x21a1d42094b07475ceb31f22ac798e8ab638c6c238f,0xc4001aa1e2388828e6056304d49a821e40c810e,0x346c9c94b26036024870461c06887e9a103cc9592323644c859013f34074c8a10127c748281b,0xca4cf81903a310e58080dc3a4e501104a30c6109d20c4b0cf00e19e3cc050a9108ca00b80b1981682c9e,0xcb05605d298058038130e826d9585c6542f0068e] i)) else (if i<80 then tableWord #[0x1a20e4248e40861c02f0ae15a4580a04e1a01bc0d0f,0x3445603907a390381d822a2b40a0d21a01bc0d0e,0x65c0e424b2d0862182f0d315a4580a04e1a01bc0d0f,0x344563316600a81d19d22e45456b2f3b22bc550e,0x1a20e42482a0741c02f0ae15a4580a04e1a02bc550f,0x66a0e42482a668ccc2f33215a4580a04e3b22bc550f,0x344561da07a0e99b9d822a2b40a0d066c2bc550e,0x770ed8410800a81d051160460a704b29a3d0238e] i else (if i<88 then tableWord #[0x2686b0410800a81d0516707745884b1aa350238e,0x33c2a01041503a0a2ced9d0b13be12cef14f6723d02390,0x2686b0410800a81d0511604605884b1aa350238e,0x1580dc038f522e26d9f1e12a4cf4691512167800d0f,0x68810420343074145a13416802c42594f288cfca98f,0x1345402082a074145a334516277c259de1aa350238f,0x2686b3490800a9a43471604605884b29a350238e,0x35b6b4d6494950036024233586aed59aa81e6a8d4da93516a0d3da734d280d308a101696d28d21c] i else tableWord #[0xd786b0410800e9ae8b03c42c4258d56b83d0238e,0x7b021032074078080dc2142504c0221dc313603c6d7c0801c1380b80707603e0b4678f30142100b80b1981682ca1,0xf63c8065b20c401ed8c37085094131b10776c230c968c213a040aa09c01c1d8678f30142100b80b1981682ca0,0xf63c80640e8c43ca02037366094d94088770c430c968c213a040aa09c01c1d8678f30142100b80b1981682ca0,0x3d81099003a03c0436a10a128260110ee189b4b683ccd9c0801c1380b80707603e0b4678f30142100b80b1981682ca2,0x2686b36d0800a9b6051160775b59e71aa350238e,0x1a21042014b07475ceb1ec3c47acf51e915e7a0a98f,0xdcc5603907a0a9b937122edc1b7b6e1a02bc550e] i)))) else (if i<144 then (if i<120 then (if i<104 then tableWord #[0x1580dc1303d00e3d5ba09b0e67846919a216780718f,0xdadf02c0a8104dec4708d196205bd0ca14c2003f86c6f27b9bc1ed6ee1f42b86b6ec1f0348a20ac1ec2a8a1192281ba88c1161c86c0d70e2228448880a819c330650f4190318b41662c843b7,0xda20c2c0a870829c47383196205c10ca14ce05c037f14a1f8520ef1461f42bb7e0d41f0348a20ac1ec2a8a11922803408c1161c86c0d70e2df4448880a819c330650f4190318b41662c843b7,0x726e487f8310004885f10e7225a9c838f71ce34641681fce3015b8b7143e8a0b8971059dc389670c695c29f,0x1fe0002e92400e04c7f00200c0042e08f0be2f0068f,0x72c0e41303d00e6cc8b89b72ae501a8482165540d0f,0x1200e4248b50862182f0d30241100a04e1b21bc0d0f,0x900000e45a8862340c08c8120700502283518e1bc0d10] i else (if i<112 then tableWord #[0x1200e42482a10c17869812088050270d928a338550f,0xe5c1081903a03c040340a6044128180400a00801c05c0380f82d04809c050420460d80b80b0660c8161e,0xe84ed3a0092e7dcf39d738e6dcd0967327bdcc0e,0xf07c8151f1060464f83a4096e8dd1145364338238f,0x1200e4248b5086219d28d30241100a04e3e61bc0d0f,0x900007d05a8862340c08c8120700502283518e1bc0d10,0xdc038f50600081c0012a41141a9513ea5540d0f,0x1fe000ca12400ee9ccd8fe0040180083b0902f1d30f] i else tableWord #[0x480000722d4ab11a7507d8090380281146c93718e1bc0d11,0x1d513c0722d4ab11a7527d8090380281146c93718e7dc0d11,0x2260e5d73ad2ae4641c3ac028114690c77567dc0d0f,0xee1db84976ced421bb4766ec9d8bb075e4e8068e,0x2686b3bb0800a8f88b0774ee4f394f1aa350238e,0x1df021032074078080dcef47484c022ef0310183c60a00801c1380b80707603e0b4120270142100b80b2241682ca1,0x1207c82014b2ac7b069bc00887acf53bf3d22bcf40f,0x7b47e5ec81d188f60043d77acf55ea3d37a4f45e809d79ef39e6bcc3f0f2de53c979009de38a978c0d9e2bc4786f09e0a3] i)) else (if i<128 then tableWord #[0x3704c7e87a957004f79ee8017b8278690487b63685b11,0x3d81081903a03c043e00a604412bdf3cc0a00801c05c0380f82d19e09c050421080d80b80b0660c8161e,0xda20c2c3e710429c4708d7cc204fdbe514c2003f86c14a1f8520a37c8f8c2b86b0d41f0348560f61545091b7c45643408c1161c86b871114224440542b0f84330650f4190318b41662c843b7,0x103a85d298fadf50130e826c0305c0befa5f40e,0x80002e81600e04c0180200c0042e08f0be054068f,0x10188007dc058640ee0060adf6bec218054068e,0x80d016024038040d200c007feff8743fd030ff073bfb7f4fe5fc3f77ecfd5fa3f37e4fc5f83ef0660c8161f,0x80e0680400006c048f74050320581e402568018024007fe050fa003024ff408280030148223fb01cfe1e] i else (if i<136 then tableWord #[0x4070580203100006c7b8054050560a0c840304cadc120060ad001ff8223e8ff4104080a4fec0f81c3e0fe1f,0xc58bf0620000780800a6281298917a384c4104834818159871e03060c8a92ba3360c41740a3e0ae1d,0x100042083e0140f0030040060f41d8381360d8e,0x484a176120fc84708a108060021704785f0c2134af10,0x80002e8051f800d038060021704785f0c2134af0f,0x26a0002e80526800d038060021704785f0c2134af0f,0x4283c01b0120140f00300431406029044820290e,0x834188000103dc02c2f85d0b6160e12be518ad15b85639815a0c8550a4a0c2818282d050a92ba33504c2784c3e0ae22] i else tableWord #[0x8600000480541e00c7c806002838060220c2244290f,0x3806fc5f83100003c0400537c6f4129bc17a6eca31043740acdc9b836e3c0db1b53690d0a10cd8670ca189f,0x21a0002096000a1c02883009e048258ab23836a1a8f,0x100001b0120140f00300400406029044134290e,0x840e49c838e03c040340a6044128180400a21b14828e718e29c4386708050420460d8e080b0660c8161e,0x42a1b81b0120140f00300431406029044820290e,0x90e82e81600e04e1cc3800c0042e08f0be054068f,0xf01081903a03c04034876044128180400a00801c05c0380f82d04809c050420460d80b80b0660c8161e] i))) else (if i<168 then (if i<152 then tableWord #[0x100001b87a0161e00300400406029044134290e,0x4ccfc81903a310c78080683a4c701104a30c6109d020550fc00e04809c050a90460d80b80b0660c8161e,0x6b00043e0120140f00300400406029044244290e,0xf01081903a03c0443f0a6044128180400a00801c05c0380f82d04809c050420460d80b80b0660c8161e,0x806c04c4188000c7c8064220301491e0c21348e8f,0x4e40001b0120140f0ed2700040614939a134290e,0x89044ce880588f11a22c443a0810a544323c3e2210f,0x33806c0480503d1287c8064220322491e0c21348e8f] i else (if i<160 then tableWord #[0x103ac4f29805a270130e91362644b0be054068e,0x22b1d50120162ac543003e6299d4018452290618a31408e91,0x62000040051c2818158f01822a4ae8cd40a3e0ae0f,0xdb17c2c0a81051784708d8bb1708f8ca8b62003f86c8b47ba2c9ed8b01f42b86b0d41f0348a20ac1ec2a8a11922803408c1161c86c0d70e2228448880a819c330650f4190318b41662ca2bb7,0x4691061605408214f1a0468cb23e7ee33c661001fc3621314a1f8520ef1461f6328570d61a9090691441583d9620aa46c5006811822c390d88c81c44508911118c2a1610ce194324628c318043b8,0xda20c2c0a810429c4708d1962048f8ca14c2003f86c14a1f8520ef1461f42b86b0d41f0348a20ac1ec2a8a11922803408c1161c86c0d70e2228448880a819c330650f4190318b41662c843b7,0x2411be3702a0741c02f0ae1b658e36c6c8d633a350f,0x2e85c8951bd1c84a0b81262dc6e8dc1251c6380e] i else tableWord #[0x2401042002a0741c02891115c36c790ab288338238f,0x3b81063b82a0751d828c758e8538258f28e63d0a98f,0x11e4ed8410811e01d051160460a704b29a3d0238e,0x2e85cc7e8fa0bc4a0b81262de3e47b8f42ec300e,0x2401042002f0e0444570db2c63c85591c428368728f,0x9021e24002f00a21a3f83009e36c258ab238368728f,0x126e4d49993125e4b0f700b2564a4939252464815f91f23a46c8c91722a44c8890f21a4291e90920e411e,0x836538780123dc02ca694b29251ca241e57cad15b0072840120c94127e4f19218a82d0520e01808904c9d9385902922] i)) else (if i<176 then tableWord #[0x9501e04a82f00a0f81821609e36cf816542a590300f,0x2e85ca171bc5804a4ab1262dc6e8929552a4300e,0x2e85c8951bc0bc4a0b81262dc6e8dc1242ec300e,0x2109752e65c1b13600d0d7cb796c0601002829051e5acb49672ca58cb035c6b657cae4312b6561c,0x12fc4acbe05e0144a21697b2f0b28929762ec300e,0xf2624c3984794040340a6044128180400a00801c05c0380f82d04809c050420460d80bcc1431300161e,0x131c5c89598c0be628b81262dc6e8dc1242ec300e,0x2ea650951bc0bc4a0b8127326640dc1242ec300e] i else (if i<184 then tableWord #[0xf0024fd00599a55c7c8c5998030114cb0c23688e8f,0x7e0de6883e1d827c090440283181acd099f3380d0f,0x7e0de6983e9a427c090440283181a8eb1d41e40d0f,0x7f3502183e1d827c09044028318690eb1d41e40d0f,0x7e0001b82f00a0f8180df09e0481c04506a2445b0f,0x266b0053020c0010380025fc060229aa7bc728f,0x7e0010b96000a0f8184d709e0481c16542a244300f,0x7e44c1b82f00a0f8180df09e0481c04506a5905b0f] i else tableWord #[0x1396724e39c5386704df9bd3766e4db9b53666c0e,0x7f3a824ce90873a02f4e79cc1100a04e3e61e4c20f,0x21a7d2758e40861c02f0ae0241100a04e1b21e40d0f,0x6d106160410a711c2367b0819eb3d04007f4341b1098a50fc29051cf30ae1ac354f29e33c10c8569df3b8b1055236564344ed9d81c83888a1122202a1612b019c330650f4190318b41662c843b8,0x1b441858a1141c4708da0c206828a6a08868365030fd40a8087d0ae1ac3507c4241a50c856a013fcb10552365643408c1161c83888a9fd3f42a1612b019c334fc9f618e7d4f99f13dc43b6] i))))))
def orderGroups : Nat → Nat := (fun i => (if i<48 then (if i<24 then (if i<8 then tableWord #[0x3cbb3a797736f36aa9a5a39ddb4f4ecbd0d0c9a0928a84655143322c292619140d0b46010480402410087,0x3cbb3a7978f736b675b4f3b372eb679cdb56cf8f4ecdcbc7d8d0c9c4c2a08c6052322c2925231c19160d0b4a010080402410087,0x3b3aba7978f736757372ef2e6ba6dd9d5cd9d5cf8dc756c8c1a898918a89846462545145433431261915130c56010080442010087,0x34c6caa5693246260408102046,0xd32b256994c6220408102046,0x39b978f776f1ef2e6deb5ed9cf438ec5c3a4a19891896359393325150c0a0642010484442010087,0x38d32c5958e34b260408102046,0x34c6d99a6532c8810244085] i else (if i<16 then tableWord #[0xd31b2695a4c9220408102046,0x32b2996371a591260408102046,0xcacaa58dc6d6389810284045,0xd31b2a699553189811204085,0x38d72b2658e34b1ca910205085,0x35b666994cb1c8810245085,0x34c6aa669585ce34a810206145,0xd32b2996371958d2cb810244085] i else tableWord #[0x3cbc7b7af774f39cd78f8f4ecdcbc7cfe0d1c9c4c24c32312d2b1d130636010080442410087,0x3978f6f1ef2e6deb675f1ed595538f4790c2a4a198938985615852514a443933251a16150c52010084484420107,0x3af976f1ef2e6deb5f1ed595538f478fc2a4a193898568615852514a443933251a16150c52010084484420107,0x39b978f6f5ef2e6deb675f1ed9d78f4fc2c1a4a19895938962615852514a463933251a160c56010084484420107,0x3978f776f1ef2e6deb5ed9cf438dc5c3a4a19891896359393325150c0a0642010484442010087,0x32c6ca658dc69958d2cc810244085,0xd73b5a64b187850244085,0xd73b296cd187811244085] i)) else (if i<32 then tableWord #[0xcaca658dc69958d2cb810244085,0xcec9a571b587812204045,0x34caaa668dc655260408102046,0xcaca658dc69934b18b810244085,0x34caca658da591260408102046,0xd2d99c6994ce2c9810309085,0xcb1b2b99c655349810244085,0xcb1b2b95c69958e34b810289105] i else (if i<40 then tableWord #[0xcb1b6b753187811244085,0x3cef37cbf1fb7ebf7bd3efcbeeefa767d9ddfd7ddcf1f92e1783d2f33caf07b2eb3aaea7a32789ce6b9664d91e398d62d71db569d8d5e5733e4f339cad1e8761d44e0b81c9301a0e4890e308a62384605615434c523424c32c4a528c891c87118c4a124461142a098180500c7e0040481108410882104008010a,0x39b978f6b674f2f1ef2e6deb6766df1e9d9b978f94c2a4a1989389856458524a464138322c1a164a010080482010047,0x3cbc7b3a7978f776f18f8f4ecdcbc7cfe0d1c9c4c232312c2925231d1b063a010080442410087,0x3cfaba7736f5b5736f29a7a75d9d5ad9d755cfd3d1c8a0928a89846253494534323129261d1b164e010080484424107,0x3aba78f736757372ef6ee39d9d5cd9d755cdc793c8a9998a8462615451454335331c063e010084442010087,0x3978f6f5ef2e6deb675f5ed9c78dc1a4a198959389635953453933251a160c46010484484420107,0x32c6ca658dc696260408102046] i else tableWord #[0xcb1b2996375b189811244085,0x34c6aa658dc696260408102046,0x3cbc7af73574ef6eeda79b59d756d3cbc7d1c0b1a9928a8461514c4b452b251d1b0e42010084442824107,0x32c6ca658dc6554ca18c811204085,0xcb1b2996371955338b811204085,0x31b2b95c69958e34a810289105,0x30bab95c696448810284045,0x3cbc7b7af774f38f8f4ecdcbc7cde0d1c9c4c24c32312d2b1d130636010080442410087] i))) else (if i<72 then (if i<56 then tableWord #[0x35aa98dc586850204085,0xd73adc64d187850244085,0x34aa996371958d2ca810244085,0x32c6caa68dc655260408102046,0x34caca6695c4ca260408102046,0x3b7af76eae6ce6e39d9d5cd9d5d3cecdd0c9a8a1998a846563554d323129130b0642010480442410087,0x3978f6f1ee6deb5f1ed595538f478ec2a4a1938985615852514a443933251a16150c4e010084484420107,0x32b2996371958d2ca810244085] i else (if i<64 then tableWord #[0x34bad71a5910c8910302045,0x35caca668dc65328a921408085,0x3cef37cbf1fb7ebf7bd3efcbeeefa767d9ddfd7ddcf1f92e1783d2f33caf07b2eb3aaea7a32789ce6b9664d91e398d62d71db569d8d5e5733cce7364ad1e8761d44e0b81c9301a0e4890e308a62384605615434c523424c3294a3244891c87118c4a124461142a098180500c7e0040481108410882104008010a,0x3cbb3af976b674f36f6ceba6dddb4ecbd0c8c1a9a2918a84646351494535332d2b26194a010088844424107,0xcb1b2996371954a18b850204085,0xd31aa996371958d2cb810244085,0xd6aa63712387850204085,0x32b2aa6571b58e34a810289105] i else tableWord #[0xcb1b2b71954d189810244085,0x34caca658dc69644e34c810302045,0x33b2995b595348811244085,0xd31aa9963716220408102046,0x3978f6f57371ee6ceae75f1ddb5ad74f4ec392c3a19985646354534945332925150c0a0646050084442010087,0x3cfed7b3ebf97def77beeefb76b77f1f97d9f57cded79ddd75dbd3f4f71798e1783d2f47cc723c4ecdb2eb3aaea79ce6b96615725c76d1b169595635785d1725c56558d5955553535293e0f23c4ed39cd934cb5168561381cbb01a0e4990e23846056154550d3048511424c930cb0294911c062184521444a1182806014031e805012044210420040080109,0x39b978f6f5ef2ee9e75f1e9d9b978f8fc2c1a39892898564625a563a26130c3e010088482010047,0x3cbc7b3a7978f776eceb619cdb53cfcfe0d1c9a18482614c4543332d1d1b063e010084442410087] i)) else (if i<88 then (if i<80 then tableWord #[0x3d3cfaba79b736f56f2da39391cf8ecdc7d1e0d1c8c2a28a844a44433432312a261c1b150e4e0100804428106,0x3d3cfaba79b73675b55d974f8f4ecdcbd0e0d1c8c4c2625434332a29261c19153e010080442010087,0x33b2995c6d5188851204085,0x34ceca65699588850204085,0x3d3cfab9b6756f174f8ecdcbe0d1c2a28884484434332a261c19153e010080442010087,0xd33b2995a656349850204085,0x3cfaf7356f2eedad6b5b59d756d3cf4785d1c1b1a9928463514c4b45251c1915130642010484442010087,0x36c6caa58dc68e2ca810284045] i else tableWord #[0xceca6575b187851204085,0xd2ca6695a653220408102046,0x34ceaa66719548811204085,0x34caca6695a653260408102046,0xd2caa99a57195520cb910202045,0x3dcf2fc7edbb5ecfafe5f7ade776dd773d9f5bd5f3bcdf1ebeaf9bceebb6ecfaeeb7a7a7b9de5e7f1f97d5f37b5e7775bd6dd7d5ecfb3dc6f0faee1f43ccb31c9f14c4f0bb0eb2ac6aba4e8c9ce5892e4786a16839c56d1b16b5a7655785c56558d594d5334acf83cce9364b91d06b19c551343a0d82e0731c0e8390e2284a0a81985505304952344509304b02a4a32447018c51124450c82a098180500c7a004048110422040080108,0xd2eb63716447810302045,0x3d3cbaba78f736f5736faf6adb9b5ad9d753cecbd4d0c8c1b09492918c8a604c4a45432e2d2b1c1a4e010080403028047] i) else (if i<96 then tableWord #[0x3cfb3a7976b675b36f1d9b4f8f4ecdcbc7d1e1d0c8c292844434332c29251a160d3e010084402010087,0x34cea99c69959534a812448105,0x39b978f6b674f2f1ef6eeddf59d6c38fc2c1a5a3999365594339350c0a063a010484442010087,0xd32b2a963756389810302045,0xd32b2696371a59324b910202045,0x32c6c96371a589260408102046,0xe34a6695c6994cd2cb810244085,0x35b2aa668dc48e2ca921408085] i else tableWord #[0x3cdf2fc7edfafdeb79ddf4fceefcbeeefaf67d7f57b0f92e1783d1f32cc727c4f0bb2eb3ab2aba9e789ce678e6358b5c9715b56b5795d54d4ccf93b43c0d82e06a1c0b01a0e438c22588e1182581515314950940cc92c4a929471194340b02606012029b801012044109021040080089,0x3cdf2fc7edfafdeb79ddf4fceefbbbe3d7f5cf5ec3e4785e0f47ccb31c9f13c2ecbaceaba9e7399e398d62d725c56d5ad61d795d54d4ccf93b43c0d82e06a0c0b01a0e438c22588e1182581515314950940cc92c4a929471194340b02606012029b801012044109021040080089] i)))))
def ordered (v : Nat) : OrderPage := orderPage plus minus 11 orderBank (v % 16) ((v >>> 4)%8) ((v >>> 7)%17592186044416) (orderClauses ((v >>> 51)%256)) (orderGroups (v >>> 59))
def ruleBank : Nat → Nat := (fun i => (((fun i => (if i<8 then tableWord #[0x20b1a11818400859080620009210020800769c42404121a2281845296a8002101b0c20808482c684604153ada720084004408406232a1a410084002604204232a1a410194002604206253ada72019406c6882021,0x1b1620808400531022400009a22090208b690e06145a18a2809490c49c602532a1a41021c00a6a822608519aa3021d4eb69c80a920b0c1181840056902240002daa20900002688026001b1a208095c2c6850081,0x32a124101954eb69c80870005a11101810c41c20210029642018a08b690e0a535a16a1021c00469022802431a71818406c694202145a1aa2829400b68022804121a22809608b690e06520b1a1182140046902240,0x70b101402068486896065a121a25820490c49c60214121a22810400869c424000216710900007408406271b12240194d685a840210009a200920002308026020b1211821452932800210431a70808482c5846061,0x20b1611821406c588202501b0c2080940076042062001183081880046902260822da43821400559022400010c40898000530022800010c408a01048688a0a5a121a258214d686a8406592a1a95821c0056802280,0x2d2a18818008680428000102210109c6c48900873585aa10086082690e0610019a710a00004408404232a0c410086cc669d4087000da2009021466a8c0650009210218a84868960a5b025a1482a4ca76904065,0x21a01098000a40840820015891810800b48062600025091118800869c420492a1a95819400769c426000190510209c6c4890085822da43821c00769c424800110212189c6c48900a14121a2281a490049c6021,0x2daa08901048688a0872081a118104005410224000150008980007604208245a18a2819400a4084062a121a258184005324ca62002cc732a0800659ce0a2000da238902848689608771b1224009608b690e021] i else tableWord #[0x1810820800561820420029021121806c314202120b0c118104820304604120a8c118184d616a840650014640890082c184606101b0620808400b328224035a16a1019400260c204200290429219048688a065,0x41212228095c2c685006100098808189048488a0a50019860818986c695006171b1a240204004410224000158108188001684e806622da53821c82a68460410010c4089000083002260001126021080074840862,0x2091611818482c184608501b062080940044ac00a24121a22829c00268802ea0009210290a84858960cfb319a75031ec0968520cb7519ab3021c8246846041001d2b00289c2c68500a50019652018988b694e061,0x1d2b00189c2c685006500292a18900007608606271b1224018400b60420c2a121a25831400661820c28229a4383254ea69c80a9000da008980006618208261b1a540206081690e0872091a1181840026042482,0x850daa3021c0045902280412082282954eb61c80a932a044101940036880206b025a14821c002408026035a04a1021c06c408202514a50a0008400a428224070b1014018400a5a8226000216008a0082c5846041,0xa2a1a458396c076a120ed8229a4382961466a8c0a9001da710a8284868960c19319a95031e08b690e08b4105a22810400631c428085190a302a5048608a0610019a71098000731c42404120c228185c2a6850081,0x2431a71819400461462400011241810800460862600015201818a04961c60210009280218a8a869160a5b025a8482a400011ce4266191a540186082690e0657191a240206082690e08500092803188004690028c,0x110b1018a1446a8c0a945a1aa2818400669c02a00009210018acc469d408bb01da14820482c68460650431a7080968a06116065b2310a2810c00731c404200110210980886408a027519904100840006086426] i))) (i/16) >>> (42*(i%16))) % 4398046511104)
def programs : Nat → Nat := (variableSlot (fun i => tablePair #[(0x2f42b92892562231e81b518b15a1280fe0d40ab082051028000,0xeceae8e6e4e2e0f8dedc7a440adb5b1ada9a4f1b433b3328d02b6463622a6101607bebcbab876b6dd03058d02ac83484a44429ad24044108006ac74f88c1d7938371a365f010a8184ad0083c0c017008202e1000d30e1c1b075c060b01055),(0x30b2e02b827c24820d1da1a716c1431170eb0ba08f05d02a000,0x4802302f1f5e1d1c23075939291908f220978e1e8d43038c68a044a2c2a8412f1d1810ba2c25a3a302174504b450244161503097f0144c404ac3814301c2ac2010ac184ad20a050e0001bf8107a1002da8008fcfa00df1ede8fde4b1ba78771a055),(0x3413072d52aa26e2221f01b418b15f1350f90cd09b068034000,0x1aa9a928d7a80fbe81b5c335a64d2008c00c7d6b04aad3c653829eaaa6a29e9842969002740d33294d326a312a22129110a7a010797802d08ed04f83ac0993c4400b3a51382c4e5e62f364134444cb025cca4808034a40042e0800698973f49012c69604109594006),(0x34330f2de2b227e2522261ec1aa1661351020d1097065031000,0x640699e3e362b609011582001b11330d50b170b04105f007dafd56f844296f6f2ed50f1680225160f03007a2eae510589c0c022e0a2dc96d89c0c9a296b6966064cd281042c82001a41a42322214daa9a928d8a8003e81a66329a64d602442322214d20d4f194e0a6),(0x3513252f12b528925722f1e31ba17f13b0ff0cb09f06e032000,0x1e0abde2214bdddbd9d603d4dd26bd1ce4e0662fcc41cbc84cb025f1f10080370ead1183af0f06fef128b078198ccc39686c1d6c836eee058082bedac6d6cec0beb82c6b03156aea00abbe9ac1eab1d82b69036880abae013433c2001b380b3730c32c7de4ca04c908006),(0xcd09105502c000,0x1feb255fdfa020aff9f7f5f3f1ee14f32bf6f5075f4f3f201f15)] i))
def panel := readPanel plus minus 8 7 ruleBank programs
def data15 : Nat → Nat := (fun i => tableWord #[0x3ff,0xf31ab504] i)
def data14 : Nat → Nat := (fun i => (if i<16 then (if i<8 then tableWord #[0x7ff420,0xe9b9724a92b079a9a8e0b,0x7ff460,0x296e5d2aa5da9a8e09,0x7ff480,0x3a2e957aad4d560e09,0x7ff500,0xe9ba42e95530d4d530e0b] i else tableWord #[0x7ff461,0x14b754d4a255cf35750a,0x7ff483,0x5cccbb17695afc52b75750c,0x7ff503,0x14b7485d5355c975750a,0x7ff440,0x0] i) else (if i<24 then tableWord #[0x7ff4c0,0x0,0x7ff4e0,0x0,0x7ff520,0x0,0x7ff4c1,0x0] i else (if i<32 then tableWord #[0x7ff501,0x0,0x7ff083,0x0,0x7ff103,0x0,0x7ff123,0x0] i else tableWord #[0x7ff523,0x0] i))))
def data13 : Nat → Nat := bookData 2 3 3 (fun i => (((fun i => tableWord #[0x120e30d03a0120230420] i)) (i/16) >>> (11*(i%16))) % 2048) (fun i => (((fun i => tableWord #[0xfbfefffefff7fffbffffdffe] i)) (i/16) >>> (12*(i%16))) % 4096) (fun i => (((fun i => (if i<8 then tableWord #[0x89485212290014000a48e5246e9137205a8c4cd0762413118988d484812220912000,0xa548d0a46752332919148d2386a12348019c00cc00640034a90a1484ea4265212290,0xa426ce136609b204da549d28cea32750938801d2a4a85253a929949524aa80053002,0x106c5226281313098a14b4ca58657d40e6987352a56852b3a95994ac8a5691cb40e5,0x902cc6166943149d8a4cc5066273314918a08c4e462623148d8a06c4e36261b120d8,0xa08c9046672333119214c88a6691b340d9906cd226681333099904cd016670b33059,0x986d4836a9135409a984d4626a80b5385a982d4616a943349d9a0ecd266683334919,0x984dce16e60b7205b8c2dd286a83b5499aa0cd5246a8235391aa46d5036881b538da] i else tableWord #[0x9c0ecc076a03b101da50dd266e8337411b9c8dcc46e91b740db9c6dcc36e41b620db,0x948ed2a76853b3a9d994ecaa76453a229da46ed037641bb409d984eca276a13b481d,0xa02f4c17a50bd505ea40f4e07a603d501e880f52876933b419d9caed2476823b311d,0x9c2e4c1729039501c9c0e4c07220394a1e250f4e57a853c429e994f4aa7a91bd40de,0x12472a238511ca46e5427290b9505c] i))) (i/16) >>> (17*(i%16))) % 131072) (variableSlot (fun i => (if i<8 then tablePair #[(0x3bb3bb3bb3bb3bb3252d72a32592031ac15d10e0c7083030000,0x43535ce748a8ab54ea3216365820db4bd5ea25193755755048f898584f930e580d86836f4cb6cd5d408581c13c8b5bcbb5b191dac713856792b77b0813b0b5071b0af5752e40256a58163615ac41b6b4482ad4306c2748b82968d3775070478a12897536da828461425f122126ab51c0d0aa5356dea0e05),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0x0,0x0)] i else tablePair #[(0x0,0x0),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0x0,0x0)] i)))
def data12 : Nat → Nat := bookData 3 4 5 (fun i => (((fun i => tableWord #[0x90284149140e9228052250090290118918283a104824208c48411a908220a10480420] i)) (i/16) >>> (23*(i%16))) % 8388608) (fun i => (((fun i => tableWord #[0xff6cff67fddffff7ffdfff7f7fbfffbffffbfffdfffffb7fbffc,0x9ffff9f9ff7fd] i)) (i/16) >>> (13*(i%16))) % 8192) (fun i => (((fun i => (if i<8 then tableWord #[0xa4846a084690246a4c45a48459884590645a4c4498644a4843988438c432904208d4119020088200,0x9804a9004a8c04a8804a8404aa0e49a06499c6498c4499864890648a0e47a06479c6478c447a5046,0x9c6209862090620a0420984208c420ad44a2d44aac64a9064aa824a9824a8c24aac04aa804a9c04a,0x9065b9845b9045b8c45ba0c51a4651a0651986519065110651a0e20a0c209cc20a08209c820a0620,0xa0632906329843290432a4e5ba0e5ba4c5ba0c5b9cc5ba085b9c85ba465ba065b9c65b9865b2c65b,0xa54349943491434a4254a4024a54339943391433a4253a4023a0e32a0c329cc32a08329c83298832,0xa449690496a402690026a5675a4e85acc75ac8759c885ac675a0665a54359943591435a4255a4025,0xa16779d677a08b7ac677906b7a02578c257a5676a167691676a5436a143691436a46a6a06a6906a6] i else tableWord #[0x2d4e12d4d0ad43aac67a906aaa823a8c2aaac07a900baad079a50c9ace79acc79a4cc9ac679906b9,0x9072aa5119a5118a570ba48fba08fba141b9941b2d41b8d41ba400ba000ba1411a4001a00012d4eb,0xad53a2d53a] i))) (i/16) >>> (20*(i%16))) % 1048576) (variableSlot (fun i => (if i<8 then tablePair #[(0x1361361361361361361361361361361361360f20b507a03d000,0x380b3ac112d038041e8c6535748443a0d105050671a0181a966bea0487c160d4b3575078b00d06),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0x0,0x0)] i else tablePair #[(0x0,0x0),(0x0,0x0),(0x0,0x0)] i)))
def data11 : Nat → Nat := (fun i => (if i<8 then tableWord #[0x2ffc48c441480420,0x2028ca55cc0205,0x3ffc4c3441480420,0x0,0x3ffc503441480420,0x0,0x3ffc462481480420,0x0] i else (if i<16 then tableWord #[0x3ffc4e3481480420,0x0,0x3ffc503481480420,0x0,0x3ffc507481480420,0x0,0x3bfd4c446a441420,0x0] i else tableWord #[0x3ff8462441480420,0x0,0x3ff8502441480420,0x0,0x3fec483481480420,0x0,0x3fec504481480420,0x0] i)))
def levels : Nat → Packing
  | 11 => (12,4,6,0,0,0,0,data11)
  | 12 => (162,3,6,0,0,0,0,data12)
  | 13 => (199,2,6,0,0,0,0,data13)
  | 14 => (17,1,6,0,0,0,0,data14)
  | 15 => (1,0,6,0,0,0,0,data15)
  | _ => (0,0,0,0,0,0,0,fun _ => 0)
def index : Nat → Nat → Option (Nat × Nat)
  | 12 => fun h => smallSlot h 5 17 4 1 (fun i => (((fun i => tableWord #[0xb1402] i)) (i/16) >>> (4*(i%16))) % 16) (fun i => (((fun i => tableWord #[0xa700840000f126892805a142ac00aac3,0xeb] i)) (i/16) >>> (8*(i%16))) % 256)
  | 13 => fun h => smallSlot h 77 275 8 2 (fun i => (((fun i => tableWord #[0x1018e84000c099080c2930a0420f,0x62029e0440148063df831828000,0xa0c0070234003000c4811c0c509,0x6018524080000c002850234002,0x121c30c440c881023c017] i)) (i/16) >>> (7*(i%16))) % 128) (fun i => (((fun i => (if i<8 then tableWord #[0x1c4b10a43fc8fc011166078000e33605ce69816a34f0b50fc000,0x2d48a00c5850ec5b02787f85622e048a8348400000160000c88,0x1138000000094026013c0c6000dc4409880c000192000000009e,0x832711440460000000001c29000513aa0708741f4881318000,0x83b5c8c09b13a022b25808fb28a09002e026000691b106abc000,0xa2560e893fe8b03abe2bd1087742ef19000000029361490420a0,0x30f749386a921000000292a439036c2398e000042f0000001853,0x6c681ae102d0122f81ca002f8cec9405500e01da12809112f014] i else (if i<16 then tableWord #[0x4388001068000c4681a0001080000000331c038b0d416c448000,0x21010c351282b20651b8839d1af0ebc70000e8c0000003114000,0x7078a0850500034f014393b68fb264926c65407d26c000117,0xbc5d274054000a3c50dc86d089b9110880000000000003076e26,0xe94502992502fe48521963fc11a429623640073428d07c86318a,0xa3ff22c8f706a83e820985c028111f26005806fc48d1258aac74,0x80c80208cf48324d4871d15027a3031f3541c43290715c00751c,0x219488b312b1e346e08c07ad94c2a0123e4cc040c991ea831861] i else tableWord #[0x49cac690f306ce4210ce23dc4b4460000001805000603801a78d,0x406f888000] i)))) (i/16) >>> (13*(i%16))) % 8192)
  | 14 => fun h => smallSlot h 100 360 8 2 (fun i => (((fun i => tableWord #[0x800117100405f0c08003160c501,0x260000600001000048280246008b,0x62080070674e02121859c020810c,0xe2c700003801610003075420006,0x43160614780243c1011c88000,0xa0028200180013c008030400006,0x8100] i)) (i/16) >>> (7*(i%16))) % 128) (fun i => (((fun i => (if i<8 then tableWord #[0xc1c46afaaecbb2505298000000e6080014e6d8200050c4000000,0x42a3d1f94b04f0617174922631da6d47092d04804211f911a761,0x628baea89946a260198b01bcad08d3d390be88ceac68d9893941,0x4548002c9d49064052c8273c4b61d82bf840506220816b0205a3,0x37c2cc04d0157af26c284f0bd20a287c00142283312e58ec072,0x62151556ee9aa1428003afa00000000030f0877c2bdc2e81d079,0x31531f50e10aa5b331018ff465a198002206000609f058001111,0x60bb911c3f00e0001cf7c56a1646b0000000c43606f927834] i else (if i<16 then tableWord #[0x125c2dcd8a49244d68e4001177516000369800080172852a0c17,0x40360d88bd48500026d400186e04c2b0f136000a282659939452,0x95f000214f96ef6200c135c0c6491f11b018837a61cdd4001b8c,0xe2cc2c69291b62847075ef74bac32612820a0454218e8f93ec67,0xe1ad5bc01f7634346b1983e00000469e2e0ea9764f413a27068c,0xa1e90918f701e24480a792a0bc411c96617d2bb23880038e9c8f,0xa26802c0000000000003583c0100000bd98b804016800306402b,0x49e20e7c561b200180018c145384e80011600000007291116000] i else tableWord #[0x55ec2290c20006474d93105c3e6141e2c96c323ed880020d890b,0x410d2b088e08302c40a800106300076ccf4e000e5ab16f0db8a8,0x8800157810972255870c528a0002b0a293b79663d2b984b45c,0xcd4ba9f889f25e4be2ff00e07501d1d276570693938206ccd009,0x2800297000000c0000001127000304800100a00070f2032cc4,0x23e000000193f0000000000000c39fac400147a84cdcb095641a,0x451f1ae10e2c085a0002c78ca2] i)))) (i/16) >>> (13*(i%16))) % 8192)
  | 15 => fun h => smallSlot h 17 59 5 2 (fun i => (((fun i => tableWord #[0x51986210109b00b12900,0x0] i)) (i/16) >>> (5*(i%16))) % 32) (fun i => (((fun i => tableWord #[0x490a56388968e4602000e2800e89b104403da5c2,0x72782c1eed59721240e4b2ee35aeadb1148ac345,0xf8929ea8810312b7840023d2fa3786c1504a2c00,0x4389fc10034e0000000000f3400] i)) (i/16) >>> (10*(i%16))) % 1024)
  | _ => fun _ => none
def book : Forest := ⟨5119,15,samples,cols,[[],[32,67,117,152],[80,97,114,131,148],[112,97,82,147,132]],levels,index⟩
theorem geometry : graphValid book (boundsBefore entries) = true := by decide +kernel
set_option maxRecDepth 16000 in
theorem row15_0 : CutRow book 15 0 1 := bandCut 10 false (by decide +kernel)
theorem band15 : CutRow book 15 0 1 := row15_0
set_option maxRecDepth 16000 in
theorem row14_0 : CutRow book 14 0 7 := bandCut 11 false (by decide +kernel)
set_option maxRecDepth 16000 in
theorem row14_7 : CutRow book 14 7 10 := orderCut (pages:=fun j => ordered (((fun i => (if i<8 then tableWord #[0x109384c3b2a19085a,0x10b084c3b2a19085a,0x1d3104c3b2a19085a,0x22bd04c3b2a19085a,0x10cd84c3b2a19085a,0x2ace04c3b2a19085a,0x10ce84c3b2a19085a,0x10ce84c3b2a19085a] i else tableWord #[0x305d84c3b2a19085a,0x30de04c3b2a19085a] i))) j)) (by decide +kernel) (by decide +kernel)
theorem combine14_0_17 : CutRow book 14 0 17 := @joinRow book 14 0 7 10 row14_0 row14_7
theorem band14 : CutRow book 14 0 17 := combine14_0_17
set_option maxRecDepth 16000 in
theorem row13_0 : CutRow book 13 0 4 := bandCut 11 false (by decide +kernel)
set_option maxRecDepth 16000 in
theorem row13_4 : CutRow book 13 4 8 := bandCut 12 false (by decide +kernel)
set_option maxRecDepth 16000 in
theorem row13_12 : CutRow book 13 12 48 := orderCut (pages:=fun j => ordered (((fun i => (if i<24 then (if i<8 then tableWord #[0x808004c3b2190c8,0x1010004bb2a190c8,0x8080004bb2a190c8,0x8888004c3aa190c8,0x9090004c3b2190c8,0x2828004c3aa19048,0x9898004c32a19048,0xa0a0004c3aa19048] i else (if i<16 then tableWord #[0x28a8004c3aa19048,0x111400043b2990848,0x11948004c3b218848,0x12150004c3aa18848,0x12958004bb2a18848,0x13188004c32a18848,0x151b8004bb2a190c8,0x89c8004c3aa190c8] i else tableWord #[0x89d0004c3aa190c8,0x9898004c32a19048,0xa1d8004c3aa190c8,0x2828004c3aa19048,0x17a28004c3b290848,0xa2300043b2990848,0x1aab800543b2990c8,0x8ac8004c3aa190c8] i)) else (if i<32 then tableWord #[0x92d0004c3b2190c8,0x92d8004c3b2190c8,0x1b2e0004c3aa190c8,0x1db18004c3aa19048,0x2b48004c3aa19048,0x8ba8004c3aa190c8,0x223b800543b219048,0x2bc8004c3aa19048] i else (if i<40 then tableWord #[0x233f000432a190848,0x23bf8004c3b218848,0x24400004c3aa18848,0x24c08004bb2a18848,0x26438004c32a19048,0x27448004bb2a19048,0x2c60004c3aa19048,0x2c78004c3aa19048] i else tableWord #[0x9898004c32a19048,0xa488004c3b219048,0x2c98004c3aa19048,0x2bd30004c3b210848,0x2c538004c3b219048,0x2d5580043b2a10848,0x2828004c3aa19048,0x2d68004c3aa19048] i))))) j)) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 16000 in
theorem row13_60 : CutRow book 13 60 64 := orderCut (pages:=fun j => ordered (((fun i => (if i<32 then (if i<16 then (if i<8 then tableWord #[0xa8b0000043aa1936,0xb0b8000043b21936,0xb8c0000043b21936,0x7878000043b21936,0xc0c8000043aa1936,0xc0d0000043aa1936,0xc8d8000043b21936,0xd0e000004c3a1936] i else tableWord #[0xc0e8000043aa1936,0xd8f0000043aa1936,0xa8f80000432a1936,0xe100000043b21936,0xe908000043b21936,0xf11000004c2a1936,0x4918000043aa1936,0xc120000043aa1936] i) else (if i<24 then tableWord #[0xf9280000432a1936,0x1013000003b2a1936,0xc160000043aa1936,0x1016800003b2a1936,0xc170000043aa1936,0xf9780000432a1936,0xc180000043aa1936,0x1399000004baa18b6] i else tableWord #[0xa998000043aa18b6,0xa9a0000043aa18b6,0xa998000043aa18b6,0x141a8000043aa10b6,0x149b000004c3a10b6,0x141c0000043aa10b6,0x141c0000043aa10b6,0x141c0000043aa10b6] i)) else (if i<48 then (if i<40 then tableWord #[0x141e0000043aa10b6,0xa9e80000432a18b6,0x159f0000043aa10b6,0x161f8000043aa10b6,0x10200000043b190b6,0x15a08000043aa10b6,0x141c0000043aa10b6,0x16a100000432a18b6] i else tableWord #[0x1721800004c3210b6,0x1022000003b2a1936,0x7a38000043b21936,0x1824000004c3a1936,0x18a4800004c321936,0x1825000004c3a1936,0x7a5800004c3218b6,0x1926000004c3a18b6] i) else (if i<56 then tableWord #[0x1926800004c3a18b6,0x18a7000004c3218b6,0x7a7800004c3990b6,0x7a8000004c3990b6,0xda8800004c3190b6,0x7a9000004c3990b6,0x19a9800004bb21936,0x1a2a000004c3990b6] i else tableWord #[0xc2a800004c3190b6,0x7ab000004c3990b6,0xb2c000004c3990b6,0x1bae800004c3990b6,0x1c2f000004c3a10b6,0x7af800004c3218b6,0x1cb0000004bb21936,0xc320000043aa1936] i))))) j)) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 16000 in
theorem row13_124 : CutRow book 13 124 64 := orderCut (pages:=fun j => ordered (((fun i => (if i<32 then (if i<16 then (if i<8 then tableWord #[0x1e32800004bb21936,0x1833000004c3a1936,0xf33800004c2a1936,0x1eb4000004c3a18b6,0x1833000004c3a1936,0x13b5800004c2a10b6,0x1f36000004c3a1936,0xf36800004c2a1936] i else tableWord #[0x19b7000004baa1936,0x1fb78000043aa1936,0x2038000004c2a1936,0x2038800004c2a1936,0x19b9000004c2a1936,0x213a000004c3990b6,0x21bb000004c3a10b6,0x15bc000004baa1836] i) else (if i<24 then tableWord #[0x7bd8000043b21936,0xc3e0000043aa1936,0xc3e0000043aa1936,0xfbe80000432a1936,0xc3e0000043aa1936,0x25410000043aa1036,0x25c18000043aa1836,0x25c20000043aa1836] i else tableWord #[0x25c28000043aa1836,0x25430000043aa1036,0x26c40000043aa1036,0x27c5000004c2a1036,0x25458000043aa1036,0x25468000043aa1036,0xc470000043aa1936,0x25458000043aa1036] i)) else (if i<48 then (if i<40 then tableWord #[0x25480000043aa1036,0x28490000043aa1036,0x25458000043aa1036,0x28ca0000043aa1036,0x254a8000043aa1036,0x294b00000432a1036,0x29cb8000043aa1036,0x1bcc0000043b21936] i else tableWord #[0x2a4c8000043a99036,0x25458000043aa1036,0x294d000003b2a1036,0x194f000004c3a18b6,0x104f800004c390836,0x2b50000004c3a10b6,0xed0800004c3990b6,0x7d1000004c3990b6] i) else (if i<56 then tableWord #[0x1051800004c390836,0x21d2000004c3a1036,0x21d2000004c3a1036,0x27d2800004c2a1036,0x2cd4000004c2a0836,0x1054800004c390836,0x1055000004c390836,0x1055000004c390836] i else tableWord #[0x2dd6000004c290836,0x1057000004c390836,0x1057800004c390836,0x1055000004c390836,0x2e58000004baa1036,0xd58800004c3a1936,0xd0e000004c3a1936,0xd59000004c3a1936] i))))) j)) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 16000 in
theorem row13_188 : CutRow book 13 188 11 := orderCut (pages:=fun j => ordered (((fun i => (if i<8 then tableWord #[0xd0e000004c3a1936,0xd59800004c3a1936,0x2cda000004c2a1836,0x2cda000004c2a1836,0x2cda000004c2a1836,0x2eda800004baa1036,0x2cda000004c2a1836,0x2cdb000004c2a0836] i else tableWord #[0x19b7000004baa1936,0x2cdb800004c2a1836,0x2cda000004c2a1836] i))) j)) (by decide +kernel) (by decide +kernel)
theorem combine13_0_12 : CutRow book 13 0 12 := @joinRow book 13 0 4 8 row13_0 row13_4
theorem combine13_12_112 : CutRow book 13 12 112 := @joinRow book 13 12 48 64 row13_12 row13_60
theorem combine13_124_75 : CutRow book 13 124 75 := @joinRow book 13 124 64 11 row13_124 row13_188
theorem combine13_0_124 : CutRow book 13 0 124 := @joinRow book 13 0 12 112 combine13_0_12 combine13_12_112
theorem combine13_0_199 : CutRow book 13 0 199 := @joinRow book 13 0 124 75 combine13_0_124 combine13_124_75
theorem band13 : CutRow book 13 0 199 := combine13_0_199
set_option maxRecDepth 16000 in
theorem row12_0 : CutRow book 12 0 3 := bandCut 11 false (by decide +kernel)
set_option maxRecDepth 16000 in
theorem row12_3 : CutRow book 12 3 2 := bandCut 12 false (by decide +kernel)
set_option maxRecDepth 16000 in
theorem row12_5 : CutRow book 12 5 37 := mixedCut (data:=fun j => treeData plus minus (((fun i => (if i<16 then (if i<8 then tableWord #[0x36344154,0x6b42d4263,0x362c4154,0x362c4154,0x8620e154,0x36344154,0x654348263,0x36344154] i else tableWord #[0x36184154,0x8634e154,0x10a3354681,0x36344154,0x6b42d4263,0x654348263,0xa75b4e472,0x654348263] i) else (if i<24 then tableWord #[0x8620e154,0x36344154,0x6b42d4263,0x654348263,0xa75b4e472,0x654348263,0xa75b4e472,0x294ad4050] i else (if i<32 then tableWord #[0xa75b4e472,0xa75b4e472,0xa75b4e472,0x294b58050,0xa75b4e472,0x294b54050,0x294b54050,0x294b54050] i else tableWord #[0x294b54050,0x294b54050,0x294b54050,0x294b54050,0x294b54050] i))))) j)) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 16000 in
theorem row12_42 : CutRow book 12 42 64 := colorCut (ds:=fun j => panel (((fun i => (if i<32 then (if i<16 then (if i<8 then tableWord #[0x39a905,0x39b290a,0x30a900,0x393081,0x3930a98b,0x389a90c,0x41298d,0x438a90e] i else tableWord #[0x30a900,0x411b88f,0x413086,0x41a910,0x292183,0x3b12191,0x312a192,0x412a187] i) else (if i<24 then tableWord #[0x292193,0x4312194,0x292195,0x292196,0x292197,0x393081,0x30a92198,0x30aa199] i else tableWord #[0x292184,0x30aa19a,0x30a9219b,0x429219c,0x30a900,0x38a19d,0x413086,0x39309e] i)) else (if i<48 then (if i<40 then tableWord #[0x292184,0x292184,0x31aa1f,0x4132a20,0x4392a21,0x3932a22,0x4392a23,0x412a24] i else tableWord #[0x3931aa25,0x412a26,0x41b927,0x31aa28,0x3a91a4a9,0x3caa182,0x31a282a,0x1c840b2a2b] i) else (if i<56 then tableWord #[0x31a2808,0x3291a4ac,0x2921ad,0x31a282e,0x4831aa2f,0x31a2830,0x291a4b1,0x292183] i else tableWord #[0x31a2832,0x4831aa33,0x31a2834,0x41b2a07,0x4132a35,0x3b1aa36,0x43931aa37,0x4b931aa38] i))))) j)) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 16000 in
theorem row12_106 : CutRow book 12 106 36 := colorCut (ds:=fun j => panel (((fun i => (if i<16 then (if i<8 then tableWord #[0x31aa03,0x3931aa39,0x3829ba,0x39a4bb,0x38aa1bc,0x38aa182,0x38a1bd,0x40aa1be] i else tableWord #[0x38aa182,0x31a283f,0x4832a40,0x31a2808,0x3931aa41,0x40b2a42,0x40b2a02,0x30a943] i) else (if i<24 then tableWord #[0x4532944,0x39b101,0x40b931c5,0x312980,0x4940bb1c6,0x40b931c7,0x39b148,0x483931aa49] i else (if i<32 then tableWord #[0x41b94a,0x4392a4b,0x412a4c,0x393180,0x4831aa4d,0x3152ce,0x32284f,0x314ad0] i else tableWord #[0x393180,0x44b151,0xcb22852,0x40b931d3] i))))) j)) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 16000 in
theorem row12_142 : CutRow book 12 142 3 := orderCut (pages:=fun j => ordered (((fun i => tableWord #[0x4c3b2190c8,0x28280043b2190848,0x28280043b2190848] i)) j)) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 16000 in
theorem row12_145 : CutRow book 12 145 17 := orderCut (pages:=fun j => ordered (((fun i => (if i<8 then tableWord #[0x1818000042a190b6,0x20200000432990b6,0x303000004c321936,0x3838000042a18836,0x4040000043298836,0x484800003b2190b6,0x5050000043210836,0x585800004c3b10b6] i else (if i<16 then tableWord #[0x606000004c3290b6,0x686800004aa190b6,0x707000004aa190b6,0x787800003b2990b6,0x3b50000054ba1836,0x20b980000543a1936,0x2f5c0000054b29836,0x2fdc800004c3a1936] i else tableWord #[0x185d000004c3a1936] i)))) j)) (by decide +kernel) (by decide +kernel)
theorem combine12_0_5 : CutRow book 12 0 5 := @joinRow book 12 0 3 2 row12_0 row12_3
theorem combine12_5_101 : CutRow book 12 5 101 := @joinRow book 12 5 37 64 row12_5 row12_42
theorem combine12_106_39 : CutRow book 12 106 39 := @joinRow book 12 106 36 3 row12_106 row12_142
theorem combine12_0_106 : CutRow book 12 0 106 := @joinRow book 12 0 5 101 combine12_0_5 combine12_5_101
theorem combine12_106_56 : CutRow book 12 106 56 := @joinRow book 12 106 39 17 combine12_106_39 row12_145
theorem combine12_0_162 : CutRow book 12 0 162 := @joinRow book 12 0 106 56 combine12_0_106 combine12_106_56
theorem band12 : CutRow book 12 0 162 := combine12_0_162
set_option maxRecDepth 16000 in
theorem row11_0 : CutRow book 11 0 1 := bandCut 11 false (by decide +kernel)
set_option maxRecDepth 16000 in
theorem row11_1 : CutRow book 11 1 7 := mixedCut (data:=fun j => treeData plus minus (((fun i => tableWord #[0x48024e342,0x48624e342,0x6b42d4241,0x654348241,0xa75b4e450,0x654348241,0x36344143] i)) j)) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 16000 in
theorem row11_8 : CutRow book 11 8 4 := colorCut (ds:=fun j => panel (((fun i => tableWord #[0x289805,0x249800,0x28a001,0x249889] i)) j)) (by decide +kernel) (by decide +kernel)
theorem combine11_0_8 : CutRow book 11 0 8 := @joinRow book 11 0 1 7 row11_0 row11_1
theorem combine11_0_12 : CutRow book 11 0 12 := @joinRow book 11 0 8 4 combine11_0_8 row11_8
theorem band11 : CutRow book 11 0 12 := combine11_0_12
theorem checked : mixedTables book 15 := by
  intro k hk
  interval_cases k
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact band11
  · exact band12
  · exact band13
  · exact band14
  · exact band15
end M2015_16
theorem m2015_16 : Face false 1023 16 :=
  mixedLower (g:=M2015_16.book) (i:=0) (hints:=4882524037)
    (before_sound M2015_16.entries M2015_16.prior) M2015_16.geometry M2015_16.checked
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem m2525_11 : Face false 1277 11 := lowerHint (lower_down h2525_11) (by decide)
theorem m2645_8 : Face false 1333 8 := lowerHint (lower_down h2645_8) (by decide)
theorem m2909_11 : Face false 1469 11 := carry_of (swaps:=[168,134,150,117,48,64,32]) (by decide +kernel) m989_11
theorem m2974_11 : Face false 1502 11 := lowerHint (lower_down h2974_11) (by decide)
theorem m3023_11 : Face false 1519 11 := lowerHint (lower_down h3023_11) (by decide)
theorem m3035_11 : Face false 1531 11 := lowerHint (lower_down h3035_11) (by decide)
theorem m3036_10 : Face false 1532 10 := carry_of (swaps:=[163,16,64,50,132,83,146,113,96]) (by decide +kernel) m1631_10
theorem m3037_13 : Face false 1533 13 := lowerHint (lower_down h3037_13) (by decide)
theorem m2775_11 : Face false 1399 11 := carry_of (swaps:=[163,147,33,132,48,98,81,112]) (by decide +kernel) m990_11
theorem m3031_12 : Face false 1527 12 := dropFace 128 4899276677 m2775_11 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem m3038_12 : Face false 1534 12 := carry_of (swaps:=[167,101,48]) (by decide +kernel) m3031_12
theorem m2566_4 : Face false 1286 4 := carry_of (swaps:=[166,101,149,134,117,50,66,16]) (by decide +kernel) m209_4
theorem m2631_7 : Face false 1319 7 := lowerHint (lower_down h2631_7) (by decide)
theorem m2643_7 : Face false 1331 7 := lowerHint (lower_down h2643_7) (by decide)
theorem m2647_9 : Face false 1335 9 := carry_of (swaps:=[166,150,101,117,66,48]) (by decide +kernel) m926_9
theorem m2779_10 : Face false 1403 10 := carry_of (swaps:=[167,151,101,48]) (by decide +kernel) m987_10
theorem m2781_11 : Face false 1405 11 := carry_of (swaps:=[167,151,101,133,48,32]) (by decide +kernel) m989_11
theorem m2830_7 : Face false 1422 7 := carry_of (swaps:=[166,150,117,48,64,32]) (by decide +kernel) m723_7
theorem m2839_8 : Face false 1431 8 := carry_of (swaps:=[165,101,150,117,65,33]) (by decide +kernel) m727_8
theorem m2823_7 : Face false 1415 7 := carry_of (swaps:=[165,101,150,117,50,66]) (by decide +kernel) m723_7
theorem m2903_11 : Face false 1463 11 := lowerHint (lower_down h2903_11) (by decide)
theorem m2973_11 : Face false 1501 11 := carry_of (swaps:=[165,118,149,66]) (by decide +kernel) m989_11

namespace M3039_15
def entries : List (Nat × Nat) := [(120,4),(306,4),(371,7),(378,7),(462,7),(470,7),(474,7),(476,8),(507,10),(509,11),(510,11),(1277,11),(1286,4),(1319,7),(1331,7),(1333,8),(1335,9),(1399,11),(1403,10),(1405,11),(1422,7),(1431,8),(1415,7),(1463,11),(1469,11),(1501,11),(1502,11),(1519,11),(1527,12),(1533,13),(1534,12)]
theorem prior : Known false entries := (consFace m216_4 (consFace m594_4 (consFace m723_7 (consFace m730_7 (consFace m910_7 (consFace m918_7 (consFace m922_7 (consFace m924_8 (consFace m987_10 (consFace m989_11 (consFace m990_11 (consFace m2525_11 (consFace m2566_4 (consFace m2631_7 (consFace m2643_7 (consFace m2645_8 (consFace m2647_9 (consFace m2775_11 (consFace m2779_10 (consFace m2781_11 (consFace m2830_7 (consFace m2839_8 (consFace m2823_7 (consFace m2903_11 (consFace m2909_11 (consFace m2973_11 (consFace m2974_11 (consFace m3023_11 (consFace m3031_12 (consFace m3037_13 (consFace m3038_12 (known_down baseKnown))))))))))))))))))))))))))))))))
def samples : Nat → Bits × Bits := (fun i => (if i<8 then tableBits #[(padColumn 154 0xfffc0000000000000000000000000003fff,padColumn 154 0xf503d40f503d40f503d40f503d40f503d40f5),(padColumn 154 0x3fff000000000000000000000,padColumn 154 0xf3f3cfcf3f3cfcf3f3cfcf3f3cfcf3f3cfcf3f),(padColumn 154 0x3fff0000000fffc0000003fff00000000000000,padColumn 154 0xf003c00f003c00f003c00f003c00f003c00f),(padColumn 154 0xfffc0000003fff0000000,padColumn 154 0x13434d0d3434d0d3434d0d3434d0d3434d0d343),(padColumn 154 0x3fff00000000000000fffc000fffc000,padColumn 154 0x51114445111444511144451114445111444511),(padColumn 154 0xfffffff,padColumn 154 0x3a0ae82ba0ae82ba0ae82ba0ae82ba0ae82ba0a),(padColumn 154 0xfffffff0000000,padColumn 154 0x28aca2b28aca2b28aca2b28aca2b28aca2b28ac),(padColumn 154 0xfffffff00000000000000,padColumn 154 0x2cb0b2c2cb0b2c2cb0b2c2cb0b2c2cb0b2c2cb0)] i else tableBits #[(padColumn 154 0x3ffffffffff000000000000000000000,padColumn 154 0x30c0c3030c0c3030c0c3030c0c3030c0c3030c0),(padColumn 154 0x0,padColumn 154 0x0),(padColumn 154 0x3ffffffc0000000000000000000000000000000,padColumn 154 0x3f00fc03f00fc03f00fc03f00fc03f00fc03f00)] i))
def cols : List ColumnInfo := [(1409,6,120,0,4),(77,1152,306,0,4),(1036,128,371,0,7),(1157,0,378,0,7),(133,1024,378,0,7),(1041,32,462,0,7),(1064,1,470,0,7),(1060,1,474,0,7),(37,1024,474,0,7),(1058,1,476,0,8),(1028,0,507,0,10),(1026,0,509,0,11),(1025,0,510,0,11),(256,2,1277,0,11),(208,40,1286,1,5),(152,64,1319,0,7),(204,0,1331,0,7),(194,8,1333,0,8),(200,0,1335,0,9),(192,8,1335,0,9),(136,0,1399,0,11),(132,0,1403,0,10),(130,0,1405,0,11),(81,32,1422,0,7),(104,0,1431,0,8),(40,64,1415,16,8),(68,8,1331,128,8),(72,0,1463,0,11),(66,0,1469,0,11),(34,0,1501,0,11),(33,0,1502,0,11),(16,0,1519,0,11),(2,8,1333,192,10),(8,0,1527,0,12),(0,8,1335,192,11),(2,1,476,1056,10),(2,0,1533,0,13),(1,0,1534,0,12)]
def plus : Nat := 0x101200910208408440840a012018021
def minus : Nat := 0x2f05289c524a1541a382424618930cc11c1701f
def orderBank : Nat → Nat := (fun i => (((fun i => (if i<8 then tableWord #[0x11421921a80768520e10005a1539880026894e420009a23b10a80768520a170a9a14021400a68108a40015a4420900036892e600009a24b900001684ec624131a22820c001684a84220a9a118194cac6904063,0x21842932800750866c80015a0432980036814e820009a24a881c2a68500a5002546412a0001684aa640011a44b881c2a68500c720a9a11821e48369140e300246638bb0009610a4ea00294219ba000a68068e6,0x29a029a88008680a682001546411a0008680aac40015a01a29800750864a60021a02a288cac6904085000da04a9800036892a4000258428a9800568108644131a22829400a680aae4820da43830d4e369880a3,0x29a00a3980016814e820015a042a1000a60842a6001d421921800a68066a40029a011a8800a50426e80015a04ba8000460844a80015a443118008610a2a80005a13a9000086812a800029421929904c688a063,0x15a019a10009610a2a80029a02a2880056812a8020a9a11821406a688206532b1a41020c00750864a8001d410929800060842680021a01228800168048620005a112108003680068001a9a20821c00750426c8,0x9a23a1080016854a400009a2528819436a4e0c3550da92028c00450866a80029a0433980036812e8032b1a41029400a50866ea002982113a800250426a80029a012b900016844a640015a04a98000951d04a8,0x4e13a900002388ea20538da62020400750c64a6001da12a28800268cea20850da8382859436a4e0a10009a23a880007684aac4920da45028c009198e2a80011a44a88104c688a065820da43820d4e36988063,0x5a02aa1104c388a0a532b0e41021680760520e10028e02ab90008380aac40004e12a9900036092e600009824b9000046112e2020a96118196083390e0a1538ce62020400858066a400156019a10003380ea60] i else tableWord #[0x920d64502855435a0806100216052a000015854a400009625288104c388a063a01d814828400a380a6a20020e029a080086012a800015804a9800036092a400009824a88280768d20e100154109aa000568028a6,0x11a442810002588882061a9a5402140065146486000da0421900086804682000da54a90000a50c64a6001143192180096a0660420a8611819400a18066a400146019a105276a800610025aa428100026880620,0x29a02b390001680ac840005a12b1900035014ea200054053a080015054e62000541231880025094e42000942231085276a000610025a8428100006844802550d6820204005519048a00118210a180056910a24,0x254641bb00061a542ce0029a03b3880086812ec00001a15380882a18460a701a8620821d04c688a0c5920d445038d54352080c300246420bb000460844ca00154109b2000a1806ae60028600a39800518028c6,0x246720ba800501906ac002982113a000a68048e40005a1121900086814ec2001da64b88082a68460a700246738bb000750866ca001d821132800a6806ae60021a012b100036814ea2000da03b2880036812ea0,0x1491a800284007204008a00058429298008610a4860005a029a90008680a6840005a03a2880086800a800015a0029800056900a400011a40288248369540a1620da5382055436a480617081a14031e4e369940e3,0x29a12ab91883694e0830025842929800919082a60019852921800a680a6a40009a2529080026892a400025a419a900026854a620005a152908001684e842920da450286083690e081538da6201840055310468,0x8628a2a80015a842a1000662ca2a800206638128002684ea60550da8202055436a4808100198b2932800750c66c8002066389b0002684ec820009a33b10904c68ca0a5001183112a0003614a46a] i))) (i/16) >>> (42*(i%16))) % 4398046511104)
def orderClauses : Nat → Nat := (fun i => (if i<16 then (if i<8 then tableWord #[0x3a81803a399a1507b93894813837b70f,0xb0abf3e8a10903e09890f888f1b080e95bdbd1abc8e06820605bc3bbb1d,0xb20918a10904109890f9c20409f8ec011163f8c1f068206059b83028b9d,0x4c5448c92968412444383c342c2418f,0x49847c70c92968412179703c6c6458f,0xd25a524c92423a322a221a148c80e,0x4a818005271887ca49a6812613930d8f,0x48080050c989e1d841d1c839913930d90] i else tableWord #[0x818005274c4b9d27a6812613cb0d8f,0x4e8005281e4e044d9ccd039913cc8d8f,0x498050c929684121797039928930d8f,0xd00818051d115509e94d0014fcf0e,0xd25a524d32423a322a221a152d20e,0xb0a91940a10900709890f888f1b080e9591161a8c0e0682060583028b9d,0x5d5cdc2bdbdb075aab2ada1c59aa5958d857a9d756a95655d554d45383028b9f,0xb0a91942e2d875fdf090f888f2d2c880e9591160c5e8205de1bac0302dd9e] i) else (if i<24 then tableWord #[0xb6420ab8a108763ab2ae3629c202a621fa9e1a961609f06820605e003028b9f,0x688a919468100709e7e708e68f1b2c880e9166160c65e50e068206058302e49f,0x4986a69e90c92968412179703af2e8f,0x3130b06fef6eee6ded6cafec6beb6a8f,0x49871f170a812f00412179703af2e8f,0x480b2b08532189df3f372f213318e,0x3132f730053276f675f574afa8f4318f,0xb0af9140a10ad8709890f888f78887877b31a8c0e0682060583028b9c] i else tableWord #[0xa91940a2e100709897b88fb2d087a9591330c0e7a068206799bac03028b9e,0xd008180347c1a15079e948119b38e,0xd00818034fc9a15079e948119b38e,0x81803436fe3607fda7b5817d19b50f,0xd00818034b6ff3607feb58119b50e] i)))
def orderGroups : Nat → Nat := (fun i => (if i<8 then tableWord #[0x32b2996371644a260408102046,0x39f6b674f2ef6de6df56cac38cc2c1a599936559433529230c0a063a010484442010087,0x39b978f6b674f2f1ef6de6df56ce8b8fc2c1a4a199938564615945433834312c22150a0652010480442010087,0x34c6aa658dc696260408102046,0x34c6a96371a589260408102046,0xd32c6ca658da6562cb850204085,0x32c6ca658dc58a260408102046,0x34ceaa6571a588812204045] i else (if i<16 then tableWord #[0x32c6ca6371634a260408102046,0xd73b5a64b187850244085,0x34ceca65699588850204085,0x3978f6f5ef2ee9e75f59c38bc2c1a39893898565595543390c0a063e010484442010087,0x39b978f6b674f2f1ef2e6deb6766df1e9d9b978f94c2c1a4a1989389856458524a4638322c1a164a010080482010047,0x39b978f6b675f2ef6de6df56ce8b878fc2c1a4a19895938964615955433834312c221c160a56010480504420087,0x3af9f6ed6ce725e35f4dc38bc3a2a193898569655935230c0a063a010484442010087,0x34aa58dc696449260408102046] i else tableWord #[0xcb1b6b753187811244085,0x35caca6371959328a814448085,0x39f6b674f2ef6de6df56cb8accc2c1a59993655943352c29230a063a010484442010087,0x39b978f6b674f2f1ef2e6d6b69e766df1e9e5b9b554596c2c1a4a19891898583646158514a494543382c221412065e010480402010087,0xd32b2996371958d2cb810244085] i)))
def ordered (v : Nat) : OrderPage := orderPage plus minus 8 orderBank (v % 16) ((v >>> 4)%8) ((v >>> 7)%17592186044416) (orderClauses ((v >>> 51)%32)) (orderGroups (v >>> 56))
def ruleBank : Nat → Nat := (fun i => (((fun i => tableWord #[0x20a9a118106083390e085538ce620194005690224020a9a118184820684604120a8611818406a1882021538da62008680768520654131a228094004690224000094108108002504206232b1a41019406a6882021,0x4e13a019c2a6850081620ce53821c00519022400011821018800168442404131a228184cac69040210009a22090000319480627191a240204006194806270a9a14018504c688a0a5820ce4381940046902260,0x94c081880046902280538ce6202a490a69860610429a60808400652c206261a9a54018406a694202100114308189c6a68900810015a008a014e3398808700118408900005504206270a9814020410a6182021,0x141209024835114061550d482008400a5042082920da450215c6468900618209a438196082690e087000da23a019882694e08700106408a0154352080a90008e220901883394e061538ce6200840075042062,0x96220901c2a6850087550d682008400819080420001a1209824836914081a01da14821e080690e041002467201880006848240938da65018400919ce0620001a1389024836914061820da4380840091908062,0x1883694e06120a9a118094001684e604001c0218189883694e0652081a11808482a18460250025464018800969102600011a449a12483691406961a9a5400840081a8808260a9a94021c0081908082] i)) (i/16) >>> (42*(i%16))) % 4398046511104)
def programs : Nat → Nat := (variableSlot (fun i => tablePair #[(0x29f2782512271fb1ce19a17515211e0f80ce0a2075049024000,0x448708341580fdf067ab1e3b74e40340195703c036e0cab61401b50449a090221e8cd90562b181322016f5c496ac02adea08a48a8589d30e1a01a0941a41e01a3448470d40df0678e8a00dc04240885c042c0805),(0x17314e1291020dd0af081055027000,0x50bde0a1d7668cdd30b72d93b5657668cd830b5eb55a81a9b522c5e8850ed6a13e7059ad325ca93203b478d143075)] i))
def panel := readPanel plus minus 7 5 ruleBank programs
def data14 : Nat → Nat := (fun i => tableWord #[0x3ff,0x34c51b7a406] i)
def data13 : Nat → Nat := (fun i => (if i<16 then (if i<8 then tableWord #[0x7fd441,0x56654156ef0d07,0x7ff440,0x4d3e36a0c376ca8909,0x7ff500,0x73e28e92a96c68909,0x7ff4c5,0x3e69f1a845183c708850b] i else tableWord #[0x7ff525,0x8aa252e12d8907,0x7ff460,0x0,0x7ff4c0,0x0,0x7ff082,0x0] i) else (if i<24 then tableWord #[0x7ff482,0x0,0x7ff4a2,0x0,0x7ff4e2,0x0,0x7ff502,0x0] i else tableWord #[0x7ff4e5,0x0,0x7ff505,0x0] i)))
def data12 : Nat → Nat := bookData 2 3 2 (fun i => (((fun i => tableWord #[0x441a0149662c40] i)) (i/16) >>> (11*(i%16))) % 2048) (fun i => (((fun i => tableWord #[0xbffffffdfffd] i)) (i/16) >>> (12*(i%16))) % 4096) (fun i => (((fun i => tableWord #[0xa0f0a0d09cd0a0909c909890a0709070a050985090509cd2a4f18c50a4a98820,0x98048c049020a0d2a05298529052a0f1a091a0519c5190519cd39c5398539053,0xa85a944aa1599d59a8999489a859a4e4a4a49ca498a49c849484944490449c04,0xa91aa0aa] i)) (i/16) >>> (16*(i%16))) % 65536) (variableSlot (fun i => tablePair #[(0x1031031031031031031031031031031031030cb099062035000,0x528c834487008369b1a221e100d8a30101c04001bd2602122e0ba0b04104d0706),(0x0,0x0),(0x0,0x0),(0x0,0x0)] i))
def data11 : Nat → Nat := (fun i => (if i<8 then tableWord #[0x1ff9462441440,0x6091958040005,0x1f9f4e65254c5,0x9b8ec782e0105,0x1ddf5275254c5,0x8ec780a0104,0x1ffd4c4441440,0x0] i else tableWord #[0x1fdf5025254c5,0x0,0x1fdd4415254c5,0x0,0x1ddf5285254c5,0x0] i))
def data10 : Nat → Nat := (fun i => tableWord #[0x3d1f5274e65254c5,0x29bc771e85c0105] i)
def levels : Nat → Packing
  | 10 => (1,4,6,0,0,0,0,data10)
  | 11 => (7,3,6,0,0,0,0,data11)
  | 12 => (50,2,6,0,0,0,0,data12)
  | 13 => (14,1,6,0,0,0,0,data13)
  | 14 => (1,0,6,0,0,0,0,data14)
  | _ => (0,0,0,0,0,0,0,fun _ => 0)
def index : Nat → Nat → Option (Nat × Nat)
  | 11 => fun v => (if v=10756249583182226414 then some (0,0) else none)
  | 12 => fun h => smallSlot h 3 14 3 2 (fun i => (((fun i => tableWord #[0x2a0] i)) (i/16) >>> (4*(i%16))) % 16) (fun i => (((fun i => tableWord #[0xc100c34a008700e5e22426000013] i)) (i/16) >>> (8*(i%16))) % 256)
  | 13 => fun h => smallSlot h 28 100 6 2 (fun i => (((fun i => tableWord #[0x200406e196035461,0xd213f110170d] i)) (i/16) >>> (4*(i%16))) % 16) (fun i => (((fun i => tableWord #[0x5144540f000000000003edad39c58e00024800155819,0x45614f01222259c1dc0e5b824cc7ccfa12234bc00410,0x1940031030a34903ed1c06f409a281b0bb510538765d,0xde09fc7594485874828006120039311bc6069c00196,0xb9c0013851fa6400306800a2fd78ef6ad63188f0d201,0x45545b1768200014a16c280010a552b0400002210800,0xb944c92b0c] i)) (i/16) >>> (11*(i%16))) % 2048)
  | 14 => fun h => smallSlot h 12 42 4 2 (fun i => (((fun i => tableWord #[0x83c250f6000040] i)) (i/16) >>> (5*(i%16))) % 32) (fun i => (((fun i => tableWord #[0x9105f8e0073eacbc080040e3aaa68f6d248d,0xe736800420a6077c00390e8000052803136e,0x30bbb0e22989cb7b9330de3] i)) (i/16) >>> (9*(i%16))) % 512)
  | _ => fun _ => none
def book : Forest := ⟨5631,14,samples,cols,[[],[66,165,118],[48,101,167],[48,66,117,166]],levels,index⟩
theorem geometry : graphValid book (boundsBefore entries) = true := by decide +kernel
set_option maxRecDepth 16000 in
theorem row14_0 : CutRow book 14 0 1 := bandCut 10 false (by decide +kernel)
theorem band14 : CutRow book 14 0 1 := row14_0
set_option maxRecDepth 16000 in
theorem row13_0 : CutRow book 13 0 1 := bandCut 10 false (by decide +kernel)
set_option maxRecDepth 16000 in
theorem row13_1 : CutRow book 13 1 4 := bandCut 11 false (by decide +kernel)
set_option maxRecDepth 16000 in
theorem row13_5 : CutRow book 13 5 9 := orderCut (pages:=fun j => ordered (((fun i => (if i<8 then tableWord #[0x108004c3b219048,0x210004c3aa19048,0x168004c3b219048,0xb70004bb2a19048,0xc78004c3b219048,0xd80004c32a19048,0xe88004c3b219048,0x12b8004c3b219048] i else tableWord #[0x13c0004c3b219048] i))) j)) (by decide +kernel) (by decide +kernel)
theorem combine13_0_5 : CutRow book 13 0 5 := @joinRow book 13 0 1 4 row13_0 row13_1
theorem combine13_0_14 : CutRow book 13 0 14 := @joinRow book 13 0 5 9 combine13_0_5 row13_5
theorem band13 : CutRow book 13 0 14 := combine13_0_14
set_option maxRecDepth 16000 in
theorem row12_0 : CutRow book 12 0 2 := bandCut 11 false (by decide +kernel)
set_option maxRecDepth 16000 in
theorem row12_2 : CutRow book 12 2 3 := bandCut 12 false (by decide +kernel)
set_option maxRecDepth 16000 in
theorem row12_5 : CutRow book 12 5 24 := colorCut (ds:=fun j => panel (((fun i => (if i<8 then tableWord #[0xc6a81,0x104ca82,0xc6a80,0x10e4a83,0xe4ca84,0x10e4a85,0x104a86,0xe4c6a87] i else (if i<16 then tableWord #[0x104a88,0x106e49,0xc6a80,0xe4c6a8a,0x104ca8b,0x104ca8c,0x1304a8d,0x120e4e] i else tableWord #[0x12104f,0x120e50,0x1210e51,0x521094,0xe8c75,0x104c96,0xe8c77,0x106e58] i)))) j)) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 16000 in
theorem row12_29 : CutRow book 12 29 21 := orderCut (pages:=fun j => ordered (((fun i => (if i<8 then tableWord #[0x3b2990b6,0x318000043b19036,0x420000043b190b6,0x52800003aa19036,0x630000043299036,0x738000043a99036,0x840000043299036,0x348000043a99036] i else (if i<16 then tableWord #[0x350000043b19036,0x738000043a99036,0x95800003b2990b6,0xa6000003aa19036,0xf9000004c3a1936,0x69800004bb19036,0xfa000004c3a1936,0x10a800004c321036] i else tableWord #[0x11b000004c399036,0x14c800003b2a1936,0x14d0000043b21936,0xd800003b2a1936,0x14e0000043b21936] i)))) j)) (by decide +kernel) (by decide +kernel)
theorem combine12_0_5 : CutRow book 12 0 5 := @joinRow book 12 0 2 3 row12_0 row12_2
theorem combine12_5_45 : CutRow book 12 5 45 := @joinRow book 12 5 24 21 row12_5 row12_29
theorem combine12_0_50 : CutRow book 12 0 50 := @joinRow book 12 0 5 45 combine12_0_5 combine12_5_45
theorem band12 : CutRow book 12 0 50 := combine12_0_50
set_option maxRecDepth 16000 in
theorem row11_0 : CutRow book 11 0 3 := bandCut 11 false (by decide +kernel)
set_option maxRecDepth 16000 in
theorem row11_3 : CutRow book 11 3 2 := mixedCut (data:=fun j => treeData plus minus (((fun i => tableWord #[0x35344143,0xaa1b58462] i)) j)) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 16000 in
theorem row11_5 : CutRow book 11 5 2 := colorCut (ds:=fun j => panel (((fun i => tableWord #[0xc64a32,0xe86c53] i)) j)) (by decide +kernel) (by decide +kernel)
theorem combine11_0_5 : CutRow book 11 0 5 := @joinRow book 11 0 3 2 row11_0 row11_3
theorem combine11_0_7 : CutRow book 11 0 7 := @joinRow book 11 0 5 2 combine11_0_5 row11_5
theorem band11 : CutRow book 11 0 7 := combine11_0_7
set_option maxRecDepth 16000 in
theorem row10_0 : CutRow book 10 0 1 := bandCut 10 false (by decide +kernel)
theorem band10 : CutRow book 10 0 1 := row10_0
theorem checked : mixedTables book 14 := by
  intro k hk
  interval_cases k
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact band10
  · exact band11
  · exact band12
  · exact band13
  · exact band14
end M3039_15
theorem m3039_15 : Face false 1535 15 :=
  mixedLower (g:=M3039_15.book) (i:=0) (hints:=4882524037)
    (before_sound M3039_15.entries M3039_15.prior) M3039_15.geometry M3039_15.checked
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem m3547_12 : Face false 1787 12 := carry_of (swaps:=[152,166,50,64]) (by decide +kernel) m3031_12
theorem m1243_9 : Face false 635 9 := carry_of (swaps:=[152,117,67,32]) (by decide +kernel) m926_9
theorem m3549_13 : Face false 1789 13 := lowerHint (lower_down h3549_13) (by decide)
theorem m3550_11 : Face false 1790 11 := lowerHint (lower_down h3550_11) (by decide)
theorem m3551_15 : Face false 1791 15 := carry_of (swaps:=[152,166,50,64]) (by decide +kernel) m3039_15
theorem m3671_12 : Face false 1847 12 := lowerHint (lower_down h3671_12) (by decide)
theorem m3795_10 : Face false 1907 10 := carry_of (swaps:=[162,50,148,115,98,81,128]) (by decide +kernel) m1631_10
theorem m3803_13 : Face false 1915 13 := carry_of (swaps:=[162,148,99,114,81,128]) (by decide +kernel) m1759_13
theorem m3807_16 : Face false 1919 16 := carry_of (swaps:=[162,48,49,148,83,114,97,128]) (by decide +kernel) m2015_16
theorem m3855_12 : Face false 1935 12 := lowerHint (lower_down h3855_12) (by decide)
theorem m3927_13 : Face false 1975 13 := carry_of (swaps:=[65,33,164,49,100,115,130,81,144]) (by decide +kernel) m1759_13
theorem m3935_16 : Face false 1983 16 := carry_of (swaps:=[67,64,161,50,116,83,146,97,128]) (by decide +kernel) m2015_16
theorem m3998_13 : Face false 2014 13 := carry_of (swaps:=[66,16,164,84,147,130,97,112]) (by decide +kernel) m1759_13
theorem m3999_16 : Face false 2015 16 := carry_of (swaps:=[65,33,160,116,131,146,97,80]) (by decide +kernel) m2015_16
theorem m4047_14 : Face false 2031 14 := dropFace 96 4882196357 m3855_12 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem m4055_14 : Face false 2039 14 := carry_of (swaps:=[152,118,101,165,64,48,32]) (by decide +kernel) m4047_14
theorem m4059_14 : Face false 2043 14 := carry_of (swaps:=[166,117,66,48]) (by decide +kernel) m4047_14
theorem m4061_15 : Face false 2045 15 := lowerHint (lower_down h4061_15) (by decide)

namespace M4063_18
def entries : List (Nat × Nat) := [(474,7),(476,8),(478,9),(633,8),(634,7),(891,12),(990,12),(1018,10),(1023,16),(1277,11),(1333,8),(1469,11),(1502,11),(1531,11),(1532,10),(1533,13),(1534,12),(1535,15),(1787,12),(635,9),(1789,13),(1790,11),(1791,15),(1847,12),(1907,10),(1915,13),(1919,16),(1935,12),(1975,13),(1983,16),(2014,13),(2015,16),(2031,14),(470,7),(2039,14),(2043,14),(2045,15)]
theorem prior : Known false entries := (consFace m922_7 (consFace m924_8 (consFace m926_9 (consFace m1241_8 (consFace m1242_7 (consFace m1755_12 (consFace m1950_12 (consFace m2010_10 (consFace m2015_16 (consFace m2525_11 (consFace m2645_8 (consFace m2909_11 (consFace m2974_11 (consFace m3035_11 (consFace m3036_10 (consFace m3037_13 (consFace m3038_12 (consFace m3039_15 (consFace m3547_12 (consFace m1243_9 (consFace m3549_13 (consFace m3550_11 (consFace m3551_15 (consFace m3671_12 (consFace m3795_10 (consFace m3803_13 (consFace m3807_16 (consFace m3855_12 (consFace m3927_13 (consFace m3935_16 (consFace m3998_13 (consFace m3999_16 (consFace m4047_14 (consFace m918_7 (consFace m4055_14 (consFace m4059_14 (consFace m4061_15 (known_down baseKnown))))))))))))))))))))))))))))))))))))))
def samples : Nat → Bits × Bits := (fun i => (if i<8 then tableBits #[(padColumn 238 0x1ffff000000003fffe0000000000000000000000000000000001ffff,padColumn 238 0x1ea00f5007a803d401ea00f5007a803d401ea00f5007a803d401ea00f5),(padColumn 238 0x7fffc0000000000007fffc0000000000000000000000000,padColumn 238 0x787e3c3f1e1f8f0fc787e3c3f1e1f8f0fc787e3c3f1e1f8f0fc787e3c3f),(padColumn 238 0x3fffe000000000000000000000ffff800000001ffff00000000000000000,padColumn 238 0x61e030f018780c3c061e030f018780c3c061e030f018780c3c061e030f),(padColumn 238 0xffff8000000000000000000003fffe000000007fffc00000000,padColumn 238 0x98864c4326219310c98864c4326219310c98864c4326219310c98864c43),(padColumn 238 0x1ffff00000000000000000ffff80003fffe0000,padColumn 238 0x12a2295114a88a54452a2295114a88a54452a2295114a88a54452a229511),(padColumn 238 0x3ffffffff,padColumn 238 0x2d4156a0ab5055a82ad4156a0ab5055a82ad4156a0ab5055a82ad4156a0a),(padColumn 238 0xffffffffc00000000,padColumn 238 0x2455922ac915648ab2455922ac915648ab2455922ac915648ab2455922ac),(padColumn 238 0x3ffffffff00000000000000000,padColumn 238 0x36161b0b0d8586c2c36161b0b0d8586c2c36161b0b0d8586c2c36161b0b0)] i else tableBits #[(padColumn 238 0x1ffffffffffffc0000000000000000000000000,padColumn 238 0x2818140c0a06050302818140c0a06050302818140c0a06050302818140c0),(padColumn 238 0xffffffffffffe00000000000000000000000000000000000000,padColumn 238 0x306018300c18060c0306018300c18060c0306018300c18060c0306018300),(padColumn 238 0x3ffffffff000000000000000000000000000000000000000000000000000,padColumn 238 0x3f801fc00fe007f003f801fc00fe007f003f801fc00fe007f003f801fc00)] i))
def cols : List ColumnInfo := [(1572,1,474,0,7),(1570,1,476,0,8),(1568,1,478,0,9),(1410,4,633,0,8),(1409,4,634,0,7),(1156,0,891,0,12),(1057,0,990,0,12),(5,1024,1018,0,10),(1024,0,1023,0,16),(768,2,1277,0,11),(706,8,1333,0,8),(578,0,1469,0,11),(545,0,1502,0,11),(516,1,474,1056,9),(516,0,1531,0,11),(515,0,1532,0,10),(514,1,476,1056,10),(514,0,1533,0,13),(513,0,1534,0,12),(512,1,478,1056,11),(512,0,1535,0,15),(386,4,633,1024,9),(258,4,633,1152,10),(257,4,634,1152,9),(260,0,1787,0,12),(256,4,635,1152,11),(258,0,1789,0,13),(257,0,1790,0,11),(256,0,1791,0,15),(200,0,1847,0,12),(12,128,1907,0,10),(132,0,1915,0,13),(128,0,1919,0,16),(112,0,1935,0,12),(72,0,1975,0,13),(64,0,1983,0,16),(33,0,2014,0,13),(32,0,2015,0,16),(16,0,2031,0,14),(8,1,470,1568,10),(8,0,2039,0,14),(4,0,2043,0,14),(2,0,2045,0,15)]
def plus : Nat := 0x20240141080900910208408440840a012018021
def minus : Nat := 0x7e0d214a27149285506932214382424618930cc11c1701f
def orderBank : Nat → Nat := (fun i => (((fun i => (if i<48 then (if i<24 then (if i<8 then tableWord #[0xa023b10800b8010ac6413a0228294cae81040850006012a9914e981880a3000a02639000048118e20002e006bb080078196c240036005b39000580068a6001de219b200038098e6020be011821f089811a0e3,0x11e219aa0001805ae6201be020821c00c49082e80006013a988008710a4ca0022002a2900088018ea053a6062020c00d8010ae600160042a180088016ca40016004329b40780580e1000a026b909c2f80500c7,0x29c4293a800b79906ca0029e219ba000470844a8b01e014830400c79906ea0015e641a2882f80460650035e219ba082f80460a70022005bb1000a710a4c80006013b18904e808a0850009e109aa000b8010ce6,0x312638bb00058110c46a13a0258396089810e0c30006015b99000478864860016044291800c710a4ea000e006ba0904e808a08332ba041018e84e80960c50035c8593b00078196e240036001a398001804a842,0x15e109b20008800aac453a60620204cae3904085002e003b38800d78864a601be020819400c710a2a84138e228294008380aac40004e12a990cae81040a50011c2113280018044a64002e001a39a089810e0a3,0x2de641bb000778426c8000a02539000038008a820006012298800d78426e80036005448b089811a0a10036002a288001805aa400034e02ab9214d820c0c1002d2638bb00048114e2053a4e62028dc2f80500a7,0x53a6062031400b8010f080006012b21800b801b3040006016ca10002809b264000a02541880048115042000e0264a000028099260001204649000068199220413a022831400580028c60006012b190002809aa20,0x35e219ba800d70844ead01e016048400d800ad26000a023b9900018055082d01da1603840036898e600006002b212ccd81940e1002ce03b3880038092e60000a024b90340780580a1413a022831f089811a125] i else (if i<16 then tableWord #[0x1de219b2800b78426e80006015398000778864a6d49e0860386082810e0c332ba041020c00180448427192024031c00b21906ec002c4638bb000849082ca0008e23b10882f80460850009e1092180018056c64,0x160043b20008800ace6000e006ca9000380150a2a13a025841eccd8194103b01e014840400c710a72c0029c429c3000d8017126002e003bc1000d800aae40011a4638814e981880c300360019a93089811a081,0x16044289340770580e1000dc2639800027098e40000e023b188001384ec628224e43830c00b4a9a2ce0036000a39882f80460a932ba041029c00d788692a001de21a3a800470846ca0036001aca000b8006b08,0x29c211c280058006ac8001604439a000d72167300022005c39800180570860006013ba1006f80820a90009a26390000778866ea000601231880028088c4200160019a1000770844ca002e000a398008800a8a2,0xa11a025831400d32164ec00360042a100048112e200011c4638800028092a200015e641ab000a70844e80006006ba08002808ee4200312420bb000d8006ae60035a850cc000c498e52e0021c429bb000a788690a,0x2e084291b40780580c1b01e01482864ae81d60c570be01403a6089810e0e58536083038c00b498e50e53a6062018406f80820430035e109298005784248600360009a900088004ac40006005ba10008710a2a8,0x70b2014029400c710a28600160042990002809a820719202402940058010a84b61e0e48306d8783920e100060133180002808cc40000e024a9000088196e6432b8e410297089811a0a3b01e01482040048118a20,0x160043b1800d800ace400360012b9000b799090e20bd211819400d48066a420be011832400278428ca70be014039c00778426e8149e080012c00580026840006002a188001801aa600029c2113a8003800eca2] i else tableWord #[0x4e02b210001384ac640004e112990003801aea2b336065030c00d6a142ec003600533880018054c62001a06638800077886486000e0262903089811a0c30006013a10800b821ae4270aa014029c00b51906ca,0x318641228005619046a0006013a900003801aa60413a022818c008800a6a2000e023a900002808ea20000e023a98800a821ae02c3a6066838c00a710a4ca0029e219b200018056a420016044391904e388a0c5,0x32ba041031c00470846ec0015e10a3a80058002ae800060113218008710a4ec00212420bb000770844eac226046840c001805b062000a026c10b527821808b8226043818400d3a40a8420be011818e083810e0a1,0x16004b202089810e083001204630821a1828e0a30006013b988008800ace40002013b80b089791a0e30035e10a4a800b784290a0036000aca000b8002b0800152019a11c2f80500850016044209104e808a0e7,0x158641a2852782000610022004bb01c2f70500a70035c042b9800b7010ac60006016a90a84e80960830035c858aa000b79904860036005a288001805684245ba0828214004721648c002e002a3100088012ca0,0x22005aa0a84e80960a30029c210aa000b78424a6000a026288284680960e50004e122989c6480900e70016001ab180038094e6053a4e62030c0013848c6270b2014029e083810e0a300318641ba800b61906ca,0x1de219ba000b21906ce002c4638b38003808ee620034e012b9000d8296c2470a2014029c00c41906ea002d0641b2800c49c82e800150641a28008801aea2002200222880078198e20000e0063a0000b80108a4,0x1520091880053b18a0800060029900001804a620d01da16022f02d3a800a5c3a5c66820400d3840a840009e108990003689882a20bda1181954e939880810004e13a900002388ea20820a0438286082810e0e3] i)) else (if i<32 then tableWord #[0x4e12a108003681aa600005a16a900002689aa2070be014018c008801886a0031e640a180073a40a6400260841a880083c18a2800120462028001805a82001bd220810d04e808a0610015e10899000d4802482,0x22001341800180172a60006015ca1800581110688226043838c00c498e30e0035e219c2800d8006b06000e006c28b4078058101b01e014838504e388a08332b8e41018f089691a0a156a5aa2020400d380a8a2,0x36004229284e80961270021c859c4800a710a72e002924214b8008490850e0029c211cb0007788690c001dc211c3000478868ec002de10a4a8007784290a002e00444a000b8002b280016001b3a00088017306,0x5c16b988001704ec620009c26b908002708ec42161e0a0028400c490852c001de10a3a800578428ca0016000ab2000180170a60006002b298001801b2a4000600232900018048c84000600542880057990468,0x2012b0105876a80081000e003ba88001800ee8220bd211829c06f488208756a5ea2030c00d4806ae60035200a39800548028c6000de06ba88001781ae820005e16b9880017848c620009e26b9080027888c42,0x21cf292a00008056c040034e8483b000c098e2ea002c2638b2800b78426c8001de109aa000b80028c60006005b21000b800eac20016076390000c498e2c800312420ba800c51906ea0025c729320005519068a,0x6013a9900058014c82001204531080088198e600012046390000a7886486000e006a98800b4a9a28a002e006aa09c2f80500650031e64129800d80106a4002e0041a100088016862b01a01483040053a9808e,0x1e064b880001804a8640022004aa0000b4a9a2ac001e065a8b80038098c40c2260468396089810e0a553a6062021614d820c0a3003126393a800b498e4ca003124213a000a49084c8002e006bb1000b80088c4] i else (if i<40 then tableWord #[0x20e02b390002388ee4200060133980002808ce40003046394b800d708472a00360043ca0003808ee840022005438800580150c271be09402140014a9a26a0006006a988009821080435ba0810296c0680520e1,0x150641ab14e981880e500060023a900018048e84000a022399000d788692c0035c211cb000a708470c0036001b4a0001804ce8270b2014031ec0748520e1b31606503840033808a82000ce23b18a14d820c0e1,0x2d201a31800548068a6000e00532080028094c4200160063a8000a70842a60006005a9880038018a608536083030c003800cca200060133189c2a80500c792ba07583945274a000810015274b901c2880500c7,0x92ba075820cd6e82040630006011190800c8290a04002e001a31800971ca4ca000dc9591b00088196c640036004339800d380ace486a60f3830ec0280520c1001de2192a000778424a620bd211821c00d48068e6,0x30864122800849082ea00160043a980088192c600016074b1000078192c20413a022828d4e939880a10011c210aa000578424a600160009a90001800aa620006012a9080013848a400008e222882082810e0a3,0x9a262028003681886a000cea629a000c82866a200360019a08007699880a0005c16a08340758580e1000d62639800025898e4000116463882089390e0a10021a019a900056806684000ce03a981c6f80900a7,0x2cef62821c2f805008335b92810184008800048a000e00011a80077886286001ce902a1000070840460026084228800982066a2000a020102800b3a40a04002e08420095a982880810015a0621a80053a98a68,0x36001a4180036a5526e000a0253948002808cc520036002ac100048114e320035af548b8003801b082001a06644800038099060000a02641000048119020001600621a800c710a086000e02620a8002809880a] i else tableWord #[0x8536083034c00d8014f120036003344800d6a1530e0035c85943800c498e30c002da634bb00058014eb20031c4294280046a152ae000e0053a48003800cc920035e219c200036a1528e000601539c8001804cc72,0x11a46408010f7182065c225a46828d5a96a88083d01da1602845876a8006100312420aa000d70026a40015c009a10001681aa620005a022188001685aa420005a1221080086998a400011a462882ccd81940f3,0xe0033ac800d708450a00060033a4800d7842708000601339c800d8002906000a023394800d800ad0400360012c1000b6c0d24e001204338c8001801b0820002013384800868190e0000da2641800026899040,0x52154a08001384d08200092254988002388d06200112454908004390d042000d224ca0000248932600011244c9000064993220853608303cf407685810100360033c480083a980f000160033b4800c490830c,0x8224e4384154e969880e5b335265048e14d3a0c103b01d214848400b698c330002ce03c49000b6808f24000ce03c3100036808ec40005a023a90001384f0840005a123a10002388f0640009a22399000548152e2,0x32b9a41018f40770580a10035a02a288001684a8420015c062a000037018a60000dc2629000027098a204139a22818e089810e0810031e6412a000c710a2a60016004219000d680a6a20021a029a09c2f8050109,0xdc03b288001701ae82000da063a800076998e20a12e025841c00d5a1673070b201403a6083810e0e5002cea6044800c198e52e002d864243800b198e50e002124213b0007819704600160064b0104e688a083,0x150641b3800049c828c0001c2112280018004a840022002338800568008c0000da002280003688086000020112810d6e4a040a5c3a5c66838e1a9728e0c300352012b900084804ac400052112990003701aea2] i))) else (if i<72 then (if i<56 then tableWord #[0x2e084311800b820ec420002012a81000b3a980ce0016005b21000b80088c2002da063b000086818ea00015a7639021a983ce0e3001ce1003a00088004ae40016003bb0800868008e000320a1a819c2880500e7,0x2da633aa00058014a6e00312420b180046a14e6a0006015293800d70108c4002dc0422900048114a2e0035af538a80068198ce0002200632000088198c4045ba0828294d6e82040850021cf2932800472444a8,0xe024a101c2f70500658226043818c00c498e2a60035c041a90001804e6420022004a1800088198a40002e006aa02ccd81940af8536083023dc2f705008553a6062018c00d8014ace0035a853b2800c79904c8,0x35e21931800971c4ea6000946411a00018056a4e00360019b100087416e4a0035d05b8a8003801ac620006016b10800581d8ce070b20140216083810e08300306638aa000d68066a4002da019a100038012860,0x3600423100037256e4a0035cf5b8a800d7404e260002015a8380097244e0692ba07582bdc2a805008586860a3820c00d8016ace0034e8483280088016a8e00302638b2000b51904a8002c2638aa00038016a6e,0x35e05b3900087816ca40021e02a2900057110a46001de65b090d6e820406fb01a014828400d80046ce002e0011ab800b32120ea00220011a3800b79904a80035c913b18003321206a001dc913a18001804464e,0xc2260468296088810e065b336065020e14c820c0630035a850aa000c418e4a6002d063921800b801aa84003600522880048114842001204629000068198a20868a0a3828e84e78960c54139e2282140057010a86,0x718202403a400b118c30e0029242143000501908ce00360012c980018044a860022006cb9000d78864a80036001a290003801aa820026081a01000c498e2a8001de9092180018010864000e096a9080088000680] i else (if i<64 then tableWord #[0x60154180002809504000120454081c6f38900c7243ce61821c00b3810ce6002ce01a3980053810ca60022062a992089390e0e30015e641b380083804ae4000ce03ba88001384ee620008e223108004810ce20,0xd22021c800b8010f06002e001ac1800248930520002012b49000880170e40008e30492000180170840006015c19000449130320000e12348800b380ef020004e03ba08003388ee62001e065c0900064993012,0x2120023c800b219070e002c4638c3800548008d20010e84cb4000a710a50c00148641b3800348130b2000d20022c80033a132b00029e219c2800b384130800008641a38000118e28e0014e104b200034893072,0x2c6638bb00034892e600009224b9000044912e20b335265038614d3a0c0c1000521539800024894e4000112453882082390e0c3b01d214844e4293a00129a13a0258416082390e0e3b336065040400848130f2,0x2dc06cc1000b700ef04000dc06cb10003700eec40005c06ca90001705b2840005c13ba10002709b2640009c23b99000a721b224000dc264a0000270992600011c4649000067199220820ce43830c00b61906ec,0xa139225841ccae49040c7c225c468496089710e0e5d01dc160486c0748521010021c859bc000778868ec001dc211bb000d48171260035201349800848170e60021201339800148170a60005215c2180014844c86,0x160054b880018055282000601342080028095262000a02341880048115242001204341080038093280000a024c9800048113240001a064c88284e48960e532b924102140084816ec40005215b9900074996e24,0x2ce83b1080058114e408516083030400b41906ec70a20140426089810e105b336065048e145820c103b01e014848400b298c330002e003c49000b8008f24000e003c3100038008ec40006013c210002808f064] i else tableWord #[0x70bdc14031c10f7182087a2b9e45839516e7a0a0a50015e109aa000b7010ce6002dc00a3980057010ca60015c00a2980087816ec40021e02ab100017816e840005e02aa100017856e640005e12a9900077996e24,0x2015b8100064992e20002d4641bb000b098e2ec0025c7293a800551906ac002ce1003a0001490828a0016000a2980058016ea4002ce022b880083808ac20004e022a0800548008a0000d2202180000384ec02,0x26081a8180074992e20b32e065038ec0648520e1002da630bb000372164ae000d6850ab800772444ca002e001ab9800b8004ae4000e0053a880018014e82000601539880068184a24000d204ba800084992e60,0x152c6b8b00048118ce0002d2019a100088018a600025c7293b000971c44ea0011e219b28001721648e00052420a30003725646e000ce9481b80008196e84000ce0232880013808c82002d26023800054992ec0,0xb01601482840085a1628a20bda11821406f6882065002da009a93089691a0cf002da06b2b800b4a9aeac000da06b2380034a9ae8c0005a06b1b80014a9ae6c0005a16b1380014adae4c002e0009a90002689ac2e,0xe003aa3800a70842c8001dc210aa0001800ea6e002de109318001804ea4e002e0009b10002808ea2e002d303b8a80018016c620006015b108000804ea0e0031303b8280038092c40000a024b08284b80960a3,0x1a064a881c2f30500a78224c43828d4e979880830034c042b9800b3010ac60014c042a180053110a46002de06bb08001304ea6286a60f382bdc2f80500a5a106025830c00b800eace00202858ab000812120ac,0x1de919218003801086400220011a080058112a20a13a0258294cae8104065b336065028e14c820c083002d8630aa000a70844a6000986309a00088004684000e00321880028094a42001604321080028092a40] i)) else (if i<80 then tableWord #[0xe006cb1000580150e292ba075828ed8783920a10025c710aa000b7b824a6000dc9589280008196a620022065a9080088192a400016074a8828aa81160a3b6120a48284008521628a00208848228003521626a,0x10c859b4000302142b0002e002b41800a8206a28001a065c098002808ce62002a086c890004810ce42149e080028400c490852e0029c429c3800a490850e00360013498001800aea60006012ba1800b8008f04,0x2ce02ab900088014ec000160053a800038014e80a1060258396c0280520e10020285933800812120ce0002013b00a84b80960c5b016014830400d5a164ec002168592b2cc0819410300340850cc000b698c30e,0x16000234800c710a50c000e00022c800d3a41308001ce904ba00043a412c800260843c980098206b26000a026414800280808520034e02b41000481190320026083bc8800d3c01228001a066404800a821b002,0x850e083030400c49c82ea0035c2113a000d38048e40004e112190008801aec2c225c46838e089710e0c3000dc06ba0800a721ae02820e043830c00c198e2ecd49e086044c5278200093002200023c800580190d2,0x356850cc000c118e2ec70aa01403a6082810e0e5002d2a6944800b519090e002c463943858772800810031e641bb000c698c2ec0020e012b1000d800cce2000a02331080087018ec0000dc063a800067198e20,0x4e1220b00081412e2a000d25230a00028092a0e0008e22203000b3c00e040006015a8815a982880a3b092014039e84b80960e5a20a043838c0052992cae0025e719b200033892e6c0010e44b8b2ccb8194103,0x413a0228204cae81040610012040133800b80004ae002ce0222b00040a1608a000e04231b80038012a6e000ce0221b000a78862a6000d24231a00013bc8e4c002de108a900053b80e840008ee0399000d83c66e2] i else (if i<88 then tableWord #[0x243ce61810e841809606132ba041010400b781886a0034484aa18003781884a000cea6292000a7886264000de2620a800d38064820009e262028008818442056260e2023dca749880c9169e0f0013e84180960a1,0x60101028003388e806000ce9390180084c08a02000d2521809c648090085b61a0e4828400b21904a870aa014029458782800610001c2109a000880048a20006001218800380006800002011200b5277a1808b,0x8208e43821e1a983c004bb0092138215589838802bb29d262018ec24805008100be0140104008810868a002e0020a2800b4b80a640000e1209180084908682001486400a00054b80a2400152639890003808e80a,0xb61e0e4822ccae8104043c6a60f3818400c4c0e0a6002dee62a18002819284a0025c710a100027b98a460016074a0a800b7c12a260015e74a09800d83d260a0034f04a820003820e640002e0839882d87838806b,0x320e5b01182f80500a756a60a2020ec2a80500a5a106025828ec0280520a10029e2192a2c2480500a59106025828ed878392081002c8641228002119286a0025c210a9800979c6486000ce24a9200088196842,0x14e1032980023840c8600120843290000804aac20002011230800238c0c260000e122b000013a0ec607192024029ed8683920c100308641ba800b21906ca0014ee60238005219068a00212420aa000d8012ce0,0x21c06a280003701a860000dc23a900002708ea2000148641ab800971c44c80020f0481b000880048e40014874193800d3c1202c90a4e80031c02f80500c500152001ab000579904ac000d2001a3000078c64c8,0x11c210a195a98288061001486411a800d800a6820022006a2800048110a04c225e4682855a97a88081000de06a980001785aa400009e26a880d6e4a040630035c210a1800848046a200352011a080014844642] i else tableWord #[0x2e086a881c2a80500e700304638b38008710a4ea0031c42932800d78866c80036001a318008800aae40036002ab10003801ac820006016b188002809ac4200320a438180028098c4071820240294005019048a,0x6016c210002809b064001e065b91800d800d30200060053a88001804d28200060153a080028094e620012043490800a821b02400320a4482000280990600002013c810000804d20245ba082820c00c71ca2a8,0x2de10a3a800172166ae0005c429ab000d80113080036000ac2000b80112e8002e000aba000580112c80022005bc98008800ad260036005bc180018016ea60006015ba1800b801b0e40006006c290001804f284,0x82260438497089811a1058536083048eccd81940e30031263944800c698c312002de6423c8008721672e002d26393c800d721670e0021c429cb0008490852c0031242143000a710a6ec001de10a4a80014a9a4b0,0x4138e22818c008380a6a2820ce438285c6f80900e9b316065040e145820c0e3d49e0860486d8783921010034a850cc00088197086000e025420800b8010ec60022005b39000b800eec270be01404a684e80960e7,0x244e80960c50025c4293200058018a80] i)))))) (i/16) >>> (42*(i%16))) % 4398046511104)
def orderClauses : Nat → Nat := (fun i => (if i<64 then (if i<32 then (if i<16 then (if i<8 then tableWord #[0x2ea0d81aa542e83404603a4a6948580304a25ccb90f,0x401301d07a1101e0760a817c298f111e2c84705e042080588251a43441d8420963c01180f11a174291e,0x800108e1300003c0149601f83803409c0182c06204c0205508c0f82283703c08c0880f4ae9592a9d,0x920d82c04d0903546a0d31e815c798301e4158300f,0x5ecbd1211ac5e52f25d2f05dcbb25c4b69692c8e,0x2f65e8c19824c2980bc1812ec600bfa5f2fc5f4be0f,0x920d82c2620903546a0d31e815c798301e4158300f,0x4907a98b1ac2409198a312488c418730c614c20e] i else tableWord #[0xf54dc4846b26d4d89ad352692ee9a133a664ca9913190,0x2483d4c19824e69c8911814e2600bfa704de5f4be0f,0x50650c99923221202503a1222ccc818f31c634c60f,0x14828f0200041e80d01849c1e00a32c6554728d518a2d45289510a1d4301a50aa1141a8205a00c162815009fd3f0200260113ea7c4f61381f00b4f49e53c126046494192774ec9d53a35,0x500d81a9923221202503a1222cc2b83031c634c60f,0x29e53aa714da9a5323546a29852ea594aa94526a494890,0x56a3dc1301d0c61109399b124ad15999a564ac55812a252abcccaae16c4a021aad5583d82782155666155062552aa153aa60ee184212a532ea90930b524a2d151aa2542a814fb3,0x800101a0300003c0141e41f83803409c0182c06204c0209409c0f80583703c08c0880f0f02dc499d] i) else (if i<24 then tableWord #[0x5a03e45c1ae2604bd67ace59ab31659ad5946b0d59aa3526a0d39a625c694d212d1f068cd11a1258680cf99e33a67095ac9590b1d632c5588b0d612c1580afd5f2bd578aed5d2b9570add5b37,0x264b5c2c2d61aeb556a1b035eb4d692d1262158300f,0x1f6b816fade0901281d0fa266b756e2db5b4b656c0f,0x5d22e04d8710e0ba03789a0fa264dd8bc5ceb9972ae41306e84bae326e4d8dc9b826a1b89a1b712c1f05d9b636a2e83686c12a6d0d986b1726c8352e20f6164d887a0d21a1708670cc1943237,0x6d8a65d61c4528701b41bc4d0d90fa265750c31843f06c09812e304520c017e28c510a10dc2804f8be12c1f05d89e1742f43686c12a274358b90d41ec2c89c0f41a4340670cc1943235,0x200980eaf65eabd03c83f0fe1f8478b20b4178108c414ebcd792f15e0bbd771bf37c6f4de2ed0f02dd761f,0x396728318442707243c8c50fe1f82185a09e084e41c738c3f87e8770c2108e29c4386708e09c00f02dc499f,0x30004c074318441247397f8b60863d827afe042bf47f8622741dd7e061084bece69cc16a2d17d2f95f0bdc9ca0] i else tableWord #[0x3dc1301d0c6111831ce2542d8940431ecc14278210c44e9820770c2109819cd3984ec6330260273c9c9e,0x808dc0004f00b879150c30e9100038744e801601c0540281461620003b0a03601984b080f0c1c499d,0x8001626c480003c0141e41f9d362209c01b1006204c0209409cc3c0583703c08c8130e0f0c34499d,0x500680880004002e048158330540b80e0240520580701500a0500c83900e06c03018004024041c,0x64cc959210427cc8c6f0dd644c85901d463ec798eb1c360c6d8d319630c5c81b1662ac509e9b,0x2020746e000278048158a83ba770801db0b4768ec8a701c760028143ae200039d618e0780d806004754041f,0xa050c0004002e048f08a80540b80e1e02840a4ef81601c0540294103237c0381b204018a013f004778041f,0x3cc5202c12328e794a31e43c6514f114464e158300f] i)) else (if i<48 then (if i<40 then tableWord #[0xcb87132d0e4384f432c28ccacf3b2a652ca0700e,0x2ea388390e13d0128f533266279cf4949660cbc700f,0xcd4140e26681c99984a20c244f4949206414700e,0xa61f93f07dc859f60240ac8502a3ea0b8fa1f33e40a4a594a3e27c0f79093dc420f68183d87ac839d,0x1a4b48050411a38de1bad18fe345688d0da1341680cfd9f33d678ced9d1fb672ce19b90366c7e89e9d,0xd68990282084f86f3596b0d5dab1fc6aa751aa3536a4d448335069ed38fdb4d69840da59fd6947e89e9e,0x14c6c4d840004002e048158330540b80e02405252ca53606bed79aeb5c00e06dad818004024041c,0x80834044001b18170240ac541d2200070e89d002c0380a805028064401fe00e06c03018004024041d] i else tableWord #[0x401301d07a8041e2000be14c7888f1642382f0210402c4128d21a20ec2104b1e008c0794d0e81ccff9e,0xdbdb736d6d81c870b6b6d4da5b43676ccd95b20e,0x40a3889f07229cdd10237335edc901b716e0808700f,0x1041247107229cde1020816ee34dbb203292dd4700f,0x37f14c26c388a50e01bc4d07d13230d05b7e37425dbeb7c148828600bf146289048a10dc2804f87c6f627836b7a0d8255bc89d0d68203507b0b281d0309c0f41a4340670cc1943234,0x1530680880015202e048158332a25400e02429e0580701500a0500c83900e06c03018004024041c,0x4c07431844000248090c50fe1f82185a09e084620a70c43f87e8770c2108860c703c2d4088b4004024041f,0x1ee0980e9101c6e18aaa1070a4a45b1280863d8278211fe18907b8421e43886b837045510738141a831c01f] i) else (if i<56 then tableWord #[0x38c7160f40680c1521443b0540be14c178c90340b46400303ee29c4b8804a138723870ea844190832ac1742920,0xed5da15804c075d9863088ec8aabb1760ebdd73ad758eadd53a9252ea1d3ba674a2d821ba4746e89d0821740e7dcf39d1fe55dce39b7344e9ccb9872e44430b9672ae51c9b922a8e450739071ee39c6ba,0x21c0083d01a031db0510ec2184282f1080b40181f0401040202507602c3aa124225641908311a174291e,0x100025680680c152145098540be14c178c90340b46400303e0802081304a1387200b0ea2a8190832ac1742920,0x100020f40680c152145ddbba0be14c178c90340b46400303e0802081304a1381d80b0ea2a819083772ee1dba0,0x8540083d01a031e0851428f01df82f1080b40181f0401040202507602c3aa121545641908377cef5de1e,0x100020f40680c1521443b0540be14c178c90340b46400303e0802081304a1381d80b0ea2a81908311a1742920,0x1b63e45c3df7bcf75ee09a1b2f6ded0bc186309ec8d84348650c3d87ae4dc9b1b91f085c9a86e268f59eabd47a6f49e8bd079ef39e6bcc796f29e4bc878e1643d2160d2f18343c5788f0de137] i else tableWord #[0x10002f9023be31521443b0540be14c178c90340b46400303e080208137c4119f08450ea2a9f008311a1742920,0x7f63e45c1ae2604bdfd21e7f2fe1fb9ad7ec6b0d59aa3526a0d39a625c694d212d1f068cd11a1258680cf99e33a67095bf57e8fcdf921d7e2871f821b7defb9f6bec7d6fa9f4be87cef99f2b7,0x2200020f40680c1521443b3fd7f814c17a1f0340b46400303e0802081304a1381d80b0ea2a81908311a1742920,0x207c0e81b030548510ec1502f85305e3240d08e0bd02e0540981101e0340580900e014010ea2aa003ff11aff82921,0x4480751185142888a0ec1c837068474190bd060100b102705c12c161a20ee0ac1482656419412822886081f,0x401301d4030b513c2c8570aa1488f8502382f02184e2c6130d2085095134248468961142184107e0f1e,0x980ea230c6110aaa228770ea1c84387013e1b82186d0d4ab8628681dc720610850ce191540650c61842f44273e1722,0x3cc520390e128e794a31e43c6514f1144878414ad8f] i))) else (if i<96 then (if i<80 then (if i<72 then tableWord #[0x1f65201a8721c251c251ea1f50f4a2944450414ad8f,0x8942082495e1123786ec4989111e2315d88b110ae08188710a20c4087e8a48908887c394651b,0x11362615e112374ae95c10312d14912110394650e,0x4c81445006b13e2722a20c580af912262394650e,0x8c41a00d01842c0902b0664281c11404e44c0fa3045e8b80289410002c84a2d2108b115961004024839e,0x232c641041263188946918a30c608bf17919c5d8b916d190818b51662c4578ad154444548a714a289d,0x46e0680889c46d8d8048158330540b80e0240531ae3546900a0500cc688cf19803018004024041c,0xb48340444540b8120560ccb41672cc090b281601c0540281403237c039642c606c03018004024b11d] i else tableWord #[0x401301d2b41111aa000be14c7888f1642382f0210402c4128d21a20ec2104b1e008c0794d0e81ccff9e,0x11ee3d4798f03763bc768eb1d239c728e31c2378e,0x2059080d641c829032023f9608fc57e3e9313fa80a3e10,0x1041264688991853a45c8a1032264448711121a428f,0x3e45c09b2604bc3821e1341f44cc9717830e4b4959288690ca1825c4dc9b12d1f085c9a93425825a499b69242ea4892b0d9242479b443a1ad0e06a436166471b10f41a4340670cc1943236,0x1b6298388a50e036837ca21b21f6508c29402624f8c114882a4f0a31448245086e14027c5f07c93a2785e86d0d8274358b90d41ec2ca0613885a4e49b9352664c0670cc1943233,0x5094c0880004002e04a52ca405528c0e0240520580701500a0500c83900e06cb5018004024041c,0x401301d9561111acaa9532a07888f1642382f0210402c4128d21a20ec2104b1e008c0794d0e81ce539e] i) else (if i<88 then tableWord #[0x21c008470982280507610c2141781a05a00c0f82008204c024af08c114258ab01f2ba56cac11a174291e,0x261cc21ee0980e9101c649ccd892421304cd4c097f2f8954bd3322d821cbc9772e810cb99706607f95796f2da5aa0f21e444874b496665e59126276494634b141a8325831,0x800108e1300003c0141501f83803409c0182c06204c0205508c0f82283703c08c0880f1ce3988b1d,0x800108e1300003c0142b81f83803409c0182c06204c0205508c0f82283703c08c0880f15a2b0659d,0x10a80108e130004c50142ba6203803409c0182c06204c0205508c0f82283703c08c0880f15a2b0659d,0x800108e13264cc80a21501f83803409c0182c06204c0205508c0f822cc737e6f8de9bc1ce39a631d,0x396728880e3270724570c50fe1f82185a09e084e41c738c8d8b590f21c434e29c4386708e09c015a2b0659f,0x4400042384c22a02a6783f99c87c13ccd0060b11b8310261566604608b32e6503703c08c0880f1ce3988b1f] i else tableWord #[0x401301d1c689c574d89af3583f87e11e2c82d05e0428dc6216b9aa4366a22644b34e694d115a2b2681e,0x26e8a61361c4528709b81bc4d07d13336c61a0b9b53644c097182290600bf1462885086e14027c5f0960f82ec4f0ba17a1b43609513a1ac5c86a0f61650389c0f41a4340670cc1943235,0x11200108e1300008a0142ba6f03803409c0182c06204c0205508c0f82283703c08c0880f15a2b0659d,0x6d8a61361c4528701b41be700d90fa2645e4df1843f06c09812e304520c017e28c510a10dc2804f8be12c1f05d89e1742f43686c12a274358b90d41ec2c89c0f41a4340670cc1943235,0x4c074880e3000248570c50fe1f82185a09e084620a70c48d8b590f21c434860c703c2d4088b415a2b0659f,0x21c0095a01a0304500a4262184282f1080b40181f040104020251c802c2585c15616c1900f2ac174291e,0x21c0083d01a0304500a1d02184282f1080b40181f0401040202507602c2585c15616c1900f0e81cc661e,0x9ce006730dc01a0327280a1d25b8b6ce405e8e816ce303f3891c80447002e7085c2d816c630060e81cc661f] i)) else (if i<112 then (if i<104 then tableWord #[0x41a00d018002740e906674c8a02722607c18a3b0080144000b00e0dc2e01e0b6044b5161004024041e,0x281d02a024846b5009ff3fa7ecfc9f73ea7ccf89ef3da7acf49e73ca78cf09df3ba76cec9d73aa749d,0x144287d0ea1b43285d0aa1342283d06a0a5fa820e,0x145c4104911345919a32a2b45289888a248f2888e,0x14681415e47d4668c22a20c580af91247a394650e,0x14c297d2ea5b4b295d2aa534a293d26a4b49291d22a434828fd1ea3b4728d96,0x53f47f4fa9ed3ca774ea9cd38a6f4da9ad34a674ca9890,0xa900a2a3a3f06b51aa2d44a8750aa08afa80394650f] i else tableWord #[0x153041049a96226a55492ba570408af1108f0650e,0x54e06808800240a9a0491a0330540b80e0240520580701500a0500c83900e45cb5018004024041c,0xaae50c0024002f55854555aa8072a9942aa55440b00e02a014a08193fc01c8b90200d540a013f00553c041f,0x565ac820824a49112922b1d62ac358123d5f48d57840d5d48b572add5a48890c44559ab0909209c,0x2b00046e00d0185c0050e92dc5b6b5a4e4745beb501f0588e6b4a4d0095a2b391147002eb305c2d816c6300649892d2523,0x3ac1403606a5c4268d01180e8750b00604648c0e,0x1d60a2ba17949e232b98cdae55c6b856fadd5b6b60f,0x1f60d81ad79af01202503a1f44cc2b830aef5daba8f] i) else (if i<120 then tableWord #[0x1d646c4857e49f5f4770cd1da46abe0afaf75e8760f,0x16041403606a136c008cafe3a85803047a4648c0e,0x2c700101a030b810401437ac6d8cb165bec502cb1293402588b0e44405d8627761463584b076089c9d,0x516451f05809b6402503a1222cc2b83023815ac78f,0x5c117170038dbfb7c1bededbc32c654dddbbb756e6dc5b7b6d6d6da5b3b656c6d85afb5c6e2d6dacb576aad4da836f69ed35a5b486d6d186db45684d9da0b3e6cacf59db3966ecd599b3165ecb595b2964ec93c,0x5600083401a030b800a1d25b8b6a4e2285bc8981fb888ec025c310002ee105c2d816c6300649892d251e,0x2e60a61361c4528701b41bee5dcab937205e5c71843f06c09812e304520c017e28c510a10dc2804f8be12c1f05d89eb8c2f43686c12a27435a080d41ec2c89cb8a1a4340670cc1943235,0x21c0083d01a0304500a1d02184282f1080b40181f040104020251c802c2585c15616c1900f0e81cc661e] i else (if i<128 then tableWord #[0x15319e0880015202e22c671512a00701214f02c0380a8050280641c80703604403018004024041c,0x5019e0880004002e22c6702a05c0701202902c0380a8050280641c80703604403018004024041c,0xb48cf0444540b88b19c5a0b39660485940b00e02a0140a0191be01cb216303604403018004024b11d,0x25019e0880004002e22c6702a05c0701202902c0380a8050280641c80722e04403018004024041c,0x3bc8d92012035c8f91e1dc3347691a15e474760e,0x3bc1403606b734ba0d01180e8750b00605ccb90e,0x3bee792012035c8f91e1dc33476dce15e474760e,0x1f60d81a8720901281d0fa26615c185d0450414ad8f] i else tableWord #[0x6d8a61361c4528701b41bc4d0d90fa2645e0c31843f06c09812e304520c017e28c510a10dc2804f8be12c1f05d89e1742f43686c12a274358b90d41ec2c89c0f41a4340670cc1943235,0x4c07431844000248458c50fe1f82185a09e084620a70c43f87e8770c2108860c703c2d4088b4004024041f,0x500d81a85809a1202503a1222cc2b830238158300f,0x20824a4911292123a4610291522243110909208e,0x50650c985809a1202503a1222ccc818f238158300f,0x250ba40880004002e22c748330540b80e5d10520580701500a0500c83900e45c03018004024041c] i))))))
def orderGroups : Nat → Nat := (fun i => (if i<40 then (if i<16 then (if i<8 then tableWord #[0x32b2996371644a260408102046,0x39b978f6f5ef2e6deb675f1ed9d78f4fc2a4a19895938962615852514a463933251a160c52010084484420107,0x39f6b674f2ef6de6df56cac38cc2c1a599936559433529230c0a063a010484442010087,0x32b2996371a591260408102046,0xe749626d53c7810245085,0xe34cb158e34b220408102046,0x38d32c6caa56954cd1cc810205085,0xd6c89a653187811204085] i else tableWord #[0x38d32c5958e34b260408102046,0xf9fdaf67d3f2fbcee7b7eb79bd6f3dbf2f9bd6edb76dbaae8e9f5bd67d7e5f57b5dd6f57d3f3f47f83c2f07a4e8783d0f25c6713b92e1b62d1b26c5b0eb1aa2a3a4e8aa1a65966358a60c6959964d8759d5a5655352d3d4dd1b394d92d4a92307d16c2b03b0c06c0a8282906218460881180509414951944cc128491220841945910c350a4230300a019d801002004108411020040089,0xcb1b258dc6554ca18b811204085,0xf97e3f6fd7ef3bbe9f9dbf6e7b3abe79dbd5f97d5ed775bd5f4fcfe1fd7f0bc1e8f98e4f89e16e5b66d5b0eb9a729aa19c36656558d5b55d3c4ed27474c62f07d19c0e7b80b06a1a4688a128260542505234611342505260651645510c390300a0198801002004108411020040089,0x3cef37cbf1fb7ebf7bd3efcbeeefa767d9ddfd7ddcf1f92e1783d2f33caf07b2eb3aaea7a32789ce6b9664d91e398d62d71db569d8d5e5733e4f339cad1e8761d44e0b81c9301a0e4890e308a62384605615434c523424c32c4a528c891c87118c4a124461142a098180500c7e0040481108410882104008010a,0x34aa58dc696449260408102046,0x32c6ca658dc58a260408102046,0xf3bcdf2fc7eefb7e3f7ade773dbf5bbf2f7b76cfaf67b7f1fa7e5f67cdee7adde76dcf6f97e7b8be1f4ad2743ccb31c4eccb1eb4ace95a367399e4b8e635729c9719c36e9b46c5a364d8e5e1725a95a539363d0f23c4e638cd634cce32ca9294990b01cc702a128390e30846098158a605485093048912418c630cb0288a124891224851c0621484a0a024060140322801002088110820040080109] i) else (if i<24 then tableWord #[0xf3fb6ed7b3e9f97def6fcdefcbe6f7bb6ddaf67d7f1fb759d56dd9e5f9573f59e1b85e0f4bccf27b32c9b1eb4ac6a5a568d9e6739b6678d5cb6cd9461d785ad5a54d4e51d163e4f3334b5158550725c0a84a064890e31896096054850941489214490a418c930cb12146918c521444a1184506014031f801002044210421040080109,0x39b978f6b675f2ef6de6df56ce8b878fc2c1a4a19895938964615955433834312c221c160a56010480504420087,0x3978f6f5ef2ee9e75f59c38bc2c1a39893898565595543390c0a063e010484442010087,0x3b3ab9f6f5f3af2eeb5d5b874cc8c6c3a8a39893898564514a312519140c46050080402010087,0x3b39f6f5f3aeae6ceadf1e5d5b574ec4c3a392918a86655855493831290c3e010484402010087,0x3b3a7975b574f371eeae6ceb6ae6e5df1e5d5b9755ced6c4c1a8a19291898583686454514c4638312a19151356010080442010087,0x39f6b674f2ef6deae6df56c38cc2c1a5a299936559433529230c0a063e010484442010087,0x3b3af975b574f371eeae6ceb66e5df1e5d5b95cf4ed5c4c2a8a192918985836854514638312c2a19151352010080442010087] i else (if i<32 then tableWord #[0x3d3c7b7ab8f572ef2e6dabaadd579756d5d3cf47d4e0c1b0aca28954514d4a4334291c19160e0b4a010080403024087,0x39b978f775eeae6ceae9e6df5e99d78ed0c4a2a199938564615854514c46392523150a4a010084442010087,0x3b7ab8f5b574f2f1ef2ae65f1e5d5acf90c4c2a8908983686154514538342c2a12064601008040201008048,0x32c6c96371a589260408102046,0xd32b2a963756389814202045,0xcacaa68dc655220408102046,0xcb1b6b753187811244085,0x3aba78f776f5b1ef2e6d6b6ae5df1e9e5b9795cf4cd5c2a8a199948583685a54514638312c221c15134e010080604410087] i else tableWord #[0x3cbc7b7af4ef6ce99cd79756d5d3cd87d0e0c1b0a8a4a2918952514d4b31291d130646010080442410087,0x3cbb3aba78f736b372efaf6ceadd9d5cdb5ad9d5cdd5c8a4a2a1988c8a896254524543343129164601008040201008048,0x3b3af975b574f371eeae6ceb66e5df1e5d5b9755ced5c4c2a8a192918985836854514638312a241915130c56010080442010087,0x39b978f6f5ef2e6deb675f1ed9d78f4fc2c1a4a19895938962615852514a463933251a160c56010084484420107,0xd32b2996371958d2cb810244085,0xd32aa68dc655220408102046,0xd33aa6719547811204085,0x3d7f3fb7db76bd9f3ace72fc6efcbe6f5bb6ddaf67d8edfb5f16f5793e3f58e1f46d0f27c4f0bb56cdad669996478e22d865d372db35ad4c51d3846916438f91b41c7302a1644906258460980d8260542505224851242906344c92c4831a44510c2306014031c801002044108410020040089] i))) else (if i<64 then (if i<48 then tableWord #[0x3978f6f5ef2ee9e75f5dc78bc1a3989389856559555339331a160c3e010484484420107,0x3af976f1ef2e6deb5f1ed595538f478fc2a4a193898568615852514a443933251a16150c52010084484420107,0x3d5f4fc7eef97df379ddf5dd2f3dbeee5b5eada9e7d8b9ef75cf72fd6e4f54d4745d0f38ccf19c56d3aa6a3a16799ce659562a89a0c715c36ad87595635253949d0d3ace52ecad29c971d46d19c3d0dc2eab10c06819462288608811835052344509414c12a4a324c8519463124390cc2a09815031c801002044108821044080109,0x3978f776f1ef2e6deb5ed9cf438dc5c3a4a19891896359393325150c0a0642010484442010087,0xf3bcdf2fc7edfafdef6fbf2f9bdecfaf67d7f1fb679765d55e5753e3f47e6385e0f4bccb31caf27c4ec7ad2b1a9e95a36789ce678e6358b5ca725c36cdab631785c9715ad5a5654c519454e9344b8f93cccb2d47a1d8751384d0730c0a84a06438c22588e118258152142505304a921410c32c4a3224851c87118c4a1244611429098180500c8a0040081108410882104008010a,0x3978f6f1ef2e6deb675f1ed595538f4790c2a4a198938985615852514a443933251a16150c52010084484420107,0x3b3ab9f73675736dad6ceba75e9e5cdad6ced2c5a4a2948c86686358514932312a193e010480402010087,0x39b978f6b675f2ef6de6df59d6cf8ec2c1a4a19895938964615955433834312c261c160a56010480504420087] i else (if i<56 then tableWord #[0x3b39f6b5f3b2ef2eed6b5e9e5cdacec4c3a4a394938a866261524a383129250c460900844020106,0x3cbc7b7af774f18f8f4ecdcbc7cde0d1c9c4c232312d2b1d130632010080442410087,0xd73aa974b187811244085,0x39b978f6b674f2f1ef2eed6b69e75f1e9d9b9793c2a4a398918985646258524a464138322a26140c52010088402010047,0x3cbc7b7aef6ceb9cd79756d5d3cf87cfe0b1a9a4a252514d4b2c1d130636010080442410087,0xcb1b2996375b189811244085,0x34c6aa637562c8810244085,0xcb1b2a9a58dc6554cb811204085] i else tableWord #[0x3cef37cbf1fb6ed7b3ebf97def77d3efcbe6f7bb6ddb3ebd9f5fc7edee779cf6dd7e6f86e1783d2f47ccb31c4ec9b1eb4ac6a5a568d9e2759ce4d8e5cc72db26c5ab64d875e1725c56a58d5a54d4e4e9363e0f23c4e938cd934ccd198560b01cc702a1281916438c2118258260548509414c1224490a418c930cb028491214701886114851128460a024060140324801002044210420040080109,0x3cfed7b3e9f97df77bdbf57cdefcbe6f5bb6ddaf6b77edb73f41e5786e1783d374bd1f27c5713b36b1a9695a1e789b6598d5cb6cd875ad5954cf92d4550701a0580e7f05c0e84a06498961160d4950d23444c92c4851a45111418050120300a0198801012044108410020040089,0x3b3af975b574f371eeae6ceb66e5df1e5d5b95cf4ed5c4c2a8a19291898583686454514638312c2a19151356010080442010087,0x39b978f6f5ef2e6dad6ceb675f1ed9d78f4dd2c2c1a4a1989592896358534a463933251a160c4e010084484420107,0x39b978f6b674f2f1ef2e6deb6766df1e9d9b978f94c2c1a4a1989389856458524a4638322c1a164a010080482010047,0xf5fbaee7b3eaf9bdf777ceefdaee5b879ee7b5eb79dcf6edaf5bc7b17c3f6392e4783d5739cced5ae6939d65994e1a85a0c71daa6a5a364d8b5b5674acec3a4e5334ad1e45d15c4b0f43b03a4c46919463184a0881182605454a523314a82848919455124430e4130300a0199801012004108411020040089,0x39f6b674f2ef6de6df1e5d5b574ac38fc2c1a59993655851493529230c0a063e050084442010087,0x3af9f6ed6ce765df1e5d5b574f4dc38fc3a39389856965585135190c0a063a050084442010087] i)) else (if i<72 then tableWord #[0x3bb978f6b675f2ef2e6dad6ceb69e766df1e9d978f95c2c1a4a1989492898583646258564a3834322c1c1a15135e010080504820047,0xf5bcfedbb5ecfa7e5f7bdbf57cdefcbe6f7bb6ddaf67d7f1fb755b76797e3f59e1b85e0f4bd1b33c9eccb26c7ad2b1a9695a36799ce6d99e3572db3651875e16b5695353947458f93cccd2d4561541c9b02a1281922438c625825826054850941489214490a418c930cb12146918c521444a11845060140320801002044210421040080109,0x3978f6f371ee6ceae75f1e5d9d5cdb4f4ecdc393c3a1998564615851393325150c0a063e050084442010087,0x39b978f776f1eee9df1e5b4d45838ec5c3a3996461583831292514120c0a0642050084402010087,0x3e3dbc797736b573ad6bab6ae9e7a3de9e5cd2c4a4a2a1948c8a8570585251312a2623094601008040201008048,0xeb4c5638b1c7810284045,0x34ceca65699588850204085,0xeb5bab75b587230a248a161449130a2461433e0408102046] i else (if i<80 then tableWord #[0x38d32c6ca5634b260408102046,0xd698dc65234b189850244085,0xc6cae575b387811289105,0x3b7ab8f5b574f2f1ef2ae65f1e5d5ad74f91c5c2a89089836861545138342a1c12064201008040201008048,0x39edd77633a72dcd8e2b0d1931213262a12a3325498c14190808088808086,0x3978f6f57371ee6ceae75f1ddb5ad74f4ec392c3a19985646354534945332925150c0a0646050084442010087,0x34c6caa58da64e260408102046,0x34c6caa695a4c9260408102046] i else tableWord #[0xd73b5a64b187850244085,0x39f6b674f2ef66df5dd6cac38cc2c1a59983655952352923130c0a063e050084442010087,0xf3fbbedbb5e9f97ddf6dbf2fabe6f3baedb9ee5d8f5fc7e9f97bdde7755b4f4fb6b8be1f47ccb31c9723c4ecab26c3ac6a3a4e739364b8e2358a619731ca725c6715aa699986518e6356659554549515354b4d12d464f83acda364b2158551381ccf03a06438c2218460981588611445094149110424c8308c12889022862184521444a1244611428060140322805002004210420040080109,0x3978f776f1eee9df1e5ddb4f438dc5c3a3996461585149393325150c0a0642050084442010087,0x3b7af5b574f1eeae6ce6e5df55cecb8fc5c3a8a19291896861554938312c2a1913064a010480442010087,0xdacaa5693247812204045] i)))))
def ordered (v : Nat) : OrderPage := orderPage plus minus 11 orderBank (v % 16) ((v >>> 4)%8) ((v >>> 7)%17592186044416) (orderClauses ((v >>> 51)%256)) (orderGroups (v >>> 59))
def ruleBank : Nat → Nat := (fun i => (((fun i => tableWord #[0x45b9e8281954e981880a900112408a015a97a880a920bd211818406f4882021002e0808900d6e4a0406500120408a000057842062043dc60808504e808a0a520be0118184cae81040650009e10818806f8082021,0x53a4e6202a490f8186061043e0608084004810226000160008a00002784204253a4e62021c82f80460410011c408901c2f70500818224e4382154e939880650008ee0218a4ae81d60a5b61e0e482a40057102240,0x3808020835ba08101960a17916085b091c14020400280802480015c008980001780a624001604089000027b82062] i)) (i/16) >>> (42*(i%16))) % 4398046511104)
def programs : Nat → Nat := (variableSlot (fun i => tablePair #[(0x1bd19016913c1150f30c509e07704c020000,0x13a124439c0780d34a78ad3912443080784710c78ad08218402c0388fbc13afc6da65801ae32caa82b70443830807d04430b08a790432005)] i))
def panel := readPanel plus minus 6 4 ruleBank programs
def data17 : Nat → Nat := (fun i => tableWord #[0x7ff,0x1ca942208e507] i)
def data16 : Nat → Nat := (fun i => (if i<8 then tableWord #[0xfff420,0x4ca55143a6a465c18c3090c,0xfff040,0x2e6aa98cf8606,0xfff440,0x13141088d1fb9aaa65918f0060e,0xfff060,0x5cd550e8605] i else (if i<16 then tableWord #[0xfff460,0x265250d5cd5530639194e860d,0xfff500,0x4ca4a1d395246535831860c,0xfff520,0x5069085b8508e5c18e40c0c,0xfff501,0x2a48c18f29a06] i else tableWord #[0xfff528,0x2652a8e863850d48c18f2890d] i)))
def data15 : Nat → Nat := bookData 2 4 3 (fun i => (((fun i => tableWord #[0x5208c110294501a0018210040] i)) (i/16) >>> (11*(i%16))) % 2048) (fun i => (((fun i => tableWord #[0x3fffeffbfffff7ffd7fd] i)) (i/16) >>> (13*(i%16))) % 8192) (fun i => (((fun i => tableWord #[0xa434e9051a014620512c2969444a510e25b2856ca35b0856c235b1882869011a00461580,0xa56d295b3a56de85b7a405e95b2a16ca85b68d6da8016a16c295b1a16c625b1a42869153,0xa474281d09074041d0a034291d1a07469151a054641511054631510c54435d1097463051,0xa434a80d2a515a91d6a075a41d6a175a35d60d75a80d6ac35a9056a015a40568c15a9450,0xa175e9157a055e4157ac55cb157a435e80d7ac35e9057a015e9452a454a8152905484152,0xad162b1d8ac5628158ac36280d8a574e91d3ac74cb1d3ac54cb153ac34e9053a515e95d7,0x2b055] i)) (i/16) >>> (18*(i%16))) % 262144) (variableSlot (fun i => tablePair #[(0x47542d3e73713032d329e2562081da18c14e0e90aa065028000,0x14d52233bc1c612021138886f071848780844ecd4cd3521a12bb3a49c1c634021d3b35314a4315104f02ff18a8086e47071f28482eb23838f94241a9153239427838c0422609dc071a12161d060998a4741824166091e0b18e31f0a06099889ab8c7c18241e826d191ca420bc1c6150c1219a72397838e18241e22591cbc1c6041211ac8e5e0e3020907e3091f0604),(0x95095095095095095095095095095095095095095095095000,0x1b66a60e17a25d0c9c5401c8e0e509e3030012),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0x0,0x0)] i))
def data14 : Nat → Nat := bookData 3 4 5 (fun i => (((fun i => tableWord #[0x294280c2b0608d68405854a22583046b0408560814a140220a10521500a4084140108220210522500] i)) (i/16) >>> (23*(i%16))) % 8388608) (fun i => (((fun i => tableWord #[0xdfffffebbff6fffbf7efeffeb7fbdfdf7fd9ffe6ff9ff7ffffff7cff,0xfbfefff] i)) (i/16) >>> (14*(i%16))) % 16384) (fun i => (((fun i => tableWord #[0x31635906201062090424104248c4240c424904238c423904228c422a0821a06219062188211a5000,0xa44899048988289a5858a185891858a4678a067890678a4667a066790667106670d8673165131646,0x104e28c4e20c4e290211ac06a316d6ac6c6302b6880a6b16503165088090a5004a5859a185991859,0xa02f8902f8906f7106f7904fb104fb90615106158c015904e3104e38c4e30c4e3306e2304e2904e2,0x105168c5160c516b0700ac6f0900e0a50f9a48f9a08f9a42f9902f9904fc104fca50f8a48f8a08f8,0x8c01a0c01a8801a0801a9051d1051d8c11d0c11d8811d0811db07162c716b05162c51690516] i)) (i/16) >>> (20*(i%16))) % 1048576) (variableSlot (fun i => tablePair #[(0x93093093093093093093093093093093093093093093055000,0x49e9007f1854000d90878391e5f1824080009),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0x0,0x0)] i))
def data13 : Nat → Nat := (fun i => (if i<8 then tableWord #[0x7ffd483441440420,0x0,0x7cff083528522500,0x0,0x7cff483528522500,0x0,0x7cff5a3528522500,0x0] i else tableWord #[0x7cfa440528522500,0x0,0x7cfe480528522500,0x0,0x7cfd1a1528522500,0x0,0x74ff563528522500,0x0] i))
def levels : Nat → Packing
  | 13 => (8,4,6,0,0,0,0,data13)
  | 14 => (95,3,6,0,0,0,0,data14)
  | 15 => (97,2,6,0,0,0,0,data15)
  | 16 => (9,1,6,0,0,0,0,data16)
  | 17 => (1,0,6,0,0,0,0,data17)
  | _ => (0,0,0,0,0,0,0,fun _ => 0)
def index : Nat → Nat → Option (Nat × Nat)
  | 14 => fun h => smallSlot h 4 16 4 2 (fun i => (((fun i => tableWord #[0x0] i)) (i/16) >>> (1*(i%16))) % 2) (fun i => (((fun i => tableWord #[0x6180000c1b200291e8c2f088c00003990947] i)) (i/16) >>> (9*(i%16))) % 512)
  | 15 => fun h => smallSlot h 47 170 7 3 (fun i => (((fun i => tableWord #[0xc01c08600164518501a407,0x201000002003019cc0240301,0x441801010023012001c1] i)) (i/16) >>> (6*(i%16))) % 64) (fun i => (((fun i => (if i<8 then tableWord #[0x292106095c02b817816e1ac85885a120788305272be118000822,0x602a04409a08b21880a7089c50094800388fc4a000609b07404e,0x713e2580000a5800000154ce0f800000000000000030a7037,0xd6bb45d046000e1db338849adda1c303c452004,0x403517f95f00100050f400184b45aa1158a29138595020001042,0xe602b04e409a2ce13345841300010080aa00000b405f836448,0x41936b48ae812012dca48280218ee601e818c3ce14117706741a,0x66990821b940be1cb0fee48419020133dabc116821e3490218ad] i else tableWord #[0x92b42a3093c8839630f90bdc0362d1229bbb82c01a0000000000,0x40f7b7386d00e40ee35c0b9030a1774e210d02ac6e9034000054,0x382a0564a68003dac000616f57f86a000] i))) (i/16) >>> (13*(i%16))) % 8192)
  | 16 => fun h => smallSlot h 71 254 7 3 (fun i => (((fun i => tableWord #[0x8c0c0001a9410704083000001587,0x630021060c21718080800408001,0x1248cb5000c20024181040000004,0xd04001062a743080c44000,0x84000018002] i)) (i/16) >>> (7*(i%16))) % 128) (fun i => (((fun i => (if i<8 then tableWord #[0x160464986310e0fb236028d4fea038ac0a4c08651191b27403b,0x86600c0001456218a8de0ba00db10f50f8078440a29c9703c247,0x194faf3cb38b2b1830c9852000c86d16f151842a4b800102e000,0xa83e13d0a105a2850000000000267521213281c613e4cd05ec11,0x5936134000000298496f826c20e9c7abeb6393741158968b9836,0xf6165a800314b23c000513000122c00060388a8d3c,0x65f101300b935000312f14912900070dc9ac03521e22df1ba446,0x7150001a9c910204800164e000e1ef8282886b201f0002816117] i else tableWord #[0x80810b8070000d8f924402a0004a51048001c1b0b08002046000,0x400a1068666615924c49aa402138ad146131c020003097927853,0x60b54d2d6fa32b17d8539bc00068fb310000000d5e84f400042d,0xd5f610c0014cb054a074001ab082f000324c000000709b081459,0x6146ac603540f8037ca361494281c800243e85fe1f8448a176ac,0xc9380d3074c61c2538f408b532c1531800000000005061968ccf,0x28ac0af892d2f694706527384ee2c64b3959024023800280f80a,0x1aa455b1252270182ae58cb6faa2c0b102bb460c39448] i))) (i/16) >>> (13*(i%16))) % 8192)
  | 17 => fun h => smallSlot h 9 34 4 3 (fun i => (((fun i => tableWord #[0xb00353023] i)) (i/16) >>> (4*(i%16))) % 16) (fun i => (((fun i => tableWord #[0xf1f060036139e85023870000064e28412a134ca4,0x104814093280cb3c940034800b9ba664b0900000,0xc9e46] i)) (i/16) >>> (10*(i%16))) % 1024)
  | _ => fun _ => none
def book : Forest := ⟨6143,17,samples,cols,[[],[66,165,118],[32,67,117,152],[32,48,64,165,101,118,152],[48,101,167],[48,66,117,166],[64,32,50,101,117,165,152],[64,50,166,152]],levels,index⟩
theorem geometry : graphValid book (boundsBefore entries) = true := by decide +kernel
set_option maxRecDepth 16000 in
theorem row17_0 : CutRow book 17 0 1 := bandCut 11 false (by decide +kernel)
theorem band17 : CutRow book 17 0 1 := row17_0
set_option maxRecDepth 16000 in
theorem row16_0 : CutRow book 16 0 9 := bandCut 12 false (by decide +kernel)
theorem band16 : CutRow book 16 0 9 := row16_0
set_option maxRecDepth 16000 in
theorem row15_0 : CutRow book 15 0 1 := bandCut 11 false (by decide +kernel)
set_option maxRecDepth 16000 in
theorem row15_1 : CutRow book 15 1 11 := bandCut 12 false (by decide +kernel)
set_option maxRecDepth 16000 in
theorem row15_12 : CutRow book 15 12 5 := bandCut 13 false (by decide +kernel)
set_option maxRecDepth 16000 in
theorem row15_17 : CutRow book 15 17 15 := orderCut (pages:=fun j => ordered (((fun i => (if i<8 then tableWord #[0x587054bb2a19085a,0x60804c3b2a19085a,0x789854c3aa19085a,0x80a054c3b219085a,0x1396054c3b219085a,0x151885c3b2a19085a,0x161b854c32a19085a,0x61c84c3b2a19085a] i else tableWord #[0x1c26054bb2a19085a,0x1ca6854c3b219085a,0x1ea8854bb2a19085a,0x20ac854c3b219085a,0x82d854c3b219085a,0x83b054c3b219085a,0x840054c3b219085a] i))) j)) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 16000 in
theorem row15_32 : CutRow book 15 32 64 := orderCut (pages:=fun j => ordered (((fun i => (if i<32 then (if i<16 then (if i<8 then tableWord #[0x101000543b219048,0x107800543b219048,0x107800543b219048,0x107800543b219048,0x88a8005432a19048,0x107800543b219048,0x90b00053b2a19048,0x98b80043b2a19048] i else tableWord #[0xa0c00043b2a19048,0xa8c80054c3a19048,0xb0d000543b219048,0xb9680054c3a19048,0xb8d80054c3a19048,0xf9180054c3a10848,0xc8e80054c2a19048,0xd0f00054c3a19048] i) else (if i<24 then tableWord #[0x91700053b2a19048,0x141780043b2a190c8,0x14980004c3b2190c8,0x15990004c3b2190c8,0x14998004c3b2190c8,0x149a0004c3b2190c8,0x159a8004c3b219048,0x149b0004c3b2190c8] i else tableWord #[0x149c0004c3b2190c8,0x149d0004c3b2190c8,0x169d8004c3aa190c8,0x171e0004c3aa19048,0x179e8004c32a18848,0x181f0004bb2a19048,0xb9680054c3a19048,0x1d2700054c3a19048] i)) else (if i<48 then (if i<40 then tableWord #[0xb8d80054c3a19048,0x19a200054bb218848,0xba380054c3a19048,0x1da78004c32a19048,0x91700053b2a19048,0x1e280004c3b2190c8,0x1f29000543b2190c8,0x129800543b219048] i else tableWord #[0x12a000543b219048,0x129800543b219048,0x1f29000543b2190c8,0x1f2a800543b2190c8,0x92b00053b2a19048,0x1fab800543b2190c8,0x202c0005432a18848,0x12d000543b219048] i) else (if i<56 then tableWord #[0x1f29000543b2190c8,0x92e00053b2a19048,0x15ae8004c3b2190c8,0x15af0004c3b219048,0x21b000054bb219048,0x15af0004c3b219048,0x15af0004c3b219048,0x15af0004c3b219048] i else tableWord #[0x25b500054c3a19048,0x15bb8004c3b219048,0x2a3c00054c3a19048,0x2a3c80054c3a19048,0x2a3d00054c3a19048,0x2a3c80054c3a19048,0x2a3c80054c3a19048,0x2a3d80054c3a19048] i))))) j)) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 16000 in
theorem row15_96 : CutRow book 15 96 1 := orderCut (pages:=fun j => ordered (((fun i => tableWord #[0x94080053b2a19048] i)) j)) (by decide +kernel) (by decide +kernel)
theorem combine15_0_12 : CutRow book 15 0 12 := @joinRow book 15 0 1 11 row15_0 row15_1
theorem combine15_12_20 : CutRow book 15 12 20 := @joinRow book 15 12 5 15 row15_12 row15_17
theorem combine15_32_65 : CutRow book 15 32 65 := @joinRow book 15 32 64 1 row15_32 row15_96
theorem combine15_0_32 : CutRow book 15 0 32 := @joinRow book 15 0 12 20 combine15_0_12 combine15_12_20
theorem combine15_0_97 : CutRow book 15 0 97 := @joinRow book 15 0 32 65 combine15_0_32 combine15_32_65
theorem band15 : CutRow book 15 0 97 := combine15_0_97
set_option maxRecDepth 16000 in
theorem row14_0 : CutRow book 14 0 1 := bandCut 12 false (by decide +kernel)
set_option maxRecDepth 16000 in
theorem row14_1 : CutRow book 14 1 1 := bandCut 13 false (by decide +kernel)
set_option maxRecDepth 16000 in
theorem row14_2 : CutRow book 14 2 13 := colorCut (ds:=fun j => panel (((fun i => (if i<8 then tableWord #[0x872543,0x726544,0x7263545,0x63540,0x7263541,0x63540,0x7263541,0x7263542] i else tableWord #[0x63540,0x7263542,0x7263541,0x63546,0x73547] i))) j)) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 16000 in
theorem row14_15 : CutRow book 14 15 2 := orderCut (pages:=fun j => ordered (((fun i => tableWord #[0x485854c3b299085a,0x293a054c3aa19085a] i)) j)) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 16000 in
theorem row14_17 : CutRow book 14 17 27 := orderCut (pages:=fun j => ordered (((fun i => (if i<16 then (if i<8 then tableWord #[0x808004c32a190c8,0xb8d8004c3b190848,0xb8d8004c3b190848,0xc0e00054c3b18848,0xc8e8004c3a190848,0xd0f0004c3b190848,0xf918004c3b190848,0x101200054c3a99048] i else tableWord #[0x109280054c3a99048,0xb9300054c3a19048,0x111380054c3a19048,0x11940004c32a19048,0x18a080054c2a19048,0x19a20004c32990848,0x1a22800543aa19048,0xba300054c3a19048] i) else (if i<24 then tableWord #[0xba380054c3a19048,0x11a40004c32a19048,0x212f8005d3b219048,0x22308005d3aa190c8,0xbb480054c3a19048,0xb8d80054c3a19048,0x263580004b2a190c7,0x26b600053b2990848] i else tableWord #[0x28b900054bb219048,0x29ba8005c3b219048,0xbc28004c3b190848] i)))) j)) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 16000 in
theorem row14_44 : CutRow book 14 44 51 := orderCut (pages:=fun j => ordered (((fun i => (if i<24 then (if i<8 then tableWord #[0x3b2990b6,0x181800004b2190b6,0x202000005caa18b6,0x181800004b2190b6,0x282800005cb21936,0x183000004b2190b6,0x181800004b2190b6,0x3038000054ba18b6] i else (if i<16 then tableWord #[0x3840000053aa1936,0x3038000054ba18b6,0x4048000054b21936,0x5000004b2990b6,0x6000004b2990b6,0x506800004b218836,0x68880000543a1936,0x7090000053b21836] i else tableWord #[0xd8f8000054c21936,0xe100000054c21036,0xe908000054b21036,0xf110000054321036,0x12148000054c10836,0x129500000542a1036,0x131580000532a1036,0x19f8000054c21836] i)) else (if i<40 then (if i<32 then tableWord #[0x200000054b21836,0xf21000004b2a1836,0x1921800004c321836,0x1aa4800004c318836,0x1b25000004c321836,0x1ba5800004b2a1836,0x22b10000054c29936,0x233180000432a1836] i else tableWord #[0x1932000004c321836,0x1236800005bb21936,0x2737000005cb21936,0x1236800005bb21936,0x37800004bb21936,0x27b8000005cba1936,0x2838800005bb21936,0x1236800005bb21936] i) else (if i<48 then tableWord #[0x39800004bb21936,0x2abe000005cba1936,0x123e800005bb21936,0x2abe000005cba1936,0x2abf000005cba1936,0x2abe000005cba1936,0x73f800004bb21836,0x41000004b2990b6] i else tableWord #[0xf418000032a190b6,0x41000004b2990b6,0x42000004b2990b6] i))))) j)) (by decide +kernel) (by decide +kernel)
theorem combine14_0_2 : CutRow book 14 0 2 := @joinRow book 14 0 1 1 row14_0 row14_1
theorem combine14_2_15 : CutRow book 14 2 15 := @joinRow book 14 2 13 2 row14_2 row14_15
theorem combine14_17_78 : CutRow book 14 17 78 := @joinRow book 14 17 27 51 row14_17 row14_44
theorem combine14_0_17 : CutRow book 14 0 17 := @joinRow book 14 0 2 15 combine14_0_2 combine14_2_15
theorem combine14_0_95 : CutRow book 14 0 95 := @joinRow book 14 0 17 78 combine14_0_17 combine14_17_78
theorem band14 : CutRow book 14 0 95 := combine14_0_95
set_option maxRecDepth 16000 in
theorem row13_0 : CutRow book 13 0 1 := mixedCut (data:=fun j => treeData plus minus (((fun i => tableWord #[0x87b8c143] i)) j)) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 16000 in
theorem row13_1 : CutRow book 13 1 3 := colorCut (ds:=fun j => panel (((fun i => tableWord #[0xa063548,0xb73549,0xa06354a] i)) j)) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 16000 in
theorem row13_4 : CutRow book 13 4 1 := orderCut (pages:=fun j => ordered (((fun i => tableWord #[0x23b28000054c3a946] i)) j)) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 16000 in
theorem row13_5 : CutRow book 13 5 3 := orderCut (pages:=fun j => ordered (((fun i => tableWord #[0x2433000005cc290b6,0x24b38000054a99036,0x253400000532a1836] i)) j)) (by decide +kernel) (by decide +kernel)
theorem combine13_0_4 : CutRow book 13 0 4 := @joinRow book 13 0 1 3 row13_0 row13_1
theorem combine13_4_4 : CutRow book 13 4 4 := @joinRow book 13 4 1 3 row13_4 row13_5
theorem combine13_0_8 : CutRow book 13 0 8 := @joinRow book 13 0 4 4 combine13_0_4 combine13_4_4
theorem band13 : CutRow book 13 0 8 := combine13_0_8
theorem checked : mixedTables book 17 := by
  intro k hk
  interval_cases k
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact band13
  · exact band14
  · exact band15
  · exact band16
  · exact band17
end M4063_18
theorem m4063_18 : Face false 2047 18 :=
  mixedLower (g:=M4063_18.book) (i:=0) (hints:=4882524037)
    (before_sound M4063_18.entries M4063_18.prior) M4063_18.geometry M4063_18.checked
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem signedRoot : Impossible true graph 16 inputs.toFinset := by
  rw [show graph = targetOf B4063_17.book by decide +kernel]
  exact mixedRoot (g:=B4063_17.book) (top:=16) (i:=0) (before_sound B4063_17.entries B4063_17.prior)
    B4063_17.geometry B4063_17.checked (by decide) (by decide +kernel)
theorem monoRoot : Impossible false graph 17 inputs.toFinset := by
  rw [show graph = targetOf M4063_18.book by decide +kernel]
  exact mixedRoot (g:=M4063_18.book) (top:=17) (i:=0) (before_sound M4063_18.entries M4063_18.prior)
    M4063_18.geometry M4063_18.checked (by decide) (by decide +kernel)
end Engine

namespace Physical
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
def Ok (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2
theorem getD_snoc_ne {α : Type} (L : List α) (S d : α) (j : ℕ) (h : j ≠ L.length) :
    (L ++ [S]).getD j d = L.getD j d := by
  by_cases hj : j < L.length
  · exact List.getD_append _ _ _ _ hj
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]
theorem getD_snoc_eq {α : Type} (L : List α) (S d : α) : (L ++ [S]).getD L.length d = S := by
  simp
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
abbrev Stat : Type := Bool ⊕ ℕ
def Stat.val (w : List Bool) : Stat → Bool
  | Sum.inl c => c
  | Sum.inr j => w.getD j false
def Stat.Valid (m : ℕ) : Stat → Prop
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
    (hv : ∀ s ∈ ins, s.Valid w.length) :
    ((simplify op w.length ins).2).Valid (w.length + (simplify op w.length ins).1.toList.length) ∧
    ((simplify op w.length ins).2).val (wiresFrom (simplify op w.length ins).1.toList w)
      = op.eval (ins.map (Stat.val w)) := by
  rcases hop with rfl | rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [simplify, simpAnd, Stat.Valid, Stat.val, GateOp.eval]
    · cases a <;> simp_all [simplify, simpAnd, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
    · cases a <;> cases b <;> (try rename_i c e; cases c) <;> (try cases e) <;>
        simp_all [simplify, simpAnd, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
    · simp at hlen
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [simplify, simpOr, Stat.Valid, Stat.val, GateOp.eval]
    · cases a <;> simp_all [simplify, simpOr, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
    · cases a <;> cases b <;> (try rename_i c e; cases c) <;> (try cases e) <;>
        simp_all [simplify, simpOr, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
    · simp at hlen
  · rcases ins with _ | ⟨a, l⟩
    · simp [simplify, simpNot, Stat.Valid, Stat.val, GateOp.eval]
    · cases a <;> simp_all [simplify, simpNot, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
def elimStep (n : ℕ) (acc : List Stat × List Gate) (g : Gate) : List Stat × List Gate :=
  (acc.1 ++ [(simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).2],
    acc.2 ++ (simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1.toList)
def elim (n : ℕ) (gs : List Gate) (acc : List Stat × List Gate) : List Stat × List Gate :=
  gs.foldl (elimStep n) acc
theorem elim_getD (n k : ℕ) (d : Stat) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    k < acc.1.length → (elim n gs acc).1.getD k d = acc.1.getD k d := by
  induction gs with
  | nil => intro acc _; rfl
  | cons g gs ih =>
    intro acc hk
    have h3 : elim n (g :: gs) acc = elim n gs (elimStep n acc g) := rfl
    rw [h3, ih (elimStep n acc g) (by simp [elimStep]; omega)]
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
theorem Stat.valid_mono {m m' : ℕ} (h : m ≤ m') : ∀ s : Stat, s.Valid m → s.Valid m'
  | Sum.inl _, _ => trivial
  | Sum.inr _, hj => lt_of_lt_of_le hj h
theorem Stat.val_append (w t : List Bool) : ∀ s : Stat, s.Valid w.length →
    s.val (w ++ t) = s.val w
  | Sum.inl _, _ => rfl
  | Sum.inr _, hj => List.getD_append _ _ _ _ hj
def Inv (n : ℕ) (y : List Bool) (w : List Bool) (acc : List Stat × List Gate) : Prop :=
  acc.1.length = w.length ∧ ∀ i : ℕ,
    (acc.1.getD i (Sum.inl false)).Valid (n + acc.2.length) ∧
    (acc.1.getD i (Sum.inl false)).val (wiresFrom acc.2 y) = w.getD i false
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
    have hvals : ins.map (Stat.val w') = g.inputs.map fun i => w.getD i false := by
      rw [hins, List.map_map]
      apply List.map_congr_left
      intro a _
      exact (hi a).2
    have hnew : wiresFrom (acc.2 ++ r.1.toList) y = wiresFrom r.1.toList w' := by
      rw [wiresFrom_append]
    obtain ⟨t, ht, htl⟩ := wiresFrom_prefix r.1.toList w'
    refine ⟨by simp [elimStep, hl], ?_⟩
    intro i
    show ((acc.1 ++ [r.2]).getD i (Sum.inl false)).Valid (n + (acc.2 ++ r.1.toList).length) ∧
      ((acc.1 ++ [r.2]).getD i (Sum.inl false)).val (wiresFrom (acc.2 ++ r.1.toList) y) = _
    rw [hnew, List.length_append, ← Nat.add_assoc]
    by_cases hil : i = acc.1.length
    · subst hil
      rw [getD_snoc_eq, hl, getD_snoc_eq]
      exact ⟨hs.1, by rw [hs.2, hvals]⟩
    · rw [getD_snoc_ne _ _ _ _ hil, getD_snoc_ne _ _ _ _ (by omega)]
      refine ⟨Stat.valid_mono (by omega) _ (hi i).1, ?_⟩
      rw [ht, Stat.val_append _ _ _ (by rw [lw']; exact (hi i).1)]
      exact (hi i).2
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
theorem elim_split_getD (n : ℕ) (pre : List Gate) (g : Gate) (post : List Gate)
    (acc : List Stat × List Gate) (a : ℕ) (d : Stat) (h : a ≤ acc.1.length + pre.length) :
    (elim n (pre ++ g :: post) acc).1.getD a d = (elimStep n (elim n pre acc) g).1.getD a d := by
  rw [elim_append, elim_cons, elim_getD n a d post _ (by
    show a < ((elim n pre acc).1 ++ [_]).length
    rw [List.length_append, elim_fst_len, List.length_singleton]; omega)]
theorem elim_split_getD_lt (n : ℕ) (pre : List Gate) (g : Gate) (post : List Gate)
    (acc : List Stat × List Gate) (a : ℕ) (d : Stat) (h : a < acc.1.length + pre.length) :
    (elim n (pre ++ g :: post) acc).1.getD a d = (elim n pre acc).1.getD a d := by
  rw [elim_split_getD n pre g post acc a d (le_of_lt h)]
  show ((elim n pre acc).1 ++ [_]).getD a d = _
  exact getD_snoc_ne _ _ _ _ (by rw [elim_fst_len]; omega)
theorem elim_count (n : ℕ) (acc : List Stat × List Gate) : ∀ gs : List Gate,
    (∀ g ∈ gs, NOk g) → ∀ S : Finset ℕ,
    (∀ p ∈ S, ∃ g, gs[p]? = some g ∧ ∃ a ∈ g.inputs, a < acc.1.length + p ∧
        ∃ c, (elim n gs acc).1.getD a (Sum.inl false) = Sum.inl c) →
      (elim n gs acc).2.length + S.card ≤ acc.2.length + gs.length := by
  intro gs
  induction gs using List.reverseRecOn with
  | nil =>
    intro _ S hS
    have hE : S = ∅ := by
      apply Finset.eq_empty_of_forall_notMem
      intro p hp
      obtain ⟨g, hg, _⟩ := hS p hp
      simp at hg
    subst hE
    simp [elim]
  | append_singleton gs g ih =>
    intro hok S hS
    have hstep : elim n (gs ++ [g]) acc = elimStep n (elim n gs acc) g := by
      rw [elim_append]; rfl
    have hpre : ∀ (a : ℕ) (d : Stat), a < acc.1.length + gs.length →
        (elim n (gs ++ [g]) acc).1.getD a d = (elim n gs acc).1.getD a d :=
      fun a d h => elim_split_getD_lt n gs g [] acc a d h
    have hok' : ∀ g' ∈ gs, NOk g' := fun g' h => hok g' (List.mem_append_left _ h)
    have ih' := ih hok' (S.erase gs.length) (by
      intro p hp
      obtain ⟨hne, hpS⟩ := Finset.mem_erase.1 hp
      obtain ⟨g', hg', a, ha, hlt, c, hc⟩ := hS p hpS
      have hpl : p < gs.length := by
        obtain ⟨h1, _⟩ := List.getElem?_eq_some_iff.1 hg'
        rw [List.length_append, List.length_singleton] at h1
        omega
      rw [List.getElem?_append_left hpl] at hg'
      rw [hpre a _ (by omega)] at hc
      exact ⟨g', hg', a, ha, hlt, c, hc⟩)
    rw [hstep, List.length_append, List.length_singleton]
    by_cases hin : gs.length ∈ S
    · obtain ⟨g', hg', a, ha, hlt, c, hc⟩ := hS _ hin
      have hgg : g' = g := by
        rw [List.getElem?_concat_length] at hg'
        exact (Option.some.inj hg').symm
      subst hgg
      rw [hpre a _ hlt] at hc
      have h2 := elimStep_none n (elim n gs acc) g' (hok g' (by simp)) a ha c hc
      have hcard := Finset.card_erase_of_mem hin
      have hpos : 1 ≤ S.card := Finset.card_pos.2 ⟨_, hin⟩
      omega
    · have h2 : (elimStep n (elim n gs acc) g).2.length ≤ (elim n gs acc).2.length + 1 := by
        simp only [elimStep, List.length_append]
        have := toList_length_le (simplify g.op (n + (elim n gs acc).2.length)
          (g.inputs.map fun i => (elim n gs acc).1.getD i (Sum.inl false))).1
        omega
      rw [Finset.erase_eq_of_notMem hin] at ih'
      omega
def reads (pin : ℕ) (g : Gate) : Bool := (normGate g).inputs.contains pin
def restrict (bank : List (Option (Fin m))) (x : Fin m → Bool) : List Bool :=
  bank.map fun p => p.elim false x
def layout (bank : List (Option (Fin m))) : List Stat :=
  bank.map (fun p => p.elim (.inl false) (fun k => .inr k.val))
theorem eliminate_pin (bank : List (Option (Fin m))) (pin : ℕ) (C : Circuit)
    (fan : FanInTwo C) (absent : bank[pin]? = some none)
    (hasFalse : ∃ x : Fin m → Bool, C.eval (restrict bank x) = false) :
    ∃ D : Circuit, FanInTwo D ∧ D.size + C.gates.countP (reads pin) ≤ C.size ∧
      ∀ x : Fin m → Bool, D.eval (List.ofFn x) = C.eval (restrict bank x) := by
  let initial := layout bank
  let gs := C.gates.map normGate
  let acc := elim m gs (initial, [])
  let S := Finset.univ.filter (fun i : Fin C.gates.length => reads pin (C.gates.get i))
  have cardS : C.gates.countP (reads pin) = S.card := by
    simpa [S] using List.countP_ofFn (fun i : Fin C.gates.length => C.gates.get i) (reads pin)
  have normOk : ∀ g ∈ gs, NOk g := by
    intro g hg
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 hg
    exact normGate_nok _ (fan _ hg0)
  have hp : pin < bank.length := (List.getElem?_eq_some_iff.mp absent).1
  have constant : initial.getD pin (.inl false) = .inl false := by
    simp [initial, layout, List.getD_eq_getElem?_getD, absent]
  have penalty := elim_count m (initial, []) gs normOk (S.image Fin.val) (by
    intro k hk
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hk
    have hr := (Finset.mem_filter.mp hi).2
    have member : pin ∈ (normGate (C.gates.get i)).inputs := by simpa [reads] using hr
    refine ⟨normGate (C.gates.get i), ?_, pin, member, ?_, false, ?_⟩
    · simp [gs, i.isLt]
    · have len : initial.length = bank.length := by simp [initial,layout]
      change pin < initial.length + i.val
      omega
    · rw [elim_getD m pin _ gs _ (by simp [initial,layout,hp])]
      exact constant)
  have count : acc.2.length + C.gates.countP (reads pin) ≤ C.size := by
    rw [cardS]
    simpa [acc, gs, Circuit.size, Finset.card_image_of_injective S Fin.val_injective] using penalty
  have inv (x : Fin m → Bool) :
      Inv m (List.ofFn x) (wiresFrom gs (restrict bank x)) acc := by
    apply inv_elim _ _ (by simp) _ _ _ (fun g hg => (normOk g hg).1)
    refine ⟨by simp [initial,layout,restrict], ?_⟩
    intro k
    by_cases h : k < bank.length
    · have index := List.getElem?_eq_getElem h
      cases val : bank[k] with
      | none =>
        have eq : bank[k]? = some none := index.trans (congrArg some val)
        simp [initial,layout,restrict,Stat.Valid, Stat.val, List.getD_eq_getElem?_getD,eq,wiresFrom]
      | some i =>
        have eq : bank[k]? = some (some i) := index.trans (congrArg some val)
        simp [initial,layout,restrict,Stat.Valid, Stat.val, List.getD_eq_getElem?_getD,eq,
          wiresFrom,i.isLt]
    · have eq : bank[k]? = none := List.getElem?_eq_none (by omega)
      simp [initial,layout,restrict,Stat.Valid, Stat.val, List.getD_eq_getElem?_getD,eq,wiresFrom]
  have eval (x : Fin m → Bool) :
      (acc.1.getD C.output (.inl false)).val (wiresFrom acc.2 (List.ofFn x)) = C.eval (restrict bank x) := by
    rw [((inv x).2 C.output).2, show gs = C.gates.map normGate from rfl, wiresFrom_norm]
    rfl
  cases hout : acc.1.getD C.output (.inl false) with
  | inr k =>
    refine ⟨⟨acc.2, k⟩, elim_ok m gs _ (by simp), count, fun x => ?_⟩
    change (wiresFrom acc.2 (List.ofFn x)).getD k false = _
    simpa only [hout,Stat.val] using eval x
  | inl b =>
    have fixed (x : Fin m → Bool) : b = C.eval (restrict bank x) := by
      simpa only [hout,Stat.val] using eval x
    obtain ⟨x, hx⟩ := hasFalse
    have hb := (fixed x).trans hx
    subst b
    refine ⟨⟨[], m⟩, by simp [FanInTwo], by change 0 + _ ≤ _; omega, fun x => ?_⟩
    change (List.ofFn x).getD m false = _
    simpa using fixed x
abbrev target := PEqualNP.Outside.L_meta_9752.Engine.edge
private def value (g : Gate) (w : List Bool) : Bool :=
  g.op.eval (g.inputs.map fun j => w.getD j false)
private def step (w : List Bool) (g : Gate) : List Bool := w ++ [value g w]
private def AgreeAway (a b : List Bool) : Prop :=
  a.length = b.length ∧ 5 < b.length ∧
    ∀ j, j ≠ 5 → a.getD j false = b.getD j false
private theorem unread_value (g : Gate) (a b : List Bool) (near : AgreeAway a b)
    (_legal : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp))
    (h : reads 5 g = false) : value g a = value g b := by
  unfold value
  rw [← normGate_eval g (fun i => a.getD i false), ← normGate_eval g (fun i => b.getD i false)]
  congr 1
  apply List.map_congr_left
  intro j hj
  apply near.2.2 j
  rintro rfl
  have yes : reads 5 g = true := List.contains_iff_mem.mpr hj
  simp [h] at yes
private theorem step_agree (a b : List Bool) (g : Gate) (near : AgreeAway a b)
    (same : value g a = value g b) : AgreeAway (step a g) (step b g) := by
  obtain ⟨length, bound, eq⟩ := near
  refine ⟨by simp [step,length], by simp [step]; omega, ?_⟩
  intro j hj
  by_cases small : j < b.length
  · simpa only [step, List.getD_append _ _ _ _ small,
      List.getD_append _ _ _ _ (by omega : j < a.length)] using eq j hj
  · simp only [step,List.getD_append_right _ _ _ _ (by omega : a.length ≤ j),
      List.getD_append_right _ _ _ _ (by omega : b.length ≤ j),length,same]
private theorem fold_agree (p : List Gate) (a b : List Bool)
    (near : AgreeAway a b) (fan : FanInTwo ⟨p, 0⟩) (silent : ∀ g ∈ p, reads 5 g = false) :
    AgreeAway (p.foldl step a) (p.foldl step b) := by
  induction p generalizing a b with
  | nil => exact near
  | cons g p ih =>
    exact ih _ _ (step_agree a b g near (unread_value g a b near (fan g (by simp)).1 (silent g (by simp))))
      (fun k hk => fan k (by simp [hk])) (fun k hk => silent k (by simp [hk]))
def f (x : Fin 12 → Bool) : Bool :=
  (x 0 && x 6) || (x 0 && x 10) || (x 0 && x 11) ||
  (x 1 && x 5) || (x 1 && x 9) || (x 1 && x 10) ||
  (x 2 && x 8) || (x 2 && x 9) || (x 2 && x 11) ||
  (x 3 && x 7) || (x 3 && x 8) || (x 3 && x 10) ||
  (x 4 && x 6) || (x 4 && x 7) || (x 4 && x 9)
def bank : List (Option (Fin 11)) :=
  [some 0,some 1,some 2,some 3,some 4,none,some 5,some 6,some 7,some 8,some 9,some 10]
def lift (y : Fin 11 → Bool) : Fin 12 → Bool :=
  ![y 0,y 1,y 2,y 3,y 4,false,y 5,y 6,y 7,y 8,y 9,y 10]
def probe (b : Bool) : Fin 12 → Bool :=
  ![false,true,false,false,false,b,false,false,false,false,false,false]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem cofactor : ∀ y, f (lift y) = target y := by
  intro y
  simp [f,lift,target,PEqualNP.Outside.L_meta_9752.Engine.edge]
theorem layout_eq (y) : restrict bank y = List.ofFn (lift y) := by rfl
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem necessary (C : Circuit) (fan : FanInTwo C) (ev : ∀ x, C.eval (List.ofFn x) = f x) :
    0 < C.gates.countP (reads 5) := by
  have raw : C.output ≠ 5 := by
    intro eq
    let x : Fin 12 → Bool := fun i => decide (i = 5)
    obtain ⟨t, ht, _⟩ := wiresFrom_prefix C.gates (List.ofFn x)
    have v := ev x
    change (wiresFrom C.gates (List.ofFn x)).getD C.output false = f x at v
    rw [eq, ht, List.getD_append _ _ _ _ (by decide : 5 < (List.ofFn x).length)] at v
    exact (by decide : (List.ofFn x).getD 5 false ≠ f x) v
  by_contra! no
  have silent : ∀ g ∈ C.gates, reads 5 g = false := by
    intro g hg
    by_contra! h
    have yes : reads 5 g = true := by cases eq : reads 5 g <;> simp_all
    have pos : 0 < C.gates.countP (reads 5) := List.countP_pos_iff.mpr ⟨g,hg,yes⟩
    omega
  have near : AgreeAway (List.ofFn (probe false)) (List.ofFn (probe true)) := by
    refine ⟨rfl, by decide, ?_⟩
    intro j diff
    by_cases small : j < 12
    · exact (by decide +kernel : ∀ i : Fin 12, i.val ≠ 5 → (List.ofFn (probe false)).getD i.val false = (List.ofFn (probe true)).getD i.val false) ⟨j,small⟩ diff
    · have past (b : Bool) : (List.ofFn (probe b)).length ≤ j := by rw [List.length_ofFn]; omega
      simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_none (past false), List.getElem?_eq_none (past true)]
  have same := (fold_agree C.gates _ _ near fan silent).2.2 C.output raw
  change C.eval (List.ofFn (probe false)) = C.eval (List.ofFn (probe true)) at same
  rw [ev,ev] at same
  contradiction
theorem lower (core : ¬ HasCircuitSize 11 target 17) : ¬ HasCircuitSize 12 f 18 := by
  rintro ⟨C,fan,small,ev⟩
  have nonzero := necessary C fan ev
  have rest (y) : C.eval (restrict bank y) = target y := (layout_eq y) ▸ ((ev (lift y)).trans (cofactor y))
  obtain ⟨D,legal,cost,table⟩ := eliminate_pin bank 5 C fan (by decide) ⟨fun _ => false, (rest _).trans (by decide)⟩
  exact core ⟨D,legal,by omega,fun y => (table y).trans (rest y)⟩
end Physical
end PEqualNP.Outside.L_meta_9752

theorem PEqualNP.Outside.L_meta_9752 : ¬ (PEqualNP.MetaComplexity.HasCircuitSize 12 (fun x : Fin 12 → Bool => (x 0 && x 6) || (x 0 && x 10) || (x 0 && x 11) || (x 1 && x 5) || (x 1 && x 9) || (x 1 && x 10) || (x 2 && x 8) || (x 2 && x 9) || (x 2 && x 11) || (x 3 && x 7) || (x 3 && x 8) || (x 3 && x 10) || (x 4 && x 6) || (x 4 && x 7) || (x 4 && x 9)) 18) := by
  exact PEqualNP.Outside.L_meta_9752.Physical.lower
    (PEqualNP.Outside.L_meta_9752.Engine.directSplit PEqualNP.Outside.L_meta_9752.Engine.monoRoot PEqualNP.Outside.L_meta_9752.Engine.signedRoot)
