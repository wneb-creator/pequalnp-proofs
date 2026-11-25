import Binary17
open PEqualNP.Outside.L_meta_2592.Binary17
namespace PEqualNP.Outside.L_meta_1884.Unary18
open PEqualNP.CircuitLowerBounds
namespace Extended
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

def plainWord (a : Sig) : Bool := !(bit 0 a)
theorem nrm_map {u} {w : List Sig} (h : w.all plainWord=true) : w.map (nrm u)=w := by
  have e : w.map (nrm u) = w.map id := by
    apply List.map_congr_left
    intro a ha
    exact nrm_id (by simpa [plainWord] using List.all_eq_true.mp h a ha)
  rw [e,List.map_id]
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


def pins : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000,0xffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000,0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000000000000000000000000000000000000,0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000,0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00,0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc]
def initial : List Sig := pins
def first : Sig := 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
def target : Sig := 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc8fffffffffffffffffffffffffffffffffffffffffffffffffffffaeafffff8c8fffffffffffffffffffffffffffafff8ffffffffffffffffffffffffffeaffc8fffffffffffefcfcfffffffffffaf8f8ffeefeeeffeefcccffeafaeaffeaf8c8
def assign (r : Row) (j : Fin 10) := bit r (pins.getD j.val zero)
def f10 (x9 : Fin 10 → Bool) := (x9 (0 : Fin (10 : ℕ)) && x9 (1 : Fin (10 : ℕ)) || x9 (1 : Fin (10 : ℕ)) && x9 (2 : Fin (10 : ℕ)) || x9 (2 : Fin (10 : ℕ)) && x9 (3 : Fin (10 : ℕ)) || x9 (3 : Fin (10 : ℕ)) && x9 (4 : Fin (10 : ℕ)) || x9 (4 : Fin (10 : ℕ)) && x9 (0 : Fin (10 : ℕ)) || x9 (0 : Fin (10 : ℕ)) && x9 (5 : Fin (10 : ℕ)) || x9 (1 : Fin (10 : ℕ)) && x9 (6 : Fin (10 : ℕ)) || x9 (2 : Fin (10 : ℕ)) && x9 (7 : Fin (10 : ℕ)) || x9 (3 : Fin (10 : ℕ)) && x9 (8 : Fin (10 : ℕ)) || x9 (4 : Fin (10 : ℕ)) && x9 (9 : Fin (10 : ℕ)) || x9 (5 : Fin (10 : ℕ)) && x9 (7 : Fin (10 : ℕ)) || x9 (7 : Fin (10 : ℕ)) && x9 (9 : Fin (10 : ℕ)) || x9 (9 : Fin (10 : ℕ)) && x9 (6 : Fin (10 : ℕ)) || x9 (6 : Fin (10 : ℕ)) && x9 (8 : Fin (10 : ℕ)) || x9 (8 : Fin (10 : ℕ)) && x9 (5 : Fin (10 : ℕ)))
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem rowInputs : ∀ r : Row, initial.map (bit r) =
    List.ofFn (assign r) := by decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem rowTarget : ∀ r : Row, bit r target = f10 (assign r) := by decide +kernel


theorem realizeMono (C : Circuit) (legal : PEqualNP.MetaComplexity.Monotone2 C)
    (computes : ∀ x : Fin 10 → Bool, C.eval (List.ofFn x) = f10 x) :
    ∃ k S, k ≤ C.size ∧ Live false target k S ∧ ∀ a ∈ S, a ∈ initial := by
  have fan : PEqualNP.MetaComplexity.FanInTwo C := by
    intro g hg
    obtain ⟨ho, hl⟩ := legal g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ho ⊢
    exact ⟨ho.imp id Or.inl, hl⟩
  have mono : ∀ g ∈ C.gates, isNot g = false := by
    intro g hg
    have ho := (legal g hg).1
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ho
    rcases ho with ho | ho <;> simp [isNot, ho]
  have he : (execute C.gates initial).getD C.output zero = target := by
    apply bit_ext
    intro r
    rw [← b_read, execute_bits _ _ _ (fun g hg => (fan g hg).1)]
    change (C.wires (initial.map (bit r))).getD C.output false = _
    rw [rowInputs]
    exact (computes _).trans (rowTarget r).symm
  have hp : proper target := by unfold proper; decide +kernel
  have out := get_rep (u := false) (execute C.gates initial) C.output
  rw [he] at out
  unfold Repr at out
  rw [nrm_id (show bit 0 target = false by decide +kernel)] at out
  obtain ⟨k, S, hk, run, hs⟩ := extract C.gates initial fan (u := false)
    (fun _ => mono) hp (out.resolve_right (fun h => h hp))
  have ns : initial.all plainWord = true := by decide +kernel
  rw [nrm_map ns] at hs
  exact ⟨k, S, hk.trans List.countP_le_length, run, hs⟩

end Extended

namespace Geometry

lemma base_bit_zero (i) : bit i zero = false := by simp [bit, zero]
lemma base_bit_bin (i d) (a b : Sig) : bit i (bin d a b) =
    (if d = 0 then bit i a && bit i b else if d = 1 then bit i a || bit i b else
      if d = 2 then bit i a && !(bit i b) else !(bit i a) && bit i b) := by
  unfold bin
  split_ifs <;> simp [bit]

def pin (i : Fin 10) : Extended.Sig :=
  Extended.pins.getD i.val Extended.zero

def position : Fin 10 → Nat := ![9, 7, 5, 8, 6, 4, 2, 0, 3, 1]

def relabel : Fin 10 → Fin 10 → Fin 10 :=
  ![![0, 1, 2, 3, 4, 5, 6, 7, 8, 9], ![1, 0, 4, 3, 2, 6, 5, 9, 8, 7], ![2, 1, 0, 4, 3, 7, 6, 5, 9, 8], ![2, 3, 4, 0, 1, 7, 8, 9, 5, 6], ![1, 2, 3, 4, 0, 6, 7, 8, 9, 5], ![1, 2, 3, 8, 6, 0, 7, 4, 5, 9], ![2, 1, 6, 8, 3, 7, 0, 9, 5, 4], ![2, 3, 4, 9, 7, 1, 8, 0, 6, 5], ![2, 3, 8, 5, 7, 1, 4, 6, 0, 9], ![2, 3, 8, 6, 1, 7, 4, 5, 9, 0]]

lemma relabel_self : ∀ v : Fin 10, relabel v v = 0 := by decide

lemma relabel_bijective : ∀ v : Fin 10, Function.Bijective (relabel v) := by decide

def embedV (v : Fin 10) (r : Row) : Extended.Row :=
  Fin.ofNat 1024 ((List.ofFn (fun i : Fin 10 =>
    if r.val.testBit (position (relabel v i)) then 2 ^ position i else 0)).sum)

def projectV (v : Fin 10) (a : Extended.Sig) : Sig :=
  table (fun r => Extended.bit (embedV v r) a)

lemma observe_projectV (v : Fin 10) (a : Extended.Sig) :
    restrictRows (embedV v) (Extended.observe a) = observe (projectV v a) := by
  funext r
  exact (bit_table (fun r => Extended.bit (embedV v r) a) r).symm

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
lemma project_target : ∀ v : Fin 10, projectV v Extended.target = graph := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
lemma project_pin : ∀ v i : Fin 10,
    projectV v (pin i) = zero ∨ projectV v (pin i) ∈ inputs := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
lemma project_self : ∀ v : Fin 10, projectV v (pin v) = zero := by
  decide +kernel

lemma project_bin_commute (v : Fin 10) (d : Nat) (a b : Extended.Sig) :
    projectV v (Extended.bin d a b) = bin d (projectV v a) (projectV v b) := by
  apply bit_ext
  intro r
  simp only [projectV, bit_table, Extended.bit_bin, base_bit_bin]

lemma bin_zero_left (d : Fin 4) (a : Sig) :
    bin d.val zero a = if d.val = 0 ∨ d.val = 2 then zero else a := by
  apply bit_ext
  intro r
  fin_cases d <;> simp [base_bit_bin, base_bit_zero]

lemma project_bin (v u : Fin 10) (d : Fin 4) :
    projectV v (Extended.bin d.val (pin v) (pin u)) = zero ∨
      projectV v (Extended.bin d.val (pin v) (pin u)) = one ∨
      projectV v (Extended.bin d.val (pin v) (pin u)) ∈ inputs ∨
      neg (projectV v (Extended.bin d.val (pin v) (pin u))) ∈ inputs := by
  rw [project_bin_commute, project_self, bin_zero_left]
  split_ifs
  · exact Or.inl rfl
  · rcases project_pin v u with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inr (Or.inl h))

def witnessBase : Fin 10 → Fin 10 → Fin 4 → Extended.Row :=
  ![![![0, 0, 0, 0], ![16, 128, 128, 16], ![16, 48, 48, 16], ![16, 272, 272, 16], ![16, 64, 64, 16], ![64, 16, 16, 64], ![16, 20, 20, 16], ![16, 65, 65, 16], ![16, 72, 72, 16], ![16, 18, 18, 16]], ![![4, 512, 512, 4], ![0, 0, 0, 0], ![4, 32, 32, 4], ![4, 260, 260, 4], ![4, 68, 68, 4], ![4, 20, 20, 4], ![32, 4, 4, 32], ![4, 5, 5, 4], ![4, 40, 40, 4], ![4, 34, 34, 4]], ![![1, 513, 513, 1], ![1, 128, 128, 1], ![0, 0, 0, 0], ![1, 256, 256, 1], ![1, 65, 65, 1], ![1, 144, 144, 1], ![1, 5, 5, 1], ![128, 1, 1, 128], ![1, 9, 9, 1], ![1, 130, 130, 1]], ![![8, 520, 520, 8], ![8, 136, 136, 8], ![8, 32, 32, 8], ![0, 0, 0, 0], ![8, 64, 64, 8], ![8, 48, 48, 8], ![8, 36, 36, 8], ![8, 9, 9, 8], ![32, 8, 8, 32], ![8, 10, 10, 8]], ![![2, 512, 512, 2], ![2, 130, 130, 2], ![2, 34, 34, 2], ![2, 256, 256, 2], ![0, 0, 0, 0], ![2, 18, 18, 2], ![2, 260, 260, 2], ![2, 257, 257, 2], ![2, 10, 10, 2], ![256, 2, 2, 256]], ![![1, 512, 512, 1], ![1, 129, 129, 1], ![1, 40, 40, 1], ![1, 257, 257, 1], ![1, 65, 65, 1], ![0, 0, 0, 0], ![1, 5, 5, 1], ![8, 1, 1, 8], ![1, 8, 8, 1], ![1, 10, 10, 1]], ![![2, 514, 514, 2], ![2, 128, 128, 2], ![2, 34, 34, 2], ![2, 258, 258, 2], ![2, 72, 72, 2], ![2, 18, 18, 2], ![0, 0, 0, 0], ![2, 9, 9, 2], ![2, 8, 8, 2], ![8, 2, 2, 8]], ![![2, 514, 514, 2], ![2, 130, 130, 2], ![2, 32, 32, 2], ![2, 258, 258, 2], ![2, 80, 80, 2], ![2, 16, 16, 2], ![2, 20, 20, 2], ![0, 0, 0, 0], ![2, 10, 10, 2], ![16, 2, 2, 16]], ![![4, 516, 516, 4], ![4, 144, 144, 4], ![4, 36, 36, 4], ![4, 256, 256, 4], ![4, 68, 68, 4], ![4, 16, 16, 4], ![16, 4, 4, 16], ![4, 5, 5, 4], ![0, 0, 0, 0], ![4, 18, 18, 4]], ![![1, 513, 513, 1], ![1, 129, 129, 1], ![1, 36, 36, 1], ![1, 257, 257, 1], ![1, 64, 64, 1], ![1, 20, 20, 1], ![1, 4, 4, 1], ![4, 1, 1, 4], ![1, 9, 9, 1], ![0, 0, 0, 0]]]

def witness (v u : Fin 10) (d : Fin 4) : Extended.Row × Extended.Row :=
  let r := witnessBase v u d
  (r, Fin.ofNat 1024 (r.val + 2 ^ position v))

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
lemma witness_target : ∀ (v u : Fin 10) (d : Fin 4), v ≠ u →
    Extended.bit (witness v u d).1 Extended.target ≠
      Extended.bit (witness v u d).2 Extended.target := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
lemma witness_other_pin : ∀ (v u : Fin 10) (d : Fin 4) (i : Fin 10), i ≠ v →
    Extended.bit (witness v u d).1 (pin i) =
      Extended.bit (witness v u d).2 (pin i) := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
lemma witness_binary : ∀ (v u : Fin 10) (d : Fin 4), v ≠ u →
    Extended.bit (witness v u d).1 (Extended.bin d.val (pin v) (pin u)) =
      Extended.bit (witness v u d).2 (Extended.bin d.val (pin v) (pin u)) := by
  decide +kernel

lemma pins_eq : Extended.pins = List.ofFn pin := by rfl

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
lemma pin_injective : Function.Injective pin := by decide +kernel

end Geometry


namespace Geometry

lemma pin_mem_iff (a : Extended.Sig) : a ∈ Extended.initial ↔ ∃ i : Fin 10, pin i = a := by
  have h : List.ofFn pin = Extended.initial := by decide +kernel
  rw [← h, List.mem_ofFn]

lemma projected_available_mono (a : Sig) (h : a = zero ∨ a ∈ inputs) :
    Available false (inputs.map observe) (observe a) := by
  rcases h with rfl | ha
  · exact Or.inr (Or.inl ⟨false, by funext r; simp [observe, bit, zero]⟩)
  · exact Or.inl (List.mem_map.mpr ⟨_, ha, rfl⟩)

lemma project_bin_mono (v u : Fin 10) (d : Fin 4) :
    projectV v (Extended.bin d.val (pin v) (pin u)) = zero ∨
      projectV v (Extended.bin d.val (pin v) (pin u)) ∈ inputs := by
  rw [project_bin_commute, project_self, bin_zero_left]
  split_ifs
  · exact Or.inl rfl
  · exact project_pin v u

lemma needed_pin_mono (v u : Fin 10) (d : Fin 4) (hne : v ≠ u)
    {k : ℕ} {S : Finset Extended.Sig} (run : Extended.Live false Extended.target k S)
    (raw : ∀ a ∈ S, a ∈ Extended.initial ∨ a = Extended.bin d.val (pin v) (pin u)) :
    pin v ∈ S := by
  obtain ⟨a, ha, hd⟩ := Extended.live_row_difference run (witness_target v u d hne)
  rcases raw a ha with horig | heq
  · obtain ⟨i, rfl⟩ := (pin_mem_iff a).mp horig
    by_cases h : i = v
    · simpa [h] using ha
    · exact False.elim (hd (witness_other_pin v u d i h))
  · rw [heq] at hd
    exact False.elim (hd (witness_binary v u d hne))

variable (nineMonoFloor : Lower false inputs graph 16)
include nineMonoFloor

lemma suffix_floor_seventeen_mono (v u : Fin 10) (d : Fin 4) (hne : v ≠ u)
    {k : ℕ} {S : Finset Extended.Sig} (run : Extended.Live false Extended.target k S)
    (raw : ∀ a ∈ S, a ∈ Extended.initial ∨ a = Extended.bin d.val (pin v) (pin u)) :
    17 ≤ k := by
  classical
  have hfirst := needed_pin_mono v u d hne run raw
  let front := pin v :: (S.erase (pin v)).toList
  have nd : front.Nodup := by
    apply List.nodup_cons.mpr
    exact ⟨by simp, Finset.nodup_toList _⟩
  have eqS : front.toFinset = S := by
    ext a
    by_cases ha : a = pin v <;> simp [front, ha, hfirst]
  have hrun := Extended.list_run run front nd eqS
  have same : restrictRows (embedV v) (Extended.observe Extended.target) = observe graph := by
    rw [observe_projectV, project_target]
  have roots : supply false (inputs.map observe)
      ((front.map Extended.observe).map (restrictRows (embedV v))) := by
    intro a ha
    obtain ⟨_, hm, rfl⟩ := List.mem_map.mp ha
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hm
    rw [observe_projectV]
    rcases raw b (eqS ▸ List.mem_toFinset.mpr hb) with horig | rfl
    · obtain ⟨i, rfl⟩ := (pin_mem_iff b).mp horig
      exact projected_available_mono _ (project_pin v i)
    · exact projected_available_mono _ (project_bin_mono v u d)
  have lower := projected_bound (embedV v) hrun (same ▸ observe_proper graph_proper)
    Reach.start roots (L := 16) (same ▸ nineMonoFloor)
  have charge : 1 ≤ mass ((front.map Extended.observe).map (restrictRows (embedV v))) := by
    have constant : Constant (restrictRows (embedV v) (Extended.observe (pin v))) := by
      rw [observe_projectV, project_self]
      exact ⟨false, by funext r; simp [observe, bit, zero]⟩
    simp [front, mass_cons, cost, constant]
  omega

lemma binary_floor_eighteen {k : ℕ} {S : Finset Extended.Sig}
    (run : Extended.Live false Extended.target k S)
    (raw : ∀ a ∈ S, a ∈ Extended.initial) : 18 ≤ k := by
  cases k with
  | zero =>
    obtain ⟨rfl, _⟩ := run
    have impossible := raw Extended.target (by simp)
    have hn : Extended.target ∉ Extended.initial := by decide +kernel
    exact False.elim (hn impossible)
  | succ k =>
    obtain ⟨U, a, b, d, hd, rfl, ha, hb, hab, fresh, tail⟩ := run
    obtain ⟨v, rfl⟩ := (pin_mem_iff a).mp (raw a (by simp))
    obtain ⟨u, rfl⟩ := (pin_mem_iff b).mp (raw b (by simp))
    have hne : v ≠ u := by intro h; exact hab (congrArg pin h)
    have hfour : d < 4 := by rcases hd with hd | ⟨_, hd⟩ <;> omega
    have hbound := suffix_floor_seventeen_mono nineMonoFloor v u ⟨d, hfour⟩ hne tail (by
      intro z hz
      rcases Finset.mem_insert.mp hz with rfl | hU
      · exact Or.inr rfl
      · exact Or.inl (raw z (by simp [hU])))
    omega

lemma suffix_floor_eighteen_mono (v u : Fin 10) (d : Fin 4) (hne : v ≠ u)
    (hd : d.val = 0 ∨ d.val = 2)
    {k : ℕ} {S : Finset Extended.Sig} (run : Extended.Live false Extended.target k S)
    (raw : ∀ a ∈ S, a ∈ Extended.initial ∨ a = Extended.bin d.val (pin v) (pin u))
    (hq : Extended.bin d.val (pin v) (pin u) ∈ S)
    (hneq : Extended.bin d.val (pin v) (pin u) ≠ pin v) : 18 ≤ k := by
  classical
  let q := Extended.bin d.val (pin v) (pin u)
  have hfirst := needed_pin_mono v u d hne run raw
  let front := pin v :: q :: ((S.erase (pin v)).erase q).toList
  have nd : front.Nodup := by
    apply List.nodup_cons.mpr
    refine ⟨?_, ?_⟩
    · simp [q, Ne.symm hneq]
    · apply List.nodup_cons.mpr
      exact ⟨by simp, Finset.nodup_toList _⟩
  have eqS : front.toFinset = S := by
    ext a
    by_cases ha : a = pin v <;> by_cases hqa : a = q <;>
      simp [front, ha, hqa, hfirst, hq, q]
  have hrun := Extended.list_run run front nd eqS
  have same : restrictRows (embedV v) (Extended.observe Extended.target) = observe graph := by
    rw [observe_projectV, project_target]
  have roots : supply false (inputs.map observe)
      ((front.map Extended.observe).map (restrictRows (embedV v))) := by
    intro a ha
    obtain ⟨_, hm, rfl⟩ := List.mem_map.mp ha
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hm
    rw [observe_projectV]
    rcases raw b (eqS ▸ List.mem_toFinset.mpr hb) with horig | rfl
    · obtain ⟨i, rfl⟩ := (pin_mem_iff b).mp horig
      exact projected_available_mono _ (project_pin v i)
    · exact projected_available_mono _ (project_bin_mono v u d)
  have lower := projected_bound (embedV v) hrun (same ▸ observe_proper graph_proper)
    Reach.start roots (L := 16) (same ▸ nineMonoFloor)
  have cpin : Constant (restrictRows (embedV v) (Extended.observe (pin v))) := by
    rw [observe_projectV, project_self]
    exact ⟨false, by funext r; simp [observe, bit, zero]⟩
  have cq : Constant (restrictRows (embedV v) (Extended.observe q)) := by
    rw [observe_projectV]
    change Constant (observe (projectV v (Extended.bin d.val (pin v) (pin u))))
    rw [project_bin_commute, project_self, bin_zero_left, if_pos hd]
    exact ⟨false, by funext r; simp [observe, bit, zero]⟩
  have charge : 2 ≤ mass ((front.map Extended.observe).map (restrictRows (embedV v))) := by
    simp [front, mass_cons, cost, cpin, cq]
    omega
  omega

lemma first_and_floor_nineteen (v u : Fin 10) (hne : v ≠ u)
    {k : ℕ} {U : Finset Extended.Sig}
    (raw : ∀ a ∈ U, a ∈ Extended.initial)
    (fresh : Extended.bin 0 (pin v) (pin u) ∉ insert (pin v) (insert (pin u) U))
    (tail : Extended.Live false Extended.target k (insert (Extended.bin 0 (pin v) (pin u)) U)) :
    19 ≤ k + 1 := by
  have hneq : Extended.bin 0 (pin v) (pin u) ≠ pin v := by
    intro h
    apply fresh
    simp [h]
  have bound := suffix_floor_eighteen_mono nineMonoFloor v u 0 hne (Or.inl rfl) tail (by
    intro a ha
    rcases Finset.mem_insert.mp ha with rfl | hm
    · exact Or.inr rfl
    · exact Or.inl (raw a hm)) (by simp) hneq
  omega

end Geometry

theorem monotone_size_eighteen (nineMonoFloor : Lower false inputs graph 16) (C : Circuit) (legal : PEqualNP.MetaComplexity.Monotone2 C)
    (correct : ∀ x : Fin 10 → Bool, C.eval (List.ofFn x) = Extended.f10 x) :
    18 ≤ C.size := by
  obtain ⟨k, S, hk, run, raw⟩ := Extended.realizeMono C legal correct
  exact (Geometry.binary_floor_eighteen nineMonoFloor run raw).trans hk

namespace Extended

def unaryWord (h : Bool → Bool) : Sig :=
  if h false then (if h true then one else neg (pins.getD 0 zero))
  else (if h true then pins.getD 0 zero else zero)

def unaryInitial (m : Fin 10 → Fin 10) (h : Bool → Bool) : List Sig :=
  List.ofFn (fun i => pins.getD (m i).val zero) ++ [unaryWord h]

lemma unary_bits (h : Bool → Bool) (r : Row) :
    bit r (unaryWord h) = h (assign r 0) := by
  change bit r (unaryWord h) = h (bit r (pins.getD 0 zero))
  cases hf : h false <;> cases ht : h true <;>
    cases hb : bit r (pins.getD 0 zero) <;>
    simp only [unaryWord, hf, ht, Bool.false_eq_true, ite_false, ite_true,
      bit_zero, bit_one, bit_neg, hb, Bool.not_true, Bool.not_false]

lemma unary_rows (m : Fin 10 → Fin 10) (h : Bool → Bool) (r : Row) :
    (unaryInitial m h).map (bit r) = List.ofFn (assign r ∘ m) ++ [h (assign r 0)] := by
  simp [unaryInitial, List.map_ofFn, Function.comp_def, assign, unary_bits]

lemma pin_mem (i : Fin 10) : pins.getD i.val zero ∈ initial := by
  have eq : List.ofFn (fun i : Fin 10 => pins.getD i.val zero) = initial := by decide +kernel
  rw [← eq]
  exact List.mem_ofFn.mpr ⟨i, rfl⟩

lemma live_roots_proper {u T k S} (run : Live u T k S) : ∀ a ∈ S, proper a := by
  induction run using Live.ind with
  | stop hp => simpa using hp
  | @binary k U a b d hd ha hb hab hf tail ih =>
    intro v h
    rcases Finset.mem_insert.mp h with rfl | h
    · exact ha
    rcases Finset.mem_insert.mp h with rfl | h
    · exact hb
    exact ih _ (Finset.mem_insert_of_mem h)

theorem realizeUnaryMono (C : Circuit) (m : Fin 10 → Fin 10) (h : Bool → Bool)
    (legal : PEqualNP.MetaComplexity.Monotone2 C)
    (correct : ∀ x : Fin 10 → Bool,
      C.eval (List.ofFn (x ∘ m) ++ [h (x 0)]) = f10 x) :
    ∃ k S, k ≤ C.size ∧ Live false target k S ∧
      ∀ a ∈ S, a ∈ initial ∨ a = neg (pins.getD 0 zero) := by
  have fan : PEqualNP.MetaComplexity.FanInTwo C := by
    intro g hg
    obtain ⟨ho, hl⟩ := legal g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ho ⊢
    exact ⟨ho.imp id Or.inl, hl⟩
  have mono : ∀ g ∈ C.gates, isNot g = false := by
    intro g hg
    have ho := (legal g hg).1
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ho
    rcases ho with ho | ho <;> simp [isNot, ho]
  have he : (execute C.gates (unaryInitial m h)).getD C.output zero = target := by
    apply bit_ext
    intro r
    rw [← b_read, execute_bits _ _ _ (fun g hg => (fan g hg).1)]
    change (C.wires ((unaryInitial m h).map (bit r))).getD C.output false = _
    rw [unary_rows]
    exact (correct _).trans (rowTarget r).symm
  have hp : proper target := by unfold proper; decide +kernel
  have out := get_rep (u := false) (execute C.gates (unaryInitial m h)) C.output
  rw [he] at out
  unfold Repr at out
  simp only [nrm, Bool.false_and, Bool.false_eq_true, ite_false] at out
  obtain ⟨k, S, hk, run, hs⟩ := extract C.gates (unaryInitial m h) fan (u := false)
    (fun _ => mono) hp (out.resolve_right (fun h => h hp))
  have hnrm : nrm false = id := rfl
  rw [hnrm, List.map_id] at hs
  refine ⟨k, S, hk.trans List.countP_le_length, run, ?_⟩
  intro a ha
  have pa := live_roots_proper run a ha
  have hm := hs a ha
  simp only [unaryInitial, List.mem_append, List.mem_singleton] at hm
  rcases hm with hm | rfl
  · obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hm
    exact Or.inl (pin_mem (m i))
  · cases hf : h false <;> cases ht : h true <;>
      simp only [unaryWord, hf, ht, Bool.false_eq_true, ite_false, ite_true] at pa ⊢
    · exact False.elim (pa.1 rfl)
    · exact Or.inl (pin_mem 0)
    · exact Or.inr trivial
    · exact False.elim (pa.2 rfl)

lemma binary_increase {d : Nat} (hd : allowed false d) (a b : Sig) (r s : Row)
    (hr : bit r (bin d a b) = false) (hs : bit s (bin d a b) = true) :
    (bit r a = false ∧ bit s a = true) ∨ (bit r b = false ∧ bit s b = true) := by
  have hlt : d < 2 := by simpa [allowed] using hd
  have hd' : d = 0 ∨ d = 1 := by omega
  rcases hd' with rfl | rfl
  all_goals
    cases hra : bit r a <;> cases hrb : bit r b <;>
      cases hsa : bit s a <;> cases hsb : bit s b <;>
      simp_all [bin, bit]

theorem live_row_increase {T k S} (h : Live false T k S) {r s : Row}
    (hr : bit r T = false) (hs : bit s T = true) :
    ∃ a ∈ S, bit r a = false ∧ bit s a = true := by
  induction h using Live.ind with
  | stop hp => exact ⟨_, by simp, hr, hs⟩
  | @binary k U a b d hd ha hb hab hf tail ih =>
    obtain ⟨v, hv, hvr, hvs⟩ := ih
    rcases Finset.mem_insert.mp hv with rfl | hu
    · rcases binary_increase hd a b r s hvr hvs with ha | hb
      · exact ⟨a, by simp, ha⟩
      · exact ⟨b, by simp, hb⟩
    · exact ⟨v, Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hu), hvr, hvs⟩

end Extended

namespace Geometry

lemma base_bit_one (r : Row) : bit r one = true := by
  have all : ∀ r : Row, bit r one = true := by decide +kernel
  exact all r

lemma unary_needs_positive {k S} (run : Extended.Live false Extended.target k S)
    (raw : ∀ a ∈ S, a ∈ Extended.initial ∨ a = Extended.neg (pin 0)) : pin 0 ∈ S := by
  obtain ⟨a, ha, hfalse, htrue⟩ := Extended.live_row_increase run
    (r := 128) (s := 640) (by decide +kernel) (by decide +kernel)
  rcases raw a ha with hpin | rfl
  · obtain ⟨i, rfl⟩ := (pin_mem_iff a).mp hpin
    have unique : ∀ i : Fin 10,
        Extended.bit 128 (pin i) = false → Extended.bit 640 (pin i) = true → i = 0 := by
      decide +kernel
    simpa [unique i hfalse htrue] using ha
  · have opposite : Extended.bit 128 (Extended.neg (pin 0)) = true := by decide +kernel
    rw [opposite] at hfalse
    contradiction

lemma unary_binary_floor_eighteen (nineMonoFloor : Lower false inputs graph 16)
    {k S} (run : Extended.Live false Extended.target k S)
    (raw : ∀ a ∈ S, a ∈ Extended.initial ∨ a = Extended.neg (pin 0)) : 18 ≤ k := by
  classical
  by_cases hneg : Extended.neg (pin 0) ∈ S
  · have hpos := unary_needs_positive run raw
    let q := Extended.neg (pin 0)
    have hneq : q ≠ pin 0 := by decide +kernel
    let front := pin 0 :: q :: ((S.erase (pin 0)).erase q).toList
    have nd : front.Nodup := by
      apply List.nodup_cons.mpr
      refine ⟨?_, ?_⟩
      · simp [q, Ne.symm hneq]
      · apply List.nodup_cons.mpr
        exact ⟨by simp, Finset.nodup_toList _⟩
    have eqS : front.toFinset = S := by
      ext a
      by_cases ha : a = pin 0 <;> by_cases hqa : a = q <;>
        simp [front, ha, hqa, hpos, hneg, q]
    have hrun := Extended.list_run run front nd eqS
    have same : restrictRows (embedV 0) (Extended.observe Extended.target) = observe graph := by
      rw [observe_projectV, project_target]
    have projq : projectV 0 q = one := by decide +kernel
    have roots : supply false (inputs.map observe)
        ((front.map Extended.observe).map (restrictRows (embedV 0))) := by
      intro a ha
      obtain ⟨_, hm, rfl⟩ := List.mem_map.mp ha
      obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hm
      rw [observe_projectV]
      rcases raw b (eqS ▸ List.mem_toFinset.mpr hb) with horig | rfl
      · obtain ⟨i, rfl⟩ := (pin_mem_iff b).mp horig
        exact projected_available_mono _ (project_pin 0 i)
      · change Available false (inputs.map observe) (observe (projectV 0 q))
        rw [projq]
        exact Or.inr (Or.inl ⟨true, by funext r; exact base_bit_one r⟩)
    have lower := projected_bound (embedV 0) hrun (same ▸ observe_proper graph_proper)
      Reach.start roots (L := 16) (same ▸ nineMonoFloor)
    have cpin : Constant (restrictRows (embedV 0) (Extended.observe (pin 0))) := by
      rw [observe_projectV, project_self]
      exact ⟨false, by funext r; simp [observe, bit, zero]⟩
    have cq : Constant (restrictRows (embedV 0) (Extended.observe q)) := by
      rw [observe_projectV, projq]
      exact ⟨true, by funext r; exact base_bit_one r⟩
    have charge : 2 ≤ mass ((front.map Extended.observe).map (restrictRows (embedV 0))) := by
      simp [front, mass_cons, cost, cpin, cq]
      omega
    omega
  · apply binary_floor_eighteen nineMonoFloor run
    intro a ha
    exact (raw a ha).resolve_right (fun he => hneg (he ▸ ha))

end Geometry

theorem unary_mono_eighteen (nineMonoFloor : Lower false inputs graph 16)
    (C : Circuit) (m : Fin 10 → Fin 10) (h : Bool → Bool)
    (legal : PEqualNP.MetaComplexity.Monotone2 C)
    (correct : ∀ x : Fin 10 → Bool,
      C.eval (List.ofFn (x ∘ m) ++ [h (x 0)]) = Extended.f10 x) : 18 ≤ C.size := by
  obtain ⟨k, S, hk, run, raw⟩ := Extended.realizeUnaryMono C m h legal correct
  exact (Geometry.unary_binary_floor_eighteen nineMonoFloor run raw).trans hk

end PEqualNP.Outside.L_meta_1884.Unary18
