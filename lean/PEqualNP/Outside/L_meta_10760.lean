import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_10760

-- Extracted from the independently checked, compacted L_meta_10538 certificate.
namespace RestrictionSixProof
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
lemma allowed_four {u d} (h : allowed u d) : d=0 ∨ d=1 ∨ (u=true ∧ d=2) ∨ (u=true ∧ d=3) := by
  rcases h with h | ⟨h,j⟩
  · omega
  · have : d=0 ∨ d=1 ∨ d=2 ∨ d=3 := by omega
    rcases this with h1 | h1 | h1 | h1
    · exact Or.inl h1
    · exact Or.inr (Or.inl h1)
    · exact Or.inr (Or.inr (Or.inl ⟨h,h1⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨h,h1⟩))
lemma bin_flip {u d} (h : allowed u d) (a b : Sig) : bin d a b = bin (flipOp d) b a := by
  rcases allowed_four h with rfl | rfl | ⟨_,rfl⟩ | ⟨_,rfl⟩ <;> simp [bin,flipOp,BitVec.and_comm,BitVec.or_comm]
lemma flip_flip {u d} (h : allowed u d) : allowed u (flipOp d) ∧ flipOp (flipOp d)=d := by
  rcases allowed_four h with rfl | rfl | ⟨hu,rfl⟩ | ⟨hu,rfl⟩
  all_goals simp_all [flipOp,allowed]

def Live (u : Bool) (target : Sig) : Nat → Finset Sig → Prop
  | 0,S => S={target} ∧ proper target
  | k+1,S => ∃ (U : Finset Sig) (a b : Sig) (d : Nat), allowed u d ∧ S=insert a (insert b U) ∧
      proper a ∧ proper b ∧ a ≠ b ∧
      bin d a b ∉ insert a (insert b U) ∧ Live u target k (insert (bin d a b) U)
lemma Live.stop {u} {target : Sig} (hp : proper target) : Live u target 0 {target} := ⟨rfl,hp⟩
lemma Live.binary {u} {target : Sig} {k : Nat} {U : Finset Sig} {a b : Sig} {d : Nat} (hd : allowed u d)
    (ha : proper a) (hb : proper b) (hab : a ≠ b)
    (hfresh : bin d a b ∉ insert a (insert b U)) (tail : Live u target k (insert (bin d a b) U)) :
    Live u target (k+1) (insert a (insert b U)) :=
  ⟨U,a,b,d,hd,rfl,ha,hb,hab,hfresh,tail⟩
lemma Live.ind {u} {target : Sig} {motive : ∀ (k : Nat) (S : Finset Sig), Live u target k S → Prop}
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
lemma bit_ext {a b : Sig} (h : ∀ i, bit i a = bit i b) : a=b :=
  BitVec.eq_of_getLsbD_eq fun j hj => h ⟨j,hj⟩

def nrm (u : Bool) (a : Sig) : Sig := if u && bit 0 a then neg a else a
lemma nrm_false (a : Sig) : nrm false a = a := rfl
lemma nrm_bit (a : Sig) : bit 0 (nrm true a) = false := by
  cases h : bit 0 a <;> simp [nrm,h,bit_neg]
lemma nrm_id {u} {a : Sig} (h : bit 0 a = false) : nrm u a = a := by simp [nrm,h]
lemma neg_neg' (a : Sig) : neg (neg a) = a := by simp [neg]
lemma nrm_neg (a : Sig) : nrm true (neg a) = nrm true a := by
  cases h : bit 0 a <;> simp [nrm,h,bit_neg,neg_neg']
lemma proper_neg {a : Sig} (h : proper (neg a)) : proper a := by
  refine ⟨?_,?_⟩
  · rintro rfl
    exact h.2 (by simp [neg,zero,one])
  · rintro rfl
    exact h.1 (by simp [neg,zero,one])
lemma proper_nrm {u} {a : Sig} (h : proper (nrm u a)) : proper a := by
  unfold nrm at h
  split at h
  · exact proper_neg h
  · exact h
def prime (d : Bool) (a b : Sig) := if d then a ||| b else a &&& b
lemma bit_prime (i) (d : Bool) (a b : Sig) : bit i (prime d a b) =
    (if d then bit i a || bit i b else bit i a && bit i b) := by cases d <;> simp [prime,bit]
lemma nrm_prime (d : Bool) (a b : Sig) :
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

lemma norm_ne_one (a : Sig) : nrm true a ≠ one := by
  intro h
  have := nrm_bit a
  rw [h,bit_one] at this
  exact Bool.noConfusion this
lemma prime_rep {u w a b} (d : Bool) (ha : Repr u w a) (hb : Repr u w b) :
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
lemma repr_const {u w} {v : Sig} (h : v=zero ∨ v=one) : Repr u w v := by
  refine Or.inr fun hp => ?_
  have := proper_nrm hp
  rcases h with rfl | rfl
  · exact this.1 rfl
  · exact this.2 rfl
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
lemma Reach.start {R u} {roots : List (Wire R)} : Reach u roots 0 roots := rfl
lemma Reach.two {R u} {roots : List (Wire R)} {p bank a b} (op : Bool) (h : Reach u roots p bank)
    (ha : Available u bank a) (hb : Available u bank b) : Reach u roots (p+1) (combine op a b :: bank) :=
  ⟨op,bank,a,b,h,ha,hb,rfl⟩
lemma Reach.ind {R u} {roots : List (Wire R)} {motive : ∀ p bank, Reach u roots p bank → Prop}
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
lemma Run.stop {R u} {goal : Wire R} : Run u goal 0 [goal] := List.Perm.refl _
lemma Run.perm {R u} {goal : Wire R} {s : Nat} {xs zs : List (Wire R)} (p : xs.Perm zs)
    (h : Run u goal s xs) : Run u goal s zs := by
  cases s with
  | zero => exact List.Perm.trans h p
  | succ s =>
    obtain ⟨op,ka,kb,a,b,rest,hd,q,h⟩ := h
    exact ⟨op,ka,kb,a,b,rest,hd,q.trans p,h⟩
lemma Run.two {R u} {goal : Wire R} {s : Nat} {a b : Wire R} {rest : List (Wire R)} (op : Nat) (hd : allowed u op) (ka kb : Bool)
    (h : Run u goal s (comb op a b :: kept ka a (kept kb b rest))) : Run u goal (s+1) (a::b::rest) :=
  ⟨op,ka,kb,a,b,rest,hd,List.Perm.refl _,h⟩
lemma Run.ind {R u} {goal : Wire R} {motive : ∀ s ws, Run u goal s ws → Prop}
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

lemma mass_cons {R} (a : Wire R) (xs) : mass (a::xs)=cost a + mass xs := by
  simp [mass]

lemma mass_kept {R} (a : Wire R) (xs) (k : Bool) : mass xs ≤ mass (kept k a xs) := by
  cases k <;> simp [kept,mass_cons]

lemma inv_constant {R} {a : Wire R} (h : Constant a) : Constant (inv a) := by
  obtain ⟨v,rfl⟩ := h
  exact ⟨!v,rfl⟩

lemma inv_inv' {R} (a : Wire R) : inv (inv a)=a := by
  funext r
  simp [inv]
lemma cost_inv {R} (a : Wire R) : cost (inv a)=cost a := by
  have : Constant (inv a) ↔ Constant a := ⟨fun h => inv_inv' a ▸ inv_constant h,inv_constant⟩
  by_cases h : Constant a
  · simp only [cost,if_pos h,if_pos (this.mpr h)]
  · simp only [cost,if_neg h,if_neg (fun x => h (this.mp x))]
lemma avail_inv {R u} {bank : List (Wire R)} {a} (hu : u=true) (h : Available u bank a) : Available u bank (inv a) := by
  rcases h with h | h | ⟨_,h⟩
  · exact Or.inr (Or.inr ⟨hu,(inv_inv' a).symm ▸ h⟩)
  · exact Or.inr (Or.inl (inv_constant h))
  · exact Or.inl h
lemma both_constant {R} {a b : Wire R} (op) (h : Constant a) (g : Constant b) :
    Constant (combine op a b) := by
  obtain ⟨v,rfl⟩ := h
  obtain ⟨w,rfl⟩ := g
  cases op <;> exact ⟨_,rfl⟩

lemma from_constant {R u} (op) {a b : Wire R} {bank}
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

lemma available_cons {R u} {bank v} (w : Wire R) (h : Available u bank v) :
    Available u (w::bank) v :=
  h.imp (List.mem_cons_of_mem _) (Or.imp id (And.imp id (List.mem_cons_of_mem _)))

lemma extend_two {R u} (roots : List (Wire R)) {p bank a b} (op) (hp : Reach u roots p bank)
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
lemma comb_prime {R u} {bank : List (Wire R)} {d a b} (hd : allowed u d) (ha : Available u bank a) (hb : Available u bank b) :
    ∃ op x y, comb d a b=combine op x y ∧ Available u bank x ∧ Available u bank y ∧ cost x=cost a ∧ cost y=cost b := by
  rcases allowed_four hd with rfl | rfl | ⟨hu,rfl⟩ | ⟨hu,rfl⟩
  · exact ⟨false,a,b,rfl,ha,hb,rfl,rfl⟩
  · exact ⟨true,a,b,rfl,ha,hb,rfl,rfl⟩
  · exact ⟨false,a,inv b,rfl,ha,avail_inv hu hb,rfl,cost_inv b⟩
  · exact ⟨false,inv a,b,rfl,avail_inv hu ha,hb,cost_inv a,rfl⟩
lemma extend_comb {R u} (roots : List (Wire R)) {p bank a b} (d) (hd : allowed u d) (hp : Reach u roots p bank)
    (ha : Available u bank a) (hb : Available u bank b) :
    ∃ q next, Reach u roots q next ∧ Available u next (comb d a b) ∧
        (∀ v, Available u bank v → Available u next v) ∧
        q+cost a+cost b ≤ p+1+cost (comb d a b) := by
  obtain ⟨op,x,y,e,hx,hy,cx,cy⟩ := comb_prime hd ha hb
  rw [e,←cx,←cy]
  exact extend_two roots op hp hx hy

lemma mem_kept {α : Type} {k : Bool} {x a : α} {xs} (h : x ∈ kept k a xs) :
    x=a ∨ x∈xs := by cases k <;> simp_all [kept]

lemma contraction {R u} {goal : Wire R} (nc : ¬Constant goal) {s ws}
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

lemma restrict_kept {R S : Type} (rows : S → R) (k : Bool) (a : Wire R) (ws) :
    (kept k a ws).map (restrictRows rows) =
    kept k (restrictRows rows a) (ws.map (restrictRows rows)) := by
  cases k <;> simp [kept]

lemma restrict_comb {R S : Type} (rows : S → R) (d) (a b : Wire R) :
    restrictRows rows (comb d a b) = comb d (restrictRows rows a) (restrictRows rows b) := by
  unfold comb
  split_ifs <;> rfl
lemma restrict_run {R S : Type} {u} (rows : S → R) {goal s ws} (h : Run u goal s ws) :
    Run u (restrictRows rows goal) s (ws.map (restrictRows rows)) := by
  induction h using Run.ind with
  | stop => exact Run.stop
  | perm p _ ih => exact Run.perm (p.map _) ih
  | two op hd ka kb _ ih =>
    simp only [List.map_cons,restrict_kept,restrict_comb] at ih ⊢
    exact Run.two op hd ka kb ih

lemma projected_bound {R S : Type} {u} (rows : S → R) {goal s ws} (h : Run u goal s ws)
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

lemma bit_table (f : Wire Row) (r : Row) : bit r (table f) = f r := by
  simp only [bit,table,BitVec.getLsbD_cast,BitVec.getLsbD_ofBoolListLE,List.getD_eq_getElem?_getD,List.getElem?_ofFn]; simp [r.isLt]

lemma table_observe (v : Sig) : table (observe v) = v := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  exact bit_table (observe v) ⟨j,hj⟩

lemma observe_table (f : Wire Row) : observe (table f) = f := by
  funext r
  exact bit_table f r

lemma obs_neg (a : Sig) : observe (neg a) = inv (observe a) := by
  funext r
  exact bit_neg _ _

lemma obs_bin (d : Nat) (a b : Sig) :
    observe (bin d a b) = comb d (observe a) (observe b) := by
  funext r
  simp only [observe,bit_bin,comb]
  split_ifs <;> rfl

lemma map_kept {α β : Type} (f : α → β) (d : Bool) (a : α) (l : List α) :
    (kept d a l).map f = kept d (f a) (l.map f) := by cases d <;> rfl

lemma kept_nd {α : Type} (k : Bool) (a : α) (l : List α)
    (hn : l.Nodup) (ha : a ∉ l) : (kept k a l).Nodup := by cases k <;> simp [kept,hn,ha]

lemma kept_fin (k : Bool) (a : Sig) (l : List Sig) :
    (kept k a l).toFinset = if k then insert a l.toFinset else l.toFinset := by
  cases k <;> simp [kept]

lemma list_run {u} {T : Sig} {k S} (h : Live u T k S) (v : List Sig)
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


lemma table_inv (f : Wire Row) : table (inv f) = neg (table f) := by
  rw [←table_observe (neg (table f)),obs_neg,observe_table]

lemma table_prime (d : Bool) (f g : Wire Row) :
    table (combine d f g) = prime d (table f) (table g) := by
  apply bit_ext
  intro r
  rw [bit_table,bit_prime,bit_table,bit_table]
  cases d <;> rfl

lemma available_rep {u} {bank : List (Wire Row)} {a} (h : Available u bank a) :
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

lemma reach_live_sub {u} {roots : List (Wire Row)} {p bank}
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
lemma nrm_map {u} {w : List Sig} (h : w.all plainWord=true) : w.map (nrm u)=w := by
  have e : w.map (nrm u) = w.map id := by
    apply List.map_congr_left
    intro a ha
    exact nrm_id (by simpa [plainWord] using List.all_eq_true.mp h a ha)
  rw [e,List.map_id]
lemma reach_live {u} {roots : List Sig} {p bank T} (hp : proper T) (nT : plainWord T=true) (nR : roots.all plainWord=true)
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

lemma live_row_difference {u T k S} (h : Live u T k S) {r s : Row}
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

lemma raw_required {u T k S} (h : Live u T k S) (roots : List Sig) (a : Sig)
    (sub : ∀ v ∈ S, v ∈ roots) (r s : Row) (diff : bit r T ≠ bit s T)
    (isolated : ∀ v ∈ roots, v ≠ a → bit r v = bit s v) : a ∈ S := by
  obtain ⟨v,hv,hd⟩ := live_row_difference h diff
  by_cases veq : v=a
  · simpa [veq] using hv
  · exact False.elim (hd (isolated v (sub v hv) veq))

def Lower (u : Bool) (roots : List Sig) (T : Sig) (L : Nat) : Prop :=
  ∀ p bank, Reach u (roots.map observe) p bank → Available u bank (observe T) → L ≤ p

def Impossible (u : Bool) (T : Sig) (cap : Nat) (S : Finset Sig) : Prop :=
  ∀ k, k ≤ cap → ¬Live u T k S

def Essential (T : Sig) (roots : List Sig) (a : Sig) : Prop :=
  ∃ r s : Row, bit r T ≠ bit s T ∧ ∀ v ∈ roots, v ≠ a → bit r v = bit s v

lemma lower_impossible {u roots T L} (hp : proper T) (nT : plainWord T=true) (nR : roots.all plainWord=true)
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

lemma observe_proper {v : Sig} (hv : proper v) : ¬Constant (observe v) := by
  rintro ⟨b,h⟩
  have hr : Repr false [] v := by
    apply repr_const
    cases b
    · exact Or.inl (bit_ext fun i => (congrFun h i).trans (bit_zero i).symm)
    · exact Or.inr (bit_ext fun i => (congrFun h i).trans (bit_one i).symm)
  have hr' : represented [] v := hr
  exact (hr'.resolve_left (by simp)) hv



def childTwo (ws : List Sig) (a b : Sig) (d : Nat) (ka kb : Bool) : List Sig :=
  bin d a b :: kept ka a (kept kb b ((ws.erase a).erase b))

lemma erase_fin {l : List Sig} (h : l.Nodup) (a : Sig) : (l.erase a).toFinset = l.toFinset.erase a := by
  ext x
  simp [h.mem_erase_iff]

lemma enum_step {u} {T : Sig} {cap : Nat} {ws : List Sig} (hn : ws.Nodup) (out : T ∉ ws)
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

def Slice (u : Bool) (raw : List Sig) (T d : Sig) (L : Nat) : Prop :=
  ∃ (f : Row → Row) (roots : List Sig), (∀ r, bit (f r) d = true) ∧
    (∀ a ∈ raw, Available u (roots.map observe) (restrictRows f (observe a))) ∧
    ¬Constant (restrictRows f (observe T)) ∧
    ∀ p bank, Reach u (roots.map observe) p bank → Available u bank (restrictRows f (observe T)) → L ≤ p
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
lemma bit_W (r : Row) (a : Nat) : bit r (W a) = a.testBit r.val := by
  unfold bit W
  rw [BitVec.getLsbD_ofNat]
  simp [r.isLt]
lemma tb_land (a b i : Nat) : (Nat.land a b).testBit i = (a.testBit i && b.testBit i) := Nat.testBit_and ..
lemma tb_lor (a b i : Nat) : (Nat.lor a b).testBit i = (a.testBit i || b.testBit i) := Nat.testBit_or ..
lemma tb_xor (a b i : Nat) : (Nat.xor a b).testBit i = (a.testBit i ^^ b.testBit i) := Nat.testBit_xor ..
lemma nbeq {a b : Nat} (h : a ≠ b) : Nat.beq a b = false := by
  cases e : Nat.beq a b
  · rfl
  · exact absurd (Nat.eq_of_beq_eq_true e) h
lemma W_nb (o a b : Nat) : W (nb o a b) = bin o (W a) (W b) := by
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
lemma bin_four (o : Nat) : ∃ e, e < 4 ∧ ∀ a b, bin o a b = bin e a b := by
  by_cases h : o < 4
  · exact ⟨o,h,fun _ _ => rfl⟩
  · refine ⟨3,by omega,fun a b => ?_⟩
    have h0 : o ≠ 0 := by omega
    have h1 : o ≠ 1 := by omega
    have h2 : o ≠ 2 := by omega
    simp [bin,h0,h1,h2]
lemma W_full : W full = one := by
  apply bit_ext
  intro r
  rw [bit_W,bit_one]
  revert r
  decide +kernel
lemma W_inj {a b : Nat} (ha : a < 2^128) (hb : b < 2^128) (h : W a = W b) : a = b := by
  have := congrArg BitVec.toNat h
  simpa only [W,BitVec.toNat_ofNat,Nat.mod_eq_of_lt ha,Nat.mod_eq_of_lt hb] using this

def rootsW (R : List Nat) : List Sig := R.map fun i => W (xN i)
def LowN (R : List Nat) (T L : Nat) : Prop := Lower true (rootsW R) (W T) L
abbrev SliceD := Nat × Nat × List Nat
def SliceN (R : List Nat) (T : Nat) (s : SliceD) : Prop :=
  Slice true (rootsW R) (W T) (W s.1) s.2.1 ∧ ∀ v ∈ s.2.2, v ∈ R

def baseOK (T : Nat) (R : List Nat) (E : List (Nat × Nat × Nat)) : Bool :=
  decide (T < 2^128) && !(T.testBit 0) && (E.map Prod.fst == R) && !R.isEmpty && decide (rootsW R).Nodup &&
  R.all (fun i => !((xN i).testBit 0)) &&
  E.all (fun e => decide (e.2.1 < 128) && decide (e.2.2 < 128) && (T.testBit e.2.1 != T.testBit e.2.2) &&
    R.all (fun i => i == e.1 || (xN i).testBit e.2.1 == (xN i).testBit e.2.2))

def BaseP (T : Nat) (R : List Nat) : Prop :=
  T < 2^128 ∧ plainWord (W T) = true ∧ (rootsW R).Nodup ∧
  (rootsW R).all plainWord = true ∧
  (∀ a ∈ rootsW R, Essential (W T) (rootsW R) a) ∧ proper (W T)
namespace BaseP
lemma lt {T R} (h : BaseP T R) : T < 2^128 := h.1
lemma plain {T R} (h : BaseP T R) : plainWord (W T) = true := h.2.1
lemma nodup {T R} (h : BaseP T R) : (rootsW R).Nodup := h.2.2.1
lemma plainR {T R} (h : BaseP T R) : (rootsW R).all plainWord = true := h.2.2.2.1
lemma ess {T R} (h : BaseP T R) : ∀ a ∈ rootsW R, Essential (W T) (rootsW R) a := h.2.2.2.2.1
lemma prop {T R} (h : BaseP T R) : proper (W T) := h.2.2.2.2.2
end BaseP

lemma baseOK_ok {T R E} (h : baseOK T R E = true) : BaseP T R := by
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

lemma lowOf {T R E K} (hB : baseOK T R E = true) (h : Impossible true (W T) K (rootsW R).toFinset) :
    LowN R T (K+1) := by
  have b := baseOK_ok hB
  exact lower_impossible b.prop b.plain b.plainR b.ess h
lemma lowCount {T R E K} (hB : baseOK T R E = true) (h : K + 2 ≤ R.length) : LowN R T (K+1) := by
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

lemma mkSlice {R T E R' G E' d L vs w} (_hB : baseOK T R E = true) (hB' : baseOK G R' E' = true)
    (hL : LowN R' G L) (h : sliceChk R T R' G d vs w = true) : SliceN R T (d,L,vs) := by
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

def av (d : Nat) (P : List Nat) (v : Nat) : Bool :=
  let m := Nat.land v d
  Nat.beq m 0 || Nat.beq m d || P.any (fun x => Nat.beq x m || Nat.beq x (Nat.xor d m))
def cn (d v : Nat) : Nat :=
  let m := Nat.land v d
  bif Nat.beq m 0 || Nat.beq m d then 1 else 0
def sumc (d : Nat) : List Nat → Nat
  | [] => 0
  | v::l => Nat.add (cn d v) (sumc d l)
def mkPool (P : List Nat) : List (Nat × Nat × Nat) → List Nat
  | [] => P
  | c::cs => mkPool (P ++ [nb c.1 (P.getD c.2.1 0) (P.getD c.2.2 0)]) cs
def initPool (d : Nat) (vs : List Nat) : List Nat := vs.map fun v => Nat.land (xN v) d

abbrev RF (f : Row → Row) (v : Nat) : Wire Row := restrictRows f (observe (W v))
def PS (f : Row → Row) (bank : List (Wire Row)) (P : List Nat) : Prop :=
  ∀ v ∈ P, Available true bank (RF f v)
lemma rf_apply (f : Row → Row) (v : Nat) (r : Row) : RF f v r = v.testBit (f r).val := bit_W _ _
lemma rf_land {f : Row → Row} {d : Nat} (dom : ∀ r, bit (f r) (W d) = true) (v : Nat) :
    RF f (Nat.land v d) = RF f v := by
  funext r
  have h := dom r
  rw [bit_W] at h
  rw [rf_apply,rf_apply]
  have : (Nat.land v d).testBit (f r).val = (v.testBit (f r).val && d.testBit (f r).val) := Nat.testBit_and ..
  rw [this,h,Bool.and_true]
lemma rf_zero {f : Row → Row} : RF f 0 = fun _ => false := by
  funext r
  rw [rf_apply]
  exact Nat.zero_testBit _
lemma rf_dom {f : Row → Row} {d : Nat} (dom : ∀ r, bit (f r) (W d) = true) : RF f d = fun _ => true := by
  funext r
  exact dom r
lemma rf_xor {f : Row → Row} {d : Nat} (dom : ∀ r, bit (f r) (W d) = true) (m : Nat) :
    RF f (Nat.xor d m) = inv (RF f m) := by
  funext r
  have h := dom r
  rw [bit_W] at h
  change RF f (Nat.xor d m) r = !(RF f m r)
  rw [rf_apply,rf_apply]
  have : (Nat.xor d m).testBit (f r).val = ((d.testBit (f r).val) ^^ (m.testBit (f r).val)) := Nat.testBit_xor ..
  rw [this,h,Bool.true_xor]
lemma cn_ok {f : Row → Row} {d : Nat} (dom : ∀ r, bit (f r) (W d) = true) (v : Nat) : cn d v ≤ cost (RF f v) := by
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
lemma av_ok {f : Row → Row} {d : Nat} (dom : ∀ r, bit (f r) (W d) = true) {bank P v} (hP : PS f bank P)
    (h : av d P v = true) : Available true bank (RF f v) := by
  simp only [av,Bool.or_eq_true,List.any_eq_true] at h
  rw [←rf_land dom v]
  rcases h with (h | h) | ⟨x,hx,h | h⟩
  · rw [Nat.eq_of_beq_eq_true h,rf_zero]
    exact Or.inr (Or.inl ⟨false,rfl⟩)
  · rw [Nat.eq_of_beq_eq_true h,rf_dom dom]
    exact Or.inr (Or.inl ⟨true,rfl⟩)
  · rw [←Nat.eq_of_beq_eq_true h]
    exact hP x hx
  · have e := hP x hx
    rw [Nat.eq_of_beq_eq_true h,rf_xor dom] at e
    have e' := avail_inv rfl e
    rwa [inv_inv'] at e'
lemma pay_nb {f : Row → Row} {roots bank p P} (o a b : Nat) (hr : Reach true roots p bank) (hP : PS f bank P)
    (ha : Available true bank (RF f a)) (hb : Available true bank (RF f b)) :
    ∃ next, Reach true roots (p+1) next ∧ PS f next P ∧ Available true next (RF f (nb o a b)) ∧
      ∀ v, Available true bank v → Available true next v := by
  obtain ⟨e,he,heq⟩ := bin_four o
  have hn : RF f (nb o a b) = comb e (RF f a) (RF f b) := by
    unfold RF
    rw [W_nb,heq,obs_bin,restrict_comb]
  obtain ⟨op,x,y,e1,hx,hy,_,_⟩ := comb_prime (d:=e) (Or.inr ⟨rfl,he⟩) ha hb
  refine ⟨_,Reach.two op hr hx hy,fun v hv => available_cons _ (hP v hv),?_,fun v hv => available_cons _ hv⟩
  rw [hn,e1]
  exact Or.inl (by simp)
lemma getD_ps {f : Row → Row} {bank P} (hP : PS f bank P) (i : Nat) : Available true bank (RF f (P.getD i 0)) := by
  rw [List.getD_eq_getElem?_getD]
  cases h : P[i]? with
  | none => exact Or.inr (Or.inl ⟨false,rf_zero⟩)
  | some a => exact hP a (List.mem_of_getElem? h)
lemma mkPool_ok {f : Row → Row} {roots} (cs : List (Nat × Nat × Nat)) {bank p P} (hr : Reach true roots p bank)
    (hP : PS f bank P) : ∃ next, Reach true roots (p+cs.length) next ∧ PS f next (mkPool P cs) := by
  induction cs generalizing bank p P with
  | nil => exact ⟨bank,hr,hP⟩
  | cons c cs ih =>
    obtain ⟨next,h1,h2,h3,_⟩ := pay_nb c.1 _ _ hr hP (getD_ps hP c.2.1) (getD_ps hP c.2.2)
    have : PS f next (P ++ [nb c.1 (P.getD c.2.1 0) (P.getD c.2.2 0)]) := by
      intro v hv
      rcases List.mem_append.mp hv with hv | hv
      · exact h2 v hv
      · rw [List.mem_singleton.mp hv]
        exact h3
    obtain ⟨out,o1,o2⟩ := ih h1 this
    exact ⟨out,by rw [List.length_cons,show p+(cs.length+1) = p+1+cs.length by omega]; exact o1,o2⟩

abbrev CutV := Nat × Nat × Nat × List Nat
def keepB (d : Nat) (P : List Nat) (ka : Bool) (a : Nat) : Bool := bif ka then av d P a else true
def keepC (d : Nat) (ka : Bool) (a : Nat) : Nat := bif ka then cn d a else 0
def cutEval (k : Nat) (rest : List Nat) (a b z : Nat) (ka kb : Bool) (c : CutV) : Bool :=
  rest.all (av c.1 c.2.2.2) && keepB c.1 c.2.2.2 ka a && keepB c.1 c.2.2.2 kb b &&
  (bif av c.1 c.2.2.2 z then
    Nat.blt (Nat.add k c.2.2.1) (Nat.add c.2.1 (Nat.add (Nat.add (sumc c.1 rest) (cn c.1 z)) (Nat.add (keepC c.1 ka a) (keepC c.1 kb b))))
  else av c.1 c.2.2.2 a && av c.1 c.2.2.2 b &&
    Nat.blt (Nat.add (Nat.add k c.2.2.1) 1) (Nat.add c.2.1 (Nat.add (Nat.add (sumc c.1 rest) (cn c.1 z)) (Nat.add (keepC c.1 ka a) (keepC c.1 kb b)))))
def sepEval (rest : List Nat) (a b z : Nat) (ka kb : Bool) (p : Nat × Nat) : Bool :=
  let e := fun v => (Nat.testBit v p.1 == Nat.testBit v p.2)
  e z && (!ka || e a) && (!kb || e b) && rest.all e
def sepOK (T : Nat) (p : Nat × Nat) : Bool := Nat.blt p.1 128 && Nat.blt p.2 128 && (T.testBit p.1 != T.testBit p.2)

def kidW (rest : List Nat) (a b z : Nat) (ka kb : Bool) : List Sig :=
  W z :: kept ka (W a) (kept kb (W b) (rest.map W))
lemma sumc_ok {f : Row → Row} {d : Nat} (dom : ∀ r, bit (f r) (W d) = true) (l : List Nat) :
    sumc d l ≤ mass (l.map (RF f)) := by
  induction l with
  | nil => simp [sumc]
  | cons v l ih =>
    rw [List.map_cons,mass_cons]
    exact Nat.add_le_add (cn_ok dom v) ih
lemma mass_keep {f : Row → Row} {d : Nat} (dom : ∀ r, bit (f r) (W d) = true) (ka : Bool) (a : Nat) (l : List (Wire Row)) :
    keepC d ka a + mass l ≤ mass (kept ka (RF f a) l) := by
  cases ka
  · simp [keepC,kept]
  · rw [kept,if_pos rfl,mass_cons]
    exact Nat.add_le_add_right (cn_ok dom a) _
lemma kid_map (f : Row → Row) (rest : List Nat) (a b z : Nat) (ka kb : Bool) :
    ((kidW rest a b z ka kb).map observe).map (restrictRows f) =
      RF f z :: kept ka (RF f a) (kept kb (RF f b) (rest.map (RF f))) := by
  cases ka <;> cases kb <;> simp [kidW,kept,List.map_map,Function.comp_def,RF]

def CutP (R : List Nat) (T : Nat) (c : CutV) : Prop :=
  ∃ (f : Row → Row) (roots : List Sig) (bank : List (Wire Row)), (∀ r, bit (f r) (W c.1) = true) ∧
    ¬Constant (restrictRows f (observe (W T))) ∧ Reach true (roots.map observe) c.2.2.1 bank ∧ PS f bank c.2.2.2 ∧
    ∀ p bank, Reach true (roots.map observe) p bank → Available true bank (restrictRows f (observe (W T))) → c.2.1 ≤ p

lemma cut_sound {R T c k rest a b o ka kb} (hc : CutP R T c)
    (nd : (kidW rest a b (nb o a b) ka kb).Nodup)
    (h : cutEval k rest a b (nb o a b) ka kb c = true) :
    Impossible true (W T) k (kidW rest a b (nb o a b) ka kb).toFinset := by
  obtain ⟨f,roots,bank,dom,nc,hr,hP,lo⟩ := hc
  simp only [cutEval,Bool.and_eq_true,List.all_eq_true] at h
  obtain ⟨⟨⟨h1,h2⟩,h3⟩,h4⟩ := h
  have key : ∃ q bank', Reach true (roots.map observe) q bank' ∧ PS f bank' c.2.2.2 ∧ Available true bank' (RF f (nb o a b)) ∧
      k + q < c.2.1 + ((sumc c.1 rest + cn c.1 (nb o a b)) + (keepC c.1 ka a + keepC c.1 kb b)) := by
    cases hz : av c.1 c.2.2.2 (nb o a b)
    · rw [hz,cond_false,Bool.and_eq_true,Bool.and_eq_true,Nat.blt_eq] at h4
      obtain ⟨next,n1,n2,n3,_⟩ := pay_nb o a b hr hP (av_ok dom hP h4.1.1) (av_ok dom hP h4.1.2)
      refine ⟨_,next,n1,n2,n3,?_⟩
      have := h4.2
      exact this
    · rw [hz,cond_true,Nat.blt_eq] at h4
      exact ⟨_,bank,hr,hP,av_ok dom hP hz,h4⟩
  obtain ⟨q,bank',r1,r2,r3,r4⟩ := key
  intro k' hk run
  have supp : supply true bank' (((kidW rest a b (nb o a b) ka kb).map observe).map (restrictRows f)) := by
    rw [kid_map]
    intro v hv
    rcases List.mem_cons.mp hv with rfl | hv
    · exact r3
    have kb' : ∀ v ∈ kept kb (RF f b) (rest.map (RF f)), Available true bank' v := by
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

lemma sep_sound {T k rest a b o ka kb p} (hT : sepOK T p = true)
    (h : sepEval rest a b (nb o a b) ka kb p = true) :
    Impossible true (W T) k (kidW rest a b (nb o a b) ka kb).toFinset := by
  simp only [sepOK,Bool.and_eq_true,Nat.blt_eq,bne_iff_ne] at hT
  obtain ⟨⟨p1,p2⟩,hd⟩ := hT
  simp only [sepEval,Bool.and_eq_true,Bool.or_eq_true,Bool.not_eq_true',beq_iff_eq,List.all_eq_true] at h
  obtain ⟨⟨⟨h1,h2⟩,h3⟩,h4⟩ := h
  intro k' _ run
  obtain ⟨v,hv,hne⟩ := live_row_difference run (r:=⟨p.1,p1⟩) (s:=⟨p.2,p2⟩) (by rw [bit_W,bit_W]; exact hd)
  apply hne
  rw [List.mem_toFinset] at hv
  rcases List.mem_cons.mp hv with rfl | hv
  · rw [bit_W,bit_W]; exact h1
  rcases mem_kept hv with rfl | hv'
  · cases ka
    · cases kb
      · obtain ⟨x,hx,e⟩ := List.mem_map.mp hv
        rw [←e,bit_W,bit_W]; exact h4 x hx
      · rcases List.mem_cons.mp hv with e | hv
        · rw [e,bit_W,bit_W]; exact h3.resolve_left (by simp)
        · obtain ⟨x,hx,e⟩ := List.mem_map.mp hv
          rw [←e,bit_W,bit_W]; exact h4 x hx
    · rw [bit_W,bit_W]; exact h2.resolve_left (by simp)
  · cases kb
    · obtain ⟨x,hx,e⟩ := List.mem_map.mp hv'
      rw [←e,bit_W,bit_W]; exact h4 x hx
    · rcases List.mem_cons.mp hv' with e | hv
      · rw [e,bit_W,bit_W]; exact h3.resolve_left (by simp)
      · obtain ⟨x,hx,e⟩ := List.mem_map.mp hv
        rw [←e,bit_W,bit_W]; exact h4 x hx

abbrev StD := List Nat × List (Nat × List (Nat × Nat × Nat)) × List (Nat × Nat) × List (List Nat)
def dupD (l : List StD) : List StD := l.map fun st => (st.1.map (Nat.mul 0x10000000000000001),st.2)
def picks : List Nat → List (Nat × List Nat)
  | [] => []
  | x::xs => (x,xs) :: (picks xs).map fun p => (p.1,x::p.2)
def pairs : List Nat → List (Nat × Nat × List Nat)
  | [] => []
  | x::xs => ((picks xs).map fun p => (x,p.1,p.2)) ++ (pairs xs).map fun p => (p.1,p.2.1,x::p.2.2)
lemma picks_ok {l : List Nat} {a : Nat} (h : a ∈ l) : ∃ p ∈ picks l, p.1 = a ∧ (a::p.2).Perm l := by
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
lemma pairs_ok {l : List Nat} {a b : Nat} (ha : a ∈ l) (hb : b ∈ l) (hab : a ≠ b) :
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
lemma beqL_ok {a b : List Nat} (h : beqL a b = true) : a = b := by
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
lemma mem_ins {z v : Nat} {l : List Nat} : v ∈ ins z l ↔ v = z ∨ v ∈ l := by
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
lemma kid_fin (rest : List Nat) (a b z : Nat) (ka kb : Bool) :
    ((kidN rest a b z ka kb).map W).toFinset = (kidW rest a b z ka kb).toFinset := by
  ext v
  cases ka <;> cases kb <;> simp [kidN,kidW,kept,mem_ins] <;> aesop

end RestrictionSixProof

end PEqualNP.Outside.L_meta_10760

namespace PEqualNP.Outside.L_meta_10760.PairMatrix

def phaseA (p : Fin 4) : Bool := p.val.testBit 0

def phaseB (p : Fin 4) : Bool := p.val.testBit 1

def phaseCode (a b : Bool) : Fin 4 :=
  ⟨a.toNat + 2 * b.toNat, by cases a <;> cases b <;> decide⟩

lemma phaseCode_A (a b : Bool) : phaseA (phaseCode a b) = a := by
  cases a <;> cases b <;> decide

lemma phaseCode_B (a b : Bool) : phaseB (phaseCode a b) = b := by
  cases a <;> cases b <;> decide

def gate (o : Nat) (a b : Bool) : Bool :=
  if o = 0 then a && b else if o = 1 then a || b
  else if o = 2 then a ^^ (a && b) else b ^^ (a && b)

def collisionMask (o keep : Nat) : Nat :=
  [0x8777, 0x8525, 0x8433, 0x8421, 0xeee1, 0xa4a1, 0xcc21, 0x8421, 0xdd2d, 0x8525, 0xcc21, 0x8421, 0xb4bb, 0xa4a1, 0x8433, 0x8421].getD (4 * o + keep) 0

lemma collisionMask_bound : ∀ o keep : Fin 4,
    collisionMask o.val keep.val < 2 ^ 16 := by
  decide +kernel

lemma collisionMask_bit : ∀ o keep p q : Fin 4,
    (collisionMask o.val keep.val).testBit (4 * p.val + q.val) =
      ((gate o.val (phaseA p) (phaseB p) == gate o.val (phaseA q) (phaseB q)) &&
       (!keep.val.testBit 0 || (phaseA p == phaseA q)) &&
       (!keep.val.testBit 1 || (phaseB p == phaseB q))) := by
  decide +kernel

lemma collisionMask_sound (o keep p q : Fin 4)
    (h : (collisionMask o.val keep.val).testBit (4 * p.val + q.val) = true) :
    gate o.val (phaseA p) (phaseB p) = gate o.val (phaseA q) (phaseB q) ∧
      (keep.val.testBit 0 = false ∨ phaseA p = phaseA q) ∧
      (keep.val.testBit 1 = false ∨ phaseB p = phaseB q) := by
  rw [collisionMask_bit] at h
  simpa only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true',
    beq_iff_eq, and_assoc] using h

end PEqualNP.Outside.L_meta_10760.PairMatrix

namespace PEqualNP.Outside.L_meta_10760.PairMatrix

open RestrictionSixProof

/-- Every represented phase pair has an actual pair of oppositely labelled rows.
  The two rows agree on every wire outside the chosen operands. -/
def MatrixSupports (T : Nat) (rest : List Nat) (a b matrix : Nat) : Prop :=
  ∀ p q : Fin 4, matrix.testBit (4 * p.val + q.val) = true →
    ∃ r s : Row,
      T.testBit r.val = true ∧ T.testBit s.val = false ∧
      (∀ v ∈ rest, v.testBit r.val = v.testBit s.val) ∧
      a.testBit r.val = phaseA p ∧ b.testBit r.val = phaseB p ∧
      a.testBit s.val = phaseA q ∧ b.testBit s.val = phaseB q

lemma nb_bit (o a b r : Nat) :
    (nb o a b).testBit r = gate o (a.testBit r) (b.testBit r) := by
  by_cases h0 : o = 0
  · subst o
    exact tb_land a b r
  by_cases h1 : o = 1
  · subst o
    exact tb_lor a b r
  by_cases h2 : o = 2
  · subst o
    change (Nat.xor a (Nat.land a b)).testBit r = _
    rw [tb_xor, tb_land]
    rfl
  · unfold nb gate
    rw [nbeq h0, nbeq h1, nbeq h2, ite_eq_right h0, ite_eq_right h1,
      ite_eq_right h2]
    exact (tb_xor b (Nat.land a b) r).trans (by rw [tb_land])

lemma overlap_phases {matrix mask : Nat}
    (bounded : mask < 2 ^ 16) (overlap : Nat.land matrix mask ≠ 0) :
    ∃ p q : Fin 4,
      matrix.testBit (4 * p.val + q.val) = true ∧
      mask.testBit (4 * p.val + q.val) = true := by
  obtain ⟨i, hi⟩ := Nat.exists_testBit_of_ne_zero overlap
  rw [tb_land, Bool.and_eq_true] at hi
  have ilt : i < 16 := by
    by_contra h
    have hp : 2 ^ 16 ≤ 2 ^ i := Nat.pow_le_pow_right (by decide) (by omega)
    have hz := Nat.testBit_lt_two_pow (bounded.trans_le hp)
    rw [hi.2] at hz
    contradiction
  let p : Fin 4 := ⟨i / 4, by omega⟩
  let q : Fin 4 := ⟨i % 4, by omega⟩
  have he : 4 * p.val + q.val = i := by dsimp [p, q]; omega
  exact ⟨p, q, by simpa only [he] using hi⟩

lemma sepOK_of_rows {T : Nat} (r s : Row)
    (positive : T.testBit r.val = true) (negative : T.testBit s.val = false) :
    sepOK T (r.val, s.val) = true := by
  simp only [sepOK, Bool.and_eq_true, Nat.blt_eq, bne_iff_ne]
  exact ⟨⟨r.isLt, s.isLt⟩, by rw [positive, negative]; decide⟩

lemma sepEval_of_rows {rest : List Nat} {a b z : Nat} {ka kb : Bool}
    (r s : Row)
    (output : z.testBit r.val = z.testBit s.val)
    (keepA : ka = false ∨ a.testBit r.val = a.testBit s.val)
    (keepB : kb = false ∨ b.testBit r.val = b.testBit s.val)
    (other : ∀ v ∈ rest, v.testBit r.val = v.testBit s.val) :
    sepEval rest a b z ka kb (r.val, s.val) = true := by
  simpa only [sepEval, Bool.and_eq_true, Bool.or_eq_true,
    Bool.not_eq_true', beq_iff_eq, List.all_eq_true] using
      And.intro (And.intro (And.intro output keepA) keepB) other

lemma sep_witness_of_matrix {T : Nat} {rest : List Nat} {a b matrix : Nat}
    (o keep : Fin 4) (support : MatrixSupports T rest a b matrix)
    (overlap : Nat.land matrix (collisionMask o.val keep.val) ≠ 0) :
    ∃ rows : Nat × Nat,
      sepOK T rows = true ∧
      sepEval rest a b (nb o.val a b)
        (keep.val.testBit 0) (keep.val.testBit 1) rows = true := by
  obtain ⟨p, q, hp, hq⟩ := overlap_phases (collisionMask_bound o keep) overlap
  obtain ⟨r, s, hr, hs, hrest, har, hbr, has, hbs⟩ := support p q hp
  obtain ⟨hz, hka, hkb⟩ := collisionMask_sound o keep p q hq
  refine ⟨(r.val, s.val), sepOK_of_rows r s hr hs, ?_⟩
  apply sepEval_of_rows r s
  · rw [nb_bit, nb_bit, har, hbr, has, hbs]
    exact hz
  · simpa only [har, has] using hka
  · simpa only [hbr, hbs] using hkb
  · exact hrest

lemma matrix_impossible {T k : Nat} {rest : List Nat} {a b matrix : Nat}
    (o keep : Fin 4) (support : MatrixSupports T rest a b matrix)
    (overlap : Nat.land matrix (collisionMask o.val keep.val) ≠ 0) :
    Impossible true (W T) k
      (kidW rest a b (nb o.val a b)
        (keep.val.testBit 0) (keep.val.testBit 1)).toFinset := by
  obtain ⟨rows, hT, hsep⟩ := sep_witness_of_matrix o keep support overlap
  exact sep_sound hT hsep

lemma matrix_impossible_kidN {T k : Nat} {rest : List Nat} {a b matrix : Nat}
    (o keep : Fin 4) (support : MatrixSupports T rest a b matrix)
    (overlap : Nat.land matrix (collisionMask o.val keep.val) ≠ 0) :
    Impossible true (W T) k
      ((kidN rest a b (nb o.val a b)
        (keep.val.testBit 0) (keep.val.testBit 1)).map W).toFinset := by
  rw [kid_fin]
  exact matrix_impossible o keep support overlap

end PEqualNP.Outside.L_meta_10760.PairMatrix

namespace PEqualNP.Outside.L_meta_10760.PairMatrix

open RestrictionSixProof

def rowClass (s w : Nat) : Nat :=
  if w.testBit s then w else Nat.xor w full

def phaseWord (a b p : Nat) : Nat :=
  Nat.land (if p.testBit 0 then a else Nat.xor a full)
    (if p.testBit 1 then b else Nat.xor b full)

lemma full_bit {r : Nat} (hr : r < 128) : full.testBit r = true := by
  change (2 ^ 128 - 1).testBit r = true
  rw [Nat.testBit_two_pow_sub_one]
  exact decide_eq_true hr

lemma classWord_agrees {r w : Nat} {value : Bool} (hr : r < 128)
    (h : (if value then w else Nat.xor w full).testBit r = true) :
    w.testBit r = value := by
  cases value
  · change (Nat.xor w full).testBit r = true at h
    rw [tb_xor, full_bit hr] at h
    cases hw : w.testBit r <;> simp_all
  · exact h

lemma rowClass_agrees {r s w : Nat} (hr : r < 128)
    (h : (rowClass s w).testBit r = true) : w.testBit r = w.testBit s := by
  exact classWord_agrees hr h

lemma phaseWord_agrees {a b r : Nat} (p : Fin 4) (hr : r < 128)
    (h : (phaseWord a b p.val).testBit r = true) :
    a.testBit r = phaseA p ∧ b.testBit r = phaseB p := by
  unfold phaseWord at h
  rw [tb_land, Bool.and_eq_true] at h
  exact ⟨classWord_agrees hr h.1, classWord_agrees hr h.2⟩

lemma bounded_true_bit {T r : Nat} (bound : T < 2 ^ 128)
    (bit : T.testBit r = true) : r < 128 := by
  by_contra h
  have hp : 2 ^ 128 ≤ 2 ^ r := Nat.pow_le_pow_right (by decide) (by omega)
  have hz := Nat.testBit_lt_two_pow (bound.trans_le hp)
  rw [bit] at hz
  contradiction

end PEqualNP.Outside.L_meta_10760.PairMatrix

namespace PEqualNP.Outside.L_meta_10760.AutoPool

def full : Nat := 0xffffffffffffffffffffffffffffffff

def op (o a b : Nat) : Nat :=
  if o == 0 then a &&& b else if o == 1 then a ||| b
  else if o == 2 then a ^^^ (a &&& b) else b ^^^ (a &&& b)

def collisionMasks : List Nat := [34679, 34085, 33843, 33825, 61153, 42145, 52257, 33825, 56621, 34085, 52257, 33825, 46267, 42145, 33843, 33825]

def phaseMask (a b p : Nat) : Nat :=
  (if p.testBit 0 then a else full ^^^ a) &&&
    (if p.testBit 1 then b else full ^^^ b)

def phaseMatrix (target : Nat) (negativeRows : List Nat) (a b : Nat) (rest : List Nat) : Nat :=
  negativeRows.foldl (fun bad r =>
    let same := rest.foldl (fun same w => same &&&
      (if w.testBit r then w else full ^^^ w)) target
    let q := (if a.testBit r then 1 else 0) + (if b.testBit r then 2 else 0)
    (List.range 4).foldl (fun bad p =>
      if same &&& phaseMask a b p != 0 then bad ||| (1 <<< (4*p+q)) else bad) bad) 0

def forceNat {α : Sort u} (n : Nat) (f : Nat → α) : α :=
  match n with
  | 0 => f 0
  | k+1 => f (k+1)

end PEqualNP.Outside.L_meta_10760.AutoPool

namespace PEqualNP.Outside.L_meta_10760.AutoPool

open RestrictionSixProof

lemma phaseMatrix_op_eq_nb (o a b : Nat) : op o a b = nb o a b := by
  simp only [op, nb, Bool.cond_eq_ite, Nat.beq_eq, beq_iff_eq,
    Nat.land_eq, Nat.lor_eq, Nat.xor_eq]

lemma collisionMasks_eq (o keep : Nat) :
    collisionMasks.getD (4 * o + keep) 0 = PairMatrix.collisionMask o keep := rfl

lemma phaseMatrix_forceNat_eq {α : Sort u} (n : Nat) (f : Nat → α) : forceNat n f = f n := by
  cases n <;> rfl

lemma full_xor_eq (w : Nat) : full ^^^ w = Nat.xor w RestrictionSixProof.full := by
  change (RestrictionSixProof.full ^^^ w) = (w ^^^ RestrictionSixProof.full)
  exact Nat.xor_comm _ _

lemma phaseMask_eq (a b p : Nat) : phaseMask a b p = PairMatrix.phaseWord a b p := by
  simp only [phaseMask, PairMatrix.phaseWord, full_xor_eq]
  rfl

lemma rowClass_eq (s w : Nat) :
    (if w.testBit s then w else full ^^^ w) = PairMatrix.rowClass s w := by
  simp only [PairMatrix.rowClass, full_xor_eq]

lemma foldlAnd_support {α : Type} (xs : List α) (f : α → Nat) (initial i : Nat)
    (h : (xs.foldl (fun acc x => acc &&& f x) initial).testBit i = true) :
    initial.testBit i = true ∧ ∀ x ∈ xs, (f x).testBit i = true := by
  induction xs generalizing initial with
  | nil => exact ⟨h, by simp⟩
  | cons x xs ih =>
    obtain ⟨hx, hxs⟩ := ih (initial &&& f x) h
    rw [Nat.testBit_and, Bool.and_eq_true] at hx
    refine ⟨hx.1, ?_⟩
    intro y hy
    rcases List.mem_cons.mp hy with rfl | hy
    · exact hx.2
    · exact hxs y hy

lemma actual_phase_witness {target : Nat} {rest : List Nat} {a b s : Nat}
    (p : Fin 4) (bound : target < 2 ^ 128)
    (overlap :
      (rest.foldl (fun same w => same &&&
        (if w.testBit s then w else full ^^^ w)) target) &&& phaseMask a b p.val ≠ 0) :
    ∃ r : Row, target.testBit r.val = true ∧
      (∀ w ∈ rest, w.testBit r.val = w.testBit s) ∧
      a.testBit r.val = PairMatrix.phaseA p ∧
      b.testBit r.val = PairMatrix.phaseB p := by
  obtain ⟨r, hr⟩ := Nat.exists_testBit_of_ne_zero overlap
  rw [Nat.testBit_and, Bool.and_eq_true] at hr
  obtain ⟨ht, hrest⟩ := foldlAnd_support rest _ target r hr.1
  have rb := PairMatrix.bounded_true_bit bound ht
  refine ⟨⟨r, rb⟩, ht, ?_, ?_⟩
  · intro w hw
    apply PairMatrix.rowClass_agrees rb
    simpa only [rowClass_eq] using hrest w hw
  · rw [phaseMask_eq] at hr
    exact PairMatrix.phaseWord_agrees p rb hr.2

lemma foldl_preserves {α β : Type} (P : β → Prop) (f : β → α → β)
    (xs : List α) (initial : β) (start : P initial)
    (step : ∀ x ∈ xs, ∀ acc, P acc → P (f acc x)) : P (xs.foldl f initial) := by
  induction xs generalizing initial with
  | nil => exact start
  | cons x xs ih =>
    apply ih (f initial x) (step x List.mem_cons_self initial start)
    intro y hy acc ha
    exact step y (List.mem_cons_of_mem x hy) acc ha

lemma matrixSupports_or {target : Nat} {rest : List Nat} {a b left right : Nat}
    (hl : PairMatrix.MatrixSupports target rest a b left)
    (hr : PairMatrix.MatrixSupports target rest a b right) :
    PairMatrix.MatrixSupports target rest a b (left ||| right) := by
  intro p q h
  rw [Nat.testBit_or, Bool.or_eq_true] at h
  exact h.elim (hl p q) (hr p q)

lemma matrixSupports_singleton {target : Nat} {rest : List Nat} {a b : Nat}
    (p q : Fin 4)
    (witness : ∃ r s : Row,
      target.testBit r.val = true ∧ target.testBit s.val = false ∧
      (∀ v ∈ rest, v.testBit r.val = v.testBit s.val) ∧
      a.testBit r.val = PairMatrix.phaseA p ∧
      b.testBit r.val = PairMatrix.phaseB p ∧
      a.testBit s.val = PairMatrix.phaseA q ∧
      b.testBit s.val = PairMatrix.phaseB q) :
    PairMatrix.MatrixSupports target rest a b (1 <<< (4 * p.val + q.val)) := by
  intro p' q' h
  rw [Nat.one_shiftLeft, Nat.testBit_two_pow] at h
  have he := of_decide_eq_true h
  have pb := p.isLt
  have qb := q.isLt
  have pb' := p'.isLt
  have qb' := q'.isLt
  have hp : p = p' := Fin.ext (by omega)
  have hq : q = q' := Fin.ext (by omega)
  simpa only [← hp, ← hq] using witness

lemma phaseMatrix_support {target : Nat} {rest : List Nat} {a b : Nat}
    (negativeRows : List Nat) (bound : target < 2 ^ 128)
    (negative : ∀ s ∈ negativeRows, s < 128 ∧ target.testBit s = false) :
    PairMatrix.MatrixSupports target rest a b (phaseMatrix target negativeRows a b rest) := by
  unfold phaseMatrix
  apply foldl_preserves (PairMatrix.MatrixSupports target rest a b)
  · intro p q h
    simp at h
  · intro s hs bad hbad
    dsimp only
    apply foldl_preserves (PairMatrix.MatrixSupports target rest a b) _ _ bad hbad
    intro p hp acc hacc
    split
    next overlap =>
      apply matrixSupports_or hacc
      have pb : p < 4 := List.mem_range.mp hp
      let pf : Fin 4 := ⟨p, pb⟩
      let q := PairMatrix.phaseCode (a.testBit s) (b.testBit s)
      have qeq : (if a.testBit s then 1 else 0) + (if b.testBit s then 2 else 0) = q.val := by
        dsimp [q, PairMatrix.phaseCode]
        cases a.testBit s <;> cases b.testBit s <;> rfl
      rw [qeq]
      apply matrixSupports_singleton pf q
      have overlap' :
          (rest.foldl (fun same w => same &&&
            (if w.testBit s then w else full ^^^ w)) target) &&& phaseMask a b pf.val ≠ 0 := by
        simpa only [bne_iff_ne] using overlap
      obtain ⟨r, hr, hrest, ha, hb⟩ := actual_phase_witness pf bound overlap'
      refine ⟨r, ⟨s, (negative s hs).1⟩, hr, (negative s hs).2, hrest, ha, hb, ?_, ?_⟩
      · exact (PairMatrix.phaseCode_A _ _).symm
      · exact (PairMatrix.phaseCode_B _ _).symm
    next noOverlap => exact hacc

lemma raw_child_fin (rest : List Nat) (a b z : Nat) (ka kb : Bool) :
    ((z :: ((if ka then [a] else []) ++ (if kb then [b] else []) ++ rest)).map W).toFinset =
      (kidW rest a b z ka kb).toFinset := by
  cases ka <;> cases kb <;> rfl

lemma phaseMatrix_impossible_raw {target k : Nat} {rest : List Nat} {a b : Nat}
    (negativeRows : List Nat) (bound : target < 2 ^ 128)
    (negative : ∀ s ∈ negativeRows, s < 128 ∧ target.testBit s = false)
    (o keep : Fin 4)
    (overlap : phaseMatrix target negativeRows a b rest &&&
      collisionMasks.getD (4 * o.val + keep.val) 0 ≠ 0) :
    Impossible true (W target) k
      ((op o.val a b :: ((if keep.val.testBit 0 then [a] else []) ++
        (if keep.val.testBit 1 then [b] else []) ++ rest)).map W).toFinset := by
  rw [raw_child_fin, phaseMatrix_op_eq_nb]
  apply PairMatrix.matrix_impossible o keep (phaseMatrix_support negativeRows bound negative)
  simpa only [collisionMasks_eq, Nat.land_eq] using overlap

lemma phaseMatrix_impossible_kidN {target k : Nat} {rest : List Nat} {a b : Nat}
    (negativeRows : List Nat) (bound : target < 2 ^ 128)
    (negative : ∀ s ∈ negativeRows, s < 128 ∧ target.testBit s = false)
    (o keep : Fin 4)
    (overlap : phaseMatrix target negativeRows a b rest &&&
      collisionMasks.getD (4 * o.val + keep.val) 0 ≠ 0) :
    Impossible true (W target) k
      ((kidN rest a b (op o.val a b)
        (keep.val.testBit 0) (keep.val.testBit 1)).map W).toFinset := by
  rw [phaseMatrix_op_eq_nb]
  apply PairMatrix.matrix_impossible_kidN o keep (phaseMatrix_support negativeRows bound negative)
  simpa only [collisionMasks_eq, Nat.land_eq] using overlap

end PEqualNP.Outside.L_meta_10760.AutoPool

namespace PEqualNP.Outside.L_meta_10760

section Live

variable {α : Type} [DecidableEq α]

def build (ops : α → α → Finset α) (goal : α) : ℕ → Finset α → Prop
  | 0, available => goal ∈ available
  | k + 1, available => build ops goal k available ∨
    ∃ a ∈ available, ∃ b ∈ available, a ≠ b ∧
      ∃ z ∈ ops a b, build ops goal k (insert z available)

def live (ops : α → α → Finset α) (goal : α) : ℕ → Finset α → Prop
  | 0, s => s = {goal}
  | k + 1, s => live ops goal k s ∨
    ∃ a ∈ s, ∃ b ∈ s, a ≠ b ∧ ∃ z ∈ ops a b, z ∉ s ∧
      ∃ rest : Finset α, s = insert a (insert b rest) ∧ live ops goal k (insert z rest)

lemma compress {ops : α → α → Finset α} {goal : α} {k : ℕ} {available : Finset α}
    (h : build ops goal k available) : ∃ s ⊆ available, live ops goal k s := by
  induction k generalizing available with
  | zero =>
    exact ⟨{goal}, Finset.singleton_subset_iff.mpr h, rfl⟩
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, tail⟩
    · obtain ⟨s, hs, hrun⟩ := ih skip
      exact ⟨s, hs, Or.inl hrun⟩
    · obtain ⟨t, ht, hrun⟩ := ih tail
      by_cases sub : t ⊆ available
      · exact ⟨t, sub, Or.inl hrun⟩
      · have hzmem : z ∈ t := by
          by_contra hn
          apply sub
          intro u hu
          rcases Finset.mem_insert.mp (ht hu) with rfl | ok
          · exact False.elim (hn hu)
          · exact ok
        have hzout : z ∉ available := by
          intro hh
          exact sub ((Finset.insert_eq_of_mem hh) ▸ ht)
        let rest := t.erase z
        have hrest : rest ⊆ available := by
          intro u hu
          have hu' := Finset.mem_erase.mp hu
          exact (Finset.mem_insert.mp (ht hu'.2)).resolve_left hu'.1
        let s := insert a (insert b rest)
        have hs : s ⊆ available := Finset.insert_subset ha (Finset.insert_subset hb hrest)
        refine ⟨s, hs, Or.inr ⟨a, by simp [s], b, by simp [s], hab, z, hz,
          fun h => hzout (hs h), rest, rfl, ?_⟩⟩
        simpa [rest, Finset.insert_erase hzmem] using hrun

lemma live_card {ops : α → α → Finset α} {goal : α} {k : ℕ} {s : Finset α}
    (h : live ops goal k s) : s.card ≤ k + 1 := by
  induction k generalizing s with
  | zero => change s = {goal} at h; simp [h]
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, hout, rest, rfl, tail⟩
    · exact (ih skip).trans (by omega)
    · have hzrest : z ∉ rest := fun hm => hout (by simp [hm])
      have htail := ih tail
      rw [Finset.card_insert_of_notMem hzrest] at htail
      have h₁ := Finset.card_insert_le a (insert b rest)
      have h₂ := Finset.card_insert_le b rest
      omega

lemma live_separates {ops : α → α → Finset α} {goal : α} (D : α → Prop)
    (hd : D goal) (hops : ∀ a b, ∀ z ∈ ops a b, D z → D a ∨ D b)
    {k : ℕ} {s : Finset α} (h : live ops goal k s) : ∃ w ∈ s, D w := by
  induction k generalizing s with
  | zero => change s = {goal} at h; exact ⟨goal, by simp [h], hd⟩
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, hout, rest, rfl, tail⟩
    · exact ih skip
    · obtain ⟨w, hw, hD⟩ := ih tail
      rcases Finset.mem_insert.mp hw with rfl | hw
      · rcases hops a b w hz hD with h | h
        · exact ⟨a, ha, h⟩
        · exact ⟨b, hb, h⟩
      · exact ⟨w, by simp [hw], hD⟩

lemma first_live {ops : α → α → Finset α} {goal : α} {k : ℕ} {s : Finset α}
    (h : live ops goal (k + 1) s) :
    s = {goal} ∨
    ∃ a ∈ s, ∃ b ∈ s, a ≠ b ∧ ∃ z ∈ ops a b, z ∉ s ∧
      ∃ rest : Finset α, s = insert a (insert b rest) ∧ live ops goal k (insert z rest) := by
  induction k with
  | zero => exact h
  | succ k ih =>
    rcases h with skip | step
    · rcases ih skip with done | ⟨a, ha, b, hb, hab, z, hz, hn, r, hs, tail⟩
      · exact .inl done
      · exact .inr ⟨a, ha, b, hb, hab, z, hz, hn, r, hs, Or.inl tail⟩
    · exact .inr step

end Live

variable {width : Nat}

def ops (x y : BitVec width) : List (BitVec width) :=
  [x &&& y, x ||| y, x &&& ~~~y, y &&& ~~~x]

abbrev basicOps (a b : BitVec width) : Finset (BitVec width) := (ops a b).toFinset

def uniqueSep {width : Nat} (S : Finset (BitVec width)) (a : BitVec width)
    (p q : Fin width) : Prop :=
  a[p.val] ≠ a[q.val] ∧ ∀ w ∈ S, w ≠ a → w[p.val] = w[q.val]

def criticalPair {width : Nat} (target : BitVec width) (S : Finset (BitVec width))
    (a b : BitVec width) : Prop :=
  a ∈ S ∧ b ∈ S ∧ a ≠ b ∧ ∃ p q ra rb sa sb : Fin width,
    target[p.val] = true ∧ target[q.val] = false ∧
    target[ra.val] = false ∧ target[rb.val] = false ∧
    target[sa.val] = true ∧ target[sb.val] = true ∧
    uniqueSep S a p ra ∧ uniqueSep S b p rb ∧
    uniqueSep S a sa q ∧ uniqueSep S b sb q ∧
    a[p.val] = a[sa.val] ∧ b[p.val] = b[sb.val]


lemma ops_equal_bits {width : Nat} {a b z : BitVec width} {p q : Fin width}
    (hz : z ∈ basicOps a b) (ha : a[p.val] = a[q.val])
    (hb : b[p.val] = b[q.val]) : z[p.val] = z[q.val] := by
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons,
    List.not_mem_nil, or_false] at hz
  rcases hz with rfl | rfl | rfl | rfl <;> simp [ha, hb]

lemma live_target_separates {width k : Nat} {target g : BitVec width}
    {S : Finset (BitVec width)} (run : live basicOps g k S)
    (hg : g = target ∨ g = ~~~target) {p q : Fin width}
    (different : target[p.val] ≠ target[q.val]) :
    ∃ w ∈ S, w[p.val] ≠ w[q.val] := by
  apply live_separates (fun w : BitVec width => w[p.val] ≠ w[q.val]) ?_ ?_ run
  · rcases hg with rfl | rfl
    · exact different
    · simpa using different
  · intro a b z hz hd
    by_cases ha : a[p.val] = a[q.val]
    · right
      intro hb
      exact hd (ops_equal_bits hz ha hb)
    · exact Or.inl ha

lemma uniqueSep_step {width k : Nat} {target g a b z c : BitVec width}
    {U : Finset (BitVec width)} {p q : Fin width}
    (hz : z ∈ basicOps a b) (run : live basicOps g k (insert z U))
    (hg : g = target ∨ g = ~~~target)
    (different : target[p.val] ≠ target[q.val])
    (ha : c = a → a ∉ U) (hb : c = b → b ∉ U)
    (hs : uniqueSep (insert a (insert b U)) c p q) :
    uniqueSep (insert z U) (if c = a ∨ c = b then z else c) p q := by
  by_cases hc : c = a ∨ c = b
  · rw [ite_eq_left hc]
    have hcU : c ∉ U := by
      rcases hc with rfl | rfl
      · exact ha rfl
      · exact hb rfl
    have hU : ∀ w ∈ U, w[p.val] = w[q.val] := by
      intro w hw
      apply hs.2 w (by simp [hw])
      intro eq
      exact hcU (eq ▸ hw)
    constructor
    · obtain ⟨w, hw, hd⟩ := live_target_separates run hg different
      rcases Finset.mem_insert.mp hw with rfl | hw
      · exact hd
      · exact False.elim (hd (hU w hw))
    · intro w hw hne
      exact hU w ((Finset.mem_insert.mp hw).resolve_left hne)
  · rw [ite_eq_right hc]
    refine ⟨hs.1, ?_⟩
    intro w hw hne
    rcases Finset.mem_insert.mp hw with rfl | hw
    · apply ops_equal_bits hz
      · exact hs.2 a (by simp) (fun eq => hc (.inl eq.symm))
      · exact hs.2 b (by simp) (fun eq => hc (.inr eq.symm))
    · exact hs.2 w (by simp [hw]) hne

namespace ChromGate

def eval (d : Fin 4) (a b : Bool) : Bool :=
  match d.val with
  | 0 => a && b
  | 1 => a || b
  | 2 => a && !b
  | _ => b && !a

lemma left_transport : ∀ (d : Fin 4)
    (a₀ a₁ a₂ a₃ b₀ b₁ b₂ b₃ : Bool),
    b₀ = b₁ → b₂ = b₃ →
    eval d a₀ b₀ ≠ eval d a₁ b₁ →
    eval d a₂ b₂ ≠ eval d a₃ b₃ →
    a₀ = a₂ → eval d a₀ b₀ = eval d a₂ b₂ := by
  decide

lemma right_transport : ∀ (d : Fin 4)
    (a₀ a₁ a₂ a₃ b₀ b₁ b₂ b₃ : Bool),
    a₀ = a₁ → a₂ = a₃ →
    eval d a₀ b₀ ≠ eval d a₁ b₁ →
    eval d a₂ b₂ ≠ eval d a₃ b₃ →
    b₀ = b₂ → eval d a₀ b₀ = eval d a₂ b₂ := by
  decide

lemma rectangle_false : ∀ (d : Fin 4) (a b c e : Bool),
    eval d a b ≠ eval d c b →
    eval d a b ≠ eval d a e →
    eval d c e ≠ eval d a e →
    eval d c e ≠ eval d c b → False := by
  decide

lemma sensitive_corner_unique : ∀ (d : Fin 4) (a b c e : Bool),
    eval d a b ≠ eval d (!a) b →
    eval d a b ≠ eval d a (!b) →
    eval d c e ≠ eval d (!c) e →
    eval d c e ≠ eval d c (!e) → a = c ∧ b = e := by
  decide

lemma opposite_corners_false : ∀ (d : Fin 4) (a b : Bool),
    eval d a b ≠ eval d (!a) b →
    eval d a b ≠ eval d a (!b) →
    eval d (!a) (!b) ≠ eval d a (!b) →
    eval d (!a) (!b) ≠ eval d (!a) b → False := by
  decide

def word {width : Nat} (d : Fin 4) (a b : BitVec width) : BitVec width :=
  match d.val with
  | 0 => a &&& b
  | 1 => a ||| b
  | 2 => a &&& ~~~b
  | _ => b &&& ~~~a

lemma word_get {width : Nat} (d : Fin 4) (a b : BitVec width) (p : Fin width) :
    (word d a b)[p.val] = eval d a[p.val] b[p.val] := by
  fin_cases d <;> simp [word, eval]

lemma of_basicOps {width : Nat} {a b z : BitVec width}
    (hz : z ∈ basicOps a b) : ∃ d : Fin 4, z = word d a b := by
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil,
    or_false] at hz
  rcases hz with rfl | rfl | rfl | rfl
  · exact ⟨0, rfl⟩
  · exact ⟨1, rfl⟩
  · exact ⟨2, rfl⟩
  · exact ⟨3, rfl⟩

end ChromGate

namespace ChromGeneric

variable {α : Type} [DecidableEq α]

lemma retained_card {a b z : α} {rest : Finset α}
    (hab : a ≠ b) (hz : z ∉ insert a (insert b rest)) :
    (insert a (insert b rest)).card +
        ((if a ∈ rest then 1 else 0) + (if b ∈ rest then 1 else 0)) =
      (insert z rest).card + 1 := by
  have hzr : z ∉ rest := fun h => hz (by simp [h])
  rw [Finset.card_insert_of_notMem hzr]
  by_cases ha : a ∈ rest <;> by_cases hb : b ∈ rest
  · simp [ha, hb]
  · have ha' : a ∈ insert b rest := by simp [ha]
    simp [Finset.insert_eq_of_mem ha', Finset.card_insert_of_notMem hb, ha, hb]
  · have ha' : a ∉ insert b rest := by simp [hab, ha]
    simp [Finset.card_insert_of_notMem ha', Finset.insert_eq_of_mem hb, ha, hb]
  · have ha' : a ∉ insert b rest := by simp [hab, ha]
    simp [Finset.card_insert_of_notMem ha', Finset.card_insert_of_notMem hb, ha, hb]

def collapse (a b z c : α) : α := if c = a ∨ c = b then z else c

lemma collapse_mem {a b z c : α} {rest : Finset α}
    (hc : c ∈ insert a (insert b rest)) :
    collapse a b z c ∈ insert z rest := by
  unfold collapse
  split_ifs with h
  · simp
  · simp only [Finset.mem_insert] at hc ⊢
    exact Or.inr ((hc.resolve_left (fun hca => h (Or.inl hca))).resolve_left
      (fun hcb => h (Or.inr hcb)))


lemma extend_coloring {edge : Finset α → α → α → Prop}
    (irrefl : ∀ S c, ¬ edge S c c)
    {a b z : α} {U : Finset α} (hab : a ≠ b)
    (hnew : z ∉ insert a (insert b U))
    (transport : ∀ c ∈ insert a (insert b U), ∀ d ∈ insert a (insert b U),
      edge (insert a (insert b U)) c d →
      (c = a → a ∉ U) → (c = b → b ∉ U) →
      (d = a → a ∉ U) → (d = b → b ∉ U) →
      edge (insert z U) (collapse a b z c) (collapse a b z d))
    {x : Nat} {f : α → Nat}
    (fbound : ∀ c ∈ insert z U, f c ≤ x)
    (fproper : ∀ c ∈ insert z U, ∀ d ∈ insert z U,
      edge (insert z U) c d → f c ≠ f d) :
    ∃ g : α → Nat,
      (∀ c ∈ insert a (insert b U),
        g c ≤ x + ((if a ∈ U then 1 else 0) + (if b ∈ U then 1 else 0))) ∧
      ∀ c ∈ insert a (insert b U), ∀ d ∈ insert a (insert b U),
        edge (insert a (insert b U)) c d → g c ≠ g d := by
  let base : α → Nat := fun c => f (collapse a b z c)
  have hbase : ∀ c ∈ insert a (insert b U), base c ≤ x := by
    intro c hc
    exact fbound _ (collapse_mem hc)
  have hproper : ∀ c ∈ insert a (insert b U), ∀ d ∈ insert a (insert b U),
      edge (insert a (insert b U)) c d →
      ¬ (c = a ∧ a ∈ U) → ¬ (c = b ∧ b ∈ U) →
      ¬ (d = a ∧ a ∈ U) → ¬ (d = b ∧ b ∈ U) → base c ≠ base d := by
    intro c hc d hd he hca hcb hda hdb
    apply fproper _ (collapse_mem hc) _ (collapse_mem hd)
    apply transport c hc d hd he
    · intro h hmem; exact hca ⟨h, hmem⟩
    · intro h hmem; exact hcb ⟨h, hmem⟩
    · intro h hmem; exact hda ⟨h, hmem⟩
    · intro h hmem; exact hdb ⟨h, hmem⟩
  let g : α → Nat := fun c =>
    if c = a ∧ a ∈ U then x + 1
    else if c = b ∧ b ∈ U then x + 1 + (if a ∈ U then 1 else 0)
    else base c
  refine ⟨g, ?_, ?_⟩
  · intro c hc
    have hh := hbase c hc
    dsimp only [g]
    by_cases ha : a ∈ U <;> by_cases hb : b ∈ U
    all_goals simp only [ha, hb, and_true, and_false, ite_true, ite_false]
    all_goals first | omega | (split_ifs <;> omega)
  · intro c hc d hd he heq
    have hcBound := hbase c hc
    have hdBound := hbase d hd
    have hcd : c ≠ d := by
      intro h
      subst d
      exact irrefl _ _ he
    by_cases hca : c = a ∧ a ∈ U
    · by_cases hda : d = a ∧ a ∈ U
      · exact hcd (hca.1.trans hda.1.symm)
      · by_cases hdb : d = b ∧ b ∈ U
        · simp only [g, ite_eq_left hca, ite_eq_right hda, ite_eq_left hdb, ite_eq_left hca.2] at heq
          omega
        · simp only [g, ite_eq_left hca, ite_eq_right hda, ite_eq_right hdb] at heq
          omega
    · by_cases hcb : c = b ∧ b ∈ U
      · by_cases hda : d = a ∧ a ∈ U
        · simp only [g, ite_eq_right hca, ite_eq_left hcb, ite_eq_left hda, ite_eq_left hda.2] at heq
          omega
        · by_cases hdb : d = b ∧ b ∈ U
          · exact hcd (hcb.1.trans hdb.1.symm)
          · simp only [g, ite_eq_right hca, ite_eq_left hcb, ite_eq_right hda, ite_eq_right hdb] at heq
            split_ifs at heq <;> omega
      · by_cases hda : d = a ∧ a ∈ U
        · simp only [g, ite_eq_right hca, ite_eq_right hcb, ite_eq_left hda] at heq
          omega
        · by_cases hdb : d = b ∧ b ∈ U
          · simp only [g, ite_eq_right hca, ite_eq_right hcb, ite_eq_right hda, ite_eq_left hdb] at heq
            split_ifs at heq <;> omega
          · exact hproper c hc d hd he hca hcb hda hdb
              (by simpa only [g, ite_eq_right hca, ite_eq_right hcb, ite_eq_right hda, ite_eq_right hdb] using heq)

lemma live_coloring {ops : α → α → Finset α} {goal : α}
    (edge : Finset α → α → α → Prop)
    (irrefl : ∀ S c, ¬ edge S c c)
    (transport : ∀ (k : Nat) (a b z : α) (U : Finset α),
      a ≠ b → z ∉ insert a (insert b U) → z ∈ ops a b →
      live ops goal k (insert z U) →
      ∀ c ∈ insert a (insert b U), ∀ d ∈ insert a (insert b U),
      edge (insert a (insert b U)) c d →
      (c = a → a ∉ U) → (c = b → b ∉ U) →
      (d = a → a ∉ U) → (d = b → b ∉ U) →
      edge (insert z U) (collapse a b z c) (collapse a b z d))
    {k : Nat} {S : Finset α} (hlive : live ops goal k S) :
    ∃ x : Nat, ∃ f : α → Nat, S.card + x ≤ k + 1 ∧
      (∀ c ∈ S, f c ≤ x) ∧
      ∀ c ∈ S, ∀ d ∈ S, edge S c d → f c ≠ f d := by
  induction k generalizing S with
  | zero =>
    change S = {goal} at hlive
    subst S
    refine ⟨0, fun _ => 0, by simp, by simp, ?_⟩
    intro c hc d hd he
    simp only [Finset.mem_singleton] at hc hd
    subst c
    subst d
    exact False.elim (irrefl _ _ he)
  | succ k ih =>
    rcases hlive with hskip | ⟨a, ha, b, hb, hab, z, hz, hnew, U, rfl, htail⟩
    · obtain ⟨x, f, hcard, hbound, hproper⟩ := ih hskip
      exact ⟨x, f, by omega, hbound, hproper⟩
    · obtain ⟨x, f, hcard, hbound, hproper⟩ := ih htail
      obtain ⟨g, gbound, gproper⟩ := extend_coloring irrefl hab hnew
        (transport k a b z U hab hnew hz htail) hbound hproper
      refine ⟨x + ((if a ∈ U then 1 else 0) + (if b ∈ U then 1 else 0)),
        g, ?_, gbound, gproper⟩
      have hcount := retained_card hab hnew
      omega

end ChromGeneric

namespace ChromRelation

variable {width : Nat}

def moved (a b z c : BitVec width) : BitVec width :=
  if c = a ∨ c = b then z else c

lemma moved_mem {a b z c : BitVec width} {U : Finset (BitVec width)}
    (hc : c ∈ insert a (insert b U)) : moved a b z c ∈ insert z U := by
  unfold moved
  split_ifs with h
  · exact Finset.mem_insert_self ..
  · rcases Finset.mem_insert.mp hc with rfl | hc
    · exact False.elim (h (.inl rfl))
    · rcases Finset.mem_insert.mp hc with rfl | hc
      · exact False.elim (h (.inr rfl))
      · exact Finset.mem_insert_of_mem hc

lemma moved_ne {a b z c d : BitVec width} {U : Finset (BitVec width)}
    (hc : c ∈ insert a (insert b U)) (hd : d ∈ insert a (insert b U))
    (hz : z ∉ insert a (insert b U)) (hne : c ≠ d)
    (notboth : ¬ ((c = a ∨ c = b) ∧ (d = a ∨ d = b))) :
    moved a b z c ≠ moved a b z d := by
  unfold moved
  split_ifs with h₁ h₂ h₂
  · exact False.elim (notboth ⟨h₁, h₂⟩)
  · intro eq
    exact hz (eq ▸ hd)
  · intro eq
    exact hz (eq ▸ hc)
  · exact hne

lemma criticalPair_symm {target : BitVec width} {S : Finset (BitVec width)}
    {a b : BitVec width} (h : criticalPair target S a b) : criticalPair target S b a := by
  obtain ⟨ha, hb, hab, p, q, ra, rb, sa, sb, hp, hq, hra, hrb, hsa, hsb,
    u₁, u₂, u₃, u₄, phase₁, phase₂⟩ := h
  exact ⟨hb, ha, hab.symm, p, q, rb, ra, sb, sa, hp, hq, hrb, hra, hsb, hsa,
    u₂, u₁, u₄, u₃, phase₂, phase₁⟩

lemma bool_other_eq {x y z : Bool} (hy : x ≠ y) (hz : x ≠ z) : y = z := by
  cases x <;> cases y <;> cases z <;> simp_all

lemma moved_phase {a b z c : BitVec width} {U : Finset (BitVec width)}
    {p r s q : Fin width} (hab : a ≠ b) (hz : z ∈ basicOps a b)
    (u₁ : uniqueSep (insert a (insert b U)) c p r)
    (u₂ : uniqueSep (insert a (insert b U)) c s q)
    (v₁ : uniqueSep (insert z U) (moved a b z c) p r)
    (v₂ : uniqueSep (insert z U) (moved a b z c) s q)
    (phase : c[p.val] = c[s.val]) :
    (moved a b z c)[p.val] = (moved a b z c)[s.val] := by
  by_cases hc : c = a ∨ c = b
  · simp only [moved, ite_eq_left hc] at v₁ v₂ ⊢
    obtain ⟨d, rfl⟩ := ChromGate.of_basicOps hz
    rcases hc with rfl | rfl
    · have e₁ := u₁.2 b (by simp) hab.symm
      have e₂ := u₂.2 b (by simp) hab.symm
      have d₁ := v₁.1
      have d₂ := v₂.1
      simp only [ChromGate.word_get] at d₁ d₂ ⊢
      exact ChromGate.left_transport d _ _ _ _ _ _ _ _ e₁ e₂ d₁ d₂ phase
    · have e₁ := u₁.2 a (by simp) hab
      have e₂ := u₂.2 a (by simp) hab
      have d₁ := v₁.1
      have d₂ := v₂.1
      simp only [ChromGate.word_get] at d₁ d₂ ⊢
      exact ChromGate.right_transport d _ _ _ _ _ _ _ _ e₁ e₂ d₁ d₂ phase
  · simpa only [moved, ite_eq_right hc] using phase

lemma criticalPair_noCollapse {k : Nat} {target g a b z : BitVec width}
    {U : Finset (BitVec width)} (hz : z ∈ basicOps a b)
    (run : live basicOps g k (insert z U)) (hg : g = target ∨ g = ~~~target)
    (ha : a ∉ U) (hb : b ∉ U)
    (h : criticalPair target (insert a (insert b U)) a b) : False := by
  obtain ⟨_, _, hab, p, q, ra, rb, sa, sb, hp, hq, hra, hrb, hsa, hsb,
    u₁, u₂, u₃, u₄, phase₁, phase₂⟩ := h
  have v₁ : z[p.val] ≠ z[ra.val] := by
    simpa using (uniqueSep_step hz run hg (by simp [hp, hra])
      (fun _ => ha) (fun _ => hb) u₁).1
  have v₂ : z[p.val] ≠ z[rb.val] := by
    simpa using (uniqueSep_step hz run hg (by simp [hp, hrb])
      (fun _ => ha) (fun _ => hb) u₂).1
  have v₃ : z[sa.val] ≠ z[q.val] := by
    simpa using (uniqueSep_step hz run hg (by simp [hsa, hq])
      (fun _ => ha) (fun _ => hb) u₃).1
  have v₄ : z[sb.val] ≠ z[q.val] := by
    simpa using (uniqueSep_step hz run hg (by simp [hsb, hq])
      (fun _ => ha) (fun _ => hb) u₄).1
  have ara : a[ra.val] = a[q.val] := bool_other_eq u₁.1 (phase₁ ▸ u₃.1)
  have brb : b[rb.val] = b[q.val] := bool_other_eq u₂.1 (phase₂ ▸ u₄.1)
  have bra := u₁.2 b (by simp) hab.symm
  have arb := u₂.2 a (by simp) hab
  have bsa := u₃.2 b (by simp) hab.symm
  have asb := u₄.2 a (by simp) hab
  obtain ⟨d, hzword⟩ := ChromGate.of_basicOps hz
  have d₁ : ChromGate.eval d a[p.val] b[p.val] ≠ ChromGate.eval d a[q.val] b[p.val] := by
    simpa only [hzword, ChromGate.word_get, ara, ← bra] using v₁
  have d₂ : ChromGate.eval d a[p.val] b[p.val] ≠ ChromGate.eval d a[p.val] b[q.val] := by
    simpa only [hzword, ChromGate.word_get, brb, ← arb] using v₂
  have d₃ : ChromGate.eval d a[q.val] b[q.val] ≠ ChromGate.eval d a[p.val] b[q.val] := by
    simpa only [hzword, ChromGate.word_get, ← phase₁, bsa] using v₃.symm
  have d₄ : ChromGate.eval d a[q.val] b[q.val] ≠ ChromGate.eval d a[q.val] b[p.val] := by
    simpa only [hzword, ChromGate.word_get, ← phase₂, asb] using v₄.symm
  exact ChromGate.rectangle_false d _ _ _ _ d₁ d₂ d₃ d₄

lemma criticalPair_step {k : Nat} {target g a b z c d : BitVec width}
    {U : Finset (BitVec width)} (hab : a ≠ b) (hz : z ∈ basicOps a b)
    (fresh : z ∉ insert a (insert b U))
    (run : live basicOps g k (insert z U)) (hg : g = target ∨ g = ~~~target)
    (hca : c = a → a ∉ U) (hcb : c = b → b ∉ U)
    (hda : d = a → a ∉ U) (hdb : d = b → b ∉ U)
    (h : criticalPair target (insert a (insert b U)) c d) :
    criticalPair target (insert z U)
      (if c = a ∨ c = b then z else c) (if d = a ∨ d = b then z else d) := by
  have notboth : ¬ ((c = a ∨ c = b) ∧ (d = a ∨ d = b)) := by
    rintro ⟨hc, hd⟩
    rcases hc with rfl | rfl <;> rcases hd with rfl | rfl
    · exact h.2.2.1 rfl
    · exact criticalPair_noCollapse hz run hg (hca rfl) (hdb rfl) h
    · exact criticalPair_noCollapse hz run hg (hda rfl) (hcb rfl) (criticalPair_symm h)
    · exact h.2.2.1 rfl
  obtain ⟨hc, hd, hcd, p, q, ra, rb, sa, sb, hp, hq, hra, hrb, hsa, hsb,
    u₁, u₂, u₃, u₄, phase₁, phase₂⟩ := h
  have v₁ := uniqueSep_step hz run hg (by simp [hp, hra]) hca hcb u₁
  have v₂ := uniqueSep_step hz run hg (by simp [hp, hrb]) hda hdb u₂
  have v₃ := uniqueSep_step hz run hg (by simp [hsa, hq]) hca hcb u₃
  have v₄ := uniqueSep_step hz run hg (by simp [hsb, hq]) hda hdb u₄
  change criticalPair target (insert z U) (moved a b z c) (moved a b z d)
  exact ⟨moved_mem hc, moved_mem hd, moved_ne hc hd fresh hcd notboth,
    p, q, ra, rb, sa, sb, hp, hq, hra, hrb, hsa, hsb, v₁, v₂, v₃, v₄,
    moved_phase hab hz u₁ u₃ v₁ v₃ phase₁,
    moved_phase hab hz u₂ u₄ v₂ v₄ phase₂⟩

end ChromRelation

lemma live_criticalPair_coloring {width k : Nat} {target g : BitVec width}
    {S : Finset (BitVec width)} (run : live basicOps g k S)
    (hg : g = target ∨ g = ~~~target) :
    ∃ color : BitVec width → Nat,
      (∀ a ∈ S, color a < k + 2 - S.card) ∧
      ∀ a b, criticalPair target S a b → color a ≠ color b := by
  have irrefl : ∀ U c, ¬ criticalPair target U c c := by
    intro U c h
    exact h.2.2.1 rfl
  obtain ⟨x, color, hcard, hbound, hproper⟩ :=
    ChromGeneric.live_coloring (criticalPair target) irrefl
      (by
        intro n a b z U hab fresh hz tail c hc d hd edge hca hcb hda hdb
        exact ChromRelation.criticalPair_step hab hz fresh tail hg
          hca hcb hda hdb edge) run
  refine ⟨color, ?_, ?_⟩
  · intro a ha
    have := hbound a ha
    omega
  · intro a b edge
    exact hproper a edge.1 b edge.2.1 edge


end PEqualNP.Outside.L_meta_10760

namespace PEqualNP.Outside.L_meta_10760.RestrictionSixProof

lemma bin_mem_basicOps (d : Nat) (a b : Sig) : bin d a b ∈ basicOps a b := by
  unfold bin
  split_ifs <;> simp [basicOps, ops, BitVec.and_comm]

lemma Live.to_generic {u : Bool} {target : Sig} {k : Nat} {S : Finset Sig}
    (run : Live u target k S) : live basicOps target k S := by
  induction run using Live.ind with
  | stop _ => rfl
  | @binary k U a b d _ _ _ hab fresh _ ih =>
      exact Or.inr ⟨a, by simp, b, by simp, hab, bin d a b,
        bin_mem_basicOps d a b, fresh, U, rfl, ih⟩

lemma Live_criticalPair_coloring {u : Bool} {k : Nat} {target g : Sig}
    {S : Finset Sig} (run : Live u g k S)
    (phase : g = target ∨ g = ~~~target) :
    ∃ color : Sig → Nat,
      (∀ a ∈ S, color a < k + 2 - S.card) ∧
      ∀ a b, criticalPair target S a b → color a ≠ color b := by
  exact live_criticalPair_coloring run.to_generic phase

lemma Live_criticalPair_coloring_self {u : Bool} {k : Nat} {target : Sig}
    {S : Finset Sig} (run : Live u target k S) :
    ∃ color : Sig → Nat,
      (∀ a ∈ S, color a < k + 2 - S.card) ∧
      ∀ a b, criticalPair target S a b → color a ≠ color b := by
  exact Live_criticalPair_coloring run (Or.inl rfl)

end PEqualNP.Outside.L_meta_10760.RestrictionSixProof

namespace PEqualNP.Outside.L_meta_10760

def graphEdge (graph : List ℕ) (i j : ℕ) : Bool :=
  (graph.getD i 0).testBit j || (graph.getD j 0).testBit i

def colorPrefix (f : ℕ → ℕ) (n : ℕ) : List ℕ := (List.range n).map f

lemma colorPrefix_length (f : ℕ → ℕ) (n : ℕ) : (colorPrefix f n).length = n := by
  simp [colorPrefix]

lemma colorPrefix_get (f : ℕ → ℕ) (n i : ℕ) (hi : i < n) :
    (colorPrefix f n).getD i 0 = f i := by
  simp [colorPrefix, List.getD_eq_getElem?_getD, hi]

lemma colorPrefix_succ (f : ℕ → ℕ) (n : ℕ) :
    colorPrefix f (n + 1) = colorPrefix f n ++ [f n] := by
  simp [colorPrefix, List.range_succ]

def fitsColor (graph assigned : List ℕ) (c : ℕ) : Bool :=
  !(graphEdge graph assigned.length assigned.length) &&
    (List.range assigned.length).all (fun i =>
      !(graphEdge graph assigned.length i) || assigned.getD i 0 != c)

def colorSearch (graph : List ℕ) (colors : ℕ) : ℕ → List ℕ → Bool
  | 0, _ => true
  | k + 1, assigned => (List.range colors).any (fun c =>
      fitsColor graph assigned c && colorSearch graph colors k (assigned ++ [c]))

def graphColorable (graph : List ℕ) (colors : ℕ) : Prop :=
  ∃ f : ℕ → ℕ, (∀ i < graph.length, f i < colors) ∧
    ∀ i < graph.length, ∀ j < graph.length,
      (graph.getD i 0).testBit j = true → f i ≠ f j

def graphColorCheck (graph : List ℕ) (colors : ℕ) : Bool :=
  colorSearch graph colors graph.length []

lemma graphEdge_colors {graph : List ℕ} {f : ℕ → ℕ}
    (hproper : ∀ i < graph.length, ∀ j < graph.length,
      (graph.getD i 0).testBit j = true → f i ≠ f j)
    {i j : ℕ} (hi : i < graph.length) (hj : j < graph.length)
    (h : graphEdge graph i j = true) : f i ≠ f j := by
  simp only [graphEdge, Bool.or_eq_true] at h
  rcases h with h | h
  · exact hproper i hi j hj h
  · exact Ne.symm (hproper j hj i hi h)

lemma fitsColor_prefix {graph : List ℕ} {f : ℕ → ℕ}
    (hproper : ∀ i < graph.length, ∀ j < graph.length,
      (graph.getD i 0).testBit j = true → f i ≠ f j)
    {n : ℕ} (hn : n < graph.length) :
    fitsColor graph (colorPrefix f n) (f n) = true := by
  have hself : graphEdge graph n n = false := by
    cases he : graphEdge graph n n with
    | false => rfl
    | true => exact False.elim ((graphEdge_colors hproper hn hn he) rfl)
  simp only [fitsColor, colorPrefix_length, hself, Bool.not_false, Bool.true_and]
  apply List.all_eq_true.mpr
  intro i hi
  have hin : i < n := List.mem_range.mp hi
  rw [colorPrefix_get f n i hin]
  cases he : graphEdge graph n i with
  | false => simp
  | true =>
    have hh : f i ≠ f n := Ne.symm (graphEdge_colors hproper hn (by omega) he)
    simp [hh]

lemma colorSearch_complete {graph : List ℕ} {colors : ℕ} {f : ℕ → ℕ}
    (hbound : ∀ i < graph.length, f i < colors)
    (hproper : ∀ i < graph.length, ∀ j < graph.length,
      (graph.getD i 0).testBit j = true → f i ≠ f j)
    (k n : ℕ) (hsize : n + k ≤ graph.length) :
    colorSearch graph colors k (colorPrefix f n) = true := by
  induction k generalizing n with
  | zero => rfl
  | succ k ih =>
    have hn : n < graph.length := by omega
    apply List.any_eq_true.mpr
    refine ⟨f n, List.mem_range.mpr (hbound n hn), ?_⟩
    simp only [Bool.and_eq_true]
    constructor
    · exact fitsColor_prefix hproper hn
    · simpa only [colorPrefix_succ] using ih (n + 1) (by omega)

lemma graphColorCheck_complete {graph : List ℕ} {colors : ℕ}
    (h : graphColorable graph colors) : graphColorCheck graph colors = true := by
  obtain ⟨f, hbound, hproper⟩ := h
  simpa [graphColorCheck, colorPrefix] using
    colorSearch_complete hbound hproper graph.length 0 (by omega)

lemma not_graphColorable_of_check {graph : List ℕ} {colors : ℕ}
    (h : graphColorCheck graph colors = false) : ¬ graphColorable graph colors := by
  intro hc
  have hh := graphColorCheck_complete hc
  rw [h] at hh
  cases hh

def graphEmptyCheck (graph : List ℕ) : Bool :=
  graph.all (fun row => decide (BitVec.ofNat graph.length row = 0))

lemma graphEmptyCheck_complete {graph : List ℕ} (h : graphColorable graph 1) :
    graphEmptyCheck graph = true := by
  obtain ⟨f, hbound, hproper⟩ := h
  apply List.all_eq_true.mpr
  intro row hrow
  obtain ⟨i, hin, hroweq⟩ := List.mem_iff_getElem.mp hrow
  have hr : graph.getD i 0 = row := by
    simp [List.getD_eq_getElem?_getD, hin, hroweq]
  apply decide_eq_true
  rw [← hr]
  apply BitVec.eq_of_getLsbD_eq_iff.mpr
  intro j hj
  have hfalse : (graph.getD i 0).testBit j = false := by
    cases he : (graph.getD i 0).testBit j with
    | false => rfl
    | true =>
      have hh := hproper i hin j hj he
      have hb1 := hbound i hin
      have hb2 := hbound j hj
      omega
  simp only [BitVec.getLsbD_ofNat, hj, decide_true, Bool.true_and, hfalse]
  change false = (BitVec.ofNat graph.length 0).getLsbD j
  simp [BitVec.getLsbD_ofNat]

def graphColorFast (graph : List ℕ) (colors : ℕ) : Bool :=
  if colors = 1 then graphEmptyCheck graph else graphColorCheck graph colors

lemma graphColorFast_complete {graph : List ℕ} {colors : ℕ}
    (h : graphColorable graph colors) : graphColorFast graph colors = true := by
  unfold graphColorFast
  split
  next hc => subst colors; exact graphEmptyCheck_complete h
  next hc => exact graphColorCheck_complete h

lemma not_graphColorable_of_fast {graph : List ℕ} {colors : ℕ}
    (h : graphColorFast graph colors = false) : ¬ graphColorable graph colors := by
  intro hc
  have hh := graphColorFast_complete hc
  rw [h] at hh
  cases hh

lemma graphColorable_of_fin {graph : List ℕ} {colors : ℕ}
    (f : Fin graph.length → Fin colors)
    (hproper : ∀ i j, (graph.getD i.val 0).testBit j.val = true → f i ≠ f j) :
    graphColorable graph colors := by
  let g : ℕ → ℕ := fun i => if hi : i < graph.length then (f ⟨i, hi⟩).val else 0
  refine ⟨g, ?_, ?_⟩
  · intro i hi
    simp [g, hi]
  · intro i hi j hj he
    have hh := hproper ⟨i, hi⟩ ⟨j, hj⟩ he
    simp only [g, hi, hj, dite_true]
    intro eq
    apply hh
    exact Fin.ext eq

lemma not_fin_coloring_of_fast {graph : List ℕ} {colors : ℕ}
    (h : graphColorFast graph colors = false)
    (f : Fin graph.length → Fin colors)
    (hproper : ∀ i j, (graph.getD i.val 0).testBit j.val = true → f i ≠ f j) : False :=
  not_graphColorable_of_fast h (graphColorable_of_fin f hproper)


end PEqualNP.Outside.L_meta_10760

namespace PEqualNP.Outside.L_meta_10760

def inducedGraph (graph chosen : List ℕ) : List ℕ :=
  chosen.map fun v => (BitVec.ofBoolListLE (chosen.map fun u => graphEdge graph v u)).toNat

lemma inducedGraph_length (graph chosen : List ℕ) :
    (inducedGraph graph chosen).length = chosen.length := by
  simp only [inducedGraph, List.length_map]

lemma inducedGraph_bit (graph chosen : List ℕ) (i j : ℕ)
    (hi : i < chosen.length) (hj : j < chosen.length) :
    ((inducedGraph graph chosen).getD i 0).testBit j =
      graphEdge graph (chosen.getD i 0) (chosen.getD j 0) := by
  rw [List.getD_eq_getElem _ _ (by simpa only [inducedGraph_length] using hi)]
  simp only [inducedGraph, List.getElem_map, BitVec.testBit_toNat,
    BitVec.getLsbD_ofBoolListLE]
  rw [List.getD_eq_getElem _ _ (by simpa only [List.length_map] using hj),
    List.getElem_map, List.getD_eq_getElem _ _ hi, List.getD_eq_getElem _ _ hj]

lemma graphColorable_induced {graph chosen : List ℕ} {colors : ℕ}
    (hc : graphColorable graph colors)
    (hchosen : ∀ v ∈ chosen, v < graph.length) :
    graphColorable (inducedGraph graph chosen) colors := by
  obtain ⟨f, hbound, hproper⟩ := hc
  have hv (i : ℕ) (hi : i < chosen.length) : chosen.getD i 0 < graph.length := by
    rw [List.getD_eq_getElem _ _ hi]
    exact hchosen _ (List.getElem_mem hi)
  refine ⟨fun i => f (chosen.getD i 0), ?_, ?_⟩
  · intro i hi
    rw [inducedGraph_length] at hi
    exact hbound _ (hv i hi)
  · intro i hi j hj he
    rw [inducedGraph_length] at hi hj
    rw [inducedGraph_bit graph chosen i j hi hj] at he
    exact graphEdge_colors hproper (hv i hi) (hv j hj) he

def graphDegree (graph : List ℕ) (v : ℕ) : ℕ :=
  ((List.range graph.length).filter fun u => graphEdge graph v u).length

def degreeInsert (a : ℕ × ℕ) : List (ℕ × ℕ) → List (ℕ × ℕ)
  | [] => [a]
  | b :: rest => if b.1 ≤ a.1 then a :: b :: rest else b :: degreeInsert a rest

def degreeSort : List (ℕ × ℕ) → List (ℕ × ℕ)
  | [] => []
  | a :: rest => degreeInsert a (degreeSort rest)

def graphOrder (graph : List ℕ) : List ℕ :=
  (degreeSort (((List.range graph.length).map fun v => (graphDegree graph v, v)).filter
    fun entry => 0 < entry.1)).map Prod.snd

lemma mem_degreeInsert (a entry : ℕ × ℕ) (entries : List (ℕ × ℕ)) :
    entry ∈ degreeInsert a entries ↔ entry = a ∨ entry ∈ entries := by
  induction entries with
  | nil => simp [degreeInsert]
  | cons b rest ih =>
    simp only [degreeInsert]
    split
    · simp only [List.mem_cons]
    · simp only [List.mem_cons, ih]
      tauto

lemma mem_degreeSort (entry : ℕ × ℕ) (entries : List (ℕ × ℕ)) :
    entry ∈ degreeSort entries ↔ entry ∈ entries := by
  induction entries with
  | nil => rfl
  | cons a rest ih =>
    simp only [degreeSort, mem_degreeInsert, ih, List.mem_cons]

lemma graphOrder_valid (graph : List ℕ) :
    ∀ v ∈ graphOrder graph, v < graph.length := by
  intro v hv
  simp only [graphOrder, List.mem_map] at hv
  obtain ⟨entry, he, hvalue⟩ := hv
  rw [mem_degreeSort] at he
  have hentry := (List.mem_filter.mp he).1
  obtain ⟨u, hu, hue⟩ := List.mem_map.mp hentry
  have hlt : u < graph.length := List.mem_range.mp hu
  subst entry
  change u = v at hvalue
  simpa only [hvalue] using hlt

def graphOrderedCheck (graph : List ℕ) (colors : ℕ) : Bool :=
  graphColorCheck (inducedGraph graph (graphOrder graph)) colors

lemma graphOrderedCheck_complete {graph : List ℕ} {colors : ℕ}
    (hc : graphColorable graph colors) : graphOrderedCheck graph colors = true := by
  exact graphColorCheck_complete (graphColorable_induced hc (graphOrder_valid graph))

lemma not_graphColorable_of_ordered {graph : List ℕ} {colors : ℕ}
    (h : graphOrderedCheck graph colors = false) : ¬ graphColorable graph colors := by
  intro hc
  have hh := graphOrderedCheck_complete hc
  rw [h] at hh
  cases hh

def graphColorDegreeFast (graph : List ℕ) (colors : ℕ) : Bool :=
  if colors = 1 then graphEmptyCheck graph
  else if 1 < colors then graphOrderedCheck graph colors
  else graphColorCheck graph colors

lemma graphColorDegreeFast_complete {graph : List ℕ} {colors : ℕ}
    (hc : graphColorable graph colors) : graphColorDegreeFast graph colors = true := by
  unfold graphColorDegreeFast
  split
  · next h => subst colors; exact graphEmptyCheck_complete hc
  · split
    · exact graphOrderedCheck_complete hc
    · exact graphColorCheck_complete hc

lemma not_graphColorable_of_degreeFast {graph : List ℕ} {colors : ℕ}
    (h : graphColorDegreeFast graph colors = false) : ¬ graphColorable graph colors := by
  intro hc
  have hh := graphColorDegreeFast_complete hc
  rw [h] at hh
  cases hh

end PEqualNP.Outside.L_meta_10760

namespace PEqualNP.Outside.L_meta_10760.KernelNat128

def mask : Nat := 0xffffffffffffffffffffffffffffffff
def goal : Nat := 0xfffffffffffefffafffeffeefefeeca0
def rows : List Nat := [0, 1, 2, 3, 4, 6, 8, 9, 12, 16, 24, 32, 36, 48, 64, 66, 80]

def singles {α : Type} : List α → List (α × List α)
  | [] => []
  | a :: rest => (a, rest) :: (singles rest).map (fun (b, bs) => (b, a :: bs))

def pairs {α : Type} : List α → List (α × α × List α)
  | [] => []
  | a :: rest => (singles rest).map (fun (b, bs) => (a, b, bs)) ++
      (pairs rest).map (fun (b, c, bs) => (b, c, a :: bs))

def rowPattern (row : Nat) : List Nat → Nat
  | [] => 0
  | w :: ws => ((w >>> row) &&& 1) ||| (rowPattern row ws <<< 1)

def labelledPatterns (ws : List Nat) : List (Nat × Bool) :=
  (List.range 128).map fun row => (rowPattern row ws, (goal >>> row) &&& 1 == 1)

def patternSets (ps : List (Nat × Bool)) : Nat × Nat :=
  ps.foldl (fun (positive, negative) (p, label) =>
    if label then (positive ||| (1 <<< p), negative)
    else (positive, negative ||| (1 <<< p))) (0, 0)

def bitTest (w j : Nat) : Bool := (w >>> j) &&& 1 == 1

lemma adj_bitTest (w i : Nat) : bitTest w i = w.testBit i := by
  apply Bool.eq_iff_iff.mpr
  simp only [bitTest, Nat.and_one_is_mod, Nat.shiftRight_eq_div_pow,
    Nat.testBit_eq_decide_div_mod_eq, beq_iff_eq, decide_eq_true_eq]

def adj_bitmapStep (acc : Nat × Nat) (item : Nat × Bool) : Nat × Nat :=
  if item.2 then (acc.1 ||| (1 <<< item.1), acc.2)
  else (acc.1, acc.2 ||| (1 <<< item.1))

lemma adj_bitmap_step_pos (acc : Nat × Nat) (item : Nat × Bool) (t : Nat) :
    (adj_bitmapStep acc item).1.testBit t =
      (acc.1.testBit t || (item.2 && decide (item.1 = t))) := by
  rcases acc with ⟨a,b⟩
  rcases item with ⟨p,label⟩
  cases label <;> simp [adj_bitmapStep, Nat.testBit_or, Nat.shiftLeft_eq, Nat.testBit_two_pow]

lemma adj_bitmap_step_neg (acc : Nat × Nat) (item : Nat × Bool) (t : Nat) :
    (adj_bitmapStep acc item).2.testBit t =
      (acc.2.testBit t || (!item.2 && decide (item.1 = t))) := by
  rcases acc with ⟨a,b⟩
  rcases item with ⟨p,label⟩
  cases label <;> simp [adj_bitmapStep, Nat.testBit_or, Nat.shiftLeft_eq, Nat.testBit_two_pow]

lemma adj_bitmap_fold_pos (ps : List (Nat × Bool)) (acc : Nat × Nat) (t : Nat) :
    (ps.foldl adj_bitmapStep acc).1.testBit t =
      (acc.1.testBit t || ps.any (fun item => item.2 && decide (item.1 = t))) := by
  induction ps generalizing acc with
  | nil => simp
  | cons a ps ih =>
    rw [List.foldl_cons, ih, adj_bitmap_step_pos]
    simp only [List.any_cons, Bool.or_assoc]

lemma adj_bitmap_fold_neg (ps : List (Nat × Bool)) (acc : Nat × Nat) (t : Nat) :
    (ps.foldl adj_bitmapStep acc).2.testBit t =
      (acc.2.testBit t || ps.any (fun item => !item.2 && decide (item.1 = t))) := by
  induction ps generalizing acc with
  | nil => simp
  | cons a ps ih =>
    rw [List.foldl_cons, ih, adj_bitmap_step_neg]
    simp only [List.any_cons, Bool.or_assoc]

lemma adj_patternSets_eq (ps : List (Nat × Bool)) :
    patternSets ps = ps.foldl adj_bitmapStep (0,0) := rfl

lemma adj_patternSets_pos (ps : List (Nat × Bool)) (t : Nat) :
    (patternSets ps).1.testBit t = true ↔ (t,true) ∈ ps := by
  rw [adj_patternSets_eq, adj_bitmap_fold_pos]
  simp only [Nat.zero_testBit, Bool.false_or, List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨⟨p,label⟩, hm, hl, hp⟩
    cases hl
    cases hp
    exact hm
  · intro h
    exact ⟨(t,true),h,rfl,rfl⟩

lemma adj_patternSets_neg (ps : List (Nat × Bool)) (t : Nat) :
    (patternSets ps).2.testBit t = true ↔ (t,false) ∈ ps := by
  rw [adj_patternSets_eq, adj_bitmap_fold_neg]
  simp only [Nat.zero_testBit, Bool.false_or, List.any_eq_true, Bool.and_eq_true,
    decide_eq_true_eq]
  constructor
  · rintro ⟨⟨p,label⟩, hm, hl, hp⟩
    cases label with
    | false => cases hp; exact hm
    | true => simp at hl
  · intro h
    exact ⟨(t,false),h,rfl,rfl⟩

lemma singles_mem {a : Nat} {rest ws : List Nat}
    (h : (a, rest) ∈ singles ws) : a ∈ ws ∧ ∀ x ∈ rest, x ∈ ws := by
  induction ws generalizing rest with
  | nil => simp [singles] at h
  | cons b bs ih =>
    simp only [singles, List.mem_cons, List.mem_map] at h
    rcases h with h | ⟨⟨c, cs⟩, hc, he⟩
    · cases h
      exact ⟨by simp, fun x hx => by simp [hx]⟩
    · cases he
      obtain ⟨ha, hr⟩ := ih hc
      refine ⟨by simp [ha], ?_⟩
      intro x hx
      simp only [List.mem_cons] at hx ⊢
      exact hx.imp_right (hr x)

lemma pairs_mem_bounds {a b : Nat} {rest ws : List Nat} (hw : ws.Nodup)
    (h : (a, b, rest) ∈ pairs ws) : a ∈ ws ∧ b ∈ ws ∧ a ≠ b := by
  induction ws generalizing a b rest with
  | nil => simp [pairs] at h
  | cons c cs ih =>
    simp only [List.nodup_cons] at hw
    simp only [pairs, List.mem_append, List.mem_map] at h
    rcases h with ⟨⟨d, ds⟩, hd, he⟩ | ⟨⟨d, e, ds⟩, hd, he⟩
    · cases he
      obtain ⟨hdmem, _⟩ := singles_mem hd
      refine ⟨by simp, by simp [hdmem], ?_⟩
      intro he
      exact hw.1 (he ▸ hdmem)
    · cases he
      obtain ⟨ha, hb, hab⟩ := ih hw.2 hd
      exact ⟨by simp [ha], by simp [hb], hab⟩

lemma pairs_range_bounds {n i j : Nat} {rest : List Nat}
    (h : (i, j, rest) ∈ pairs (List.range n)) : i < n ∧ j < n ∧ i ≠ j := by
  simpa using pairs_mem_bounds (List.nodup_range) h

lemma rowPattern_bit (row i : Nat) (ws : List Nat) :
    (rowPattern row ws).testBit i = (ws.getD i 0).testBit row := by
  induction ws generalizing i with
  | nil => simp [rowPattern]
  | cons w ws ih =>
    cases i with
    | zero => simp [rowPattern]
    | succ i =>
      have h1 : (1 : Nat).testBit (i + 1) = false := by
        rw [show (1 : Nat) = 2 ^ 0 by rfl, Nat.testBit_two_pow]
        simp
      rw [rowPattern, Nat.testBit_or, Nat.testBit_and, h1]
      simpa using ih i

lemma rowPattern_flip {p q i : Nat} {ws : List Nat}
    (h : rowPattern q ws = rowPattern p ws ^^^ (1 <<< i)) (j : Nat) :
    (ws.getD j 0).testBit q = xor ((ws.getD j 0).testBit p) (decide (i = j)) := by
  have hb := congrArg (fun w : Nat => w.testBit j) h
  rw [rowPattern_bit, Nat.testBit_xor, rowPattern_bit] at hb
  simpa [Nat.shiftLeft_eq, Nat.testBit_two_pow] using hb


lemma adj_labelled {ws : List Nat} {pattern : Nat} {label : Bool}
    (hm : (pattern,label) ∈ labelledPatterns ws) :
    ∃ r : Fin 128, rowPattern r.val ws = pattern ∧ goal.testBit r.val = label := by
  obtain ⟨r,hr,he⟩ := List.mem_map.mp hm
  have hr' : r < 128 := List.mem_range.mp hr
  refine ⟨⟨r,hr'⟩,congrArg Prod.fst he,?_⟩
  have hl := congrArg Prod.snd he
  change bitTest goal r = label at hl
  rwa [adj_bitTest] at hl

lemma adj_ofNat_bit (w : Nat) (r : Fin 128) :
    (BitVec.ofNat 128 w)[r.val] = w.testBit r.val := by
  rw [← BitVec.getLsbD_eq_getElem, BitVec.getLsbD_ofNat]
  simp only [r.isLt, decide_true, Bool.true_and]

def adj_frontier (ws : List Nat) : Finset (BitVec 128) :=
  (ws.map (BitVec.ofNat 128)).toFinset

def adj_word (ws : List Nat) (i : Nat) : BitVec 128 :=
  BitVec.ofNat 128 (ws.getD i 0)

lemma adj_word_bit (ws : List Nat) (i : Nat) (r : Fin 128) :
    (adj_word ws i)[r.val] = (ws.getD i 0).testBit r.val := adj_ofNat_bit _ _

lemma adj_word_mem {ws : List Nat} {i : Nat} (hi : i < ws.length) :
    adj_word ws i ∈ adj_frontier ws := by
  simp only [adj_word, adj_frontier, List.mem_toFinset, List.mem_map]
  exact ⟨ws.getD i 0, by rw [List.getD_eq_getElem ws 0 hi]; exact List.getElem_mem hi, rfl⟩

lemma adj_mem_word {ws : List Nat} {w : BitVec 128} (hw : w ∈ adj_frontier ws) :
    ∃ k, k < ws.length ∧ adj_word ws k = w := by
  simp only [adj_frontier, List.mem_toFinset, List.mem_map] at hw
  obtain ⟨v,hv,he⟩ := hw
  obtain ⟨k,hk,hv⟩ := List.mem_iff_getElem.mp hv
  exact ⟨k,hk,by rw [adj_word, List.getD_eq_getElem ws 0 hk, hv]; exact he⟩

lemma adj_flip_unique {ws : List Nat} {i : Nat} {p q : Fin 128}
    (hf : rowPattern q.val ws = rowPattern p.val ws ^^^ (1 <<< i)) :
    uniqueSep (adj_frontier ws) (adj_word ws i) p q := by
  constructor
  · have hb := rowPattern_flip hf i
    simp only [decide_true, Bool.xor_true] at hb
    simp only [adj_word_bit]
    rw [hb]
    exact Bool.ne_not.mpr rfl
  · intro w hw hne
    obtain ⟨k,hk,rfl⟩ := adj_mem_word hw
    have hki : i ≠ k := by
      intro he
      exact hne (congrArg (adj_word ws) he.symm)
    have hb := rowPattern_flip hf k
    simpa only [adj_word_bit, hki, decide_false, Bool.xor_false] using hb.symm

lemma adj_unique_symm {S : Finset (BitVec 128)} {a : BitVec 128} {p q : Fin 128}
    (h : uniqueSep S a p q) : uniqueSep S a q p := by
  exact ⟨Ne.symm h.1,fun w hw hne => (h.2 w hw hne).symm⟩


def adj_patternCorners (ps : List (Nat × Bool)) (i j : Nat) : Prop :=
  ∃ p q, (p,true) ∈ ps ∧ (q,false) ∈ ps ∧
    (p ^^^ (1 <<< i),false) ∈ ps ∧ (p ^^^ (1 <<< j),false) ∈ ps ∧
    (q ^^^ (1 <<< i),true) ∈ ps ∧ (q ^^^ (1 <<< j),true) ∈ ps ∧
    p.testBit i ≠ q.testBit i ∧ p.testBit j ≠ q.testBit j

lemma adj_corner_rows {ws : List Nat} {i j : Nat}
    (hi : i < ws.length) (hj : j < ws.length) (hij : i ≠ j)
    (hc : adj_patternCorners (labelledPatterns ws) i j) :
    criticalPair (BitVec.ofNat 128 goal) (adj_frontier ws) (adj_word ws i) (adj_word ws j) := by
  obtain ⟨x,y,hx,hy,hxi,hxj,hyi,hyj,hpi,hpj⟩ := hc
  obtain ⟨p,hp,hpt⟩ := adj_labelled hx
  obtain ⟨q,hq,hqt⟩ := adj_labelled hy
  obtain ⟨ra,hra,hrat⟩ := adj_labelled hxi
  obtain ⟨rb,hrb,hrbt⟩ := adj_labelled hxj
  obtain ⟨sa,hsa,hsat⟩ := adj_labelled hyi
  obtain ⟨sb,hsb,hsbt⟩ := adj_labelled hyj
  have hfra : rowPattern ra.val ws = rowPattern p.val ws ^^^ (1 <<< i) := by rwa [hp]
  have hfrb : rowPattern rb.val ws = rowPattern p.val ws ^^^ (1 <<< j) := by rwa [hp]
  have hfsa : rowPattern sa.val ws = rowPattern q.val ws ^^^ (1 <<< i) := by rwa [hq]
  have hfsb : rowPattern sb.val ws = rowPattern q.val ws ^^^ (1 <<< j) := by rwa [hq]
  have ua := adj_flip_unique hfra
  have ub := adj_flip_unique hfrb
  have usa := adj_unique_symm (adj_flip_unique hfsa)
  have usb := adj_unique_symm (adj_flip_unique hfsb)
  have hne : adj_word ws i ≠ adj_word ws j := by
    have hb := rowPattern_flip hfra j
    simp only [hij, decide_false, Bool.xor_false] at hb
    have hbe : (adj_word ws j)[p.val] = (adj_word ws j)[ra.val] := by
      simpa only [adj_word_bit] using hb.symm
    intro he
    exact ua.1 (by rw [he]; exact hbe)
  have hip : (adj_word ws i)[p.val] ≠ (adj_word ws i)[q.val] := by
    simpa only [adj_word_bit, ← rowPattern_bit, hp, hq] using hpi
  have hjp : (adj_word ws j)[p.val] ≠ (adj_word ws j)[q.val] := by
    simpa only [adj_word_bit, ← rowPattern_bit, hp, hq] using hpj
  have his : (adj_word ws i)[sa.val] = !(adj_word ws i)[q.val] := by
    have hb := rowPattern_flip hfsa i
    simpa only [adj_word_bit, decide_true, Bool.xor_true] using hb
  have hjs : (adj_word ws j)[sb.val] = !(adj_word ws j)[q.val] := by
    have hb := rowPattern_flip hfsb j
    simpa only [adj_word_bit, decide_true, Bool.xor_true] using hb
  have hipa : (adj_word ws i)[p.val] = (adj_word ws i)[sa.val] := by
    rw [his]
    exact Bool.eq_not.mpr hip
  have hjpb : (adj_word ws j)[p.val] = (adj_word ws j)[sb.val] := by
    rw [hjs]
    exact Bool.eq_not.mpr hjp
  refine ⟨adj_word_mem hi, adj_word_mem hj, hne, p,q,ra,rb,sa,sb,?_,?_,?_,?_,?_,?_,ua,ub,usa,usb,hipa,hjpb⟩
  all_goals rwa [adj_ofNat_bit]

def lowMasks : List Nat := [0x5555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555, 0x3333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333, 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f, 0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff, 0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff, 0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff, 0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff, 0xffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff]

def flipPatternBits (i x : Nat) : Nat :=
  ((x &&& lowMasks[i]!) <<< (1 <<< i)) |||
    ((x >>> (1 <<< i)) &&& lowMasks[i]!)

def flipIndexLaw (i p : Nat) : Prop :=
  let d := 1 <<< i
  let mask := lowMasks[i]!
  (mask.testBit p = true ∧
    (decide (p ≥ d) && mask.testBit (p-d)) = false ∧
    p+d = p ^^^ d) ∨
  (mask.testBit p = false ∧
    (decide (p ≥ d) && mask.testBit (p-d)) = true ∧
    p-d = p ^^^ d)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
lemma flipIndexLaw_checked (i : Fin 10) (p : Fin 1024) :
    flipIndexLaw i p := by
  unfold flipIndexLaw
  decide +kernel +revert

lemma flipPatternBits_bit {i p : Nat} (hi : i < 10) (hp : p < 1024) (x : Nat) :
    (flipPatternBits i x).testBit p = x.testBit (p ^^^ (1 <<< i)) := by
  obtain (⟨hm, hf, he⟩ | ⟨hm, hf, he⟩) :=
    flipIndexLaw_checked ⟨i, hi⟩ ⟨p, hp⟩ <;>
    change lowMasks[i]!.testBit p = _ at hm <;>
    change (decide (p ≥ (1 <<< i)) && lowMasks[i]!.testBit (p-(1 <<< i))) = _ at hf
  all_goals
    rw [flipPatternBits, Nat.testBit_or, Nat.testBit_shiftLeft,
      Nat.testBit_and, Nat.testBit_and, Nat.testBit_shiftRight]
    have regroup :
        (decide (p ≥ (1 <<< i)) &&
          (x.testBit (p-(1 <<< i)) && lowMasks[i]!.testBit (p-(1 <<< i)))) =
        ((decide (p ≥ (1 <<< i)) && lowMasks[i]!.testBit (p-(1 <<< i))) &&
          x.testBit (p-(1 <<< i))) := by
      cases decide (p ≥ (1 <<< i)) <;>
        cases x.testBit (p-(1 <<< i)) <;>
        cases lowMasks[i]!.testBit (p-(1 <<< i)) <;> rfl
    rw [regroup, hf, hm]
    simp only [Bool.false_and, Bool.true_and, Bool.and_true,
      Bool.and_false, Bool.false_or, Bool.or_false, Nat.add_comm (1 <<< i) p, he]



set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
theorem lowMask_bit_checked : ∀ (i : Fin 10) (p : Fin 1024),
    (lowMasks[i.val]!).testBit p.val = !(p.val.testBit i.val) := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
theorem highMask_bit_checked : ∀ (i : Fin 10) (p : Fin 1024),
    ((lowMasks[i.val]!) <<< (1 <<< i.val)).testBit p.val = p.val.testBit i.val := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
theorem lowMask_lt_checked : ∀ (i : Fin 10), lowMasks[i.val]! < 2 ^ 1024 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
theorem highMask_lt_checked : ∀ (i : Fin 10),
    ((lowMasks[i.val]!) <<< (1 <<< i.val)) < 2 ^ 1024 := by decide +kernel

lemma fastForkPhaseWitness {positive negative fi fj li lj i j : Nat} {a b : Bool}
    (hfi : ∀ p < 1024, fi.testBit p = negative.testBit (p ^^^ (1 <<< i)))
    (hfj : ∀ p < 1024, fj.testBit p = negative.testBit (p ^^^ (1 <<< j)))
    (hli : ∀ p, li.testBit p = (decide (p < 1024) && (p.testBit i == a)))
    (hlj : ∀ p, lj.testBit p = (decide (p < 1024) && (p.testBit j == b)))
    (hn : (positive &&& fi) &&& (positive &&& fj) &&& li &&& lj ≠ 0) :
    ∃ p < 1024, positive.testBit p = true ∧
      negative.testBit (p ^^^ (1 <<< i)) = true ∧
      negative.testBit (p ^^^ (1 <<< j)) = true ∧
      p.testBit i = a ∧ p.testBit j = b := by
  obtain ⟨p, hp⟩ := Nat.exists_testBit_of_ne_zero hn
  simp only [Nat.testBit_and, Bool.and_eq_true] at hp
  obtain ⟨⟨⟨⟨hpos, hflipI⟩, ⟨_, hflipJ⟩⟩, hmaskI⟩, hmaskJ⟩ := hp
  rw [hli] at hmaskI
  rw [hlj] at hmaskJ
  have hmaskI : p < 1024 ∧ p.testBit i = a := by simpa using hmaskI
  have hmaskJ : p < 1024 ∧ p.testBit j = b := by simpa using hmaskJ
  rw [hfi p hmaskI.1] at hflipI
  rw [hfj p hmaskI.1] at hflipJ
  exact ⟨p, hmaskI.1, hpos, hflipI, hflipJ, hmaskI.2, hmaskJ.2⟩

lemma boundedMask_bits {mask dim : Nat}
    (hlt : mask < 2 ^ dim) (bit : Nat → Bool)
    (hbit : ∀ p < dim, mask.testBit p = bit p) (p : Nat) :
    mask.testBit p = (decide (p < dim) && bit p) := by
  by_cases hp : p < dim
  · simp [hp, hbit p hp]
  · have hpow : 2 ^ dim ≤ 2 ^ p := Nat.pow_le_pow_right (by decide) (by omega)
    have hzero := Nat.testBit_lt_two_pow (hlt.trans_le hpow)
    simp [hp, hzero]


lemma fastOppositeCorners {positive negative fi fj gi gj li lj mi mj i j : Nat}
    {a b : Bool}
    (hfi : ∀ p < 1024, fi.testBit p = negative.testBit (p ^^^ (1 <<< i)))
    (hfj : ∀ p < 1024, fj.testBit p = negative.testBit (p ^^^ (1 <<< j)))
    (hgi : ∀ p < 1024, gi.testBit p = positive.testBit (p ^^^ (1 <<< i)))
    (hgj : ∀ p < 1024, gj.testBit p = positive.testBit (p ^^^ (1 <<< j)))
    (hli : ∀ p, li.testBit p = (decide (p < 1024) && (p.testBit i == a)))
    (hlj : ∀ p, lj.testBit p = (decide (p < 1024) && (p.testBit j == b)))
    (hmi : ∀ p, mi.testBit p = (decide (p < 1024) && (p.testBit i == !a)))
    (hmj : ∀ p, mj.testBit p = (decide (p < 1024) && (p.testBit j == !b)))
    (hpos : (positive &&& fi) &&& (positive &&& fj) &&& li &&& lj ≠ 0)
    (hneg : (negative &&& gi) &&& (negative &&& gj) &&& mi &&& mj ≠ 0) :
    ∃ p q, p < 1024 ∧ q < 1024 ∧
      positive.testBit p = true ∧ negative.testBit q = true ∧
      negative.testBit (p ^^^ (1 <<< i)) = true ∧
      negative.testBit (p ^^^ (1 <<< j)) = true ∧
      positive.testBit (q ^^^ (1 <<< i)) = true ∧
      positive.testBit (q ^^^ (1 <<< j)) = true ∧
      p.testBit i ≠ q.testBit i ∧ p.testBit j ≠ q.testBit j := by
  obtain ⟨p, hp, hP, hPi, hPj, hia, hjb⟩ :=
    fastForkPhaseWitness hfi hfj hli hlj hpos
  obtain ⟨q, hq, hQ, hQi, hQj, hni, hnj⟩ :=
    fastForkPhaseWitness hgi hgj hmi hmj hneg
  refine ⟨p, q, hp, hq, hP, hQ, hPi, hPj, hQi, hQj, ?_, ?_⟩
  · rw [hia, hni]
    cases a <;> decide
  · rw [hjb, hnj]
    cases b <;> decide

lemma lowMask_bit {i : Nat} (hi : i < 10) (p : Nat) :
    lowMasks[i]!.testBit p = (decide (p < 1024) && !(p.testBit i)) := by
  apply boundedMask_bits (lowMask_lt_checked ⟨i, hi⟩)
  intro q hq
  exact lowMask_bit_checked ⟨i, hi⟩ ⟨q, hq⟩

lemma highMask_bit {i : Nat} (hi : i < 10) (p : Nat) :
    (lowMasks[i]! <<< (1 <<< i)).testBit p =
      (decide (p < 1024) && p.testBit i) := by
  apply boundedMask_bits (highMask_lt_checked ⟨i, hi⟩)
  intro q hq
  exact highMask_bit_checked ⟨i, hi⟩ ⟨q, hq⟩

def inspectNat {α : Sort u} (n : Nat) (k : Nat → α) : α :=
  match n with
  | 0 => k 0
  | p + 1 => k (p + 1)

lemma inspectNat_eq {α : Sort u} (n : Nat) (k : Nat → α) : inspectNat n k = k n := by
  cases n <;> rfl

def fastVertices (n positive negative : Nat) : List (Nat × Nat × Nat × Nat × Nat) :=
  (List.range n).map fun i =>
    let low := lowMasks[i]!
    let high := low <<< (1 <<< i)
    let forkP := positive &&& flipPatternBits i negative
    let forkN := negative &&& flipPatternBits i positive
    inspectNat forkP fun forkP =>
      inspectNat forkN fun forkN => (i,low,high,forkP,forkN)

def edgeBoolFast (vi vj : Nat × Nat × Nat × Nat × Nat) : Bool :=
  let (_,li,hi,pi,ni) := vi
  let (_,lj,hj,pj,nj) := vj
  let cp := pi &&& pj
  let cn := ni &&& nj
  (!(cp &&& li &&& lj == 0) && !(cn &&& hi &&& hj == 0)) ||
  (!(cp &&& hi &&& lj == 0) && !(cn &&& li &&& hj == 0)) ||
  (!(cp &&& li &&& hj == 0) && !(cn &&& hi &&& lj == 0)) ||
  (!(cp &&& hi &&& hj == 0) && !(cn &&& li &&& lj == 0))

def criticalEdgesFast (ws : List Nat) : List (Nat × Nat) :=
  let (positive, negative) := patternSets (labelledPatterns ws)
  inspectNat positive fun positive =>
    inspectNat negative fun negative =>
      (pairs (fastVertices ws.length positive negative)).filterMap fun (vi,vj,_) =>
        if edgeBoolFast vi vj then some (vi.1,vj.1) else none

def hasCriticalEdgeFast (ws : List Nat) : Bool :=
  let (positive, negative) := patternSets (labelledPatterns ws)
  inspectNat positive fun positive =>
    inspectNat negative fun negative =>
      (pairs (fastVertices ws.length positive negative)).any fun (vi,vj,_) =>
        edgeBoolFast vi vj


def adj_phaseMask (i : Nat) (a : Bool) : Nat :=
  if a then lowMasks[i]! <<< (1 <<< i) else lowMasks[i]!

lemma adj_phaseMask_bit {i : Nat} (hi : i < 10) (a : Bool) (p : Nat) :
    (adj_phaseMask i a).testBit p = (decide (p < 1024) && (p.testBit i == a)) := by
  cases a with
  | false =>
    change lowMasks[i]!.testBit p = _
    rw [lowMask_bit hi]
    cases p.testBit i <;> rfl
  | true =>
    change (lowMasks[i]! <<< (1 <<< i)).testBit p = _
    rw [highMask_bit hi]
    cases p.testBit i <;> rfl

def adj_corner (positive negative i j : Nat) (a b : Bool) : Nat :=
  (positive &&& flipPatternBits i negative) &&&
    (positive &&& flipPatternBits j negative) &&& adj_phaseMask i a &&& adj_phaseMask j b

lemma adj_fast_corner {ps : List (Nat × Bool)} {i j : Nat} (hi : i < 10) (hj : j < 10)
    {a b : Bool}
    (hp : adj_corner (patternSets ps).1 (patternSets ps).2 i j a b ≠ 0)
    (hn : adj_corner (patternSets ps).2 (patternSets ps).1 i j (!a) (!b) ≠ 0) :
    adj_patternCorners ps i j := by
  obtain ⟨p,q,_,_,hP,hN,hPi,hPj,hNi,hNj,hij,hij'⟩ :=
    fastOppositeCorners
      (fun p hp => flipPatternBits_bit hi hp _)
      (fun p hp => flipPatternBits_bit hj hp _)
      (fun p hp => flipPatternBits_bit hi hp _)
      (fun p hp => flipPatternBits_bit hj hp _)
      (adj_phaseMask_bit hi a) (adj_phaseMask_bit hj b)
      (adj_phaseMask_bit hi (!a)) (adj_phaseMask_bit hj (!b)) hp hn
  exact ⟨p,q,(adj_patternSets_pos ps p).mp hP,(adj_patternSets_neg ps q).mp hN,
    (adj_patternSets_neg ps _).mp hPi,(adj_patternSets_neg ps _).mp hPj,
    (adj_patternSets_pos ps _).mp hNi,(adj_patternSets_pos ps _).mp hNj,hij,hij'⟩

lemma adj_singles_map {α β : Type} (f : α → β) (ws : List α) :
    singles (ws.map f) = (singles ws).map (fun (a,rest) => (f a,rest.map f)) := by
  induction ws with
  | nil => rfl
  | cons a ws ih => simp [singles, ih, List.map_map, Function.comp_def]

lemma adj_pairs_map {α β : Type} (f : α → β) (ws : List α) :
    pairs (ws.map f) = (pairs ws).map (fun (a,b,rest) => (f a,f b,rest.map f)) := by
  induction ws with
  | nil => rfl
  | cons a ws ih => simp [pairs, adj_singles_map, ih, List.map_map, Function.comp_def]

def adj_vertex (positive negative i : Nat) : Nat × Nat × Nat × Nat × Nat :=
  (i,lowMasks[i]!,lowMasks[i]! <<< (1 <<< i),
    positive &&& flipPatternBits i negative,negative &&& flipPatternBits i positive)

def adj_edge (positive negative i j : Nat) : Bool :=
  (!(adj_corner positive negative i j false false == 0) &&
     !(adj_corner negative positive i j true true == 0)) ||
  (!(adj_corner positive negative i j true false == 0) &&
     !(adj_corner negative positive i j false true == 0)) ||
  (!(adj_corner positive negative i j false true == 0) &&
     !(adj_corner negative positive i j true false == 0)) ||
  (!(adj_corner positive negative i j true true == 0) &&
     !(adj_corner negative positive i j false false == 0))

lemma adj_edge_sound {ps : List (Nat × Bool)} {i j : Nat} (hi : i < 10) (hj : j < 10)
    (he : adj_edge (patternSets ps).1 (patternSets ps).2 i j = true) :
    adj_patternCorners ps i j := by
  simp only [adj_edge, Bool.or_eq_true, Bool.and_eq_true] at he
  rcases he with ((h | h) | h) | h
  · exact adj_fast_corner hi hj (a := false) (b := false) (by simpa using h.1) (by simpa using h.2)
  · exact adj_fast_corner hi hj (a := true) (b := false) (by simpa using h.1) (by simpa using h.2)
  · exact adj_fast_corner hi hj (a := false) (b := true) (by simpa using h.1) (by simpa using h.2)
  · exact adj_fast_corner hi hj (a := true) (b := true) (by simpa using h.1) (by simpa using h.2)

lemma adj_criticalEdgesFast_eq (ws : List Nat) :
    criticalEdgesFast ws = (pairs (List.range ws.length)).filterMap (fun (i,j,_) =>
      if adj_edge (patternSets (labelledPatterns ws)).1 (patternSets (labelledPatterns ws)).2 i j
        then some (i,j) else none) := by
  unfold criticalEdgesFast
  simp only [inspectNat_eq, fastVertices]
  change (pairs ((List.range ws.length).map (adj_vertex _ _))).filterMap _ = _
  rw [adj_pairs_map, List.filterMap_map]
  rfl

lemma criticalEdgesFast_sound {ws : List Nat} {i j : Nat} (hw : ws.length ≤ 10)
    (he : (i,j) ∈ criticalEdgesFast ws) :
    criticalPair (BitVec.ofNat 128 goal) (adj_frontier ws) (adj_word ws i) (adj_word ws j) := by
  rw [adj_criticalEdgesFast_eq] at he
  obtain ⟨⟨a,b,rest⟩,hab,he⟩ := List.mem_filterMap.mp he
  change (if adj_edge (patternSets (labelledPatterns ws)).1
    (patternSets (labelledPatterns ws)).2 a b then some (a,b) else none) = some (i,j) at he
  split at he
  · rename_i hc
    have heq : (a,b) = (i,j) := Option.some.inj he
    cases heq
    obtain ⟨ha,hb,hne⟩ := pairs_range_bounds hab
    exact adj_corner_rows ha hb hne (adj_edge_sound (ha.trans_le hw) (hb.trans_le hw) hc)
  · simp at he




def criticalGraphFast (ws : List Nat) : List (Nat × Nat) :=
  let es := criticalEdgesFast ws
  (List.range ws.length).map fun i =>
    (i, es.foldl (fun mask (a,b) =>
      if a == i then mask ||| (1 <<< b)
      else if b == i then mask ||| (1 <<< a) else mask) 0)

lemma criticalPair_symm {width : Nat} {target : BitVec width}
    {S : Finset (BitVec width)} {a b : BitVec width}
    (h : criticalPair target S a b) : criticalPair target S b a := by
  obtain ⟨ha,hb,hne,p,q,ra,rb,sa,sb,hp,hq,hra,hrb,hsa,hsb,ua,ub,usa,usb,hpa,hpb⟩ := h
  exact ⟨hb,ha,Ne.symm hne,p,q,rb,ra,sb,sa,hp,hq,hrb,hra,hsb,hsa,ub,ua,usb,usa,hpb,hpa⟩

def adj_neighborStep (i acc : Nat) (e : Nat × Nat) : Nat :=
  if e.1 == i then acc ||| (1 <<< e.2)
  else if e.2 == i then acc ||| (1 <<< e.1) else acc

lemma adj_neighbor_bit (i acc j : Nat) (e : Nat × Nat) :
    (adj_neighborStep i acc e).testBit j =
      (acc.testBit j || decide ((e.1 = i ∧ e.2 = j) ∨ (e.2 = i ∧ e.1 = j))) := by
  obtain ⟨a,b⟩ := e
  by_cases ha : a = i <;> by_cases hb : b = i <;>
    simp [adj_neighborStep, ha, hb, Nat.testBit_or, Nat.shiftLeft_eq, Nat.testBit_two_pow]

lemma adj_neighbor_fold (es : List (Nat × Nat)) (i acc j : Nat) :
    (es.foldl (adj_neighborStep i) acc).testBit j =
      (acc.testBit j || es.any (fun (a,b) => decide ((a=i ∧ b=j) ∨ (b=i ∧ a=j)))) := by
  induction es generalizing acc with
  | nil => simp
  | cons e es ih =>
    rw [List.foldl_cons, ih, adj_neighbor_bit]
    simp only [List.any_cons, Bool.or_assoc]

lemma adj_neighbor_sound {es : List (Nat × Nat)} {i j : Nat}
    (h : (es.foldl (adj_neighborStep i) 0).testBit j = true) :
    (i,j) ∈ es ∨ (j,i) ∈ es := by
  rw [adj_neighbor_fold] at h
  simp only [Nat.zero_testBit, Bool.false_or, List.any_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨a,b⟩,he,(⟨ha,hb⟩ | ⟨hb,ha⟩)⟩ := h
  · dsimp at ha hb; subst a; subst b; exact Or.inl he
  · dsimp at ha hb; subst a; subst b; exact Or.inr he

lemma criticalGraphFast_sound {ws : List Nat} {i adj j : Nat} (hw : ws.length ≤ 10)
    (hi : (i,adj) ∈ criticalGraphFast ws) (hb : adj.testBit j = true) :
    criticalPair (BitVec.ofNat 128 goal) (adj_frontier ws) (adj_word ws i) (adj_word ws j) := by
  obtain ⟨k,_,he⟩ := List.mem_map.mp hi
  have he1 : k = i := congrArg Prod.fst he
  subst k
  have he2 := congrArg Prod.snd he
  change (criticalEdgesFast ws).foldl (adj_neighborStep i) 0 = adj at he2
  rw [← he2] at hb
  rcases adj_neighbor_sound hb with he | he
  · exact criticalEdgesFast_sound hw he
  · exact criticalPair_symm (criticalEdgesFast_sound hw he)

lemma criticalEdgesFast_exists {ws : List Nat} (hw : ws.length ≤ 10)
    (he : (criticalEdgesFast ws).isEmpty = false) :
    ∃ i j, criticalPair (BitVec.ofNat 128 goal) (adj_frontier ws) (adj_word ws i) (adj_word ws j) := by
  have hn : criticalEdgesFast ws ≠ [] := by simpa using he
  obtain ⟨⟨i,j⟩,hm⟩ := List.exists_mem_of_ne_nil _ hn
  exact ⟨i,j,criticalEdgesFast_sound hw hm⟩


lemma hasCriticalEdgeFast_edges {ws : List Nat} (h : hasCriticalEdgeFast ws = true) :
    ∃ i j, (i,j) ∈ criticalEdgesFast ws := by
  unfold hasCriticalEdgeFast at h
  simp only [inspectNat_eq] at h
  obtain ⟨⟨vi,vj,rest⟩,hm,he⟩ := List.any_eq_true.mp h
  refine ⟨vi.1,vj.1,?_⟩
  unfold criticalEdgesFast
  simp only [inspectNat_eq]
  refine List.mem_filterMap.mpr ⟨(vi,vj,rest),hm,?_⟩
  change (if edgeBoolFast vi vj then some (vi.1,vj.1) else none) = some (vi.1,vj.1)
  rw [he]
  rfl

lemma hasCriticalEdgeFast_sound {ws : List Nat} (hw : ws.length ≤ 10)
    (h : hasCriticalEdgeFast ws = true) :
    ∃ i j, criticalPair (BitVec.ofNat 128 goal) (adj_frontier ws) (adj_word ws i) (adj_word ws j) := by
  obtain ⟨i,j,he⟩ := hasCriticalEdgeFast_edges h
  exact ⟨i,j,criticalEdgesFast_sound hw he⟩

end PEqualNP.Outside.L_meta_10760.KernelNat128

namespace PEqualNP.Outside.L_meta_10760.HT128

open RestrictionSixProof KernelNat128

def graph (ws : List Nat) : List Nat :=
  (criticalGraphFast ws).map Prod.snd

lemma graph_length (ws : List Nat) : (graph ws).length = ws.length := by
  simp [graph, criticalGraphFast]

lemma graph_row (ws : List Nat) (i : Nat) (hi : i < ws.length) :
    (i, (graph ws).getD i 0) ∈ criticalGraphFast ws := by
  unfold graph criticalGraphFast
  simp only [List.map_map, Function.comp_def]
  apply List.mem_map.mpr
  refine ⟨i, List.mem_range.mpr hi, ?_⟩
  simp [List.getD_eq_getElem?_getD, hi]

lemma live_coloring_up {n k : Nat} {ws : List Nat}
    (hnk : n ≤ k) (hnd : (ws.map W).Nodup)
    (run : Live true (W goal) n (ws.map W).toFinset) :
    ∃ color : Sig → Nat,
      (∀ a ∈ adj_frontier ws, color a < k + 2 - ws.length) ∧
      ∀ a b, criticalPair (W goal) (adj_frontier ws) a b → color a ≠ color b := by
  obtain ⟨color, bound, proper⟩ := Live_criticalPair_coloring_self run
  have card : (ws.map W).toFinset.card = ws.length := by
    simpa only [List.length_map] using List.toFinset_card_of_nodup hnd
  refine ⟨color, ?_, proper⟩
  intro a ha
  have hb := bound a ha
  rw [card] at hb
  omega

lemma graph_colorable_of_live {n k : Nat} {ws : List Nat}
    (hnk : n ≤ k) (hnd : (ws.map W).Nodup) (hw : ws.length ≤ 10)
    (run : Live true (W goal) n (ws.map W).toFinset) :
    graphColorable (graph ws) (k + 2 - ws.length) := by
  obtain ⟨color, bound, proper⟩ := live_coloring_up hnk hnd run
  refine ⟨fun i => color (adj_word ws i), ?_, ?_⟩
  · intro i hi
    rw [graph_length] at hi
    exact bound _ (adj_word_mem hi)
  · intro i hi j hj he
    rw [graph_length] at hi hj
    exact proper _ _ (criticalGraphFast_sound hw (graph_row ws i hi) he)

def allowed (k : Nat) (ws : List Nat) : Bool :=
  if ws.length ≤ 10 then
    let colors := k + 2 - ws.length
    if 4 ≤ colors then true
    else if colors = 1 then !hasCriticalEdgeFast ws
    else graphColorDegreeFast (graph ws) colors
  else true

lemma allowed_complete {n k : Nat} {ws : List Nat}
    (hnk : n ≤ k) (hnd : (ws.map W).Nodup)
    (run : Live true (W goal) n (ws.map W).toFinset) : allowed k ws = true := by
  unfold allowed
  split
  next hw =>
    dsimp only
    split
    · rfl
    · split
      next hone =>
        cases he : hasCriticalEdgeFast ws with
        | false => rfl
        | true =>
          obtain ⟨i, j, edge⟩ := hasCriticalEdgeFast_sound hw he
          obtain ⟨color, bound, proper⟩ := live_coloring_up hnk hnd run
          have hi := bound _ edge.1
          have hj := bound _ edge.2.1
          have hne := proper _ _ edge
          omega
      next notone =>
        exact graphColorDegreeFast_complete (graph_colorable_of_live hnk hnd hw run)
  next outside => rfl

lemma rejected_impossible {k : Nat} {ws : List Nat}
    (hnd : (ws.map W).Nodup) (rejected : allowed k ws = false) :
    Impossible true (W goal) k (ws.map W).toFinset := by
  intro n hn run
  have accepted := allowed_complete hn hnd run
  rw [rejected] at accepted
  cases accepted

end PEqualNP.Outside.L_meta_10760.HT128

namespace PEqualNP.Outside.L_meta_10760.KernelNat128Rows

open KernelNat128

variable {goal : Nat} {rows : List Nat}

def labelledPatterns (goal : Nat) (rows : List Nat) (ws : List Nat) : List (Nat × Bool) :=
  (rows.filter (fun r => decide (r < 128))).map fun row => (rowPattern row ws, (goal >>> row) &&& 1 == 1)

lemma adj_labelled {ws : List Nat} {pattern : Nat} {label : Bool}
    (hm : (pattern,label) ∈ labelledPatterns goal rows ws) :
    ∃ r : Fin 128, rowPattern r.val ws = pattern ∧ goal.testBit r.val = label := by
  obtain ⟨r,hr,he⟩ := List.mem_map.mp hm
  have hr' : r < 128 := of_decide_eq_true (List.mem_filter.mp hr).2
  refine ⟨⟨r,hr'⟩,congrArg Prod.fst he,?_⟩
  have hl := congrArg Prod.snd he
  change bitTest goal r = label at hl
  rwa [adj_bitTest] at hl

lemma adj_corner_rows {ws : List Nat} {i j : Nat}
    (hi : i < ws.length) (hj : j < ws.length) (hij : i ≠ j)
    (hc : adj_patternCorners (labelledPatterns goal rows ws) i j) :
    criticalPair (BitVec.ofNat 128 goal) (adj_frontier ws) (adj_word ws i) (adj_word ws j) := by
  obtain ⟨x,y,hx,hy,hxi,hxj,hyi,hyj,hpi,hpj⟩ := hc
  obtain ⟨p,hp,hpt⟩ := adj_labelled hx
  obtain ⟨q,hq,hqt⟩ := adj_labelled hy
  obtain ⟨ra,hra,hrat⟩ := adj_labelled hxi
  obtain ⟨rb,hrb,hrbt⟩ := adj_labelled hxj
  obtain ⟨sa,hsa,hsat⟩ := adj_labelled hyi
  obtain ⟨sb,hsb,hsbt⟩ := adj_labelled hyj
  have hfra : rowPattern ra.val ws = rowPattern p.val ws ^^^ (1 <<< i) := by rwa [hp]
  have hfrb : rowPattern rb.val ws = rowPattern p.val ws ^^^ (1 <<< j) := by rwa [hp]
  have hfsa : rowPattern sa.val ws = rowPattern q.val ws ^^^ (1 <<< i) := by rwa [hq]
  have hfsb : rowPattern sb.val ws = rowPattern q.val ws ^^^ (1 <<< j) := by rwa [hq]
  have ua := adj_flip_unique hfra
  have ub := adj_flip_unique hfrb
  have usa := adj_unique_symm (adj_flip_unique hfsa)
  have usb := adj_unique_symm (adj_flip_unique hfsb)
  have hne : adj_word ws i ≠ adj_word ws j := by
    have hb := rowPattern_flip hfra j
    simp only [hij, decide_false, Bool.xor_false] at hb
    have hbe : (adj_word ws j)[p.val] = (adj_word ws j)[ra.val] := by
      simpa only [adj_word_bit] using hb.symm
    intro he
    exact ua.1 (by rw [he]; exact hbe)
  have hip : (adj_word ws i)[p.val] ≠ (adj_word ws i)[q.val] := by
    simpa only [adj_word_bit, ← rowPattern_bit, hp, hq] using hpi
  have hjp : (adj_word ws j)[p.val] ≠ (adj_word ws j)[q.val] := by
    simpa only [adj_word_bit, ← rowPattern_bit, hp, hq] using hpj
  have his : (adj_word ws i)[sa.val] = !(adj_word ws i)[q.val] := by
    have hb := rowPattern_flip hfsa i
    simpa only [adj_word_bit, decide_true, Bool.xor_true] using hb
  have hjs : (adj_word ws j)[sb.val] = !(adj_word ws j)[q.val] := by
    have hb := rowPattern_flip hfsb j
    simpa only [adj_word_bit, decide_true, Bool.xor_true] using hb
  have hipa : (adj_word ws i)[p.val] = (adj_word ws i)[sa.val] := by
    rw [his]
    exact Bool.eq_not.mpr hip
  have hjpb : (adj_word ws j)[p.val] = (adj_word ws j)[sb.val] := by
    rw [hjs]
    exact Bool.eq_not.mpr hjp
  refine ⟨adj_word_mem hi, adj_word_mem hj, hne, p,q,ra,rb,sa,sb,?_,?_,?_,?_,?_,?_,ua,ub,usa,usb,hipa,hjpb⟩
  all_goals rwa [adj_ofNat_bit]

def criticalEdgesFast (goal : Nat) (rows : List Nat) (ws : List Nat) : List (Nat × Nat) :=
  let (positive, negative) := patternSets (labelledPatterns goal rows ws)
  inspectNat positive fun positive =>
    inspectNat negative fun negative =>
      (pairs (fastVertices ws.length positive negative)).filterMap fun (vi,vj,_) =>
        if edgeBoolFast vi vj then some (vi.1,vj.1) else none

def hasCriticalEdgeFast (goal : Nat) (rows : List Nat) (ws : List Nat) : Bool :=
  let (positive, negative) := patternSets (labelledPatterns goal rows ws)
  inspectNat positive fun positive =>
    inspectNat negative fun negative =>
      (pairs (fastVertices ws.length positive negative)).any fun (vi,vj,_) =>
        edgeBoolFast vi vj

lemma adj_criticalEdgesFast_eq (ws : List Nat) :
    criticalEdgesFast goal rows ws = (pairs (List.range ws.length)).filterMap (fun (i,j,_) =>
      if adj_edge (patternSets (labelledPatterns goal rows ws)).1 (patternSets (labelledPatterns goal rows ws)).2 i j
        then some (i,j) else none) := by
  unfold criticalEdgesFast
  simp only [inspectNat_eq, fastVertices]
  change (pairs ((List.range ws.length).map (adj_vertex _ _))).filterMap _ = _
  rw [adj_pairs_map, List.filterMap_map]
  rfl

lemma criticalEdgesFast_sound {ws : List Nat} {i j : Nat} (hw : ws.length ≤ 10)
    (he : (i,j) ∈ criticalEdgesFast goal rows ws) :
    criticalPair (BitVec.ofNat 128 goal) (adj_frontier ws) (adj_word ws i) (adj_word ws j) := by
  rw [adj_criticalEdgesFast_eq] at he
  obtain ⟨⟨a,b,rest⟩,hab,he⟩ := List.mem_filterMap.mp he
  change (if adj_edge (patternSets (labelledPatterns goal rows ws)).1
    (patternSets (labelledPatterns goal rows ws)).2 a b then some (a,b) else none) = some (i,j) at he
  split at he
  · rename_i hc
    have heq : (a,b) = (i,j) := Option.some.inj he
    cases heq
    obtain ⟨ha,hb,hne⟩ := pairs_range_bounds hab
    exact adj_corner_rows ha hb hne (adj_edge_sound (ha.trans_le hw) (hb.trans_le hw) hc)
  · simp at he

def criticalGraphFast (goal : Nat) (rows : List Nat) (ws : List Nat) : List (Nat × Nat) :=
  let es := criticalEdgesFast goal rows ws
  (List.range ws.length).map fun i =>
    (i, es.foldl (fun mask (a,b) =>
      if a == i then mask ||| (1 <<< b)
      else if b == i then mask ||| (1 <<< a) else mask) 0)

lemma criticalGraphFast_sound {ws : List Nat} {i adj j : Nat} (hw : ws.length ≤ 10)
    (hi : (i,adj) ∈ criticalGraphFast goal rows ws) (hb : adj.testBit j = true) :
    criticalPair (BitVec.ofNat 128 goal) (adj_frontier ws) (adj_word ws i) (adj_word ws j) := by
  obtain ⟨k,_,he⟩ := List.mem_map.mp hi
  have he1 : k = i := congrArg Prod.fst he
  subst k
  have he2 := congrArg Prod.snd he
  change (criticalEdgesFast goal rows ws).foldl (adj_neighborStep i) 0 = adj at he2
  rw [← he2] at hb
  rcases adj_neighbor_sound hb with he | he
  · exact criticalEdgesFast_sound hw he
  · exact criticalPair_symm (criticalEdgesFast_sound hw he)

lemma criticalEdgesFast_exists {ws : List Nat} (hw : ws.length ≤ 10)
    (he : (criticalEdgesFast goal rows ws).isEmpty = false) :
    ∃ i j, criticalPair (BitVec.ofNat 128 goal) (adj_frontier ws) (adj_word ws i) (adj_word ws j) := by
  have hn : criticalEdgesFast goal rows ws ≠ [] := by simpa using he
  obtain ⟨⟨i,j⟩,hm⟩ := List.exists_mem_of_ne_nil _ hn
  exact ⟨i,j,criticalEdgesFast_sound hw hm⟩

lemma hasCriticalEdgeFast_edges {ws : List Nat} (h : hasCriticalEdgeFast goal rows ws = true) :
    ∃ i j, (i,j) ∈ criticalEdgesFast goal rows ws := by
  unfold hasCriticalEdgeFast at h
  simp only [inspectNat_eq] at h
  obtain ⟨⟨vi,vj,rest⟩,hm,he⟩ := List.any_eq_true.mp h
  refine ⟨vi.1,vj.1,?_⟩
  unfold criticalEdgesFast
  simp only [inspectNat_eq]
  refine List.mem_filterMap.mpr ⟨(vi,vj,rest),hm,?_⟩
  change (if edgeBoolFast vi vj then some (vi.1,vj.1) else none) = some (vi.1,vj.1)
  rw [he]
  rfl

lemma hasCriticalEdgeFast_sound {ws : List Nat} (hw : ws.length ≤ 10)
    (h : hasCriticalEdgeFast goal rows ws = true) :
    ∃ i j, criticalPair (BitVec.ofNat 128 goal) (adj_frontier ws) (adj_word ws i) (adj_word ws j) := by
  obtain ⟨i,j,he⟩ := hasCriticalEdgeFast_edges h
  exact ⟨i,j,criticalEdgesFast_sound hw he⟩

set_option maxRecDepth 10000 in
lemma labelledPatterns_full (ws : List Nat) :
    labelledPatterns KernelNat128.goal (List.range 128) ws =
      KernelNat128.labelledPatterns ws := rfl

set_option maxRecDepth 10000 in
lemma criticalGraphFast_full (ws : List Nat) :
    criticalGraphFast KernelNat128.goal (List.range 128) ws =
      KernelNat128.criticalGraphFast ws := rfl

set_option maxRecDepth 10000 in
lemma hasCriticalEdgeFast_full (ws : List Nat) :
    hasCriticalEdgeFast KernelNat128.goal (List.range 128) ws =
      KernelNat128.hasCriticalEdgeFast ws := rfl

end PEqualNP.Outside.L_meta_10760.KernelNat128Rows

namespace PEqualNP.Outside.L_meta_10760.HT128Rows

open RestrictionSixProof KernelNat128

variable {target : Nat} {rows : List Nat}

def graph (target : Nat) (rows : List Nat) (ws : List Nat) : List Nat :=
  (KernelNat128Rows.criticalGraphFast target rows ws).map Prod.snd

lemma graph_length (ws : List Nat) : (graph target rows ws).length = ws.length := by
  simp [graph, KernelNat128Rows.criticalGraphFast]

lemma graph_row (ws : List Nat) (i : Nat) (hi : i < ws.length) :
    (i, (graph target rows ws).getD i 0) ∈ KernelNat128Rows.criticalGraphFast target rows ws := by
  unfold graph KernelNat128Rows.criticalGraphFast
  simp only [List.map_map, Function.comp_def]
  apply List.mem_map.mpr
  refine ⟨i, List.mem_range.mpr hi, ?_⟩
  simp [List.getD_eq_getElem?_getD, hi]

lemma live_coloring_up {n k : Nat} {ws : List Nat}
    (hnk : n ≤ k) (hnd : (ws.map W).Nodup)
    (run : Live true (W target) n (ws.map W).toFinset) :
    ∃ color : Sig → Nat,
      (∀ a ∈ adj_frontier ws, color a < k + 2 - ws.length) ∧
      ∀ a b, criticalPair (W target) (adj_frontier ws) a b → color a ≠ color b := by
  obtain ⟨color, bound, proper⟩ := Live_criticalPair_coloring_self run
  have card : (ws.map W).toFinset.card = ws.length := by
    simpa only [List.length_map] using List.toFinset_card_of_nodup hnd
  refine ⟨color, ?_, proper⟩
  intro a ha
  have hb := bound a ha
  rw [card] at hb
  omega

lemma graph_colorable_of_live {n k : Nat} {ws : List Nat}
    (hnk : n ≤ k) (hnd : (ws.map W).Nodup) (hw : ws.length ≤ 10)
    (run : Live true (W target) n (ws.map W).toFinset) :
    graphColorable (graph target rows ws) (k + 2 - ws.length) := by
  obtain ⟨color, bound, proper⟩ := live_coloring_up hnk hnd run
  refine ⟨fun i => color (adj_word ws i), ?_, ?_⟩
  · intro i hi
    rw [graph_length] at hi
    exact bound _ (adj_word_mem hi)
  · intro i hi j hj he
    rw [graph_length] at hi hj
    exact proper _ _ (KernelNat128Rows.criticalGraphFast_sound hw (graph_row ws i hi) he)

def allowed (target : Nat) (rows : List Nat) (k : Nat) (ws : List Nat) : Bool :=
  if ws.length ≤ 10 then
    let colors := k + 2 - ws.length
    if 4 ≤ colors then true
    else if colors = 1 then !KernelNat128Rows.hasCriticalEdgeFast target rows ws
    else graphColorDegreeFast (graph target rows ws) colors
  else true

lemma allowed_complete {n k : Nat} {ws : List Nat}
    (hnk : n ≤ k) (hnd : (ws.map W).Nodup)
    (run : Live true (W target) n (ws.map W).toFinset) : allowed target rows k ws = true := by
  unfold allowed
  split
  next hw =>
    dsimp only
    split
    · rfl
    · split
      next hone =>
        cases he : KernelNat128Rows.hasCriticalEdgeFast target rows ws with
        | false => rfl
        | true =>
          obtain ⟨i, j, edge⟩ := KernelNat128Rows.hasCriticalEdgeFast_sound hw he
          obtain ⟨color, bound, proper⟩ := live_coloring_up hnk hnd run
          have hi := bound _ edge.1
          have hj := bound _ edge.2.1
          have hne := proper _ _ edge
          omega
      next notone =>
        exact graphColorDegreeFast_complete (graph_colorable_of_live hnk hnd hw run)
  next outside => rfl

lemma rejected_impossible {k : Nat} {ws : List Nat}
    (hnd : (ws.map W).Nodup) (rejected : allowed target rows k ws = false) :
    Impossible true (W target) k (ws.map W).toFinset := by
  intro n hn run
  have accepted := allowed_complete (rows := rows) hn hnd run
  rw [rejected] at accepted
  cases accepted

end PEqualNP.Outside.L_meta_10760.HT128Rows
