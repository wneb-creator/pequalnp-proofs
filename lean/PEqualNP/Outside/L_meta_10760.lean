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

def keeps : List (Bool × Bool) := [(true,true),(true,false),(false,true),(false,false)]
def bl (b : Bool) : Nat := bif b then 1 else 0
def mkCut (Z : List SliceD) (c : Nat × List (Nat × Nat × Nat)) : CutV :=
  let s := Z.getD c.1 (0,0,[])
  (s.1,s.2.1,c.2.length,mkPool (initPool s.1 s.2.2) c.2)
def hintOK (k : Nat) (cuts : List CutV) (seps : List (Nat × Nat)) (rest : List Nat) (a b z : Nat) (ka kb : Bool) (i : Nat) : Bool :=
  bif Nat.blt i 1000 then (match cuts[i]? with
    | some c => cutEval k rest a b z ka kb c
    | none => false)
  else (match seps[i-1000]? with
    | some q => sepEval rest a b z ka kb q
    | none => false)
def kidOK (k : Nat) (next : List (List Nat)) (cuts : List CutV) (seps : List (Nat × Nat)) (rest : List Nat) (hints : List Nat)
    (a b z : Nat) (kk : Bool × Bool) : Bool :=
  Nat.blt k (Nat.add (Nat.add rest.length (Nat.add (bl kk.1) (bl kk.2))) 0) ||
  hints.any (hintOK k cuts seps rest a b z kk.1 kk.2) ||
  next.any (beqL (kidN rest a b z kk.1 kk.2))
def pairOK (k : Nat) (next : List (List Nat)) (cuts : List CutV) (seps : List (Nat × Nat)) (s : List Nat)
    (p : Nat × Nat × List Nat) (hints : List Nat) : Bool :=
  [0,1,2,3].all fun o =>
    let z := nb o p.1 p.2.1
    mem1 z s || Nat.beq z 0 || Nat.beq z full ||
      keeps.all (kidOK k next cuts seps p.2.2 hints p.1 p.2.1 z)
def allZip (f : Nat × Nat × List Nat → List Nat → Bool) : List (Nat × Nat × List Nat) → List (List Nat) → Bool
  | [],_ => true
  | p::ps,[] => f p [] && allZip f ps []
  | p::ps,h::hs => f p h && allZip f ps hs
lemma allZip_ok {f ps hs} (h : allZip f ps hs = true) : ∀ p ∈ ps, ∃ x, f p x = true := by
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
lemma asc_ok {l : List Nat} (h : asc l = true) : l.Pairwise (· < ·) ∧ ∀ x ∈ l, x < 2^128 := by
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
lemma asc_nodup {l : List Nat} (h : asc l = true) : l.Nodup ∧ (l.map W).Nodup := by
  obtain ⟨h1,h2⟩ := asc_ok h
  have nd : l.Nodup := h1.imp (fun h => Nat.ne_of_lt h)
  refine ⟨nd,?_⟩
  refine nd.map_on ?_
  intro x hx y hy e
  exact W_inj (h2 x hx) (h2 y hy) e
def stOK (T : Nat) (Z : List SliceD) (k : Nat) (next : List (List Nat)) (st : StD) : Bool :=
  asc st.1 && !(mem1 T st.1) && st.2.2.1.all (sepOK T) && st.2.1.all (fun c => Nat.blt c.1 Z.length) &&
  allZip (pairOK k next (st.2.1.map (mkCut Z)) st.2.2.1 st.1) (pairs st.1) st.2.2.2
def levelOK (T : Nat) (Z : List SliceD) (k : Nat) (next : List (List Nat)) (D : List StD) : Bool :=
  D.all (stOK T Z k next)
def LevelN (R : List Nat) (T k : Nat) (D : List StD) : Prop :=
  ∀ st ∈ D, Impossible true (W T) k (st.1.map W).toFinset

lemma stStep {R T E Z k next st} (hB : baseOK T R E = true) (hZ : ∀ s ∈ Z, SliceN R T s)
    (hn : ∀ s ∈ next, Impossible true (W T) k (s.map W).toFinset)
    (h : stOK T Z k next st = true) : Impossible true (W T) (k+1) (st.1.map W).toFinset := by
  have b := baseOK_ok hB
  simp only [stOK,Bool.and_eq_true,Bool.not_eq_true',List.all_eq_true] at h
  obtain ⟨⟨⟨⟨ha,hT⟩,hs⟩,hcut⟩,hz⟩ := h
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
  have good : ∀ c ∈ st.2.1.map (mkCut Z), CutP R T c := by
    intro c hc
    obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hc
    have hi : q.1 < Z.length := by simpa only [Nat.blt_eq] using hcut q hq
    have hm : Z.getD q.1 (0,0,[]) ∈ Z := by
      rw [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hi]
      exact List.getElem_mem hi
    obtain ⟨⟨f,roots,dom,base,nc,lo⟩,hv⟩ := hZ _ hm
    have ps : PS f (roots.map observe) (initPool (Z.getD q.1 (0,0,[])).1 (Z.getD q.1 (0,0,[])).2.2) := by
      intro v hv'
      obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hv'
      rw [rf_land dom]
      exact base _ (List.mem_map_of_mem (hv j hj))
    obtain ⟨bank,b1,b2⟩ := mkPool_ok q.2 (Reach.start (u:=true) (roots:=roots.map observe)) ps
    refine ⟨f,roots,bank,dom,nc,?_,b2,lo⟩
    simpa [mkCut] using b1
  apply enum_step ndW hTm
  intro a' ha' b' hb' d hd ka kb hab fresh hprop hlen
  obtain ⟨a,ham,rfl⟩ := List.mem_map.mp ha'
  obtain ⟨c,hcm,rfl⟩ := List.mem_map.mp hb'
  have hac : a ≠ c := fun h => hab (by rw [h])
  have hd4 : d < 4 := by
    rcases hd with h | ⟨_,h⟩ <;> omega
  obtain ⟨p,hp,perm,ho⟩ := pairs_ok ham hcm hac
  obtain ⟨x,hx⟩ := allZip_ok hz p hp
  -- one unordered pair serves both orders
  have core : ∀ (o : Nat) (ja jb : Bool), o < 4 → W (nb o p.1 p.2.1) = bin d (W a) (W c) →
      (p.2.2.length + (bl ja + bl jb) ≤ k) →
      Impossible true (W T) k (kidW p.2.2 p.1 p.2.1 (nb o p.1 p.2.1) ja jb).toFinset := by
    intro o ja jb ho4 hW hl
    have hf := List.all_eq_true.mp hx o (by
      have : o = 0 ∨ o = 1 ∨ o = 2 ∨ o = 3 := by omega
      simpa using this)
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
    rcases hk with (hk | hk) | hk
    · exfalso
      rw [Nat.blt_eq] at hk
      have : k < p.2.2.length + (bl ja + bl jb) + 0 := hk
      omega
    · obtain ⟨i,_,hi⟩ := List.any_eq_true.mp hk
      unfold hintOK at hi
      cases hb : Nat.blt i 1000
      · rw [hb,cond_false] at hi
        cases hg : st.2.2.1[i-1000]? with
        | none => rw [hg] at hi; exact Bool.noConfusion hi
        | some q =>
          rw [hg] at hi
          exact sep_sound (hs q (List.mem_of_getElem? hg)) hi
      · rw [hb,cond_true] at hi
        cases hg : (st.2.1.map (mkCut Z))[i]? with
        | none => rw [hg] at hi; exact Bool.noConfusion hi
        | some q =>
          rw [hg] at hi
          exact cut_sound (good q (List.mem_of_getElem? hg)) nk hi
    · obtain ⟨s,hs',e⟩ := List.any_eq_true.mp hk
      rw [←kid_fin]
      rw [beqL_ok e]
      exact hn s hs'
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
  · have r := core d ka kb hd4 (W_nb _ _ _) fits
    have e : (childTwo (st.1.map W) (W p.1) (W p.2.1) d ka kb).toFinset = (kidW p.2.2 p.1 p.2.1 (nb d p.1 p.2.1) ka kb).toFinset := by
      unfold childTwo kidW
      rw [W_nb]
      ext v
      cases ka <;> cases kb <;> simp [kept,rp.mem_iff]
    rw [e]
    exact r
  · have hfl := flip_flip hd
    have f4 : flipOp d < 4 := by
      rcases hfl.1 with h | ⟨_,h⟩ <;> omega
    have r := core (flipOp d) kb ka f4 (by rw [W_nb]; exact (bin_flip hd _ _).symm) (by omega)
    have e : (childTwo (st.1.map W) (W p.2.1) (W p.1) d ka kb).toFinset = (kidW p.2.2 p.1 p.2.1 (nb (flipOp d) p.1 p.2.1) kb ka).toFinset := by
      unfold childTwo kidW
      rw [W_nb,bin_flip hd]
      ext v
      cases ka <;> cases kb <;> simp [kept,rp.mem_iff] <;> tauto
    rw [e]
    exact r

lemma levelStep {R T E Z k D' D} (hB : baseOK T R E = true) (hZ : ∀ s ∈ Z, SliceN R T s)
    (hI : LevelN R T k D') (h : levelOK T Z k (D'.map Prod.fst) D = true) : LevelN R T (k+1) D := by
  intro st hst
  refine stStep hB hZ ?_ (List.all_eq_true.mp h st hst)
  intro s hs
  obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hs
  exact hI q hq
lemma chunks {T : Nat} {Z : List SliceD} {k : Nat} {next : List (List Nat)} (c : Nat) (D : List StD) (n : Nat) (hc : 0 < c)
    (hl : Nat.ble D.length (n*c) = true)
    (h : ∀ i, i < n → levelOK T Z k next ((D.drop (i*c)).take c) = true) : levelOK T Z k next D = true := by
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
lemma lowSearch {R T E K D} (hB : baseOK T R E = true) (hI : LevelN R T K D)
    (h : (D.map Prod.fst).contains (R.map xN) = true) : LowN R T (K+1) := by
  apply lowOf hB
  simp only [List.contains_eq_mem,decide_eq_true_eq] at h
  obtain ⟨q,hq,e⟩ := List.mem_map.mp h
  have := hI q hq
  rw [e] at this
  simpa only [rootsW,List.map_map,Function.comp_def] using this
abbrev c0 : Nat := 0xcccccccccccccccc
abbrev c1 : Nat := 0xaaaaaaaaaaaaaaaa
abbrev c2 : Nat := 0xf0f0f0f0f0f0f0f0
abbrev c3 : Nat := 0xff00ff00ff00ff00
abbrev c5 : Nat := 0xffff0000ffff0000
abbrev c6 : Nat := 0xfafafafafafafafa
abbrev c7 : Nat := 0xffffff00ffffff00
abbrev c8 : Nat := 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0
abbrev c9 : Nat := 0xff00ff00ff00ff00ff00ff00ff00ff00
abbrev c10 : Nat := 0xffff0000ffff0000ffff0000ffff0000
abbrev c11 : Nat := 0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa
abbrev c12 : Nat := 0xcccccccccccccccccccccccccccccccc
abbrev c14 : Nat := 0xffaaffaaffaaffaa
abbrev c16 : Nat := 0xfff0fff0fff0fff0
abbrev c17 : Nat := 0xffffaaaaffffaaaa
abbrev c18 : Nat := 0xffccffccffccffcc
abbrev c19 : Nat := 0xfcfcfcfcfcfcfcfc
abbrev c20 : Nat := 0xfffff0f0fffff0f0
abbrev c21 : Nat := 0xeeeeeeeeeeeeeeee
abbrev c23 : Nat := 0xff00ff00ff00ff00ff00ff00ff00ff
abbrev c24 : Nat := 0x33333333333333333333333333333333
abbrev c25 : Nat := 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f
abbrev c27 : Nat := 0xfa00fa00fa00fa
abbrev c28 : Nat := 0x55555555555555555555555555555555
abbrev c31 : Nat := 0xffff0000ffff0000ffff0000ffff
abbrev c32 : Nat := 0x5555000055550000555500005555
abbrev c35 : Nat := 0x3030303030303030303030303030303
abbrev c36 : Nat := 0x550055005500550055005500550055
abbrev c40 : Nat := 0xcccc0000cccc0000cccc0000cccc
abbrev c41 : Nat := 0x30003000300030003000300030003
abbrev c42 : Nat := 0xcccc0000cccc0000cccc0000cccc0000
abbrev c44 : Nat := 0x3333000033330000333300003333
abbrev c46 : Nat := 0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee
abbrev c47 : Nat := 0x30303030303030303030303030303030
abbrev c48 : Nat := 0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0
abbrev c53 : Nat := 0xf0f00000f0f00000f0f00000f0f0
abbrev c54 : Nat := 0xcc000000cc000000cc000000cc
abbrev c55 : Nat := 0xf0f00000f0f00000f0f00000f0f00000
abbrev c56 : Nat := 0xfc00fc00fc00fc
abbrev c58 : Nat := 0xf000f000f000f000f000f000f000f
abbrev c61 : Nat := 0xcc00cc00cc00cc00cc00cc00cc00cc00
abbrev c65 : Nat := 0xaa00aa00aa00aa00aa00aa00aa00aa
abbrev c69 : Nat := 0x88888888888888888888888888888888
abbrev c70 : Nat := 0xf0c0f0c0f0c0f0c
abbrev c72 : Nat := 0xffffccccffffcccc
abbrev c74 : Nat := 0xf000f000f000f000f000f000f000f0
abbrev c75 : Nat := 0x5555550055555500
abbrev c81 : Nat := 0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a
abbrev c82 : Nat := 0xaa00aa00aa00aa00aa00aa00aa00aa00
abbrev c83 : Nat := 0x33003300330033003300330033003300
abbrev c110 : Nat := 0x1111000011110000111100001111
abbrev c111 : Nat := 0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c
abbrev c112 : Nat := 0x50005000500050005000500050005
abbrev c113 : Nat := 0xaaaa0000aaaa0000aaaa0000aaaa
abbrev c114 : Nat := 0x55000000550000005500000055
abbrev l0 : List Nat := [0, 1, 2, 3, 4]
abbrev l2 : List Nat := [0,1,1000,1001,1002]
abbrev l3 : List Nat := [c1,c0,c2,c3,c5]
abbrev l4 : List Nat := [0,1,1000,2,3,1001,1002]
abbrev l5 : List Nat := [c1,c0,c2,c3]
abbrev l7 : List Nat := [c1,c0,c2,c19,c3,c5]
def d0 : Nat := c69
def d1 : List Nat := [0, 1]
def d2 : List (Nat × Nat × Nat) := [(0,2,3),(1,1,3)]
lemma d3 : baseOK d0 d1 d2 = true := by decide +kernel
lemma d4 : LowN d1 d0 1 := lowCount d3 (by decide +kernel)
def d5 : Nat := c46
def d6 : List Nat := [0, 1]
def d7 : List (Nat × Nat × Nat) := [(0,0,1),(1,0,2)]
lemma d8 : baseOK d5 d6 d7 = true := by decide +kernel
lemma d9 : LowN d6 d5 1 := lowCount d8 (by decide +kernel)
def d10 : Nat := 0xeaeaeaeaeaeaeaeaeaeaeaeaeaeaeaea
def d11 : List Nat := [0, 1, 2]
def d12 : List (Nat × Nat × Nat) := [(0,0,1),(1,4,6),(2,2,6)]
lemma d13 : baseOK d10 d11 d12 = true := by decide +kernel
lemma d14 : LowN d11 d10 2 := lowCount d13 (by decide +kernel)
def d15 : Nat := 0xa8a8a8a8a8a8a8a8a8a8a8a8a8a8a8a8
def d16 : List Nat := [0, 1, 2]
def d17 : List (Nat × Nat × Nat) := [(0,2,3),(1,1,3),(2,1,5)]
lemma d18 : baseOK d15 d16 d17 = true := by decide +kernel
lemma d19 : LowN d16 d15 2 := lowCount d18 (by decide +kernel)
def d20 : Nat := 0xeac8eac8eac8eac8eac8eac8eac8eac8
def d21 : List Nat := [0, 1, 2, 3]
def d22 : List (Nat × Nat × Nat) := [(0,2,3),(1,1,3),(2,2,6),(3,1,9)]
lemma d23 : baseOK d20 d21 d22 = true := by decide +kernel
lemma d24 : SliceN d21 d20 (c35,1,[0, 3]) := mkSlice (w:=0) d23 d3 d4 (by decide +kernel)
lemma d25 : SliceN d21 d20 (c81,1,[1, 3]) := mkSlice (w:=1) d23 d8 d9 (by decide +kernel)
lemma d26 : SliceN d21 d20 (c36,1,[1, 2]) := mkSlice (w:=0) d23 d3 d4 (by decide +kernel)
lemma d27 : SliceN d21 d20 (c8,2,[1, 0, 3]) := mkSlice (w:=4) d23 d13 d14 (by decide +kernel)
lemma d28 : SliceN d21 d20 (c23,2,[1, 0, 2]) := mkSlice (w:=0) d23 d18 d19 (by decide +kernel)
lemma d29 : SliceN d21 d20 (c9,2,[0, 1, 2]) := mkSlice (w:=8) d23 d13 d14 (by decide +kernel)
def d30 : List SliceD := [(c35,1,[0, 3]),(c81,1,[1, 3]),(c36,1,[1, 2]),(c8,2,[1, 0, 3]),(c23,2,[1, 0, 2]),(c9,2,[0, 1, 2])]
lemma d31 : ∀ s ∈ d30, SliceN d21 d20 s := by
  unfold d30
  simp only [List.forall_mem_cons]
  exact ⟨d24,d25,d26,d27,d28,d29,by simp⟩
def d32 : List StD := dupD [
 (l5,[(0,[]),(1,[]),(2,[]),(3,[]),(4,[]),(5,[])],[],[[0,1,2],[0,3],[4,1,5],[1,3],[0,5,2],[0,3]])]
def d33 : List StD := []
lemma d34 : LevelN d21 d20 2 d33 := by intro s h; cases h
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma d35 : levelOK d20 d30 2 (d33.map Prod.fst) ((d32.drop (0*8)).take 8) = true := by decide +kernel
lemma d36 : LevelN d21 d20 3 d32 := levelStep d23 d31 d34 (chunks 8 d32 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact d35
  ))
lemma d37 : LowN d21 d20 4 := lowSearch d23 d36 (by decide +kernel)
def d38 : Nat := 0xe8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8
def d39 : List Nat := [0, 1, 2]
def d40 : List (Nat × Nat × Nat) := [(0,2,3),(1,1,3),(2,1,5)]
lemma d41 : baseOK d38 d39 d40 = true := by decide +kernel
lemma d42 : SliceN d39 d38 (c24,1,[0, 2]) := mkSlice (w:=0) d41 d3 d4 (by decide +kernel)
lemma d43 : SliceN d39 d38 (c28,1,[1, 2]) := mkSlice (w:=0) d41 d3 d4 (by decide +kernel)
lemma d44 : SliceN d39 d38 (c12,1,[0, 2]) := mkSlice (w:=2) d41 d8 d9 (by decide +kernel)
lemma d45 : SliceN d39 d38 (c11,1,[1, 2]) := mkSlice (w:=1) d41 d8 d9 (by decide +kernel)
lemma d46 : SliceN d39 d38 (c25,1,[0, 1]) := mkSlice (w:=0) d41 d3 d4 (by decide +kernel)
lemma d47 : SliceN d39 d38 (c8,1,[0, 1]) := mkSlice (w:=4) d41 d8 d9 (by decide +kernel)
def d48 : List SliceD := [(c24,1,[0, 2]),(c28,1,[1, 2]),(c12,1,[0, 2]),(c11,1,[1, 2]),(c25,1,[0, 1]),(c8,1,[0, 1])]
lemma d49 : ∀ s ∈ d48, SliceN d39 d38 s := by
  unfold d48
  simp only [List.forall_mem_cons]
  exact ⟨d42,d43,d44,d45,d46,d47,by simp⟩
def d50 : List StD := dupD [
 ([c1,c0,c2],[(0,[]),(1,[]),(2,[]),(3,[]),(4,[]),(5,[])],[(4,5),(1,3),(0,3),(2,3),(2,6),(1,5)],[l4,[4,1,1003,5,3,1000],[4,0,1001,5,2,1004,1005]])]
def d51 : List StD := []
lemma d52 : LevelN d39 d38 2 d51 := by intro s h; cases h
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma d53 : levelOK d38 d48 2 (d51.map Prod.fst) ((d50.drop (0*8)).take 8) = true := by decide +kernel
lemma d54 : LevelN d39 d38 3 d50 := levelStep d41 d49 d52 (chunks 8 d50 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact d53
  ))
lemma d55 : LowN d39 d38 4 := lowSearch d41 d54 (by decide +kernel)
def d56 : Nat := 0xeae8eae8eae8eae8eae8eae8eae8eae8
def d57 : List Nat := [0, 1, 2, 3]
def d58 : List (Nat × Nat × Nat) := [(0,2,3),(1,1,3),(2,1,5),(3,1,9)]
lemma d59 : baseOK d56 d57 d58 = true := by decide +kernel
lemma d60 : SliceN d57 d56 (c23,4,[0, 1, 2]) := mkSlice (w:=0) d59 d41 d55 (by decide +kernel)
def d61 : List SliceD := [(c23,4,[0, 1, 2])]
lemma d62 : ∀ s ∈ d61, SliceN d57 d56 s := by
  unfold d61
  simp only [List.forall_mem_cons]
  exact ⟨d60,by simp⟩
def d63 : List StD := dupD [
 (l5,[(0,[])],[],[[0],[0],[0],[0],[0],[0]])]
def d64 : List StD := []
lemma d65 : LevelN d57 d56 3 d64 := by intro s h; cases h
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma d66 : levelOK d56 d61 3 (d64.map Prod.fst) ((d63.drop (0*8)).take 8) = true := by decide +kernel
lemma d67 : LevelN d57 d56 4 d63 := levelStep d59 d62 d65 (chunks 8 d63 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact d66
  ))
lemma d68 : LowN d57 d56 5 := lowSearch d59 d67 (by decide +kernel)
def d69 : Nat := 0xeee8eee8eee8eee8eee8eee8eee8eee8
def d70 : List Nat := [0, 1, 2, 3]
def d71 : List (Nat × Nat × Nat) := [(0,2,3),(1,1,3),(2,1,5),(3,1,9)]
lemma d72 : baseOK d69 d70 d71 = true := by decide +kernel
lemma d73 : SliceN d70 d69 (c25,4,[0, 1, 3]) := mkSlice (w:=0) d72 d41 d55 (by decide +kernel)
def d74 : List SliceD := [(c25,4,[0, 1, 3])]
lemma d75 : ∀ s ∈ d74, SliceN d70 d69 s := by
  unfold d74
  simp only [List.forall_mem_cons]
  exact ⟨d73,by simp⟩
def d76 : List StD := dupD [
 (l5,[(0,[])],[],[[0],[0],[0],[0],[0],[0]])]
def d77 : List StD := []
lemma d78 : LevelN d70 d69 3 d77 := by intro s h; cases h
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma d79 : levelOK d69 d74 3 (d77.map Prod.fst) ((d76.drop (0*8)).take 8) = true := by decide +kernel
lemma d80 : LevelN d70 d69 4 d76 := levelStep d72 d75 d78 (chunks 8 d76 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact d79
  ))
lemma d81 : LowN d70 d69 5 := lowSearch d72 d80 (by decide +kernel)
def d82 : Nat := 0xfeeafeeafeeafeeafeeafeeafeeafeea
def d83 : List Nat := [0, 1, 2, 3]
def d84 : List (Nat × Nat × Nat) := [(0,0,1),(1,4,6),(2,2,6),(3,2,10)]
lemma d85 : baseOK d82 d83 d84 = true := by decide +kernel
lemma d86 : SliceN d83 d82 (c28,4,[1, 2, 3]) := mkSlice (w:=0) d85 d41 d55 (by decide +kernel)
def d87 : List SliceD := [(c28,4,[1, 2, 3])]
lemma d88 : ∀ s ∈ d87, SliceN d83 d82 s := by
  unfold d87
  simp only [List.forall_mem_cons]
  exact ⟨d86,by simp⟩
def d89 : List StD := dupD [
 (l5,[(0,[])],[],[[0],[0],[0],[0],[0],[0]])]
def d90 : List StD := []
lemma d91 : LevelN d83 d82 3 d90 := by intro s h; cases h
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma d92 : levelOK d82 d87 3 (d90.map Prod.fst) ((d89.drop (0*8)).take 8) = true := by decide +kernel
lemma d93 : LevelN d83 d82 4 d89 := levelStep d85 d88 d91 (chunks 8 d89 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact d92
  ))
lemma d94 : LowN d83 d82 5 := lowSearch d85 d93 (by decide +kernel)
def d95 : Nat := 0xfefefefefefefefefefefefefefefefe
def d96 : List Nat := [0, 1, 2]
def d97 : List (Nat × Nat × Nat) := [(0,0,1),(1,0,2),(2,0,4)]
lemma d98 : baseOK d95 d96 d97 = true := by decide +kernel
lemma d99 : LowN d96 d95 2 := lowCount d98 (by decide +kernel)
def d100 : Nat := 0xfeeefeeefeeefeeefeeefeeefeeefeee
def d101 : List Nat := [0, 1, 2, 3]
def d102 : List (Nat × Nat × Nat) := [(0,0,1),(1,0,2),(2,8,12),(3,4,12)]
lemma d103 : baseOK d100 d101 d102 = true := by decide +kernel
lemma d104 : LowN d101 d100 3 := lowCount d103 (by decide +kernel)
def d105 : Nat := 0xfeeafce8feeafce8feeafce8feeafce8
def d106 : List Nat := l0
def d107 : List (Nat × Nat × Nat) := [(0,2,3),(1,1,3),(2,1,5),(3,2,10),(4,1,17)]
lemma d108 : baseOK d105 d106 d107 = true := by decide +kernel
lemma d109 : SliceN d106 d105 (c24,4,[0, 2, 3, 4]) := mkSlice (w:=0) d108 d23 d37 (by decide +kernel)
lemma d110 : SliceN d106 d105 (c32,4,[1, 2, 3]) := mkSlice (w:=0) d108 d41 d55 (by decide +kernel)
lemma d111 : SliceN d106 d105 (c25,4,[0, 1, 3, 4]) := mkSlice (w:=0) d108 d23 d37 (by decide +kernel)
lemma d112 : SliceN d106 d105 (c23,5,[0, 1, 2, 4]) := mkSlice (w:=0) d108 d59 d68 (by decide +kernel)
lemma d113 : SliceN d106 d105 (c31,5,[1, 2, 0, 3]) := mkSlice (w:=0) d108 d72 d81 (by decide +kernel)
lemma d114 : SliceN d106 d105 (c10,5,[0, 1, 2, 3]) := mkSlice (w:=16) d108 d85 d94 (by decide +kernel)
lemma d115 : SliceN d106 d105 (c40,2,[0, 2, 3]) := mkSlice (w:=2) d108 d98 d99 (by decide +kernel)
lemma d116 : SliceN d106 d105 (c53,2,[0, 1, 3]) := mkSlice (w:=4) d108 d98 d99 (by decide +kernel)
lemma d117 : SliceN d106 d105 (c41,1,[0, 4]) := mkSlice (w:=0) d108 d3 d4 (by decide +kernel)
lemma d118 : SliceN d106 d105 (0x3000300030003000300030003000300,1,[0, 4]) := mkSlice (w:=8) d108 d3 d4 (by decide +kernel)
lemma d119 : SliceN d106 d105 (c54,1,[0, 2]) := mkSlice (w:=2) d108 d8 d9 (by decide +kernel)
lemma d120 : SliceN d106 d105 (c9,3,[1, 2, 0, 4]) := mkSlice (w:=8) d108 d103 d104 (by decide +kernel)
lemma d121 : SliceN d106 d105 (c82,2,[1, 2, 4]) := mkSlice (w:=9) d108 d98 d99 (by decide +kernel)
lemma d122 : SliceN d106 d105 (c42,2,[0, 2, 3]) := mkSlice (w:=18) d108 d98 d99 (by decide +kernel)
lemma d123 : SliceN d106 d105 (c55,2,[0, 1, 3]) := mkSlice (w:=20) d108 d98 d99 (by decide +kernel)
def d124 : List SliceD := [(c24,4,[0, 2, 3, 4]),(c32,4,[1, 2, 3]),(c25,4,[0, 1, 3, 4]),(c23,5,[0, 1, 2, 4]),(c31,5,[1, 2, 0, 3]),(c10,5,[0, 1, 2, 3]),(c40,2,[0, 2, 3]),(c53,2,[0, 1, 3]),(c41,1,[0, 4]),(0x3000300030003000300030003000300,1,[0, 4]),(c54,1,[0, 2]),(c9,3,[1, 2, 0, 4]),(c82,2,[1, 2, 4]),(c42,2,[0, 2, 3]),(c55,2,[0, 1, 3])]
lemma d125 : ∀ s ∈ d124, SliceN d106 d105 s := by
  unfold d124
  simp only [List.forall_mem_cons]
  exact ⟨d109,d110,d111,d112,d113,d114,d115,d116,d117,d118,d119,d120,d121,d122,d123,by simp⟩
def d126 : List StD := dupD [
 (l3,[(0,[]),(1,[]),(2,[]),(3,[]),(4,[]),(5,[])],[(2,3),(0,3),(4,5),(17,24),(1,3),(4,6),(2,6),(2,10),(0,10),(4,12)],[[0,1,1000,1001],[1,1002,2,1000],[1,3,1003],[1,4,5],[0,2,1004,1005,1006],[0,3,1007,1008],[0,1,5],[2,3,1009,1007],[1,5],[1,3,5]])]
def d127 : List StD := dupD [
 (l7,[(0,[]),(6,[]),(2,[]),(7,[]),(1,[]),(8,[]),(9,[]),(5,[(1,1,2)]),(3,[])],[],[[0,1],[2,3],[4,1,5],[5,6],[1,7],[0,1],[2],[0,1],[0,7,3],[0],[2,3],[1,7],[8,1],[4,7],[1,6,5]])]
def d128 : List StD := dupD [
 ([c56,c1,c0,c2,c5],[(1,[]),(10,[]),(11,[]),(3,[(1,1,2)]),(5,[]),(0,[(2,1,2)]),(2,[(2,1,2)]),(7,[]),(12,[]),(13,[]),(14,[])],[],[[0,1,2],[2,3],[2,1],[0,4],[5,1],[6,7],[1,8,9],[5,1],[5,10,7],[1,9]])]
def d129 : List StD := []
lemma d130 : LevelN d106 d105 3 d129 := by intro s h; cases h
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma d131 : levelOK d105 d124 3 (d129.map Prod.fst) ((d128.drop (0*8)).take 8) = true := by decide +kernel
lemma d132 : LevelN d106 d105 4 d128 := levelStep d108 d125 d130 (chunks 8 d128 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact d131
  ))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma d133 : levelOK d105 d124 4 (d128.map Prod.fst) ((d127.drop (0*8)).take 8) = true := by decide +kernel
lemma d134 : LevelN d106 d105 5 d127 := levelStep d108 d125 d132 (chunks 8 d127 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact d133
  ))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma d135 : levelOK d105 d124 5 (d127.map Prod.fst) ((d126.drop (0*8)).take 8) = true := by decide +kernel
lemma d136 : LevelN d106 d105 6 d126 := levelStep d108 d125 d134 (chunks 8 d126 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact d135
  ))
lemma d137 : LowN d106 d105 7 := lowSearch d108 d136 (by decide +kernel)
def d138 : Nat := 0xfeeefac8feeefac8feeefac8feeefac8
def d139 : List Nat := l0
def d140 : List (Nat × Nat × Nat) := [(0,2,3),(1,1,3),(2,2,6),(3,1,9),(4,1,17)]
lemma d141 : baseOK d138 d139 d140 = true := by decide +kernel
lemma d142 : SliceN d139 d138 (c25,5,[0, 1, 4, 3]) := mkSlice (w:=0) d141 d59 d68 (by decide +kernel)
def d143 : List SliceD := [(c25,5,[0, 1, 4, 3])]
lemma d144 : ∀ s ∈ d143, SliceN d139 d138 s := by
  unfold d143
  simp only [List.forall_mem_cons]
  exact ⟨d142,by simp⟩
def d145 : List StD := dupD [
 (l3,[(0,[])],[],[[0],[0],[0],[0],[0],[0],[0],[0],[0],[0]])]
def d146 : List StD := []
lemma d147 : LevelN d139 d138 4 d146 := by intro s h; cases h
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma d148 : levelOK d138 d143 4 (d146.map Prod.fst) ((d145.drop (0*8)).take 8) = true := by decide +kernel
lemma d149 : LevelN d139 d138 5 d145 := levelStep d141 d144 d147 (chunks 8 d145 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact d148
  ))
lemma d150 : LowN d139 d138 6 := lowSearch d141 d149 (by decide +kernel)
def d151 : Nat := 0xfeeefae8feeefae8feeefae8feeefae8
def d152 : List Nat := l0
def d153 : List (Nat × Nat × Nat) := [(0,2,3),(1,1,3),(2,1,5),(3,1,9),(4,1,17)]
lemma d154 : baseOK d151 d152 d153 = true := by decide +kernel
lemma d155 : SliceN d152 d151 (c24,5,[0, 2, 3, 4]) := mkSlice (w:=0) d154 d59 d68 (by decide +kernel)
lemma d156 : SliceN d152 d151 (c28,4,[1, 2, 3, 4]) := mkSlice (w:=0) d154 d23 d37 (by decide +kernel)
lemma d157 : SliceN d152 d151 (c25,5,[0, 1, 4, 3]) := mkSlice (w:=0) d154 d59 d68 (by decide +kernel)
lemma d158 : SliceN d152 d151 (c23,5,[0, 1, 2, 4]) := mkSlice (w:=0) d154 d72 d81 (by decide +kernel)
lemma d159 : SliceN d152 d151 (c31,5,[0, 2, 1, 3]) := mkSlice (w:=0) d154 d72 d81 (by decide +kernel)
def d160 : List SliceD := [(c24,5,[0, 2, 3, 4]),(c28,4,[1, 2, 3, 4]),(c25,5,[0, 1, 4, 3]),(c23,5,[0, 1, 2, 4]),(c31,5,[0, 2, 1, 3])]
lemma d161 : ∀ s ∈ d160, SliceN d152 d151 s := by
  unfold d160
  simp only [List.forall_mem_cons]
  exact ⟨d155,d156,d157,d158,d159,by simp⟩
def d162 : List StD := dupD [
 (l3,[(0,[]),(1,[]),(2,[]),(3,[]),(4,[])],[(1,3),(0,3),(1,5),(0,5),(1,9),(0,9),(1,17),(0,17),(2,6),(18,24),(2,18),(6,10),(12,24),(10,18)],[[0,1000,1,1001],[1,2,1002,1003],[1,3,1004,1005],[1,4,1006,1007],[0,2,1008],[0,3,1009],[0,4,1010],[2,3,1011],[2,4,1012],[3,4,1013]])]
def d163 : List StD := []
lemma d164 : LevelN d152 d151 5 d163 := by intro s h; cases h
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma d165 : levelOK d151 d160 5 (d163.map Prod.fst) ((d162.drop (0*8)).take 8) = true := by decide +kernel
lemma d166 : LevelN d152 d151 6 d162 := levelStep d154 d161 d164 (chunks 8 d162 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact d165
  ))
lemma d167 : LowN d152 d151 7 := lowSearch d154 d166 (by decide +kernel)
def d216 : Nat := 0xeac0eac0eac0eac0eac0eac0eac0eac0
def d217 : List Nat := [0, 1, 2, 3]
def d218 : List (Nat × Nat × Nat) := [(0,8,9),(1,4,6),(2,2,6),(3,1,9)]
lemma d219 : baseOK d216 d217 d218 = true := by decide +kernel
lemma d220 : LowN d217 d216 3 := lowCount d219 (by decide +kernel)
def d221 : Nat := 0xfeeafcc8feeafcc8feeafcc8feeafcc8
def d222 : List Nat := l0
def d223 : List (Nat × Nat × Nat) := [(0,2,3),(1,1,3),(2,2,6),(3,2,10),(4,1,17)]
lemma d224 : baseOK d221 d222 d223 = true := by decide +kernel
lemma d225 : SliceN d222 d221 (c32,4,[1, 2, 3]) := mkSlice (w:=0) d224 d41 d55 (by decide +kernel)
lemma d226 : SliceN d222 d221 (c25,4,[0, 1, 3, 4]) := mkSlice (w:=0) d224 d23 d37 (by decide +kernel)
lemma d227 : SliceN d222 d221 (c23,4,[0, 1, 2, 4]) := mkSlice (w:=0) d224 d23 d37 (by decide +kernel)
lemma d228 : SliceN d222 d221 (c31,5,[1, 2, 3, 0]) := mkSlice (w:=0) d224 d59 d68 (by decide +kernel)
lemma d229 : SliceN d222 d221 (c10,5,[0, 1, 2, 3]) := mkSlice (w:=16) d224 d85 d94 (by decide +kernel)
lemma d230 : SliceN d222 d221 (c40,2,[0, 2, 3]) := mkSlice (w:=2) d224 d98 d99 (by decide +kernel)
lemma d231 : SliceN d222 d221 (c47,2,[3, 0, 4]) := mkSlice (w:=4) d224 d13 d14 (by decide +kernel)
lemma d232 : SliceN d222 d221 (c41,1,[0, 4]) := mkSlice (w:=0) d224 d3 d4 (by decide +kernel)
lemma d233 : SliceN d222 d221 (c48,2,[1, 3, 4]) := mkSlice (w:=5) d224 d98 d99 (by decide +kernel)
lemma d234 : SliceN d222 d221 (0xc0c00000c0c00000c0c00000c0c,1,[0, 3]) := mkSlice (w:=2) d224 d8 d9 (by decide +kernel)
lemma d235 : SliceN d222 d221 (c24,3,[0, 2, 3, 4]) := mkSlice (w:=0) d224 d219 d220 (by decide +kernel)
lemma d236 : SliceN d222 d221 (c82,2,[1, 2, 4]) := mkSlice (w:=9) d224 d98 d99 (by decide +kernel)
lemma d237 : SliceN d222 d221 (c9,3,[1, 2, 0, 4]) := mkSlice (w:=8) d224 d103 d104 (by decide +kernel)
lemma d238 : SliceN d222 d221 (c83,2,[2, 0, 4]) := mkSlice (w:=8) d224 d13 d14 (by decide +kernel)
lemma d239 : SliceN d222 d221 (c54,1,[0, 2]) := mkSlice (w:=2) d224 d8 d9 (by decide +kernel)
lemma d240 : SliceN d222 d221 (c58,2,[0, 1, 4]) := mkSlice (w:=0) d224 d18 d19 (by decide +kernel)
lemma d241 : SliceN d222 d221 (c42,2,[0, 2, 3]) := mkSlice (w:=18) d224 d98 d99 (by decide +kernel)
lemma d242 : SliceN d222 d221 (c55,2,[0, 1, 3]) := mkSlice (w:=20) d224 d98 d99 (by decide +kernel)
lemma d243 : SliceN d222 d221 (0x5050000050500000505000005050,1,[1, 3]) := mkSlice (w:=4) d224 d8 d9 (by decide +kernel)
lemma d244 : SliceN d222 d221 (c11,3,[1, 4, 3, 2]) := mkSlice (w:=1) d224 d103 d104 (by decide +kernel)
def d245 : List SliceD := [(c32,4,[1, 2, 3]),(c25,4,[0, 1, 3, 4]),(c23,4,[0, 1, 2, 4]),(c31,5,[1, 2, 3, 0]),(c10,5,[0, 1, 2, 3]),(c40,2,[0, 2, 3]),(c47,2,[3, 0, 4]),(c41,1,[0, 4]),(c48,2,[1, 3, 4]),(0xc0c00000c0c00000c0c00000c0c,1,[0, 3]),(c24,3,[0, 2, 3, 4]),(c82,2,[1, 2, 4]),(c9,3,[1, 2, 0, 4]),(c83,2,[2, 0, 4]),(c54,1,[0, 2]),(c58,2,[0, 1, 4]),(c42,2,[0, 2, 3]),(c55,2,[0, 1, 3]),(0x5050000050500000505000005050,1,[1, 3]),(c11,3,[1, 4, 3, 2])]
lemma d246 : ∀ s ∈ d245, SliceN d222 d221 s := by
  unfold d245
  simp only [List.forall_mem_cons]
  exact ⟨d225,d226,d227,d228,d229,d230,d231,d232,d233,d234,d235,d236,d237,d238,d239,d240,d241,d242,d243,d244,by simp⟩
def d247 : List StD := dupD [
 (l3,[(0,[]),(1,[]),(2,[]),(3,[]),(4,[])],[(2,3),(16,17),(20,21),(24,25),(8,12),(4,6),(2,6),(4,12),(8,10),(2,10)],[[0,1000,1001],[0,1002,1,1000],[0,1003,2,1000],[0,3,4],[1,1004,1005,1006],[2,1007,1008,1009],[0,4],[1,2,1006,1004,1007],[0,4],[0,4]])]
def d248 : List StD := dupD [
 (l7,[(0,[(1,0,1)]),(5,[]),(6,[]),(1,[]),(7,[]),(8,[]),(4,[(1,1,2)]),(3,[(2,0,1)]),(2,[])],[],[[0,1,2],[0,2,3],[0,1,4],[0,5],[1,5,6],[3,5],[3],[2,1],[0,6],[7],[3,2],[0,2,3],[8,1],[0,2,4],[0,6]]),
 ([0xc0c0c0c0c0c0c0c,c1,c0,c2,c3,c5],[(0,[]),(9,[]),(10,[]),(3,[(0,0,1)]),(3,[(1,0,1)]),(4,[]),(6,[]),(0,[(2,0,1)]),(8,[]),(4,[(2,1,2)]),(1,[])],[],[[0,1,2],[3],[4],[2,1],[0,5],[2,1],[1,6],[7,8],[1,8,9],[2,8,10],[2,1],[2,9,7],[1,6],[7,6,9],[1,9]]),
 ([c1,c0,c2,c3,c18,c5],[(0,[(1,0,2)]),(5,[]),(7,[]),(11,[]),(12,[]),(4,[(1,1,3)]),(13,[]),(2,[]),(1,[]),(3,[(2,0,2)])],[],[[0,1,2],[0,3],[0,4,2],[0,1,2],[1,3,5],[6,1],[7,3],[7],[0,5],[7,3],[8,1],[0,5],[9],[0,3,2],[0,3,2]]),
 ([0xcc00cc00cc00cc,c1,c0,c2,c3,c5],[(0,[]),(14,[]),(6,[]),(3,[(0,0,2)]),(1,[]),(10,[]),(3,[(1,0,2)]),(4,[]),(0,[(2,0,2)]),(7,[]),(12,[]),(4,[(2,1,3)]),(2,[])],[],[[0,1,2],[3],[4,1,5],[6],[0,7],[2,1],[8,2,9],[1,10],[1,11],[5,1],[2,10,12],[2,11,8],[1,2,10],[1,2,9],[8,10,9]]),
 ([c1,c0,c2,c3,c16,c5],[(0,[(1,1,2)]),(8,[]),(6,[]),(1,[]),(7,[]),(3,[(1,1,2)]),(4,[(1,2,3)]),(12,[]),(2,[]),(15,[])],[],[[0,1],[0,2,3],[0,1],[0,2,4],[5,1,6],[3,1],[2,7,8],[9,1],[0,6],[3,1],[8],[0,1,3],[3],[0,6],[0,1,4]])]
def d249 : List StD := dupD [
 ([c56,c1,c0,c2,c5],[(0,[]),(8,[]),(3,[(2,0,2)]),(1,[]),(3,[(0,0,2)]),(4,[]),(7,[]),(5,[]),(6,[]),(16,[]),(1,[(2,1,2)]),(17,[]),(18,[])],[],[[0,1],[2,3,4],[3,1],[0,5],[6,1,7],[6,8],[7,1,9],[10,1],[6,11,12],[6,1]]),
 ([c70,c1,c0,c3,c5],[(7,[]),(19,[]),(0,[]),(3,[(2,0,1)]),(5,[]),(3,[(0,0,1)]),(3,[(3,1,2)]),(12,[]),(3,[(0,1,2)]),(4,[]),(8,[]),(17,[]),(6,[]),(18,[])],[],[[0,1,2],[3,4,5],[6,7,8],[0,9,2],[0,4],[0,7],[4,10,11],[12,4],[0,11,13],[0,7]])]
def d250 : List StD := []
lemma d251 : LevelN d222 d221 3 d250 := by intro s h; cases h
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma d252 : levelOK d221 d245 3 (d250.map Prod.fst) ((d249.drop (0*8)).take 8) = true := by decide +kernel
lemma d253 : LevelN d222 d221 4 d249 := levelStep d224 d246 d251 (chunks 8 d249 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact d252
  ))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma d254 : levelOK d221 d245 4 (d249.map Prod.fst) ((d248.drop (0*8)).take 8) = true := by decide +kernel
lemma d255 : LevelN d222 d221 5 d248 := levelStep d224 d246 d253 (chunks 8 d248 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact d254
  ))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma d256 : levelOK d221 d245 5 (d248.map Prod.fst) ((d247.drop (0*8)).take 8) = true := by decide +kernel
lemma d257 : LevelN d222 d221 6 d247 := levelStep d224 d246 d255 (chunks 8 d247 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact d256
  ))
lemma d258 : LowN d222 d221 7 := lowSearch d224 d257 (by decide +kernel)
def d384 : Nat := 0xfeeefac0feeefac0feeefac0feeefac0
def d385 : List Nat := l0
def d386 : List (Nat × Nat × Nat) := [(0,8,9),(1,4,6),(2,2,6),(3,1,9),(4,1,17)]
lemma d387 : baseOK d384 d385 d386 = true := by decide +kernel
lemma d388 : SliceN d385 d384 (c28,4,[1, 2, 3, 4]) := mkSlice (w:=0) d387 d23 d37 (by decide +kernel)
lemma d389 : SliceN d385 d384 (c24,4,[0, 3, 2, 4]) := mkSlice (w:=0) d387 d23 d37 (by decide +kernel)
lemma d390 : SliceN d385 d384 (c25,4,[0, 4, 1, 3]) := mkSlice (w:=0) d387 d23 d37 (by decide +kernel)
lemma d391 : SliceN d385 d384 (c23,4,[1, 4, 0, 2]) := mkSlice (w:=0) d387 d23 d37 (by decide +kernel)
lemma d392 : SliceN d385 d384 (c31,4,[2, 3, 0, 1]) := mkSlice (w:=0) d387 d23 d37 (by decide +kernel)
lemma d393 : SliceN d385 d384 (c11,3,[3, 4, 1, 2]) := mkSlice (w:=1) d387 d103 d104 (by decide +kernel)
lemma d394 : SliceN d385 d384 (c12,3,[2, 4, 3, 0]) := mkSlice (w:=2) d387 d103 d104 (by decide +kernel)
lemma d395 : SliceN d385 d384 (c110,1,[2, 3]) := mkSlice (w:=0) d387 d3 d4 (by decide +kernel)
lemma d396 : SliceN d385 d384 (c111,2,[4, 3, 0]) := mkSlice (w:=2) d387 d13 d14 (by decide +kernel)
lemma d397 : SliceN d385 d384 (c48,2,[1, 3, 4]) := mkSlice (w:=5) d387 d98 d99 (by decide +kernel)
lemma d398 : SliceN d385 d384 (c61,2,[0, 2, 4]) := mkSlice (w:=10) d387 d98 d99 (by decide +kernel)
lemma d399 : SliceN d385 d384 (c65,2,[4, 2, 1]) := mkSlice (w:=1) d387 d13 d14 (by decide +kernel)
lemma d400 : SliceN d385 d384 (c8,3,[1, 3, 0, 4]) := mkSlice (w:=4) d387 d103 d104 (by decide +kernel)
lemma d401 : SliceN d385 d384 (c112,1,[1, 4]) := mkSlice (w:=0) d387 d3 d4 (by decide +kernel)
lemma d402 : SliceN d385 d384 (c69,2,[2, 3, 4]) := mkSlice (w:=3) d387 d98 d99 (by decide +kernel)
lemma d403 : SliceN d385 d384 (c47,2,[3, 0, 4]) := mkSlice (w:=4) d387 d13 d14 (by decide +kernel)
lemma d404 : SliceN d385 d384 (c55,2,[0, 1, 3]) := mkSlice (w:=20) d387 d98 d99 (by decide +kernel)
lemma d405 : SliceN d385 d384 (c113,2,[3, 2, 1]) := mkSlice (w:=1) d387 d13 d14 (by decide +kernel)
lemma d406 : SliceN d385 d384 (c9,3,[0, 2, 1, 4]) := mkSlice (w:=8) d387 d103 d104 (by decide +kernel)
lemma d407 : SliceN d385 d384 (0xff000000ff000000ff000000ff000000,2,[0, 1, 2]) := mkSlice (w:=24) d387 d98 d99 (by decide +kernel)
lemma d408 : SliceN d385 d384 (c36,2,[1, 2, 4]) := mkSlice (w:=0) d387 d18 d19 (by decide +kernel)
lemma d409 : SliceN d385 d384 (c32,2,[2, 1, 3]) := mkSlice (w:=0) d387 d18 d19 (by decide +kernel)
lemma d410 : SliceN d385 d384 (c10,3,[0, 1, 2, 3]) := mkSlice (w:=16) d387 d103 d104 (by decide +kernel)
lemma d411 : SliceN d385 d384 (c35,2,[0, 3, 4]) := mkSlice (w:=0) d387 d18 d19 (by decide +kernel)
lemma d412 : SliceN d385 d384 (c74,2,[1, 0, 4]) := mkSlice (w:=4) d387 d13 d14 (by decide +kernel)
lemma d413 : SliceN d385 d384 (c40,2,[2, 0, 3]) := mkSlice (w:=2) d387 d13 d14 (by decide +kernel)
lemma d414 : SliceN d385 d384 (0x55005500550055005500550055005500,2,[2, 1, 4]) := mkSlice (w:=8) d387 d13 d14 (by decide +kernel)
lemma d415 : SliceN d385 d384 (c41,1,[0, 4]) := mkSlice (w:=0) d387 d3 d4 (by decide +kernel)
lemma d416 : SliceN d385 d384 (c44,2,[3, 2, 0]) := mkSlice (w:=0) d387 d18 d19 (by decide +kernel)
lemma d417 : SliceN d385 d384 (0x55550000555500005555000055550000,2,[1, 2, 3]) := mkSlice (w:=16) d387 d13 d14 (by decide +kernel)
lemma d418 : SliceN d385 d384 (0x303000003030000030300000303,1,[0, 3]) := mkSlice (w:=0) d387 d3 d4 (by decide +kernel)
lemma d419 : SliceN d385 d384 (0x33330000333300003333000033330000,2,[0, 2, 3]) := mkSlice (w:=16) d387 d13 d14 (by decide +kernel)
lemma d420 : SliceN d385 d384 (0xf000f000f000f000f000f000f000f00,2,[0, 1, 4]) := mkSlice (w:=8) d387 d13 d14 (by decide +kernel)
lemma d421 : SliceN d385 d384 (c114,1,[1, 2]) := mkSlice (w:=0) d387 d3 d4 (by decide +kernel)
def d422 : List SliceD := [(c28,4,[1, 2, 3, 4]),(c24,4,[0, 3, 2, 4]),(c25,4,[0, 4, 1, 3]),(c23,4,[1, 4, 0, 2]),(c31,4,[2, 3, 0, 1]),(c11,3,[3, 4, 1, 2]),(c12,3,[2, 4, 3, 0]),(c110,1,[2, 3]),(c111,2,[4, 3, 0]),(c48,2,[1, 3, 4]),(c61,2,[0, 2, 4]),(c65,2,[4, 2, 1]),(c8,3,[1, 3, 0, 4]),(c112,1,[1, 4]),(c69,2,[2, 3, 4]),(c47,2,[3, 0, 4]),(c55,2,[0, 1, 3]),(c113,2,[3, 2, 1]),(c9,3,[0, 2, 1, 4]),(0xff000000ff000000ff000000ff000000,2,[0, 1, 2]),(c36,2,[1, 2, 4]),(c32,2,[2, 1, 3]),(c10,3,[0, 1, 2, 3]),(c35,2,[0, 3, 4]),(c74,2,[1, 0, 4]),(c40,2,[2, 0, 3]),(0x55005500550055005500550055005500,2,[2, 1, 4]),(c41,1,[0, 4]),(c44,2,[3, 2, 0]),(0x55550000555500005555000055550000,2,[1, 2, 3]),(0x303000003030000030300000303,1,[0, 3]),(0x33330000333300003333000033330000,2,[0, 2, 3]),(0xf000f000f000f000f000f000f000f00,2,[0, 1, 4]),(c114,1,[1, 2])]
lemma d423 : ∀ s ∈ d422, SliceN d385 d384 s := by
  unfold d422
  simp only [List.forall_mem_cons]
  exact ⟨d388,d389,d390,d391,d392,d393,d394,d395,d396,d397,d398,d399,d400,d401,d402,d403,d404,d405,d406,d407,d408,d409,d410,d411,d412,d413,d414,d415,d416,d417,d418,d419,d420,d421,by simp⟩
def d424 : List StD := dupD [
 (l3,[(0,[]),(1,[]),(2,[]),(3,[]),(4,[])],[(4,6),(10,11),(5,7),(20,21),(3,7),(1,9),(1,17),(8,12),(24,26),(3,11),(2,18),(4,12),(24,28),(5,21),(20,28),(10,26)],[l2,[0,2,1001,1003,1004],[0,3,1003,1001,1005],[0,4,1001,1003,1006],[1,2,1007,1000,1004],[1,3,1000,1008,1009],[1,4,1000,1008,1010],[2,3,1004,1007,1011],[2,4,1004,1012,1013],[3,4,1005,1014,1015]])]
def d425 : List StD := dupD [
 ([c1,c0,c21,c2,c3,c5],[(0,[]),(1,[]),(5,[]),(6,[]),(2,[]),(7,[]),(4,[]),(8,[]),(9,[]),(10,[]),(11,[])],[],[[0,1],[1],[0,2],[0,2],[0,2],[0],[1,3],[1,3],[1,3],[4,2,5],[5,2],[6,2],[7,8],[5,8,7],[5,9,10]]),
 ([c1,c0,c2,c6,c3,c5],[(0,[]),(5,[]),(2,[]),(12,[]),(1,[]),(13,[]),(14,[]),(15,[]),(3,[]),(16,[]),(17,[])],[],[[0,1],[0,1],[2],[0,1],[0,1],[2,3],[4,1,5],[5,6,7],[7,6],[0],[2,3],[2,3],[8,1],[5,1],[5,9,10]]),
 ([c1,c0,c2,c3,c14,c5],[(0,[]),(5,[]),(3,[]),(13,[]),(14,[]),(9,[]),(18,[]),(17,[]),(19,[]),(2,[]),(20,[])],[],[[0,1],[0,1],[0,1],[2],[0,1],[3,4,5],[2,4,6],[3,1],[7,4,8],[2,5,6],[9,1,10],[3,5],[0],[2,6],[3,1]]),
 ([c1,c0,c2,c3,c5,c17],[(0,[]),(5,[]),(4,[]),(7,[]),(9,[]),(14,[]),(19,[]),(1,[]),(21,[]),(11,[]),(22,[])],[],[[0,1],[0,1],[0,1],[0,1],[2],[3,4,5],[3,5],[2,5,6],[7,1,8],[9,4,6],[2,4,6],[3,1],[2,10],[3,1],[0]]),
 (l7,[(1,[]),(9,[]),(6,[]),(2,[]),(14,[]),(12,[]),(0,[]),(23,[]),(24,[]),(10,[]),(25,[]),(16,[])],[],[[0,1,2],[3,4,5],[6,2,7],[8,1,9],[10,1,11],[0,2],[3],[0,2],[0,2],[0],[3,1],[3,1],[7,1],[7,1],[8,9]]),
 ([c1,c0,c2,c3,c18,c5],[(1,[]),(6,[]),(8,[]),(14,[]),(26,[]),(3,[]),(19,[]),(0,[]),(27,[]),(2,[]),(25,[])],[],[[0,1],[2,3,4],[5,3,6],[7,1,8],[4,3],[0,1],[0,1],[5],[0,1],[2,4,5],[9,1],[2,6,10],[0],[5,4],[8,1]]),
 ([c1,c0,c2,c3,c5,c72],[(1,[]),(6,[]),(8,[]),(14,[]),(16,[]),(7,[]),(25,[]),(0,[]),(28,[]),(4,[]),(19,[])],[],[[0,1],[2,3,4],[5,3],[6,3,4],[7,1,8],[0,1],[0,1],[0,1],[9],[2,4],[2,10,5],[5,1],[5,4],[5,1],[0]]),
 ([c1,c0,c2,c3,c16,c5],[(26,[]),(9,[]),(16,[]),(2,[]),(3,[]),(19,[]),(0,[]),(27,[]),(1,[]),(13,[]),(10,[])],[],[[0,1],[0,2,3],[4,1,5],[6,2,7],[0,1],[3,1],[4,0],[8,0,9],[7,2,10],[3,1],[4],[3,1],[3],[4,0],[7,0]]),
 ([c1,c0,c2,c3,c5,c20],[(15,[]),(9,[]),(29,[]),(2,[]),(4,[]),(19,[]),(0,[]),(30,[]),(24,[]),(1,[])],[],[[0,1,2],[2,0,3],[2,1],[4,1,5],[6,0,7],[3,1],[0,5,8],[0,2,4],[9,1],[3,0],[3,0],[4],[4,2],[7,0],[3]]),
 ([c1,c0,c2,c3,c5,c7],[(26,[]),(10,[]),(31,[]),(16,[]),(32,[]),(3,[]),(4,[]),(0,[]),(1,[]),(33,[])],[],[[0,1,2],[0,3,4],[5,1],[0,2,6],[7,1],[2,1],[2,0,5],[6,1,3],[8,0,9],[5,0],[4,2,6],[9,0],[5,0],[6],[5]])]
def d426 : List StD := dupD [
 ([0xeeee0000eeee,c1,c0,c2,c3],[(0,[]),(1,[]),(19,[]),(9,[]),(2,[]),(3,[]),(10,[]),(0,[(2,0,3)]),(16,[]),(14,[]),(1,[(2,0,3)]),(8,[])],[],[[0,1],[1,0],[2,3,4],[5,6],[7,3],[7,8,9],[7,2,3],[10,3,6],[10,2,9],[11,2,3]]),
 ([c27,c1,c0,c2,c5],[(0,[]),(2,[]),(19,[]),(14,[]),(1,[]),(10,[]),(16,[]),(4,[]),(0,[(2,1,2)]),(9,[]),(2,[(2,0,3)]),(15,[])],[],[[0,1],[2,3,4],[1,0],[5,6,7],[8,5,9],[8,3],[8,2,3],[10,3,6],[11,2,3],[10,2,9]]),
 ([c70,c1,c0,c3,c5],[(0,[]),(14,[]),(0,[(2,0,1)]),(0,[(0,0,1)]),(0,[(3,1,2)]),(19,[]),(0,[(0,1,2)]),(9,[]),(4,[]),(1,[(2,1,2)]),(10,[]),(3,[(2,0,3)]),(26,[])],[],[[0,1],[2,1,3],[4,5,6],[7,5,8],[9,7,10],[11,1,5],[12,1],[9,1],[9,1],[11,10]]),
 ([0x3333303033333030,c1,c2,c3,c5],[(0,[]),(9,[]),(0,[(3,0,1)]),(0,[(0,0,1)]),(3,[]),(19,[]),(0,[(3,0,3)]),(0,[(0,0,3)]),(2,[(2,1,2)]),(16,[]),(24,[]),(4,[(2,0,3)])],[],[[0,1],[2,1,3],[4,5],[6,5,7],[8,9],[10,1,5],[11,1,5],[8,1],[8,1],[10,9,11]]),
 ([c75,c0,c2,c3,c5],[(1,[]),(10,[]),(2,[]),(16,[]),(0,[]),(32,[]),(3,[(2,1,2)]),(4,[(2,1,2)]),(19,[])],[],[[0,1],[2,3],[4,1],[4,3],[5,1,3],[6,5],[7,1,3],[6,1],[5,8,7],[6,1]])]
def d427 : List StD := []
lemma d428 : LevelN d385 d384 3 d427 := by intro s h; cases h
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma d429 : levelOK d384 d422 3 (d427.map Prod.fst) ((d426.drop (0*8)).take 8) = true := by decide +kernel
lemma d430 : LevelN d385 d384 4 d426 := levelStep d387 d423 d428 (chunks 8 d426 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact d429
  ))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma d431 : levelOK d384 d422 4 (d426.map Prod.fst) ((d425.drop (0*8)).take 8) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma d432 : levelOK d384 d422 4 (d426.map Prod.fst) ((d425.drop (1*8)).take 8) = true := by decide +kernel
lemma d433 : LevelN d385 d384 5 d425 := levelStep d387 d423 d430 (chunks 8 d425 2 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact d431
  · exact d432
  ))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma d434 : levelOK d384 d422 5 (d425.map Prod.fst) ((d424.drop (0*8)).take 8) = true := by decide +kernel
lemma d435 : LevelN d385 d384 6 d424 := levelStep d387 d423 d433 (chunks 8 d424 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact d434
  ))
lemma d436 : LowN d385 d384 7 := lowSearch d387 d435 (by decide +kernel)
def postedEdgeFun (x : Fin 7 → Bool) : Bool :=
  decide (∃ i < ([0, 2, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 2, 6, 3, 6, 5, 6] : List ℕ).length / 2,
    (List.ofFn x).getD (([0, 2, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 2, 6, 3, 6, 5, 6] : List ℕ).getD (2 * i) 0) false = true ∧
    (List.ofFn x).getD (([0, 2, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 2, 6, 3, 6, 5, 6] : List ℕ).getD (2 * i + 1) 0) false = true)

def originalGWord : Nat := 0xfffffffffffefffafffeffeefefeeca0
def originalGRoots : List Nat := [0, 1, 2, 3, 4, 5, 6]
def originalGEssential : List (Nat × Nat × Nat) := [(0,4,5),(1,8,10),(2,1,5),(3,2,10),(4,1,17),(5,1,33),(6,1,65)]

lemma originalG_baseOK : baseOK originalGWord originalGRoots originalGEssential = true := by
  decide

lemma originalG_posted_table : ∀ r : Fin 128,
    postedEdgeFun (fun i => r.val.testBit i.val) = originalGWord.testBit r.val := by
  decide


end RestrictionSixProof

namespace RestrictionSixProof

def programCut (s : SliceD) (cs : List (Nat × Nat × Nat)) : CutV :=
  (s.1, s.2.1, cs.length, mkPool (initPool s.1 s.2.2) cs)

lemma programCut_sound {R T s} (hs : SliceN R T s)
    (cs : List (Nat × Nat × Nat)) : CutP R T (programCut s cs) := by
  obtain ⟨⟨f, roots, dom, base, nc, lo⟩, hv⟩ := hs
  have ps : PS f (roots.map observe) (initPool s.1 s.2.2) := by
    intro v hv'
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hv'
    rw [rf_land dom]
    exact base _ (List.mem_map_of_mem (hv j hj))
  obtain ⟨bank, hb, hp⟩ :=
    mkPool_ok cs (Reach.start (u := true) (roots := roots.map observe)) ps
  refine ⟨f, roots, bank, dom, nc, ?_, hp, lo⟩
  simpa [programCut] using hb

lemma guessCut_sound {R T s k rest a b o ka kb}
    (hs : SliceN R T s) (cs : List (Nat × Nat × Nat))
    (nd : (kidW rest a b (nb o a b) ka kb).Nodup)
    (h : cutEval k rest a b (nb o a b) ka kb (programCut s cs) = true) :
    Impossible true (W T) k (kidW rest a b (nb o a b) ka kb).toFinset :=
  cut_sound (programCut_sound hs cs) nd h

def guessCuts (Z : List SliceD) (guess : SliceD → List (Nat × Nat × Nat))
    (k : Nat) (rest : List Nat) (a b z : Nat) (ka kb : Bool) : Bool :=
  Z.any fun s => cutEval k rest a b z ka kb (programCut s (guess s))

lemma guessCuts_sound {R T Z k rest a b o ka kb}
    (hZ : ∀ s ∈ Z, SliceN R T s)
    (guess : SliceD → List (Nat × Nat × Nat))
    (nd : (kidW rest a b (nb o a b) ka kb).Nodup)
    (h : guessCuts Z guess k rest a b (nb o a b) ka kb = true) :
    Impossible true (W T) k (kidW rest a b (nb o a b) ka kb).toFinset := by
  obtain ⟨s, hs, hc⟩ := List.any_eq_true.mp h
  exact guessCut_sound (hZ s hs) (guess s) nd hc

end RestrictionSixProof


end PEqualNP.Outside.L_meta_10760

namespace PEqualNP.Outside.L_meta_10760.AutoPool

def full : Nat := 0xffffffffffffffffffffffffffffffff

def inputs : List Nat := [0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa, 0xcccccccccccccccccccccccccccccccc, 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00ff00ff00ff00ff00, 0xffff0000ffff0000ffff0000ffff0000, 0xffffffff00000000ffffffff00000000, 0xffffffffffffffff0000000000000000]

def var (v : Nat) : Nat := inputs.getD v 0

def low (v : Nat) : Nat := full ^^^ var v

def flip (w v : Nat) : Nat :=
  ((w &&& low v) <<< (1 <<< v)) ||| ((w >>> (1 <<< v)) &&& low v)

def table : Nat := 0xa0601a00aa05000a07a0800000660921900000000000090600060b000000000000000c0860c00000050a00080c00001900000021b000000000000c0721c00000011a00000041c00900000000000000000000000000080b41b005000000000905000000000000000000000c0500000000000000000000000000000000000000031a00000b00080900000000000700031900000000000000000070a01b000000419000000000008709000000000000000000000c06b0601c00cb0500080a41a000

def op (o a b : Nat) : Nat :=
  if o == 0 then a &&& b else if o == 1 then a ||| b
  else if o == 2 then a ^^^ (a &&& b) else b ^^^ (a &&& b)

def poolRun : List Nat → List (Nat × Nat × Nat) → List Nat
  | pool, [] => pool
  | pool, (o,a,b) :: cs => poolRun
      (pool ++ [op o (pool.getD a 0) (pool.getD b 0)]) cs

def available (d : Nat) (pool : List Nat) (raw : Nat) : Bool :=
  let w := raw &&& d
  w == 0 || w == d || pool.any (fun a => w == a || w == (a ^^^ d))

def truth (anchor : Nat) (support : List Nat) (w : Nat) : Nat :=
  (List.range 8).foldl (fun bits r =>
    let pos := (support.zipIdx).foldl (fun pos (v,i) =>
      if r.testBit i then pos ||| (1 <<< v) else pos) anchor
    if w.testBit pos then bits ||| (1 <<< r) else bits) 0

def guessOne (d : Nat) (vs pool : List Nat) (raw : Nat) : List (Nat × Nat × Nat) :=
  if available d pool raw then [] else
  let anchor := Nat.log2 (d ^^^ (d - 1))
  let masked := raw &&& d
  let w := if masked.testBit anchor then masked ^^^ d else masked
  let support := vs.filter (fun v => (w ^^^ flip w v) &&& d != 0)
  if support.length < 2 || 3 < support.length then [] else
  let code := (table >>> (12 * (truth anchor support w / 2))) &&& 4095
  if code == 0 then [] else
  let c := (code &&& 255) - 1
  let o := c % 4
  let a := vs.idxOf (support.getD ((c / 4) % 4) 0)
  let b := vs.idxOf (support.getD (c / 16) 0)
  if code < 256 then [(o,a,b)] else
  let c' := code / 256 - 1
  [(o,a,b), (c' % 4, pool.length, vs.idxOf (support.getD (c' / 4) 0))]

def guessAux (d : Nat) (vs : List Nat) : List Nat → List Nat → List (Nat × Nat × Nat)
  | _, [] => []
  | pool, w :: ws =>
    let program := guessOne d vs pool w
    program ++ guessAux d vs (poolRun pool program) ws

def guess (d : Nat) (vs ws : List Nat) : List (Nat × Nat × Nat) :=
  guessAux d vs (vs.map (fun v => var v &&& d)) ws

end PEqualNP.Outside.L_meta_10760.AutoPool

namespace PEqualNP.Outside.L_meta_10760.AutoPool


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

def singles : List Nat → List (Nat × List Nat)
  | [] => []
  | a :: ws => (a,ws) :: (singles ws).map (fun (b,bs) => (b,a::bs))
def pairs : List Nat → List (Nat × Nat × List Nat)
  | [] => []
  | a :: ws => (singles ws).map (fun (b,bs) => (a,b,bs)) ++
      (pairs ws).map (fun (b,c,bs) => (b,c,a::bs))
def insert (a : Nat) : List Nat → List Nat
  | [] => [a]
  | b :: bs => if a <= b then a::b::bs else b::insert a bs
def ordered : List Nat → List Nat
  | [] => []
  | a::ws => insert a (ordered ws)

def autoCut (k : Nat) (ws : List Nat) (spec : Nat × Nat × List Nat) : Bool :=
  let (d,L,vs) := spec
  let constants := ws.countP (fun w => w &&& d == 0 || w &&& d == d)
  if L+constants <= k then false else
    let program := guess d vs ws
    decide (k+program.length < L+constants) &&
      ws.all (available d (poolRun (vs.map (fun v => var v &&& d)) program))

def nodeCheck (target : Nat) (negativeRows : List Nat) (k : Nat) (ws : List Nat)
    (specs : List (Nat × Nat × List Nat)) (deps : List (Nat × List Nat)) : Bool :=
  !ws.contains target && (pairs ws).all (fun (a,b,rest) =>
    forceNat (phaseMatrix target negativeRows a b rest) (fun bad =>
      (List.range 4).all (fun o =>
        let z := op o a b
        if ws.contains z || z==0 || z==full then true else
          (List.range 4).all (fun keep =>
            let child := z :: ((if keep.testBit 0 then [a] else []) ++
              (if keep.testBit 1 then [b] else []) ++ rest)
            decide (k+1 < child.length) ||
              (bad &&& collisionMasks.getD (4*o+keep) 0 != 0) ||
              deps.any (fun q => decide (k <= q.1) && ordered child == q.2) ||
              specs.any (autoCut k child)))))

end PEqualNP.Outside.L_meta_10760.AutoPool



namespace PEqualNP.Outside.L_meta_10760.RestrictionData

def full : Nat := 0xffffffffffffffffffffffffffffffff
def inputs : List Nat := [0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffff0000ffff0000ffff0000ffff0000,0xffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000]

def forceNat {α : Sort u} (n : Nat) (f : Nat → α) : α :=
  match n with
  | 0 => f 0
  | k+1 => f (k+1)

def getCode (data : List (List (List Nat))) (i : Nat) : Nat :=
  ((data.getD (i / 1024) []).getD ((i / 32) % 32) []).getD (i % 32) 0

set_option maxRecDepth 100000 in
def data0 : List (List (List Nat)) := [
[[2551727690,1688309284,153642062,225524090442,0x1ec51a24e0d05c800,15570323394,397156748896,1410878538,0x3b85418634de0,484465401248,66586692366,3082,0xf61081862418,33307396232,29693298456636,506542388,41955202,0xa5907821bc24,21854463758222,149958666,0x14ebdc3821844c39ae0,484465478304,542,634,245283973826,0x5714108a509a0,25565933685088,0x12150c2214cc59920,5777878550752,0xd0f838108718a0,15570322242,0xb424c878820],
[38722991088,2652505040,105731721136,73082737552,864276338337648,29693298446316,542,634,245283972418,0x7868844d32a2d0,487342590,6325463976594,0x2a1c42272ab270,41951814,653205999490,28176469331564,370959386,50610359174,346853248146,0x5d8c89ccb0c8,0x240706319ccf82,0x110463238a19ccb1a8,432735171736,4834002028,532834,154125763614,25872067730,0x3e1b2f6332ae24,41794471242766,4854253644954,0x57127afb37159e219c26135218822800,3650],
[64592574664,683965624,236261380264,1986,8342921352,506542396,264253314,0xe41640509bc2c,5258053565988,0xf41b808500e,548425802,0xa520d57d3820c6c58f880,2754,522384199832,13967316104,5314108,1346,2085726764,506538788,25176846,15740042,0xd7d108ec6868,2711629378,0x630839a08878c8,1390504344760,2782086463656,308185436312,953165762,5579377653820,10497794,0xe37011e32392c,309374597668],
[236257447822,189933834250,0x5d2fe5108ee60e180,16150179394,918972149561528,8261621546152,8074330264,4031784898,28669121837116,10497666,529554477267244,1168368056868,3727331086,163444183050,0x1e34bc505108ee68d580,3650,0xec26045eb8,2754,40877758092,2754,123741638,2362946,384475147308,27274818,782903886252942,0x78589144b206286e42,0xf0b1228b91c70488185b278c980,0x7601c16118714,1986,3557895300,896333419046,209932284482],
[0x2e90a848f0879c380,1946699782,92555522,0x4dc58467bc080,62323232180,806,834,490228366,1007176458,0x1e16160a37c56220628c7cba80,194,56258210530,0x387058487db780,1718884778434,0xc147058467fb580,7186033188,59001550,210053139338,0x8162e1a3985190f5080b180,879969872008,60305779516,79701442,1146203180,0xc18e1c22e24,1954,226774474,0x441100c2ab70702355090a980,360721162,0x5e024c09041c28,571396,360722054,394276610],
[0xe910320a3934,0x838193823a2c,0xb9050e08f82,0x627d050e06f0e,0x32881204848af8a,0x10c12bd11cf08ea89e80,0xa20060704342,0x1a80e0e0870aa99c80,76101684,180367106,1795209764,289954352910,571406979402,0x106197c8c410aac9680,5695554129335680,1346,1392552508,11060,2946,18918436,190851982,535562,0x2878b857d237870a5c48,1346,46189790630,8652738,19430734356616,372785954,175437330740,3852838137730,87042931748,0x6106010a8f8e],
[0xe03008c700a,0xbc0187804044b943c08ecb08280,13641666,47309268334652,18886402,60517580421420,210057706020,0xde338f08f8e,172753973258,0x20628c817943c119b2e3d40,59636738530,0x55378a82b67c40,5504019084,1092484,289426278,92556386,0x9c1f6113779c0,1089156,1426065350,3650,0x2880ff03040d48,1986,2545640824488,3650,2793569032,0x2212128060e04c818a19f1c,549494612,8871000396,63336322,907448078,1444319114,0x88484a0181825d69c54785c495383240],
[0x2b0161c6898714,174601644684,839729130244,3650,230838946,0xcd4d050c1b86f40,0xf1e086e848,27414786,516721930280,27414914,18967901435912,143622,143746,3719180,5209936900,27415878,6604084610,0x24b7dc384228b38e940,1125178000,0x23c0334540422338070,0x25c02c2c138250,0x6401e030ca3a030,143106,61139192,0x9e052098d84432ef068,3659854040,6579091784,1924,614,738,31653640,14348],
[14852,3846,3970,4075702,6324006441170,0x1309094030d021c3ae467cac061c4450e4fa0,198,450,73133476244,41506665220620,3821095940,6995071878,24740123650,0xd83f7071a28e5da0,90710655697668,79715425731014,80814937359170,0x4c14fa24e7ca0,71315470,71315530,0xd088245a0e7401058ac0c74304987cf58e8be0,0xe40e243e1980c141c08ff6f818,71315458,0x2a00828c6a3e3c,5649809460,482391213132,141222,30157334882,854791057778,0x160bc1c487c1c5847070bd31b054ff6f09a0,1183399988,33208836179532],
[141990,7263505378,26366450,0x6110120712021e12344a0a173b7071d3554f8820,31148065868,352929220,2074942673302,143858,0x110909c010583e14a529f0c0431b340370,0xe183828c2244750,10773536776,109660444,7600650087713300,29698097302540,29698097303044,7424524325894,27415938,0x783f8a04888c344e50,0xe80c111c5630,319331996,3691552660,137574326668,60315804548,54990660340070,27412962,0x6347f870584917a8,0x7121431aa091998,386443932,568212,257782001036,58091712388,27413606],
[27413730,0xc487f44a291fa,0x1e12245353220870a938084cf149090104c628c88f3ca8b838544bd0678f400,0x7b00b1c70644a8,0x51007404465898,0x59007408866488,5154193645116,0xa2018412334,0xbc0160e18aab02,0x5601231332aa24,0xd802268ccab0e,606935666428874,0x5807aea09c6530738a400,120292933768,7919968828,7919969844,2114,6459766192676,249116651278,511856650,0xb000a01afcf023b142440,41981492,1088556,1474,63195918,142474,0x100acb02c36a6818,2764889686152,1405134396,136951860,7481410,44435618340],
[15247372174,18135142410,0x3c4075e21c210c6e60ea0,1789256695944,139721810492,8074077748,31598658,28170074660,53462724366,273690634,0xd900635f9e0c6a68ca0,1346,268437572238,1345866634,0x21814e0340831e31430880ba0,3679554,1212967566,3090696970,0x3424750314264c88aa0,3679554,143411854,38691957642,0x2c18f1e314308989a0,1346,1392552484,3681038,3681290,0x6b004233c8de1c21514,845162562,20826167589412,3238686478,3371558531082],
[0x4500ae0084e2f30f023b2a390,146104465468,360722050,28063855393580,360722306,0xcf00b624f0e,348139835274,0xf60189900104b0c04912ac2b0,449651030068,141378,1485945380,173819326350,5527660171274,0x2880490020e0bd0a1e31170b8f8,0x6b80260120e53c5121213d2e0e8,0xd021a16284514308842,0x1b40650340868586787828894ee8c8,5252242,0x15c0660be058ec2c22ccf82,0x6a80ac0d06872c4a0e2892cef098,13757858966,1617973650,0x8e00581d80d0338bb08b2be34,172272152978,0xd900b834086858712851132c024,235424994,83440350302618,0x120050d02084228e52b64ae046bc08762c00,563828,564204,569444,142622],
[142682,0x7e4520e28a8346c0,0x7b007e0241c1072640,2133006230976,40139708769600,2282819388,19335821876,2282830636,2109698,523994558222,801124618,0xab016b48231a9661c0,120292910920,120292958392,2109250,335513314456,481070217352,143362,29108551476,4354,1622052,2206355598,1716490,0x8d8010aa5fc58482909f669de0,620145070472,226540036,56635142,3682178,0xe18384e234e4,3258994014,51949628794,2719660608480],
[464158771592,14340,3718,3842,7999406060260,29009923294,29009923322,0x49d1a07067c9e0,1305740864794,659863319873888,52440218,0xcb04c6a848e0,849305901013152,27172827338,321136091600928,565012,889233420,889233924,109333894,109334786,0xf9871921ae4,9353367152350,1644447482,0x3c1e50704aaa2f0,5140,5644,10244,142694,274562,273856205028,15580808286,1644446842],
[0x220a79418a2aace8,438350917906,0xa9033a051482884ab1c8,257781991876,49394239822,1241788690,0x8b805023e0ee09040a2174c188,0x250187808db323c,4833953270,31190959858,0x1c252884084f026f1c18bbc5db464,1661625993842,5017742650778,0x4e801b03f24081095183089cb10c9137d0c339c00,563828,2108690,0xe58044289ac24,30937328670,404761882,0x10895801b017a231a870a40,124487083320,21249192,2026170520,2130908081288,264253318,31609090,3728116137004,7026651020836,3733082382,264253770,0x18e008c0fbf5128aa024c0,16818692],
[60829062,4206850,0x730d004069b38,2130371190056,6872757627032,41955206,264253698,1864074607668,238909734444,28026421028,20872720654,202666314,0x60403dfc239ca90ee0,126632930,0x2ba01f08890e08899e60,806431772,26140028436,370225164,43319903748,10829976966,27416034,0xb1f9e0218489bca0,1653368930,0x1c260f02b089dc20,201606118,1328354,0xc7058469fb60,672718,673866,0x12700f868786ca884ce8aa0,264251722,0xb280589844289be14],
[429581254188,5709610321232964,141666,81965248882,0x2a600a2c443511506f08e0,980876806474,0x59c02c3c2cb37088f8860,126632930,0x32a2016834c7811823407f0,503925276,109661204,109661708,109663236,27415878,27415938,8899456386993936,1653370594,0x1cd00983c0ac2416d0,7558205316,140390,140514,0xe60f068a41e50,18264115298,0x129213c161c87092c4610,503925276,109661204,109661708,109662212,27415622,27415938,0x7e7808a291398,201608934],
[1331170,0xd14835611c574,7558209924,141542,42084706,0x7c3983c1a2917a,0xa88038d0b8b6e25c445cc4912e7c0c70d400,0x43f8038cc62f6a0,46175728420,222308066,48866807066,0x56c0236a415a0,60259679292,44086443316,7518310658,83878329892,7518310478,106868928778,0xac057385584f261be0,0x610030d04486cba0,619217186074,0x17012c0c66a78b20,0xe36030c904a,0xa80a8082530cc89aa0,620145068424,14727172,3681926,3682050,0xe18384e232e4,3258993886,1238580096250,0x66009c903386948a0],
[258059571150,27172827338,0x9407307063b287f0,80009521358,0xd08802047112,0x4d03243040a493cae790,8426516,8427020,437331972,273670,109334658,0x7cc442c5290e10,0x880c158ca45f8,26311149544,22987349190104,754,386035384,3681602,24750576006552,1574,1602,123543298676,224253322092,20464084580,5116021214,58011576858,0xc6008a2871d2df67412a12cb13c,40713121187442,0x4101331243c370086613c346c,1698,8203037298,0x25019161c18eed9a],
[0x1a804e5211b2c16aa13b0d2f0400,21011060,17686436844,21016676,3347868958,244084058,0x40401f90105c150a151480,2133300,506538540,234924836,535310,13643018,0x10e200fd108ec31aa0,1480854112,225221823008,2026118968,2273448,46232,47240,12092,12340,12588,3330,404622,666890,0x10a00fd758299d4127b0,2458,0xb2031a14370,2330,29825085559600,2458,9209242542832],
[2330,950391196447408,0xc11c1c21a690,3274,62354736720,846,5252426,0x10d600570e88c6a79f8,74801744609512,0x78488c6a84d8,299961110137032,529760801950904,879855556,2107086,285486354,0xc408032c3d60d2bc247c,219964278,222307570,0xc608925a1710f1e38bc2664,70877464434,255232538,0x1bc01b8492ade4cac5a7c1012c0,97601489002044456,1134106516760,75170460808,616156888184892,10497794,616123226241324,2544636082724,61308528267150,5489037474296074,0x10ce00541d7ca010bb146dc0],
[23791255696,771796516,27274190,3681546,991768902500880,11300,2894,3210,559273868821704,17721233848,847552680,137997363608,92582024,748760380,4719517602295348,17890883514156,23147044,303777771457806,1939885466,0x67004e0213ffa60e2e5541823c0,387134691745640,3842,5912062152,1744891064,4226,15059710104,3491952776,4098,1746452276,251801858,1746452516,55886098574],
[1478111498,0x2a80221b81552e232f9f469e60,1371614508,533618,840453006,303582410,0x4e0140be4670d20,3711825628442,0x640942a0466c78ca0,3711825628314,0x170328540c6a7cc20,1610,180608322446,0xe04a8082d1a,0x2c08830c0466a80b20,970,66088945077006,24209254788250,0x1e0340be540c6a84a20,1939885834,0x3c0a82c470708919a0,1939885838,335011795146,0x340b83d36aa18e0,10469516110,5361126361034,0xc48800a1bc360e50662eea9820,180363934,151275034,7161997732738,0x90283c110baac390,0x90287190a31a2d370],
[209725062,209727618,28110569613736,136332938,7595822432520,470044802,0x1c5308814729874,0xd81221082bc2192c,360961876580,0x4c04244648c86,8692198802,0x12a00380c1c38104c84312fc20c42f0b8f8,10494402,8935485573060,575613847886,0xf825042045112,0x608a00640b808f83ce05a7f4c1a8,49300578,840451914,0x341e1501888da323c,0x92018d1c8576,2508554651378,0xe838c086314e2213a0ccf048dcfcb464,0x4902100c26a72,0x7431058f368d9a,0x10c012400f81424343122116c4c866ca7812e7c0e2a3c00,4396,41987620,10496974,12594442,0x37800e80f940236a60a8,10495074],
[0x39300e5047188,17059090,0x9f00e70299419992ae34,10495074,0xe54039413264,48244322,0x8848c0468d1a,0x6240124a90511b1a110,0x37020c053038ca19e2f0,2017608840,23143452,1091156020,0xc0e1509bc2c,53034273586468,962624253838,5512678764810,0x9d005b80187e038fe58288c6c88f8,8585474340196584,60448588898,0x16e05e032801422242b0899c8,59523914,0x27c03a80340bb01180c599844ae0a8,0xf802f406607412186f86,0xca00d0bc087112,0x4e801180a415a008481428d116893bc3c,0x13a011a002200233a0dccdc3e34,8460778495698018,0x18990041601c19c01a19078110c2c064,32300484834,0x8348053086722c6b11a,0x38274005c05138186022296a5225c5b8e691400,0xee0328494a],
[24468044997424,9150012607006480,797978,0x1a8164023a9e2d0,4162,127938190,266314,0x11819411c1c222650,0xe4014010706b0e,48245914,0x2300c6180c6894f8,45086033748456,180367426,264203469940,168579138,0xf22028322064,0x3c01093a0909550c46,65972953181586,0x6a0cc5ee121393ac3c,30844596170356,208432274,0x880a09740c2553b124,0xc838e17c0c6c8d1e,0xcc1464c6ad9a,0x1e0a26f2baa13b0f284400,5669608633496,0xa50190d1c8e088,10497666,0x5280fe0213934,91809357871660,30167298,7485427470],
[0xa700a9c710a,0x2134013602abd4423b947140,18257951880,1168717691452,10497666,4676649564972,31609090,356490833678,326516232458,0x6ea001c0d2e5008da966d40,0x5d809191982cc0,0x5c80d1c1192c40,0xbb006347207c70,7974546873424,6711624240,15364,4230,4354,410184116440,3298,2157752,3212721713320,53418718360,106839603336,39858178,53420277556,6744584450,53420277796,6790601301307534,6150445216010,0x1fe011a4003c0190322e97140a63b9a62c0,2586],
[173959186822,871890431258,0xcb01f0b0119b1e20c0,3472886938,0x6580f8580c6a7cfe0,2586,143894415750,7283241318894874,0x6780c904c6a80ee0,48245146,0xb4406931a9b8c,146813250,383790238,143933336906,0x4b584c6a84d60,138423946,0x1b6021047070891ce0,3346,1749658660,104868894,0x6180a48c0d1a,0x13e00a1491d208c6a98ba0,4433399438,2001515589834,8057487805258464,500368941902,500368943050,0x61e400ce03720e30442eea9a20,140738,1108973596,2950,3202],
[5775620,3506720646,230969474,0xdc61c4621c8,12731918,6442258,0x1cdd013336e3918,205533062,121647234,2228500862580,47332827244,0x128284d19992ae04,83360858757180550,0x1c01024046b394cd12,0xf2006f0070d86258dbf22c2598bd2c2b0,0x2c02600c3949112,0x375000601290243a331532c670,0x19501e8188c6a962,0x1a8374231aad230,0x4b80b4023408daae210,0x4b80ec1d08c6abcf8,41788361541580,0x4e022030989c4,360825497934,42058366857490,0x67a8048d00d602700910141e810298f0c1a8,0x2a40420d0208236cc898,6474137542497732,403775170038,1718142117618,0x3481482999e2844460898231bd2a1c63c346c,10495458],
[6872948034162,3436480212378,0x1f2012e01940d4023381112899b1c12d92698282423c1024f400,945263600304,1478427288208,739105198704,139462,39854530,474608583154,0x4d0543caf2e0f8,12591686,22563278722,502569961932,22563275506,3282376642310,3334492434,3088205932680,188752226,331800920818,21921812659244,2759010762532,9886941856156130,0x858053e0e1b20911a,0x1e06d003c4032735650210bb92644c00,141726,1583578,0x7e2503280d760,0x2c8025a002c08861cf20,2820164682,0x61011300d8d82c834ea0,3831717472,2892437024],
[4572857154,1518479052192,210783562,3724682972448,4644625558527200,18430382578848,20686656052320,120561393800,30140348732,3846,143618,3717668,826429198,1716490,0x78efa16184184c99a60,568084,587246604,506539524,126635014,146813314,4280231798500,973883870,0x982c0a069fa,0x2c73829088aa8820,10497282,1241675784,10497282,1043406868,10497282,1043407364,5021901017222,3682562]],
[[0x4bc6091b21afc,37761282,12485466988,3682242,0xcc3140a086fe,0xc45c0886d12,0xf0612ce0a4222ab230,218907678,56633498,7988225158660,5786774,414755630338,3993972158648,421967016,121742921836,245620613732,51641871510,257843572114,0x6c19fcad32e2c,2855639560804,510384430304526,317235755011482,0x8a8042c00dc03c2b4b8831e29678e0e08ad414225400,36718602,0x5650012403b04921870c40,58759092,3679654,3679682,57682702,22027455370,0x43805f806d91b06218a3074940,6577788340],
[1318,1346,113527438,0x6ec01c5c04b0a,0xa500a6021c021808d01b88160a18d2640,589344144376258,91278568727872,219789372,90197762,4089526828,9966083750948,2018,339348713802,0xa0556e142312ab21c0,43160,44168,2950,535810,52472876,1837149732,459287822,3402,0x34f0052c77fc38e1c217050,533922,0xc6c621b8210,3330,527492,3681798,790786,0x38ff02404e4b8,117455906984,32229715846],
[32397488386,381248191548,185233794,1250979069484,2478265975844,2156679502,0x509c3030c918a,0x130a9401b828904ce5e10d838488b0b0a60,23137400447192,822131204,18886406,205533442,8183928513688,23521416,6337375539074,0xcc4121a3c34,25301736526210,9766831392964132,16673435918,0xcc3030504918a,0x26186802942c04a5c614683831bae390,109331426,0x38d00645b03822b2750,29030893038,6043487082,0x438043017a0021e3e08e440c223b82f0,2130908034744,3681862,4354,8727977819784,1994,0x1580706b008a1b814],
[0x37403c1c4a0a1ba0c,0x48401e158042223c04,2018,0x6c2185318385112,0x448043018603c58e5ab8940888e4c8,15092554,0x43006a02103c3c1429a808f4ee8a8,0x30801e1e261f011eb0f86,0xcb00c500882e0411caf102,0x32c0254044340c39fc047ac3c3c,0x90aa0cb8140988d192,0x42806d804c340429bf0f3f43e2c,0x4280450192034340970208aac4424,3813043042,0x83040873561b05196f19a,0x220d90083008a01bc0528b950b0b38595489838a9af651fc600,0x22b4005c1c1064758,0x2cd80361c7064f48,0x64058b81870889b8,0x4a011018469ca8,56633370,382678149401346,713084217916,14160513054,0x9e0143c6708d92,0x4701622b22c24,30814794714318,0x4703140c18708d9a,0x3503edca0505042184e54f9200,1346,7987292814,247516392202],
[0x178212019807201c40b06c83cc60,9135745102,158966769802,0xaf00cc586903a0,10812,11060,3330,31501348,12070158,3402,0x8c7800781cae7090507085428,0xf00c0206e098,2355131508872,798978,306827082548,3230421250,18323455012,30342402318,51741618570,0x438c01340bc1234bba0423b2a3d0,0x240dd009a1ac3b0,7936829754102672,1013375176,241930004664,32218566278,32218566914,0xcf00426ec88,205533058,3805358439476,205533570,717452557860,241741885710],
[2669326528906,0x114d007605c1921c97610f0231bae210,0x3ac00f202c4c0e0f0ac9f8,75778762,0x26405f00b038b1cc22cae0d8,0x10d00bc05202281381c6891444cae8c8,0xd201a043086e86,0x38e83c0a387112,0x21a01880a60121c75444caec98,0xf40a41a108306f86,0x17d004b00ec03c17091444cb102,0x17d004b00ec03c12146d2a222bbc34,0x5402f0780605192,0x64806604e071ab30c23e24,0x216019816403100b06870491444cb10e,0x6d038a09c66f03091470b19a,0x29c00998216019816c025e00c3043915d97908892f259ec200,50613314,840452878,2903701482570,0x48807611128c0,0x3d601611c4840,1275242648,2950,3330,1584180,423669292,12068,527630,3402,0x10c00df68387065448,879969886392],
[172088551592,21559529350,5377904898,18827263036,988252585524,174284980012,1383305724964,1403390300494,60584330,0x60a2007bfcd0704dce79f20,41987108,27274062,3338,0x1dc08b807e6463ce8,568868,3022,18886026,32619534632,6057009176,0x481c19608aa988,53053893692,748760372,0x130010406011a22e2c,0x2600273c11a22f24,0x26002081830468ad0e,378563978,0xb60004c004fff43999e5080ae0,0x1e0141844681aa0,17768285488882,50609015328,859599831538,0xda000ac01bc154a919a0],
[1821301334152,3846,4354,864074284,0xd800e1940bc24,0x6c00d0502f4e,0x36002811a1b050710a,0x1b0078df6061c4a994267d0,9570597799625648,139458,484146854637960,1631653244,198,5252418,7906536922724,71313374,290761874,720173492511376,6068257180366,40894754250,0x8f01e9009c3e1cc3cd542a630,576484192784,0xbc800102c0a023b2ae04,5786774,0x2f200040d0208ecad02,0x116039a0030187838711d4ab0c8,4788894321014,330765453938,4199068824,0x4680f6801434143850115ccb888,0x8d01ed002868887823b2af3c,0x410401c11613274],
[64527821386,0x8f01eb00286828089045733424,95095654386,0x1db003121898368354cd9a,0x1f40550122023c03d03c2a06a03f808c1480c290898d26e978a9d4e60d7200,1346,2010417490702,123237600138,0x218127008f0062026a01f3c48c628c2407c540,1346,268437572238,1007176586,0x2181d203d043403704dc016e0c18a209c340,11836,12084,3330,31502372,12070158,3402,0x465a00257d825065418,18886466,83878328636,1662189157940,365759566004012,25964802,75229720590,474632458,0x465a0030b5fa022cc4ca8de0,0x91800f0f027c2,0x24200342229471cca9d60,60259679292,1191263540],
[7518310530,83878329892,38149451918,7518310730,0x1ab9c3946cacba0,1677913224,5920341052,8994356,117489452,310530306,729960462,1384272138,0x11f003a1d74cc66cb09a0,0x1196800205088d14f0ab1960,782496385312,10785669618,0xf60f06288c08a0,19574835186,8320091201226784,0x31601210702347f0,6880453584,7518307662,126707847314,0xc4401c8682b0c338370,724811614032,3906,20969581814,0x2430016a0f04f42,0xdc8682a08b392d0,1610,0x1a80ce804706a1bc04,0xe7c00603096],
[28518793113858,0x1c80cc807d853222ba230,13925092594,0xcd807b0340888ecf8,14686500,0xc6d800603096,24702374290,0x1c80b1804429ecc88af0b8,0x39003a00ec04fc004180c1bc3088f8a8,0x2a801d80d1805428f09012,0xdc00f803b013d001060e163e2a308afc88,0x37003e00ec04f400418141bc3089106,36536611218,0xdc00f803b013d001060307c10c22402c,0x104300305a0397500314230a150a3c2c264,0xdc00f803b013b00106160e09bc308910e,354080650203546,0x2181d200403017802401f00940d1d822a004f0b8234bd23112b78408a95f469c3e00,13120058968,53779779400,139458,1456497522,0x410540458ae098,23628629106,1146646274,56703540,188752226,0x3a401b6084472,0x7480344586f0e,8479436363558986,0x868021c002406b02b401d80edb5caee71c0a00,0x510006200241c10729c0],
[51867210136,226540044,226540548,3682182,56635394,0xf4404e1b4e4,378367143262,51949628794,28470827337024,1828,2766,3338,0x17e03c83871a0837860,964,3022,3338,0x6a070c1214191fb0,115430927634,0xc2e00daa0270e85421e770,1828,1358,3346,0x7c8e5c3421fef0,972,6436,22820695318,3442,0x5938034f03f60941a2650,1614,3346,0x3c81825088ff8,886],
[1138,0x816008d40222108be7244c08a99c8,19553921548,226536452,4888480646,2962,0xfa871c542a6fc,2038,2290,0x980be033f0e1c6822764,1138,0xe3097851508a9fa,0x43e001300cc0222336665f086341a0,996600500616,14340,3718,3842,31544148341988,8262453849438,1927913958778,0x41012e8009cb071c18d3d0,51867210120,226540036,56635142,3682178,8126160024804,378367143262,51949628794,0xd809e4e18d4d0,0x4a00aa00481c1152b0,33823665562,0xf40144023aa6470],
[2462,2522,229819573062,0xf00c02065fa,6615093008443624,1644446842,0x3e03103818a2aacc8,6931514584224018,0x1874004c5012834c3c1794eb1a8,0x94188050109c4,325554319157582,294708849692946,0x165e00d140741ec34223bb074,510186282305014,0xe8221f0c66f2,0xbe00dc0fc017006058020d0030481060c1179c68a286484dfcd1e,0x7a01105cecd8a,0x18601f80a600dc0fc0fc065002200480609008114c489bc982998bf678abe00,1828,2766,3338,0xe7090a0e0856a20,486,79700706,8044209961312,462,1354,0x5fa0011000700ce170d50aa88a0,462,1354,0x19c24283822bbf0,1610],
[0x5fa000f001100941c12e14,226537004,0xd010a8003444,1634,134514,0xbfc001e001e01ad412c310,3671626,0x5fe000f000d00b39c12e2d0,482,0x6227002483c130690,1924,533094,56632034,0xfa3c131e10,1378,0x140d00bc406891f02d1e8,14348,2144772,56635142,3970,4149324731288,2790,79703010,0x22006201d43c13574,5508,533990,16162760290,2490694126970,0xc04002201e80020261b6e2444cc486070454560,1314,33031538623462,36516947170],
[0x3418e091489fc60,0x3bb00347898714,59435777139116,34238338,4574048014,8869015434,0x6008a01588e49970e0ae0,1314,62332145452,802,4263164414030,369906058,0x985fa0011019201e0d816e1e1b68954e8960,498300897610,0x5c305000280ff00381468a8aaf808,676226,44136227520052,0x30100803e050231c44c,2081048930,498502103414,13590229386,0xb860e0005000500f82855929d333c390,0x3c0638e31a524,0x5ac03a1b9cb186,6594130314,0xb86120003000700e81854fb26733e310,5207734118540258,0x1442600460bc141373406d0,325493098385284,2483700838,5086517028066,0x1f07d81042ac1e50],
[0x4a0ec16386862,0x48010082600283c74a38d3c4610,81428570819084,1271917038596,317979259782,317979259906,0x1d07cc08410ad13b8,1314,81410050248422,83761590242,0x14008402306a452457c,343085284434308,2617919718,292830202210,0x110887740410ab17e,0x14011c00c6bc1e0a39ef18a,0x321658003002805203f8025286088898426f0a244df47994200,0x17c600104119cd0,77343281544,14340,3718,3842,30994392528100,168054110,62287531386,0x1025c00272c1c7066f68,593461850437464,750798414,0x7c808802047092,0xc2e02f81c8041946cb9a8,73035433074,0x6a026e0041b011c050b8a140848f0c988],
[6577787380,51623567980,866,13705955742,5116021210,0x301e40ace110ee12ed4a,0x1a80a0800d8082008e54a8440a36c7c8ea00,1482,0x39020a00bb00cc184b0e,1300301884698,0x72041c016e01aa0f16c3c9a0,2250,6579595777698702,0x93004bb007060e06d9a,0x25c016e01cc68990a0,73039686260,9433099564,534130,1452305294,146239679818,0x176015aca1228590,0x77c007858e18d24,1007175630,8324664530,0x1b0500303402e4029c950d11baa710,75916826,0x75c034c66cb82,0xb00cd00e599b2c2b0,0x108017007198231aad290,2069319002504,31607814,235303298],
[7215057367406700,0x75c01460046806011a21924,10291808406,0xef8012946ad82,0x4b0032c002c021000a004a08dbde1d8b72b8c8,450,29093889988,31186766158,0xfc03848387112,0xc17e0061c807c86649bb07c,487516046710,14011090674,0x3200cc01a808300a024023e013f4012e0ba7021426e5db464,378563186,0xd00d50051c846ad8a,0x5101ec007003200cc01a8099001a01281fa00942688665a2b15728084600,3390268464,0xe43a000e801100c81309090a6249cb8210,0x2de0170d8c6cf82,0x8807606590370a446ce8e8,5254162,0x5f800e0c8150c434844cf86,3512758546,0x190d8017a001c0d50c60214844ef0a8,144854038,0x2d40228170d8c6d182,0x644e004780241981b710a909c3e3c,57264828474466,0x4104005f01b16853c2c06c,38890137826,0x4084013c073a52c6d11e,0x21007e015028f0250c6d18a],
[0xcb00a162005f01635025002403f0008144c97448c6c8180200,0x9718009034186b0e,0xd9802e02d1a,0x862014a010b00d504c6a6f28,180367682,66050867486,0x540847888e4ed42,0x6c09bc2a9dc2c34,0x3e190d8c22e6c,0x37a00440887142,0x30a00c0801a1cfc04688c9e,0x2ba005c193c32258cd4a,0xa88061c013e008c0218024095e62db213e900,2946,535588,666510,3466,0x26a801dc302061c48,571396,2625158,247475970,0xdde1c826e488,4690222365244,21953138562,1670508002348,536962,7034151530382,814231946,0x680d840026024e004a592410e08c1f520,584417861784,6295170,8308079541052],
[14684034,35123706924,4482,25960796046,2696425866,0x680c50075400714963030448272e0,122454820210,0xad00dc3c2f0894a60,172946723360,139462,139714,0x3d90034c0b452864c,139462,139714,90414522866,0xfc801a34301c2a1cff6e0860,0x1d580150b606508ae1820,388140652270576,360718918,8590746226562,0x88400fd0306062118,71303750,5225230913410,33098630760916,847187567254,553519178482,0x1d580190cbd354ef06,155201810,0x1d9003a600c86dd3fc3a290,0xfc801b0503382,0x3f20068d1f8e83142ba650,1731034067504],
[394273122,75488682936908,247472482,0xc47050862f6,52948711797122,0xc500db004a04d60030f0c45e9af0f0b8,139714,515908086,784343666,954436906827324,2508212982,2508213106,500305184341796,0x282860c320911e,0x30081438a32918a,0x680c5002c0170076013804c05a0610321083b0230132006179b85a1373c14562fda476300,7535085514,0x3cc0684022020cd50ce0a8,2250,0x1e2034601b85186f06,0x3303bc074a001112,0x3303c4068403b8584aba34,0x502000f0045028ca,0x403c40244003c06c43584b3c24,0x92c016243c08f9e,0x6b004f009c0a77804e2007c007806341c58f0911a,0x9b8017c013c03303cc01902c803e001c01174811231ba674d00,0x5be0028140434c8,318814212,48246406,247475970,0xec80604e488],
[2651929148,53693403010,5162575936556,536962,54593605518,5302145418,0x5809580094b71d0622295cd0,0x1605d00650049a197cb0,0x33400988071a14a21bc90,139458,6099933611378,84465644989022768,0x46024441382238610,3196303369464,53693400690,390293235748610,0x12c802c6f07cae8c8,6941514853560,247472482,0xec0136084676,52387934594,0x9ec004a01c13e6b2bc3c,10785670518,210781922,998953370148,0x5200ac021804e4009602e2208890ce,0x78a4418e2918a,0x38014802b00a403601300581740520110080100c8620f41ef49bb8a82b3fe2870b00,3218,0x24826062880c2e0,0x2b5800b0b040caa0,1089156],
[186965297094,3650,0x15b400e4829303080d1a0,8099267852,46172420,52438950,1986,8462264751720544,795974,15738818,0xeb013c196bd0,1958,1986,61305878311792,1986,0x2683c52c217b30,29371970,6832374047960304,806,834,1580580,1998,15740050,0x3654f9088a21f030,193407749698,0x88661a867d78,258000334056,0xc660481168c,1314,6424006,1314280982434,7985264727732376],
[1314,122289171772,29369250,0x571003c0851a4c0c1b94c,0x54341e044a534244,1314,4565659890,0x165e002502466c9515895642c09a6114867640,1892696954,0x4500e98075200b32273073540,70,194,51942412440,418,1611196,1318,1346,4177570340,30374134697038,71315602,0x18b790b0a26113876fc0,0xfa801e070e80c185080c58,0xf038c4061861c48,10494822,1314,921463501108376,371341960,75332947900,2891063348,1986,39749492900,142616654],
[10981509226,0x3f600580c775dd06248b38c6940,7700,8204,566532,3462,4354,537434101988,2612993492574,1644447354,0x8e01770079403ca0e12b0d24c0,241024698292,0x181c005813c193cc,570465828,802,403434,0x28029028d5e0208b28d61c0,1356930596,1998,535698,0xec8042f080c78,973062036200,358231858904,1318,2108130,108253457576,39855526,1474,0x3da003190c3122c3c,2754,1617068,0x6a40161300ad24],
[35177917294,0x6811f0914b092,0x5ec0030e7b2fb8139844e51c60,10772,11276,11780,142534,4482,137197888740,973883742,4536303651194,0xe006d001880e7052124c54a20,4162991768,806,834,988279843380,3679522,974203812,0x57401e1c506d4e,49303570,0xe0519758086112957f0,0xd300643a0c62030f0,0xb28058e1032d0,1796,795942,12314477890,0x59c03e412061c203450,0x4408d0304b07030,0xb88058e107210,251696260,12650022214,62925602],
[0x16700a748187061d48,6896343423661240,27249537864488,5252398,1386,0x8400705c0705865808c62151c,0x608314619554,0x3812f07141a0ac,0x948328e221a4,1314,18371602762,0x4ec03480505c070a4993dd7c3c31292d27988,1490043770,0xc000c023c024599b1f34,293741934,921940625869170,0x25007a0641bf0f01092ce7de,0xd033a01e1d0143a1cc54cc92,0x196004c05e801480740b600d80340f81d016c07a014150e409c58314281830f05bf6df2a8ee80,1753173034756,92555942,97544898,0x3cc2c30831b60,21120362,0x16c09f0176010c013e003605f808e0538a818728e34ae0,0x12a028680121b010304,590603116998,1690114745154,0x29a801de0b022b0a379e0,60490539458,0xd261d0879960,84479420],
[1314,488221612,2022,2274,3419594,0xbb008601fc00e06e8019007a00b816f3c440c1131f3d0,9936499401154,0x12d802f056121ff90,370223644,416747203604,3239161356,120629342212,809791878,809792898,0x1fac084611326eb0,95451399364484,29372098,260327522,0x57824e12a7630,51826556432,0xa09415061c6,61705903170370,0x182050cd50ca9d8,1954,402794,0x3603a4001006800900441b1e18c4aaca8,56070613892,143042,482356066,0x31c01660ac1b374,1092484,59405892602726],
[58074614882,0x24600a87985846dda,0x56009805d804300fa02c0e801202e80a1901881c81540222e2e13b109784c3d92f6a9be80,0x6dde00138cc88f78,7692,8196,3462,4354,68225177828,15580808798,1644447354,0x315a800dd007e289a5dc,0x78d3401a824a27d4,56633758,2522,0xda0507066e2,0x102600a2010a8a72,0xf015601c812c0460112520448c6eacaf80,2379778,1700959692016,2946,26307078214,639922050,0xc400d89198270,3138,133190,19157058,14533684472,2946,1613876,1098,0x2d00042b0c12e04],
[13642646,284138933394,0x15800422f43048408,30685818754,44435615284,15317878474,0x316007940047003045109892be04,0x16b400d1c6246f96,0x83f0039c45092,0x18d003c6001f80109c4bf0845c4c21fa0,2108690,0xe760049d81862408,2018529026,16664039220,121646978,0xaa00760109a224,0x711001a094a0c4d70f86,0x4b00396169112,0x17780011800904bca0c4d7039d60,180363546,0x6b400e61188b02,0x2f007f8019263cca0,536642,23091900476552,121646978,0x28100760109ae34,121644746,0x9e0028510c21be04,232297885590,75822350848774290,0x3ec04a60010975430659a60,84428418],
[1267352505392,2108690,3643818910840,536450,61088984,15116543304,56635138,1979858088,533414,13988819010,880588987196,71315458,222376012,0x308030802c3470c081189fdbe04,70378254405526,56205152530,0x3a8018401840161c4ab2f3010dbfda06f0,0x16f007830424ab02,0x4208680564212a12b0,879860260,18885582,1723402,0x1f8033b001dc0010721898329845229c8,738739278,9312053514,0x3af007b2002730d213704198,0x24a00888016008346664a4488,46287822,54946826,0x9ec017f00d98662574186c,0x6c401de022c026400a023b29924,20980810]],
[[0x5901be00d6017601cd8818919892d289a,0x64809c15e02f402e801c1b81e81a00c01102a05a00c8104098643bc028270a0466eafb13c2e14,126109282,908609994,0x179802f40db0044044c00b0341cc54ac96,0x44023200283903b00740222031805501301d80741a18c119ab54d12,0xd500c82dc05a806100283903b02c0380220440e400d0218130b87980318c14178dadb7c2c2d40,1721058,0xd60276801d4219264,1721058,0x6302d601d886c1a,0x17a014900738054c031101ae00bedaf4f86,0xad00e207b80fb00be02da005011d4d112,0xb700c7c056807103ac053ec02b8020f02a40420a606b6d542c69c0,0x165009300220332004c08c6a976,0x20403a7000c0a26a72,0x17c801b81be00780b9009406b001191231b2d2840,41979940,10497174,18886034,0x1da0a360628a1608,28091975132,0x79c00e83047319a34,482949541676,61594151792676,0x144460073a0a7096,0xe3c39629192,0x6d00dd002e03c200441c8156005091fde02809a61148a750,140810,0x3e48013121858c,4126981296420,12730978],
[0x3d600120d1858ea90a,0x32e000a807ae00d872bb995c10690,0x123005b400883408da91270,10497174,18886034,691048294778268,1582461169460,610,0x17d005c1d19b024,0xc23d00287070a9096,0xa72c0288839629192,0x275005ec007032b982795d061a8,0x31407b403cc01703580910074050115cc6498,721023993220,23665992054,283581097034,0x1e04080a2037401d80d02602fc014680833f40c48c4a4b5226c,0xc3802403c00d600d480020222152b244,0x221c1003123670a872,0x1b4075800f02040330345203500c60038063c70b810811a00101131e1312f2d92,0xd100780c8042032c03a0984300107e066068a408402a02c0ec01701a163d0143a059005010a4c495e84eeb8b20,0xcee00120985332c19d8,0x108802730078c00c30861c2,0x368048806680510045800c81e100d1e1cf110a30901f38,0xda018c027015e01e40f3803280db807c3c1444cc2728,0x303c16122a6998,0x6c30023048f06572,0x7f015c0298091804503180c83ce0130e83d3a53c,0x2e0f05848ab074,22014871538,0x4a40363c50c23124,0x4180fe02b80530127008206301907bc017065cb116],
[0x63036b003d200440cb2b192,0x382380260510041d00281d815c02e0884d023e00c7e01f00503203848060787d802d57787822a57db07f0,4978693635245956,29706381992550,615832847164130,2080703157204,19350525316,303580646,0xf1800340cc12186662,0x3c6000703d849ca,0x4d400202f00582080e33036401f00470013806c090254210bbb26d0,0x5e804f01c822814f002a0006004873c48208a30925708,0x2a4000406e08a019002200c203ba01b023b297dc,0x4a00d4028808839c026818406c002800830a229bd4,11823816580,32333907958,2693810402,0x1b10076807f14306d4a,0x10600d802c035007826144088060d80b00e1980c1f0083c0e4101281d06c050901c091f02d80727048c9c608a95f6d1e8,0x4f80068339aa1c6,0xc220028140434a,0x1580450014036c01f8410d44c7f28,21500158922,0x280ac0886fc00302cc141844a8708,0x221002be0030a11225dc,0xf03891b2958c,163401766340,1098,0x272004822865e2,0x13803300a6011b000b80818055e1c8aa72,0x82025009c01980fc15405203302c5205201b0148122d0260640706482a031502598058582b26342acbf8d9a,0x3500240141f01280cc0d406600b0542a80b0fc0cc0b14814806c0b09c07e0341300c240701c0602f01083c2b03989058302245537b807a3f000],
[190887071524,3776472526,447365032002,0x3ad838db5020a680,0xbd000e04110210,0x5080070cc648f8,0x13600050308660e8,412594104536,0x47800a8338678c8,0x4a8006878688b8,0x11a00030610699a8,31610977668242,0x71001d83086a888,542,634,0xf60c306642,0x11a0022818922e24,0xd6000503086c0e,0x5d001ca24186c9a,0x25800fe89da08a1dce249680,0xe900046117670,0x6520078cc221a650,0x6420048611c230,3354,0x313002180c6878f8,3226,0x30d003e540c6a7cd8,2458288328,48245914,0x32700328540c6a84a8,0x18a800c4707089198,0xc4400d40c906a188],
[53120193899068,847724213775156,0xb940018160cc22b06c,50646292738596,0xb0c005842205c8d1e,0x2db00161e146ad9a,0x1188015b801a55ffc878d34e308380,94420579403790,0x1288014c800900823068ca,0x13d80149801fc794c318080,0x12e8004716728d3fc0,94962214346,5848398776123072,4838006251896080,0x5c7000208c1946f0,0x16c400f19622986d0,0x2ed801f0a11a2b0,2508731822736,957989488,115363098,0x2ca8012c131a9e230,0x2c9801340ca19f210,0xb2a000c12170889f8,4833955102,168054106,0x5b100344150690c8,4833954974,168053978,63995365594264,0x2cf8004e44288a188,0xae2000c29f0cc232e7c,0x2c88015824a3034],
[1666659234092,0x2ba8007824a3224,0x154c002610782888d1e,0xade005c161e18c4cd9a,0x1d7009de00220fd7b7f88e76d40f32c0,5711965090506826,0x212003643cf1e530f71c0,0x72400282a061a12c,0x6c400240461b824,0x1c1003101186ece,0x6b400b0f0306fca,0x46c008503cf0242bb926f40,0x1d78039d0a48672946ec0,0xe4361c7063ca,0x3618a2213162dc0,0xc26078140c2211d50,0x3010640c113d30,462895118394640,0x664008c04f2a26f0,4354,538668,30140351012,7535087822,1192202,0x63400fd0a1a0612a4630,0x36200324126210,184734227704,3049432566806,0x2a20018e2dcad02,0x2a20073b82dcaa8c8,0xb08012486acb8,0xa880046824186c1a8],
[973883738,0xbe800e2ce3088c888,37761282,3121366750,556207205650,0x385f890c223324,0x51c00628e2dcad0e,0x15f0032440aacd9a,0x270005080028043c39f4f689c90338cd39720c0,0xe30011839b0a48672976040,0x19e803e18c1aa24,7608623789271886,310340783386,0x8ac01d150dc1c45242dce69f20,0x2f9000f02843a2,0x8c401505f0d84954a71ea0,115363226,0x28a0086031a265c,348546029135956,0x988016e1aa2c,0x8b803e18c1b064,0x5700643b030a1cf088ad1e,0x88803c2506d8a,0x198002190b41cfee022216e78ca0,0x56004f4092866f2,0x14c00140dd0742d88e7cc20,1789460121860,61439023277006,9487064262090,0xfc0fb15895080b20,48246042,0x13f802882212245c],
[6611379796,0x4d600318c1ae6c,0x66c01701e01261e172b264,0x27f00310848d0e,0x4d20062506d8a,0x5c40090c8020281417f701111f084920,81913934166068,0x2c40049c04f33b2c,0x3f802d02c0c1be24,0x1e401b0f0306fce,0x3c80210630718a,0x5d4016110c8520fe46b0e3c2d5247d0,213913874,0xff806209600c04a3834,274578,0x48033044268542bb24,1521555115934,0x83a0a61a342ce23050911a,0xb080680c1f048334685e890511ba66f0,0xa4807432130d070e3831e173a86d0,0x2780840cc14a8c96,0xde021018282dcad12,0x4d012088160d038739f2b732a270,0x6503b406326972,0x2e80c41f18a34232b230,49206956417998,41098023560650,0x3e324334eb0e8,1198307175446,8257122643090,0x1fa01f028880a020891ca1cadceb4b8,0x3f80f86307192],
[0x1f046190b4163823c6212242dcec198,0x3e80cc021861e6,4539037420904994,0x7901b600811884f2,0x441a3641742b008e6462553b26c,0x941d0f833c58f041023490b73b464,0x2101d0686306972,0x783a048246b1225872a0c083145f4d9a,0x2dc00102070d5104caa848842208a7396c895608db7c8178ed000,0x402001c72654a,0x2e1309cc09dee00,7428417547338,0x5e8004c1f40d520f330,61070142094,1410878538,0x1f1001a42b2122d0,7535085854,973883738,0x9b0004c086064838c2217270,4832905934,68176906,0x11e0015c07a19a21e210,0xbc0b0306d4a,0x254002d80b244884e8,218150948,7535087310,104869770,0x468001101d011c8b9c90a99a8,0xe60018c01184c92,0xe60010c03824702dcaa888,973883098,0x23c00298066a09030c22ad34],
[103828882,0x6c40052950b72b024,0x6b0004a02214081186c9e,0x986d04106d9a,0x960002056009b644497682182dce0cd8600,52970890,11352019748,727000327566,88602085066,0xeb6144bb901d57200,484465381216,6779071374,53737974858,0xe70a848834ea0,1241552420,273038,66586692362,0x3ec2106483c18,82525657925768,314615904316,41955330,41302420995116,8458944036,2114736078,4930640048138,0x1cd7e88704184c39ba0,1340304788320,3027419371044,3255855886,1410878538,0x79c0a0218844a60,31142995590],
[5785362,0x9f804050224c589a0,0x10430e0c19ce59960,0x8a1c1065c920,355696449554656,0x6a070106648a0,498359087827040,0xe5439628871820,112174162928,773162398672,41445634,19832374160,101731458,0x9f1841a0750,443107549778736,966637152658,392220001008,5367875965707984,0xf832044d32a2b0,5086350324368,41952198,24249906270210,466435532000876,1746691226,88191314950,3255856274,0xa82c2089cab0d8,0x3c0706319cd002,0x36063238a19ccb1b8,27083007243432,0x881e089cab898,8456207778495624],
[203491436,533090,0xa221a1c849e,6779071634,0x5804198bd18aac0e,692430326938,0x348937fa55f8bb3b8143b4e2947e00,782874828622602,0x40a0008dc0f870b203290,807933604976,60197782096,1598182478384,791450052112,84140574138872,45202436328,15049455832,9680747720,696680632,964986024,15570322754,99124422792,1344432786,24439173524276,10876464236,6555713738,1673226382238,2819779722,0x492003d07fe95648310c332d030c2a00,3367731618254,0x6020242f0726342,0xec309ca31c1e00,6714051342],
[18369418,0x1177800eb05862718,0x44161c3066c88,88150254919228,0xb02418c1a534,14498677746,0x740a597830c1ac64,0x4407022e190306c4e,55902760346,0x740a75ec08c4b14ce34bf200,549746824,0x76001011203c,167814708,1986,0x7a06d051b824,0x934003f01f01426e8e,0x616000280300a,0x9100f760033035c21d836a24da0,0xf600098027888,139721810492,0xfa00140a834,67109005250,67620217894948,3989761453838,4363692028042,0xe20035f9e0c6a693a0,142650404,35662670,1345866634,0x3400f8000402047de19ca78aa0,10215303716,2419608334],
[133164976970,0x10601f24006600871f861302dce889a0,771796004,1749044046,585480825738,0x580610002347282dca988a0,146142154318,2553827082,0x1f008f890841c2aa3f0,1986,987918055460,352472846,192950282,0xb819847987831aac350,1346,29264820260,4267605782158,1749045130,0x33285e60b0daad2b0,141250,31878670,1517757165578,0x2e01010f8d0f023bae230,1138,0x6805f0002120c612470c3087c2,0x10e01a3d48000c0a808483184de05b4ce0e8,915446803392728,36720258,13994749112,0x1248001301d00c04f96,38673084546,0x418038f6200350040408c70b70a0902dcef088],
[0x44b806f5a0020600903320630c23e7c,10760507794,0x408068f5600350042418491cc0b72c02c,0x480c240461c224,2114735330,0x37982010b0b19a,0x408068f5e0005014e02084266309ab5579e095f239afe00,834,143899313712,11580,569396,3074,536868,265358,3338,0xafa9104868a8,11544514,3264249112968,3411261664572,2107086,3346,0xc7e2930a3024,6706850958,81796043664666,0x38bbd428e2c6c161e80,120292931720,242599666236,50374196,1986,0xf602813824,8059514638,12595210],
[0x4e80085800d7a2c36a171680,8967376,1375598731952,1856635073168,3330,504037968,772489776,2337277706768,2109126,27275266,27900711855320,637582340,143494,4354,31647896,60552,7035164900412,27376130047284,4354,1622052,3332963463310,26882314,0x6802f8001e008d789d710ce10c23356788080,2267882210626,0x3e09e01162c21e7f40,103784165608,103784166616,3202,126007480,193120424,2109062,4098],
[3717180,3496111847988,197576964908,572964,27313852430,36519964874,0xd5df915347c1f3840,47514186832,1309860400,349235769872,1211649282,156825338088,294264295640,4354,37048606904,2688869544,0xb070b06e898,940782840968,0xf01878a3c3c,7855503719732,4354,6885185011748,206293201038,7927500919050,0x6abeb908d0b1a2d5202f40,0x1a00be000781908a031c6872a06ec0,1095724,2370,40814792590,6455054538,0x4b580416192a12c40,0xe130e1ae2d0],
[111938826928,3681538,833459782256,1194237051472,4354,25920016,58616,3193860,10498182,4354,0x7e140606e8b8,103280864424,139618,3500482556040,3878363970876,0x9603c1414034,629149698,80273496686884,0x6e0085a08508e,0xb4062850310a,0xd005f001b8240902aa4ad7d02148a2d4a62140,1986,18279717517356,30241012004,10636942,15162568714,0x1e1e1e0f0f382c0c6ab8f20,1346,2027561269292,30241012004,5456809614,1749045130],
[0xf0f0f0a82fc10e86abcda0,1986,5286444,11044,209865486,142474,0xf0f0f00c1f70da341c,5384130,54081580,21543204,5506408279694,11115057162,0x3c3c3c0902f840b6ac0aa0,19015618,238630956,76069156,38864572046,38847795210,0x7878780e011f20e0236cd0920,163244833576,972,3524,2254,2506,0x1a00be000780cc0a48a73d4c1c58a9f0c,197576957732,10202802134,516973408530,0x6802f8001e0283c121c0c29228c67a82270410cd67f38350,29687394880194,0x320222c6f1338710,18264116594],
[0x1e030a48a58da38208504acb92d0,0x6c1612281108,352611075548,2405471196756,235195703596,0xe0983d0160cc623c04,0x704c1e82c2c3318b086,0x1c83d05c3e05112,0x500854345245061fe62458ab2b6e8e8,0x6802f8001e07d02c18e0429cce9d8,6455053682,0xe41d81560105812aecb8,1738,0x6a00103d078128162,0x180c2e188047c44160236ef088,0x180c2e004090c143a1b3d3c,0x1101580082e049ce,0x1d0140ec0503112,0x34017c00760509008143870514914f866241868ccad4024,0x3a0102864290584080456f08e,0x10d170e4408882428d6060aa0911a,0x27401a1e84007e07e010d05a0a163429491450908addc4042c49bf64184200,1993805424014,1993805425418,0x1e40314150618bdb0,0xf038106616,19865290498,0x6fc0202833296350,1175545648,335075701520,0xcac161986f0,121619718864],
[18751896007344,62294273933968,2786714224,38722990672,41445762,19832373776,0x5d03810684f8,7139137768,249166890092,140402,20435725206,3255856258,0x1aa00305984cc8b098,293908872,20942236988,43664498,0xcba071ca2e6c,1909043236,0x83805d038106c4e,18120461450,0x7d4002e03e806ff5b35e780a14b3123e300,7535085982,973883866,0x3be001441c03584c0c308a0cc60,140410,0xde03101402281d3e0,0x44062019030434ba0,448696650592,2955747511072,159394838,159395090,0x105b000bfc02da1219ca81a60],
[30073226692,62287529550,16777489682,0xed0019c406e48061209cc89960,0x11008be00c11119c10899920,159421956,142598,39858306,0xf70e08a10e4,1278239838,29030892666,0x8301fc9aa3b0,3076,2438,798722,32580598899608,48490617382280,798406,4098,6975177951724,2418,0x5390010858306b56,0x24c0127068106c12,0x83004e5ec0c12b230,1610,5326004891212,39855218,0xce80ec28a8c96,699318413331714,0x9700bd832aab0b8,0x4e80ec19c8b4a8,7915671938638],
[756082307218,0x93014f61972ae7c,0xa1002819c8d02,0x9f01140caab02c,1403420427378,0x24280630992aac9e,0x11e0284d832aad0a,0x2ac03fc80138198086017c4f245392e9ac124d49437d00,0xce804500f8382819ca3408,1009852932,252465414,252466434,0x7f030185329ae4,0x7804340886de,32989896279802,0x142009df05865129476d00,0x2ada0004282728fd90,0x59a00e04113d70,23657990554,0xf1f057316530,6486508494,24293682322,0xc9e0230650272206d0,0x89e01d064820422246b0,519081662509712,970,0x770008330a12c44,39854706,0x2f2001056c6c12,0xf60360b7092aca8f8,52983938180046,6895726610],
[0x20404c09a5c8b1c8,0x10203a010b832acb8b8,991103566450,0x68300f0da609c8c198,560132,141702,39858178,62813368879332,2065087619678,29030892154,0x4d01c83842e0228cca,0x10600c56d9ab92877b9533500,742409338,0xc1019602628b80c209550,5785166,61238962714,0xea01ac0cb0572984f0,5784690,0x3a806f03183921c4b0,6880363152,32415289968,115976717902,59649747602706,0x36a80d10666f3a2610,0x4c701c5d04204108c99f8,0xd900b819c8d02,0x6b80b0d032aca8d8,0x35c04d049caacc8,0x364046092acb0b8,0x1ae027809c8b4a8,584149395022,9043210386],
[59650274897532,0xdb00b819c8d02,0x6c809e0272302c,21120114,0x134c0127809c8c9e,0x18a004123049cad0a,0x542bc0470328197abe4b7c1619ad4962ff00,73261924810,0x16c007d80b20508311030aa888,722915585046,87822462226,0x2f80054803435b090cd3ae2c,317931946722,0x4ce002681b9878708c1e,0x160134021c38a208d1a,0x2bc03b5801705415838811c02e0799832e21608b73966ed00,0x4c110610681c8,0x4c110610691b8,0x7c1f07869ca8,0x30404c170334aa898,9144660162,9940889644156,0xf700b819c8642,0xcd0090ae06722e2c,18370754,622033652766,0x5f80881149c8cca,0x16e01f8026014749650ed3172d500,0xe8321619934,0x9011a0422a2c,292403915812,223406484430],
[0x1b08c020a0a208d1a,0xc4a20011e011802b0360c83e4314ad4186c900,68175886,948980234,0x37a01c43c30882f120,338654283483360,515668812356,221763373462,41445890,0x276830c1042a03f0,5105536022,7253019922,0x20b600143403a48672a0790,0x821e18c221370,240935601604,7713343054,8321772818,0x55c0060480109d6f2a26f0,0x1ec02024008c5e0c7042266d0,0x63858741042a82b0,0x42002819c8d02,0x3e01140caaaa270,0x7c03b06722b250,1610,0x4201d86a1ae4c,1138,18794890947734,325484459887874,510198255497416,9852638229738680,484826048078,86000300178],
[0xb8053d865cab988,0x2500140caab03c,20341303299090,4644865504850220,3772785778,0xc0880332c9c8c9e,0x18071c6c19c8d0a,0x1e74008600f802e025809349ad3a9660c18ed41a27d00,344950148500,53889514705356,2409583749668,5786382,2711121098,0x954000e0208c016301681f387d39c67100,0x5b8002c40110ec04a9e,0x54802d07a06b0a,0x1ec00d9001e3c2003c0d4308ce283210,0x1619b0047090634f8,0xec1d40684428654e8,112009322840,3490727234,670357301432,0x3a90006c0104a92,0x8e002a6014e433210aac98,0xea4002206c04f92,0x101140053c0395d8112aac7c,4408230094,36526113138,0x18726000c2c2045caae64,3342970424478,3772935562,0x1a201e0c003c1982d404c2d80b06c14e92dca1a130449e49e24d00],
[0xf200d041061ce,0x6c401c72654a,0xd82242739e64700,0x5a1c003404117dc,8804903078140884,0x32603470c19dcc,352417108077668,688832146462,0x70b0b0306d4a,0x7500b9004fc44848a1e39f23900,0xf831025066197250,272706852,68176846,463924653194,0x6e400581e20c30410a8968,197636680718,68177098,0x4700440e20c30410a9938,23099425071400,656847000,0x2c40022219988b488,165785212,68174582,41446786,0x5980173b8184842b024,33312763038,7047507338,0xf4800b40680a00500ba02e070283e04dfbb0449e32021500,142018,296471345188,825813405454,16648261770],
[0xa300b200604e07987831ab0430,142018,252786724,19433287438,7253020682,0x2c80181781f9e0c6ad148,0x58041000a32600c6138c3087c2,0x58041000a2860088184b424334ce0a8,21450157648024,104290348946,0x5008e0032200e194a81818ccac3c3c,104626414306,0xc746001b02d06120c23e6c,103829890,0x1601040018ca8030c5a1219cb00e,0x7c08c630718a,0x17a0163c080104031a602c80182706e831525a6830c109f481f580,0x9d80a1e0e30a7708,303067458,475866148777076,0x321a3e18c22e2c,18370882,3440824052766,0xf86530e308d4a,0x95c00120148027803a03415710b1278c84ed80,1986,4157830652040,3714,46217116468,2714520632364,4482,403752251406],
[557855114,0xc30024100164014164055d42c886c17020,0x64401841111f0,1986,6390979606572,30241012004,115976720014,7713345418,0x13c09c0183506b03da0d031a99330,14025894594,455203385620524,0x688016093924,28724833701518,14025895946,0x3bc0390270060d41d40f3808dab4470,1098,0x1730005035806c1452951c1067c2,0x5cc00140d601b0514a460e24d3b8210,0x282e402949409c8e4f8,56632642,69301487404100,5778360656246,104024009490,0x1417201411cd065bcee8a8,0x401001f04872c48f150ae998,9965951970440,12905890162,498488949812,0xf81f1841bd2c,266356150658,0xba8002811400a0080450215bcb00e,1856567792010],
[0x30c03d0801aa00a0bc09c0181a183076028060d29acd57c6442c32bf889c580,1986,987918055460,8539918,12595210,0x7a00ac01f44f0a8fd70,18883014,1986,1667437246508,223590037796,62926478,3284160522,0x47403d9e1850a91c90,3726194800,36146715394852,1010,0x640440d2008822141151c1067c2,0x190110348022088528b981898ccce0f8,0x220b900e8089409c8e4e8,56631874,791888991489604,22030746614,5111828242,0x4100882e403a0a388c89cce898,0x36200040d1c91901050ae988,2491487992636,9674590141556,3284157170,0x4a006c04407a00b04c0f0e04310e3323e24,1980048117774,0xb607c610704a,0xf7800b41d0f40360221583613803034378287e04826078724b3af7162c2ddf899a680],
[111710602978,0xc40020020f85d0263c68278ca1a480,973883866,0x37e001e0af80121584c0c308a0cc60,0x702ec019030434c20,159421964,159426564,142598,39858306,4144652456164,77513909342,206430037114,0x96807f2653220,846,1994,0x3160026601ac08e34201e90,206,1994,0x76026e01ac08e34207e30,3812690956,3812697604,2446,13642882,8849218597299144,2378,0x578011038c1e72a25a8,118,2122,0x8601de008836a60e34209fc,1778,0x16a006c0e4147042176c,1398]],
[[1522,0x1e600f83b828f066da,0xa60010401740150020f8662cb7c995050,3076,3206,4098,31406692600036,98831458910,1376002269818,0x4a07e01c807241c30654b8,159421956,142598,39858306,2022938611940,77513909342,206430037114,82472220249134404,0x705300b03047ce,0xf406e0bd00930334cd12,0x6780785000500b011c01f00f8130140082502a0040508868739c21e2c6497daa3940,11544514,6313583132,3334,4226,1561233271556,6947107078,6947108098,0x1bf06030a531afc,580930242,74818742557548,580930242,4703024097022],
[0xb38008224501047c2,0x5ec012ec6e9baa7240,0x33f680010a09ca8738,0x95b00381049728,3076,3206,4098,8145149724900,876475867742,1309426298,0x64090e100fb03049f6,374385461586546,0x6c00dc06e0f2002006078f331e0a04abab2cc0,34149692,11114548,1661124848428,1305811234340,7255117038,4969967300754,0x780b201cc0fd3c2c67384750,20983682,0x49e001c100480c098934,6996176172,1306075475492,30606905046,0x24f000df80196040e0508f92,0x93c004b013402718035039f6828b0106738e670,0x6203a043006c0c27297250,20983682,48447814240556,34150180,976470349483926],
[0xc1010309092,0x1741c81ca78c2432ac81c8,0x902b80e30684b8,436749962,190660612172,0x24f000ec8011c244c6b1864,0x2700303d003e00583318864e,155840441242,0x24f0001b002c0f80303d00f4047028cfe872d74ae4c,0x2b00303d004201233188472,0x3aa003b006402582100607a07880d063d09192ad0c96,0xac0fe0084013049cad12,0x1d5001d803a0048230020f80102f009001039039a68bb196ab2b0e60,0x3718001022618e,385653754316434,0x2f403c98011409b804608901f4094bd0f96,40269649834130,0x2cc019e4c00b807018aa00904c807c09d0020dc1a1d0610adccb1d20,0x1280aac023049ca9f6,982965819042418,0x1278000e800e0841fc0f20020ce05388143aaeb4c60,1986,0xb940088e52183c,1986,0xd880250482c2c219ac,13642898,0x15e800962022867c6,756986002,0x45300146800612d10324d382310,98,18374301740,173723987492],
[438997142,5387604370,0x219c002fc804040418c2383250,71313026,0xb4200166007e401cfc18c2204610,0xcb0039b001082d400c120c22cc1778,610,1932510914190,146114515090,0x2b080050b026c649cc4138,1122,0xaae001fa007e4006090402162,0x4a6001c7000c041826f05352ae6188,0x2303e008008011003c060b008db193c,0x221e292242822ae74,12905891954,7389216627601188,0x4a60017601f00400401c8030418f87954f096,0x2cc8001822789192,0x2829c0047910028b0b1a817400a08c1f0040b05c19051e1e1c441f0ba072c5149b5e472d7dae650,948981138,0x31004b00cc0620b728bd4,63084553114412,0x9a01701b40260506729b24,0x8c0fc0ef0049819cad16,0x7130010c05b401a1081bc032e0608ccad92,0x2e40389801d82480c203e1283a018160a82f03428a83a06603ff06584ab0c0b8,0x680c18008498fcc,0xb40e806006002c027048119211c4,0x820061986cce,33312764306,0xe58000e078a0100c2b8067414a0e8060583208828286c07816c0a06051f90c5fd3274],
[0xbc170b406390326406606c021a0861273b46c,2557633266,0x15c002f600ac12108962,0xe26004b03b048400c2c39a38c809d02b01c613ac49dd0d9a,0x2ec036f80150676058671d817c07c27008c85c0c48a1a0a14370a0b010883e0a5068700819be1c676c537b8271f5000,31190961438,297815386,0x272005c0531001b15420e310,222309650,31408155278,182463770,0x31e00348231a90290,0x385006e00ed001a839216270,52971402,0x288070200e260079198230,3289410442,0x4b0068f000a18378878f8,0xa04004a05c100110610680e8,0x6de006e83288a1d8,56633370,0xbc01a5c006c0c084aceb86,24232308796690,0x168034080071ec18958ca898,43166754842,0x2e08014c0496006f0e82563ac3c,5756531795998,0x678004104d92,0xf805d50005b800c6644ab32e24,0x19c00638e716c8d1e,0x3c80192106d9a,0x3a0189c00204900094b22dd20448c6e173880,18369602],
[0xfe802ca12024,71605798725966,6906997943362,0x36a00e905cc4c31b380,4833955098,0x6640148231a818f0,48246042,1521251627184,352368692,352368940,12595330,281030606,549466378,0x484015a68184878f8,12595458,1124120620,73056469540,18264117454,1086337290,0x2e600f940236a9498,31190961434,1409338224924,0xd0080c03112,0x43007c39cca0cc62382c,27929882770,0x9f003046506664afce,0x32a09108924821a0a1b8b11a,0x94004a82a512598482e670399b80,94962214478,2328668354,0xf728cc4ce409880,4833955102],
[168054106,0x4f00310698154209c50,0x7815680084994630,0x55a00f010a196610,0x2b5007c28468f8,627182955752,96968395836518616,0x156802868378a78c8,0x2ab004d061067cb8,97531132597670056,20067178157208,0x6827c288a188,0xa9c0008261622c7c,0x2b3007870b23034,352399241516,0x2ab0068904a3224,0xc1301825c8d1e,189046746522,0x15810c800103c37fffd9031794e448480,52972482,473340504514092,0x1810c0208c1a324,689618054054,0x8c04450550abc2,0xbec01183d20a212917f40,0x3a6006839216470,63909483627600,0x3a2014a11e230,0x73c038c11f210,0x1cd00440cd44a81f8,313122130792,0xe34a11888d58],
[0x1d10063810699c8,0x2b2019823049caa8b8,0x2b2018827809c8aca8,12352516034,0x71c02e16c8b188,10810928700,18369558,0x2c601d823049cac82,0x2c6018817341272af24,7969314637892766,0x14f00dc1a3049cad0a,0x1bf00a7801e067fd774c098b539435c0,9104580199099458,0x74402460028150694a22539474c0,0x1a100df010a213153440,1134834099484,0x6f8047009a1aa34,52971682,0x69402609e22d24,4578380870,7582245576010826,0x6b802ac0d06857e08d539670c0,0xc60b1c70644e,256157890,0x1fc28b6254182f40,0x2b8016c0bc04618fc90,9799277325925488,723100752,0x1660031841a0630,0x1660031841a4610,0xc7004428498f8,184734227688],
[80502605438102596,605596175382,0x3ca00a40e49cad02,0x1e5004607b849caa8a8,9781367403883672,0x3f8018e16c8b188,0x790031a09061b07c,1309426298,0xb002f03a442322c,1309426298,0x1781841614308cce,0x1d90042018d2ccad0a,0x9f8062c016050182e031fc9d2c43289654992540,21551942566,0xa0281186bc2,0xd6c00d0408391c6529963c0,0xc8800f0284426,5786562,0x1de0092018161ed531c6240,0xa58038441842205c,0x28e0123218422654,92042902343100492,0xa38010412a24,0x35001100183788b1e,0x4f400604106d8a,0x15805e0482c0707f7011278c78f60,0x25403e81d06306772,0x30802303984855b8e7cee0,1788187128092,0x19a008828423834,0x6f5001106106222,0xc700a20de23a24],
[980767694942158,0xc50070d028610b18a,0x14600c81f07818ae38342aa7081d20,787298047255630,0x960e118664a,0x3984855895288c60,0x43e0984c242d89508b420,1169858910600,13291854460,843127924,322395349100,20439508068,496990070548894,68176410,0x1c2f073a0d0ff45b94c8c220,3874919425108,0xd680718a11a64c,469492677323876,60885524565262,912600060816778,0xca018817028e81851fb808909f28c8a0,0x21f0443c4c2945b9508d060,0xbf00a106e0e,901602857742154,0x35403c360f0b873a18b15cba67d0,0xc60330040703c2e0634784842a87b0,347474133797658,0x1902c81a83d0225f42c44,976425402928278,0x2a00603206e02849cad12,0x2a0060540280e1c9833e49732a310,0xf80bb023011869f2],
[0x18406a0e944a843ab2d0,86002574,125981074,0x32c06960b070a8c2708,495080514,0x86039b10a0a0222c74,73116182690,0x17c01e0f8041e22d24,0x86011f0112acefc6,0x2205101cf1e3610b192,0x58346088060280871c50212fcbf54b1c8,0xfb02c71c19124,71746910185038,2196940994,0x1340e70514104f0b888,730094648462358,0x9a01f05302452ccac92,0x5800c090b802088141830a7c864973af2c,0x1d01543605806070d491b7943264,0x321d0680c0c743060181c36453dd0d1e,0x542900b01710c2d070705bccd9a,0x4680adc015064432428705e6486dc5cd114eb12826fa2db7c837053000,0x54d80071c99524,5920277442,734786520474,0x1e7001561428108a0199600,3811074958,640705930,0x1ef003a851c534e0318a00,6014329081193934,68176706,0xa370004ee1619dce0597e00],
[77343281544,14340,3718,3842,2045495063780,168054110,6989827450,0xab50004f040434820,3082,0xab9001d80a0381870c,506542884,66586693518,17313802,0xd1556003fe162c1128e750,11275355662,344537983882,0x1566003c8381922f0,0x2ac400160a112152d0,16227787590,327306058,0x555e003c9808b296670,0x552800e260a11218250,0xab3000882c58a21c630,10766936730,0xaa90004b8c81087cf8,6989826334,2887855549074,0xa83001e3d414225aeacc8,0xd522000c4c18c30af82,0x142a8500194c0e022cab1a8,308218528868,1918911518],
[0x546800b08606c92,0xa610004b0b9e0444cb2e34,447954316562,0xa61000d0c30728cb3024,0x150e0009c3876cc9e,0xa0cd816c8d1a,0x529800a6ed6445cc3394886e070e200,0xc7cc005c1780410303c0,834,0xb5003ac114690,266440631920,457821638509136,0x1258008b9001f052c1aa630,369401972240,222308074,0x7e03818a2ab8e8,8424452,2107142,2108546,989992076334,222307434,5312893861000,502,273682,0x49200039800e83e0e051ab02c,8335798820,222308066,3689435917594,0x12580009a00140107aa6a886c1e2f01c4a0,1376012782,12734474,56488154485728],
[2083013058,0x8436428878b60,0x2707832887cb20,24723334594,0x24b0002bc00882e8a6940881aa0,0xc0b03288c88a60,0x640901c160608a89a20,0x521a1e06088c9e0,763994598538,0x190ba0a2844e90960,3832154400,569019154008288,9942945788234,0x6503108138cbc860,246033707018,0x6506992b03f0,895293091722,0x360228e1462323b0,8426500,2107910,2108674,989992076974,222308074,0xa020eb01261c6,0xf008e4af82,453214037312176,0xa827078309b39290,0x24900042400cf80e05402,0x1891400215e0036055022a0a0c2ba650,126632306,0x12880021e005468c383a25dbc210,0x4a0781c160608af1f8],
[6989826930,0x10f0014506c4826ef4d8,686284442568236,621027657508,168314518,309386850434,0x24d00019c0024018046e7c8441916f4f888,601732170742,9624619602194,0x9040007300190502130d220a25bc02c,0x640c3c1dac224,9625693342178,0xd8373061504b11a,0x6822d001e01f800b0a82c32aeb4908a54cd550a06163cfd8c7e300,0x15a0a91000440e3318f9b0,0x6cc034c00e33193990,1925725695020,43335626020,2964343694,6664768522,0x1f07f161a60c23272f0,53412358033482,0x16064106c71c2ac2b0,10833907662,9942945788234,0x12067b8421842ad250,88143327118,104626417738,985470922701048,4162,2138417688334,622799777866],
[0x140e32866160ac0b8,0x16e2003881460a3a2,0xe0dc29b0f3090e898,0x1e07098308ae988,0xc0ac3c0c1bb3c,1208501366,0x580c74194c9042,0x110e7e220b5333c24,0x61a08a3e199cef8e,0x19044273734c19cd04a,0x362d88bdfc5c68a2d48d7a900,0xac30001203f8181cf0,940592066,0x4b0611e2946b0,15570323522,99289227888,17046794832,121116426800,121116429328,940591002,0x7361c10888468,20085431764184,76361925960,4564470146,541325691048,36633481368,1915715229832,19339952370,77796988856948,15570323522,105266654244,266357582],
[5437418634,0x4d2000b1800975ad2f21c5808655d60e37b00,623039761218,0x5607067738e77700,5349956295239928,2108694,3442,224974516424,901977002424,14348,571908,3846,3970,17050481908,672216428,1382,140770,53158759802,0xafe4006b3b23086207d30,0x73c78082383c,26804077345076,36509339906,348018817572,2619395305550,29007674372362,0x2ca001a0aea6050119314650,0x1700c341121b230,0x1c1c084404220210,492654123583736,0x19004244810894e8,790324383180,1698],
[6187710965710,4552982024466,0x1810004691842ca1c92aa998,790324387428,4613555194464246,1794761583002,0x18300287091de0283109cbb12c,242,151537250,0xe18639a84a0ccad1a,0xc380030e7b09acb81851b0f32900,22561973902,1993805425674,0x203003c838187d10,8268899191042,85665271564027600,51742533378,0x7b0194906827298290,671375540848,210689983056,0x8208833221230,4564470146,816060860664,7642452200,0x3b088108894d8,80337380481224,143362,545407862,41138810754,0x6e81c728a988,62291722398,25872067714],
[0x1ec00416ca3322e2c,1909043236,266357838,10000813194,0x22b000234007b00975c9be4360dd3922f500,0x8f9801a60260619ca0c160,0x2302380c81409ca34120,0x78740448350e0,36442761346,0x4e0683d0210d3030854860,2771354421646,859813472794,0x3be0054171068173241d0,592637490529712,1510232006,22592638978,0xfae0e2ac750,49394237810,0x18804046f3ae310,82879097008880,8064617746,7129288460141232,1107575794,0x2462110d22b2270,6798421862336080,0x3402c04b32b8230,0x6428004886ec2,0x2c0f90316cae4f8,103224032772,1138774166,163248378114,0xd03a5c8e8b8],
[308189837585576,585571692696,0x72c82a88f488,138792693906,31551008161332,31147454722,0xb1706a24024,0xa12810a50e0b09e,0x681cca809c910a,0x1126800865001b06260320683435b952d13a5d2060a1619ad5946ab00,0x12415220032403865217910,0x82c00270419b8f0,273418,332886282644,4536996608556,9043000100,107562946318,26048745354,0x15c08203e1014022931dc10,0x603206106b0f8,17920231388392,0x81106106b8d8,0x7c2306106c0c8,0x5c060c306f02,0x885449cae0a8,0x3284004405078c85a2,0x58711853194ee888,0x2c38b20b323b3c,1208501878,29008883906,0x91c662818cb333c24,0x71a0890287194ef8e],
[5081260994908362,0x93400f9e9773050286fc9567b00,7535085982,973883866,0x2ac40008c03584c2422281c90,1410878538,0x2e0ae06a1918f250,0x7a0385120f630,88789928240656,18295849208,9680749800,54018357893592,663134408,0x98485cab0b8,0xb02c0888c12,57743784981656,370959390,6077414935698,0xe202172ae34,11820100866,81673695268,0x6272609ccc9e,206701235466,0x25700030c002a015805fd65ca14e18c92d59624f00,0x2a012800e0740cc8076,0x760141c7265ca,0x7280f14296184239664900,0xe818003810863728,0x5640381044f18,311351876744,180392837662,0xd1c702288c12],
[640262093286444,380659412516,0xa3740428c1e,3576651345098,0xc500384013de624691ce541723500,1411926282,941306896041072,4678462596688,464294388272,3264243446288,594857265092,13825500366,22569839106,0x22806e033a4046810890c8,9993333426919864,27420992643240,321302680,713340040,80326204,178335540,31142997250,1360113700,47484062,6856142090,0x9540005f002900880b8350393f5fe0618b539820d00,0xc401438e2228dc90,6814195826,757362757531728,940589554,396497598480,515467792120,20913295110376],
[107802440920,533004204232,0x6c361a1c18ac0b8,79414042486952,89083032824984,190925268086,25872068738,56905191046196,6846254595628,4574956109860,0xf1c728904e,0xcc83810708a,0x9540005f00170181600702e0cc03825ff7ce170b122f5671f280,7037703415263888,6441758,4041371082,0xf64000101d0c10422f030,406924084,412899978348,18257883428,1010,605047946,0x240e000280d76060944ac038,22197481956520,7250924546,0x94f81848308e988,16125018482,326690257972,10758406602,84024639012,2703238130,26374852618],
[0x524d0019207003107c0d06a524a08044967079de80,0x7a15220016e0041048638,0x760be40027869628,0x1d407404106a718,0x6bb800f86306822,27437203339836,1208502518,68178242,0x63f11058c2bc24,0x28228f8630af8e,6745518410,0x4ae00192801d6f70d1426c7dd380,141970,1065429796,650128158,4564471178,0x559800b3007203d4302080748,0x320a901f0fe083cb8,0x905607e045ca8,7629447410,0x64d044348aa988,0x710241c1ab7c,208046932082,352325839916,1065430308,6640625028254,965845609866,0xb19000b82e0140f8060685a08c1aaf5c5813c65dd680c380,0xb0383388c81c280,8368383465117496,917405442535208,0x758121c6887718],
[0x1a090d832c8a988,7778592729980,422087602292,1394,272639702,74788392175602,0x320ef00882c7f0981088d4a,0x1903703e0180c80105c0be4cc0a0a4cc84b780,0x4100b0304199210,155910777444,498,5364683664394,0x2a2007a0f83580538587144a9948,0x781808b08a92,0x5e025503348aa9a8,5567905443224,656849032,0x760c40412f3c,0x2d008d810861f6,16644066690,0x1907b80b41cf43220422b024,33312763038,3289402762,0x17e00360c80e0b87c0104e0982c250117dcc22092c4e88a780,19847061086488,2706,5913138277180,4098,5811308,4577054082,1417675828238,20670598538],
[0x10e800a40ba024ba858187cf0,6779071370,0xd206d03b8382132b0,0xb203868511a8490,143362,29762422,209003769730,0xc710d222a610,6804856024568,5650796930,1821739418236,36526117250,7292051358572,124797390948,3558370454,5085250205019522,0x7408100cc22f085041ae3c,516345053682,24189186092,52617621796,89323498654,4573335932298,0x34c007c1301c170041f0bc0b07a0292217f1607067250908880,7530894210,0xe82a44d02387c,7535083634,55087389096492,9279549619236,79475778034,616078767058826,0x12d8002820018ec0be1380703d01902a98672c38a70998080,41445090],
[0xd90e69032191b02512a87f40,0x5d800d8d29624,0x3e801a0dc2885ee,9169449106,0x32808aa0028d001e9007080892ae09020,450,1953601060,5387602638,60381892754,0x15460032a00bf862c353303d70,6983792792,1314,132038,874803202,31748533655084,2784004587524,509348931727382,15102098,0x3978004f903067b8c450,866,0x56f000e1003e30039cd60b04346,0x93c003f100045810080822d402,0x49e001eb800c114f8c82862ae51e8,0x9f80041e0c308f02,0x420b6c0210d3030854c8,0xcc0783620085088134e7cb8,8287245341698,0x6c098a0c1608a998,20980322,0x24f00102c009c2428221a64,20980322,0xc890a088c1a],
[0x1892400608600720c0600105c2180740184428b6531d0b12d4be04,0x49e001048019a0186020083954d096,0xec009004b4b112,0x5088ec0008410c00e418080682e190a4c21817091a2603090c30454ce60a1632d7e2a6dc0,0x628548800de803862a2d9c,0x4e0ffc0027041b194,222308074,0x534601360126462,0x1384d40361b056ccf6,0x5a00200f0182418cccd72,0x49e001038005602468986e0f7a850286fd2b6a40,0x6d801702460a,37659927907920,796166,4226,6967812562226420,5103488364,506531812,25866291166,973883866,0x2a940005007600fc0b41f90e81425ae0728,0x1b077807a0d0454a,431627447043976,0x220518078704a0f3c,0x3a7c0017024372,2285019729772,0x1a15e01d02219724,531442141513806,41446802,0x13580018200120c8470260701c0708828280702500855e49170e44ad2c20c0,0x541e10010d0740cc8076,0x4f8051c7265ca],
[0x1209b806b0a586108cb1fa0,0x1aca40060c0340844229fd4,132139330,0x60e0188261a5c4,0x17580a81850cca9f6,4862035118706,0x18a000e0fa04c2d01c1cc011791b0498aeb4e20,98969075576,5773743336,950429912,189213734088,3625000972,58762756,4476294,4477186,0x7f2a121226bc,180691773364,5527648743468,58095416100,9940722946198,0x2b80629f0d09192,0x12980007a000903c81b201d81d9fd89851122402750,0xf0056091924,8287168924686,6403767360582034,0xa60798a1c18c674036d0,0x94c003f7003d00d00840f28,2886285408024,1858389708936,16817668,60829062,4206850],
[0x748340101a6a4,2014603758,5966417098,0x94c0003b000380a640681f01081900c327e41916ce41c8,360859214,62089591296146,4958841025094040,516777084085384,5913930310377714,0x4a0a0c3a44232274,932452436615980,0x1e700118c64a372,0x12980007600620b1d40240e8341e0a204b00a14d1991950c96,0x4b008b044106d92,0x129800076000b003033009054121a0a0b06838440081c160ac0451aab3c1633bae210,3894955282,0x3ac0017805205419c0936e817407d4,0x384014042a122932c,4412009424164,0xd00ec03a00c1ee008a809c8d16,4604273118610,0x22d00018c001a07c198058260b0b090383c142e0e838ce07c8d809eec098,0x1e5007070e48376,0x6e80ca809ca9ca,0x12880007e005601852040c04481d058481c13a03070f83602e028ee19126fdb274,0x49401d07261f2,0x3b024601106809ca6e2,0x3c0760420f0580c64185033008c0e73415861352d1e,0xcd0a6430f0230704440604108d9a,0x2580003807ce00d8f00f0360f04782a058220d0ca120904838085c043e0210e0e1c35110736d10537b846b83000,0x6228006c19c72a6790,8859495956],
[269561868,8859502084,2214876550,184702434,0xf8103861226ed0,7910999787206320,0x314c00360d09227e90,0x6298006c19c72c0670,738806804,201936396,738808836,184702278,184702338,0x3f4838a2903d8,0x706c0cb0905c8,0x71b00c2907b8,0x18c6001b0671cb11a8,738806804,201936396,738807812,184702022,184702338,0xfd20e28a44e4,0xc6f000d83424915e,7812558262650,0x18760029e9e9f139ca09ada00,0x17a00012000fc0029c015061092040,734482224188732,1278294068,1007761708,2109698,408043024014],
[2189439242,0x171c00e85e80ffa0029401ae88c6a51e60,0x1cd200328458e20,0x176c0004199400fc2845cde0,20950818616,120292960424,120292961432,481070217352,4098,3338747700,4354,1622052,165826702,1716490,0x5c2f0543003d03d8052c400e971c0d09375269b20,619217186074,0x2cb801adc00cc146878aa0,52440218,0x5950035b801cc14687ca20,4833955102,168054106,0x2c5a00670d15070880960,77343279496,14340,3718,3842,7999406060260,168053982,201892982010,0xb6a006b90024ff8241213b0,0x165400560141000e7002e05306224790,27172827338]],
[[0x167c005a0619003f8384a28750,0x60d002e98003802803112,0x68c1a001880ff6002840185068a212aa710,0xeb00620446fa,0x1129000ad00742f8250628b2c2d0,32298162492428,5636,0xed006844a06,0xed006845082,0xe5007da0719210ec,994,0xc40e1208845e,0xf1006204447a,0xb22001ed000a3007418b941c12ab4d8,0x3c401383107c4,49394239822,0xa7001a043112,0x880e2ad8011401d008088004f8008383e860a0f3f4c198,0x1d940014e0034061e0236cc888,1309427062,0xf5007432046f2,0x170045610023804b40020c004e51259c78d9868709e7d346c,236087526,4984433314418,0x56f00248187c00ff03164ad9a,0xc814a66004424802603ed002c07d00737096114918276a6044df00c9da00,3185780,1089004,3191396,797982,273754,0x1f9148382329a1c],
[0xcb00fa400e960052448641422a674,0x196018dc001fa00a489409227ec,0x65807fe00239000fd00524320a72c064,0x32c040100399801490c829cb11e,0xcb016660029225024915a,0xcb0100400c8b4001d400340fe40417069ce0d9aa00,153517272,239502536,0x5e068648e4b8,4456085908648,0xc2414c91198,739238857740,739238858244,150449976326,184702338,0x3e45609192c4e4,16110612830,0x81970086d17a,0x2bd801ecf6042ec1997600,2423278350,4842482826,0x27200b960000200ac803b8241c185c90,0x55a004c0a9300420611214670,0x1568025050a0070ca196650,0xa8100241c118230,0x2b5005a09f401840ca199210,0x2cc800e828470f8,0xab4017480378678e8,0x2ad005ce00e1047cd8,0x28c4009070488c8,0x2b5005d200e1048cb8,2819780738],
[0x38f00406008a04228a998,86352398788,2423279558,25872068738,0x54e00fa03a600d1c619c1ac6c,0x19ef00241c12e24,0x159802cd0078d940c106bce,0x2ba800e084a318aac8a,0x50541801200e02502ba00ffa27f0c2cccc1c91e00,58074757288,1663472792,239509640,94562368501820,41955218,811509161869100,39997177774628,417151873310,16110612826,0x13a8031f003c3afcc08c6a1d8f600,172961343306,0x6ca334ce350ee00,23012435859260,5891183788210740,5891184123755308,48247042,523994558222,0x53b8005e2510a,0x274801b0a006b940236a59d20,0x173e002464660ce0,0x173a003470464ca0,5908776259567432,3154297016],
[409155773063336,0xba10000e498,25572237570184,3196529425724,6393059393588,6393059393836,1598264848642,3194382332046,0xb9d000a310a,0xf01394005434001207f59407055350719a0,2586,173959186694,0xb99000b82d1a,0x17320030c0466a788a0,798058613914,0x5cc800d8180c6a7c820,2586,191139055878,0x175a0011c3a04d1a,0x175a0032c131aa0390,48245146,0xaebc004b04c6a666,182463642,0xb2c131aa1310,788574820,0xba10014300d1e,9933319562,0x17120024539c90231aa4290,0x2ed4000c11c1c226670,411904604385482,0x5d9800920a8a28630,0x16e2003e04115b2a210],
[0x5b8800e8488c6aacf8,0x5378004c01045112,0x13a400d7f0031a05482884ab1d8,0x2dc400060d0236ab8c8,0x5b8800041d08c6abcb8,0x158a002203098fc4,411629713893838,0x2dc40006043112,0x6b0272800a84800440c30b1ca1f02447cb27c,379468998780406,0x5d98009402772,0xd204f7800cc045042221308a2ca14f1e047cb464,0x5d980024120a06a72,0x2e3400142481468d9a,0x19409ca0050d003907208884256b265883169f24100600,567146976336,0xe56007c284b0a,0xd7c01b68009880042802b6036360b203210,0x6f4001b0038e00b300b06c61cf8,141786756456,141786764632,66685657416,3372513464,399537241256,24230637375896,45122627720,2820164882,871651819531060,21512601802,0x917808a1ae64,5638352014,427723413032346],
[0x3c78001bc0077400bfd2f1078553143df00,0x69600420f81610d2c,0x7f0784c0499504,9596494,1750625994,0x1702c7f2bb147d500,52972302,9674321034,0x1c7d001120390481c18fc10,0x6cd8018c064a01064778,57393700819304,0xe0f021870889d8,77427153096,7348592524565688,395288057796,51641872390,52973762,0x60470c19c1ac7c,172941143442,0x6046fc32a302c,19356791332,0x58504986328cce,0x702140c18708d9a,0x40801680e409023e45f10283353153b100,0xaae00480d00ca11bd4,23143948,38385700,3811078158,103968970,0xb600c0e1f52112957a500,0x194057a00283580022c624c60,142649892],
[35662542,11830053642,0x4240274801048010040071007502a81ea1e19ca3cb60,0x2b5c003a00858691320,10073277152,19335821876,1477524268,2109698,2499956494,2340434186,0x65ef0013052b3160c6aa8960,5113176200,4354,10337990964,4226,1620516,667790,845164938,0x3320800a297885831aab3b0,519213397230480,61027830125424,906574396,125841666,3725146924,1947843620,23718949134,18480263562,0x591c00482f102070231bae290,18368866,26945450576,0x5f5000680e0211088232630,0xd038461b8210],
[6847745666,30251118159080,0x86804b0800ea007019051458282dcae8d8,2796262281490,0x10d00961001d40be071438c42dcaecb8,63775994658372,5787782,0x636800ea05f039303c15cb102,0x82804b4800ea05f03860433c6010b733c3c,748764468,0x1ab7c001101890b821823e6c,598344265220644,0x216012c6003a817c0e18d0c3c15cb10e,0x941c461438081c360919a,0x7d800855e0065808c047fc0009001ec00ac02c02c05989027411f16a89fd3424b7d1674300,0x3e22121774100,0x216017220018446172e0,0x5320050ceca44aa0,0x3194007c284a0260,56634638,3402,0xdd00c2418714,0x31ac005e04813c2c,0x31ac00686813d24,56312885134,0xc610014cc1a710a,0xc63001ff16aa8860,0xc6d001b04813a2c,0x31b400686813b24,146104545038,0xc6f000482508a,0x632800f9e0da2b390],
[32998284737580,17382692,3871502222,64701493514,34292388512496,52971746,545629852336,7604785664680592,70877466954,0x6c8284a2f250,0x2df800b1401319068232630,0x1906003910a1b6210,128885223298,0x3204007c04286e0e8,0x3204005c3286e4d8,0x314400319e13a0715cef0c8,0xc51000c668f8ec8f4b8,1213859380,1213859628,223680797252,72904838,61139874194,0x18c50cfa20e7533e2c,0x644800df0a14224,0x314400318b0883c2aaf10e,0x321c00139e3060b19a,0x30802b00c4790003880041cc00ac02c1981d0360c4318ab5e9e980c53fd186eb00,0x86804710027048f003a80f600a0886274e0,0x1778015050c308a2f4a0,30073239860,403802504748,4354],
[405518,667914,0x237b80158822508a8b20,0x22170d8a0aa9ae0,116039695412,4226,3389603364,667790,7518310730,0x11bfc004b8822508ac960,0x38a4c2208ad920,8994356,528634114,3658039332,722395492494,3749859594,0x2ea836a38b2c3d0,0x46fd003c64365822c7b0,3174586569616,0xa901c90207022e770,975563326288,0x9209060c231330,106537116432,30073226020,142934,0xcc90016084f12,0x14c02c54005780ee2a020453338290,1667841623664,7518309234,0x2874007902bc025702804532b9230,5375022210,1410947409400],
[0x334400140605502,0x5900a19001ec0af01c94338c8f1d8,0x1540286c007b01d40538f0de19caf8c8,0xaa014360016e01e08309002,0x2a8050d800f205d80f96086fca8,0x1540286c007901cc053930de19cb106,4432875922,0x5500a1b001e4073014e44310b72c03c,1654,0xf870607192,0x5500a1b001b40990010599fc6a24224,0xaa01436003b80e602821a14282dcb10e,0x6c70d360919a,0x2a80250142801d602700800200066008412822118194069a69f9292adba207146717d1a68500,5101863814,5101865346,6923589053104,2525542546064,6572750,1880640394,65148044778544,23660144644,5786830,5787018,4080445980888,226788552,226922936,2776932520,153528472,0x33840028f18448ac88,15244307324,0xcf9001a4672],
[0x19be0024649ae6c,38384164,0x66e800ce3f0d48cce,1217555866,0x6420078800f20024200180c1d80e1d03d0389faf25529c25700,1482,8539494334136,18884194,7389718530806168,14340,143110,3970,8420044420332,273378,505837873286494,0xd0083606d7a,0x693002ed80023c406301117f824103370,0x79a00744013380241c107350,0x1a18b00481c115330,142622,142682,7249149563106512,6711684506,0x2e0144023aa2490,2462,2522,229819572418,406004209197584,1644446842,0x3d03103818a2aace8,0xde00b803112,0x71a80199c0698b1508b1c8],
[0x695800bc14d068ca,0xc150008440430536ab9a8,30140336580,49394239822,20136341778,0x5b94005140f90b0d051b3074,19335813060,0x829181206676,73035433714,0xd600c5400fd60033008d83160c3c0718451752042863084f6d1a,0x17c018a801de03d058100130520840880e81e4449109d05031213c9e20b00,0x8806070c4a9fb8,76816722825118120,55594260694936,0x5c2d06704cb1188,738806788,184701830,184701954,8938346139796708,0xf866070c4915e,3474641293690,0x1280d0e4e2837084cc79fa80,77343281544,14340,143110,3970,7999406060772,168054110,19474173306,0x231740050c009d8181c197d10,0xd9b0018601506119cf0,0xac39c02a0611dcd0],
[1506,877677850,0x190716031a9e470,91808608402,0x71b8004610048270741922a630,0x1ada003614d065ca,0x305c002090048278368b1f8,3895526340,750798414,4835520658,0x5b9c004fc0141f61a0c66eb9b8,484931866052,29009921014,73035433074,0x622006f5003b80ec062e0c6831901a161c2a2fc210c2fd327c,1927418655796,1644446842,0x4e0520c40e0704ab524,792209679730,0x30c0620846ad8a,0xc44003880487000881283b01a06c0a80c80b038792212959f044df27cdb80,992947248590744,13031722270,13031722330,0x7e28681c22c14,62271135039084,0x1c020c1501324264,0x380470308c070de,2071519334794,0x2e0020041bfe2868084cc7dd280,973884698,0x1938008a0c0066131a852d0],
[18369138,29731007894672,0x29402e063206d9a,0x28c033051a22450,17390660750,146239679818,0x5f03a8640c284aa178,498454784202,357895118567896,31186766158,67077058089234,0x11c80e1051926ec1a8,5785422,9933319554,0x2d00239808dab23c,3852730402422,14011090674,0xfc028440003801d01910103c00820866e19b0b14bd3464,601506212466,0xda033502c0b52cd8a,0x3f00a26004ff000b818808c0320441040e2596d96d008b12f280bb80,847567144,0x8e01b81c38208184ce898,378699018514,0x163218000500c42c48cb3c3c,120540267618,0x1f4200290321a120c2406c,945178822882,0x23080885a0274386b11e,0x700e2c28a0c6f18a,0x1a31d80021680cc07163e090a4bb8084466e81b180,1747741582],
[3728079858970,0x991801fd40021016a03984c6a5f28,621244080792,18368370,541780482492,963219889652,0xf0e339922c6c,0x6421053532ae64,0xa8020928c0e,0x313c0005805b80783120a14c8c9a,0x158400ef01404002a06e01f00c80f05100e162bfb40b254e84a580,0x2201c482928a966,0xc741a852802c1c082306a72,0x192036163d85cc4e85a280,259469261868,0xca801de00c5217024064,0x5f00a190001a03ec01901d038561605050d11e,0x77807190518918a,0x2980327001308004234001a006403201201901707cc2208c6c899d80,126635726,906776970,0x33004b800ee01010f0a89c30,0x4b8014b14620bc10,0x87002834460894f8,10809170280,459686076632,61850790978760,0xa50009c1241a050ae9b8,0x2bd80013200787873a08f1a8,62287528562,0x570329426ef888,90204818290],
[0x3141b1209bbf34,19829950550402,3265145815588,44396055662878,0xb197038a32b18a,0x144018a801c6033000700284d803f07e0c81c270320540680dc07f497f048308b12f6918a80,0xec0670026865f58,0x8052c51886748,0x5480d852866f38,30157496488,2096791741592,0x1c5a000501396060af188,1982169649538,0x8811c161c034,210781922,26668093850148,0xa601426003e8091002a07960870ce,0xc984418e2b18a,0x298031100381801f4088340f052022604582b81e07068fa5de0e32166bda87ec0,53601200283148,1090052,27075583167878,27075583168770,0x17a007da071921aec,11544162,0xc40e120886de,442005318813434,0x198c002be0013600305500c100b941c12a0ce8,0x1f8c00e98038104172,0x7860078401d68068c1061cc8,378249473957304,0x6080079807c2843f2],
[0x170b540230d04485498,153507208,0x52058c0740499f3c,2631418,0x1ae0210ec04a2b4c,0xe55001482441e,0x72a800486689a,0xaee002a900360d901c42ecb92,0x9e00c1400e900340ffc00c6802a0340740d80507c3e8010282ad69609198bc2a33c0,0xd2c014266401c2e06864834a8,0xcca03280189267c98,279308250636,8859496452,69827064198,35467326850,0xf90906c192a6e4,79869699738078,3494136314,0x2e8006034c032cf98bb2a6ec0,7700,8204,1090052,3462,4354,0xfae031a1ae4,15580808926,1644447482,0x63124001c403e4079418a2a8748,0x1ab000540104172,0x159f003de01940c1068f28,11546510,0xcb8005828c71ca],
[930240177148,0xb18032843f2,0xa611b0098611227cc,415868900,0xa501580440a26a76,0x192c0044800606326a92,0xc14003b807fa00254000c0dc1481b03607c00812805c008540870597c60423b2b24c0,2634882,77461527548,41955342,916993738436746,0x156c00500d802631e02db2b1c4,0x329e8018e3286d76,0x9805021d8187002,0x7700dc07c234068686e2c0511b2b60c0,0xa1e007fa00954008500440e8318623e44,0x140c004f00d5002587086,0x15a0132a0000404d00bc0160a41d403c15cb112,0xa700d1fc000a053fb0011a00f4014082050bc0160940870360507051d20bab52b1f60,0x33b0250cb00082306d72,0xd300f9e0c6ab5ee0,23698444332,4996183030305188,109332622,0x2ca0050f1488ea,0x2a18004280036008900f315818eb822f0,11857367076,109332622,0xcc8048280a0488ea,0x1f640053e004780796031586e6c03270,0x3388006320658a04650,126632906],
[0xbd00e5500166611285c10,8310109092456710,0x761800fc1227502,0x1c8e00210339fc3e0a2ac41d8,5650793074,0x29a007461c0a844e44b8,0xec7000a82e0490a,0x2c0800a7c009d00674456e6118,0x7638000e067502,0x7208008c0470b482c7b227c,0x18220031805805023805e150573a334,0xec7001c3828a2e6c,0x1f40c8042992af24,0x5790007e802c812c06404500a32236b086,0x182e001660030d189192,0x69005404902000f03fd00081f400040fc150486602c1c5c1f00c058050740468f190440a095925fc60ecbf4b9820,0x89048261a8c19d8,0x3f200881e1f0c61dc8,0x2f5000f640078c424a,0x15e011d40016001d0008f006f03ec01609406602e80c2dcc2728,0x383c16122a2998,0x2de000c0b06588c2f08,4124789728882,0xaa01406003780f200180580302d80a919702d42534,0x2e0f05848ab06c,0xee01209060c23124,0x550057300048803780fa03f01600c0c201302dcb116,0x3858006b00440cb2b192,0x154017028f0039400b00c7f20071fd002a00c0700701d4033d073a1e0a1e2c08f1940ad7cc3c020ca57db0670,0x4580358048119211cc,0x3b6c00240604472,0x193e002b80ca0270f86c874e],
[0x2f0012029038d200c0c4436cd92,0xb200b8400ef004c001e0012200ac022905c16022103209c0f0b60542a0e0081b60105c8d92f0c8e8,0x2a4026bc006d00204c049005821027805857297cc,0xe201601c0d20178440b7399c4,0x164015b40012600da038801a01601c0d201615ca6f6,0x3680482418308d4a,0x2c801e051e0029100009000b03470d06e0d170740a0701854061a0881808243c1c58e1c2405013008f1c1908715f6d198,377635786,0xbc04818c04e0506112a1d4,0x6c400dc00c346223cc,0x3a800190030a11225c4,2478743512690,0xb2014020035808d00ec1e408c0e0f0ecca72,0xb200b6c0040804a700358050785e0641381e110a40430f0dc186b14709d816182352c06021592f6d9a,0x16400b029100372802e0376002a800320002048b0d050b50141850a460ae09c0f0340e3e061e0a24661c2c34142404115c2c319cd37b0665e1000,0x1d4019833cc000c3411216330,52971402,0xb19001f8111982f0,0x6e01ff00541800f191329a6d0,4050676622,115363098,0x64001dc003731a1e270,0xa2b00120204d1e,0x2874000a044d5a,0x39b0008d84e5800d10541a0210,36526116494,113397514,0x2e0058800faa003485844a91d8,0x29003cc007830004e44288a1c8,207570895390,207530788890,0x15380044064f0004e94d06245d2b098],
[23087614052,30954784798,0x9be00221706d92,0x97e00394e21a1213542e2c,0x3f80ee4004c700190d91333064,0x4a01d680090a00178f808ecad1e,0x4e01df8009120009464c6cd9a,0x9c03bf001b0285000c1800bb6e27aa13b09dec0,0x61006c1f0c001414c660b8,0x6c5000180cc668a8,0x28127800a833867898,0x5d70019061068188,0x71403469b001a1e1a23c,0xb0ed8023a800502722c74,538,40703743788610,0x70801f0539002282948b8e,77996653046794,0x343ee00d4021009b3003fb682287738bd940,0x316014a5321478c0,0x3f00443e1b22714,0x119002c110a12a2c,52971810,0x2b60190680606b4e,0x2ddc005f400404286cca,0x2ed4003ac010e0afc7047539675c0,0x45403e18c1aa2c,0x5a8800bc02842,0xf241c2208b1e,0x4dc00c6306cca,0xc190008b0068460b11490b73987340,0x983865182139a32c0],
[0x102400460b8640c18fd50,0x3d900261e05053211d30,12836,3278,3338,15439510536,4537065814588,54219871732276,798978,0x65500c31c324,21770510,53152338314,0x479c00d7982020114e81e8,0x3316001ac00283c308889d8,496982628276424,184734227640,36509338446,60167311762,0xa6005198f86c8b188,0x17401219a532b23c,4949420043538,0xa3f14a532b32c,1252175033380,2204125298,0x2780194da63a1cacd9a,0xff001b03be013090e371f55490334a539b25c0,0x182003c14a5321b6540,2586,191139055046,383798682,0x6601b2031a205c,28038389639252],
[0x4b80360326122c6c,0xb403e18c1ae64,0xd1f0010e00980c2873c6cad1e,0x8403c2506d8a,0x1a460020c02c1c30907e2263b1e2040,0x1ea03b071444cc7cfe0,6102290322730604,3218,23677914318,0x15060013c242502d1a,0xa5f000a1e0a168c685c38,48246042,0xe900a208848cc18,0xa9300160f068483a2,0x16200f04c516253ba3c,0x432001862908832be74,25964690,0x50ec80018047c041e53c124,0x3aa400460c709098850461ccb11e,0xb500880302f0b94f18a,0x293800a02d0013401c0601028484ab8e0d0bcf081c20,507531338,0x82007f80de0a5e081708,0x5330008d400c34c2,0x5330005dc00bb03d00811423a74,0x1ee008818c1bc2c,0x3cc06c3c0c1bd24,0x28f800500d4004100e404423c3214cb04e,8479575511167370,0x51f000a0258005a0060181302fbc2c611a6f4899e0,2328666854,853315985368778],
[0x1ec1c2d895090920,6611379804,0x6398008180118a122c74,0xfd00318c1ae6c,0xc810001b005604c261e172b264,0x8a80310848d0e,1649438090,0x19020003a009090c1874121fc4447ba53b0,0x6010828c9085f2,0x6c780015012806028392043c2d3a8770,580929126,0xf7f00148254c2,0xea7001540fe1f06308a21d8,21889582114,0x20e002880d41644cc24b8,25820949390,125981074,0xe90018c033f166f86ce3f08,0x7c4800140a74c2,0x3a94005d037e1cb82aac74,2063220377890,0x4903a0683e2c4c122d24,0x29680010600508048708e824dd51046,0x38ec005207c1f839232984d192,0x521000c222004202282c1a342850a164bf4ef0b1c8,536628350185874,0x28f800a1290011048c20d0a1434248242dccb9a8,4732393008162506,0x9865294ccc088,0x3ce400360282dcac92,0x5290001fc00de00c07074142818532872b73b134,0x1cc2003e0e83480814260b490b73b46c],
[0xe80f0940309848876,0xbe02206863068f2,0x736800984a070e194c62305ccc083145f2d9a,0x994004194002c801aa001d4013071a3350a8f831b8bc24baca2db7d0764b7000,388199843797448,776392921358264,388199843824040,0xb0880c290798,388199843828104,638142980,159536006,159536130,33128333362404,48524557586782,0xb0880c2917a,0x531001e4ea34739cc0199200,0xa14341420814,4504904930828,1516673013284,1126492571654,1126226234114,0x2a4800f8418236df40317a00,68232244,73056462380,2370,264150994830,18264117258,0x9be00060c005644b0620f230,68230100,50938412,50938660,10498318],
[10498378,0xc9c0029ff05818684b8,0xbfc002e368d1ca99a8,271266,6734781783944,10498194,0x2c5000208f260c623b34,0xa9c0036261a3472c06c,0x1538002a6d0a3472c464,274082,0xc620104715a,0x14280048a52d5468e69f20592200,132139202,0xa9f0005a0161801c43861cb20,7520661014924000,0xde802aa80188110d3c,19335821364,672217388,12595458,545410830,549466378,0x805d0012eb001af60236a59920,120292910904,0xc74001c0204e4a8,2105954,0x18e800980c04f888,214479933442,7010489477447476,4354,1622052,0x6360009e2508e,3423090651402],
[0x18800508bdc00525f04282129a730,866,0xd600c04c988,14340,3718,3842,534799037156,168053982,42979192058,0x1a380013c1011f210,1644446842,0x3fb800616000e1b8041c12aace8,90206908690,0xe3fb8012e5001a61d86664ab1c8,257781991876,0x339000b8020494e,863116779073810,0xfbe000845ea000830f63e86cc188,0x1f7c0031100090d808dab23c,458,711678236923780,4833953270,585510184690,0x1f6c0066c0156400232994109e46da2411472d1a,0x1f5c0010c5802a8801e3830912cc8a74146c0706e00,292225864072,14340,798470,3970,3865487422692,965304413534,18264116602],
[0x60e0013dc184b428,3772549602,0x8bc14687188d1188,6640271738884,1660067935110,1660067935234,5882569997108452,6843508564734302,427822167535994,0x44ea260bcc2182a00,2423278222,4842482826,0x272003d1000ee0907060f68,0x1a080130f0c70851d8,0xcfc00a80810664c8,7186412563614082,0x32f0037070480a8,0x6820061048c98,0xcac00d707049888,86352398276,25234001862,23674253442,0x31d000c748541aa64,0xc6400518102106bce,0x18b800a31898728c8a,0x18b801ac9ec0415513893f500,0xaa9800960640c1030ec0,0x6ea001f028ce128c6e40,1375598723632,1856635064848,3330,126007528],
[193122520,14852,4230,4354,31645848,58504,7018018585148,292141742900,73056468524,73056468772,71807029390,1052938,0x2f6013fc00585790008cd400fa800d81527f92946717d0d25c0,0xd029a00c020025c0e120d6540,67625889694912,4552004213564480,569004811576256,85974923316,85974923564,4354,405134,667914,0x1a0329000b0acc5831aae20c0,121668690056,37761282,64776911156,146813058,3188275748,675295374,6501323146,0x1a032900130a5f60236abce60,10804],
[11052,3458,404238,667018,0x1a0329000182b3160c6ad018,86171784,143618,43563316,7483650,89087621668,25833742,6702649738,0x1a0329000582971c08c6ac0ae0,0x49145408c9aa0,126400564,126400812,31600898,54931086,185217290,0x3406520009028ad208c6ad0920,73035432782,142930,0x17b00a12002604c401ae801f50043029a0c53040450a992b6e0860,818381434263584,73056465348,64596318629398,0xd0905404c7112,0x5f402ac800988035d003ea005e028e68114af902683127d39390,6551794310,275714,0x1cd215011ab9730,109334786],
[3265054380344,54948098,602174658328,4354,9262141244,13644034,30250583037516,0x1b68001a0160302123c04,0x1b68001a078a3189086,0x101968000873408f09223c18904ab1102,0x2032d00010e6810e0892f783c125f2e8d8,0x17d009e5000fa800cc03c29c9582,0x17d009e5000fa8001c06284c3c29cae9b8,12594290,0x6da000581ba8368ec98,0x14065200018023220c236ef088,0x501948002206970231bbd3c,0x2e1c3bb0001582,0x122e1c3270004c0a704a2c3c3406c,0x50194800f40e1850115bc224,0xbe8051b0005025600d7400fa801780a39a043890a9a83062409f310e,0x1a3c5c292350cb19a,0x45f4028d8002829480102006e801f500620b1187d0468d349a425afd120c3308fd9473b00,2370,1614941547546,0x12600c5c000040447221297830,428976676,2370,1322010,0x1c40015208c6a6658,50378788,0xd3c00440a04f8e]],
[[12595210,0x217c0313001cb02c36a6f18,2370,1322010,0xbac016231a9d94,0x1d080008139581992382c,0x1d80cfc001384502c42,0x47720009bb7c1878084af9e,0x1b98004c062506664b0ca,0x762003109ab3090511b9571500,0xd7c017f2001e405840758,66591266120,0x13200d3801f40540cc624b8,33328234664,17870436598936,0xe8442869188,15596628028,3089645666,472524106796,9634721180964,5638352014,209448373658,0x31e00a16000db0054a007207ebec62043d4962fb00,413642,0xfa04a80498f3c,46287986,18279521434412,874278082,5278274952146974,24225775784058,0x4b5170fb966eb00,0x49ee000ca10dd4],
[0x630801f8111cc,636481433610020,459168648702990,26699536829642,0x13ca003730018ff89090da3172df00,0x34070ce128664c0,437324164,2106086,2107714,0x118400711aa128762c0,292225868952,2105698,36700240956,2340502836,4354,540708,18187055246,790794,0x18300a26004d1001f100548055e5053608a1f720,0xa2f04890821ee0,85974924844,4354,405518,667914,0x76042b000b9023242ab0da0,621210083292,116039695412,18886786,3389603364,700461198,557274132810,0xec08620035c890e042ab4be0],
[12332,3458,404622,667018,0x76043f000b118c38ab41c,13155892,3289346,20837908516,62379815054,14299402,0xec11ec00f2c015de023242ab8920,59293228,14823682,21377038,50999562,0x4f1003b0221800e2e408c90ab43f0,0x13e400e408a600140cc04,0x13e400e408a600330507506,0x13e400bc0c4530001582,0x62c0275801cbc0c8da007c200f4cc14238770,30073240468,572812,73056468868,12595302,492847640802,0x4f700390229800ff13c142396b0,0x7fe001f02600c04072,0x644027b801d8235801ca8009028d6047838c47e3a270,286161980073552,7518309106,0x9ee007608d60072a00740b821411b3b210,527870856282610],
[0x31e013840022046b001eb005b80a38a243c6872463172b8f8e8,9290612206139864,4226,52623854326,0x31e015c4002550001100430a4089002,0x63c02b88011a4007b4000b00d9831cb1acfc98,4354,131958,0x18f009e2004a090a003da00a501ca38a541509228ab1102,0x63c027880128242800f6802940728e2950de0a24517cc02c,533874,0x18f009e2007a08ba003fa00a501103070a5465122217308e,0x31e013c400f411ac007bc014a029490c2340970e7062b110a,0xc7804f1003d06ee003d400bb803a1d08b00431671c309454a422e9c119c447d9a64d00,796770,3512749466,0x1e402880c68b828,2146,5629911941262746,0x5001801e16031ab01c,2146,90335325672451482,0x281df00086031a3404,0x6d9618a06862,0x42e60149cb0014fec01b2f8e2c160911a,0x517300a4e5800a7f600d968b03131b9e63500,4833955102,168054106,0x8340317000028074d4221810,1305718304026,0xbd04b380002200561884a8e68,115363098],
[1478750803528,0x7c4002e02d1a,0x138e0017c3e70069884a9e28,30417175076,18264117454,12595466,0xd80fcda29d4,18264114534,557452407879106,0x61402754000090032492f9a3c650b09e,0xf6800312664914a,0x30e013a6000028019244d9848711c1f61100,18884066,0xd600c04d188,571908,3846,3970,534799037668,168054110,738742922618,0x355000248013c10101c30,0xd04000480241c109210,0x90d601207045cf8,2751484497188,687871125454,110062219538,0x1179800d8e0398b0a28a9b8,1927960768680,18155035079832,0xd816048187c4,750799182,22820696338],
[0x63f7000a781ce0e0e1ab06c,31909574886774,73035433714,0x7e60004fe06c41d091458c36a421c5978d1a,0xf7001b7801c5800bc05c18809064c9a90dca1c157480ef80,0x64110d1cb1188,638142468,159536006,159536130,521195339039972,0xc8220104915e,55012101362042,0x2788524dce81e780,9939361316432,2678,3530,12952180088,3402,0x74160906a158,2484840350152,2484840351672,57638763549096,571908,3846,3970,7999406060788,0xd1b0481b56c,0xd1b0481b5e4,2674,105280728458,0x209ca001a40cb9354681c195d30,0xdb2a004404119d10],
[6280543730785520,146810818,0xfc21012a64,10779643086,7791209930,0x43ce051a26450,116039681828,179402982734,1993003249810,0x22f30004bf008809ca0e0412aa9e8,305295098820,315682219598,1202754433170,0x18fdc0029201c1e1f4341926eb9a8,3904200871364,8302653113462,8082853010,0xcfa069a0140e045e8e09ce519cb274,516079772794,0x1d809834440e0704ab524,9141634930,0x401e1b844146ad8a,0x5fa0000c04b02a1b084225586c3666e84bd80,2586,0x2af000fa1a2604,265502,4967648650,0x156800762c0c6a0f0a0,2586,0xe3003e8683778,30140337444,7535085518],
[67649416594,0x45ee0030e40398b0a2879b8,1988,2382,38121516434,0x18fdc0024101ce0e0e1aa47c,31143339572,92384372524,1398,20981490,0x4eb800aac004f6062900c21099409232f0a1a,0x163400d8c00748024900560010052018427b22c2fc26050,459390656285996,459390656290596,1812621974,6735015719186,0x8bdc00106200e3d90536aa9d8,126388164,31598926,4192395079954,0x68b6007360047a0247706146ac198,9933319554,0x3d01e362408db323c,238402282870,32308733682,0x4f8800a6400cee011304f0060c2134811991637db464,52682057714,0x1518003e0123c32481468d8a,0xb2a006b20041c0115803907d0130510020c22ca920a260bf4889780,0x16e80012451502386c,0xa8243992ba24,6877519319182],
[3859156078874,0x31200986000420e00a8c00140dd01f228a1183870919280,54529306,0x384002c188b0a2a3778,0x680e07098d24,28602364225486,0x1fc000420068383112,0xaf20022fd0018420038398b0a28a9b8,436766660,109193550,53877818274066,0x5770031fa8004620070790e0e1ab07c,0xd01e0ea3234,48470895997740,3607881721206,111765628658,0x9b1001628009cc0c7835811021099186061970d1a,0x57b00351001ce0092c000c0f201e0d6044084f77260bf2988280,18264116810,4058226644744,21443299003074,0x12c80025034b8e823874,232412330540,1982186799140,18264115954,0x195009cd000234005605e14462b0ca,0xca804e6800c7c019ac01d016b4a40c319c287cc0,141350,2114,229856874036,0x25200082c10fac,437329956],
[589318254,4679588114764050,0xa04005fe000f601f2818cc184b825f0,1986,0x5b02c2c18e24,4833953806,0x8b00185046b112,0x22e000c040020401714062ab098c83d50,54494558693314,0x62e00162468008,5508,54631989260038,426812379266,0xbe40038c5d40ab04,6940119148163974,0x315000c4e69502,0xbd40038c2731c0873b8c630,18264115534,5335159058,0x5d8016530019c03e0341106c1e43048535034e8,0x642000a808480e,0x40800284029a7112,0x15ec00307000870071ba02665705138,0x6420017825386,0xc840019067502,0x61000468053c6cc3c38aa7988,0x171400440a046f2,0x5ca0025047c03e034110f06827018644d41f34,0x2890003a016098a2a6c,0x2ba80033e0019c05302f4018a68ccdb3c04,0xaea0012f8004e05302f4018a13336d086,0x33200aac801209f0072e0075c01ec053c01e03e03c0f0b8324650d050211351112],
[0x38cc802ab2004893a00458020e00ceb80130010120a607401e03e03c161468b0c31b65f91609b2fdaa69c0,1644447482,0x62c0c5c002e406d8088e28a2d9c,0x24e001ba034231aaf94,0x8b02f10014c0ed802c0b0dab1cc,0x133a003a395006d806231ab384,18264114930,0x16c80065c2081c2032804128d72,0xae600183800ae067805d4c72c231bab65c0,458,7951831536000680,1089548,8708,3462,4354,2073401826028,11544034,0x2e4800a600c046de,31190959866,0x4b4000fe800df01c2018b941c12a0738,0x348800ca80381040f2,0xccc00bd8068c1062498,75316865419594,149264402812,0x3035800c341121734,0xd6e00130246f2,0xf60104a1764,0x3100880240e2684e,412642706,0xdc80577003210021600b64003809800408e0440f03412ae3027223f4b0da0,411978,0x17d00e4581918f2c],
[411378,0x1b4029ec0218684e,8942138984954,0x3802d45c3eeb1c20,1644447482,0x304fb00007806e010628a9fcc,0x1d9e004404123c4,95842540827740662,0xcc80440a26a72,0x577002158016c802e81fe004794142384470b4aa0,64445500098,0xbc1604e6c19e8,101255556,20980454,20982082,0xc42003bc11c2e2c1da8,18264115150,771756306,0x69c02a680114c0074c01e602d03603c0f0a206a0606368d407dc,0x6843098242430874,0x2a0f05848aa46c,0x63b000082e04572,0x69c02b98010b40074c005e01602c0f40d80f03c2c81663868a535294e,0x1a700a8e0034216800e98000c06f02f03603c0f09e0512c2922831f7112,0x34e0151c006863200454009e800302a00300b0580900c5e06c0781e104026d7e04521657e30770,0xf5c001f0010411928dc4,6544534332271054,1787119037842,0xd3805730031b001fe0079c00681b80183413005c018b0e0f06e0e3091455c322f0,44293220288016,126424964,2106982],
[2107234,0xa8807d12346a55c8,0x7c01882e0434a,0x1a90099b000eb8030c0430010a83604c0f0d2048a046850a09d25728,4833951782,4833951842,0x698cb868c83167c,51696593705588,2493249511922,0x1a90099b000ec801c5f800a03604c0f0e60421cbc53749bc4,4833953506,0xea03673384cd1a,0x352015b40023401d18013b000207c0e1481d0e81d0244818541320441c083e0c41422d4a61574537e347c,18264115146,5489364307156932,0x1d0800440a04572,0x1ab0099900024400770120c1084aa72,0x6ac02664005a2000401a03501a0182103e0705a58182c4f2d9a,0x6ac00ca801d300234008d0046c00a18028d06c030083b00e16045098120a13010a80d0302060d00858529e081067614dee21fec800,0x356001d0518cca09e280,13223618058,0xd6800b20a3394c0b6080,940592066,0x20c4006ba0a324cc0dde80,4833955102,272649594,0x10280038e0075b0036c104060cc8,0x218c007060454b8,90925214212708776,0x2fa006e50014042866198,0x21840030e047088,0x86100110f0a1f3c],
[0x2164007870b22b34,0xd0aa000849ac6c,0x1670037680162c1122e64,0x214c00783854188c8e,40020581322010,0xb2801b6c00fffb92836c0f5080,0xec20038104b42,0xba0a324cc11ce80,0x883000d8161a122b24,4833955102,107562945914,0xb1400440800f6361f06201c90,7761266063412,7761266063660,4354,155340430,199241994,0x2ef0077f002b6142651e8,0x1e1c002601265cd8,0xf0a0030e0484c8,0x1ddc00f81c18690b8,0x777000430e0698a8,1940316514254,1675637010,0x61600ec2006e6282a04a2a7c,0xeee0078704a2d34,0x1dd4001415061b22c,498,46941922,0x627193c0a04108ad1a,0xc4c01d5400a7ef540a00856e173780,0x724002514800c40461832b0],
[0x10d78005c1506107090,0xdac01c9c00dc161a2470,0x6910016128050,1709465862704,7904452874768,696699128,7642468584,0x1702c04908ae0d8,0x5420c04888e4c8,4555095108,18370694,232272728322,0xa87a5cae888,29965454261052,0xc10500848382bc74,0x6320e0423e2c,0xf3c6a23f24,30822096203918,6489480987447562,0x69e0020f806e30005036d800b0d1ff27f10a15033f5651a280,0x10842a8007c0e0411994,0xd06001c5119b8c,2761802496036,0xe0a0681188f4e,0x605008541890ca,0xd5a003f140c582ee559c80,0x42f000dc16181c30,180843335696,0x759003e0446a078,9223459619048,0xec221988c4d8,224035129544],
[120922362040,3505327368360,124730666136,64727048950,51641872514,3372718668852,0xd0f010a23e2c,30880677668,319105298574,33075560485130,0xb53000460171800281b640024130ffdf3c043126b56598b80,0xde80253800420706040f48,0x26405ef0035030e041738,60199152936,33328236696,317316304008,165783612,21512602226,0xbe01818622c6c,5643513380,4032842702,2819779722,0x560170803fc801f5fd0a48499955183fc0,0x58a402153187f40,0x3236000e0cc63708,0x404c00440410fdc,39183263540,51641872386,855514393700,5595292535822,241336872138,0x2bb800d6e002e0b5d43c3485613993b40],
[30090219208,338184706,2069126090920,663132312,30244111555720,153018771516,353811180660,11279117868,178335524,2819779726,129187212490,0x4e01b18036c800482a04817fe90315539c3540,0x53e000901041b104,4564471114,0x713001184830410ad02,0x21180670f000a30b80890431e7340,0x1710aa002b80e041238c,0x11837d80071e1a584,0xfc1618a8188a76,25346767884618,0x2900713001f040b048429f70c0,0x3d07c1002c38106d02,0x73706f7e00771f0662a06fc0,0x861001c40fe060f18,0x1e140096030e041708,20058025826620,19339952626,0x3d8160c622a6c,14233480292,1410878350,266357706,0x20a000d038c8015018260d7b160e2c26664222b40],
[0xe828c933226ac0,7145726497019672,0xd05b0019845f08,28870512287196,0xb80c1606a92,0x62d8246622a6c,0xa2b0661ac64,1368935758,41053578,0x38c80150740705af2c0505523a32640,414205373834,0x3a88009c1841f18,0x1fcc00a1c1862708,0xc834881a85c,206154356,27385277548,9678515586,118647950,2786911743370,0x1778035070300061501c0983d6ca414b3242140,9626374446388,206154348,206154852,41053326,0xa8310104cca,0x5ce00fc1be400185407038e7c3f50a83298c98f20,0x4704882c443604108a1ee0,0x9d200010c43e2,0xece002e80c18a02630,0x1c1001592800c4046183210,0x132600118a6a1978,113258370],
[0x192c801526003503810724,5387602638,0x4df0000160031424f92,0x6a20018f0000040065d43a0212a1f28,0xf8168485f2,0x6030d7025088134c7c88,0xa051c5030582aa7c,113254754,0xaf2003be8009424472,0xaf2006ca00e360073029f392bc44,0x33f8000101c929086,0x3d10004800804887112,0x386c400990185601b7c000c0d92003c3c3140b01418e7362eea15065ff8a9a60,0x2642a8005100e0412f84,0xeea001c726c66,0x2e3c80500854188d72,0x67f001fc0ff07062c36ead960,0xa2e00010c4462,0x4e002e81962801c8,0xa2a001383ce4c0738,1410878274,421102493976,0xe196801382003c540e04076,16218351754,0x15ec00b7c01f2c009601827264334289d4,10802451714,0x28a01828222064,0x1d40f0a809ca84e,0x1d2c00783d030c22189082,0x50d340017805ba000a06c5001901c0961428682831c3818acbba066977e2c710,0x10b2001f404c24a03d4,0x77700134078704a05cc],
[0x71140741b19924,44891066353870,35443469714,0xec02db0007038e800f0b090680303e202010509992d2e250,0x280a0212b2e630,0xfc09fd0005401040ca,0x29df001a30419fcc,4733398086132164,32025161517558,2594416257650,0x35a0074403610071d0038100c0dc0df10a86272cbcb8,606975519956260,738802551246,0x760840986d92,0x66016d800381b0400783c1e160448441438143c744121944bb23c,0xd20241a01061f6,2959893106,0xf3c0019c066809c86e2,0x1ce8004c1438f0214340280683e1a0ac309d0d1e,0x70a18b81c50900c08ccad9a,0xd4801420066002a8010e001c0d3e0025a13c1614184888904623130a292812c534213a414dee29f0a800,0x36ac0070a0092654d8,180772040,0x2938000a0b86c8acb8,290289097421992,0x150c00041846d198,2065211440140,72346615300,516302860294,272127490,0x3c870541b2b4e4,46626167868766],
[317785440570746,0xa6e001ece22b4c0999200,0x26c000c600d74000f600050308624aa0,0x7ce001184c4a,0x176c0080080084c00e98033022c83ca20,10274200032,674253454,7097546,0x2a78007c22c871120,0x4a0302005b28004b86798e0,0x1b5b000b0304808a0,29537357130,0x362005d1800c50338684820,0x559000b0c4614e,3681170,0x3bc0c4462a17b0,0x33200660b4b00049c04f324790,4354,538668,30140348964,7535087310,528650,0x68195003505a0800fd11010612a66d0,0x163002ee4001184c96,0x2868007142dcad02,0x163002e4c004866b722a270,0xb180176e0024612b250,146813314,3121367518,338722646691218,0x3662000c6080e08c308cb0e8,7700],
[8204,8708,3462,3682562,0xfdc16221ae4,973883102,6848792314,0x195002e9c0028a738230c22ad2c,0x2b2000b02c9c000c020461b264,0x140c0030c142dcad0e,0x59400020596800b061c13ccd9a,0x390225a005400809ec003cc00dc8004b0043805dada690c7c205b4c0c8ea00,38747394264,0x79600220e118664c8,9678375454,1583706,69348731818008,60423577864,33026213063228,1510229526,205532050,0x4483e408992af24,0x16b4000408704d1e,6390361650646362,0xd28017560017077bf60adcc0d8b600,271655428,67916038,67917058,0x7f048394ca6b88,90642200009596,0x213400660ca321bf4,0x1d01828ce13306c],
[90642200015204,0x3a03042020ad1e,0xe85c328cad5a,0x8140048600ff505189c4c1988a00,7535085982,973883866,0x385000b1800b98007f800d61309088a170e0,0xad401e6c009740007807c284448a0,0x36b001c5c04b96,0x36b001c5c04d12,0xc41000f50069a00503c00da1e1729e7f0,4698735044,792741326,667404195876114,0x22580059800d04f50034a600dec0c38c273a0770,0x4d54002c0c122350,0x31c0074600310a123330,0x2cc01b830f0037600249200610846704226710,1482,0x11e00a86004c6009e0a12c4c,1010,0x8d005410033280263614c8c96,0x73c004ce00486c19cad02,0x2340150c0097c00b31b0672aa250,0x2340150c009940131b0672ab230,0x722090d065ce,5067010194,0x89000b025c8012d80298205c8b1e8,1309426682,0xa5a801348029020a0308b8c8,3076,2438],
[798722,0x7f0280c188e4,23735583326,1309426298,0x17600a86004d20027486c0c1af2c,1678298334194,0x41800c812a40024ae006388205c8c9e,0xe580095c0030486c19cad0a,0x433001d046100240981c2027c801d500052000680713d39717b008124d4073fb00,0x1480ff600120b10199ec,0x41b00088782c22e64,0x105c0022642208d1e,9914030263642,0x5207f4012d4016680116800d0798a1e02713077f100,0x2ffc00271682498724,9595598,811101002,0xf080a000503fd30c7e900,18369294,18369418,0x1d401aca0002e01588039811862768,0x308000e8008c4006b00d303062f58,128885222286,53737974986,0x4d80261801aa0a485928,0x1ac01083f900582383088998,0x1fd401903049088,0x388002c80170461a53c,2269135858,0x35800681da803a97830c1ac6c,546732230389796,0x3a8001f800ce6e190306c4e],
[0x1cc00540ef40061c1188d9a,0x95005841d802a0540de009a003480775f104811530d3c900,0x25f80048030046111d4,15105892940,23144452,14183054,34761930,0x208038700770061f904f28d7bd00,16236455794,0x78ca12213955b900,407915714,908610318,95577722058,0x302002bb006615064864a60,517147691552,8626137998,23673204042,0x28d800763324a7c960,0x70582c6ca7d920,0x28c80032503286818e0,0x65400560fcc998a0,567844,2766,2826,0xeb087086e28,659286188184,138521404552,3846,3970,320911916,6863908,3918],
[147117330314,0x572000c7001540f7a71462286b0,0xc71f05732a290,22571429138,5051089161466448,2793967627796,1007437470,75507994,87995223046,5786898,0xa02375c8b0c8,421967032,0xe72a15cab8a8,6114133982360,556742580844,2452529194084,72903958,22442462610,0x26030114fe572b024,1978505121054,0xd1af07cad9a,0x9b60074c01ce0049801d03ae0009c01be00880e1477b154ece636ad41856100,4029170694,4029172866,6854936685264,2456890178224,371739406,1344818058,0x2f600319006a815211c50,129286922800,867685233168,180780536],
[226922984,140914,3634441796,371739782,303582466,0xd20047926b098,14537766024,43665010,121975189108,88865354284,0x6901a3613324,243338333454,9596314,0xc4e0074401ce0077801d500052008d00981381483bd95f25529c53100,0x329c006e0904b0a,0x1201c7002c140028501633860cc8,0xba800bd400404052841cb8,0x46c01d7802b4058284634a8,86136749336,3490726338,4936804924,91406585703220,81642143946,76407746148,0xf010c908c9e,417492362,0x338081e003103a201bb803b0477001f0143aaf2020430c9141e31700,0x5ff8005191c01a0b86c81ca8,0x13a0032ac09265498,2267813093900,271656452,188996153606],
[566953276674,0xf2420b1b29ae4,7890104216766174,14766860026,0x81c009c036018b3e8ad31e70300,2955954958,2955955082,0x22a78005b80c5033865f28,0x30ce000cc063046718,0x198e005f02506466f08,74788324875868,32333908082,0x11034590830c1ac6c,48387175067748,2955955470,0x1200c0c4e0b0306d4a,0x97e0074403f10036d000580b81e0d812022c75f90b193131f2eb00,59067437548,205532170,0x130c00147180ebc0454c8f6,0x49f001038021269f2,0x64401c40140d80e050b0bd40b729f6e100,3626295448,3586,1895872828,155236916,536962,12369083428,1510231950,105918858,0x2c81468003cc002e8055d70231ab04f0,906573876],
[822130988,799106,22032142,38809994,0x164077f000da02b48231ab4430,0x710ba000213fc00140629490cab38210,0xb7e001e1503c286e06,0x2443d800ac6002a0786c9102,0x122164000c2a1800219fc4a05cae4d8,109331022,0xbbe0007834848f92,0xc21e4004f9000b058d8820822cce8a8,651194262,0x87100159c00e4898785cb102,0x52194005670038a3b8139673bc3c,0x1794000f07847602,0xe0415cc000b0685bb0d9c23e6c,0x1a215400042a48014504a48672c424,1510231154,0x1a21d4004ff000703811a70104114cd18a,0x5d01a1fe8014c0d45800f5000c1ae8000c02600f01451214ed95682084fca06a300,0x15cc00914498a966,0x2a0119080e0025800823069f2,0x15bc00f21111332169d00,0x608f80c518c09fa0,0x1f401e054050460df60,77343285416,4354,37048607880,2109058,974207796,2109698],
[95689489444,11037470990,971133322,0x194041b002c80efe0027c024bae0c8c6c174e0,0x982a0b188a41ca0,0x2a700130f0c70844c60,249150126140,249150126388,10498306,2181642788,8249560559694,1623208202,0x5200c18008b4016a02bd6502f064aa0,530965903412,530965903660,132741476738,264946200206,0xf6400a318a,0x2902bd002e100213006080ae88c6ad1120,142930,0x725800486c6002412394b0862e0bab4e08a0,818381434263648,2114500676,2034,0x739800d8c0048321e409cb102,0x3924002c3630012071c65294370f7d393b0,21023236,275718,31610242,0x39d215011ab9730,3330,123741510],
[722759938,58019447900,54948098,189466772940,5255554,3092269846,0x5878200e0c125083eb1102,0x5878200e28e25ba05ff4e8f8,0x2eb8001604c1b85582,0x185d30004581208a1484c3b8ae9d8,0x64d8372aecc8,109330802,0x5e30003e0542a60a56b6f0a8,0xa2a0b188af198,322984613835912,171980166,1653600187906,7449201492076,0x1c9200161b38009028a2870b9a891077cc424,104999794,0xe73001ae80130340890d386436af18a,0xca0210800a406868401d601961800d05f401583c640a40542a3e5148450abd5a12026a2fda262100,109331018,0xb6053a0030100178542702289cb0,98786361714,0xc34006a1ce38f38bc70,0x2f00060260821b250,6475135848776240,0x5402021e09102,0x6a8040c288e4f8,4555095108,906776726],
[0x5c0468309102,0x3840468308e8b8,0x840468308eca8,0xa8043e07602,0x3362c043e08f188,4961872264764,2350532149044,48358258178,0x8c8c909824264,0xc5c046830910e,0xe1308d1a8918a,0xf201f98016c0a5400c20c0034077c01ed0052e03f02a0b83202f00b44ad7b04830866b5691fa80,19335821364,672217388,2109698,545410830,549466378,0x290645002b381263f220,18883010,0x5d80b40f013834,0x2f40340f01392c,4354,12683980430,667914,0xb14016e02b6142647060,0x1b40130f0c7084f020,9036678848718,142930,0x137a001d9006c297004d01d07e0e73272e0977db83b0,0xba1411ab8790,7535086454,142866]],
[[0x76401b0624001e02680e83f0739592438f7d39330,5255814,275714,93767795022206672,3330,123740614,2850189570,32300964908636,109334786,150543667148,0x332800774003c44,2290,0x7c9800d83060015005200680305ae816ab1102,0x1f2600360c18005c013801a038a2a8e070b5f4e8c8,0x2ba8016c0041b85582,0x575002d816378d1e1b88e9a8,3522798611608,0xc2a78000b805aa0389064848f188,171980162,0xb320f023e74,41509991432236,0x41008628ac124,7342322,0x9b9000ec80360c38004c04b01d07e0e3850884d070724f110a,0x2b6800a406869401e2003e802903b200d8784033380d80207010a8783c11c0741f839dd942d6a283c0830bf499cd80,10772,568588,14724612,3078,4482,0xff162226e4,973883870],
[6848793082,0x4460059680030a700241ce08c308a0ce8,5124,3334,4226,0x7f0280c18ee4,73035432926,73035432954,0x554013fc0084c01c41807f0280c1873c,0x22a00edc012a80640c10d34,0xa85dc02c0c11f2c,140414,141786,0x77a00220420c9383822aad2,0x174040d001181cb007880102002603d200f1802dc02504607c078030160e7b236adf4a8b780,271655444,271656460,271664132,272126310,1443648770,0xfce0e5321ae90,0xb0e848221b670,500564523859536,1088502804,1088503820,1088504324,272126150,4701312514,0x3f7838b88c3c8,778046756406712,0x4c3a06388c7a8,1088502804],
[1088503308,1088503556,272125958,4701312514,0xfde0e2e234e4,41906181147998,83812096183674,0x77a00220420e74e9e9e6aa99e80,10497410,1241688072,10497410,1043410452,10497410,1043410948,5021901017350,4482,0x4bc6091b226fc,37761410,12485470060,4162,0xcc3140a089fe,0x58c0313e0886d92,0xf0531000608025012ce0a4222a1c30,5124,3334,4226,8683362815716,0xf0740863de,1309426682,0x2412180082c00fb00e0c01048f28,0x531c0060807c2849718,0xcc38c044284a708],
[0xe67001ad802101301d04e010b72aa5c,5393945708,0x8c0ae01504818195c4,495076766,273835674,0x43c8007bc00c3800340470318090730247f1306b50d12,0x12ac00e5803cc0113003de00ed805680fc0180d01502a1180900e06c1441cecbc08b7c2b3fc0,914649734,275714,0x3906900c0a84798,17617242628,275590,58873218,0x1e83a40302a276c,0x77a001e04d03109f0a84c2ba04,0x77a001e04d031093839c4b086,0x61004060327112,0x3bf000d01505405013c9f0a879bab7a40,15741186,8726533288,143618,2216976520,4226,1616692,79704322,521776676,4514418838,0xf0c00ca0125842dcb102,0xf0c00ca0125fe022aae119e0,0x3aa0009a800b819c8d02,0x1d700d7e40026600586819ca24960,2109318],
[109064450,3436781640856,143490,1616700,413954,521776684,369392433476,73806332989334,0xa043002e812122085aad102,0x20100502180174090979e0aab0e750,2109318,109334786,6741388560700,37900546,2181633836,1669409685060,4514418838,0x8140ca048e22085b4d102,0x20503281238bc8216d3a0630,6847745266,111963190648,6241403272,136334338,0x18fc001c20150d091a9874,0x25f000eb8031a005835142192c,75508746,460531091606,0x31f8003940107024b9a,0x56100347003170038a0015004a06a81c80641ec01145582026ad42e5c,0x12d80076c019300a18506472,0x2b1801a28018a801e2804d80f40a40a84dc01b806858ac3c6d54324c,0x33401480882dca676],
[0x5d8028304772,0xac600760b2c00c5c00e2804d80f407c0e80380a8320be027063474adf0d02,0x158c00ec1658018b801c5009b01e81381700501506410c0d09c184216d42b7c2c21c0,0x10f2002a580085e01706135743e44,526940984078486,0x43d80082401a2803700d00bc05242dcd102,0x390d2000c41200cfc01b700d03e13098520f1f95aaeb1fe0,0x3d500c220017500186819ca8f6,23675292026,0x158c0013c00f70063a006fc026c07a04e05c0240441d00480d0cfc5294eeb4f20,0x7e0562038014500582082306cf2,0x1d5c0028134a528acb5ea0,506533948,0x2ee00682c5219b4,11914030636,0x4a805a0e12fa4,438997142,45081467457938,0x3ae40003a00ff9e260216b82350,506533940,0x490008a0183219ac,1491152420,438997142,5609001362,0x4bb8007ea39e260c66c03290,0x2e1000e6c3282204670,109333322,0x2d804168007308b285c30,0xf0041a0c2210610,0x25c800384436ca44f8,299230384114690,0x1904001a600b0e38de0f1ec61d8],
[0x1f8078c003aa00bf80220a5c0236e64c8,2336764244004,146114515222,23220626,0x4837672aae8908,0x1904001b20070e4822868285b2e7c,5650794610,0xf50154c14cb3af2c,0xac2007e0b24001de0016810100a48a34221534244,32218565490,0x37003e30002900cc062902740524529068225755192,0x17025006214801f839200fb00c39800d81058037e014203b00a07c14687858120e41106c02e039e295a92aa083b57d2e750,0x5e011648018c801de800380ea02302dcb106,8831419219227026,0x885e011c7007c80318c801bb000e807480483a07301a8340b73306f0,0x1a07e10008498fdc,0xfc03b2001ed005c4027048119211d4,36509336306,0x102802b8322213c4,0xfe0243312acce,0x6d809c1c0c298f192,0x2b2801f839600fd0019400c06048824004dc802af01e8221581a0ac2c3b80c80540509072bac2453fd32610,0x1aa004c05e0882dca676,0x2bc02f028304772,0x1a80862007e0e5803f401090042200de805780f402c0d81100180f0740c4094043c0a3914adf2d0d8,0xe206ca38881b8,109331018,0x2f011007c04f0061785242ca8718,0x1cc03c062c52a8988,1881162098,0x6a011806a1ce38f3a3d4,826944807666],
[0x1ea02c6184810c325c4,0x1ec0dc062c52a99e,0x2740242c10e089f2,0x6a01f84001d0211002d6005a0520880862c3602330081831502301c3503718a9760c0e0b5f6d9a,0x6a03f90006e00fc06372009f20037800e818b0043806ec017402a0b0e0b030810a264110b0a2433e1bd0341b034261f07118099020dcce34dec31c9a800,2458,2901809333186,0x179004819ac00288045220370,3842,2154632,146104465980,4482,14203948,852947227524644,32325521358,1172555592074,0xc801ec00475000afc8240612a4650,906248734,56633370,0xb20239c000c7d0909550b82,0x1540f0900077c0051e82cc54ea8e8,6062438908446,4585457690,0x2a9001e017880038de14d0a24a52b0b8,1948850948196,61405153310,0x4f03770005c4003c4431848d92,0x4f03770005c40038cfd0f31542e3c,4786724210231622,104626418066,0x76f00043c60078f33214a53b064,14015285618],
[0x4d03c700047c00138ca60a060c6cd9a,0x9a078e003e03790018f80043aa0018262654811231b8fd540,0x4e0d50150a003c610681c8,0xde02c5a480038338688b8,0x13802201496003c610699a8,0x3062b8009110306b16,0x183154001184c92,0x1012180041e007b06722a3c,0x7c24e0124a00371c3322c74,0x286c004e0c43fa,0x57807147d90010a801c850c1ae24,0x7426601c340042e0064294c8c0e,0x3a1390090f0014a24186c9a,0x4826601a407280596801a700cb600f572877b91cf40,2370,0x5450017802046c1a,0x702003ac020b40045a00721e221289c50,0x50a00b370027b00241c10bc30,275524128526,47391461770,0xe0b500c3600730b0a2889e8,0x5c808871700110184690d8,0x39c06ed0028d0184894c8,70877463114,0x85b00242fa015440084150648b1a8,0x7086400714c48c6,372789650,0x602e003e401c21900373238d190a53ae7c,0x21e0022f480163604a3034,0x47402da80190481c1b12c,0x1619d00a760024404a3224,14015285490],
[0x786bc0285801e3390a2c3c12cd9a,0x17400f0d7804603a8038d0801a400110076b75240239e5393c540,0x10cc000d401e221213e4c0,2554778664,0xbb005544ae098,0x1c0c0014243414020a5a2,0xb300a8e160db4c3a3c,0x577800a402c46,21906880002,59593075113572,0x76801a05544d0ce,0x5480670d0286a6f18a,0x16380116080012805c03056f181446c81fe0,0xb34002a400d0487061738,55899598482,0x22002c08c0468308e098,453268806,57238020453890,0x105017b01811423a74,0x11002c018361ce70c2bc2c,0x8800b03683890223d24,0x1f001a033472cb0ce,0x580120e83061e5850b18a,0xc5d6000160070184c16fe1830412f489d20,0xfc0a11b514,0x2c80343512382c,0x56a800a402bc2,3082748464926,0x8100482d44b0ca,0xa0f001b20060382ba241446e91ba0,256156774,0x50f00298361c7064f2],
[0x390470b084e98ae0,0xea801851a2c6c,292473122404,32916725329166,0x75c010846d8a,0x22440046c032050d0b011fa2c04546e9c9a0,0x5606c12e04821e,94586459409178,0x2258005e014130443e674eb16,0x51003814a8c12,0x1658018d801a30066400940386c1c28f1edb4ca8860,0x10c05c10c6aac820,189012404454,5506601358658,0xe814f6010b824a21d8,688021866018,0x90e001a81883239d0c824b8,86002574,125981074,0x8da000d40335a1307064e5f08,495080770,0xe80a378f8328aac74,1737422317986,0x7e0420d42b5132d24,0xb4c00ace00361c23e0e67510c6,0x420bc01839e3c6d44d192,0xb2c00449b000c8096021a2478e5164bf65d42c630,0x36400048003da006c341c0302dc88c6,0x420d868a41acc9192,0x12c700318880063c008412210d0a047261c424485b50b9e8,18368034,0x6404a0180e062f6],
[0x1922001502c70c2,0xb79001780209703436848cc54ec1a8,0x1474008b0361c7064f2,7613710209042568,0x2cd003110034200568024c01c0a1a1c738b011bb6d3333c,0x3c060c28aa06c,0x88004034121c1a1c4,826944807282,0x7c01024290541858630a8f2,0x3600828c11ac5618c5778382a552d9a,0x1b600d3802889801ba00d0802540342006100db806c24242a1c53319f188acb28b6df435c14800,0x6b180054159400f832654c8,0xb1100088326acb8,9678374626,3865877991832,16146086412,258171059716,64542765062,507008514,0x3fa1e021b2b4e4,405564766,303973313914,0xbd800533f8ad3006c700,565002274836,0x6c1b50c28e0c,0x5d700388c18e24,828445337606,868451928834,0x64c003e488db7d00cbb00,0x63f8003880063800f83265ce,0xb3b00088326b4a,0x56080073704ad3816b500],
[0x14f2000be00bf2000c28272873d0,0x6020019e0177801f0a10d3b0,6348580509042064,0x168a00110a11f370,0x22cfc0009a1a0750,0x59f800042b224730,30140348708,14692110,143626,0x5988007d0b0c21c2a66b0,7692,8196,2182,3682562,549229501156,973883102,6848792314,0x2c7c000473829088aacd8,354,66747240564,5102445164,126108642,0x58580044586c96,0x2c34003c08acad92,0x57580048ac473b2ae34,0xc2400250e043e2,0x2c1c0034e161b264,0x5748001c348ecad0e,0x2c14001810ac8d9a,0x4da8003aa0069a00f9047171c1e3b281c7900,0xc5e003e0c9972c,9140022564],
[77470919966,0xe78a684ad5a,0xfe878ad38866f00,7535085982,973883866,0xe1400b91000d61309088a0f58,0x10ec0066a007c28444c8,0xc7e0014528679b8,0x18fc00442848ca8,0x318800a486821089998,0x63d0004104a088,1746690974,0xc6e0028a86c92,0x319800e8972ac2c,0xc8600010221af24,0x317800c10086c8c9e,0x31a8000804286d0a,0xb5000b4800fef31c3189b38925100,2285005642,0xf8ad30e64d00,16917228174,371739402,0x75002ebc003ac16187c50,0x9c0c0c060f2,0x1780663001a30418bc10,36526116938,0x35500343812889e8,0x35d001d064694d8,0x6b200120904a0c8,0x2598002ce009416287042,0x2598002a60088d84a9a8,56917256386],
[7366815190268296,309288050284,0x68582a0a19fc4,760773372062,29009922586,0x1d7e001f5002a2006109eb0d12168cb0c4e,0xd8c00380c146ad9a,0x2688003ea001ef002a6004b499d422142b0f22500,676200021285936,86068238864,62386503928,216921310440,0x32780065428691d8,62386510024,8626137994,7769164389544,4261281899108,128885222662,8626138514,51608623918644,16656216620,0xc43e0ca3324,27852819726,3376055086490,0x15a00f8c0077c01d8075400d3400340fa27cc73d39c40300,0xd680739200145286348e0,0x5108003a02813a2c,0x510800686813b24,36620627726,0x5118006c2510a,0x42d800be80721801fc51a153d0,0x96032412e1b0],
[2146,134538,41901387272,139618,0xa2b0008c1413c34,0xa2d000180bd2c,447113444900,3672930,91303451102957962,0x288c0016b31a34470,0x518800324136050,8626139010,0x145e00163241b8210,0x5178005c3286e4f8,2546,998635202969954,0x210400281b5000a1c6a1b0b15cef0c8,0x4208005036a001438f8ec8f4b8,56632642,1685751340,1213859620,55920200726,848327042,0xa06d40028608f7c1cd53be2c,3307595130978,0x210c00281b5000e02188742aaf10e,0x28ec0008c90518a,0x4eb0190a0074a013100f814e005163001660030e3000e0940ca8aed1730cff479de80,0x29c0b0f0007e06b22194,0x10060007c400688112238c,16162891140,0x20f40032e0396003c042869f6],
[0x189032e00d86a62,0x10a60007ac007e238a9ad07dd880,0x168a001fc0912124a0718,0xc7e001b8041042488,0x1ae8004c0182a0618f3c,3490726466,301128068140,3445673307428,53223840320670,417492362,0x2a8800f817e0083400dec00580e0d7ac3c7286525480cf80,2478065214922,68355688091008,51623560828,681716833528372,7424949987948,22404993788708,1857453337358,32487533386,0x98aa001fc858480858c5768,0x171500041046758,0xc0f002506466f48,34089632051522,28171139983784,96152866082,0x66d81c3288ad88,133188136572,496569369145460,8524461612644,0xf138246c87f6,62287530266,0xfe80010229f406024c72ed4a],
[0xd3805bc00c1005740314801f80c6964a80c12352c84b980,0x18d801bbc00140c5a081f78,0x33280022c00e10e066ce8,40911672408,0xde20028446d848,46308719782072,9381324844200,172135583894,17383846274,134261914684,475058021744180,30880677676,0xc0879682c264,438290649358,89190330762,0x79808fa005b2002405d8020b00674011ac00e300560282b03fbfc8288866b5691aa80,18882914,55884987436,21525249316,9678376846,10745966858,0x137800f61426370a0,3338,0x67030e060f08,27275522,0x148600b406121422a74,4565576812,1893347108,478152050,0x66400ac044912c28d0a,0x55803580ac05aac50a11930,0xc5002c241c193d10],
[0x8ea001258010cc04,0xcce00125800e03386,0x1e20155a000a1a03582,0x27580c46d000247200e7686d12142b8690,0x1b0120a82e04072,0x1f602094004510018d001b03c134d0cc808a77e3a250,0x487c149092ba630,7535086322,0x82500114400634006c0382c4361a3cb0ecf8,38713492428,1213861956,2485421174,0xd0106189002,0x1d2020c400451000cf003f00d81a047b060229ef4f0a8,23657991238,214909875586,0x6c10908823e7c,457542061950050,0xcec451b402c,1461942141220,0xac088040847f2,0x1e60209c00441000df004100c80619619a3061a3ab310a,0x3cc0473002d7000e026401138034201906004d802e0f030483206403122a6655f0b7195f6998380,0x2930071c442885748,128885222282,0xb808e0e6487728,15275724900,128885222550,8626138498,0xb8439a22e34,26805702603372,2066158302244],
[396280491342,26913295754,0xd24000e02e40105801fd0027200280c361a8270227ce062ca23a83bc0,0x22f80015a008b00382a15caf018,2105698,0x31f8004fa00d850921a64,2105954,0x63f0009fc0178246c1a,0x5038008720030e005a01205e752be04,0x6680e11940028100585096,0x36c02a54001106915cd102,0x2c32c0088290010ac001094801d02e06400819e46ad3aa7740,0x1e020b0f0009f01a824a2d94,0x13c2b4c00391af8c,0x209c0064154800f010a1b3c4,0x10c275005e0928d66,0x4f1800746b00404286df2,0x37c0117c001dd002503fe08d53ab7440,1994,0x9860052c0863ea8,14724108,11780,3078,4482,549229504236,73173903204,3679202,879791886584314,0x59a8003d01580f81953829088a0728,0x6430013e015010862498,0x367001cc058d81283c88,0xe6009024cca],
[268482252660,0x702000b180c904572,0x4c22816389a124,0x9c600090249f2,68195879002,0x6801908002c05d802070067c012e00c4801a1f0041d098692a208e57d2c2a40,0x73014f83265ca8,0x920688326b498,2028025868,2028027396,507006982,507008514,0x7be0f1a234e4,518173527390,148280741242,0x40b3f8ad32c6540,587246604,506539524,126635014,4482,0x7c6091b226e4,973883870,0x982c0a069fa,0x3c320c000d81ce0a42229fcc,0x5026002612172a3c4,7346938779814262,81090126039666,0xdac001760034a0025c018900560141d80a1e4f1cacb4fa0,5773743256,0x5b4800060e86888,180691773916,1913203508],
[0x5b48006c19a302c,180691777316,757643653270,39728817148306,0x714002980ff9879d4e098a0,0x2dac0004586c92,0xab100072079d4a0f020,1443436324,3188360846,121938153618,0xe2289730a790,0xfee0011118b370,2146,0x12a60014a0028148d00840748,43507941176,16817668,60829062,4206850,0x748340101a6dc,721571358548,1913204012,36286500,53747928526,54337376658,0x1414002060050dc0032c01103f001071881c324fc102404516ce41e8,0x57a8000100e00402103d4,1443436844,19378839492,133190142582,2249109650,0x64100032c01c807025606c3302c09fa141a0229ed28988,0x44c00154004586376],
[7215932533962,0x60803430007b80041a1001320066801a0581680583c0f031120bc234d54b24c,384831357741046,976439442180594,0x5048008720019a00dc13071280900407809071b3224950d92,0x2fc01a1800e819a0033e0026c00cd002c0d012094048020e390226c53688d3bc2e290,0xf80e2071f05732504,0x3039b800e20582c15cd106,73100980626,0x7320ccc60076a006a0040d06d038e0314ad430610,0x2320009a00e0e1618dcc,0x72c00e80417293c4,0x1740907048648cce,828674450,0x1b200cb4000602bc00a1f7002d28024b8019e00581605280e03034121c3100c7e314ff4c9b8,0xd6801c81dc05857295cc,0x1f200219e1229dc4,23673202034,0x55f8006503f02088a4a,0x36c01958000c061800d180073003cc00b02405829022050e1d8022b4314aac3434,0x568028421f31fc4,765288096754038,0x6300e1c214289f2,0x1ba020b4003f2008fc0068801500c161a2460c042416147008ce7e284b5f6d9a,0x1ba0355001ce00d480514003018a009f802ec035200970020c014dd0678490180e0a18490f0782418a24144854046309314dee39aa6800,0x680e1208865a,0x32d8015a400b0d0341944c09f980,681698029224970,0x2f1c0049a284884e0b7780,0x4e2006d5800d6d000844818a285cc,109331442,0x59d0005600d980156d00238050308864e],
[640707522,0x2c500158c00cb61a0482672520df280,0x3be0017c80117a0008a422283250,0x373000c8800f8801f0a10d230,0x24c00220c99f210,48245778,0x5908004046800750c08a81e8,7518306674,0x33300010a000a68398e08c89c8,3368261542490,0x17f800afe0067011e06aca8,585123406,5375021202,0x5ae002bf8018c1722e7c,0x16c800b020010e1c8d02,0x2d90015fc00d2c72302c,29030892658,0x2cf0004af2001378296088c9e,0x16b800af600109a19cad0a,0x6ee004a90022f005610034964ba334b1ce0f6080,0x8db00010740701085ca,0x44686134e11de80,0x13f40002fc00088c308a0738,0x1fec0042e001301843ca8,0xb34011c2000c63067998,0x23840071e048488,0x5a6008dd000e241283c,0x46e800618672ad34,79481510558199042,0x8d1001d0c21b024,0x8d300158130c308cc9e,0x8cd001b43086d0a],
[0x1738010b001da800faf466c59d0175380,0x2e011a1944c41d280,0x610006880011841f28,7786220302,7786220426,0xbc047d800fa04989dc,4934615827555636,4917017347958828,116152878066,0x11180125e0c306b1e,0x4420072e190306c4a,0x2d1800432006d770916244b044c880,146121244212,1191264044,4354,729960462,667914,0x36100223f80056614680c920,197660851252,4354,1621540,4867510414,1716490,0x9b8042a4002f8c38a153d0,872604808,6559972668,77528154164,6559973676,143746,405646,1166168458,0x98027bb8009c1d6f042122e4d0],
[0xc530018c1310b0,77528153644,143746,405518,1166168458,0x98027f68005f89094234410,0x7fe8006686d878,27078846636264,7518309238,7518309618,0x2f9c003c738221810ae4b8,0x18160014da1608f1a8,0x183f7800b07860028238e121a19caf898,0xc1796001a061ce39608afc88,0xc1fb400583c5000c31490305c9106,310186635650,0x183f6800b078a0018628e308572c02c,0x1e7800c80c3465824264,0x183f6800d07860028228a09e0215cd10e,36872505037194,0xc39d803460041501ab90026a00d1898002c800284c2822cf7dec11a0472df8799f80,0x61b02f2400098c1a1cc,0xae002c800070098c1a384,0xfe1000d0cb88966,0x70901eb800263069f2,0x1ff80102c00405001f11a42b08e7d9a80,120292959384,388024559401096,1191264060,4358,4482,3719204],
[1716494,404763018,0x1858003a03dcc002703df042821281d90,3170974772,4354,1621540,4867510414,1716490,0x1d01c64007d8061700173418c38a972d0,1669669109292,417417277826,833760931854,3330747806090,0x1d0045200305800b3808c90ab4430,54539650,812290455167480,0xe2c61c08e5e8,7518306418,68290601347272,7518309106,0xcc1d0c58508eca8,0x1c7a000616ac000c02292121629caf898,0x3024000304c3a345088fc88,0x71d800185ad000307296121629cb106,369746093568386,0x71d800185ad00050529234858a72c02c,0x5fd00121c18688824264,0x1c76000a16ac00141c62304f1629cb10e,528070592197002,0x1888003a02b1002aa0089803e400a14f400bc03828c54bdf7031624afe207b40,0x49800750311e060f18,0x4708009a071e041708],
[0x231001a81c781113c,241334070388,1669967404,16131370788,28128087198,417492362,0x16b801ee801570017500170801fe70a285199a42236c0,0x38714913227640,0x8664001703404195dc,0x66fc003404117d4,98762546416262092,0xa042c0c1ac64,8867768462366,62331521363274,0x100e000f5c000d017ec628a2e32332c0,54539650,0xc8e1c08e1a8,5008402212248,885233609096,0x45a00785ad001102a0d1b1422bc3c,0x45a00785ad001102a0386c508b102,0x22d003c2d6800881304e1b1422be2c,7518307186,197871570958,0x45a00785ad001100e061346c508b10a,0x333006c400740566004bc0116801e13f004de002201c1d2c8616186ba66d40,2737222040,948980998,948981122,249951268916,13049148012,288849769508],
[7790947662,3557181910410,0x3ff002b3002aa002ea00215002c7c1481bf46859a32828c0,0x2f7003f800990005028ca,0xbdc00fe04030022f00667003d0272233c4c,0x3f80099000502672,0xc2f9003f8045a0039a400a41478aed1096,0x2f9003881c22f0017e4000c110282dcb102,0x50b54002871038ff4008cc016a40044018120b2872b73aa65c0,0xc58703800e6900244891430ab708,1309426682,0x24040c7c0053b000bc07507041af94,0x4604420033580190a532318c,7518307314,0x3f8800c1083c004cd6005c440a14cacf6,0x650dc0a86306df2,0x5ee007f008e4005ef000303c2ab11490b73ab61c0,1755603535536,7518307662,5375021202,0xcb7000e434330c281c50,879859748,0x9c04e0c466e,438997138,0x1c211010aae2168,126633486,1191874706,0x50b800f10f818632b02738,0x14160009ab051aa59a8,7518307186,0x2f7003f80476002908006202a1983361a84e5c88,33037561769084],
[7518308338,0x740f8709422d2c,6301042,0xf0bdc00fe054a0054401c3590009e00984490650e3e757096,0x65e800382789192,0x82f5003f814d8018af80235004bc00fb80190140783c28e08516313552d61cb5f6b1ba0,3184132,3334,4226,2165863190756,3368261543006,1309426810,0x1b4800a2e003f80e478103cc,0x237400328061867285c4,0x8bc0049019030444e,0xe0280b03048ca,0x58e001680a6400b58023d0049c0139800982c0c3307b438c4238ab4b88e0,290331501823450,0x3508015c0208a1c6eb9860,3023791744094,0x6a50023070606c92,0x48359001a8400d80c01067f18,1348242578,0xa93c0048a4222a1dc,0x5c4801f0a125d4,95115297237452,5375017374,159531546,0x3f300201801218035080089f96088c12,0x1f980100c0090c01644004c0d4062f45011c68a6baf2d0,0x132800d620010e1c8d02,0x265001abc00d2c7207cc],
[1512777468490,0x2ef0032815f801650048e00a1a006894098361c0e02b851c5f0d06,0x7f50007a6001300e08d01214618cad92,0x176801940afc00b3802450050d00344e04c190101405b42e14717d30210,352398120333752,7518306506,0x26100671000705c54040830a3718,0x488c1cf0aa3988,7518306418,0x40409002270052b000ac00703d02848f2940fd4,47655793260,7518308338,0x2903e1c2508cce,90705330613817746,0x1778000202a10029600084460008444011f9002c4e04c0a0438e08d84c042aad478466fdb26c,848551859997258,0xbbc000101508016b0048600a1a00589c098361c11a83478c51c5f2d0e,0x3fc8003b700123e0a298a0210e0e83826a528c11d0d9a,0x2f9007d40004058c027e00b6801c6015f0089801c900130a09c54260612031e3831410b0709c51c2da14dee419ac800,1885356482,11679581090,0x18400456003f0d4819b980,104810547212,418794048004,26202638598,104698514434,0x117800f5a8b6df61b3480,0x51b0004c0610e0c,0xa68003c0a11004,92112691230428294,0x29e000f0285002,0x1e88004e400e7b1136df41baf80],
[759003890530,0x19ac0028ee04d4a1dad80,0x6be00db400c0a003d8800a82840cc8,0x6f4001b000968007e200706041cb8,42438391976,0x34e8008f02847c98,30165739656,0x34d800b60612b3c,382754958,0x7b10016d06162,0x697001ea011622e64,29051164576910,0xd3600096112ad9a,0x3ed002e3006b400604a200035007f78830a154e1f2180,0x8500f440027200319d1cd1481fa080,0x7c9003e0b4a219f80,29703999605450,0x6be0067f000d7e00390ac80768,0x13203318010340026012624d8,322282488008,0x1f34009c18484b8,0x1f2c00a1c186a0a8,0x5e4000a0586a998,487619321970,0xf44002f20058509ac3c,0xf9a00642a061ad34,338184514,0xa8282223064,0x3e8800910128c8e,0xfa2005060988d9a,0xfbc00b9400998016f0038934005ac00faae483433f0271080,0x1be8002680020cf1c8278f80]],
[[0x109c000600854a298e80,0x365002a3c005840ca,0x6f402e9006b401b7c007505860f68,0x1320151801fbc009852861758,52924152264,4986885407160,561602650354,9294749547137176,75646452646579336,0x433000e050a1a83c,25872068738,0x4310029722c6c,689892372004,0x866004106c6bce,0x42b0008e816c8c8a,0xfac00b9c00b30800620c801d6bcc31c622d48bdfc0,0x197c003840100020040e1120bff40,3505536446996,6170460098213388,300133157845028,0xafa003458704e,0x57d0002809218918a,0xa970021403cb000a7800082c7c472bb9e7c40,23143316,0x344800885c1c181248c,0x4c34d800641f0a12584,47725690776038,8732819578186338,0x57b001fe25531f7940,230697154,15436164708,471354446],
[12080803018,32779338946332,1669145999924,44930190402,7135345275747940,692497584206,981941793162,0x4a64006f6000a60028642bc6010bb2073c0,0x113c00a14286d808,6214797419035260,5777010048052,3716495294508,337138050,1683964326030,0xb61a1428b18a,0x5d600dad008500b58037e00903e80232001dc00183ac906f1eba26fc0,0x69d0012e0706041f28,0xf9a007b030e042718,0x8660055052842f08,15049794908,81642144754,0xa207808a22c6c,15570322146,1234201614,4032842826,0xbbc01c3005872a0022401f0e9610490266755242ac0,7909918101498432,5786318,210783626,0x169b000bc0eb05865738,0x1f96001700f06465f28,0xc3100310541846718],
[14051355016,7283204161154172,3878701641332,152774927730,41245670519844,0xb13c1986d4e,43367165322,0x2b8800e5c0015803c24190509f5cc243464bca523c0,1344818438,10203459978,0x73463c04b2256240,4758693866444252,71743609837524,490176392300,18189151618,8459021454,2564976010,0x16b007040160710046c002b8012061a00836bd83354ea0f60,37757282,0x1ea800223002580604672,0xf54001118011161bc44,0x12d003c816285006,4715879878786,0xcd020021c03d3000a180010d8360487df4ea9de0,0x346800d2b81c181308c,0x2634d800b202a0613184,8496373034020070,9294318824802,0x446007c954aadca0,7923081159394914,0x6b02b05b4200690,0x6938006d03501096281c70],
[189012403814,928619197698,0x7b05f0509308610,0x5a0800483a05ca24f8,2083012706,0xb206e045aa3958,0x519b4003c28004816018101d4,3184076,1089476,25820949390,6471971218,0xb540026a0059c0135800a18015c05199f84043c041130fdc,2762792341492,0x998009c883c1c2b2c6c,0x640184a0daad24,0x30b8001cc00bc0d0180c649086,0x1310053c2e64b192,0x50b3c00135a010e0165007040120850045c001780341c1e1c912247147553fd41dbfdac7b0,14230382066,0x980f81cc15ca8c6,73100980626,0x665700120fa400184429108c1ca0ad32e730,0x69b0011f016107d4,0xf9a007e8163604a09cc,0x10cc00d701503318bc4,0x58d20040c90694e,8861674578,0x342012201630070c01a0810045c00578024740307c1065062bcb0270,2559996266064,0x388800d9e0003405840ca,0x26970005e03a3921fcc,0x7e58001e02e1f0a1a1c4],
[0x30c400d20142848f6,0x647601e0326a72,0x16d8004c40054400408022e0008c00504808187c2d077920d045f0c4c8,1880641538,6387629868456,0x653001610dc4,0x27f800e8284476,22099799747986,0x69c01f402e200e18014112008b8002b000c0a1f0141c982417286bbb234,0xda0460a48621fc4,0x51023014186876,294697120065778,0x22402ca009bc008b8002b000c1a0ac108431616e02021c175c0304baf6d9a,0x171800fd0062c02ea01a9008900b70057807040160850045c01fb0063148fc7e34a3810a363728c58129a22134dec498f1800,3679714,3523531144,14727684,3846,3970,0xec81c134e4,86003038,86003066,0x6f380013989045428,0xc3e071c88e2,622394528829832,103753042948,25938260870,25938260994,94485475240920292,107056771422,1690087108986,0x113d3484cc09d580],
[0x12a001cf000a84001a1e189290,77343281544,14340,3718,3842,8420044420324,168054110,219056074106,0x16d400c35200198c00138607043cc8,0x6c400e9580056a00442845cb8,3482,0x385c002180c689918,0x9fc0079300061146ab488,36530309454,344674808082,0x26b007c0832001a7a019851a306c,36530308850,0x267000e017300053a000923003045c85143082172d1e,0xe0500030e26d8a,0x25900081c02de000a940047c004572c617030216e0cc180,417490894,12953087562,0xd860966e19be80,0xa0400cca00013400120907061708,0x2b5004a7800d1e002c71c1913c,0x18e00a518005a6001c2411934,6324391155673164,0xce807261dc6002c241c1ac64,0x1bb00f1500070904bce,0x57e0004104d8a,0x18d003140c1212001bd007fa38dc1190e1cb680,7032476674050274],
[0xc7a00368363891188,151604228,37901190,37901314,517050754319588,1546809282910,386710802810,0x63d0004f680c338831ad80,0x1d1e00120204d188,8003671570436,4001835921158,2000917892994,0x1d0e001cb071c1b4e4,0x7448000a044d5e,0x74380028b404d7a,0x39b0008a090008c20009eb81c189c10,0x1c500d6e00224800687862f78,0x388024140060200442846ce8,535962,0x35b800d70716c8148,0xd5b0005c1cd0684a,0x6b30010300685850013e200f368b1a8,49415211214,421984219410,0x7e803c3f8800b0a019851a2e7c,0x22a007520018451ab134,0xc580187808db322c,62287529462,49415210610,0x6c1000f700b85770031ac009650050c27ccc91f0d1a,0x1b04003b403990aee001cc02e201a5bd1111ee349680,43361791562],
[0x17580130c66a519480,4839197454,9674321290,0x1790034a8007ea00e41207063f28,0x3780b63001e1800f061064718,0x2e40747003cf80361c7064f08,20430526404,52973766,848327042,0x1d5009861e00670c19c1ac64,0xef8067a00a6ac6cce,0x1898014c5088328d8a,0x2c70008d800e68030b05e600c9d968114184e548880,32365906422,0x65d00144988a72,0x659001d945b4d07d0580,10496098,0x856003f00c04d9a,0x4a40040c005a0d031a99230,0x8a400ca123210,0x2f70018846aa8f8,0x2cd00447800dc80488c6aace8,0xbe400503192,0x6a9000a480062f3001742884ab1c8,0xbe400f0846ab8b8,0xb3c0111a0037e01d08c6abca8,0x6268005407098fc4,3393211598,0xe0804a045192,0x4155a0088b001b7601d109ab274,0xc1fe003468430222184,48244854],
[7612680690,0x6401b804940341200e6760025a403e0ca2ee36020a31174d9a,0x50938061c01430019006e012500d0b800c30020402d201f0eb2129804795c225940,39124469858,0x48a00b0204d9a,0x5ca0048a0086031a11c70,0xeb00ca127250,0xc3400503192,0x2ff200330b00262c5422c610,0xdbd000381c26bca,0xee2000a4700430536ab9e8,60247607748,3393211470,0xeb804a045192,0xe0bcec002e88074426ac1a8,1439051597976,0x14ec0060500350b0a28cc88,330,0xa2e70023900688411432218c,192979396,481592109302,7612680562,0xf8051c00e7e00290a80086180087300d0d006a06a33ea1b232f2d9a,0x3e014700282004847c035c801498803b400cb001e4036401a806a0522749415263c264ec0,1143491274,0x27300620c9066728,0x4c0020c9067718,6679865480,0x1ba2001be3922b3c,30451319851250,0x375c00310638a2e6c,0x35b800d4161b264],
[13095693582,0xe4a001adc005c44286d4a,0x3208280103007c28e0058c00f01500c0200383c806b80a8807e075e9011a113284940,319047034,0x3b049e00d0300091c00de048846a0cc8,0x401d9e00298041041cb8,0x54400db4001b025012634a8,0x9110001a0442843f2,0x2d0060200ec138442865488,1669961084,503907428,139618,0x37940032046889a,0x22027100030c013f80152cc4ab96,38708735122,0xbc0441010020a00e82c23a0032c006e02fd002f0186003b806c80c300780c6a4c900830b65caa22c0,64901668300746,0x98599b2a61c0,1644447482,0x12c1400015007c6418a2a8708,0x3cb000b4090706172,0x10eec002ccb223d4,1644447354,0x8d640003600960e28a25c4,0xf5400881207063f2,0xbc70035489f2,0x138801638018b4001ec032e00780e044968b0108c6eacea0,0xeb100010a2618e,7777945327259538,0x1038011829f000b48006860068f4844af96,0x2f80651000cc06da002d3000617829219cb112,0x14c05102800e8353e0053400cc06b600185a6000c0f029188c4f50b1d60],
[1422,1514,0xa360014e803e818619504,0x307c0035394888e,0x1040c4802163888ea,0x43400a22001488039da0a23b822f0,349786181668,98,6987999370,0x9c400318800a8c015b80860c328b83270,71315334,11297519106,0x16fe0017066f8328a04610,0x2d8042a004201c28003c299844c1778,0x70980008a0c3962a41e8,16125018738,0xce900130410644c8,11780,3046,143746,0x5fa800641477808584,0x1c4e0004a5206f86,0xe29000d2869602,0x3764001e0c91e907365ba26c,0xcfe0007800a6001c9005603e0041305732324,0xd039d80051e00d0e0994c6cb96,0xd013680019e00794011c07044846b182,0x410160c20500260f08b8062401292001e00c40077801980c10070d2012100a8243c14121e020209b5cfe6b2fdae730,0x92801216001638424a,0xca00fa801282af00292005e032180018230270e2187309dc,0x2cb00683800318c18bd4,0x76019e4000d00b1c0040c01301601827026050672a52c],
[85762322280708,0x1d806790003402c900101004c058060a406c15cb116,0x687a280019c00cb29182,0x1d80381e20040c00383c729b00114d000d03c03c0025c0011fe00980b00c0f81fb097011657e30630,618748023748,0xe6600345869ce,0xe660009018c7182,0xc8405001380c5400ecc015300ac010f1683904512f0c9d8,0x5e02821c08814a,0x6060027e00441f8120b40d4138a73178c,0x18403298005602f3002302f500120bc05e17297c4,0x880086001d7006605e00413c0e1cc676,0x1d8067b0004402b9001090064048160bc0e240e1ca6f2,0x1d80281de00169000440700d009680372008c120bf00183380519a0130f1b0240b051d01c023d21c304d7db47c,0x2cd00368030421223cc,4574109069584324,1143490162,0xe16001a740021025078688a72,0x3d00303bc008880320b0898017700140340076801a80cf001cc031401d8070e82c3c061a8041045440898eed8a,0x7a0060778011100641611300c7802aa002a02806804ac025a009700d4067800e6018a004c02430830f05231c160e2c230cc8082519114dee5180b800,348166054426,0x32600c6028006c5261a963ac34,5771903514,0x6ae001cbc007e091393ae24,0x18c012400a6f000686306c1e,0xc200ce0031d0009a8030fc800f808ecad1a,0x1ac01cc01f4081200402004dc0097e8013880102005e50662db97c240,154940245110,3438929798386,0x733001b40a0b625418a0c0,1090785672,3762358908],
[112084488308,322395349100,266703315556,5109877022,73605717195270554,0x958022b001a6000cc00cf00fee19894c66660,0x729001c6832866f6,0x365001eb801cd228b8a772,0x39980031b438e19895066da0,0xa0360022d0004841ac6c,0xf2010bbc003e18c1ae24,0x21100031f0c228c0e,0xa0620021b00062c186c9a,0x140dc010c05e40397400a4b00252803e21a09df267460,4833955102,168054106,0x63500040ff0008940075c15082728,0x46a00ba500381800907042f18,0x44940036a0079801207046c88,0x3208002c1260192400339922c7c,0x160a500c6200298c1ae74,0x4f0146db0015824a302c,0x15806a3001840ca1b124,0x18b4001e0928c8e,0xc9e000b05880f4807086c00283c15cad1a,0x3ac002ca001505a80ca03e40291d0086801a60039806180d3804701ffb808a789526f160,0x355000838010300082306a72,0x33008001d00e121582cc4a6f8e0,0xb5d000ae100682005811863f38,0x6ae0023340033c01106863084728,0x7ee00a3d0021601903044f18,0x582fc00d48001088588b188],
[0xb06880197001a09061b07c,29030892154,0x1a300568022e7003a2e2322c,1309426298,0x75401c60143801ac28b88cce,0x5380066c00e2dcad0a,0x22601930084c009a80232009100683a401c80f20086d00c700a9c02e80f4b4c1a22539dd10,0x1b2800abc001d00e0e1624511329def0,580930534,0xe8b000f058275c2,0xe23000941820a160a0874,66675828898,0xcd7000dc0c8b86420924,0xcbf0011c0658f06718c876,0x12c80155803234007901954e4d142,0x259002a50067f400dd6002a094085121c2fd9af4b1f8,0x259002a30011fd0037c80058142632110582add0b9e8,18368674,7425227784950,0x1998000580ac7142,0x94a0037f800c818308c143918954ec1a8,0x1c5000640282dca366,0x30fc0012e800282dcb142,0x1bfc00282001c900121c241460879088b74327c,8787761540,0x3078008e0e32866f6,0x5f4004d0d1c306772,0x39408e128f0d0e,0x12c80153801a08011300c72000d0160e2c486664a1cadced4a,0x6d8008bb8020e00a31a00ff8037880b845c0226010700a980418038806380a700120398466484e2224c4dc2db7c957e0c00,721856811400,14340],
[3682054,3970,0xec81c134e4,6059144015198,45116050810,0x82280013a207045418,0x42a0304dcd1188,152205642244,38051410822,38051410946,0xcee3454042b44e4,586046158188894,586046157533562,0x27440024f2824dcc01f080,0xd0200340850638e,0x75c00741c30658a,0x4f1800638210b350036d80,1169858903112,118047276,118047524,18886926,18886986,0x5530004b803fb003d10289a13c,18886802,0x82e800328822123b2c,0x411c0016478348e234464,274082,0x654020e384b15a,0x103900023156307d97205e180,0x5368009b806ed800f4261c920,77343281544,14340],
[3718,3842,8762823914724,168054110,77322153338,0x16480038c00a540013c1010d390,0x16260006203c9004c3e1b215370,146297327002,0xe7300043e0036061a26530,2688825288,26311149496,194,0xe18187087998,2242,3676575965820,22498322036,2150,2658,7110073591564766,0x2014004ad0018a26a92,0x3f1002014006720057c014bba6b8041c12eacd8,84231425539731730,0x47ca0067fb001494e00298782884cb1b8,0x380c003330109cc,197576959268,809605017878,0x3d04002f2001c0e27182,0x7ba0033ce4001171007d84d011b3074,4833953270,31190959858,0x72a80060c01ccd400c4f40063413730a31458f0d1e,0xf8400275000c88033f002e600671418e44370d8a],
[0x3e10009d40032200cfc009b80045484cdee85c36c073d80,0x982a0b188ae1a,0x25d801e84831b88e21bb80,0x502004524000e17060f08,0x2a48005be002c71c1913c,0x37a80000a001c2411934,2691711474,0x1c4a00290485422a64,0xe2300070904bce,0xe1f00070904d8a,0xacc002aa0025e801af30a6f0bcd024b380,0x882a0b188b1188,1980319748,495080326,495080450,0x7d0109070ac4e4,299428024193374,74857014530426,0x4fd0916148c39ab80,0x224a001f00c04d188,18850612034052,2356326436614,2356326436738,0x223a001cb071c1b4e4,0x223e001f00c04d5e,0x223a001f00c04d7a,0x73600110ff0002768341c187cd0,0x40395400440410bcb0,0x3ef0001880110a11b290,3170961196,7712708595140,90736453582],
[347720564879634,0x21e90010c8034e9003d41e0aeea9f8,249150112708,0xd002cc048ce,964223840530,0x367f002ea0151c0056600090077838386ab9b8,682912408446,0xb0d018684a7f2,0x87c003b400034018c08c66cc488,4564608714,0x38e00987808db3234,0x3b803a028115c4,328575510134,176580362,0x1750081c00ccc4004aa8011402c139c9a20a378f2d1a,0x1a1400ba8042200ce40166028c0144036132276090dcee3c8e80,46288458,0x42084112038981d4,0xa0a82c622b86c,88321825585636,46287602,294229405386,0xd6504996e598780,0x5e40226a000ca10dd4,0x14c0e8d001f8111cc,0x4c01a3800d871c193c4,0x3480130f86c8cce,0x6500261c8832ad8a,0x30280074c008900fb1217026cc5c8180,189783870874,0x2cd00160800d818683778,0x586000e07098d24],
[99501419329120974,0x67c014940043192,0x1576007620033200d47c00ec10a28a9b8,0x76200161800887c4,379567877198,0x4cd001f7004a045192,0x6af400ed4009920027c401ce0e0e1ab07c,6218841584153140,0x2c100158289b32c,379567876086,777354897148274,0xf62002e90030e00266200c9b8016804213340491bf2d9a,0x20f8015e800d7005d2002a804ec03370026e005a0109ebc3922c2fd2658c0,1796,795942,2385317463362,0x454c003ec1c103470,1314,10133992496,1318,1346,1578244,957798696998,442509378,0xff0140438b8,52101796648,5156,1390,23038209830162,0x274008190014b400674c0c619514,8082462028,13628448804],
[6674416945262,0x29c800c608eb112,0x878009300206c002f50005600a927d430998312c82590,7114081090,0x390d8592302750,1986,0x5d02c2c18e24,109332494,0xa9a0050469112,0x42300207400461002f804fc1c0631098c03cb0,141954,0xd0c860504ac6,48884903554,0x686722c139b0c630,0x6f802dd6002b0098c000a07c170b822730d210,836178819567234,0x553000408841454352c79e8,0xac063c00ed00479c000c1182214bb527cd8,534278,534914,209859336,2239827292,285249076,2137388,7249930020,0x68e8005085016,47725683036562,0x72a00abc00f0c006bc0153c00ccff5091c664ca96,0x3794002d01af002c34015100ff00b8030020e1412c2e0bb51112,0x2413002965806bc02a0c64005a0312003825b800ae00a5806ff00e295018040102612aa354189b2fdaa6040,2462,2522],
[0xda0507063c2,0x13884f8000080c42a2d8c,0x1d0585000f1841b1c4,0x6642ae8009888372cd76,0x6c41402a26de2,0x279005405dc0061a0096c004f1c1b08c6eade20,565149094267018,0xe2051a00e50,208775945608,2182,274690,442073339794668,1343296868,109331966,1644447482,0x2168010460030d0028e002901bcc2e0273ae0728,0x618022a005a0d047ca,0x638814680788,0x1c460005401041093c,0x31b0015c0940498f34,0x69001a81224112172c,0x8f180007024572,970736174558,412642450,0x10bc0064806c40260de80002015b0098c00b500c1009900a1015a023e002175e0c1e12d974b0960,240281546,0x210118011c40a1181cc,89404375965668,5391730,0x35029c4170684a,0x2cd8015941265bac7f0,1644447482],
[0x4b5b000a6401c82e0628a9fcc,8816984271692740,0x140d001a38a28976,0x49c80130f86c89f2,0xaac002f60030d0052c027e0023f741a0cdbad330,0x822005860062e00290004c007d805c0182281a328a7307cc,0xde9000a400d6000ba009d016203ec02e00c1140d858a72a524,0x1bd2001480dc803110052c03ec02e00c1140b089cb116,0x2ad000bd80058800c20051400ba0089070e2b182,0x40b002c4e600d836e00008058c01480dd80162002c80092e02cc07e80540181f81ec64127fe30690,292533932996,0x280e5406198a9ce,483235598201218,0x19061a00370112800a50068401b04201c39609144bc32610,0xa12346a51b8,962,562642830822,4833956034,0x5f90033c1cd1a957c,0xde9000b405ec00a5400fd807c1d0aa02826087315d4,0xe343c1e043166c,156325929458,0x6f48005a04bb002ae01f601f0742b81e8719bce6f6,0xa80ac18c684a71a,0x8830000500b1802d017700740690027c0294d008b00702c160706c2302e0e1358a0f38cafe346c,0x1b300243003160150906348c7f6,442433169906,0x20f800c500d980641b7000140011003660057805e8053804a809d00170051282443009630c03011eed8a,0x12c801c700314036601906dc000500b08031006a017f0057805e8053804a80b7012e03482408408d8728108c020e14a308e3630537b96761400,0xcc4003a030678a098f80,9433810586321934,0x3b70039f0660a],
[0x1998006480c3394c0b0c80,0x35e80013a030678a0d8b80,4581656506114,0x44400b99000b2092a64,0x232007ee007cc8004631c28b0e,0x3fc007d6800a040206d8a,0x4a50012f003d1000734005db003984c08203210,0x1b48007a4002c200261e0634f8,0x1b3e003d2016a8035e0654e8,0x38b007b1800a85e06a158,0x26e003d4c0008608506a92,0x1ad0038b00366009a3001498608508acb8,0x137001e9e00147384f92,0x4352001387007a7800e2d862c8b198,27145601828,0x3ecc003a0d04176,0x137001ece000c2907182,0x286cc00e1401e9a00042e60c11422e6c,623048159618,0x375800514186c9e,0x36a00706006ac001b400137000e12e58506d8a,0xda801c1801ab0006d002b2004a800a5801d222ca0a084a58383dbc0,0xc81c19e2847b40,0x1c44002f071e06ace,1417693978,0xcc6002444005ff0034c2338a0728,0x9e0006140030e043c98,0x26b4005f200e34265c88,1417691378,0x7e4800251070a122aa74,0xfd100134121c1ab6c,0xfd1000e2412d24],
[0x7e7800e14186c9e,0x3f3c0038904d8a,0x7dc0001009b4015b0054803590035f0404d8a7385d540,0xc81c19e29074c0,0xe2801c9c0014389061f18,0x100fe9000080c10e082708,0xb9400c3401c7811b3c,335020049266,0x332002980861422a6c,0x2fb80033600384381ac64,0x66c0038904c4e,672296074,0x2fd80177002440061400d78206109233113040,0x2c0a2ce2986fc0,0x1bc01ce40018701063728,0x14c0ffb001101043f18,0xb806bc007e044f08,848327042,0xc8401e8181ac74,4505760130,0xc7c01e8181b064,0x327005c0c50608cce,0x319002de50608d8a,0x1b840002c800438062200d2f90e085613192ac0,26319924348,15251123764,516748848940,120943424100,1893887246,129187212618,0x65c00e8400d580035801f78000900286007c1f9c321a113284740,0x8758001a058608386],
[0x439c00110040863e2,0x3f1d0618a82750,0xb1001185e00049c04f303330,343945090,0x20c900306c00378720a072c,1951536676,0x8708006440f00832af96,9169449106,0x614003a980033cc6b023cb86470,113258370,0x830c00b990001e05503209872c,506533412,0x4740079e8001e06c41a6f96,180640977042,0x17d003a1007a5800b402179898b062c1f58,0xa13c781c062a51c8,0x2802827000f0183830854b8,2422445737458,0x2d4013b5003e3810b04c7c98,343941474,0x21ee0013601899044,113254754,0x21f20019c0626472,0xc5dc00e74002e20014200cf400d41410ba7d43c44,0x194400a383c154b096,0x28b000ce6001c0468309112,0x1611220037c004cdc01381a5002814003d003856c0289d0067a00041c4c34a699cf008cb5f6a9ca0,0x5d086c800610309b2dcc,0x420dda0003c038389af84,0x5c518800340c26acf6,0x168cce000e0d1108d72,0x568009c02ea002fc801c83f50c386282f4adb60],
[0x112f000440a1419004,0x44ac0011028506466,0x1fe6002a1627602,0xfed001fc7c146a80650,98,17869887783942,0x1fee001101c27602,0x276003fcc00730f1f051ac05e8,0xcc8006e90006605b0735500758,0x3c20920007c0183327026072,0x21ce0012184840889ac2138,0x340ad80078d0006844020c828072,0xa900003f0007063ac060c129ae2718,9007757972232584,0x230800a8243992973c,29056062978,37435608277100,0x86400a8785b2a124,0x2f980042e0072c7189096,0x45c000b48004e8077802a2000608c04304182907182,0xd02de0066e00cc0cc803e4001a001e801c2d6009d00e7004388048805440110314f848252d79e0e6977e2c710,0x18a007ba007ce800c6071e040ca,0x15b003b9003320099d001540f18214203cc,0x1fa2001881c78105c4,0xcd8003a071e0444e,0x64e001206c311e0864a,0x1fc006d80345006e066401ee024900644013a01de00e20122019f00760fd90a4c5622dae250,0x5814594b2e630,0x8f001f6c002b07e060ca,0x55400554400a7b001d0cc8429fcc,0x10468004404121c4,0x921800f426976],
[0x3dd8035e069f2,0x3d8024a800cd803d401d90013a01de00cf800040df9011a29f0bcb8,0x2a4c001c3920dd4,0x48b0009890620fcc,36526114290,0x46600f0a08889ce,0x5f002de0022c005340018138030a58909182,0x19c803703160030fc8023d00485bc0089001c4023c025340161c18e6c2a010ac702422c4bdb26c,0x6ad000fd801b700681e40020d6012601a3006c1f0283866218743464,0xd8120471e08a72,0xf2003a4019c8037033e00f10136802e2009900f1006f009300a6802c2c29780e1bf0a28b08b0d8a,0x79001d200c6806b4037033e00f100048007a0090b88026403c401bc024c023a00d48644c547320c58534a55f0537b98719c00,633802691752222,19806271213946,0x22640068905c184cc19a080,0x9ae007060468a,0x89f001709c334ce1b1e80,53167402520,118047268,29511886,18886922,0x1324001e80675003d411028a252c,18886802,0x5d7800248498318afce,0x2e4c002489224cb11a,0xb8900188b4482a1588b21d9580,4833955102,738742922618,0x1a4c00719000b1a00364104060ce8,0x1e680061400146800f4261cd8,0x6a40031a0097400a818454c8,0x5e48005021c12aacb8],
[485159518351634,0x2dc40024db0036e3003e343188b198,5381310666,0x2c200125f00370da2e7c,7535084146,0x9c180177e002f0423418b306c,4833953270,43807434354,0x5e60075400420c018098003b00a536c0cde2ad1a,0x716005e6007740044800098003d00e92d2610cf1ae1f0580,0x7c070b04cb11e,68184782836090,0x19a0a6604cc218280,5479970786790686,56312884602,0x7b180018f0009b400d7e09060778,0x9e000ac40030e0424e8,0x24800a0400a81845cd8,1610,0x5f8800830141070c,223590026532,1793959421902,0x870027d00383112,0x4342002b300621c009d400f60898aaa7c,0x6820027b001408704aad34,55897506290,0x61ab000b6600290c90a3064,0xc7800f1006e04572,0x54200211a0063c0069800c33ccf1acd1a,0x1b1001548008d0031e0035401d2949011c68a6b89d8c0,0xf0304b28a7840,0x140060e800640709060f08],
[0xa92002eb80048241c185dc,0x4890029f001c2411934,124667314674,0x59e00290485422a64,0x168800b090706b1e,0x2d100070904bca,0x94a0036a004680140801ae235849c30bd440,0x6828b061331a73c0,0x172030b40032843718,8861010698,0x9805e700190481c18fdc,0x2e02e5001f8111d4,317865346550,8861012162,0x2a9006c306706b1e,0x54a00220c0886cca,0x102c009b00828017650e2c244941b2f40,147681482912,35424957917258,0x1f4019a06001f0880808d08c0c820,1318,1346,1575172,854719481766,114304962,3968633738764,1986,23917342254566,307243714,0x5d381011b066d0,7535083890,0x33403afc00b6013b80035802a09c14227307290],
[5156,1390,31834302852370,0x219400723001474c0c61870c,39736909860,41366341742,0x1ce4002528629112,0x10ce00392800a3e214319833b23148,109332494,0xe86000c3469112,0x69a0051d003928012398a31626303718,0xe96001351e06287988,7535085042,0xb603de0040805038006b00bc138732ed49f34,2470143069130,0x247002c3000d38001b4015b6007584abc44,250584500466,0xe2001250011b802d81068010ca0045b0098801d4007e00d0841b9840bb4f112,0x20e200724014af400050010e00246e00b600a402a18f001822a8005400b60131003a800fc01a1234250846a4ad026cbf4a9f20,0x1b07a9000f1841afcc,0x562efc001703f0389b184,0x48873b00120b72ad76,0x27e00fc0e26de2,0x21bc0058600106007e9cb08c6eadde0,219724908080,7535085514,0x1cc40017080110106670a0778,19834530701800,7535083762,0x105000c868210824c8,54945934,3092544506090],
[0xba400c4340c56e3918,109332618,0xd84005d6006980850dc5c0fdc,75920514,0x65684c146aa06c,7535084914,0x2ca80018b000c4800b3001901e188490524ce84e,0x5de0013a0636b002,0x2891c00b0401234011a802060150db800d200104b0087015600b30006050180c2ac92e61acbf6b19a0,7535083722,0xb5c00468023700570001c001c4008600b04204219923283d4,7535083634,0xafc00123000c831614205c4,0x23700570031800290025804cc00e20113000c1a1108a8ce,0x23700570211000f60025804cc00e2011300c86c508b112,0x710038600715e803122008dc015c012807b400a2002b002380299801c4007e00b04202e50f18449aae2e7f0,1644447482,0xfdc007a600c60440e0704a87dc,0x36d00127800d40c838da89d4,0x1688003a010410bcc,3163178943474,0x158800581e86866ce,25844443678426,0x19e801208031802300a86ec007d0012c02040588038804040146bd0a096164bdb02f0,0x340578160e2894a,0x68b0613bb06b0,0x5976001408628a9fcc,0x2cfe001408628aa1c4,0x4df4007e048f6,0x74b000f02849f2,0x97c0015c0376003e8017b001c4023e01bc98418228bb1210,0xa12346a51e8],
[31606502,4833956034,0x7c9003087346a55b8,7406317859782858,0x46e00b603ba002c400be8026d001d802c2881086648ca5718,83641072507272,7535083634,0x28f8002f8019f0014e002605a084328a7317d4,156325929206,144974045554,0x235005b0264801450035804f40391a34508a676,0xe12d07810a69a,0x1c40026200235005b01d9005c05d000407a00c7f017e00d60003009010450ac1b018655b71461021df6d1a,0x71003b600598001a0026400ed00a4805b003a0150df8012c006600470081017a00d6000500460218611130281830e084cd1a8537b9a6c8c00,0x55d00220c63128c7340,0x2b0c0030e04492,0x157c00f870ce530cd240,210781282,0x4a4006c40963130d7140,0x1278001f50007c60048904480cb8,0x1750060980025a006b4281ca8,0x46c004360038b00706043498,299909722,0x10a001450019404781ab3c,146239680898,0x286003490b22e6c,146239680898,0x51400514186c9e,0x27e0012e50606d8a,0x19fc004360023c00fd803d201a8803496c70381730dcbc0,0x70f09128e6b40,0x58c006e0904aca]],
[[0x6dd000161001633860718,0x9ad00051400e34262488,0x24800e8c00c3810f3c,971232193140,0x54243a0ca2ab6c,8998410803817764,0xff400e14186c9e,0x7fa0071e04d8a,0x18060500085004d8073c01ffe36084230fc640,9583768860911040,0x12d60005d40052840f08,0xdea002088014a105dc,0x489003b5002a0611134,0x564000c14a1ac6c,379332195888932,0x2ae00341c5288c9e,0xab800d070e28d8a,0x1188015f801930015e800292007fe4288cb91c1c0,0x900a0912926140,0xaee000c28005828461f08,0x7de004210038a1189dc,0x2e5000b5801c7810bd4,56931494508,0x37601e280385061ac64,0x3c30038904c4e,672296074,0xe08061807cc01fd8e0a04248ce4f6a0,6177318386,0x183c005505729f14,37757282,0x4a7c002c806048f2,0x4a7c002f8047ccf16],
[28465467410,0x319cc00432001fc00e3c007440070a6fe1ab4ea9ce0,0xb44a3c003a0ca1adcc,0x1118460009f0a1b1c4,0x160a38003c0c904ce6,0x69038018e26de2,0x499c00361f4878f4eadba0,0x95e80078448e6,18259924482,0x710ca08801e8,0x95f8005c39acc0758,38893283554,0x3a3002e02162839b8,0x317800e6c146a3ca8,1143489474,4817974614280,0x601f200033e000e0c80604076,9676419218,0x199c0022f00406003042788729b4297cc,0x75a00270b992c044,38865496818,0xe22000ce4008412392849182,0x50cda00217001060057c00bc004804c1dc04428c06d40006009050214556ac436977e2c7d0,6632257098379398,0x2f200220905182,0x170be4007d00d8e3614a2ae770,0x6318001c16187cc,0x325800b1c6189c4,4841294578,0x1214006b2000a06216146b182,0x2426009060058400b400680541cc04428406e4000200e0c28e1c39508104494bdb06d0,0x51c00110311e063708],
[0xffc00dc1c7810fdc,1669959860,0x337800c690014638a118c,10259894692,0xac801681c38906476,0x1e1801b071e044f2,0x19bc0028b001650033000e01b07101a6037200770011fe21236159276c8e8,2358264930,431089196648904,0x6468001f700110d878c80ce,60167308378,0x1e4011e9001bc2c0e0a21fcc,0x1916004890ca21c4,0x275400d06068f6,0x20b4001e0326972,0x19bc004260051e00104028601b900498033dc78482abb32c,0x466001090e506067f6,0x16200481c28488f2,0x19bc00291001610031001201909f012e037a0007007060b0661c39030a6eed8a,0x31003ba00588001e0069401de002300104008201cd009500c400480641bc04428c06e40384024e2a222238c0866085cdc8537b9c695c00,0x4714003a143061c6,0x471c003e0c307242,0x188c82b0c30c6640,0x94c80071142c,418,4728174,0xc7a001d0f05092,0x4550000d00089c0016989025330d23c0,1958,1986,464691680392,1998],
[39857298,0x13b80003400b228b0c2a10c,1314,7080528590,311718034,0x2de80010e001d38004ee0013c02fc032f2c09ca95238f60,80660173849125314,0xbc2a0450851ee0,802,7814389384,486,4034,15768524,9510436,369641454,35098488484114,0x1fb0007ac0054600fae0038de633062cc54ca0,0x47fc003a1cc61c2,0xd3e002b031cc857c20,219964366,137502290194,0x27f001c21b0022700134800f8a00643a808aee58b60,3181964,48808360742788,2982958150,15599432962,0xa3fa1cc677a20,2378446,58091925650,0x297005dd8002810000e80346ac44cc80960,0x12190009831418704,30164902],
[6514829250,0xf50d508a9860,369640814,927718191250,0x17f002244003d700003004439a8613904b42b3d0,0x16f0092a8007b010304,0x48a4003a1b861c6,0x48ac003a1b87242,0x11c01e8f0e6e2abf50,0x92e800618108d4,0xadc001021094c,102829860,71314550,5909938336018,0x2de01f062c0089300058c004c8009808a807e208c78212bdac290,45117181316,139842,524297186,0x8bd0005e86e1b3e10,120666140,1790333532692,414301196,414301700,103575558,13988820482,8932677861036952,1657197960,0xfa00e09584,39854658,554452450,94014924305892,0x88c004de003e0800a16187054389551096],
[0x56a0079a0003a006785070041ceef112,0x111801de800350020400f34003f0042022c0314230b33131284e49e930f6ad5826f900,13640222,634,0xf60c306642,0x47800b9c009830008a0624824d8,0x2c88012f7001a2e002b05863cc8,10764,11268,2950,4482,272933954788,973883742,6848792954,0x32a0013ae4006e30006601f8c219724,0x27f00220c003170031084884e,0x24fe0004ac8c92,0x89806514d600062c00118012804472872b73832d900,386010187686,1986,0x68800166800610b40424d8,1986,1011117880,7972,1295469513430,317415276686226,0x2b3c00484e100037004b91c30c21f1c,1314,5002833196,141218,0x252c0019302ed6,0x72f0005b200146246f92],
[0x17b00736005873e00483b900052006e008897702848498941623c0,1986,26665049030680,141250,508666396,3334,39858306,5156179651332,462713094,462714114,0x16eb0e694c6bf60,1986,21459913250716,141250,43063692,319889177849922,0x12250004a4504ac6,0x48ac0012454c2,0x12230004b1c1624a6dd60,1958,1986,2181927340444,39857990,4226,0x7c17e1412b04,1695839174,3461828875522,0xf86e639486fb20,846,1994,0x71020818203ab0,206],
[1994,0x76b00192091b420da50,812,3364,322225640057750,39857298,0x1a6a000702e8025403ec138c30a78d8,8068,141414,13644098,61287468440,2022,39858498,33843914612,2525977642570,0x1ad7000e3a0017028b0c12e44,1138,0x56a800b34800de06871b010306c92,0x13a0011d80027d00063008b00cc0b06045330992ec0c11f0b0,2964342690,26757996579124,1954,86786512676,0x490c000e1b06248f96,7559475346,0x64600303800240b6009b00d0b8c24334cb0e8,0x703848681ad84,941902822,1925489915330,597178196870568,1954,31056929508198],
[38739932610,0xa19a0e523574,0x9298002424484694a,0x2434008140177a001d8800b98042010e2ccb9b3e44,155407640306,0x1bdc00d0eec009d88005d806d01e1c91c8904e6f092,0x1bdc00d0ef4000e8002f80037005602440370140830f0e108964042b7c8662f00,98,65519292012,31159554020,16125020190,973883866,0xb820031f000c1a000d500f8834042488e1748,0x2b30054f801bc2002b058644b8,3076,3206,4098,8488747108580,49394238046,1309426298,0x2ec00813c003de001d3001c9070c19924,0xdd807f3800f8400d01048ce,0x48200297000998001c0219cad12,0x3b80627bd00297003e1000c600db00f3b8f811730720d00,11542978,0x38b000842d010db4,17934917164,17934917540,0x44b80013b001880c128f86,0xae01e2e0004ec000b025112,0x35802b804fe008fc00e7400afc000c20034b03e4ec04a072d0,866],
[88118289142,0x16f8007cd0001c0626f12,0xb8c00382000410011ac00248031ce0a30420d250,486579148,5319460,0xf78007402e56,0x4ac4003616086f92,0x6540010d001609c2001da0063c408588a80d8,973882734,0xa7800503092,0x44d800c92000ac028804ce0e8186aca8,19992356,29509046,363998892306,0x5120061500280800268039831a2bc2c34,6301802,0xf840097a000388009e028c86c0238c633944,0xd30023900132800071000ec0631c460e2770f96,0x154200121538031e8013a014c0482304085b4f112,0x1a2004720077c00dd80120110025c014340031013a00b80f40233117882c246df5631ea80,0x54e00375800d2b0015824a09dc,0x70802cc801a16000505318bd4,0x750025520010d8005870c19b2c,0x1150044300008c00d161a524,0x2596001482421a,0x707001a10071180088e48b12,0xe0e0034200e90098fb600049007590448734ce34e380,1882267676,120660500,120661516,120669188,28856678],
[30168322,559940465245344,5377169284,534118,82961588827330,0x4b5c003a8a850886dba0,1882261892,1332166,2618586370,0x70731cc66faa0,3272706356,51451692,24173949380,0x25d6001b0b1a8f96,1544188050,0xef7001282d980010358053403e88219ccb0920,1625373212,115424276,115425292,115425796,28856518,28857858,0x7f50ae230fb0,5377174916,535526,538050,0xea2a142231730,818176610,0x78a8a86e231ef0,135350511672,31469698,998567960],
[31469698,249642524,115425044,65024130,249643012,0xb25161e07486,28857858,0x4abd42b88d3c8,470567782,1332674,3522355975576,818177510,16137606402,29182270780916,0x994800020d0494a,0x1ab7000fbe000f0060e608a3e44,29030893298,0x156a002d1200264051e1c24408e6b092,0x156e0024f00421000ee014a0154054084a7089c6c9795aae51ab80,37385561212592,498552858256,498552864368,795234,99002303987248,2634,318926200,1446,1474,536955093448,18734786316216,31216028391336,41986580],
[3189772,506539524,126635014,10498434,8769929093490404,973883870,0x982c1684a9fa,0xaa401be60016700435000dc05f016201a5ba7b3421162523f38,6139655754756,1534913940742,1533840199810,0x5918007b870c18ee4,0x164e0011014043de,0x5918004e0c43fa,0x2bc0384c6003a100081800ea804111c4,0x21e017e40087280090a81864f6,0x1df00f2c00344005b869ca,0x11e801e28001500e9801ac03441e00218037017c06b8073edb4c548c80,0x1e8051600714218714,450,41341226628,22299533928358,963956991938,0x140801728541866dc0,84430850,323807048965132,0xd2900093c014212604,30165478,314007647106,0xd290000ac0017006788272c2306eac0,5132,5636],
[3334,4226,1015179960,17601875177128,21680783000,8068,2150,4418,119583020,0x89d00047e00173c11923be04,0x9c78005084f96,0x2900f2d00048200130207112,0x43402128051e0089f000e34000849d000701680c40c9e63947098b4072340,198,3650,5373297510,1884312578,0xcdb0001c015800960188714220760c0,0x600c002c690304,0x3f400a50841c6,0x3fc00a5085242,0xa6c01bd0841ff60,0x87801b0305242,0x13c11020830a31ee0,5506568162244,0xaac0047e800441604f16,0x47e800441605092,0x2af00072a00107001900901b01cc2c1210a34de0,845542435544480,536322,75641368,8533512],
[180464193436,6716149634,874582412,337723652,1284002694,84431938,0x51e00d78858884db20,85849923852011284,22007750200460,3855827963140,1346,2651605026,0x6aa80870508519a0,30168194,0x1f80571cc653920,6848792558,0xa1c0038505112,0x450800c660027c00480300901a83198318c54860,194,4701824994,686337705465808,89885307060674,0x2c8014d073195f90,1019639816,120659740,60491435745300,60475541955084,120661508,0xe4022629106,0xe4022629502,0x1583fa854cc31ae90,350675491919004],
[6657201444244,859198035852,111844399492,84431046,0x27ee0006838a94c2,0xd1d000b3c01f9c0e1cc86dd8,1925802520520,4226,7376020,3181964,30140338052,30168134,432821506,4281409004,0x228c008dc004d60009b800303e800d80f1802d00f8163430e15008e76d553e44,0x4508009de0078c01681640387c3081189551096,0x514001d0801302c8067804101f402c00824085b4f112,0x1460046a00786000540099003a1002603600fc06780ae05600c0440a7861112a28b64239e78c0408dab5479b20,0xc98030440007d800c421217dc,0x1e400bcc000698018c119d4,0x4f00dce0022f400d41619bcc,0x2b402f10010a3003470c19dc4,0x14f200064c00c9084ab16,7089660910922770,0x284000ed8000c80c35801fc2062a24c7c960,0xb3400786328cf6,2702732658,0xb2c007704884cad0a0,1546,151408149908,0x27de00142105cc,0xa10016e6001b471a424],
[5656987572383566,0x1419000c85086f8a,0xa01e4003175e004e10018c039d00049004580fbc0c4c195211510670,302532746,0x18440073f003780c18a058c,0xa0e800260211924,533090,0x9e80016d800d31a34ac0a,0x4c801188009d400674039a800cacc37337061d8,0x132000f7800adc00eb8017f8016403701a3336c64c8,0xdb800410c9858c,0x284200023413d24,2105954,0x13b0002e7001a0846f8a,0x2298009d200125000db801aac26aac227c,0x4cb00052e0018600a8572a334,0x308800e9a0013a0aa0c628584,0xa088005084176,0x284e0009808464a,0x1407b0039c009600279000b2008200d4803b10076c012373c1231292d2b9a,0x501ec00e6c8012c00c7801103ba000c8014e00e25801b803072014202cc00436a0062030819201d008b41fc011229649edb4eb918,0x7a4005820074400bfc00b20258091999291c4,0x1429000bc16286672,0x114a000e0c00d849ca,0x4e0384055a00a6c8012c00ef801db0043200548028960082003b009f01b101d50008807f0060ac0b207d004741646c953b24c,0x18900536001a600882dca676,0x6d6007160028304772,0x734c047600cc1ca004b003be007740019002b4004be807076013a034c01f400ec01880df01b40c83e804c1c615b50d12,0xa40734c047600cc0cdb00258018b002a0774001900e28069008920086003b009f016200207d003b006202f80020020ac0186439883e1040e6981376dee79d8a00,0x7e05d00720269800ef400a5300239007c4006a001e01f7004811231ba1c70,0x98310254005a00bbf00026012cc00e4802f6800d40178035c01102877c23c50,0x2b9800620446fa],
[0x26e8007600c26b0024b80149400e43c28a09cc,0x3ea00c0f001ea400241c10bc4,0x456c003de00726001207046ce,0xa044007dc00df002340a2894a,0x1a60271800c0803a04401d002680304400bb006240082012e02c3800bc05f035a00783c9008e08ee9748,0x12bc00d7c00e6400082306d72,0x4a9000a8c00320f3c446c97a8,0x2d240018e2c01ddc00bc04618fd4,1309426682,0x1fd400978070a78014ec00f8c850c211c4,0x78e00ab5001d1801903044f6,0x192e001aa0003c00b03049ca,0x6d8015400ea801e900044037e01883e81fc0098061c804e80428800dc01780be06b401b02eca253c27c4,0x8a7c002e0114a528ac9fe,0x22400c3b0003f00a08038cc04408d018c401880574082600a2c04546ea72,0x34406acc01b203407200754012200590004400b30024101100e800fc026402fc025401a8031017c0d580060e8a9d9454df27dd3e00,303114884,97544902,0x5604002a04507242,0x3cc2c30831b180,0xb2a800731162c,546,22029806,2550681746,0x522007205701c4ea8002f45c18cca34ac80,0xad20007a0093e80068a810714,0x1591000a86c18d0c,238100100,28329926,0x565c002a1b07242,0x5dd8007ea1b0637a680,11302626246],
[71313026,0x12b800aca0014ea1b063fa380,13810930988,517321371428,0x5b440013028c7096,833789399442,0xad2005302b9001f280132e00241002f7844126111556409e80,97583857658520386,0xbc2a04508519c80,930,73497192072,614,4034,15768524,34676772,930,22030442,0x162001a3000d03281ce120074d00046a98ac0c2cc549380,0x15c1000a838c6342,0x1fe6002b0638c8579180,0x7fb800638c65f9080,298607694,30164938,0x27d002426b0026700123800f18072f000307e046e6650608d80,3186196,238100492,283644076548,59525382,59528450,8910686079125376,113317252,7519356518],
[28329698,0xb52001ea1b06758380,3181964,37444581921156,36566750278,45156693250,0x2c3ea0e319dff40,0x57ac0034847242,925270208839232,1442,352468648,89326661784,1442,27952000444,2150,2274,13678372,134762518,134762898,0x2bd000160390383f2001215bf3c4c041131f38c0,0x1605000a84847242,0x70a002f0d2121ff7c0,0x1c4800d211a1f740,0x2d160002112b2c,10772131620,0x168d0009c147096,170160530,0x4f600d0c5600176400217001307c8304f3b42234c0,1212459048,0x5e500010446b018,7161325729800,51842756636],
[0x17a40004111b414,303117580,0x17ac0004111c604,121131494,0x5ed00010447582,0x5db000ffd40411226efc0,236349319398,595880290,0x7a36c2276e40,0x17cc0004111a7edc0,1092116,303115276,258184654340,75779078,75781506,0x7ea1211a8eac0,3186572,61186581380,11297518726,59528514,0x3ea0e31a96840,1086852,64546162278,75777762,0x3f7801ea1211a9e640,0x164f000987418d04,59525030,6514829250,0x3d435422a6440,2082,22029802,0x32f80029a00841881191000f049106312ab22c0],
[0xb18053402696000705810714,0x597c002a1ce18d0c,484518532,121129670,0x1665000a87387242,0x15b801fa87386affe0,285261316,45218296518,125982210,0xadc00a7a87386b7ee0,104626414666,0xb18056009a0008ec007940155006b40297006e026c78463c109556b8e60,1938087976,1938090008,126760579080,484523548,484524564,484524812,484525060,121131334,121132546,9001182952209376,79500954598,28331106,0x649000e21b06cdb20,266380317060,121132102,47365780994,0x7e87386cfa20,952426616,1949847938,20420421720],
[0xf80a0c6f048,2904450,20447688744,2904450,20447690760,484524316,6304130,5105107980,484525316,0x65b67838c9586,32271791618,0x2a55f5030b234f30,11297519106,81790719728,601313011302,34239682,30263826669200,14727188,484522508,266380327940,121130886,121132546,34808353184744,1092484,747732453051366,730220219490,0x1e7c009e07a84846dda8,484515724,109551100804,121132358,16112440834,4304041785324],
[0x2710011d800f28072b002c060902260740a873153c244,70746401650,0x476003ca0087800306bc001a001d801b00874070d18a1ae3c24b131192,0x2c3000898c00c48019f4800c10073ae01b6026c06780e6bc00ac063001500329988c2ea1189c2b146d18426a1128c4f0b508cacc3db7d0065300,0x9858c8c2881c,0x6c1b50c28e14,0x2c400388c18e2c,0xe82865429604,9086365739279758,55070912718850,0x27a6001fd9cd37d00c4500,0x10ce002830678800640e0a0c20f210,30077419916,11857369380,129330342734,26492905492882,0x77e40038f007da0a141c1631040b8,0x16fe002e805580085007e800138a80458a5ca8,372787982,0x8ad00008085192,0x153c000290050e089e003480201162a13c,0x3d0c00085066a0048b851c22d34,27387773030,104626414538,0x1f3800f1d001cd8009b060d05636110b8e,0x3c74006f200b04a50c48d8c71192,0x4f001e3a003790008677630041dbfe0162500,487342970,0x29640007e0075c00139000b32273072b0,7692,8196,3462],
[4354,2073401825508,15580808798,1644447354,0x299000184011fc00dbe007941c12a34d8,10764,11268,2950,4482,549229503716,973883742,6848792954,0x2b9c0004a009ec00a8401ce0a4222952c,319046522,0xc5a00081c00a5003f40091666c7ce,0x669000dd01be4008854ac92,0xf3800fdc00f9c0068803ae01ba025c06e80db801280c2034a0010217d894c077c80,0x4f5c0005601e311834,2890314946988,0xa81614e22e24,0xda015fb000617025096,0x5814003e0181207192,0x4da0111e0046a0028780076402241fb4220d0488c071a0,4029751828,238101516,238106116,59527430,59528450,0x3fe828cc853820,532659898124,838902788,42750534],
[19370112258,4230057910128,23681329162,0xb72000a50003dc0051032a0b297330,0x307001afa00098030103c4,842026476406,98896472138,0x81000612f0015e004808f001b6026a8002500b14e860c23c1c2a115182b0,98896471022,134762514,0x38e800ba2a1a1250,864314958,203714706,0x49580018cc316ca88f8,2164335492,116094162054,42751298,0xff0f838c8a5b8,0xe270006b4001c0570024044106b4a8,4539331150066,0x16fc0030a80009400106978ab888,87446547430,2958194114,8553520313708,26883409266,0x85002c37b003b0047800dd012a01e38014202418d8c4e070b0e3e653096,0x515c0015401a02c092d2d192,0x4180161fa800a602930019e002500b900dd012a036403902020046008f0009015401a0a3113625659c087839495421d180,450,56962911348,22603173356,22603173860],
[16125020062,973883866,0x1704006b7000bae000db0060600fc890d0208a303d4,0x6af002f740078704a112c,0x7e100031e001d02219924,0x1e6e000b380041048ce,0x3ca800220904d92,0x74400a601af8004e016e017100db00e4008c0185803ee2e1dccc24c580,11542882,0xdbd000a600c044698,772,454,2178,0x17100b9a007c80a1ac,995090235746,0x279e00093005a084688e,10981509354,0x44004e8012f8017f00054800d5e006680340902c0458b03a807360,33834418630,42746690,0x1c54001b077819b0837aa0,1122,88118288882,0x29cc007e80761000840e501e37828c1083c9e0,0x68dc02118704,7039378246,7159727549442,0x9f80071f48467f8e0,1884056334,134762898,0x30b8017bc00ec443e044a84820,1506],
[0x4f3c00122003088e5203d4,2336597578028,1675409593796,231979379534,997307224466,0x6f9001770078ac80135000a0d780029800498012200e29f61c0418a5b08a516a2330,0x31280016f0012112a14,1880174092,303116292,0xc4a0005cc004845186,0xc4a0005cc004845582,0x1894000b4800ff20319226e70,66582497510,42748258,0x2e6003186c1a7610,470041702,1328354,0x79d000c3048469fd8,231979378154,0x10c801a3803c57186b4b8,2957797578,0x86a000a780088461c54ab898,38893284326,5966416994,0xf52001880858a3374,470043622,1330274,0x187001a41104848dde,0x534007221e1736d192,0x970026f002da00d1ee800d5007cc032404980644004e02c81b9003e05080541b13729b25b608060e3b2554398f80,7700,1089548],
[8708,3462,4354,537434102500,15580808926,1644447482,0x54e00239c003e6801e50704a87dc,37413472723186,0x3cc01042001a30418bcc,0x13640021700030d0ca1b24,0xfc4001ef001d012694e,6964307062975890,0x12e000f0800b1c00de80321007f80dc803ec017dc39514c3c8080,772,3654,4226,0x17dc00741e6025e98,358231860872,0xc41000906002a0b812e3c,3678562,0x120c00aa0b812fac,1506,0xe1015d90000101489025096,0x5078002209120009025192,0x1c600236000514002da006080340840841a5fe05a8076e0,584149394926,2550681746,0x1d7c00a8620e8a863ce20,0x780207318704,8113123910,129823438082,0xe8247638c657d20],
[0xb72003960163400860241a09102ca5cce0,4029747588,1332294,27982320898,0x38606838c877be0,31690131212,2955354947076,12866118,62308505090,8805126287063712,3042,339348711410,0x4bd0006ae006e402d806700d2063388b49e0,0x9e580050c00c31183cc,1993819134244,75507702,1855562485906,0x434000e08b009ec005034c004f802160090e7e9c66404532d4b88a0,64873402756,9728709702,9728710146,0xf6061ce233fd0,31469702,31469954,8380538952,126760579128,31469702,31469954,8380545032,65024134,65024386,2095136780],
[0x4d83058781d204,5454408244557190,121132546,0xedf7839a234e10,4029755268,1332678,235304450,8212930024904,81612839300,12866758,62308504834,7732879349640,0x5e010f046576,235303114,0xdf200206000a07c6002bc00506ac00164005b400ce02a804232c04142d30670b993c24c,94391030,62308502898,0x21e000501a6002a0d98014805bc01aa02700c2458618ef022564f192,0x6f700187007c6002c400506a40136039406cc00a4057037e016c06501882706248ccc2682136a60a08edd5459ea0,10772,14724108,11780,3078,4482,137197889252,973883870,6848793082,0x2a90043d400013801ce0a42228dd4,0x36c02314000b022191cc,0x8d00d0b00163604a13c4,3050548782450,0x11d0014a801633869ca],
[0xdee0030e00f8c001540069c01b3002b00498033201ac4247094c5cb20,0x983963888ea,0x6bc077a800c46001190026402ff006cc048a80e0ea052082061c384b01cf0,0x1bee000e8800c401b01080720110418f2d0,498454784106,0x20d00399000a0b415c6197290,1880174100,303116300,303116804,75779334,75781506,0x3f68128487be8,11830051270,12862274,0x7a400760f48467fb8,134762514,0x4cc028b005903c744422044a8498,43430995046,40861197538,0x6622121227f4,421545574,12863202,0x271001f1f04848a7e,0x79c007e010e1736d092,0x3e8015e00c90030a005100d94002100d300c3013a02c4024346005a02f81c90031006c0e400c0e41182a996dd03078d625520690,51623560828,3650,56962913388,22603175396,5650793982,1644447482,0x1930040a004578006d400166001793c441186315d4]],
[[0x480485800104119cc,0x20406a6800940499bc4,0x1e40301001224328776,0xb6400e2c6c12,0x2bc018e0061400a601b2800420095004d8015400b3c00fa84c04cc4c8488,0xf900098800c701cb4002901981c4464a376,0x20f00006801981736acca,0x204008100277001ee001a07be0036401f300c501320051001b802b0164056c00f815015804c1216e345d4324c,0x25e001f30035c01078015b006e80cc1e11348c7f6,0x4120001300330599889f2,0x7f002bc00ce008c0c18014c011600b74003e01ae0182026403d806c1b300290174056c00f006048b41e0681783f099b4ed92,0x21404780bc4015e00670046060c00a6008b0000400dd000f802b8001030404c80d500a40d3007200a405d037a013e03810682e091683c0d03444246dd37ba06e700,1986,29264814108,3334,11546754,1561233271556,28791042310,28791043330,0x1ba820a0a5318fc,64445500098,413743201818988,2063234788034,25858967643774,0x2b5001a9a000890a03047c2,0x760035440025b20269b026d40,0x3190003c1c70640e,0xcde0039f0660a,0x6cc8007d0a50823c02cbc0,0x6200295c0075840052cc81708,795174,20982082],
[926937714431980,25314290,0x5a30006f003c2005ac6001450308664e,66675829698,0x15c800d550004cb54089eac8367c0,3650,0x163b000f293030801a8,20950824856,484459166088,966,3778,8741160910721004,962,554069674014,973883866,0xd800a501364007f400baa000db000bb003cb91c140c9088e0cc8,0xd7c004ee00ba5000a15064834b8,3076,3206,4098,0x7040478188e4,240820707934,1309426298,0x58b001fa8008500088800e47811524,0x1344001e60081400e34267ce,0x33b003850024d8001ee00221a19cad12,0x1db8033b0030e007fc0126c009e8024400960032c00f3840a0305cc0f660,23217482,0x4a680074312033181cc,0x70787c3215e4,1721202,0x4c580043811065ca],
[0x7220015640492ae11ce0,973883866,0x1dd4001f4400076801483a030c2281d4,0x186002f240028541920f2c,0x14820004bc00738c221724,0x8100043a0071e0484e,0x422004ca80038904d92,0x84400f880174c001ba001da007c2050b045ce17320,424281836225012,71450826,0x743c528042183c4,71450738,2549080940914,0xc0f80025640492ae419a0,0x708021aa00046107d4,0xf3004d8800285419209cc,0x6ee000a28005870c19b24,0x11b8004660071e0494e,0x17c2000903386d92,0x4ee00aca005eb800fb14160664c44820,6043016708,1510756614,1510757634,8410038178846436,369953249723870,92488346666490,0x6e3800ef070a38cb18730,73959340021252,2311229279494,2310155538562,0x2192001c9070c190e4,0x219a000082e0445e],
[0x2192000082e0447a,0x2bc0385b200374c00798140c18ddc,0x884c0c78ca076,6599265510266,0x1b601f9001fc800fc2006618c2730fc4,0x5b0302c00541844f6,0x75e004b600389049ca,0x1e400802003fe00f2c00d700d5010e0364023c009e004a400dfa030db4e64c8,0x4790003e1000783851c22e89b8,0x79010b10005844195cc,0x4804ef8003404117c4,0x240c15000d01046f6,0x3600bd800d1c306772,0x374800c780173c006d4012f801ea06022451342334,0x3bc000de000e0304d4a,0xe9c013409dc00c7801fb0055600fb807a80a080234009e014c000a00560ad8314717d3444,0x3980123c38908a72,0x7f017a802070062063c007a0293001ae001f00d900f500ca03740234023e0103a0048e872010924ced92,0xfe0227004f02a400be00c40c7800f4017a00d7006b8007c0364033c01c19406e80360798023005602a81e080308685394a72c589590537ba261900,0x1600cc8004ab000a81261ca8,0x5f7000580c4e001501267c98,15050320908,1007758852,111921099142,111921100162,0xf783412192a4e4,179558984030,3762579834,0x544000af800b3c810bb066ac0,3471662319636,809930047261196,0xe82865429a04],
[0x39c8006230668e,61745023461634,0xb0c003f251537d06c7c0,0x85c01009000a81262f6,0x4cb0035e00ebe0015012694a,0x952001ce4108bb876640,7692,1090052,3462,4354,2073401826020,15580808926,1644447482,0x198c008970013940018b001e50704a832c,0x3c300109800c61000e0410724,0x68c0043200033000a818454e,0x4428000a4005fc00181146a7ca,0x13b800e50054600ab401f700f900fe017b007880e5c002203cb048119287c040,0x73b800a812624a8,0x1ce6001501268498,1007757836,1007758852,251941254,251942274,547011893011684,358842665310,3588462250362,0x32e002cf2042ec21da0,889233420,8708,109333894,109334786],
[0x7da071921ae4,9353367152350,1644447482,0x448001ad8001b1001e50704a81d4,0x61800c8b0015061092c,0x6580005d001f0a11724,0x66f0006a4001c0e36a84e,0x3a5c007184d92,0x8060038200b9c00f9802f5007880da8023a00f90408a4c27260,5638351050,54993545763296,7427131015780,0x11a02e92001681c6480ce,16125020058,0x17d019c015300051d000e50b833458c0f18,9626154270820,0x31ba001a81c648076,49394238874,0x4dd400d5e005f2007bd001da170a62082385cc,0xa160003b800741b19924,0x6da000e180041048ce,0x329c00220904d92,0x1f4056080037c003601b2017700bd00740f1010240027b80848d4230bd70,7114744562,0xc810bb1a730,0x852800878014cc003505863728,266480975980,0x18eb000883606181c4,73035432478,155443030042,0x48da00252008d003d9000d280149007c4020619e2940fcc,0xb6065f8002c1b191c4],
[27491060180338,0x19e800eb801633869ca,0xdba0032200f640108400d5008d003500d2801450032b1094324c6cf8,1523107597252,54303436089598,0xec80195012694a,0x1f3001fa12042ee91b8,1644447482,0x4f006a60007e400440e0704a95cc,0x204076e8003c04997c4,0x90334c0054184676,0x500294007c284772,0x7ec00728033c01f30000800170002f8010a03cc1c3c6593a52c,0x43a00246002c32c87f6,0x8de007184872,0x80a0037200f867807067803e600010075009e031018c01606a03bc00d500344432586254ed92,0x3a80bdc014e00cd001c2006601b8020c01f0cf00e0cf000c806d80004016c058bf006c0f3006a008404f036a01df00d6053485161484a094d914dee91ae80,1278285316,319574150,319575170,8322760741108,22146061570412,5536585224676,5536515394526,1384146308314,0xf3400a5c0031801eb003ece739b0c7140,6915469020692,655548878860,164613984772,83246230677775510,25314687224194,0x377800fa651537d0cce40],
[796070,2107234,980741924760,0x16e0052c8009318008ce0038b062883f08,31605366,31607882,0x5c34a00f8801260800406006dd070c193cc,797858,26936634462,0x4330010e012f80508800705e288cca,0x2b600a120018400f78006397c668b7d0d68c0,973883866,0x1118002e9000764007b801088014c0c9088a0cc8,5124,3334,4226,2165863190244,2407128392670,1309426682,0x1550002d8008aa00144800e4781072c,0x115001538000fd001f0a10d24,1910523490,0x26980082800b6801e28b067ca,0x8da00203002ae0050c009a8025c0fd0063004220072aa1a0902730dc240,1723466,0x4f1001f41a18f2c,1722738,88735020506442574,0x982458c8cda,0x452002d8305ee39fa0,973883866,0x42a80078b001188014c0c30c2281cc],
[0x290400153800140c218924,0x196000454006f021883ce,0x11d40030a003890484a,0x129c00af8039a003e40032801cd007ec332c59d03f620,1278284804,319574150,319575170,499256195714788,0x5e09120883de,25848280024058,0x780800f239a6c41c60,3184132,3334,4226,558594907325336,39891992200584,9972998050300,625303724916,758,1226,232794478,156325931482,0x8740073e006780b98051b000ce0093400fbf0280c183d4,1956454099418,0x1f1c00036002d90012e801584c2422285c4,0x50b00050c007c28444e,0x38200235a00389048ca,0x6db001950041600d1009fc00bc8025400d200964005ca1e36dce47020,71453514,0x984a81a189cc,378387828976996,673906],
[324278971466,0x266801560c17b92750,0x1c84009f300046107cc,0x13640054b001bc086209c4,0x6ee00176800d303062f6,0x74003820071e0494a,0x1f300ab8033f00211007fc378cc6313cb0,1122,19579636764,3206,274434,1610738637188,26369748998,26369750018,7678009739516,4833953378,24683581966700,4833953506,79354307198,0x15cc001d1000890c284462,0x3d1c0025b14709b267c,0xe0d0015a014f00264800382c0c195cc,0x10db4003c80ad20002094197c4,0x1b00c44006304676,0xa00bf8005149066f2,0x23480009b001f60077800144008f01e582c6cb8c9ca,0x3380bdc014e00d10032e0033006d8033405e4015400b8022801d02ec00205701ca00a80030021009201a81ab002a401540a38b14a7061466867c537ba66240,0x1a0e040004a0018e2654a,0x71400e020068e16e29460c0,0x55f000e6106696,4901623808681746,0x1c1400d5c48ee537a0],
[68175462,0x541d60117a0018e26772,0x6c0013085666e55ee0,1881163162,0x15f003580fa5000dac00ad200690109bae0cb8,0x7fc0000801328012be0020f800e1c25081ca8,0x2a2012ba001758012831283498,3076,3206,4098,8178817403108,1881162334,1309426298,0xc78005a00b560021700391e0454a,0x8c60020d0053600f9805ac01340454025e01b88022c06f03e7529629ce573e0,0xaba0078820882848076,0x5750018e265ca,0x2601f54007470b52c59b20,0x67300011e0002e800e1118a81d4,0x2040021c801c781092c,0x19bc003050009608a128f24,1910522978,0x475001158011872865ca,0xbc037d00044049200c90055008da000480d6830489ce5f1a0,0xa38652a61960,0x3a100006900142680f08,97015158669764,498,98576106,0x3b4007a2000440257002c8800a083c38a05c4,0x6da0018b801e1c12844e,0x38200246e00528464a],
[0x17405f2008220017806fe0008806d805b4015f000bc01088004f6021421319db0,0x78385208828481f6,871913138317002,0x12020033851c2d4b9a750,0x1d5c0003e8005838987cc,0x3f100169400e38989c4,0x11b8008ba0071e042f6,0x1d00122800c9046ca,0xf480266004b800ec0032800b700fd4a1092339bcb0,0x49a0038904462,0xd14594b1c670,5132,3184132,3334,4226,4122054900,870,533474,0x3456001bc08445e,1309426810,0x6a670018b0075200047800dc41c6883708,163401760868,0xd1d8001401078c8076,12358542234,0x1194006f7002d50012402e1801cf038b084238fc4,0x75e0090200041c38908476,0x67a0069600336484f2,0x45f00104803e1801b100fb0015400048013ac31409cc772,0x2980be4014600d100346002b006f8031401c2000d00dd00f500ee011c007009817600707f00203602f812371004f01e816c0da46a44662184214deea1a,0x14c05f200a30068801a300158037c018a00e10006806e807a8077019a00a81fe007c022809a064c00e1b9009e03d02a80140d37b001]]]

def data1 : List (List (List Nat)) := [
[[440681638239136,226532900,1998,56633354,0x1c930612c5850e30aa0,0x7870450831a60,855674948,56633230,56633674,0x2e68184e1260c34960,226530348,5412,56632718,1482,0xf11b419014,3447758380,6299428,861939726,1574986,0x1fe87811b428e370,39856514,21902695988,15191809836,2434,14813198,603853957514,0xe562808e1c114310290,6207300143490672,159417180,1233194196,3340,3364],
[56632150,5945436562,0x68a73ff0f06138470451278c8,1346,6478804705507752,1778,0x29234d0308e260a7c88,1348,13640654,10488210,0x228e78ec712330c32024,128962283806,0x8081023420440499a,0x9228e78913b1c73821290018d80,442515814,39856066,0x630c1030841e,23669769274690,0x3ce1910a098880,842,0x6700c04181d4,39854530,0xfc1b010c64,498,1142495929290,0x9410382210a118180,0x6c1e141827d0,56633230,56633418,0x460a76260639e34303370,0x901020c206750,39856386],
[167625399860,88101396268,2306,411174926,94611762587914,0x250564140e1c114310470,8107655900,788,812,226526020,13640534,4871694482,0x107c14fd96260638470451278c8,450,93454572509100456,1522,0x1f038db13030d0d0a7c88,159417636,982,6293650,0x2432011a3cc02041020c32024,0x34560e0848480489e,128962283802,0x3c0e026f38913cc021ce084a40671c0,0x8c0e341807f0,1994,0x540b82a3606041414301db0,39856962,0x2d808e34208770,22233302517584,39854178,0x3181c114216710],
[545600837363440,159417100,159428100,1623198726,6668946690,0x2286441ba1ed809e1421e650,114,0x43009d147818e240c3a0210,38498157887992,1398,29043476882,0x58c1c4c7360c84c8,2434,427852740,882,0x5c0d816c38d06982,0x7c1f050b4780408e343223c,66009511863412,80749426,0x3c0481c6e8d80408e3432624,39855842,0xa2b0709e08a1a,0x1a0d0581c12ab1732946120c739c1144886240,202,21029506352068,114,1383014097266,0x3b01410382210a29fe0,10775185566,10775185818,0x1f0f8470c30a31f20,2378],
[22269147582260,1778,24466023358756,56632418,575563385242,0x25e70228a39d60,0xd02a6d0841d20,2122,28866217347540,56632770,3126887260260,1522,4638600882506,0x25e70228a49b60,1346,0x194091c114202650,159384526,39856530,0x147c0107c19a031c27850c0cf8,3074,0xe2c81f045060dd8,450,0x1702470450831b8,964690550,13641746,0xa04b0b419a031cf0450c3488,3330,0x822049e1418d74,5252682,0x478c20613d0560c11432244,5252210,0x11981360304ca04e15850c992],
[0x40a0103054192c9291c112a314750,1346,0x9e0238d0801b8,846,205523346,0xb81683f0f030e260a0708,4131276295804,318767602,0xa03838f8781871e1430f2c,2956602775140,239076210,0x2a0241582948742c38d0a992,0x9c050312341c19aaae161c2382211059e8,0x2e0b872048230450a61d8,194,0xee0238d081988,202,0xd0620a58680c3434287d4,0xdc04981886c,746586226,0x190b82c2c34061a0450c276,167669434010,0x105c2428e5c241157f058708e088441a64,0xe02a6d08462,0xa0410230228a71a,0x19ce87c19b9e1c244c2e439c1143001]]]

def data2 : List (List (List Nat)) := [
[[4212,6252,553687844,1122,507520794,0x6a70905070834020,0x5c145c067888,43201404732,2182,56633858,30339571748,14027344014,459287050,0x1dc86320ba146394310,73039902856,79702150,2562,437019287596,1702928932,23079118,597063387658,0x1bd20304b2146398210,0x681c220469f8,672678102,1354,0x1063981c2c518a78c8,6325580,1610,62824373045382,699402770,0x1c30bd11061a03c,525898],
[0x1c51b30d11062222c,0x813010f01a464,133206910690,0x54a230cc200848708a1a,0x811cc551824a0a1463807e40,1627655672,5912936734,244914873362,0x6083e198838c8,5922636216,2690712692,2306,23102820,370165270,26756738,1647227016748,912332900,228083342,144956212938,0x1b4f9170518428256c0,16207855818,0xb83418420275c0,760775512172,241866709092,970395764366,89530582730,0x6f91304a1c283d340,4674015228608,361364530276,1762,8536394328602,0x2a41961c20670c0],
[1762,150328068634,0x4619961c2886f40,4674015620800,0xe83c39d070809820,2562,23109156,2126,789002,0x3307b19004146283370,532593014936,16940168,2182,2306,56664108,217973858852,1059022,160975114,0x7077b830704c146318450,206,22012773714,0x48063680c0c7810a78f8,0xe0f05810879e8,10800350706,0x142f8682601087cc8,2434,360748876,77431054916,13222037894,0xe41c184c1e04a02,0x7201123de130781a034,0x182404a09b90662226c],
[643900964,235948494,0x1c839a18d0c858108a0a,0xb8641863553fd0186b198c31f60,8446809573689040,51925557028,1583246,56633866,0x6207216004146281c50,780,0x1d83a0180412e04,6055099640838,0x71c80440104d82,0x21366025c3c88198679d8,12981387378,0x48ec170259ca58a87810e80b8,5651954127110568,10800350578,0x3b07c15950a87810a8488,1581302,1855763016066,0xc1c0583047491f0d1e043222c,18528413220,3362802126,0x22d06c1920a09c28087810ea0a,0x212163205023156f282380c02198e399e0,0x1240381c2960a419a0,120666233184,0xe094051106182630,12981388746,0x24202430834441880cf8,176150293506],
[0x18a09c0c41840dd8,22012775682,0x1b04f05810651b8,10800350194,0x52150960c8581085498,13422832774,1060226,0x5170760411574,97711565002,0x30741e29031e85c1c1a244,0x7405808ca41986986,0x40b0aa0cc858106a12,0x60c0d018f1e124b2eb05022c66314690,0x6c14441880198,12981388618,0x6a05c2f0981a06201dc,8084540674,924171861366380,882,0x4204c147870a87810a5ce,0x190208a41988982,0xe0438880214481125d3a196198c59b8,0x1706a03830960861a8,337134810,0x1c440d04828d98a1418a6888,4632102602,0x902050621a74,0x1c440d00c1a62921c29b2c,54534386,0x170ce40bc0209608462,0x170c90b160c1c0a14e140415810e71a,0xf0992682068630314ba8e09408583001]]]

def data3 : List (List (List Nat)) := [
[[2754,0x4b058306199180,838995240,1275220120,21640,318805564,5940,209755692,7972,52439438,2506,0x1ff9020905a0a308780,52437442,800556204524928,117477460,4556,318805028,79701710,2378,0x6f84041413020d3fc0,52437442,6955538492292800,13153883408,12440,13448,318803516,3892,209753644,5924,1550,1610,0x3fc20281a064078],
[2281849064,173073912024,83907784,43386034360,83909800,2178,87812112520,29368636,2434,73933356,235939364,1634,133578,0x18faaab1c0a06820e32c0,205530754,0x4505c0a06818e71c0,206728891940,142615822,27272906,0x3762c1d018f2fc0,189121177218,0x6261cb606810feec0,1794,0xf8530094290,268522096,1794,4483409601072,1250,2120952,232339304680,994,2127048],
[2182,2434,2959114392,1762,532796,1927576330804,285221676,57261678437924,1506,133578,0x1d089a9565d78c0e01902440,0x3b01c37011263c0,117475212,117475716,29369062,3138,0x760f61e0c8193e140,1275212584,436352024,13448,318803292,133253078100,834,670937718308,1998,293612042,0xe8042950f5d709505061a0e50e20,1318,1346,0x64a81c1a0851d60,1270,52439498],
[0x1a02809b8608dc0854ca0,436354200,1275097352,79702146,377528372,109093164,52439554,14084483214,36710922,0x38383c0f055641050385830c58a60,0x810380459a20,138413298,0x2d03605a80203065c9a0,2258083682656,0x4150885890a0380471920,5508,317907281382,79701602,74374280074713120,3364,1358,27273618,0x210321c426c160c29e390,388198070609776,7116,1250,1216358262,5398088082,0x4b51a80c19f2d0,1098,0x1701c150d8304886,524290450],
[0x640505436c160c1a0250,1023417284,27273078,2450,0x3907d830484e8,4198692,6954158486,831128611346,0x320281e1ce9b05830888a8,0x5b025c13a051cda038049998,8076,120468840836,287815248102,2402,0xa0d80303d8080701a764,1762,0x13821c0410468c81e06a1a,0xa151441112c2c51b18ac84b084258ac1050385830c0180600,5156,1358,1482,0x2581f305830630e8,5156,1678,1738,0x5c0738583063ca8,1810,0x4c042630583065088,27272850,0x1a83338c160c21734,0xcc92c31011c6c,1382],
[1442,416817366874,0x2112efc0e160c2017e100,29368674,62507729946,0x2c9c1a042027db00,29369230,29369354,0x161b3c2e03081718,388,29370054,2370,6155195260178028,626,0x9b50e85830844e,0x950e858308642,0x622d8080e1a042837c500,5932860426,78814094089579840,842,0x31801004181ec40,12440,13448,4156,4404,6188,6436,1678,1738,4382746243184,1745384528,454],
[27272834,3657584888,60565902568,1666,898923387080,251681976,27320421345448,454,27273474,914398780,12993994548,2434,8302540923940,8776591758,10488266,0x3abd5fa161a09a0a19f60,55977250572,55977250820,13994313478,9666840962,0x3d703416810a1be20,1538,529452,1730,1421878798,263882,0x312e4140b05830a1dca0,2178,532268,2434,387983630,264586],
[0x3042fa161a09a0a1fb20,5932860178,0x43042010623aa0,498,0xc3042010625a20,1538,527652,0x18a0104440104686,27264786,0x6280438405068108318e0,118115864196,738,94381298,0x120aa43a160c20d7f0,834,8100417471084,30173889380,100959011486,0x4a0c2c0106492,0xa1e047ebc1a04210330,0x3c0a10205a04212710,450,94380914,6158399055673008,0x420781a0106906,54528402,0x1f07282c44214650,738,94381810,95030463583736,73123562108,226],
[0x5e1106818a6c,5477829604,498,0x628160f60104692,0x285428aaf088681086088,786930,0x10a15050a10141a0421a74,450,94381430,16107193762,0x6205cc389a086da,0x570652893094edb889b1a0418450f00,842,0x18811801004181d4,29368770,536853849672804,498,0x1904304201063ca,0x2561a0b1a0428470100,39605516732004,404629097579294,0x3c460d830869a,0x11dc760c285cf900,0xac0243606818269c0,839008424,9797914776,9797915784,2449479228,2449479476,2449481772,2449482020,612370830],
[612370890,0x311b0062e08c051ff2416818324c0,142616194,0x243f80982481080a06818363c0,451036016173888,74796872721088,1666,59379198087368,15569278136,1666,39730567320,1122,530236,0xf806201a34,2680168685100,5234499364,670067337358,1308625098,0x78e900ca5ff020281a0841620,0x2c3c405c39281a0641de0,7716,1998,2250,6575120879744224,3858760508,209753428,677337926506572,194,262223710094,1994,0x417c07c1340186b4d8220650b20,0xa50780451ae0],
[4052,209753164,292175291940,52439502,52439562,0x5f01f03302c0c18bed8220454960,2050,48711374035168,1332,5291416492108,1994796329474,229833197966,6226463242,0x3208e0158030c82ae60d0881963b0,0xd629e310196790,37749746,0x3f805601403028900c117350,0x3a0960158050b1e0444310118730,1543504684,5412,52438998,0x47003601a02892,0x3e08e02581410d0f8f00c19e290,0xc381d011e670,6092,209755588,52439318,79702418,0x8e0138050a582825e3c03047ce8,3202,212399717832,39033350655234],
[0x1408e01180702c0a38580489a8,1142,2341860297234,0x3023804a00c2e0504b20900c1a63c,0x8a0c541d01a674,3925870194,0x2811402500380ad08812724,1762,0x288478e3321e04a1a,0x2814d035001008450bb1273454ab2c4b528e0560c20665300,13994311954,193416203796,0x40370090b0d08820e4c,0xb0d08819004,0xe40342204706,0x3900240304982,0x1780fb29c2268306e4500,209752100,1294,2248148362,0x47d030407a80203062728,0x5800a01f809981a043998,1474,2248279442,0x2580de01606660d08819434,19596576198,609912629698,0x4f006e008bcb0c40659e,0x13c04b02b0715230583086ca,0x9e007c0709dbbc160c18762b00,52439054,2442],
[0x607405c80e70122060cc8,27273166,205531274,0x3f401f034b0c4064118,712991844370,0x3a8088368e06826821f3c,2434,119546214,11140336898,0x410045bcf0740689e,0x120321a887034220698a,0xae004c0702191368268187e0f00,0xd206606810064c0,0xcd00c8660681016440,5412,52438990,52439434,0xc40523c0041c6f2121f0c8201c240,2114,0x4702681886140,109093380,7189039366,109353896450,0x52836d80d540e20780451fa0,6028,6391230142852,1766,0xc1004c02762,0x16838405903de0b01c0655e60,460,98,62507730958],
[2122,0x48c00c2e181a09a0a58d20,96214253411552,3532,1378,473967054,1931495946,0x12c303422065cba0,1794,525276,52438794,0x1c2001402a6811c0c,52439554,5662321038,1260399114,0x3b4051012097bc09a08609a0,1369450890,0x6a80be02c19bc09a0670920,31272734148,27273678,2570,0x1ca01e9a0474820,4071656270726,7952403714,0xdc1b2004406181d011e7b0,8580,52439270,4140400912866,0x3ac03bc31011f730,209748156,109085076,209748396],
[452,1486,125839890,0xf41ae01281b07873f5420c2214683a0250,38,98,0x6a7051a0881f8,1398,52438898,0xd7004a009c8486c40884c8,1171922391480,109088196,27273038,6478113298,0x1e833c0450361b890e921f022683263c,2483531359860,9160361330,0xfc10b0059c04881a724,1762,0x38211343867781e06a1a,0x7e06a0080d010a0683122231960844c4e6d252a4364089a0c21be80,7716,1998,2442,0x2d00220241881c89a060728,27274182,3330,0x86009d41d011e7c,2086,2530,1667269468004,0xd8028129300409a0884e],
[0xd4018d4cc09a0698a,0x3b004dbe4089a0827b180,0x978032706810829b080,202,0x8e40121340aa0e268203c4,0x29100fa0060f09872208176,0x25e00a8389a088c2,0x4940176360a6810a2fab80,1346,0xd09504c0809960,3884,7236,73043822670,2570,0xe0313402280f7190581a0a0c820,0x5d0141e010c7f0,42547022284,1718096008772,73043822926,52439434,0x5806204a091ce07ae0226820d350,4261419316,9667943980,4235044,3222292622,17717807306,0x4e078741b0b9009fe28c1a04298490,159394186,0x58c407400d006812b00215c048819c450,292175282988,3364,0x9c80060104896],
[243280274,0x162c403a80e788f4110878d8,0x70a3c1e0879c8,1526,52438770,0x24a00a162210781087c98,52437350,0xa180420104d82,0x212300e735d8041a274,52437990,567378190552450,0x7851002186351081e0699e,0xf192010c038d232c20d110aa0a,0x3c6301d01702a0f1541f04a032ca2676dd3a070b110c318580,0xa4607d004c0eb01820a0080c28fcc,0xd604c3a160c21184,2516583026,0x601281c240282c6d606f0583064f2,0xc04700c818c0d49052c5830a358080,2516583746,0x124038901c1a0801820,0x2d004b00c838a58682817f0,3372,3187678276,1998,52439562,0x9f00b607e116370201d50,0x154035e06818e730,54358181828,73043822926,52439434,0x1102900f07140d08818f2b0],
[59925800700298,0x3b00440c605900c71026819c470,0x9f80320140680419e650,962,4865433988,2416986726,1060098,0x7884201067dd8,452,974,13959711122,0x24401981083a3160307810c8098,0xd82c681088188,1398,52438770,0x12816202108042212c,0x900040104d82,0x34630128a644010699e,0x156004401c1ca284225068108a0a,0x19807a02a0341a0b8150b2456139710f0305a0430e6fc0,0x18f00d0383682906f40,0xf301f0740479a8,2406,52439650,1839068159868,1611680898,0x350111d8041a06c,502,73043821170,0x4700605c02c1305e85c01010890a,0x4205a01502380102e01604865b9022682126a40,19998442284],
[7716,1998,52439562,0xbe05e011038481215806c07b608810dc30,98,473966606,2570,0x8c20146c18c0c303422063f58,79703362,38828450806200,1794,133542,265474,1667269468028,1611681094,1060226,0x63dd8041a064,0x2a033353685c0101089ce,0x3a0094da3078106a0a,0xf81680fa004c030889be4089a084dfe0,14461961802,0x3a80ec086013015817c160c1a244,1138,0xa3a81b401e04701a05a0510020306992,0xa3a80e408a00e0340180e09090bf0385830851ea0,2578,0x51605100d502b0546a03065f08,25904024004,1742,79702546,0xee03502960503a042819805838f00c11bc4,0x3fc00821e11851008f41108776],
[0x1470034160983078106992,0x1cc07f0028098030583844ff0385830855c60,0x32401e110681806d0,5033168164,73043821902,3204450706,0x4601fc0760711c80c181c50,7012876386,0xcf00bc0a146820e610,1988,1742,79702546,0x1f4008c02c3b4146c4083cc8,0x8500aa00501351a0a3fb8,706739033364904,209751492,1270,1074809106,0x903eb1080421734,3899857576822,1059274,0x61ec04a0284c08a03c32090bc61f06810a996,0x3b8076011281a19071605068108a12,0x143c80e404c1a80580383c34196088993793052c44316770,0xba00e048360c298750,0x7e00381d0106610,2030043342,73043821898,0x2302a0b0a0103d055039a2038583081f58,98,0x283014320821b8,452],
[73043822030,2578,0x2281905ac04c1d43430a068289dc,313363087366772,52437878,1010,0xc60241060087a190781086ce,0x820389c0a01051181498020f810aa12,0xf6078060589a0cc0e2305c06824543a04c89d8e028116810c69a8,8757706954,0x1f601d02961209c0730168268195c4,0x159807a051c3780486c81220a5f6,0x3fe01e389a08662,0xf203902b80de01771c226829b6c,230695282,0x16202b80f203f0785a08462,0xb1015c0740e3e1c70b0d0d01808fc1c48e810c71a,0xc3386e07089c0e58d04c0b161a06060a85830c3421066d394682001]]]

def specs : List (Nat × Nat × List Nat) := [
(0x55555555555555555555555555555555,10,[1,2,3,4,5,6]),
(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f,10,[0,1,3,4,5,6]),
(0xff00ff00ff00ff00ff00ff00ff00ff,10,[0,1,2,4,5,6]),
(0xffffffff00000000ffffffff,10,[0,1,2,3,4,6]),
(0x33003300,4,[0,2,4]),
(0x505000005050,4,[1,3,5]),
(0x33333333333333333333333333333333,10,[0,2,3,4,5,6]),
(0x1010000010100000101000001010000,4,[3,5,6]),
(0x50500000505,4,[1,3,5]),
(0x5555555555555555,7,[1,2,3,4,5]),
(0x330033,4,[0,2,4]),
(0xcc00000000000000cc,4,[0,2,6]),
(0xffff0000ffff0000ffff0000ffff,10,[0,1,2,3,5,6]),
(0x555555550000000055555555,7,[1,2,3,4,6]),
(0xffffffff,7,[0,1,2,3,4]),
(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,7,[0,1,3,4,5,6]),
(0x5050505050505050,5,[1,3,4,5]),
(0xff00ff00ff00ff00ff00ff00ff00ff00,7,[0,1,2,4,5,6]),
(0xff00ff00,5,[0,1,2,4]),
(0xcccccccccccccccccccccccccccccccc,7,[0,2,3,4,5,6]),
(0x3333333333333333,7,[0,2,3,4,5]),
(0xf0f0f0f000000000f0f0f0f,7,[0,1,3,4,6]),
(0x101000001010000010100000101,4,[3,5,6]),
(0x3000000030000000300000003,4,[0,5,6]),
(0x550055005500550055005500550055,7,[1,2,4,5,6]),
(0xffff0000ffff,7,[0,1,2,3,5]),
(0xf0f0f0f0f0f0f0f0,6,[0,1,3,4,5]),
(0x5050505050505050505050505050505,7,[1,3,4,5,6]),
(0x11111111111111111111111111111111,7,[2,3,4,5,6]),
(0xcc00cc0000000000cc00cc,5,[0,2,4,6]),
(0x5050000050500000505000005050000,5,[1,3,5,6]),
(0x330000000000000033,4,[0,2,6]),
(0xff00ff00ff00ff00,6,[0,1,2,4,5]),
(0xffff0000ffff0000ffff0000ffff0000,7,[0,1,2,3,5,6]),
(0xf0f00000f0f00000f0f00000f0f,7,[0,1,3,5,6]),
(0x50505050505050505050505050505050,6,[1,3,4,5,6]),
(0x330033000000000033003300,5,[0,2,4,6]),
(0x11110000111100001111000011110000,5,[2,3,5,6]),
(0x330033003300330033003300330033,7,[0,2,4,5,6]),
(0x55555555,4,[1,2,3,4]),
(0x3030303030303030303030303030303,7,[0,3,4,5,6]),
(0xff00ff0000000000ff00ff,7,[0,1,2,4,6]),
(0x33330000333300003333000033330000,6,[0,2,3,5,6]),
(0xcccc000000000000cccc,5,[0,2,3,6]),
(0x55550000555500005555000055550000,6,[1,2,3,5,6]),
(0x505050505050505,5,[1,3,4,5]),
(0x5050000050500000505000005050,5,[1,3,5,6]),
(0x3300330033003300,5,[0,2,4,5]),
(0x33003300330033003300330033003300,6,[0,2,4,5,6]),
(0xf0f00000f0f0,5,[0,1,3,5]),
(0xcccc0000cccc0000cccc0000cccc,6,[0,2,3,5,6]),
(0x3030000030300000303000003030000,5,[0,3,5,6]),
(0xffff000000000000ffff,7,[0,1,2,3,6]),
(0xff00ff0000000000ff00ff00,6,[0,1,2,4,6]),
(0xcc000000cc000000cc000000cc,5,[0,2,5,6]),
(0xf0f0f0f0f0f0f0f,6,[0,1,3,4,5]),
(0x5555000055550000555500005555,7,[1,2,3,5,6]),
(0xf0f00000f0f00000f0f00000f0f0,6,[0,1,3,5,6]),
(0xf0f00000f0f00000f0f00000f0f0000,6,[0,1,3,5,6]),
(0x3333000033330000333300003333,7,[0,2,3,5,6]),
(0xcccccccc00000000cccccccc,6,[0,2,3,4,6]),
(0x333333330000000033333333,7,[0,2,3,4,6]),
(0xff00ff,5,[0,1,2,4]),
(0xcc00cc00cc00cc00cc00cc00cc00cc,6,[0,2,4,5,6]),
(0xff000000ff000000ff000000ff,7,[0,1,2,5,6]),
(0xff00ff00ff00ff,6,[0,1,2,4,5]),
(0xf0f0f0f,4,[0,1,3,4]),
(0x111111110000000011111111,4,[2,3,4,6]),
(0x50505050000000005050505,4,[1,3,4,6]),
(0x55005500550055,4,[1,2,4,5]),
(0x303030303030303,4,[0,3,4,5]),
(0xf000f000f000f000f000f000f000f,6,[0,1,4,5,6]),
(0xf0f00000f0f,5,[0,1,3,5]),
(0x5500550000000000550055,4,[1,2,4,6]),
(0x33003300330033,5,[0,2,4,5]),
(0x55550000000000005555,4,[1,2,3,6]),
(0x30003000300030003000300030003,5,[0,4,5,6]),
(0xf0000000f0000000f0000000f,5,[0,1,5,6]),
(0xf000f00000000000f000f,4,[0,1,4,6]),
(0x30303030000000003030303,4,[0,3,4,6]),
(0x50005000500050005000500050005,4,[1,4,5,6]),
(0xff000000ff,4,[0,1,2,5]),
(0x505000005050000050500000505,5,[1,3,5,6]),
(0x1111000011110000111100001111,5,[2,3,5,6]),
(0x333300003333,4,[0,2,3,5]),
(0x3300330000000000330033,5,[0,2,4,6]),
(0x33330000000000003333,5,[0,2,3,6]),
(0x110011001100110011001100110011,4,[2,4,5,6]),
(0xf0f0000000000000f0f,4,[0,1,3,6]),
(0x55000000550000005500000055,4,[1,2,5,6]),
(0x303000003030000030300000303,5,[0,3,5,6]),
(0x33000000330000003300000033,5,[0,2,5,6])]

def forestCodes (forest : Nat) : List (List (List Nat)) :=
  if forest == 0 then data0 else if forest == 1 then data1
  else if forest == 2 then data2 else data3

def forestSize (forest : Nat) : Nat :=
  if forest == 0 then 9598 else if forest == 1 then 186
  else if forest == 2 then 160 else 658

def rootBudget (forest : Nat) : Nat := if forest == 0 then 12 else 9

def roots (forest : Nat) : List Nat :=
  (inputs.zipIdx).filterMap (fun (w,i) =>
    if forest != 0 && i+1 == forest then none else some (full ^^^ w)) |>.reverse

def target : Nat := 0xfffffffffffefffafffeffeefefeeca0

def forestTarget (forest : Nat) : Nat :=
  if forest == 0 then target else
    let v := forest-1
    let low := full ^^^ inputs.getD v 0
    (target &&& low) ||| ((target &&& low) <<< (1 <<< v))

def trailingZeros : Nat → Nat → Nat
  | 0,_ => 0
  | fuel+1,n => if n.testBit 0 then 0 else 1 + trailingZeros fuel (n >>> 1)

def gamma (n : Nat) : Nat × Nat :=
  forceNat (trailingZeros 512 n) (fun b =>
    forceNat (1 <<< b) (fun p =>
      (p + ((n >>> (b+1)) &&& (p-1)), n >>> (2*b+1))))

def readCuts : Nat → Nat → Nat → List Nat × Nat
  | 0,_,n => ([],n)
  | count+1,last,n =>
    match gamma n with
    | (gap,rest) =>
      forceNat (last+gap) (fun next =>
        match readCuts count next rest with
        | (cuts,rem) => ((next-1) :: cuts,rem))

def readDeps : Nat → Nat → Nat → List Nat
  | 0,_,_ => []
  | fuel+1,last,n =>
    if n == 0 then [] else
      match gamma n with
      | (gap,rest) =>
        forceNat (last-gap) (fun next => next :: readDeps fuel next rest)

abbrev CodeRow := Nat × Nat × List Nat × List Nat

def CodeRow.parentDelta (r : CodeRow) : Nat := r.1
def CodeRow.step (r : CodeRow) : Nat := r.2.1
def CodeRow.cuts (r : CodeRow) : List Nat := r.2.2.1
def CodeRow.deps (r : CodeRow) : List Nat := r.2.2.2

def codeRow (code index : Nat) : CodeRow :=
  match gamma code with
  | (parent,rest) =>
    forceNat (rest >>> 10) (fun rem =>
      match readCuts (rem &&& 15) 0 (rem >>> 4) with
      | (cuts,deps) => ⟨parent-1,rest &&& 1023,cuts,readDeps 512 index deps⟩)

def row (forest index : Nat) : CodeRow :=
  codeRow (getCode (forestCodes forest) index) index

def insert (w : Nat) : List Nat → List Nat
  | [] => [w]
  | x :: xs => if w <= x then w :: x :: xs else x :: insert w xs

def ordered : List Nat → List Nat
  | [] => []
  | w :: ws => insert w (ordered ws)

def pairIndex : Nat → Nat → Nat × Nat
  | 0,_ => (0,0)
  | fuel+1,n =>
    let i := fuel+1
    let base := i*(i-1)/2
    if base <= n then (i,n-base) else pairIndex fuel n

def op (o a b : Nat) : Nat :=
  if o == 0 then a &&& b else if o == 1 then a ||| b
  else if o == 2 then a ^^^ (a &&& b) else b ^^^ (a &&& b)

def applyStep (step : Nat) (ws : List Nat) : List Nat :=
  let keep := step % 4
  let o := step / 4 % 4
  let (i,j) := pairIndex 12 (step / 16)
  let a := ws.getD i 0
  let b := ws.getD j 0
  let rest := (ws.zipIdx).filterMap (fun (w,k) =>
    if k == i || k == j then none else some w)
  ordered (op o a b :: ((if keep.testBit 0 then [a] else []) ++
    (if keep.testBit 1 then [b] else []) ++ rest))

def highState : Nat → Nat → Nat → Nat × List Nat
  | 0,forest,_ => (0,roots forest)
  | fuel+1,forest,index =>
    let r := row forest index
    if r.parentDelta == 0 then (0,roots forest) else
      match highState fuel forest (index+r.parentDelta) with
      | (depth,ws) => (depth+1,applyStep r.step ws)

def normalize (ws : List Nat) : List Nat :=
  ordered (ws.map (fun w => if w.testBit 0 then full ^^^ w else w))

def node (forest index : Nat) : Nat × List Nat :=
  match highState 12 forest index with
  | (depth,ws) => (rootBudget forest-depth,normalize ws)

end PEqualNP.Outside.L_meta_10760.RestrictionData


namespace PEqualNP.Outside.L_meta_10760.AutoPool

lemma forceNat_eq {α : Sort u} (n : Nat) (f : Nat → α) : forceNat n f = f n := by
  cases n <;> rfl

lemma singles_eq_legacy (ws : List Nat) : singles ws = RestrictionSixProof.picks ws := by
  induction ws with
  | nil => rfl
  | cons a ws ih =>
    simp only [singles, RestrictionSixProof.picks, ih]

lemma pairs_eq_legacy (ws : List Nat) : pairs ws = RestrictionSixProof.pairs ws := by
  induction ws with
  | nil => rfl
  | cons a ws ih =>
    simp only [pairs, RestrictionSixProof.pairs, singles_eq_legacy, ih]

lemma op_eq_nb (o a b : Nat) : op o a b = RestrictionSixProof.nb o a b := by
  by_cases h0 : o = 0
  · subst o; rfl
  by_cases h1 : o = 1
  · subst o; rfl
  by_cases h2 : o = 2
  · subst o; rfl
  simp [op, RestrictionSixProof.nb, h0, h1, h2,
    RestrictionSixProof.nbeq h0, RestrictionSixProof.nbeq h1, RestrictionSixProof.nbeq h2]

lemma insert_perm (a : Nat) (ws : List Nat) : (insert a ws).Perm (a :: ws) := by
  induction ws with
  | nil => exact .refl _
  | cons b ws ih =>
    simp only [insert]
    split
    · exact .refl _
    · exact (ih.cons b).trans (.swap a b ws)

lemma ordered_perm (ws : List Nat) : (ordered ws).Perm ws := by
  induction ws with
  | nil => exact .refl _
  | cons a ws ih => exact (insert_perm a (ordered ws)).trans (ih.cons a)

lemma ordered_mem (a : Nat) (ws : List Nat) : a ∈ ordered ws ↔ a ∈ ws :=
  (ordered_perm ws).mem_iff

lemma ordered_mapW_set (ws : List Nat) :
    ((ordered ws).map RestrictionSixProof.W).toFinset =
      (ws.map RestrictionSixProof.W).toFinset := by
  ext w
  simp only [List.mem_toFinset]
  exact ((ordered_perm ws).map RestrictionSixProof.W).mem_iff

lemma singles_mem_perm {p : Nat × List Nat} {ws : List Nat}
    (hp : p ∈ singles ws) : (p.1 :: p.2).Perm ws := by
  induction ws generalizing p with
  | nil => simp [singles] at hp
  | cons a ws ih =>
    simp only [singles, List.mem_cons, List.mem_map] at hp
    rcases hp with rfl | ⟨⟨b, bs⟩, hb, rfl⟩
    · exact .refl _
    · exact (List.Perm.swap a b bs).trans ((ih hb).cons a)

lemma pairs_mem_perm {p : Nat × Nat × List Nat} {ws : List Nat}
    (hp : p ∈ pairs ws) : (p.1 :: p.2.1 :: p.2.2).Perm ws := by
  induction ws generalizing p with
  | nil => simp [pairs] at hp
  | cons a ws ih =>
    simp only [pairs, List.mem_append, List.mem_map] at hp
    rcases hp with ⟨⟨b, bs⟩, hb, rfl⟩ | ⟨⟨b, c, bs⟩, hb, rfl⟩
    · exact (singles_mem_perm hb).cons a
    · exact ((List.Perm.swap a c bs).cons b).trans
        ((List.Perm.swap a b (c :: bs)).trans ((ih hb).cons a))


end PEqualNP.Outside.L_meta_10760.AutoPool

namespace PEqualNP.Outside.L_meta_10760.RestrictionSixProof

lemma legacy_pairs_step {T k : Nat} {ws : List Nat}
    (ndW : (ws.map W).Nodup) (hTm : W T ∉ ws.map W)
    (check : ∀ p ∈ pairs ws, ∀ (o : Nat) (ja jb : Bool), o < 4 →
      W (nb o p.1 p.2.1) ∉ ws.map W → proper (W (nb o p.1 p.2.1)) →
      (kidW p.2.2 p.1 p.2.1 (nb o p.1 p.2.1) ja jb).Nodup →
      p.2.2.length + (bl ja + bl jb) ≤ k →
      Impossible true (W T) k (kidW p.2.2 p.1 p.2.1 (nb o p.1 p.2.1) ja jb).toFinset) :
    Impossible true (W T) (k+1) (ws.map W).toFinset := by
  apply enum_step ndW hTm
  intro a' ha' b' hb' d hd ka kb hab fresh hprop hlen
  obtain ⟨a,ham,rfl⟩ := List.mem_map.mp ha'
  obtain ⟨c,hcm,rfl⟩ := List.mem_map.mp hb'
  have hac : a ≠ c := fun h => hab (by rw [h])
  have hd4 : d < 4 := by
    rcases hd with h | ⟨_,h⟩ <;> omega
  obtain ⟨p,hp,perm,ho⟩ := pairs_ok ham hcm hac
  have core : ∀ (o : Nat) (ja jb : Bool), o < 4 → W (nb o p.1 p.2.1) = bin d (W a) (W c) →
      (p.2.2.length + (bl ja + bl jb) ≤ k) →
      Impossible true (W T) k (kidW p.2.2 p.1 p.2.1 (nb o p.1 p.2.1) ja jb).toFinset := by
    intro o ja jb ho4 hW hl
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
    exact check p hp o ja jb ho4 (by rwa [hW]) (by rwa [hW]) nk hl
  have rp : (((ws.map W).erase (W a)).erase (W c)).Perm (p.2.2.map W) := by
    have e : (W a :: W c :: p.2.2.map W).Perm (ws.map W) := by
      rcases ho with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
      · exact perm.map W
      · exact (List.Perm.swap _ _ _).trans (perm.map W)
    have e1 := e.erase (W a)
    rw [List.erase_cons_head] at e1
    have e2 := e1.erase (W c)
    rw [List.erase_cons_head] at e2
    exact e2.symm
  have lenr : (((ws.map W).erase (W a)).erase (W c)).length = p.2.2.length := by
    rw [rp.length_eq,List.length_map]
  have fits : p.2.2.length + (bl ka + bl kb) ≤ k := by
    have h := hlen
    unfold childTwo at h
    cases ka <;> cases kb <;> simp [kept,lenr] at h <;> simp [bl] <;> omega
  rw [Nat.add_sub_cancel]
  rcases ho with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · have r := core d ka kb hd4 (W_nb _ _ _) fits
    have e : (childTwo (ws.map W) (W p.1) (W p.2.1) d ka kb).toFinset = (kidW p.2.2 p.1 p.2.1 (nb d p.1 p.2.1) ka kb).toFinset := by
      unfold childTwo kidW
      rw [W_nb]
      ext v
      cases ka <;> cases kb <;> simp [kept,rp.mem_iff]
    rw [e]
    exact r
  · have hfl := flip_flip hd
    have f4 : flipOp d < 4 := by
      rcases hfl.1 with h | ⟨_,h⟩ <;> omega
    have r := core (flipOp d) kb ka f4 (by rw [W_nb]; exact (bin_flip hd _ _).symm) (by omega)
    have e : (childTwo (ws.map W) (W p.2.1) (W p.1) d ka kb).toFinset = (kidW p.2.2 p.1 p.2.1 (nb (flipOp d) p.1 p.2.1) kb ka).toFinset := by
      unfold childTwo kidW
      rw [W_nb,bin_flip hd]
      ext v
      cases ka <;> cases kb <;> simp [kept,rp.mem_iff] <;> tauto
    rw [e]
    exact r

end PEqualNP.Outside.L_meta_10760.RestrictionSixProof

namespace PEqualNP.Outside.L_meta_10760.AutoPool

open RestrictionSixProof

def rawChild (a b z : Nat) (rest : List Nat) (keep : Nat) : List Nat :=
  z :: ((if keep.testBit 0 then [a] else []) ++
    (if keep.testBit 1 then [b] else []) ++ rest)

def keepCode (ka kb : Bool) : Nat := ka.toNat + 2 * kb.toNat

lemma keepCode_lt (ka kb : Bool) : keepCode ka kb < 4 := by
  cases ka <;> cases kb <;> decide

lemma keepCode_bit0 (ka kb : Bool) : (keepCode ka kb).testBit 0 = ka := by
  cases ka <;> cases kb <;> decide

lemma keepCode_bit1 (ka kb : Bool) : (keepCode ka kb).testBit 1 = kb := by
  cases ka <;> cases kb <;> decide

lemma rawChild_map_keepCode (a b z : Nat) (rest : List Nat) (ka kb : Bool) :
    (rawChild a b z rest (keepCode ka kb)).map W = kidW rest a b z ka kb := by
  simp only [rawChild, keepCode_bit0, keepCode_bit1]
  cases ka <;> cases kb <;> simp [kidW, kept]

lemma rawChild_length_keepCode (a b z : Nat) (rest : List Nat) (ka kb : Bool) :
    (rawChild a b z rest (keepCode ka kb)).length = rest.length + (bl ka + bl kb) + 1 := by
  simp only [rawChild, keepCode_bit0, keepCode_bit1]
  cases ka <;> cases kb <;> simp [bl] <;> omega

lemma legacyNodeCheck_sound {R : List Nat} {T k : Nat} {negativeRows ws : List Nat}
    {specs : List SliceD} {deps : List (Nat × List Nat)}
    (hT : T < 2^128) (hAsc : asc ws = true)
    (hSpecs : ∀ spec ∈ specs, SliceN R T spec)
    (hDeps : ∀ q ∈ deps, Impossible true (W T) q.1 (q.2.map W).toFinset)
    (matrix_sound : ∀ a b rest o keep, o < 4 → keep < 4 →
      (∀ x ∈ a :: b :: rest, x < 2^128) →
      (phaseMatrix T negativeRows a b rest &&& collisionMasks.getD (4*o+keep) 0 != 0) = true →
      Impossible true (W T) k ((rawChild a b (nb o a b) rest keep).map W).toFinset)
    (auto_sound : ∀ child spec, SliceN R T spec → (child.map W).Nodup →
      autoCut k child spec = true → Impossible true (W T) k (child.map W).toFinset)
    (checked : nodeCheck T negativeRows k ws specs deps = true) :
    Impossible true (W T) (k+1) (ws.map W).toFinset := by
  have h := checked
  simp only [nodeCheck, Bool.and_eq_true] at h
  have out : T ∉ ws := by
    simpa using h.1
  obtain ⟨nd, ndW⟩ := asc_nodup hAsc
  have bounds := (asc_ok hAsc).2
  have outW : W T ∉ ws.map W := by
    intro hm
    obtain ⟨x, hx, he⟩ := List.mem_map.mp hm
    have eq := W_inj (bounds x hx) hT he
    exact out (eq ▸ hx)
  apply legacy_pairs_step ndW outW
  intro p hp o ka kb ho4 fresh properOut ndChild fits
  obtain ⟨a, b, rest⟩ := p
  have hp' : (a,b,rest) ∈ AutoPool.pairs ws := by rwa [pairs_eq_legacy]
  have perm := pairs_mem_perm hp'
  have parentBounds : ∀ x ∈ a :: b :: rest, x < 2^128 := by
    intro x hx
    exact bounds x (perm.mem_iff.mp hx)
  have pairChecked := List.all_eq_true.mp h.2 (a,b,rest) hp'
  simp only [forceNat_eq] at pairChecked
  have opChecked := List.all_eq_true.mp pairChecked o (List.mem_range.mpr ho4)
  simp only [op_eq_nb] at opChecked
  have newNat : nb o a b ∉ ws := by
    intro hm
    exact fresh (List.mem_map_of_mem hm)
  have nonzero : nb o a b ≠ 0 := by
    intro hz
    apply properOut.1
    rw [hz]
    rfl
  have nonfull : nb o a b ≠ full := by
    intro hz
    apply properOut.2
    rw [hz]
    exact W_full
  have skipFalse : (ws.contains (nb o a b) || nb o a b == 0 || nb o a b == full) = false := by
    simp [newNat, nonzero, nonfull]
  rw [skipFalse] at opChecked
  simp only [Bool.false_eq_true, ite_false] at opChecked
  have childChecked := List.all_eq_true.mp opChecked (keepCode ka kb)
    (List.mem_range.mpr (keepCode_lt ka kb))
  let child := rawChild a b (nb o a b) rest (keepCode ka kb)
  have hmap : child.map W = kidW rest a b (nb o a b) ka kb :=
    rawChild_map_keepCode a b (nb o a b) rest ka kb
  have childNodup : (child.map W).Nodup := hmap.symm ▸ ndChild
  have childFits : child.length ≤ k+1 := by
    dsimp only [child]
    rw [rawChild_length_keepCode]
    exact Nat.add_le_add_right fits 1
  change decide (k+1 < child.length) ||
    (phaseMatrix T negativeRows a b rest &&& collisionMasks.getD (4*o+keepCode ka kb) 0 != 0) ||
    deps.any (fun q => decide (k ≤ q.1) && ordered child == q.2) ||
    specs.any (autoCut k child) = true at childChecked
  rw [← hmap]
  simp only [Bool.or_eq_true] at childChecked
  rcases childChecked with ((tooLong | collision) | dependency) | cut
  · have bad : k+1 < child.length := of_decide_eq_true tooLong
    omega
  · exact matrix_sound a b rest o (keepCode ka kb) ho4 (keepCode_lt ka kb) parentBounds collision
  · obtain ⟨q, hq, hd⟩ := List.any_eq_true.mp dependency
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hd
    have eqSet : (child.map W).toFinset = (q.2.map W).toFinset := by
      rw [← hd.2]
      exact (ordered_mapW_set child).symm
    intro n hn run
    exact hDeps q hq n (hn.trans hd.1) (eqSet ▸ run)
  · obtain ⟨spec, hs, hc⟩ := List.any_eq_true.mp cut
    exact auto_sound child spec (hSpecs spec hs) childNodup hc

end PEqualNP.Outside.L_meta_10760.AutoPool
