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
def wordData : List (List (List Nat)) := [
[[49173,49175,49169,49171,40977,49165,49167,40973,32781,49161,49163,40969,32777,24585,49157,49159,40965,32773,24581,16389,49153,49155,40961,32769,24577,16385,8193,49170,24579,40978,49164,49166],
[40974,32782,24583,57361,57363,57357,57359,57353,57355,57349,57351,57345,57347,65555,65553,65551,65549,65547,65545,65543,65541,65539,65537,73751,73741,73743,73737,73739,73733,73735,73729,73731],
[41001,81935,81933,81931,81929,81927,81926,81925,81923,81921,49196,49198,90125,90127,90121,90123,90117,90119,90113,90115,98327,98323,98313,98315,98309,98311,98305,98307,41013,32821,106507,106505],
[106503,106501,106499,106497,49208,49210,114707,114697,114699,114693,114695,114689,114691,49212,49214,41022,122889,122891,122885,122887,122881,122883,131095,131091,131087,131077,131079,131073,131075,41029,32837,24645],
[139271,139269,139267,139265,49224,49226,147475,147471,147461,147463,147457,147459,49228,49230,41038,155663,155653,155655,155649,155651,49232,49234,41042,32850,163845,163847,163841,163843,172055,172051,172047,172043],
[172033,172035,41049,32859,32857,24665,16473,180227,180225,49244,49246,188435,188431,188427,188417,188419,49248,49250,41058,196623,196619,196609,196611,49252,49254,41062,32870,204811,204801,204803,49256,49258],
[41066,32874,24682,212993,212995,221207,221203,221199,221195,221191,41073,32881,24689,16497,8305,49268,49270,237587,237583,237579,237575,49272,49274,41082,245775,245771,245767,49276,49278,41086,32894,253963],
[253959,49280,49282,41090,32898,24706,262151,49284,49286,41094,32902,24710,16518,57358,90124,41109,32917,303109,303105,311317,311297,49309,319489,49313,41121,327681,49317,41125,335873,237582,49293,41101],
[32909,344077,344079,344073,344075,344069,344071,344065,344067,344072,344074,16391,344064,344066,16384,16387,16386,8194,352269,352265,352261,352257,360467,360457,360459,360453,360455,360449,360451,32776,32779,32778],
[32768,32771,32770,32949,368649,368645,368641,376851,376847,376837,376839,376833,376835,32957,24765,385029,385025,57422,57426,393235,393228,393231,393227,393217,393219,32965,24773,16581,401409,57442,57450,409619],
[409615,409611,409607,409618,409610,32775,32973,24781,16589,8397,57466,57474,57478,425997,425993,425989,434189,434185,434181,434177,442377,32990,450569,450571,450565,450567,450561,450563,458765,32998,24806,466949],
[466951,466945,466947,65618,475153,475149,475145,483329,491533,491529,507917,507913,507909,507905,516119,516105,516107,516101,516103,516097,516099,41217,524297,524293,524289,532503,532495,532485,532487,532481,532483,40972],
[40975,41225,24841,540677,540673,73810,548887,548879,548875,548865,548867,41233,24849,16657,557057,565271,565263,565256,565259,565255,41241,24857,16665,8473,73847,581645,581641,581637,581633,589833,589829,41254],
[598025,598027,598021,598023,598017,598019,606221,606213,41262,24878,614405,614407,614401,614403,82002,622605,622601,638977,647181,647177,647173,663565,663561,671757,671753,671749,671745,98351,90165,49486,679945,679947],
[679941,679940,679943,679937,679939,49489,688137,688133,688129,131119,90181,49494,696335,696325,696327,696321,696323,49497,24921,704517,704513,90194,90201,49502,712719,712715,712705,712707,49505,24929,16737,720897],
[221230,90225,49508,49510,729103,729099,729095,49513,24937,16745,8553,745489,745483,745481,745479,745477,745475,745473,41329,753675,753673,753671,753669,753667,753665,761879,761875,761861,761863,761857,761859,41337],
[33145,770055,770053,770051,770049,778263,778259,778251,778241,778243,41345,33153,16769,786435,786433,794647,794643,794635,794631,41353,33161,16777,8585,811017,811013,811009,819209,819205,819201,41370,33178,835589],
[835591,835585,835587,33181,843785,851969,860169,876561,876553,876549,876545,442385,442369,884753,884745,884741,884737,49589,892937,892933,892929,131131,114757,49594,901139,901125,901127,901121,901123,49597,33213,909317],
[909313,114777,49602,917523,917515,917505,917507,49605,33221,16837,925697,221242,114801,49610,933907,933899,933895,49613,33229,16845,8653,950281,958485,958473,958469,958465,49625,966665,966661,966657,131135,122949],
[49630,41438,974853,974855,974849,974851,49633,41441,983045,983041,122969,49638,41446,991243,991233,991235,49641,41449,16873,999425,221246,122993,237630,49646,41454,1007627,1007623,49649,41457,16881,8689,24580],
[24582,1024017,1024013,1024007,1024005,1024003,1024001,40967,41465,1032205,1032199,1032197,1032195,1032193,41469,33277,1040391,1040389,1040387,1040385,1048599,1048595,1048591,1048577,1048579,41477,33285,25093,1056771,1056769,1064983,1064979],
[1064975,1064967,40964,40966,41485,33293,25101,8717,1081349,1081345,1089541,1089537,41498,33306,1097733,1097735,1097729,1097731,33309,25117,1114113,25125,1138705,1138701,1138693,1138689,458757,1146897,1146893,1146885,1146881,49717],
[1155085,1155077,1155073,49721,33337,1163269,1163265,147545,49726,1171475,1171471,1171457,1171459,49729,33345,25153,1179649,147569,49734,1187859,1187855,1187847,49737,33353,25161,8777,1204237,41257,1212437,1212429,1212421,1212417],
[49749,1220621,1220613,1220609,49753,41561,1228805,1228801,155737,49758,41566,1237007,1236993,1236995,49761,41569,25185,1245185,155761,237646,49766,41574,1253391,1253383,49769,41577,25193,8809,41581,33389,1269765,1269761],
[1277973,1277969,1277959,1277957,1277955,1277953,49781,1286161,1286151,1286149,1286147,1286145,49785,41593,1294343,1294341,1294339,1294337,163931,163929,49790,41598,33406,1302529,1302531,49793,41601,33409,1310723,1310721,163955,163953],
[49798,41606,33414,1318919,49801,41609,33417,8841,1335313,1335309,1335305,1335297,41617,1343501,1343497,1343489,41621,33429,1351689,1351681,41625,33433,25241,1359873,1368087,1368083,1368079,1368075,41633,33441,25249,17057],
[172151,1384449,1400833,41650,33458,1409035,1409025,1409027,41654,33462,25270,1417217,1417219,33465,25273,17081,1441805,1441801,475137,1450001,1449997,1449993,1449985,49865,1458189,1458185,1458177,49869,33485,1466377,1466369,49154],
[49873,33489,25297,1474561,221278,188529,49876,49878,1482771,1482767,1482763,49162,49881,33497,25305,17113,1499149,1499145,1507349,1507341,1507337,1507329,49893,1515533,1515529,1515521,49897,41705,1523721,1523713,49901,41709],
[25325,1531905,221282,196721,237666,49906,41714,1540111,1540107,49909,41717,25333,17141,1556489,843777,1564693,1564689,1564681,1564673,49921,1572881,1572873,1572865,49925,41733,1581065,1581057,49929,41737,33545,1589249,221286],
[204913,237670,49934,41742,33550,1597451,49937,41745,33553,17169,25365,1622037,1622033,1622029,1622017,49949,1630225,1630221,1630209,49953,41761,1638413,1638401,49957,41765,33573,1646593,213105,237674,49962,41770,33576],
[33578,25386,49965,41773,33581,25389,409614,409606,32774,1671185,1671181,1671177,1671173,41781,1679373,1679369,1679365,41785,33593,1687561,1687557,41789,33597,25405,1695749,1368084,1368086,40979,1368076,1368078,41793,33601],
[25409,17217,41806,33614,1728523,1728519,41810,33618,25426,1736711,32780,32783,24584,24587,24586,49158,32772,16388,16390,1753105,1753101,1753097,1753093,491537,491525,1761297,1761293,1761289,1761285,50017,1769485,1769481]],
[[1769477,50021,33637,1777673,1777669,50025,33641,25449,1785861,49160,50029,33645,25453,17261,1802253,1802249,41277,1810453,1810445,1810441,1810437,50041,1818637,1818633,1818629,49174,50045,41853,1826825,1826821,50049,41857],
[25473,1835013,50053,41861,25477,17285,41865,33673,1851401,1851397,33189,1859605,1859601,1859593,1859589,50065,1867793,1867785,1867781,50069,41877,1875977,1875973,50073,41881,33689,1884165,50077,41885,33693,17309,41889],
[33697,25505,1900549,41509,1122309,1908757,1908753,1908749,1908741,50089,1916945,1916941,1916933,50093,41901,1925133,1925125,50097,41905,33713,1933317,50101,41909,33717,25525,25529,17337,1957909,1957905,1957901,1957897,50113],
[1966097,1966093,1966089,50117,41925,1974285,1974281,50121,41929,33737,1982473,50125,41933,33741,25549,778260,172091,221259,57505,57509,57485,65701,90263,50133,90203,90255,2015249,2048001,49608,2064385,2064387,319601],
[2080791,2105367,2105345,2105347,2113537,335985,2138135,2162695,2170881,2179075,2195471,2211851,2179072,2236441,2195459,2203649,345163,345161,58441,42057,2211848,17485,17487,9293,2261021,2261017,2261013,345173,345175,58453,50261,42069],
[33877,9301,345183,345181,58461,50269,42077,33885,345187,345185,58465,50273,42081,33889,58513,50321,42129,2392069,2392065,2392066,58517,58521,42137,58525,50333,42141,17565,17567,9373,58529,50341,42149],
[33879,58457,42073,33973,33975,17589,17591,9397,409662,2482177,2490383,2498561,57350,57950,57953,409682,2605071,57354,57346,34061,17677,17679,2654209,58093,409697,409698,58098,58101,2662417,2662401,409706,58154],
[409612,2211847,24578,2670597,2375699,409616,409608,34077,2506759,409604,2686981,2605075,2605068,40971,34085,2703385,2703381,2711577,410769,410773,410929,58673,410697,25922,58241,58245,58261,58265,58293,2777105,58317,2834443],
[66453,3022851,3039235,3055619,3096587,3112961,40963,50713,3194885,3194881,3252227,3276811,3432453,82497,1482795,82797,26373,729143,3710983,221518,3751943,3768321,51006,18237,729159,3825665,51057,729179,3915777,221534,51078,51098],
[221198,3989509,4005901,4014094,4014093,4014085,51117,4055047,4136961,4194307,4243457,40962,4317207,43101,43105,43118,43122,237586,237578,4456465,4456453,4481035,107073,1482807,1769525,107373,4603913,4603905,34158,2842625,2842627,443545],
[443481,4620295,4653057,51466,4710401,35085,114985,221202,221194,51541,4890633,35161,115005,115237,51464,4988931,238046,221670,5201941,5201925,51701,5259287,51737,43545,35353,5292033,5316611,5332995,5414913,5464067,5488659,34329],
[5505025,3194886,51877,35493,27301,27303,5578753,43547,237574,5627919,5636113,5636101,1482823,1769541,140141,1876037,5849089,52014,52022,35637,11061,5914643,5931025,5931009,5931011,1179761,52062,27485,5988357,52081,27505,42678],
[6127617,762479,6397955,52293,6447127,52309,238206,35962,6553603,52365,6643735,6774785,44297,44306,44314,6881297,1769561,1876057,2990081,2990083,476249,36213,19829,19831,221897,221901,52630,5890049,52045,7176207,7184393,7192593],
[7192586,7192585,52677,188965,7282689,7315459,221925,221929,3276823,7413781,52781,7438357,7471127,4546561,4546563,221957,7626753,44721,205349,7782403,53005,7938071,7970841,409761,221345,7979117,7979033,7979009,413501,225085,412185,223769],
[412189,223773,7995403,222745,222749,50717,3203073,221206,223801,51769,5357569,8028173,8028174,8028165,223909,8093713,8093709,8093710,8093701,8093702,8126481,8126477,8126478,8134681,8134657,44289,1372043,1372041,225161,53129,8142853,8142849],
[4317204,8159257,1369625,1369627,1369631,1369629,3203077,1368227,1368225,2703477,2703374,2703373,2703361,278549,7970837,413637,53189,241605,44997,8265729,413641,241609,45001,237729,2711553,238737,25745,25747,2392070,238741,42133,413645],
[53197,241613,45005,8282113,413649,241617,8290305,413653,241621,45013,7979125,7979029,7979018,7979017,8306689,413661,53213,241629,45021,28637,28639,20445,20447,8314881,238897,42289,241469,7987201,240153,35355,18969,18971],
[240157,5300225,413665,53217,241633,45025,8323073,238665,413669,241637,8331265,237717,303113,8421389,8421390,8421381,7225461,7225365,238745,53286,53310,241729,45121,36929,28737,8519681,8527889,8527881,8527882,319805,42726,8585229],
[8585230,8585221,5226517,51709,53402,8863767,8863749,53486,8871945,53502,8904721,8904709,53510,320037,43762,5734407,1122469,37182,6619141,44201,9191433,37286,53678,53710,9330701,51506,51526,53806,2180163,2212943,2376851,2393229],
[2393269,35357,2245813,10043400,10043403,369613,2509339,2581589,7225361,7225345,50329,2408449,7127057,7127049,2433033,50265,33881,10158097,10166289,10166281,54126,2216863,2216871,7972121,2380727,2679953,2712861,2511811,2689561,7980321,2610131,10118433],
[9920515,10159397,10452995,29749,3196513,8650765,8650757,311301,319493,27193,3769429,3769437,688957,46249,10829825,10895369,4408465,11026443,17713,2719745,50325,5294645,5548569,51741,11763719,46713,13945,46749,11853825,11878415,10806553,11126045],
[12091415,12124183,12173325,12173317,10805253,55114,8093857,2400261,12263436,12263439,8096281,2609027,4321167,2131225,10945821,10954013,2131233,11396385,10954021,13008919,8455313,8489497,13123587,13164561,13164545,13172755,44861,7987213,9324057,9324061]]]

set_option maxRecDepth 100000 in
def data0 : List (List (List Nat)) := [
[[0x4c0c20000141919f8,0xc9430000140099f9,0x92860001815f9,0x34824880001915f9,0x1ec51a24e0000095fa,0x74020a438fd8,0xb8f0c808ff9,0xa830a440ff8,0x770a830c810ff9,0x70cc608c8117f9,0x7c07020460502a19f7,4811909635319,0xf610818608c2a15f8,0x3e0a3046014049bf8,0x6c060a0641c0297f8,0x78c40148417f8,0xa0082300a0500b21e7,0x14b20f0430460140a1bf8,0x9f031c640460140b1df8,0x47810460140b9ef8,0x14ebdc3821844c08c0297f9,0x70cc608c0416f9,507811815,77914445799,0x723820e448fe8,0xae282114818ff9,818109875359737,0x12150c2214cc08c0497f9,0x54144608c0595f9,0xd0f83810808c0697f9,0x74020a450f78,396140143087609],
[4956535066617,695306014888953,0x6278608c0717f9,0x4410408c0793f9,0xc483810808c0917f9,0x6c060a0641c0f97f8,507877303,78048663479,0x723820e458fb8,0x3c34422698838ff9,8176261059811320,0x5c0c30880508417e8,0x150e211394840ff9,0x14010460510799f7,0x26058720230b40500b21e7,0x3340b0e40461680a1bf8,0x58718230281ac0b21e7,0x5e44e60460500b19e8,0x28610840460500c1be8,0x5d8c89cc08c0a13f9,0x12038318ce60460500b1de8,0x110463238a19cc08c0a17f9,0x64c10608c0a93f9,0x240420460ac0b1df8,0x410460592699f7,0x11f14e40461ac0b1df8,0x3030c30460580c1de8,0xf86cbd8cca08c0b15f9,0x2603089ca08c0b96f9,0x46a3810608c0c17f9,0xae24f5f66e2b3c43384c26a4118ffa,2521077735],
[0xf0a0440c1297f8,717158950770680,0x1b8123046094059df8,2521143223,8748144478296056,0x78c40948417f8,0x3f0082304a0500b21e7,0x1c82c80a130460940a1bf8,0x99078d40460940b1df8,0x7a0dc0420460940b9ef8,0x10582046094909ef8,0xa520d57d3820c6c08c1297f9,687702581606,0x1e682190300001403a177,0xd02100000a01c822177,0x5102304e01403a177,687702647094,0x7c5190700001403a177,0x1e3100000a01c842177,0x60082305601403a177,0x1e041180000a01c0ba877,0x35f4423b02300001403a178,0x50d01000016449be7,0x31841cd044206000029bf8,0xa1e042000014821bf8,0x143e0a304609c029bf8,0x11f05202300001405a1f8,0x1c681000016459bb7,0xa2619a520e000029bf8,0x28080000a0588421e7,0x1c6e023c64000014841bf8,0x9010530460ac029bf8],
[0xdc082a0230000140b21f8,0xb0e3c10230000140ba2f8,0x2e97f288477046000029bf9,0x1e150100001e449de7,0x1a1e67044206000039df8,0x3c1c78200001c821df8,0xf0a204609c039df8,0x7828100001e459db7,0x342619a520e000039df8,0x28080002801c8421e7,0x3c341050300001c841df8,0x22010530460ac039df8,0x378aa02300005003a1f8,0x98382102300001c0ba4f8,0xf1a5e28288477046000039df9,77921163239,0xec260440c7697f8,20707579750,0x26120440c9a1777,77923522406,0x760240c9a9777,39585208113127,0x166120440c1497f8,0xd0100003a449be7,0x1640602044206000071bf8,0x78589144b2062860024497e8,0xf0b1228b91c70488185b240c0017f9,0xec0382c23046000e59bf8,53352375,0x1a822206000849fb8,0x6858d14046002461fe8,0x1870783046002449fe8],
[0x1748542478420608c001ff9,0x3a04204609c849fb8,0x161102300002c84a5b8,0x26e2c23046000849ff9,0x3a0b044107697f8,20678055799,17458435959,8224624613660664,0x1e042000038821bf8,0x1e16160a37c56220628c0008217f9,78190353335,0x68ca01000410851fb8,0x1c382c24046000821ff9,0xc81ac22046002469bf8,0x60a382c23046000851ff9,0x6b1484141397f8,989837968742392,0x187412404609c071bf8,0x8162e1a3985190f5008c1397f9,0x66712520a000059df8,0x1c150200002c831df8,0x260104602c9a9d77,0x88a30460a4059df8,0xc18e1c202300003805a1f8,776478135,0x361102300002c85a5b8,0x2208806155b83811aa8046000059df9,0xac01000050c319f7,0x5e024c0904000c315f8,2339386103783,0xac01000052471be7,0xbc0100005a471de7],
[0x3a440c8280024717f8,0x20e064e084141597f8,0x2e4143821050000500b21e7,0x313e82870320a0000a1bf8,0x19440902424520a0000b1df8,0x10c12bd11cf08e4140017f9,0x510030382046000c31df8,0xd407070438520a08c001ff9,319136144234488,0x2b008000280588321e7,0xd601000050831bf8,0x21c1502000058831df8,0x850a8280024797f8,0x106197c8c410a0008317f9,0xa1e09c4046000831ff9,78057740086,5840760865462135,17726871415,9854374450471270,0x2410460509a9b77,0x5b010460589a9d77,0x4104605c9a9e77,0x2878b857d237870a08c9a9778,20707645238,0xac120441c9a1777,0x8400a64597b7,0x11ac120441c1497f8,6254317694883703,0xa363840a48417f8,0xe043c318230520500b21e7,0x2888530460a40a1bf8,0x3083008540460a40b1df8],
[0x701804630460a40b9ef8,0xbc0187804044b943c08ec08c1497f9,0x68100003a459bb7,0x560e184420e000071bf8,0x48080001c0588421e7,0x6e14b1c4000038841bf8,0x61d0d40460ac071bf8,0x378ce3c20230000380b21f8,0xa0e3c18230000380ba2f8,0x40c51902f28782336046000071bf9,0x6f1503046000609ef8,0xaa6f1505046000099ff9,0x520420024817f8,4613935732728,4855720613320696,0x2c22046002499df8,0x1383ec22046000859ff9,9288752898874295,0x2a80000122cf19bb7,17732574183,0x14407f818220e000f19bf8,78055380919,0x250b40441c7697f8,78660247463,0x534120e0024a1fb8,0x88484a01838132062860024597b8,0x418120e002459fb8,0x4218120e000841fe8,0xf199070000500b21e7,0x1b0b420e0000a1bf8,0x2b0b420e0000b1df8,0x221212806060975a7151e17125441c0017f9],
[0x5602c38d13046000f19bf8,0x514e230460024a1fb8,0x1870783046002459fb8,53385191,0x6e1220e000861fe8,0x19a9a0a18320e08c001ff9,0x78f0430460ac861fe8,0x6890230000524aa3a7,0x1e13c18230000508623e8,0x68902300005a4ba5c7,0x45013c18230000588625e8,0x882300005e4aa6a7,0x882300005e4ba6c7,0x3882300005c8626e8,0x26d120460024a9fb8,0xd120460024b1fb8,0xc4d120460024b9fd8,0x496fb87084516046000861ff9,294961718663160,0x8f00cd1501088c0ac8417e8,0x9700b0b040ac8417f8,0xc803c06194000050841be8,0x88000280588421e7,0x1d2000050841bf8,0x4f02904c6c22197000058841de8,0x6d12000058841df8,0xc41200005c841fe8,78928680935,81478818791,81545928167,0xf1000420911fe8,79264225255],
[79331335143,79398444519,79465553639,0x1f1000438841fe8,0x2e036142000420879fe8,0x1309094030d021c3ae467cac061c44500008417f9,78995790823,79062900199,0x220e30000420869fe8,0x4b800c120460ac841fe8,0xe3c10230000508423e8,0x683c10230000588425e8,0x170a8102300005c8426e8,0x6c1fb838d14046000841ff9,0x14a00e1a408e4c17f8,0x244018d120460024c9bf8,0x24c018d120460024d1df8,0x260a7d12046000869ff9,0x22010460ac0b9ef8,0x22010460ac909ef8,0xd088245a0e7401058ac0c74304987cf5808c1597f9,0x3903890f866030507023fd8230000500b21e8,0x8804118000280580ba8e7,0x2a00828c6a0230000500b21f8,0x150c10230000500ba2f8,0x7050c18230000500ca3e8,4785075985128423,0x1c16118230000525321e7,0x31c16118230000508823e8,0xb05e0e243e0e2c238385e98d82a7fb0460000a1bf9,0x46890230000580ba4f8,0x1e3408e20230000580d25e8],
[4785076119543271,0x6c3c10230012ac0b21e7,0x64902300005888a5e8,0x3088090389010f091a25050b9db838e9aaa0460000b1df9,0x7409182300005c0ca6e8,0x150902300005c8826e8,0x78c70e202300005c0d26e8,0x882300005c88a6e8,0x2212138020b07c294a53e180863660460000b9ef9,0x1c3070518440460000c9ff9,0x2822726c0017f8,459870776989688,0x6c0301022808e4e97f8,0x360541140460024f1bf8,0x360541140460024f9df8,0x36054114046002501ef8,0xd12046002509fd8,0xf07f140911186046000871ff9,0x1d018223046000879ff9,0x4c220025117f8,0x3702328c0017f8,0x80204608e5217f8,0x1c1634046002529bf8,0x1901c1634046002531df8,0xd12046002539ef8,0x31a3fc382c24046000881ff9,0x3890a18d5040460000d1ff9,0x5c220025417f8,2416523089912,0xf0140408e5517f8,0x1b0d12046002559bf8,0xd12046002561df8],
[0xd12046002569ef8,0x6243fa2514046000889ff9,0x7848914d4c8821c2a4e02133c52424041318a3223cf2a2e0e1512f408c0017fa,0xf601638e0c890ff9,0x510074044602c1215f9,0xb200e8110c898ff9,0x12c037860381213f9,0x5100c2088a0ff9,0x5e00b070c550280581219e8,0x158048c4cca0501213f9,0xd802268cca0581215f9,0x45002719908a8ff9,0x2c03d7504e3298120ffa,0x1c02040941d17f8,0x3b02204a008049bf8,0x3b02204a008061ef8,2496206775,0x178020460941f17f8,0x1d0041304a0080a1bf8,0xf41204a0080b9ef8,0x2c002806bf3c08ec0940117f9,0x28080007401403a177,0x840000200a01c062877,687677710646,0xf1100007c01403a177,0x440000200a01c0ba877,0x402b2c0b0da80000401403a178,0x141e0220000e8029bf8,0x53c08000040140622f8,0x1053056008029bf8,0x391000014c91bb7,0x14b1230000f8029bf8],
[0xe33418000040140b21f8,0x10e3c10000040140ba2f8,0x1e203af10e108637000008029bf9,0xd04c010000e8039df8,0x20881180000402403a1f8,0x1e14080000401c0624f8,0xf1100001cc91db7,0xd1e220000f8039df8,0x31ca8180000405003a1f8,0x414080000401c0ba4f8,0x6c8031afcf0635000008039df9,3902445431,0x3e802040a41d17f8,0x281c20000e8071bf8,0x21814e0340831e3143080001d17f9,0x1c10040249a9b77,0x24263052008049bf8,0x5c1c20000f0049bf8,0x1a123a818a1326000008049bf9,0x1c10040309a9e77,0x4462052008061ef8,0x2408e18000040380622f8,0x160c78f18a184000008061ef9,26987894582,5840747376580471,0x1c10040509a9b77,0x1c100405c9a9e77,0x1ac0108cf23787080089a9778,0x326020a4c917b7,0x4bc3e1480a41f17f8,0x608530520080a1bf8,0x188804630520080b9ef8],
[0x11402b802138bcc3c08ec0a40117f9,0x8812040ac1e17f8,0xac01000050c51be7,0x66188086000c517f8,0x56008000780500b21e7,0x67805b120000f00a1bf8,0x28876020000f00b1df8,0x3d80626400412c301244a0001e17f9,0xd16294056008071bf8,4785075556785079,0xb1230000f8071bf8,0xa1e1c18000040380b21f8,0x141c08e20000040380ba2f8,0x1440248010705e850f188b8000008071bf9,0x6b80260120e53c5121213d20ac0117f9,0xd021a16284514308000c917b8,0x1b40650340868586787828894e0001f17f9,0xa04000020281480b28e7,0x5701982f8163b0b08b30000040500b21e8,0x3540560683439625071449670000080a1bf9,0xcd0210000041480b24f8,0x181c10000040580d25e8,0x11c00b03b01a06717611650000080b1df9,0xa070e180000405c0d26e8,0x1b201706810d0b0e250a22650000080b9ef9,0x7042000008751ef8,0x25f1bc3840000080d1ff9,0x4801434082108a394ad92b811af00000117fa,4790160653426168,4790179108363768,4790161391623672,4790161525841400],
[4790178034621944,0x1f914838a2a0942a15f9,0x3d803f0120e088b0ff9,0xf85088b8ff9,321117668249593,9574824619513848,81100255029729272,9574824619677688,0x808250120500ca3a7,0x3d0041304a0240a1bf8,0x17e0104a0240c9fb8,0x2ac05ad208c6a0940497f9,0x1c02040944697f8,0x1c020446c0617f8,35340874782695,0x4e1e260308e17f8,0x7002040944917f8,4790161460797287,0x1b1c040944997f8,0x2501805c0ca6a7,0x3104a0300b9ef8,0x41c1204a0300c1f78,0xd104a0300c9fb8,0x8d8010aa5fc58482909f60940617f9,0x9063864640c97f8,950134381679607,950134381712887,61728986502903,0x3860e13884648717f8,0xc24044648797f8,0xc187064648817f8,87029132857337],
[0x6c12040648d17f8,79331922935,79399032311,79466141431,0x1d1a07064388d17f8,0x6c120443c8d17f8,0x6c12044688817f8,0x93a340e0c8d0ff9,0x98021c304a0380c9bf8,0x2582466c0940713f9,0x190104a064079bf8,0xcb04c6a0940793f9,0x304707080940897f9,0x653a060946217f8,0x1241252a0940997f9,1194266615,0xd40246e5793f7,0xd40246e5815f7,0x684446e5897d7,0x684446e5917e7,0x3e61c64846c8e97f8,0x881c020646c8f17f8,0x6204446c8f97f8,0x1e0f28382548d8ff9,80472839159,80539948535,80607057879,1194299383,4616159631335,0xff0c684748e17f8,0x3a0b044708f17f8,0x620444708f97f8],
[0x4414f28314548e0ff9,0x3307e0104a0500c9fe8,0xa9033a051482884a0940a17f9,0xf014040946b17f8,0xb802040946c97f8,0x2502104a05c0c9fe8,0x8b805023e0ee09040a21740940b97f9,0x94061e0236c0940c1779,81100255033104376,0x7432040947217f8,0x7094a210213c09bc7062ef1760940c97f9,0x182e0a080947617f8,0x49048c4a0940d17f9,0x27400d81f9204084a8c1844e5886489be8128ffa,4785075412147704,0x808000280642a21e7,0x1cb00885130000502a19f8,0x39a01100005c2a1df8,0xc1010000642a1df8,0x42256006c05e88c6a0002a15f9,0xe7e0104a09c3b1df8,22267603163128,0x78c40949597f8,0x1f024040949617f8,0x3f0082504e0500b21e7,0x78902504e0500ca3a7,0x6c80a1304a09c0a1bf8,0xcc80a1304a09c0b1df8,0x6f41204a09c0c9fb8,0x7e0104a09c879fb8,0x63802303efd44a2a0941397f9,0x1008250012bc05a1b7],
[0xe8082500002e58a597,0x10082500002e5925a7,0x1cc34010182500002c8ea5b8,0x7c010102500002c8f25b8,0x320182304a0ac059df8,0xa008250000504521e7,0x1f8041280002802c0ca9a7,0x1b2038102500005005a1f8,0x6f404204a000451df8,0xd0d0204a000459df8,0x13707182500002c0ca5b8,0x305182500002c87a5b8,0x30201efe11ce504a000059df9,0x78c40949897f8,0x15d00f84448704404a000061ff9,0xc0440965717f8,0xc2c2204a002579bf8,0x2c2204a002581df8,0x142c2204a002589fd8,0x142c2204a002591fe8,0xd1204a002599fe8,0x58fcf010c2404a0008e9ff9,0x628c60965a17f8,0xe13078158404a0008f1ff9,0xc0440965a97f8,0xa204a0025b1df8,0x6382c2304a0008f9ff9,0xa40949f97f8,0xa4094a097f8,0x12700f868786ca884c0941597f9,0x3f0082500005069a1e7,0xb2805898442898250000500b21e8],
[0x6405098250000500b21f8,0x1448dc3f008250000500ca3e8,0x88250000525321e7,0x4c56098250000508823e8,0x15300516221a88a8304a0000a1bf9,0x723068204a000699df8,0x2ce0161e1659b84404a0000b1df9,0x78c4094a517f8,0x654402d0698f02304604a0000b9ff9,0x78240965b97f8,0xd1204a0025c1bf8,0xd1204a0025c9df8,0xd1204a0025d1fb8,0xd1204a0025d9fb8,0xd1204a0025e1fd8,0x3f3c0451404a000901ff9,0x628c60965e97f8,0x39a013078158404a000909ff9,0x70a040964c17f8,4790159885147128,4790159885180408,0x1cc1e0d1404a000911ff9,0x440a04094a597f8,0x25242782c390e12504a0000c9ff9,0x78240964e97f8,0xd1204a0024f1bf8,0xd1204a0024f9df8,0xd1204a002501ef8,0xd1204a002601ef8,0xd1204a002509fd8,0x3f3c0451404a000871ff9,0xc0440966097f8],
[0xa204a002611df8,0x1a2906ac2304a000879ff9,0x70a040965217f8,4790159884327928,0x141104a002531df8,0x3e1cc1e0d1404a000881ff9,0x2a200e342e2db897111731244b9f00940017fa,0x87f007198c918ff9,0x2b0126020931778,0x6a01010098721e77,0x5b0582010064131f78,0x56c0236a020131779,0x381f062481317f8,0x290f0624c1317f8,0x7008100c02e0641326a7,0x270f1301805c131ef8,0x1c02040309317f8,0xc70f13018064131fb8,0xac057385584f20301317f9,0xc20061a0890920ff9,0x48161c301c064131bf8,0x17012c0c66a0381313f9,0xe36030c80449317f8,0xa80a8082530cc0441317f9,0x9063860649297f8,61789422392311,61789489501687,61789556610807,0x3860e13884948717f8,0xc24044948797f8,0x120612064948817f8,0xcc013920670c928ff9],
[0x3c158c804c9317f8,0x653a063101317f8,0x2501cc1c18ec04c1317f9,0x12a0f063641317f8,0x68440102302e064131fe8,0x1340c90c102924f205c1317f9,35402284209143,35402351318519,0x68452c49317d7,2268073975,0x68452c89317e7,0x1f3110b14a4749317f8,0x880c158ca4988f17f8,0x620444988f97f8,0x14e828c8498a297f8,109598414711,404777468958584,30185426935,0x1682b14a4988597f8,109732632503,19783620535,0x730f0530c9317f8,0xd0da2849a6217f8,85832632538175480,85832570358667256,0xd81c2731c9317f8,0x6300451438e96fb3a0950964930ff9,0x2507432040987217f8,0x10404cc490f0dc021984f00641317f9,53645303,0x1e8f063b01317f8,0x25019161c18ee0681317f9],
[0xd40272908d960b5509d8130ffa,0x14080000a0302a21f8,0x41e3180000a47c2a21f8,0x14080000a05c2a21f8,0x31e3180000a0642a21f8,0x3a3180000a43c2a21f8,0x20200fc8082e0a850000142a19f9,0x2080000a01c93a177,0x1e3112b00001403a177,0xe0080000a01c962177,0x2082705601403a177,0x1a041380000a01c0ca937,0x438803f4423b02700001403a178,0x2c2000014339978,0x1a382000014341978,0x1e3100000a01c98a177,0x88000b401c062177,962880971127,694375817591,688003621239,687669322103,687669354871,0x280701805c0cb026,0xc40000500e0300ba877,0x1440000500e0300ca937,0x10a00fd758299d400000a01c062178,0x2900a01c0ca177,0x1640634052014039978,0x500e064152177,0x364063400a01c151978,0xb001c0ca177,0x10c0634000160039978],
[963753320823,0x6c0c063500001c2c9978,0xc11c1c200000a01c08a178,687670960503,0xe84a00000a01c09a178,687674990967,0x14080000a01ca0a177,0x4358015c3a231a82b00001403a178,0x220411b5000168039978,0x3c24463500001c2d9978,0x886811b5000014359978,0xf0e84635000014361978,0x347180000a01ca52177,0x8080000a01c6ca177,0x220840000500e05c0ca967,0xc408032c3d60d2bc00000a01c0ba178,0x347180000a01ca5a177,0x350080000a01c722177,0xc608925a1710f1e38bc00000a01c0ca178,0x42028100000a01c762177,0x3cda00000a01c0d2178,0x37803709255bc9958b4f8000014039979,0xad6004c0c20000143b19f8,0x4203810270000143b21f8,0x8c041000014939bf8,0x460c868e4256000029bf8,0x28080000a0589621e7,0x460b8bc13000014961bf8,0x4a0f04204e0ac029bf8,0xdf0a04320270000140b21f8,0x4e010083418270000140ca3b8,0x219c00a83af940217604e000029bf9],
[0x58a100000a02c06a138,0x5c010001604519f7,0xd010001604599f7,0xe08000b002c0ca1b7,0x70c046240001600599f8,9263946231,9331055095,1513509134775,0xfe540c2400002c2c99f8,0x1081100000a02c08a1f8,0xca100000a02c09a1b8,0x8085202b00001405a1f8,0x2c20001680599f8,0x594200002c2d99f8,0x2188c0a4640000144519f8,0x208b17830000144599f8,0x16100000a02c0c2178,0x4512318a200000a02c0ca1b8,0x1ce8100000a02c0d21f8,0xce009c0427ff4c1c5caa80000140599f9,0xb00c68e4000014989bf8,0xb40580621e7,0xb031000168061bf8,0x34000000302d9bf8,0x502c0300c2967,0xe06800000a0580621f8,0x6811000014491bf8,688810206055,0xd031000014499bf8,0x1e0440000501805c0caaa7,0x681880000a0300ba2f8,0x340c4880000a0300c2378],
[0x1606880000a0300ca3b8,0x1540110dc0aa971197cfa000014061bf9,0xa3820000342d9b78,0x2080000a059852177,0xc86100000a05806a178,0x90c20000144d9b78,0x2700a05f23000014069b79,0x1b01d0620520140c9bf8,0x640942a0466c0a40293f9,0x1b01d06200a064151bf8,0x170328540c6a0141513f9,5912500727,0x15068c20001600b19f8,0x702540410001600c9bf8,0x2c08830c0466a0002c13f9,5979609591,0x1e0dc40c20000582c99f8,0xb02540410000642c9bf8,0x1e0340be540c6a0002c93f9,0x1ce8100000a05808a1f8,0x1e05416238384000014089bf9,0x1ce8100000a05809a1f8,0x2700212000014621bf8,0x1a05c1e9b5000014099bf9,0x1380410000149f9bf8,0x2701e042000014a09bf8,0x62440050de1b072833177056000029bf9,0x2b008000b41480b21e7,0x24110000b42280b21e7,0x341c42a50001680b19e8,0x240a0f0442ea0002d13f9,0x240a1c6428c680002d93f9],
[0x320080000a14835a177,0x19004000050a40580c2967,0x664402100000a1480b21f8,0x208100000a1ac452177,0x1ba229300000a1ac0b2178,0x38088000051140580c2967,0x1c53088147280000a2280b21f8,0x1b024421057840000146999f8,0x540b0100000a2b80b21f8,0x130109119200000a0580c2168,0x8186180000a0580d21e8,0x95001c060e1c0826421897e10621780000140b19f9,0x5010000160899f7,0x1040e8e3000014a51bf8,0x4302a120000146c9bf8,0x3e0941081100000a05c0ca3e8,0x3045003205c047c1e702d3fa0000140b9bf9,0x17820000161c1977,0x190c20000146f9b78,0x683c2a03111b40000140c1b79,0x4900c68e4000014a59bf8,0x12408c12000014721bf8,0x1d071810c629c44274199e091b9f90000140c9bf9,0x2481080613000014761bf8,0x3a1882c79b40000140d1bf9,0x430049003e05090d0c48845b13219b29e04b9f00000293fa,687668437367,0x28080000a1ec03a177,0x28080000a01c3e2177,0x18040000501201c0ca937,0xde003a03e5008da80000a02403a178,0x28080000a01c46a177],
[0xe4c0394100000a01c062578,0x20880000502801c0ca967,0x9f00e7029941999280000a05003a178,0x28080000a01c6b2177,0xe540394100000a01c0ba578,0xb8080000a01c712177,0x22123011a00000a01c0ca578,0xc480249520a236000014039d79,0xdc083014c0e328609c0297f9,0x3c210000143b9bf8,0x16100000a02405a1b8,0x8213056014049bf8,0x181c2a130000143d9bf8,0x607802130000143e1bf8,0x380838180000a0240b21f8,0x140e150980000a0240ca3b8,0x4e802dc00c3f01c7f2c144636000014049bf9,0xf4038c223000014059df9,0x709822000014469bf8,0xb702f019400a11121584000014061ff9,998631781931000,0x27c03a80340bb01180c599844a0ac0297f9,0x3e00bd01981d0486180000a0500b21e8,0x3280342f02180000a0500ca3e8,0x9d002301482b4010902851a22d1270000140a1bf9,0x274023400440046741b99b80000140b1df9,0xf0784406130000146b1bf8,0x31320082c038338034320f0221850000140b9ff9,0x3c2a12000014711bf8,0x41a40298433916350000140c9ff9,0xe09d00170144e0618088a5a9489716e0000297fa,0x770194200002c3099f8],
[0x2c81d2400002c0319f9,0x4103c6a64000030031bf9,0x61052064031bf8,0x6a059008ea0a40313f9,3024801079783,0x1e8080002c0440321f8,9007200398842872,0x230328238384000044031bf9,0x7200a0083830000583099f8,0x1701000064309bf8,0x2300c6180c680003093f9,0x1480b48300004c031bf9,0x2b008000a405831a1e7,0x3d83c10000a40580321f8,0x283100015c05831a1e7,0xf220283200015c0580321f8,0x1e00849d0484aa80000583199e8,0xf00219c180002c0680321e8,0xd4198bdc2427270000580319f9,0x381b226500005c031bf9,0x6363000064319be8,0x2202825d030954e0003193f9,0x641c70be06364000064031bf9,0x660a32635000068031bf9,0x78289bcaea84ec0000313fa,0x294078100001c939df8,0x5280c868e4256000039df8,0x28080002801c9621e7,0xa501fc04200001c961df8,0xa700105304e0ac039df8,0x39881380002801c0ca9a7,0x6f8aa02700005003a1f8],
[0x29c02a7182700001c0ca5b8,0x4268026c0557a8847704e000039df9,0x2202100001c3b9df8,0x2203a010001ec039df8,0x28080002801c3e21e7,0x881bc1200001c3e1df8,0x3c480000902801c0ca9a7,0x14c020980001205003a1f8,0x130178900001201c0ca5b8,0xdd400381a5ca011b5000024039df9,0x1760246460003395f9,0x1720347040003415f9,0x17600c68e400001c989df8,0xe8170100001c469df8,0x190080000e030092578,2755960119783,5630462412990823,5630462413023655,0x17e03800002801c0621f8,962884673911,0x800000e0300aa1f8,0x17602910001ac061df8,0x63800000030361df8,0xc701100001c491df8,0x98080000e06049a567,0x18e03100001c499df8,0x3240440000701805c0caca7,0xc701880000e0300ba4f8,0x608010498080000e0300c2578,0x16600c6880000e0300ca5b8,0x3fc0234800780320645d2e2814c7700001c061df9,0x2900e0480ca557],
[0x144063405201c091d58,0x65805c105201c0c9df8,0x32c07c2c0466c0a40395f9,0x6780000e064151df8,0x6580f8580c6a01c1515f9,0xe00e0480ca957,0x86031a00001c01c092158,0x6780470e8100001c01c0ca1f8,0x33c064826350000380399f9,0xb8080000e2940ca177,0x16880d263500001c529978,0x230080000e0645421e7,0x5b8080000e06407a1f8,0x10c18c300001c5419f8,0x25ac263500001c0799f9,0x210080002801c08a1f8,0xdb010823838400001c089df9,5630462815676775,0x684980002801c092178,0x190080000e05c092578,0x18602923000000e0480ca578,0x9f0050a48e90463500001c091d79,0x4210100002801c09a1f8,0xe901d0100001c621df8,0xe501f09300001c099df9,0x3a4028100001c9f9df8,0x3a4028100001ca09df8,0x30f2006701b9071822177056000039df9,0x88000b401cc92136,0x421980007c16803a177,2755972899238,5630463230683430],
[0x5800002801cc921b7,0x3441100007c05035a1e7,0x1b8880003e02801c0c2967,0x371871180007c05003a1f8,0x3090000b41ec03a177,0xc480005a02801c0ca967,0x737404ccdb8000b405003a178,0x31008000f605035a1e7,0xe8040007b02801c0c2967,0x206dd008000f605003a1f8,0xb054180014005003a1f8,0x250509a333250000503599e8,0x4a0a109999280002801c0c2168,0x700409011ace5300002801c0ca1e8,0x1e400de00e1b0c4b1b7e4584b317a0000500399f9,0xb0098030e5200002801c0ca5e8,0x6ea000c025204874662a6000050039df9,0xca80f40c463500001c661978,0x3506e8463500001c0a99f9,0x12e02d008d0236a0003595f9,0x4b80ec1d08c6a0003615f9,0x4c0338e400001ca51df8,0x9c044061300001c6b1df8,0x2a0170100001c6c9df8,0x9901e81080000e05c0ca5e8,0x33d40246806b013804880a0f40814c7800001c0b9df9,0x15202106810411b600001c0c1d79,0x2e006338e500001ca59df8,0x2f0170100001c711df8,0xc804a0100001c721df8,0x6902905333c50888c11304637a5438c7800001c0c9df9,0x5010011ac0399f7],
[0x3201dd0200001c761df8,0x1900f17500001c0d1df9,0x7c804b8065035008ce0444a266c704b649a60a0908f00000395fa,0x37058609c0417f9,0x2b072400002c041df9,0x2b05860003897f9,2339392590839,668643438958071,0x6e80e040ae6417f8,0x4d0543caf20ac0417f9,0x601000052a919f7,0x1503810000280593a21e7,0xea07020000513a1bf8,0x1503810000280593b21e7,0xbf0f3930000280580421e8,0x31b010000280200ca3e8,0x16783b5000050041bf9,0x5a010015500b19f7,0x26a07020000593b1df8,0x27e023b6000058041df9,0xa09876c0003a97f9,0x11900f84a02000020721ef8,0x42c029f070d9040000200c9ff9,0x781b400f100c9cd5940842ee0000417fa,4790435935100408,0xc104e0883b1df8,0x7e25032809c3b15f9,0x59004b40058110c938ff9,23102803447800,0xc2022601b1b0590940ff9,0xe4609c9417f9,0xac609c0697b9],
[37460879150968,48591323566073,1726751281144,0x6c670c950ff9,0x10804328809c9517f9,0x10c328609c0717f9,0x12d07cc09c0897f9,0x1c12044ac0917f8,0x1c12040489617f8,0x270280580921e7,0x88270280480ca3a7,0x7104e050091bf8,0x18a1204e058091df8,0xd104e0480c9fb8,0x78efa16184184c09c0917f9,1194528759,0x8c024aeab13f7,0x78c44aeab95f7,0x78c44aeac16f7,0x8c024aeac97e7,0xf9246c84ad3f97f8,0x3a0c44ac1117f8,0x982c0a064ad4017f8,0x58e70521114958ff9,0x501aac068961bc6,0x4a035589613f7,0x501aae068961dc6,0xf8c555c9615f7,0x501ab0068961ec6,0xf8c55609616f7,0x248a05020349fc961fc7,61801971980263]],
[[0x12f18246c89fc9617f8,0x12010344b0111fc7,0xba0c44b01117f8,61815393753063,0xcc3140a084b14017f8,0xc45c08860689617e8,0x78309670521114960ff9,0x34310270281ac0b21e7,0xd808270282b80b21e7,0xe87cea504e0500b19e8,0x2c204e0500c1be8,0x3048ae504e0500c9ba8,0x3a1eb4a09c0a13f9,442418609165305,0x38b0e304e1ac0b1df8,0x72604204e2b80b1df8,0x6030c304e0580c1de8,0x1e0456504e0580d1de8,0x1b067f2b4c09c0b15f9,0xa63858609c0c17f9,0x1d03122aac09c0c97b9,0x12086347cc09c0d17f9,0x4540216006e01e15a5c418f14b3c7070456a0138ffa,0x11820000383b19f8,0x1594004900ec124860003b15f9,0x70104e1d8769df8,0x1c104e4d03b1d77,0x1c104e4d43b1d77,0x1b8104e0a43b1df8,0x1483c10270000383b21f8,0x8700bf00db2360c4314604e0003b1df9,0x6204449c7697f8],
[20679202679,20746311543,0x6c440a49397f8,0x37600e2e02000038939bf8,0x29402980870086023406e20582860009397f9,0x21801606040014a15f8,0x14c11ca4a40017f9,921805956388856,0x15810000280589521e7,0x1e782000050951bf8,0x1220d1c3000058951df8,82382821335,0x4f02c260026597f8,0x28155b8508c4a0009517f9,20075681655,20142790519,0x270280589aa166,0x208270280649aa326,0x64104e0509a9b77,0xdb0104e0589a9d77,0xdb0104e0649a9f37,5378315820855,0xd3c014b1dff0e3870809c9a9778,8953607624567,0x31b18864ac1497f8,42332952338246,2219702622071,61730970802151,0x60052068961fc7,0x38ff024040a49617f8,0x1b58ea09c9b97f8,0x1e04298270520500b21e7],
[0x1e2c298270520500ca3a7,0xb1885304e0a40a1bf8,0x2c298270520580d25c7,0x246885304e0a40b1df8,0x482085304e0a40c9fb8,0x4046204e0a4879fb8,0x284e18186404e0a40d1fd8,0x130a9401b828904ce5e10d838488b009c1497f9,0xa858c44256000071bf8,0x6201000280961be7,0x48080001c0589621e7,0x310080001c0689623c7,0x3b8bc13000038961bf8,0xb304e0ac071bf8,0x170e24120270002800b21e7,0x1988243404e000501bf8,0x2e060a0901380001c0580d29c7,0x22b2e1a3c20270000380b21f8,0xf87418270000380ca3b8,0x330c0c14120270000380d23d8,0x4c30d0052858094b8c28d07063704e000071bf9,0x684409c9e97f8,0x71a00c8b60704504e000089ff9,0x6c26044ac7697f8,0x1683844ae6617f8,0x10e010c05e800878f8239103088e4ac0017f9,0x1f024044b07697f8,61808548648935,3593585696711,0x7f024044b26617f8,20143216615,0x5601c1ac022860ac9617e8],
[0x6e80783894143000050961be8,0x90803c2b008444000058961de8,20143544295,0x3610c298c1c2000068961fe8,0x448043018603c58e5ab89408880009617f9,0xe6409ca117f8,0x43006a02103c3c1429a808f4e09c1597f9,0xc2007878987c047ac0270000500b21e8,0x32c03140220b810472b8270000500ca3a8,0x65804a8088681873f808f5804e0000a1bf9,0x242a832e05026230270000580d25e8,0x8500db00986808537e1e7e804e0000b1df9,0x85008a03240686812e041155804e0000c9fb9,0xe346609ca617f8,0x41820439ab0d828cb704e0000d1ff9,0x220d90083008a01bc0528b950b0b38595489838a9af609c0017fa,0x456800b83820c968ff9,0x59b006c38e0c970ff9,0x64058b8187080441417f9,0x940220308c978ff9,0xd8081415c0581421e7,0xae05999440280581419e8,0x2981c860501413f9,0x1a604215c058141df8,0x4f00a1e338402c068141de8,0x11c0588ac80581415f9,0x380d41c90980ff9,0x4703140c187080681417f9,0x6a07db940a0a084309c140ffa,20740544375,0x1dc1460a43b97f8,0x1cd09030000383b9bf8],
[0x178212019807201c40b06c80003b97f9,0x11044300002c3d1db8,0x940ca180001203805a1b8,0x5780662c3000024059db9,8264521591,8331630455,0x90280649aa326,0x3c10120509a9b77,0x5c10120649a9f37,1255147216695,0x8c7800781cae7090507080249a9778,0xf00c02064dc0497f8,0x22458c60a43d97f8,0x610520683e1fc7,0x11dc1460a43e17f8,0x302310290120500ca3a7,0x888530520240a1bf8,0x3884620520240c9fb8,0x6060530520240d1fd8,0x10e3004d02f048d2ee8108ec0a40497f9,0x90374026860003c97f9,0x70ca04b880003d17f9,0x1e33056024071bf8,0x1c2a130001ec071bf8,0x3c03020002803e1be7,0x1e018100001c0683e23c7,0x67802130000383e1bf8,0x31008000122800b21e7,0x6ec0213000024501bf8,0x188040000901c0580d29c7,0xa70b810000120380b21f8,0xe123c18000120380ca3b8],
[0x9b601098000120380d23d8,0x229a00ec0b8324392ec21e04637000024071bf9,0x1d6007901626070785000024089ff9,0x4844024a117f8,0x26405f00b038b1cc22ca0ac0497f9,0x10d00bc05202281381c6891444ca0003d97f9,0x6900d0218430000503e1be8,0x1c741e051c30000683e1fe8,0x21a01880a60121c75444ca0003e17f9,0x3d029068420c18000120500b21e8,0x5f4012c03b00f05c24511328000120500ca3a8,0x2fa009601d80782428da5444570000240a1bf9,0x1500bc1e01810000120580d25e8,0xc900cc09c0e35661840000240b1df9,0x10b00cc0b201880583438248a22650000240c9fb9,0x3681c504e33781848a3850000240d1ff9,0x29c00998216019816c025e00c3043915d97908892f20000497fa,0x18220000516319e7,0x190c20000504399f8,0x2a4121860016315f8,0x12201d840004395f9,0x7ac02c200002c069db9,0x260105602c9a9d77,2758050226534,5631013050558758,0x1800002802c9aa177,0x32810002289a9d77,9338264951,0x200000160649aa537,1530025125175,0x86006fb41c38300002c9a9d78,0x66712526e000059df8],
[0x1408a30520ac059df8,0x1414310290000504521e7,0x2811881480002802c0ca9a7,0x4623102900005005a1f8,0x1cc30e3052000451df8,0x512863052000459df8,0x142137202900002c0ca5b8,0x51b025202900002c87a5b8,0xe7182900002c0d25d8,0x3051003dfe683826e7052000059df9,0x5010002284f19f7,0xd0100022c4f19f7,1513511395767,0xee045c03f32300002c4f19f8,0x880001c2280921d7,1925357871575,0x24040000e0160480ca997,0x1e61180001c02c0921d8,0x5a4180001c02c09a198,0x120706582282b00003805a1f8,0x18b4840002800599f8,0x594200002c5099f8,0x26002080c023440000384519f8,0x4c004e7823440000384599f8,0x980082060c11a280001c02c0ca1b8,0x5a4180001c02c0d21d8,0x5b000260027ffa1cccf280000380599f9,0xf00a0c223000038059df9,0x814802c200002c5299f8,0x5e4400002c0799f9,0x641212400002c9e9df8,0x6d0005600de0aa500002c089df9],
[0xd4070205602c091df8,2758040691175,5631012571490727,0x338080002802c0921f8,0x1b001c3281000228091df8,0x360068281000048459df8,0xd800a04686c1418000160480ca5b8,0x3600f1bec0c389532800002c091df9,0x4400d0e4400002c099db9,4790985236584951,0xdc2a1ca52360ac059df8,0xc28205602ca01df8,5910641744375,0x28105602e681d77,0xe61c4a626e0ac059df8,0x220105602ca11df8,0x8aa505602c0c1de8,0xa3bf9d4c0ac0595f9,0x2c27028200002ca11df8,0x26161182b00002c85a5b8,0x11e03d201387c39879aa8056000059df9,0x218e4802c1615f9,0x179000205814047650000504519e8,0x16100002802c0c21e8,0xbc80010340823b280002802c0ca1a8,0x8b01cd00180c3c1c388ea50000500599f9,0x22d802c200002c6619f8,0x268194200002c6719f8,0x7d2400002c0a99f9,0x4680f6801434143850115cc0004515f9,0x23407b400a1a221e08eca0004595f9,0x820803822c200002c0c1df9],
[0x78314300002c731db8,0x11e03d60050d05011208ae600002c0c9db9,0xb1212400002ca61df8,0xed801890c4c1b41aa600002c0d1df9,0x1f40550122023c03d03c2a06a03f808c1480c290898d26e978a9d4e0000595fa,20746639223,0x1d4163860a49897f8,0xe58c44000038989bf8,0x86049c023c018809a807cf12318a30900009897f9,20741265271,0x3e802040a44697f8,0x1e042000038469bf8,0x8607480f410d00dc137005b83062880004697f9,9808025463,9875134327,0xc02e0649aa626,0x3c101805c9a9e77,0x5c10180649a9f37,1667464077111,0x465a00257d825060309a9778,316817730541543,0x4e1e260309c17f8,0x60c08c60a44917f8,0x532a024040a44997f8,0x63082901805c0ca6a7,0x8c20530520300b9ef8,0xe2520520300c9fb8,0x465a0030b5fa022cc4c0a40617f9,0x48c00787810000309a9f78,0x121001a1114a38e6052000061ff9,0x381f062481517f8,4996465580906488],
[0x7008100c02e0641526a7,0x270f1301805c151ef8,0x470f13018064151fb8,0x1c02040309e17f8,0x1ab9c3946c0301517f9,0x3201000030509bf8,0x160e100001c0580621f8,77124144563035128,0xe01000038499bf8,0x250480000e01805c0caaa7,0xae0900001c0300ba2f8,0x14a0900001c0300ca3b8,0x8f801d0eba66336000038061bf9,0x8cb40010284468a785000038061ff9,0x5b183000030079bf9,0x282e040026697f8,0xf60f062880004817f9,0x48ec053380017f8,0x1d8f143080004897f9,0x62c02420e04000030091ff9,0x3343000030099fb9,0x1c0204030a017f8,0xec03020560300c1fe8,0x31100721a0ac30c0ac0617f9,0x151844056000061ff9,21949421543,0x4e1e26030a397f8,0x2430016a0f040b04997e8,0x3721a0a822c0301617f9,2749591265767,0x1a80ce804706a18000280580621e8,0x39f001808000280300c23e8],
[0x67c032218000280300ca3a8,0x39019900fb0a6445000050061bf9,0x19f000000030661bf8,0x66c03d81a04440000300a9bf9,0x1c0000030691df8,0x31b60018080002c0300c25e8,0x17018100002c0300d25e8,0xe4058c02214f66445000058061df9,0x39003a00ec04fc004180c1bc30880004917f9,0x15400ec068c02a14784000060499fe8,0xdc00f803b013d001060e163e2a308a0004997f9,0xdc00f803b013d001060506f0c2200001805c0ca6a8,0x22070180001805c0d26e8,0x1b801f0076027a0020c060f8218440000300b9ef9,0x20860060b4072ea0062846142a147850000300c1ff9,0x6e007c01d809d800830b0704de18440000300c9fb9,0xa10469b040000300d1ff9,0x2181d200403017802401f00940d1d822a004f0b8234bd23112b78408a95f40000617fa,6717473099769,0xc85860004b97f9,2339394130935,0x56d060ae6797f8,0x410540458a0ac0697f9,0x1601810000280598521e7,0x1116180002805806a1e8,0x6c2000050069bf9,0x5a0100160c0b19f7,0x1d200db042000059851df8,0x3a401a22c3000058069df9,0x1e2000a05860004d97f9,0x868021c002406b02b401d80edb5caee0000697fa,0x288003100120e08998ff9],
[0x609c30524d00c9f78,0x1b010532789a1b77,0x1b0105327c9a1d77,0x1c10532809a1e77,950118290528119,0x1e8809c30524d0871f78,0x2c0c3830524d0879f78,0x60c3830524d0881f78,0x6793860a49a1779,110068668279,110135777143,3456739155767,0x17e03c83871a084d5b59778,110202886007,110269994871,3456719888183,0x1a81c30485064d48f9778,0xd701c10280649a9f67,0x30b8036a809c3a15080509a9778,110337103735,110404212599,3456738762599,0x1f23970d084d5af9778,20743657335,14572754807,0x2a81c102e0649a9f67,3179359674215,0x164e00d3c0fd8250605c9a9778,110471321463,3456719986535,0x3c81825084d4911778,20744050551],
[20744116087,0x816008d40222108be7244c08a0649a9778,82015125549781879,950194885268855,82015125684000375,79467026295,0x3ea1c7150a4389a9778,110538430327,110605539191,0x2602f80cfc3871a0843c9a9778,79936788343,0xe3097851508a4409a9778,0x87c00260198044466cccbe10c9a8f79,0xe80a040649a97f8,79332807671,79399917047,79467026167,0x72c1c7064389a97f8,0x783c0a0643c9a97f8,0x1c0e0a064409a97f8,0x2080974004e5838e0c9a8ff9,0x609c30520649a9f78,0x1b010532789a9b77,0x1b0105327c9a9d77,0x1c10532809a9e77,0xec809c30524389a9f78,0x2c0c38305243c9a9f78,0x60c3830524409a9f78,0x3602793860a49a9779,0x25005500240e089b0ff9,0x3f00610520480c9fd8,0x3d0051008ea0a40917d9],
[1718097783,18226878327,0x6b04a0e680f78,0xf00c02064ddb597f8,0x2f00c8b9d89b8ff9,0x620444e08f97f8,0x7c062070314549c0ff9,0xc5016804620520500c9fe8,0x1874004c5012834c3c1794e0a40a17f9,0x25062014040a46b17f8,0x12817058c60a46c97f8,0x8604a026205205c0c9fe8,0x5978034501d07b0d088ee0a40b97f9,0x1d003002040a47117f8,0xe8221f0c60a47217f8,0xbe00dc0fc017006058020d0030481060c1179c68a286484dfc0a40c97f9,0x7a01105cec0a40d17d9,0x30c03f014c01b81f81f80ca004400900c120102298913793053317ec148ffa,110672648055,102552475511,3456750886711,0xe7090a0e084d6689778,80876312439,0x26010012d89a9d77,0x3a87820004d48f9f78,20747097975,21552076663,0x5fa0011000700ce170d50a0ac9a9778,110739756919,110806865783,0x67090a0e084d6691778,2762949173606],
[0x5fa000f001100941c10000280589aa167,0xd808000280589aa177,0xd010a8000000280649aa367,2828648751462,0x80000284409aa367,0x17f8003c003c035a820000509a9b78,0x1c000034c9a9d77,0xbfc001e001a01673820000589a9d78,20747458423,0xc44e0049078200005c9a9f78,78930155383,0x410012f89a9b77,0x1b010012fc9a9d77,0x1f47820004d4911f78,20747491191,0xa06805e203448f810000649a9f78,79265699703,0x410012789a9b77,0x1b0100127c9a9d77,79467028087,0x1e30b830004389a9f78,81681618807,0x26010013089a9d77,0x4400c403a878200043c9a9f78,79735461751,0x410012949a9b77,0x1e1b010012989a9d77,0x121f47820004409a9f78,0xc04002201e80020261b6e2444cc48607040009a9779,80876279671,0x1e0ac12040a65a97f8,0x4404a30520025b1df8],
[0x1a0c7048a40520008f9ff9,0xeec00d1e260019c15f8,0xd839e1884de6897f8,0x8299370000500b21e7,0x8851326e0000a1bf8,0x10851326e0000b1df8,0x6008a01588e499704dc0017f9,20679989111,0x3a0d240a49f97f8,20680054647,0x3e0986680a4a097f8,0xb0620520ac0d1fd8,0x985fa0011019201e0d816e1e1b689540a41597f9,0x1d0143102900005069a1e7,0x170c14000a03fc00e051a2a2a8290000500b21e8,0x148148000280580d29c7,0x282444298290000500b21f8,0x30100803e0502318290000500ca3e8,0x1f0290290000525321e7,0x1d044298290000508823e8,0xca8298290000500d23d8,0x170c1c000a000a01f050ab253a660520000a1bf9,0x780c71c63052000699df8,0x16b00e86e728290000580d25c8,0x624298290000580d25d8,0x170c240006000e01d030a9f64ce60520000b1df9,0x128068163860a4a517f8,0x2884c008c1782826e60520000b9ff9,0x4a02312060a64c17f8,0x4a0520520025f1bf8,0x250260530520025f9df8,0x3e0fb020855052000911ff9],
[0x4a0ec163860a4a597f8,0x90020104c005078e9471a70520000c9ff9,0x1283c44260a64e97f8,0x25048530520024f1bf8,0x25048530520024f9df8,0x2504853052002501ef8,0xe83e60420856052000871ff9,81681586039,0x4a0ac12040a66097f8,0x9c04a3052002611df8,0x2801080460d48a4052000879ff9,0x4e02312060a65217f8,0x4e052052002529bf8,0x2217052052002531df8,0x88443ba020855052000881ff9,0xa008e00635e0f051cf70520000d1fd9,0x321658003002805203f8025286088898426f0a244df40a40017fa,0xbe300082089c8ff9,81100273615673336,79332971511,79400080887,79467190007,0x70c1c7064e88717f8,0xa0444e88797f8,0xe80a044e88817f8,0x204b8004e5838e0c9d0ff9,0x4378035909d8ff9,0x2cc040a86c97f8,0x3e40440102302e064151fe8,0xc2e02f81c8041946c05c1517f9,0x11014040a87217f8,0x6a026e0041b011c050b8a140848f00641517f9],
[0x620444f08f97f8,0x30140534c9e17f8,21260538871,0x330f053509e17f8,85832571835553784,0x603c8159c221dc25c9e0ff9,0x350141001b0104011ca95088146d8150ffa,14165154295,0x1c8105005d80660c20000584f19f8,0x97600410000644f1bf8,0x72041c016e01aa0f16c0004f13f9,1925360230871,0x5d806e146180001c0580921d8,0x24c012ec01c1838180001c0480ca3d8,0x12e00b700e634000038091bd9,0x11018102b00003809a3d8,0x4648300004c509bd8,0x2080001c059de21d7,0x15a4180001c05809a1d8,0x1106483000038621bd8,0x2ec02b59424000038099bd9,0xef800f0b1c30000389f9bf8,0x1e042000038a09bf8,0x7c0c102b000038a2a3d8,0x360a00606805c805392a1a237056000071bf9,0x12198001402280b21e7,0x3ae01a63360002800b19e8,0x2c0334039666c0005013f9,0x42005c01c6608c6a0005093f9,0x78734180001c1480b21f8,0x78900001c2285721d7,0x1c0cc0000e1140580d29c7],
[0x19a20e736b00001c2280b21f8,0xeb8028c008d00c023440000386999f8,0x995c200001c2b80b21d8,0x3be004a51a80001c0580d21c8,0x2580196001601080050025046def0ec5b90000380b19f9,973642231,0xd8c43000038a51bf8,0x3a17020000386c9bf8,0x3f00e120e180001c05c0ca3e8,0x182fc00c3900f90cc9370000380b9bf9,0x38c11c4000038a59bf8,0x1a1902000038721bf8,0x6401980350106014048047c027e8025c174e04284dcbb0000380c9bf9,0xb483000038761bd8,0x6806a8028e42350000380d1bd9,0x5101ec007003200cc01a8099001a01281fa00942688665a2b15720000713fa,0x1942000038099fd9,0x390e8003a004403204c242429892720ac0717f9,0x16f00b86c6360002800b1de8,0x8807606590370a446c0005017f9,0xa040000e0282b80b29c7,0x17e003832054310d211300001c0500b21e8,0x3458180001c0500ca3e8,0xc86c00bd000e06a863010a42270000380a1bf9,0x228900001c2b80b25d8,0xb5008a05c3631b00001c0580d25c8,0xc89c008f004833036e21521380000380b1df9,0x1a0a80e130000386b1bf8,0x820800be0362d0a7850000380b9ff9,0x487043000038711bf8,0x2042009e039d296360000380c9ff9,0x10803f00a814781286360000380d1fd9],
[0xcb00a162005f01635025002403f0008144c97448c6c0000717fa,0x4b8c00481a0c30000585299f8,0x6cc017010002940c9bf8,0x862014a010b00d504c6a0005293f9,0x2b008000a40585421e7,0x3d83c10000a405807a1f8,0x2a0423c447270000585419e8,0xd81378553b80000580799f9,0x7c321b18400005c079bf9,0x1bd00220443000064541be8,0x1850060400d0e7e02344000064079bf9,0x2ba005c193c32258c0005413f9,0x2a20187004f80230086009025798b6c0000793fa,1389500902,4503600998455799,0xa2002d215f7,59190877655,0x26a801dc30206001b915f8,2339388463079,90071993930161127,0x760100005a6b1de7,0xdde1c8260026b17f8,0x11101c260ac9e97f8,0x1472090000280589ea1e7,0x309e4120000509e9bf8,0x2080002c0689ea5c7,0x332e20d30000589e9df8,0x184410000689e9fd8,0x680d840026024e004a592410e08c0009e97f9,0x8812040ac5897f8,0x300000051ba9be7,0x1e398084001ba97f8],
[0x38000002805858a1e7,0x105b12000050589bf8,3025407616455,0x305b12000058589df8,0x505c1000068589fd8,0x680c500754007149630304480005897f9,0x1c82e0535c0017f8,0xad00dc3c2f080005a17f9,0x14223000044099fd9,2339390821367,2339395343863,0xf6400d302d14b3601597f8,2339395408887,2339395376631,0x150d2020ae6c97f8,0xfc801a34301c2a1cff60ac0897f9,0xeac00a85b032845056000089ff9,0x5840c26c0441617f9,0xac01000052d419f7,0x1f40c1820003120500b21e7,0x442007e8183030006240a1bf8,0x2200000052d499f7,0x13026021000028059c121e7,0x3c34c042000051c11bf8,0x31501418000287680b21e7,0x2038141800028059c221e7,0x756006432f4d5380002805808a1e8,0x25008000280440ca3e8,0x3b20074c0190dba7f8000050089bf9,0x3f2006c14080002805808a5e8,0x7e400d1a3f1d06285000050089ff9,0x3261350000440a9bf9],
[0xbc0100005a8f19f7,0x895028430007680b1df8,0x76010016a80b19f7,0x62382843000059c21df8,0xc0a054a180002c0440d25c8,0x62806d8025026b001878622f4d78000058089df9,2336509761015,8655493013510136,0x2ec02001c297f8,0xd9038a32a0005a97f9,0x9580536c0017f8,0x95804001c497f8,0x71c19832a0005b17f9,0x141430619040000440c9ff9,0x18040a1c51940000440d1fd9,0x1a031400b005c01d804e01301681840c8420ec08c04c80185e6e1684dcf05158bf60000897fa,0x1c1204048a097f8,0x3cc0684022020cd50c0ac0917f9,2749993951719,0x7880d1806e14618000280580921e8,0xcc0ef01d28000000280480ca3e8,0x6607880d080770b095000050091bf9,0x2810007802281000048699df8,0x80788048800780d886b096000058091df9,0x49600b121e0400005c091ff9,0x358027804e053bc0271003e003c031a0e2c7840000480c9ff9,0x26e005f004f00cc0f300640b200f80070045d20448c6e0000917fa,0x5be002814040026e17f8,0x4c020ae6e97e7,0x17010000526e9be7,0x760100005a6e9de7,0xec806040026e97f8],
[0x278440ac9f17f8,0x3201810000280589f21e7,0x96403020000509f1bf8,0x2080002c0689f25c7,0x65b0420000589f1df8,0x9e0420000689f1fd8,0x16025600252dc741888a0009f17f9,0x5817401940126860005f97f9,0xcd0026201c6852880006097f9,2339395736567,0x58c406040ae6f17f8,0x4b05439f520ac0997f9,0x8c0488827044056000099ff9,0x2e8328604c1617f9,0x320181000028059de21e7,0x58be0e6b300002805809a1e8,0x9640163783e5000050099bf9,0x328194300004c0a9bf9,0x76010016d00b19f7,0x76009b042000059de1df8,0x30ca4180002c04c0d25c8,0x13d8009403827cd65000058099df9,0x282e040026f97f8,0xc904001e016f8,0x3a2590a0006197f9,0x5200ac021804e4009602e2208880006217f9,0x3c5220c71400004c0d1fd9,0xe005200ac02900d804c01605d0148044020040321883d07bd26ee2a0acff80000997fa,5911501446119,0x24826062880acf193f8,0x2b5800b0b040acf197f8,9294662773873591],
[0x15c400005722cf19bb7,5927607573479,0xada00724149818420e0acf19bf8,0x78b0441d2693f7,0xb0241d0795f7,879765771392951,19029923767,0x1e10628c841c8d97f8,6563729399,0xf033824597b7,0x3ac04f0641e7017f8,78662080439,78058100663,0xdf078c641ca017f8,78079268791,0x9a0f14b0841de317f8,0xe01057250841fa7,0x308c0418320e0ae4a1fb8,84595283766,78087984950,6617978738615,21647169463,0x781056062459fa7,0xd953e4222880ae4597b8,0x1684000056422459fa7,0x44330d4320e0ae459fb8,0x3c12040ae7097f8,0x3198120441e761777,78691964726,0x62041e681777,0x132014044de4a17b7,0x1c5e8e538841c9b97f8],
[78662145975,0x71e40241ca117f8,0xe0120f394841ee7,0xae2007810a349818320e0ac841fe8,0xa8683c0894a620e0ac0c1fe8,2939885543,0x8811320e0ae711fe8,0x597800940919b2545625590b0269845241c1597f9,0x70d044fc0f97f8,0x228074c03a90059913989f8ff9,21427033079,21425001975,0xc180246c9f97f8,54235127,6755948107768,84567627639,82688579447,0x3e4024dc9f97f8,0x1ba0078240ae7197f8,0x22010560609f9fe8,0x62de42c289844e0ac9f97f9,0xfa801e070e80c185080ad2693f8,0xf038c4061860ad0795f8,0xa03390a196f7,83792893815,0x34610f0a80ae7217f8,389383588059128,0x4628c646ca197f8,0x2b14846c9597f8,54267895,0x25050446e7317f8,0x880246ca097f8],
[0x28e8c846ca217f8,0xfd8016031dd77418922ce46c1597f9,80474018807,80541128183,1195151351,80608237527,80675346407,0x1f48646474a017f8,0x260628c8478a017f8,0x620445008f97f8,0x4700bb803ca01e5070958a00ff9,0xe078c4500a197f8,0x607001604f060ae7397f8,0x88024aca017f8,54333431,6755994179576,0xa00a40a35780822ca0aca017f9,5691367957795831,21632717815,0x41056061691be7,0xec8042f080ad6913f8,0xe28f044ae7017f8,0x5368484ade317f8,84195678135,35406131468247,0x1934680ae7417f8,668660615485303,20105926519,0xf6800c6430c484ac9b97f8,54366199,6754615465976,0x1a900584c024aca117f8],
[0x830c464ade397f8,0x3408f848a52560ac0c1fe8,0x5ec0030e7b2fb8139844e4ac1597f9,91681231863,91748341239,91815450359,1195249655,91882559463,0x7fc6869fca097f8,0x3a0c4088a097f8,0x42030c485054017f8,0x1c00da003101ce0a42498a08ff9,0xf822505e317f8,84567693175,21582321527,0x39868464dca097f8,30186311671,0xe844505e397f8,0x57401e1c5060ae7517f8,0x1782056060a09fe8,0x381465d6021844a0aca097f9,0x34c0190e831880adb393f8,0x2ca0163840adb397f8,5965201250807,0x610573b1b39b77,0x16f000057341b39b77,0xb3807c8240c38426e0adb39bf8,0x1102340c12c0ad9c15f8,0x2e20163840ad9c17f8,0x1e010573b19c1d77,0x1790000573419c1d77,0x1e0126f3a59c1dd7],
[0xb38053a40c38326e0ad9c1df8,0x18803014040ae7597f8,0xc64438326e0ae761f78,88182564067191,82688743287,0x21001c1701c161960231880ae681778,0xc10628c326e0ae681f78,0xe04bc1c5064de7317f8,0x2520ca3884dca217f8,2940147191,0x22384326e0ae769df8,0x4ec03480505c070a4993dd7c3c31292d24dc1597f9,0x58d04509b597f8,0x60006011e0122ccd8a10ff9,4928170174322680,0x34680078240ae7717f8,0x25007a0641bf0f01092ce0aca117f9,0xd033a01e1d0143a1cc54c0ac0c17e9,0x32c00980bd002900e816c01b00681f03a02d80f40282a1c8138b0628503061e0b7edbe4158ffa,0x3306283056000f19bf8,0x2c220560024a1fb8,0x2e83056002459fb8,0x1e61618420e0ac001ff9,354339037550584,0x16c09f0176010c013e003605f808e0538a818728e0009f97f9,0x4a80a1a00486c040ae5e97f8,0x44c1583056002779bf8,0xc4c1583056002781df8,0x14d400ef05811585056000a19ff9,0x70ac23056001691bf8,0x6930e842560ac001ff9,354339171768312],
[54497271,0x74665066617f8,78527895479,78595005879,0x1a100042ca09fb8,0x2ec021807f00381ba006401e802e05bcf1103044c000a097f9,0x484c2c23056002789bf8,0x25b005e0ac24056000a21ff9,0x58453c80017f8,0x18420472b81597f8,0x18223056002579bf8,0x382c23056002581df8,0x18223056002589fd8,0x18223056002591fe8,0x3f58108c2260560008e9ff9,0x15b400b033cc0017f8,492721588410343,0xf8440ae5a17f8,0xaf049c250560008f1ff9,0x182230560008f9ff9,0x504a0a83056001b39bf8,0x1c0f833830560019c1df8,0xc102866a8626e0ac001ff9,54562807,6756158183416,0x3603a4001006800900441b1e18c4a000a117f9,0x3438473d00017f8,2339402487783,8092545946654712,0x63802cc1583056000a29ff9,4620713727992,0x3607832040ae4917f8],
[0x6c2c22056002499df8,0x12300543cc2c23056000859ff9,0x56009805d804300fa02c0e801202e80a1901881c81540222e2e13b109784c3d92f60ac0017fa,0xdbbc00271990a30ff9,80474248183,80541357559,21983958999,21983991783,0x3f8a2651c8e97f8,0x3a0b0451c8f17f8,0x6204451c8f97f8,0x18ad4006e803f144ca38ff9,0x3c69a00d41250a40ff9,950117204727671,18228156279,0x1b40a0e0e7b8f78,0x204c014402150a48ff9,0x1e02ac039025808c0224a408918dc160ffa,0x4880003e0280100b28e7,0x18c09180007c0500222f8,0xb4058c921a6,0x310031000168c91bb7,0x989180007c1680b21e7,0x18801b1230000f82d1bf8,2847979151782,0x8000028648c021b7,0x49100007c052e321e7,0xd89180007c050c021f8,21991722131878,0x31000280c91bb7,2775763722662,0x2d00042b0c1000028058c921a7],
[0x340800028058c923a7,0x108a000000028060c923a7,0xac002117a182000050c91bb8,0x1c941180007c2800b21e7,0x14b1230000f8501bf8,0xe441100007c0506921e7,0x31600794004700304510989280007c0500b21e8,0x5ad00347189180007c0500b23e8,0x20fc00e71100007c0500c23e8,0xc6801e3000fc0084e25f8422e260000f80a1bf9,0x8080002806507a1e7,0x73b0024ec0c30000510799f8,0x1e1410000280590821e7,0x7c282000051081bf8,0x1d008000b41ec0b21e7,0x15400ec02130001683d9bf8,0x1c44006825283135c0000b40500b21e8,0x12c00e585a0000b40500ca3e8,0xbbc0008c004825e50626b80001680a1bf9,0x2b008000a405863a1e7,0x35a007308c40000586399e8,0x2f007f8019260006393f9,0x208000f6052e321e7,0x54020218000f6050c021f8,0x1d008000f62800b21e7,0x50200ec02130001ec501bf8,0x1d008000f60506921e7,0x9e0028510c218000f60500b21e8,0xd858218000f60500b23e8,0x435801b01810000f60500c23e8,0x1f6025300084baa1830001ec0a1bf9,0x1421000140052eaa177],
[0x127141800140051eca1f8,0x808000280659c21e7,0x1a832440000519c19f8,0x208000280599c21e7,0x1d20000519c1bf8,0xe1410001400519c21f8,0xd808000280599ca1e7,0x3b010000519c9bf8,0x41000052f219f7,0xd0731800140052e321e7,0xcd0731800140050c021f8,0x8804000a00280400b29c7,0xd410001400500823d8,0x308030802c3470c081189fd8001400500b21e8,0x10008db6a0001400500b23e8,0x34585a0001400500ca3e8,0x7500308030802c389565e6021b7fb0002800a1bf9,0xb7803c1821250000586499e8,0x10821a0159084a0006493f9,0x347180002814835a1e7,0x480800028058f321e7,0x690000281485721e7,0x7e00cec007700041c86260ca61148000281480b21e8,0xb0210000280592721e7,0x8ac2a8000281ac4521e7,0xebc01ec8009cc3484dc0000281ac0b21e8,0x1250044400b0041a333250000506919e8,0xb090000280596aa1e7,0xd198000282285721e7,0x9ec017f00d986625740000282280b21e8,0xd8803bc045804c8014047650000506999e8,0x500800028059b421e7]],
[[0x16406f8035805d80736206246624b48000282b80b21e8,0xc901382bc05e805d00383703d0340180220540b40190208130c87780504e1408cdd5f62780000500b19e9,0x3c220000521c19e7,0x1b1420000506f9be8,0xbcc017a06d8022022600581a0e62a50000500c1be9,0x22011900141c81d803a0111018c02a80980ec03a0d0c608cd5aa0000500c9be9,0x3540320b7016a018400a0e40ec0b00e008811039003408604c2e1e600c630505e36b6df00000a13fa,0x69000028058f1a1e7,0xd60276801d4218000281480b25e8,0x69000028059b3a1e7,0x18c0b58076218000282b80b25e8,0xbd00a48039c02a6018880d7005f6d7a0000500b1de9,0x56807103dc07d805f016d002808ea60000500c9fe9,0x2dc031f015a01c40eb014fb00ae0083c0a901082981adb5500000a17fa,0x165009300220332004c08c6a0006613f9,0x20403a7000c0a260006713f9,0x5f2006e06f801e02e402501ac0046448c6c0000a93fa,0x5010001acf199f7,0x28080002c060f1a1e7,0x48080002c068f1a1e7,0xed051b03145000058f199f8,0xd14d3000058f19df8,0xf3801d0608e63000148359df8,0xe0e412000058f31df8,0x700a0313000148571df8,0x5111801ce8298000a40580c25e8,0x38f0e58a0000a40580d25e8,0xda01ba005c078400883902ac00a123fbc050134c2290001480b1df9,4785083884411383,0x7c900262430000592699f8,0x781c682000059271df8,0x6120001ad6919f7],
[0x1eb0009068c2c750001ac451df8,0x65c001500f5c01b0e57732b80001ac0b1df9,0x48c016d00220d0236a0006915f9,0x28080002c0616921e7,0x48080002c0696921e7,0x4e90270440000596919f8,0x2e0e4120000596a9df8,9289570807,0x2fa00b83a33000228571df8,0x308f400a1c1c2a0001140580c25e8,0x29cb00a220e58a0001140580d25e8,0x13a802f60038195cc13cae80002280b1df9,0x31407b403cc01703580910074050115cc0006995f9,0x14fc0c2000059b399f8,0x2c14d3000059b39df8,0x2103601000059b41df8,0x3c081014406e803b01a04c05f8028d01067e8189189496a0002b80b1df9,0x187004807801ac01a9000404442a50000580c1de9,0x110e0801891b385000058741de8,0xda03ac007810201981a2901a8063001c031e385c08408d00080898f0989790000580d1de9,0xd100780c8042032c03a0984300107e066068a408402a02c0ec01701a163d0143a059005010a4c495e84ee0000b15fa,0x677000904c2999620e0000b9ff9,0x108802730078c00c30860020895f8,0x368048806680510045800c81e100d1e1cf110a3090000a517f9,0xda018c027015e01e40f3803280db807c3c1444cc0006b17f9,0x181e0b09150001d00b9ff9,0x6c30023048f073e00017f8,0x1fc05700a6024601140c60320f3804c3a0f4e0006c97f9,0x5c1e0b09150002d40b9ff9,0x5203053e40017f8,0x12900d8f143080006d17f9,0x20c07f015c0298093804103180c83de00b832e500005c0c9fe9],
[0x3181b5801e900220659500005c0d1fe9,0xe08e00981440107400a07605700b82213408f8031f807c0140c80e120181e1f600b55de1e08a95f60000b97fa,0x8d80c38c9a7d0ff8,0x1b048e58a0021993f8,0x23018c218a0021a15f8,0x791ce4a0006f17f9,39629906350072,5093212773127160,0xf1800340cc121860021c15f8,0x3c6000703d840006f97f9,0x13500080bc016082038cc0d9007c011c004e01b0240950842ee0000c17fa,0x5e804f01c822814f002a0006004873c48208a3092000a597f9,0xa9000101b8228064008803080ee806c08eca0007117f9,0x12803500a20220e7009a06101b000a0020c288a0007217f9,24215201648632,0x7874053f00017f8,0xa09040022b15f8,0x1b10076807f143060007317f9,0x10600d802c035007826144088060d80b00e1980c1f0083c0e4101281d06c050901c091f02d80727048c9c608a95f60000c97fa,0x4f80068339aa0022d95f8,0xc22002814040027e97f8,0x1580450014036c01f8410d44c000a617f9,0x5018260022e17f8,0x280ac0886fc00302cc141844a0007417f9,0x88400af800c284480007517f9,0x781c48d967f0ff8,0x982e053f80017f8,75912714743,0x272004822860023593f8,0x13803300a6011b000b80818055e1c8a0007617f9,0x82025009c01980fc15405203302c5205201b0148122d0260640706482a031502598058582b26342acbf80000d17fa,0x1a801200a0f809406606a03300582a1540587e066058a40a40360584e03f01a09806120380e0301780841e1581cc482c181122a9bdc000ffb],
[390936725458937,30936861708281,0xd052114a78fd9,0x75b071b6a0168ffa,0x5e80070208a80ff9,0x5080070cc60201716f9,0x26c000a0610ca88ff9,0x6010860301716f9,0x47800a833860381713f9,0x95000d0f0ca90ff9,0x11a0003061060b80917f9,0xe60008c20280b80c1be8,0x71001d830860501713f9,511678391,85833291703,8657030814339000,0x8d001140c490a98ff9,0xd600050308605c1716f9,0x5d001ca241860b80c17f9,0x4b001fd13b41143b9c170ffa,0x1d20008c200a0c8009bf9,0xca400f1984400a030009bf9,0xc840090c200a034009b79,0xb0064009bf8,0x313002180c681600093f9,3441946565624,0x30d003e540c6a1640093f9,0x92860141993f9,0x170100a0641a1bf8,0x32700328540c6a0141a13f9,0xc5400623838400a044009bf9,0x622006a0648300a04c009bf9],
[0xc14009261680093f9,0xc0c00b28416c0093f9,0x172800302c1984500a05c009bf9,0x5c20049300a060009b79,0x586002c21102e400a064009bf9,0x16d800b0f0a3500a068009bf9,0x1188015b801a55ffc878d34e0140093fa,0x2af0008c200a024009bf9,0x1288014c800900823060141917f9,0x13d80149801fc794c0140097fa,0x4ba0011c59ca0180093fa,777930458927097,0xa638b39c178ffa,0x898120e08aa8ff9,0x171c000823060241817f9,0x5b1003c6588a0301817f9,0x176c00f8508ab0ff9,321117670313977,0xe46034181779,0x370201c0c00c9bf8,0xb2a004b04c6a0381813f9,0xb26004d032860c00793f9,0xb2a000c1217080441817f9,81100275628939256,0xa0445608797f8,0xb62006882a0cac0ff9,81100254231697400,0xa04443cac97f8,0x74682a10ac8ff9,0x2cf8004e442880c00997f9,0x2b880030a7c3308c05c1817f9,0x164400ac1250ad0ff9],
[0xc20650cad8ff9,0xaea001e0928060181779,0x154c0026107828880c00c97f9,0xade005c161e18c4c0c00d17f9,0xeb804ef001107ebdbfc473b6a0180ffa,0x144b00823060c01917f9,0x84800d90f3c794c0c00097fa,0x1c9000a0a81860201917f9,0xd88004808c3028020009bf9,0x1c10031011860201b17f9,0x6b400b0f03061d40097f9,0x11b002140f3c090aee0200097fa,0x75e00e7429219ca0240097fa,0x1c86c38e0cae0ff9,0x1b0c511098188ffa,0x61303c0a06110ae8ff9,0x1808320608af0ff9,0x69400ac60341917b9,0x1990023013ca0441917f9,5631975114744743,4506349616045048,0x1c1204048b097f8,0x1c1204048b117f8,0x91024064191fb8,0x18d003f42868184a0481917f9,0x1b10019208af8ff9,94583915548665,0x163002c2028060191be8,0x151000c716e5028064191ba8,0x2a20073b82dca0501913f9,0xb080124860c80a93f9,0xa8800468241860601917f9],
[0x3a0c45841117f8,0x17d001c59c6110b08ff9,0x1201034588111fc7,0xba0c45881117f8,0x8180886068b117e8,0x1c2fc486110b10ff9,0x51c00628e2dca0641917b9,0x15f0032440aac0c80d17f9,0x138002840014021e1cfa7b44e4819c669c190ffa,0x38c00460e6c29219ca0c80097fa,0x33d007c318301c030009bf9,0x1b0800c63060301a17f9,0x2420e04018048009ff9,0x8ac01d150dc1c45242dce0300097fa,0x5f2001e0508b18ff9,0x8c401505f0d84954a0340097fa,0x1b8100e02406400a3d8,0x514010c063401c048009bd9,0x27a00648201c04c009bd9,0x262005b862800093f9,0x117007c318301c05c009bf9,0x2b80321d81850e7844501c064009bf9,0x44401e128301c068009bd9,0x198002190b41cfee022216e0380093fa,0x56004f4092862940093f9,0x14c00140dd0742d88e03c0093fa,0xd052114b20ef9,0x6fc1c650cb28ff9,77718030434635769,0x1f81f62b12a0198ffa,0x17010240641a1fd8,0x4fe00a2088480481a17d9],
[0x6284604c1a17d9,0x135800c630605c1a17f9,0x19b005c0780498785ca0641a17f9,0x4fe00621090b38ff9,0x4d200625060681a17d9,0xb8801219004050282fee02223e01a0ffa,0x950025e5028044009bf9,0xb100127013cc0441b17f9,0xfe00b40b03062d40097f9,0x1e401b0f03062d80097f9,0x1e401083183022068009fd9,0x175005844321483f91ac38f0b540440097fa,0x330001402406400a3e8,0x1ff00c412c018094028048009bf9,9291149812113384,0x1200cc1109a150a0481b17f9,0xb121e0402e048009ff9,0x41d0530d1a167118284024064009ff9,0x2c201a0307c120cd1a17a241446e0480097fa,0x29201d0c84c341c38e0c785ce04c0097fa,0x13c0420660a54028060009be9,0x6f01080c1416e5028064009be9,0x13404822058340e1ce7cadcc0500093fa,0x6503b4063263300093f9,0xba03107c628d08c0540093fa,0x5981c650cb40ff9,0x4ac1c230cb48ff9,0x7c648669c1a8ffa,0x11700ac60601b17e9,0x78282dca0641b17e9,0x3f403e051101404112394395b9c1b0ffa,0x1fc07c318302e068009fe9],
[0x1f046190b4163823c6212242dce05c0097fa,0x3e80cc021870cc0093f8,0x2040760230e800ff8,0x7901b600811883780097f9,0x11068d905d0ac0239918954e0600097fa,0x250743e0cf163c10408d242dce0640097fa,0x2101d06863063a80097f9,0x783a048246b1225872a0c083145f40680097fa,0x16e000810386a882655424421104539cb644ab046dbe4008ffb,0x402001c7260088117f9,0x2e1309cc08c0117fa,0xd832060e808ff8,0x2f400260fa06a90b50ff9,0x71c0830280201b9af8,0x541841d41b96f8,0x7c400690ac80201b96f9,0x1c1204048b597f8,0x3a0c45ac1117f8,0x4d8002604303241c6110b58ff9,81082671162954744,0x208201c05c1b9af8,0x478005701e866880381b93f9,0x17816060e810ff8,0x4a8005b0164890b60ff9,0x1a010280481b9bf8,0x1c1204048b697f8,0x320102e0481b9ef8,0x468001101d011c8b9c90a0481b97f9,0x73000c6008c20280601b9be8,0xe60010c03824702dca0501b93f9,0x3a0c45b41117f8,0x11e0014c0335048186114b68ff9],
[0x318202e0681b9ee8,0x1b10014a542dca05c1b96f9,0x6b0004a022140811860601b97f9,0x986d041060681b97f9,0x12c00040ac0136c8892ed04305b9c1b8ffa,0x1942004024211af8,0xa92880082116f9,0x54a24c5004024019af9,0x14a11880082216f9,0xeb6144bb900080196fa,0x70cc60e00216f9,0xca0830080581c9cf8,0xc83086010bc16f8,0xe70a84880101c96f9,0x4a008020120102a20f7,9297195717762295,0x3e03810020280102a20f7,0x1f61083240040102a1cf8,0x12c3a02180200a0240222f8,0x92812307c014021ef8,0x5004010050280100b28e7,0x2590782180200a0500222f8,0x3f062004014291ef8,0x3f062004014299ef8,0x11f0043180200a0100b24f8,0xe6bf443820c26004014021ef9,87838197373343481,0x581c083004024269af8,0x61083004050269af8,0x54184008e416f8,0x79c0a021880082696f9,0x1d011180201201005a0b8],
[0x16100201201006a2b8,0x4fc020281126004024021af9,0x82187060ce7004024021ef9,0x450e083004010051af9,0x143810880082716f9,0x6a0701060082796f9,0xe2a0a23004010059cf9,0x72a1cb144004010069ef9,0x687860f00216f9,0x2d01040101e96f9,0x9e180201c0100820d8,0x93c3004038021af9,0x184100201c0100824d8,0x13e3083004038021ef9,0x32602083004010079af9,0x38440418020080400924d8,0xb6a44004010081cf9,0x26241c084004010091ef9,0x3e0c81134c0f80216f9,0x12810860101f96f9,0xa0080202801107a0f7,0x2c1c3e1900105a0280100b28e7,0x1a8387c320020b40500222f8,0xd038c010140081ac0b28e7,0x5222728020280100b20e8,0x308418020280100c22e8,0x54161044e5004050021af9,0xf01c18c6730020280100b24e8,0x1b03191c50ce6004050021ef9,0xc50e0830040100a9af9,0x881e089ca0082916f9,0x1e0ae04cc80082996f9],
[0xc2102b0040100b24f8,0x2080200805926a0f7,0x288868720020081ac0b24f8,0x650418020080580c24e8,0x2c020cc5e8c550040100b1cf9,0x509c0820040100c1ef9,0x348937fa55f8bb3b8143b4e0080216fa,0x5900a8020a818ff8,0x20500046e07c38590b70ff9,0x2f07260e02a96f9,7705317576697,0xba0d8cb80ff9,0x2e11860e00497f9,0x4c8681080e00597f9,0xa86460e0069779,7705317642233,4956538605561,730491796263929,0x39840e00793f9,0x74020a820fb8,50751694540793,0x50226050ba17e8,0xb1d1820cba0ff9,0xa21260e00a17f9,0x186c0405a8197f8,0x185941060e00b17f9,0xa81260e00c1779,0x924007a0ffd2ac906218665a01c0ffa,0x3101c726008b717f9,0x6020242f07260082a96f9,0xec309ca0e00117fa,55001527521272],
[308139622307320,0x22ef001d60b0cba8ff9,0x882c3860cbb0ff9,0x140b052860381c93f9,0x58120c60cbb8ff9,0x3603054140b17f8,0x1d02965e0c3060581c97f9,0x880e045c32060cbc0ff9,0xd041060681c97f9,0xe814ebd811896299c1c8ffa,576422865934328,0xec0020220040242a1bf8,0x14010040302a1ef8,26980521911,0x1e81b41460f82a17f8,0x49a001f80f80a130040502a1bf8,0x30b000140100405c2a1ef8,0x9100f760033035c21d836a0082a17f9,0x7b0004c01074014039f78,0x20881180200a02403a378,0xfa0014080200a01c062678,0x7d001100a01cc91f37,0x7b001e2207c014039f78,0xe83c14180200a05003a378,0xfe0014080200a01c0ba678,0x71001afcf0635004014039f79,598275659667448,598275659700216,0x281c2074014071bf8,0x3400f8000402047de19ca0e80297f9,0x4c1c2078014049bf8,0x481c2004160049bf8],
[0xf80a020040242c9bf8,0x8300f92003300438fc309816e7004014049bf9,0x5c01004160061ef8,0x342020040302c9ef8,0x221458180200a0380622f8,0x2c03080011a39416e5004014061ef9,0x2206c04014c517f8,0x4c1c20780140a1bf8,0x7c023e2421070a0f00297f9,5918758839,0x39812040f82c17f8,0xa8120041600a1bf8,0x5c010041600b9ef8,0x2e06611e61e0c6a0082c17f9,5985867703,0x1b41460f82c97f8,0x1f0d09030040502c9bf8,0x3420200405c2c9ef8,0xcca17982c36a0082c97f9,4785762751552439,0xf3307c014071bf8,0x585858180200a0380ba2f8,0x5c02021f1a1e0477004014071bf9,714173587255,0x6805f0002120c612470c308014c917b8,0x10e01a3d48000c0a808483184de05b4c0f80297f9,0x3409811860082d17f9,0x11820040502d9be8,0x342260082d97f9,0x4920004c074030100200a0500b23e8,0x24046180200a0500c2368,0x20c01c7b1001a80202046385b8504816e70040140a1bf9],
[0x89700deb40040c01206640c61840040140b1ff9,0xa058100200a05c0d26e8,0x8100d1eac006a00848309239816e50040140b9ef9,0x90184808c30040140c1f79,0x3f062004014751ef8,0x1bcc10085850040140d1ff9,0x408068f5e0005014e02084266309ab5579e095f20080297fa,282867178231,0x43022074008329bf8,275701570295,4785359283198711,566258356626022,4503884373596919,0x1000201806032a277,564600901903031,0x57d48824004030329af8,0x581004648329bb7,0x17c023407c008329bf8,0xc68fc280091813f8,72339358458485495,566112730391271,0x18fc5261400405c329af8,0xc7e13004060329b78,0x253250103004064329bf8,0x38bbd428e2c6c0083293f9,0x1c02040e83297f8,0x70f822004024329bf8,0x601004030329ef8,26981078967,0x3d80a040f83297f8,0xf0313004050329bf8,0x60100405c329ef8],
[0x4e80085800d7a2c36a0083297f9,4793046537051896,0x5012040e83497f8,0x6c12040e83517f8,0x3a00e040092557,0x3c107401c081df8,0x5c107401c091f78,0x880c265f40397f8,35347450173415,0xd0100e060bf1f67,0x1960240401cbf17f8,0x4c01074050359be7,0x883a02801c0c2367,0x3a02801c0ca3a7,0xf1074050039bf8,7971929758712,0x199802040e83597f8,0x639802060e83617f8,0x3a00e05c0ca6a7,0x3107401c0b9ef8,0x184020d307401c0c1f78,0xcd107401c0c9fb8,0x6802f8001e008d789d710ce10c233560e80397f9,0x1080428200401c3b9ef8,0x7c13c022c584074008039ff9,0x182a041a41d97f8,0x182a041a81d97f8,0x70200481da557,0x3c100e0401d9df8,0x5c100e0481d9f78,72341824976296935,5630463219442535],
[0x7102801c1d9bf8,0xcb802041ac1d97f8,0xb802041b01d97f8,4786038222200568,0x32e04200e0601d9f78,0x880c2601cc217f8,0x3577e454d1f001c1d97f9,0xb10100201201c3ba2f8,0x9c2004024349bf8,0xa2a02004024351bf8,0x907080100900e040092957,0x920e100201201c0821f8,0x1120e100201201c092378,0x3e01201c0ca3a7,0x4502207c024039bf8,0x502201201c1f9bf8,0x58385830041ec039bf8,0x6d858300401c3e1bf8,0x1e030f14004024359bf8,0xe4a0104004024361bf8,0x100900e05c0caaa7,0x643150180201201c0ba2f8,0xc0202180201201c0c2378,0x1cd70f8100201201c0ca3b8,0xd57d7211a16345aa004024039bf9,0x34017c000f0321140638d0e5004024039ff9,9297195916663800,563912704303799,0x26030100200e05c0522f8,0xc060200401c419bf8,0x96b0082c32500401c051bf9,0x1c261c30041a4061ef8],
[0x34202004030351ef8,0x70401007020030092c57,0xc20e100200e0400624f8,0x1160e100200e030092678,0x3e00e0300ca6a7,0x3107c01c061ef8,962880052984,0x308020281ac0622e7,0x14040101400e0300c2a67,0x101400e0300caaa7,0x1f85018180202801c0622f8,0x6030100200e0300aa2f8,4785350306601719,0x19782820041ac061ef8,0x70e0103004030361ef8,0x12c07828200401c491ef8,0x960000200e06049a667,0x9204428200401c499ef8,0x1b8021682100200e0300c2678,0x2d018a14080200e0300ca6b8,0x1a00be003704812055495afa0429145a900401c061ef9,7059609527,0x428050460f83497f8,0x1c2a041a41f97f8,0x512004050349bf8,0x1c3e130041a40b9ef8,0x1e1e1e0f0f382c0c6a0083497f9,7126718391,0x76050460f83517f8,0x1c2a040fc3517f8,0xa2a02004050351bf8,0x3420200405c351ef8],
[0xf0f0f0a82fc10e86a0083517f9,0x7020048c92516,0x5083e00e040092557,0x70200481fa557,0x190480101400e040092957,0x440100702005c092c57,0xf0f0f00c1f70da00200e040092558,0x29100e040c91db7,0x67207c01c081df8,0x29100e0401f9df8,0x14083e0980202801c0821f8,0xa5a0900200e0400ba4f8,0x1e1e1e04817c205b500401c081df9,0x91100e048c91f37,0x1c7207c01c091f78,0x91100e0481f9f78,0x24320900202801c092378,0x242e0900200e05c092678,0x3c3c3c07008f907011b600401c091f79,0x13011307c01cc89fb8,989084818871,989051461431,0xea1cc91db7,964367556407,0x6802f8001e033029229cf5307162a01cc917b8,0xb8020401cc917f8,0x13011307c01cc91fb8,0x3c2f02107c01c0c9fe8,0x1a00be000780a0f0487030a48a319ea089c1043359fc0f80397f9,0xd801150200401cc91fb8,0x6404458de2607c008039ff9,0x440a0401ccb17f8],
[0x780c292296368e0821412b201c1f97f9,0x360b09142360080a1bf8,0xa43284004051259bf8,0x23011418020b405003a378,0x6d858300401c641bf8,0x1c1307a02c198c4004050359be8,0x1c1307a0b0b0cc6280202801c0c2368,0x720f4170f8100202801c0ca3e8,0x28042a1a2922830ff3122c5595b004050039bf9,0x34017c000f03e8160c70214e6004050039ff9,0xc060200401c669bf8,0x720ec0ab0082c09500401c0a9bf9,294090349303,0x6a00103d0781280092693f8,0x180c2e188047c44160236e0083597f9,0x6030b8010243050e86c0083617f9,0x880ac004170200401c6c9ef8,0x740503b014080200e05c0ca6e8,0x6802f800ec0a120102870e0a29229f0cc4830d1995a00401c0b9ef9,0x1d00814321482c204022b700401c0c1f79,0x868b8722044412146b030550400401c0c9ff9,0x27401a1e84007e07e010d05a0a163429491450908addc4042c49bf60080397fa,0xe81c083004024379af8,0xe81c083004050379af8,0x7900c50541860083796f9,0x3c0e04180201202c0422b8,0x12804100201202006a238,0xdf804050665004024041af9,0x8c2004024041ef9,0x9c082004020051af9,0x19582c300402c041ef9,0x714460083816f9],
[0x44381060083896f9,0x7150082004020069e79,730492064503545,0x241040201e96f9,0x9e180201c020092258,0x93c3004038041af9,0x2e81c083004020079af9,0xd4c3004020091e79,0x3a038102b0040500422f8,0x88020280593b22e7,0x1308418020280580422e8,0x308418020280200c2268,0xd500182cc2664004050041af9,0x8c2004050041ef9,0x9c0820040200a9af9,0x14d20040593b1ef8,0x19740e394004058041ef9,8007056128349945,0x83805d0381060083a96f9,0x21c0820040200c1e79,0x1f5000b80fa01bfd6cd79e02852cc0080416fa,0x1c1204048bc97f8,0x3a0c4088bc97f8,0x77c002883806b098186114bc8ff9,4793054050393848,0xde03101402280e83b96f9,0x880c40320608bd0ff9,0xd0f0cbd8ff9,94583916466169,0x4c01074038081fd8,0x4c01074038091fd8,0x105b000bfc02da1219ca0e80717f9],
[0x1c02040e85517f8,0xe80a040e85617f8,0x1f4021074040091fd8,0xed0019c406e48061209cc0e80817f9,0x11008be00c11119c1080e80917f9,668666119295991,2362072897495,668666119362535,0x3dc382285f4bf97f8,0x4c3065f4c017f8,0x6c26045f41017f8,0x4180fe4cbe8ff9,86381630455,86448740311,0xc3424bf17e7,0x1da1c3065fcbf17f8,0x2c1a1a065f8c017f8,0xc23d8bf17e7,3324171525991,0x196024045f81017f8,111882999783,0x53900108583065fa8317e8,0x24c0127068106060bf17e8,0x4180272f60608bf0ff9,7972808367079,0x9b01d420740500b1be8,0x13010740506e9be7,0x67407614540740500c1be8,0x13e0360ce40740500c9ba8,0x9700bd832aa0e80a13f9,0x4e80ec19c80e80a93f9,0x73302d060e86917f8],
[0x58050230740580c1fe8,0x24c053d865ca0e80b17f9,0x5080140ce407405c0c9ea8,0x27c045032aa0e80b96f9,0x146c26040e86e97f8,0x24280630992aa0e80c17f9,0x11e0284d832aa0e80c97b9,0x15601fe4009c0cc04300be279229c974d60926a41d0ffa,0xce804500f8382819ca0083b96f9,0x786207400a839bf8,0x786207400a841fd8,0x786207400a849fe8,0xfe06030a65074008bf9ff9,0x3c021a044074008c01ff9,0xf0087864074008101ff9,0x5080277c161944a0e80117fa,0x156d0002141394c08ff9,0x2cd0070208c10ff9,0x2c11020160481d9fb8,0x3c7c15cc02c1d97b9,0x182a040ec5617f8,0x2d40210200481d9fd8,0x327808c19409c80401d97f9,0x22780741920810880481d97f9,0xec0d0f0cc18ff9,2752745380839,0xee0010661420280581d9be8,0x13010280ec6e9be7,0x17900082b630280601d9be8,0xf60360b7092ac0501d93f9,0x303048d060ec6917f8,0xcd82302c0601d9fe8],
[0x20404c09a5c80581d97f9,0x10203a010b832ac05c1d96f9,0xe6c26040ec6e97f8,0x68300f0da609c80601d97f9,2422844036087,2422911145943,668727024687079,0xe48382285fcc217f8,0x1e0d0d06610c017f8,0x6c26046101017f8,0x9a03907085c0450c20ff9,0x830062b6cd5c943bdc1d8ffa,0xb1010020121dc1022f8,0x182032c04c51701840040243b9af9,0x2c2004024439bb8,0x39088180201202c0923b8,0x1d403581960ae5004024059bb9,0x2c20040244b1bb8,0x7500de0630724004024069bb9,0x66860083c93f9,8497438314533881,0xd80602004024561bf8,0xd90128110020120400923d8,0x6d501a20ccde7004024081bf9,0x26380e2e821020846004024091bf9,0x6c805c0ce407c0240c9ba8,0x6b80b0d032ac0f80493f9,0x35c04d049ca0241f93f9,0x364046092ac0083d93f9,0x1ae027809c80083e13f9,0x4401023004024691bf8,0x86c118020120580c23e8],
[0x6c80d2e40040240b1bf9,0x36c02e067200201205c0ca2a8,0xd9013c04e40040240b9af9,0xa120040246e9bf8,0x9a60093c04e40040240c1bf9,0xc5002091824e50040240c9bb9,0x150af011c0ca065eaf92df05866b520080493fa,0x110ec04024c317f8,0x16c007d80b20508311030a0f00497f9,0x2a144818020120380823d8,0x51ca818020120380923d8,0x5f000a900686b61219a7004024071bf9,0x25031c4004024551bf8,0x267001340dcc3c384004024081ff9,0xb009a010e1c5104004024091ff9,0xaf00ed6005c150560e204700b81e660cb885822dce0080497fa,0x260883083004040051bf9,0x260883083004048051bf9,0x7c1f07860084093f9,0x30404c170334a0f80513f9,0x110883004058419be8,0x12151664004058051bf9,0x7b805c0ce40040286c9ab8,0x19a01215c0ce400405c051af9,0x8c2004060419be8,0x486a0c2004060051bf9,0x5f80881149c80084193f9,0x5b807e0098051d25943b4c0080513fa,0x3a0c85860084397f9,0x2404681080f00597f9,0x882943004038059bf9,0x34041060084497f9],
[0xd84601050510400402c091ff9,0x312880047804600ac0d8320f90c52b500080597fa,0x2082004038471af8,0x1c48200404c471eb8,0x37a01c43c30880084716f9,0x134011840084796f9,0x78104180201c0400622d8,0xce888200201c0300922d8,0x9e180201c03009a298,0x4ed06182085004038061af9,0x4c14100201c0400626d8,0x6c14100201c0300926d8,0x416c00286807490ce5004038061ef9,0x1043c3184004030079af9,0x7031c3004030551ef8,0xe5e02004030561ef8,0x7c0108020200300926d8,0xab800c0900213ade5004040061ef9,0x3d8040480118bc18e084004030091ef9,0xc70b0e82085004030099eb9,0x2100140ce407c0300c9ea8,0xf8045032aa0f80616f9,0x1f00ec19c80301f96f9,565699544687335,0x4201d86a18020280580622e8,565699545047783,0x44601b318020280300c22e8,0x4a01b06720020280300ca2a8,0xe802e4e4004050061af9,0x1180760ce40040300a9af9,0x3870f13004030691ef8,0x50181180202c0300c26e8],
[0x5c029ec32e5004058061ef9,0x94005032aa0084916f9,0x9400a142004060499ee8,0x4201ec19c80084996f9,0x707010040306e9ef8,0x6044019964e40040300c1ef9,0xc038e360ce40040300c9eb9,0x79d0021803e00b8096024d26b4ea5983063b500080616fa,706457909759993,0xc40c85860084b17f9,0x8c419880f00697f9,0x2c2004038069bf9,0xa19860084c97f9,0x2550003808230058c05a07ce1f4e0080697fa,0x5b8002c40110ec04050c317f8,0xa9005a0f40e850ff8,0xf6006c800f1e1001e06a1846714c30ff9,0x2c336008e120cc38ff9,0x1d83a80d08850cc40ff9,0x1a14460f00997d9,28596068782008,343222929100793,0x3a90006c0104050c517e8,0x11c0054c029c8664214c50ff9,0x7520011036020780500b1fe8,0x40450014f00e576044aa0f00a17f9,73957826527303672,0x8812040f06817f8,0x61c980030b081172a0f00b17f9,0x30a589080f00c17f9,0xe0e260f00d17d9,0xd100f06001e0cc16a02616c058360a7496e50d098224f241e0ffa],
[0xf200d04106008c317f9,0x6c401c726008c397f9,0x3608909ce0f00117fa,0x2d0e001a0208c58ff9,0xfa401a0208c60ff9,0x19301a3860cc68ff9,0x5021602280581e97f9,0xa0619860601e97f9,0xe1616060cc70ff9,0x3a805c8027e2242450f1c1e8ffa,0x3e0c409419860084f93f9,0x2082004040509bd8,0x2082004038579bd8,0x1b0104180201c0400ba2d8,0x372002c0f106182085004038081bd9,0xb8104180201c05c0922d8,0x20820040385e9bd8,0x23802207106182085004038091bd9,0xa812083004038099bd9,688706735313913,0x2c400222199880085093f9,0x13c30040380b1bf9,0x20820040386b9af8,0x9e180201c05c0d22c8,0xb3002e7703090850040380b9af9,0x3e0cc30040380c1bf9,0xd20830040380d1bd9,0x3d2002d01a02801402e80b81c0a0f8137eec11278c0080713fa,4786999836352407,0x8a0e2307c038081fd8,0x301194200201c0500823d8,0xf814100201c0400ba6d8],
[0x146016400c09c0f30f0635004038081fd9,4786999970570135,0x1e2207c038091fd8,0x12194180201c0500923d8,0x6c14100201c05c0926d8,0x16400c0bc0fcf0635004038091fd9,0x58041000a32600c6138c308038c917b8,0x58041000a2860088184b424334c0f80717f9,0x138241060085017f9,0x6120c180201c0500b23e8,0xa011c0064401c32950303199580040380a1bf9,0xc2e1c3004038681bf8,0x18e8c003605a0c241840040380b1ff9,0x18c100201c05c0d26c8,0xb0082000c65401862d090ce50040380b9ef9,0x3e04631830040380d1fd9,0x17a0163c080104031a602c80182706e831525a6830c109f40080717fa,0x9d80a1e0e30a0085313f9,0x9083004058541be8,0x361987184004058079bf9,0x64347c318400405c079af9,0x8c2004060541be8,0x190908c3004060079bf9,0xf86530e3080085413f9,0x95c00120148027803a03415710b1278c0080793fa,26983339959,0x3c812040f85517f8,276248075239,0x2b0b04009ab17f8,0x4f00c13004050551bf8,566112799762119,0x2f00c1300405c551ef8],
[0x10a01004068551fd8,0xc30024100164014164055d42c886c0085517f9,0x1910061040085596f9,26983405495,0x174010460f85617f8,0x1c2a040fc5617f8,0xd80602004050561bf8,0xe5e0200405c561ef8,0x4f0270060d41ac0f68340c6a0085617f9,0x1a2011020048c91f97,0x33c02983307c040091fd8,0xd1002c120200481f9fd8,0x688016090020280400923d8,0xd100880202005c0926d8,0x77807204e00c1a83a81e7011b5004040091fd9,2226013609399,0x1730005035806c1452951c106040c917b8,0x1730005035806c145291838934e0f80817f9,0x282e402949409c80401f97f9,0x1b01004052681b77,0x7e0f051426e0080a1bf8,0x2a0b0913004051b21bf8,0x60e1418021400500823d8,0xa0b900a08e6832de7004050081bf9,0x200800f8243962478a85004050081ff9,0x48830830040400a9bf9,0x301404009b397f8,0x1d041060085717f9,0x3e07c61060085797f9,0xf8104100202005c0d26c8,0x5d4001408a005004022810ade50040400b9ef9,0xd8220820040400d1fd9],
[0x30c03d0801aa00a0bc09c0181a183076028060d29acd57c6442c32bf80080817fa,26983798711,0x39812040f85c17f8,0x4120040505c1bf8,0x60100405c5c1ef8,0x1e802b007d13c2a0085c17f9,316823570257399,26983831479,0x610ec040f85c97f8,0xd03c040fc5c97f8,0x1e010040505c9bf8,0x61e0200405c5c9ef8,0x11d00f6786142a0085c97f9,976778782643961,0x83804086048c797f8,2500879982391,0x640440d2008822141151c106048c917b8,0x190110348022088528b981898ccc0f80917f9,0x220b900e8089409c80481f97f9,0x1b010040529619f7,0x5a0700c140048200a1bf8,0x290914004051cf9bf8,0x4c2c10020280580923e8,0x20804417201d051c4644e6004050091bf9,0x1b10002068e48c808285004050091ff9,0x48830830040480a9bf9,0x11991504004058091ff9,0x61e020040486b9ef8,0x9400d80880f40160981e1c08621c66400405c091ef9,0x1cd041080085e17f9,0xb607c61060085e97f9,0xf7800b41d0f40360221583613803034378287e04826078724b3af7162c2ddf80080917fa],
[0x1a027880086096f9,0xc40020020f85d0263c68278c0080997fa,0x3a0c4088c797f8,0x6fc003c15f00242b098186114c78ff9,0xe05d80320608c80ff9,0x130107d41cc89bb7,668644724053943,4793682268561303,0x130107d424c89fa7,0x78a011307c5fcc89fb8,0x90618307c644c01fb8,0x180818307c644101fb8,0x96807f260f8c897b9,112017872823,112084981687,0xc580099806b0238d0864a0c97b8,16320632759,112152090551,0x1d809b806b0238d086480f97b8,0x38d0541cc913b7,0x38d05420c91797,86449395639,0xd03424c917a7,0x1f705143085fcc917b8,101347563447,0x578011038c1e72a648c017b8,16454850487,112219199415,0x21807780220da9838d086481017b8,112286308279,0x5a801b039051c108a1cc917b8,16790394807]],
[[16857503671,0x1e600f83b828f06088c917b8,0x530008200ba00a80107c33165be4cc90fb9,86382285815,86449395671,86516504551,0x7241c3065fcc917f8,0x1702d06648c017f8,0x140602066481017f8,0x940fc03900e483860cc90ff9,0x130107d41cc91bb7,4793682268594071,0x130107d424c91fa7,0x3ae011307c5fcc91fb8,0x90618307c648c01fb8,0x180818307c648101fb8,0x49400307f260f8c917b9,0xe0a60160608c98ff9,0xf406e0bd00930334c0f80c97e9,0x33c03c28002805808e00f807c0980a00412815002028443439ce10f16324bec1f0ffa,0x58100541cc91bb7,0x2f0a307c00a839bf8,361327304599,361394413479,0x2d701820045fcc91fb8,0xcf0a307c00a841fd8,0xcf0a307c00a849fe8,0x37e0c0614a607c008bf9ff9,0x11502004648c01fb8,0x8818312507c008c01ff9,0x11502004648101fb8,0x223810a507c008101ff9],
[0xb3800822450104008c917b9,0x17b004bb1ba6e0f80117fa,0x67ed0002141394ca0ff9,0x12b60070208ca8ff9,86382416887,86449526743,86516635623,0x1da1c3065fccb17f8,0xcc12086658c017f8,0x4e0c46581017f8,0xc8121c201f60608cb0ff9,0x2a900d0e4ccb8ff9,0x36006e03707900100303c7998f050255c1f8ffa,0x412004050a01bf8,95425927117085688,0x3058583004050a11bf8,0x26010d4056008501bf8,0x6c1c102b004051e422f8,0x1214a48a82b0040500c23e8,0xf016403981fa7858ce70560080a1bf9,0x50080202805907a1e7,0x93c0038200901813004051079bf8,0x34202004051091bf8,0x2603054004168501bf8,0x1c81410020b40502da3e8,0x93c0037e0065810381420020b40500b23e8,0x12780096026804e3006a073ed0516020ce70041680a1bf9,0x1880e810c01b0309ca0086413f9,0x5008020280599c21e7,0x582045840040519c1bf8,0x4120040519d1bf8,0xde060e1420021400500b23e8],
[0x304040c20021400500c23e8,0xba0e40e53c61219560042800a1bf9,0x902b80e3060086493f9,0x682100202814835a2e7,0x2c64420020281480b22e8,0x24f000ec8011c244c6b0020281ac0b23e8,0x1380181e801f002c198c4004050691be8,0x9123418020282b80b23e8,0x49e0003600581f00607a01e808e0519fd0e5ae90040500b1be9,0x1580181e8021009198c40040506e9be8,0x1d5001d8032012c1080303d03c406831e848c95680040500c1be9,0x5607f0042009824e50040500c9be9,0x1d5001d803a0048230020f80102f009001039039a68bb196ab20080a13fa,0x1b8c000811320e0500b1fe8,0x57b000c210020281480b26e8,0x17a01e4c008a04dc02304480fa04a5e80040500b1fe9,0x1250011630040500c1fe9,0x2cc019e4c00b807018aa00904c807c09d0020dc1a1d0610adcc0080a17fa,0x1280aac023049ca0086693f9,0x37e00907860086713f9,0x1278000e800e0841fc0f20020ce05388143aae0080a93fa,7218763703,0x2e50022394841c3597f8,78055905207,0x3620094120b0b0841c7e97f8,0x68102c062459fa7,0x15e8009620228605a4597b8,0x168f520e0580c1fe8,0x114c0051a00184b440c934e41c0b17f9,27399721975,77067388524959736,0xa1cb062b8cc17f8],
[0xd15402c060cc1fe8,0xa090202c068cc1fe8,0x867000bf201010106308e058cc17f9,0x2201056008291ef8,0x1684002cc00fc8039f8318440560080b1ff9,0xcb0039b001082d400c120c22cc0086817f9,280400141047,0xe0f9503004148359ef8,0x88146a0020a40580c26e8,0x1584002858136324e60041480b1ef9,364084894455,0x557000fd003f2003048201004059269bf8,0x253000e38006020c137829a9570041ac0b1ff9,0x8c0f802002004400f0182c0236c0086917f9,0x443c5244850450042b80b1ff9,0x30140400a0517f8,0x6901d041060086a17f9,0x253000bb00f80200200e401820c7c3caa70040580c1fe9,0x1664000c113c40040580d1fe9,0xa0a70011e4400a2c2c6a05d00282307c0102c1706414787871107c2e81cb14526d791cb5f60080b17fa,0x1c4820040686b9ee8,0xc4012c03301882dca0086b96f9,0xe58011840086c16f9,0x26805c06d00981419ca0086c96f9,0x4607e0778024c0ce500405c0c9ee9,0x3898008602da00d0840de0197030466500405c0d1ee9,0x2e40389801d82480c203e1283a018160a82f03428a83a06603ff06584ab00080b96fa,0x1a03060021260086e17f9,0x2d03a01801800b009c12046480086e97f9,0x8200619860087017f9,0x3e0cc30040600d1fe9,0x396000381e2804030ae019d05283a018160c8220a0a1b01e05b02818147e4317f40080c17fa],
[0x2f05c2d018e40c9901981b0086821849ce0080c97fa,0x9872600a3216f8,0x15c002f600ac121080087516f9,0xe26004b03b048400c2c39a38c809d02b01c613ac49dd00080d17fa,0x17601b7c00a833b02c338ec0be03e13804642e062450d050a1b8505808441f05283438040cdf0e33b629bdc010ffb,0x7432046640c97f8,4996483170932728,0x139002e0298800d8aa10cc8ff9,0x350081400e1000ca1e7,0x3a809302801c2019f8,0x570100e1000c9df8,0xc7800d208c6a01c2015f9,0x1c280370076800d41c90cd0ff9,0x194201c02c2019f8,0xa201c080389801e4602c2015f9,0x6208301c0582019f8,0x4b0068f000a1837880382013f9,0x140800940b8200220c20ccd8ff9,0x6de006e832881000997f9,0xd8081415c0582021e7,0x5e00d2e0036060425670280582019e8,0xb05031430281000c9be8,0x168034080071ec18958c0502013f9,0xa0cf07430ce17f8,0x170400a6024b003787412b1cce0ff9,0x29e2604315c058201df8,0x33c00208202c1000d1de8,0x3e017540016e00319912acc0582015f9,0x19c00638e716c81000c97f9,0x3c801921061000d17f9,0x740313800409200129645ba408918dc200ffa,0x8c200a024239bd8],
[0x1fd00594200a024019bf9,0x4120063260142217f9,0x6482928a0142397d9,0x36a00e905cc4c0140197fa,0x9010203200c329bf8,0x199005208c6a00c3293f9,0x170100e1080c9f78,0x588c6a01c211779,0x2a010f601c019bf8,0x2a0100e1f0019bf8,0x30080900e06424a3a7,0x860101201c249bf8,0x830080900e06401a3b8,0x24200ad340c2401201c019bf9,0x30081400e0642223a7,0x860102801c221bf8,0x440a0401cd617f8,0x440a0401cd697f8,0x2060100e064221fb8,0x2e600f940236a01c2217f9,0x3a190200e064239fd8,0x5208c6a01c2397d9,0x3402030081400e06401a3e8,0x8600f873994198c402801c019bf9,0x34060100e064249fe8,0x9f003046506664a01c2497f9,0x19504884492410d050dc500e064019ff9,0x94004a82a512598482e67001c0197fa,777930461319161,19076446359513,0x1ee519899c208ffa,81100254233991160],
[0xa04443ccf97f8,0x278018834c0aa10cf8ff9,0x1e055a0021260242117f9,0x156803c0428602c2117f9,0x56a00f8508d00ff9,321117672738809,0x158803e0446034211779,0x156802868378a0382113f9,0x2ab004d061061080793f9,0x2b50018c20cd10ff9,0x2480820cd18ff9,0x6827c2881080997f9,0x2a700020985880582117f9,0x159803c38590d20ff9,721713634643961,0xaac01a24128060211779,0xc1301825c81080c97f9,0x2c041061080d17f9,0x2b021900020786ffffb2062f29c210ffa,0x1942012108239bd8,0x35d005942012108019bf9,0x604300823061082217f9,0xa0907061082317d9,0x8c04450550a1082397d9,0x2fb00460f482884a1080197fa,0x74c00d072401202c019bb9,0x74402c2012034019bb9,0xe88052841e40193f9,0x1cf00e3041e80193f9,0xe68022066a25012040019bf9,0x2473c4012118019bd9,0x71a508c401211c019bd9],
[0xe88031c083012048019bf9,0x2b2019823049ca1ec0193f9,0x2b2018827809c81f00193f9,0x170223012058249be8,0x38e0170b64012058019bf9,0xa11860242413f9,0x8c2012060249be8,0x16300ec11824e5012064249ba8,0xb1806205cd049ca0242493f9,0xe2806540c2012060019bf9,0xa7806e0d1824e5012064019bb9,0x6fc029e007819ff5dd30262d4e0240193fa,0x2058914498a0242397d9,0x1d10091800a0541a528894e0240197fa,0x684037c042884c0280193fa,0x420e58802c2217b9,0xdf008e0134301c02c019bf9,433968287736,0x1a5009827882240197f9,76812432812775385,0x1af0031e28602c2397f9,0x1ae00ab0341a15f82354e02c0197fa,0x18c1638e0cd30ff9,2098440933337,0xfe145b12a0218ffa,0x15c00b605e0230cd40ff9,0x1168320608d48ff9,0xac60342217b9,0x59800c61060402217f9,0x59800c61060482217f9,0x18e0088508d50ff9,94583918006265],
[0x23c0162e143028058221be8,0x46802c2028060221be8,0x1e500520724e5028064221ba8,0x1e5004607b849ca0502213f9,0x22c01a11861100a93f9,0x3f8018e16c80582217f9,0x1e400c68241860602217f9,0x4e0c46b01017f8,0x5801781d2210d60ff9,0x4e0c46b41017f8,0x2f03082c28610d68ff9,0x1d90042018d2cca0642217b9,0x4fc031600b0280c17018fe4e9621944b2a4220ffa,0x5049881102317d9,0xa02811861102397d9,0x35b00341020e47194a1100197fa,0x191001e0508d70ff9,97032775899097,0x7780248060587b54c0340197fa,0x14b007088308401c040019bd9,0x51c02464308401c048019bd9,0x28e0110648301c04c019bd9,0x28e0041042800193f9,0x1a8008800c1bc401c058019bf9,0x27a0030208301c068019bd9,0x15805e0482c0707f7011278c0380193fa,0x25403e81d063062980193f9,0x30802303984855b8e03c0193fa,0x68161080402397d9,0x33401105084028040019bf9,0xdea00220c20e870ff8,0x31c028837882b80197f9],
[0x37c00c61060402497f9,0x62803868143085020068019fd9,0x14600c81f07818ae38342aa700400197fa,0x5981638e0cd78ff9,84473429878116345,0x73090ab12a4228ffa,0x43e0984c242d89501180197da,0x110610666c2397d9,0xc61066882397d9,0xc9046a82397d9,0x12c410a0582397d9,85729472986453977,0x1c402849ca0642397d9,0x41046c42397d9,0x385e0e741a1fe8b7298238fda,0xe18ccc80482397d9,0x35a01c6284604c2397d9,0x6ac0121060582397f9,0x6ec008208d88ff9,0x33e01427260682397d9,0x19403102e051d030a3f7011213e4238ffa,0x21f0443c4c2945b95011c0197da,0x5f805083028048019bf9,0x33400c61060482497f9,0xd500f0d83c2e1ce862c572e0480197fa,0x3180cc0101c0f0b818d1e1210a04c0197fa,0x4f01a814101415c05801a3e8,0x3205903507a044be8028058019be9,0x1bc06e0a54028060019be9,0x1500301903701424e5028064019be9,0xa80181500a0387260cf925cc0500193fa,0xf80bb023011863340193f9],
[0x6101a83a512a10e0540193fa,0x52042b8ce17f8,0x3c123380580d1fe8,0x32c06960b070a8c6700b17f9,0xec1215c058249fe8,0x10c07362141404415c058019ff9,598967792930808,0x5f00783e0107883500197f9,0x86011f0112ace0582497e9,0x1102880e78f1b08502c068019fe9,0x58346088060280871c50212fcbf540580197fa,0x7d81638e0cd90ff9,0x8281c230cd98ff9,17997336547289,0x2681ce0a28209e0240ffa,0x29804682c80602497e9,0x9a01f05302452cca0642497e9,0x2c0060485c010440a0c1853e4324b9c248ffa,0x740550d8160181c35246de500600197fa,0x321d0680c0c743060181c36453dd00640197fa,0x542900b01710c2d070705bcc0680197fa,0x234056e00a832219214382f32436e2e688a75894137d16dbe4018ffb,0x1536001c7260108117f9,0xb07020460102a1df8,0x558a584046014021ff9,0x1e7001561428108a08c0217fa,31220332924921,5248665718777,0x3de00750a38a69c250ffa,0x155e001c726010a697f9,0x4104010a797d9,0xa370004ee1619dce0101697fa],
[81100282004281336,79337067511,79404176887,79471286007,0x77104066dc8717f8,0xa0446dc8797f8,0x1a0a046dc8817f8,0x156a0009e0808db8ff9,3166735539447,0x2ae400760280e061502595f8,0x78c4014dd17f8,0x7c070200a058259df8,0x84100a05c259ef8,0x34555800ff858b044a0142597f9,0x150082016020259cf8,0x281c08302c020259cf8,0x559800f20e060202596f9,0x1562000b050890dc0ff9,0x3c74061dc2596f8,5491236565456888,0x1557800f26022ca0242597f9,0x154a0038982844802c2595f9,0x2acc00220b162880342597f9,0x281c26050dc97f8,0x155200097190210dc8ff9,0x1a0a05440dd17f8,0x2a0619aa050dd17e8,0x1506003c7a82844b5cdd0ff9,0x6a910006260c6185028058259de8,0x142a8500194c0e022ca0502597f9,0x8f8683056058259df8,0x393020d6058259df8],
[0x2a340058430302c060259de8,0x29840012c2e7811132c0582595f9,0x342614302e064259ee8,0x2984003430c1ca32c05c2596f9,0x150e0009c3876c0602597f9,0xa0cd816c80642597f9,0xa530014ddac88b98672910dc258ffa,0x63e6002e0bc0208dd8ff9,557744528631,0x16a0075820120102a1df8,0x7c12309c0102a1df8,0x340c5d040080442a1cf8,0x24b001172003e0a5830280102a1df8,0xac0420a40102a1df8,0x6a0100847cf81cf7,0x7e03818a2a010f815f8,72503858604579062,72339699384491222,72339699451600102,0x7340102008474f89cf7,0x6a010087c48f9cf7,0x4d50126010f895f8,555399978231,0x1080402e0642a24e7,0x92400073001d07c1c0a3500805c2a1cf8,0x3e1b40080602a1d78,0x6a010083902a1cf7,0x1ad81c230080642a1df8,0x12580009a00140107aa6a886c1e2f00102a15f9,0x1481100500847c2a24f8,0x30900500805c2a24f8,0x19b016300a0102a1df9],
[0x7c284010fc95f8,0x843642881580217f9,0x2707832880102b97f9,0x2e0d0100a0103b9ef8,0x12580015e0044174534a0400a024021ff9,0xc0b03288c0142717f9,0x320480e0b0304500a138021ff9,0x521a1e06080142797f9,0x2c7868180500802c08a4f8,0xc85d051422700a010059df9,0x72300a010069f79,0x205851880142817f9,0x90b05c06014ef97f8,0x6503108138c0142897f9,0xe523018050080400ba4f8,0xca0d32500a010081df9,0x341ce8180500805808a4f8,0x6c0451c28c400a010089ef9,72503858605562102,72339699385474262,72339699452583142,0x7340102008475079cf7,0x6a0100847d079cf7,0xa020eb01260110795f8,0x78047250b40100b1de8,0x670c876c1680217f9,0x2a09c1e0c26c0102d97f9,0x924001090033e03810050280100b25e8,0x312280042bc006c0aa04541418500a050021ff9,0x78c4014f197f8,0x4a20008780151a30e0e89760142917f9,0x2503c0e0b0304500a148021ff9],
[0x1a0a04014f397f8,0x10f0014506c4826e0142997f9,0x4e05818d42360100b1df8,0x1213044008058f81df8,0x28210050081ac0b2578,0x12023928050080580c2568,0x1268000ce001200c02373e4220c8b7a00a0100b1df9,0x460d04200a0106b1ef8,0x2303a02100500805c0ca6e8,0x1208000e600320a04261a44144b700a0100b9ef9,0xc818783b500a0100c1f79,0x4609404200a010721ef8,0x6c1b9830a82500a0100c9ff9,0x1a08b4007807e002c2a0b0cabad24229533554281858f3f60140217fa,0xad05488002207198cde0ff9,0x1b300d30038cc60102e96f9,0x70178c81402f97f8,0x285c0417c2897f8,0x585820080402f9df8,0xc6a020080442f9ef8,0x7c1fc58698308c0102f97f9,0x309408a081403197f8,0x5819041b1c70a1400317f9,0x285c0418c2897f8,0x90b05c0677c0317f8,0x4819ee108610a1440317f9,0x52170180402005c0324f8,0xc2e1c3008040319df8,0x1c023ea24008040031df9,0x402c04431a4e7,0x7c78e8180402c0440324f8,0x4880e13008044319ef8],
[0xa07194330b05008044031ef9,0x2dc40071028c16888ff8,0xe0dc29b0f30901480317f9,0xf0384c18450a4010031ff9,0x302b0f030614c0317f9,0x240420088640b1df8,0x2c063a0ca64008058319de8,0x221cfc4416a66008058031df9,0x30d0451f0cce700805c031ef9,0x19044273734c19cc0103197f9,0xd8b622f7f171a28b520100317fa,0x5618000901fc0cde8ff9,0x38104024e117d8,0x12c18478a0242617f9,0x74020a890fd8,0xb8f0cdf0ff9,2181992255481,0xe198ce00ff9,0x70cc6130e097d9,0x38104050e117d8,0xe6c382110e10fd9,0x2489020ce10ff9,80071252213045209,0x88082098040091d58,0x7e09861300815f9,0x887861300896f9,0x1be0986130091779,0x480c040528997f8,0x11b06178a0502617f9,0x74020a8a0fd8,0xc4130ce18ff9,2181992419321],
[91224698151245689,0x26900058c004bad69790e2c0432aeb0260ffa,0x9110104010e117d9,0x1581c19dce1300217fa,0x26038389168a8ff8,72341848194849767,2779188304871,0x346186050e293f8,0xd202047140c97f8,54857719,2415799735287,30439085559,30439118583,0xfe1267148717f8,0xa0447148797f8,54890487,2416269497335,0xc608247148817f8,0x57f200359d9184310e28ff9,0x1cf1e02081ec2697f8,0x61833e081f02697f8,0x22008100902806426a3a7,0xa20f13012050269bf8,0x261e0206024e417f8,0xd30f0103012064269fb8,0xb2800682ba98140464c0242697f9,0xb8061a0890e30ff9,0x707021101080402695f9,0x1c010fa080442696f9,0x320084890210e38ff9,0x2e00c054540a17f8,54923255],
[0x5a0b05063202697f8,0x21209702028064269fe8,0x1810004691842ca1c92a0502697f9,0x2e00c05454e417f8,0x20c8020d0928b0ff8,0x1a1e020745ce417f8,0xc180143848ef0141884e5ce40ff9,73889388279,0x90841347216f8,0xe18639a84a0cca0642697f9,0x61c001873d84d65c0c28d8268ffa,0x2a066300802c371cf8,0xe81c083008058371cf8,0x80c00f20e060103716f9,0x1e15033200900802c0424b8,0x260b038a25012010041ef9,0x30306180401602006a438,0xf6032920d04e500802c041cf9,0x138a23008020069e79,0xc43861400416f9,0x208220cc80202896f9,0x44041004020020092458,0x5f0082008040041cf9,8013653332268793,0x3b08810880103996f9,0x24888083008020091e79,0x88140080593a24e7,0x104120280113a1ef8,0x2650418140080580424e8,0x3740e394028010041ef9,0x3a038102b0080580424f8,0x18186180402c0200c2468],
[0x3d80082d94664008058041cf9,8007056262567673,0xfe040103a96f9,0x12a0c20080200c1e79,0x8ac0008d001ec025d726f90d8374e0100416fa,0x11f30034c04c0c3394e48ff9,0x2302380c81409ca0103b96f9,0x3c3a02240120103b9ef9,0x43e14300802c3c1db8,0x4e0683d0210d303080103c17f9,0xa15066200900802c08a4b8,0x320c38180900802c0925b8,0x77c00a82e20d02e6012010059db9,0x43600563012010069fb9,0x2d022012038289fd8,0x150a8100901c0100825d8,0x1f5c1c5012038021ff9,0xb80204024eb97f8,0x6201011bce0242817f9,0x12d832c80242897f9,0x782c10090080400925d8,0x32a819a45012010081df9,0x21022012010589ef8,0x48c4221a45012010089ef9,0x304e41e04012010091ff9,0xd00b012cca1ec0217f9,0x64280048861f02997e8,0x2c0f90316ca0103e17f9,0x1808a18090280100b21e8,0x10f810090280100c23e8,0x9809720090280100ca3a8,0x681d2e4012050021bf9],
[0x8c2604e50120100a9bf9,0x8856ca0242917f9,0x72c82a880242997f9,0x8142c18090080580c25e8,0x396415440120100b1df9,0x1d022180900805c0ca6a8,0x162e0d440120100b9ef9,0x5094085287050120100c1ff9,0x340e65404e40120100c9fb9,0x449a002194006c18980c81a0d0d6e54b44e974818285866b560240217fa,0x920a910019201c3290e50ff9,0x20b0009c1060103f16f9,9289225553190135,0x13606460115615f8,0x108168481483f97f8,0x86c041fc2997f8,0xc85a020080583f9df8,0x30850200805c3f9ef8,0x5702080f8405008a4c0103f97f9,0x6032061061400517f9,0x104c61061440517f9,0x40883083008040051df9,0x3e1183083008044051ef9,0x1701830c18140080580521e8,0x442a24e5028010051bf9,0x650800880a0f1928c0ff8,0x58711853194e1480517f9,0xb0e2c82cc814c0517f9,0x24042008aa40b1df8,0x360883008058419de8,0x1238cc50319666008058051df9,0x38d04481438ca700805c051ef9],
[0x120d61449cc0104197f9,0x24d003e7a5dcc140a1bf20100517fa,0x1c1204048e597f8,0x3a0c4088e597f8,0x15620004601ac26121114e58ff9,0xa830a8c8ff8,0x170570350c8ce60ff9,0x1e80e1448138e617f9,0x143041080382717f9,9367473000441,4956541620217,0x312121081380917f9,695308900734905,5357969904996345,0xb02c0888060e817e8,0x69090b94e80ff9,0xb0e309c1ac0b1df8,0x2c38114409c0580c1de8,0x388085ca1380b15f9,0x16044309c05c0c9ea8,0x4c10861380b96f9,0x6272609cc1380c17f9,0x30205a81380c97b9,0x12b800186001500ac02feb2e50a70c6496ac270ffa,0x2a012800e0740cc8010e597f9,0x760141c726010e617f9,0x1ca03c50a586108e1380217fa,0x1d0300070210ce88ff9,0xac8070208e90ff9,0x90fc08e98ff9,0x15002020d6058279df8,0x68e38114402c060279de8],
[0x919428a880582795f9,0x162844605c2796f9,0xa37404280602797f9,0x6818210cea0ff9,0x62801c2009ef312348e72a0278ffa,0x150a100401604406a4b8,0x6b03a2e500802c069db9,0x88294301c010059df9,0x1b06860104415f9,0xbe01040104495f9,0x115008300802c589cf8,0x19c08300802c599cf8,0x15051180401604409a498,0x114037019d2023408400802c089cf9,0x11c071208400802c091df9,0xc78394300802c099db9,336868378252793,747943525717497,336863147922937,747943057790457,0x1d011180401605c0ca4a8,0xa22300802c0b9cf9,0x16a400802c0c1df9,0xcc54300802c0c9db9,0x25500017c00a402202e0d40e4fd7f81862d4e0100595fa,0x310050e3888a0104a97f9,55821934071800,96942432971296761,0x38104c300216f8,0x1714460104b96f9,0x3c02230080344b9ef9,0x130541861400697f9],
[0x1919860342897f9,0x3e0cc3008040069df9,0x361b0d0e0c5008044069ef9,0x483a05ca1480697f9,0x510542860342997f9,0x163a043008059851df8,0x18186180402c0340c2568,0x67828b65008058069df9,0xc74092500805c069ef9,0x10a4c2880104d17f9,0xf1c72880104d97f9,0x6641c0830080340c1f79,0x9540005f00170181600702e0cc03825ff7ce170b122f560100697fa,0x6403041060104f97f9,0x31201c050289fd8,0xf0e26038ef97d8,0x3d9000040743041080382897d9,0x3082008040509dd8,0x6022c180e0280100825d8,0x8808201c010579dd8,0xe0080406b24d7,0x904100e0080400ba4d8,0x12070001406bb0304a2501c010081dd9,0x143041060105097f9,0x6c0c100e0280100b25e8,0x4a7c0c2418401c050021ff9,0x3c1204038f197f8,0x13041060382917f9,0x140a02008059a01df8,0x27208401c0100b1df9,0x5090101c0106b1ef8,0x31208201c0100b9ef9],
[0x524d0019207003107c0d06a524a0804496700380217fa,0xf42a44002dc008208eb0ff9,0x760be40027860105216f9,0x1d4074041060105317f9,0xd77001f0c60e8d8ff8,0x63d0e3081480797f9,0x24042008d040b1df8,0x2082008058541de8,0xc7e220b185008058079df9,0x141147c318500805c079ef9,0x1921060105417f9,0x4ae00192801d6f70d1426c0100797fa,2337847252967,2182020468728,0x26c02050eb97f8,76579062489520088,0xab30016600e407a860410eb8ff9,0x6415203e1fc10ec0ff9,0x120ac0fc08ec8ff9,0x1c6c020528e97f8,0x64d044348a0502817f9,0x1c40907061400a97f9,0x60e120a8f0ff8,721563312525305,2181993172985,0x60a241881400c17f9,0xe0e0e261400d17d9,0x1632001705c0281f00c0d0b4118355eb8b0278cbbac280ffa,0xb0383388c1400217fa,0x3b76003790ee0ff9,0x684c03308ee8ff9,0xeb02438d10ef0ff9],
[0x1a090d832c80502897f9,0x1c4c61060542897f9,0x18919860602897f9,16792917975,4574137956767704,0x880a0f1928f8ff8,0x641de011058fe1302110ef8ff9,0x3206e07c030190020b817c9981414998288ffa,0x10402c0c1060105695f9,0x244d018140080400925d8,0x40200486b24d7,0x1384404180402005c0924d8,0x151003d07c1ac029c2c38a25008040091dd9,0x1e06022c20a00280100825d8,0x2f012a819a45028010081df9,0x28830830080400a9df9,688706869990905,0x1d83101040105795f9,0x168046c08430080406b1cf8,0xf804100402005c0d24c8,0x320f7016839e864408450080400b9cf9,0x3e0cc30080400c1df9,0x620820080400d1dd9,0x17e00360c80e0b87c0104e0982c250117dcc22092c4e0100815fa,0x906808300804c589ed8,2749076512487,0x15830a06011ba96f8,5630050772231399,0xb1028010589ef8,0x4434100402c06858a4c7,0xa50a083008058589cf8,0x268082008068589ed8],
[0x43a002902e8092ea16060105896f9,0xca083008058599cf8,0x3481b40ee0e080105996f9,0x164070d0a23008044099ed9,0x8814008059c124e7,0xe31028011c11ef8,0xc2a66181400805808a4e8,0x18e21a44028010089ef9,0x31830830080440a9ef9,0x2a1a081580402c0440d2cc7,0x1a8282182b00805808a4f8,0x1102408020160220681aacc7,0x6a1d02180402c0441aa4f8,0x1d0e810040d605808a4f8,0x3506180402c0440c24e8,0x484408504180402c0440d24c8,0xe8102019845e10a083008058089cf9,0x7838904011c296f8,0x1687260105a96f9,0x3101040105b16f9,0xa660c30080440c1ef9,0x214680820080440d1ed9,0x34c007c1301c170041f0bc0b07a0292217f16070672500100896fa,0x703810140080580925e8,0x1d05489a04028010091ff9,0x1c1204048f197f8,0xc86821081480917f9,0x10e12084008058091df9,0x9409010080486b1ef8,0x118290208300805c091ef9,0x12d8002820018ec0be1380703d01902a98672c38a700100917fa,695303940380409],
[0x36439a40c8646c0944a0100997fa,0x176003634a41c2d17f8,0x3e801a0dc28841e9017f8,0x11145520e0500c1fe8,0x32808aa0028d001e9007080892ae41c0a17f9,35382105591,8193979022579704,90388928159324152,0x707854028060f01fe8,0x551800ca802fe18b0d4cc050f017f9,0xd0220560f8021ef8,576683744438,4512121128197367,0xd09183e0b40100b24e7,0x39c0102407c168021ef8,0x288339a83e0280100b24e8,0x73d00289183e0280100b26e8,0x39983e0280100c26e8,0x72f0009f2060cf707c050021ef9,585166462199,0x2b780070801f1801ce6b0582028011079df8,0x24f000fc40011604020208b05a0280100b25e8,0x24f000f5c00608a7c641431570b4050021ff9,0x4fc0020f06184008058639de8,0x420b6c0210d303080106397f9,0xcc0783620085088134e0106417f9,0x1e2619420a00280100b25e8,0x3604c5060b04140050021ff9,0x50081400805926a1e7,0x24f00102c009c2428220140081ac0b25e8,0x500814008059b3a1e7,0x322428220140082b80b25e8],
[0x3124800c10c00e4180c0020b84300e803088516ca63a1625a90280100b1de9,0x24f00082400cd00c3010041caa60280100c1fe9,0x760048025a50280100c9fe9,0x14223b000210430039060201a0b86429308605c2468980c2430c11533982858cb5f80500217fa,0x3142a44006f401c3150f08ff9,0x1383ff0009c1060106596f9,0x6a0100847df11cf7,0x534601360126011f115f8,0x1384d40361b056c0106617f9,0x5a00200f0182418ccc0106697f9,0x12780040e00158091a261b83dea140a1bf40100a97fa,0x6d80170254882917f8,0x89018a8148f117f9,0xc3a34f195f7,112624506855,0x6304c1228948cf197f8,0x4c0c5490f197f8,0x78c478c0f97f8,0x605c05494f197f8,0x3a0c4088f197f8,0x5528000a00ec01f81683f21d0284b5cf18ff9,0x1b077807a0d0414a9217f8,0x1889018a8148f197f9,0x11028c03c38250f20ff9,0x3a7c00170254982917f8,0x8501728148f217f9,0xd0af00e8110cf28ff9,0x3c6b008208f30ff9,695309169399785,0x9ac000c10009064238130380e038441414038128042af248b8722568290ffa,0x541e10010d0740cc8010f197f9,0x4f8051c726010f217f9],
[0x1209b806b0a586108c1480217fa,0xd6520030601a0422114f38ff9,0xfc0a938fd8,0x30700c4130cf40ff9,0x2eb015030a1994f48ff9,0x8d80fc08f50ff9,0x314001c1f40985a038398022f23609315c298ffa,0x5c2c102b0080580da4f8,0xac12008058a01df8,0x1c53056010359df8,0xb038102b008059f5a4f8,0xd81102b95e0100b20f7,0x38082b00805afd2477,0x11102b00805a58a4d7,0x11102b00805a5924e7,0x7f2a121202b0080588ea4f8,0x2a121182b0080588fa4f8,0xa0e0314056010571df8,0xd86c182b008058a2a4f8,0x242a050a02b0080580c25e8,0xae018a7c34202b0080580d25e8,0x2530000f40012079036403b03b3fb130a224480560100b1df9,0x1e00ac12008058b41df8,0x3c4c0e140082b81a9df8,0x5b00c51b0180402c0681aa5e8,0x14c0f31438318ce80080581a9df9,0x4a6001fb801e8068042008059269df8,0xa801010040d60580da4f8,0xd858540081ac451df8,0x100caf0081ac0b20f7,0xe808040d605a58a4d7,0x1008040d605a5924e7],
[0x7483401018040d60588ea4f8,0x1e0518040d60588fa4f8,0x58e810040d6058a2a4f8,0x4a60001d8001c05320340f80840c806193f20c8b670081ac0b1df9,0xac120080596a1df8,0xe1e170220041140580c25e8,0x8cf0512e60082280b1df9,0x1d6018a860106995f9,0xa815819b03008059b39df8,0x9414187488460082b80b1df9,0xd403e01040106a15f9,0xf38008c63250080586e1de8,0x94c0003b0031058ea0120741a0f0510258050a68cc8ca80080580c1de9,0x2580458220830080580d1de9,0x4a60001d8002c00c0cc0241504868282c1a0e11002070582b01146aacf058cee0100b15fa,0x741420080646b1ee8,0xeb0005e014815067024dba05d00106b16f9,0xe1005010a848a0106c16f9,0x100d01040106d16f9,0x6807601d0060f70045404e400805c0c9ee9,0x2180208200805c0d1ee9,0x22d00018c001a07c198058260b0b090383c142e0e838ce07c8d809ee0100b96fa,0x1e5007070e480106e17f9,0x6e80ca809ca0106f97f9,0x4a20001f8015806148103011207416120704e80c1c3e0d80b80a3b86449bf60100c17fa,0x49401d07271340216f8,0x3b024601106809ca0107216f9,0x3c0760420f0580c64185033008c0e734158613520100c97fa,0xcd0a6430f02307044406041080100d17fa,0x12c0001c03e7006c780781b07823c1502c110686509048241c042e021f01087070e1a88839b68829bdc020ffb,0xc45000d8338e504a014061ff9,0x4202204a016579bf8],
[0x202204a016581df8,0x4202204a016589fd8,0x4202204a016591fe8,0x581204a016599fe8,0x1f02070c2404a0148e9ff9,0x38360658404a0148f1ff9,0x6298006c1a12404a0148f9ff9,0xc53000d8338e504a0140b9ff9,0x581204a0165c1bf8,0x181204a0165c9df8,0x581204a0165d1fb8,0x581204a0165d9fb8,0x581204a0165e1fd8,0x1fa41c51404a014901ff9,0x38360658404a014909ff9,0x38d8061404a014911ff9,0xc63000d8338e504a0140c9ff9,0x581204a0164f1bf8,0x181204a0164f9df8,0x581204a016501ef8,0x581204a016601ef8,0x581204a016509fd8,0x1fa41c51404a014871ff9,0x6378006c1a12404a014879ff9,0x38d8061404a014881ff9,0x18760029e9e9f139ca0940297fa,0xbd000090007e0014e00a8308f58ff9,0xa7007e0441dc2a17f8,5361501832091640,0xf0441f02a17f8,0x808090280642a23a7,0x2f80a130120502a1bf8],
[0x414010120642a1fb8,0x171c00e85e80ffa0029401ae88c6a0242a17f9,0x39a4006508f60ff9,0x2ed80008332801f8508f68ff9,0x4e0c41504697f8,0x1c0204030f817f8,0x1c0204030f897f8,0x7002042482a17f8,3308402646887,0x31c0424c2a17f8,0xc02e0642a26a7,0x3101805c2a1ef8,0x4f120180602a1f78,0xd10180642a1fb8,0x5c2f0543003d03d8052c400e971c0d0937520302a17f9,0x48161c301c0642a1bf8,0x2cb801adc00cc14680382a13f9,0x190103203c2a1bf8,0x5950035b801cc146803c2a13f9,81100254236579832,0xa04443cf717f8,0x58b400ce1a2a0e10f70ff9,81100254236612600,79338902519,79406011895,79473121015,0x1d1a07067bc8717f8,0xa0447bc8797f8,0x2f01c267bc8817f8,0x5b50035c80127fc1208f78ff9,0x5950015805040039c00b814c1880442a17f9,0x653a063102a17f8]],
[[0x59f00168186400fe0e12804c2a17f9,0x30680174c001c014010280642a1fe8,0x1a3068006203fd800a1006141a2884a0502a17f9,0xeb006204447cf817f8,0x89480056803a17c12831458f80ff9,0x758002032bcf893f7,80546928119,0xed0068452c4f897d7,0xed0068452c8f897e7,0x39401f681c648474f897f8,102961288695,0xc40e120887c48f17f8,0xf100620447c48f97f8,0x1644003da0014600e83172838254f88ff9,0xf1004e0c41506b17f8,0xb802043642a17f8,0x53800d02102e0642a1fe8,0x880e2ad8011401d008088004f8008383e860a0f3f405c2a17f9,0x1d940014e0034061e0236c0602a1779,0x4e0c41507117f8,0xf5007432043902a17f8,0x5c011584008e012d0008300139449671e3661a1c279f40642a17f9,0xe1261507495f8,0x488876083b02a17f8,0x56f00248187c00ff03164a0682a17f9,0x190294cc008849004c07da00580fa00e6e12c2292304ed4c089be02a0ffa,0x3080500e0302a2578,0x1080500e47c2a2578,0x3080500e05c2a2578,0x3080500e0642a2578,0x1080500e43c2a2578,0x3f22907046500a01c2a1d79],
[0x19601f4801d2c00a4890c8284500a0302a1ff9,0x32c031b8003f4014912812400a47c2a1ff9,0xcb00ffc00472001fa00a486414e500a05c2a1ff9,0x1960200801ccc00a486414e500a0642a1ff9,0x6580b330014912812400a43c2a1ff9,0xcb0100400c8b4001d400340fe40417069ce0142a17fa,0x926014b817f9,0xe460e02b97f9,0x5e068648014ba17f9,0x40d836a0e02d97f9,0x6120a640700140c9ff9,0x1583c230700164f1bf8,0x1583c230700164f9df8,0x1183c23070016501ef8,0x5812070016509fd8,0x7c8ac12325070014871ff9,0x1e0223070014879ff9,0x40cb80436070014881ff9,0x2bd801ecf6042ec0e00297fa,19851516317688,81243359914235768,0x139005cb000010056401dc120e0cf90ff9,0x156801302a4c0108184480242a97f9,0x55a0094142801c328602c2a97f9,0x54080120e08f98ff9,0x15a802d04fa00c20650cfa0ff9,0x2cc800e82840342a9779,0xab401748037860382a93f9,0x2ad005ce00e10403c2a93f9,0x51880120e08fa8ff9,0x56a00ba401c208fb0ff9,0x540930280602a9f68],
[0x38f00406008a042280502a97f9,0x506c054a00b17f8,0x90704058fc17e8,0x3030c302c0602a9f68,0x153803e80e9803471867060582a97f9,0xcf780120e08fb8ff9,0x2b30059a00f1b281820cfc0ff9,0x2ba800e084a318aa0602a9779,0xa0a83002401c04a057401ff44fe18599982a8ffa,0xd85861582a97f9,0x6326014fa17f9,0x72300a0342a9f79,0x1580411881682a97f9,0x140100a05cfc1fe8,0xb8840cd4c014fc17f9,0x48c1232500a0602a9f79,0x309018300a0642a9ff9,0x1e022300a43c2a9ff9,0x13a8031f003c3afcc08c6a0142a97fa,0x28454ca0142f9779,0x6ca334ce01403177a,0x29dc002100a01c3b9f78,0x29dc003a0100a1ec039f78,0x29dc00620100a01c3e1f78,0x5c040280902801c0cab27,0x1e8020980501205003a378,0x14ee00178900501201c0ca738,0x13a400d850035ca011b500a024039f79,0x173e0024646014339779,0x173a0034704014341779,0xa7f00170100a01c469f78,0x2f0080500e040062578],
[0xba1000410b401c061f78,0x5d0800000e0302d9f78,0xba1001100a1ac061f78,0x5d0800000a030361f78,0xba1001100a01c491f78,0xba1001100a01c499f78,0x2e8400440280701805c0cae27,0xb9f001880500e0300ba678,0x2e74002880500e0300ca738,0x7809ca002a1a000903faca0382a9a800a01c061f79,0x5800e0400ca557,0x14406340b001c081d58,0x5cc8005c10b001c0c9f78,0x17320030c0466a160039779,0x5ce800000e0642c9f78,0x5cc800d8180c6a01c2c9779,0x280e00e0400ca957,0xb2031a00501c01c082158,0x5d6800470e8100501c01c0ca378,0x2eb400658263500a038039b79,0xb8080500e2880ca177,0x575e00258263500a01c511978,0x2b8080500e06407a378,0x1658263500a01c079b79,0x2f0080500e0400ba578,0x2e840050c000500e0400ca578,0x9404980500e0400d2558,0x2e240048a73920463500a01c081d79,0x5da8001823838400a01c089f79,0xbb5001d0100a01c621f78,0xbb300124151400a01c099f79,0x5b8800f810456c168039779],
[0x5b8800e8488c6a01c2d9779,0x14de00130041100502801c0ca768,0x9d2006bf8018d02a41442500a050039f79,0x2dc400060d0236a014359779,0x5b8800041d08c6a014361779,0x2b140044061300a01c6b1f78,0xbb300170100a01c6c9f78,0xb71000181080500e05c0ca768,0xd604e500150900088186163943e0488f900a01c0b9f79,0xac900170100a01c711f78,0x2ecc004a0100a01c721f78,0x1a409ef0019808a084442611459429e3c08f900a01c0c9f79,0x2ecc001209050300a01c761f78,0x171a000a1240a3400a01c0d1f79,0x19409ca0050d003907208884256b265883169f201403977a,0x2103261584a93f9,0x1cac00f850a948ff8,0x6be00db4004c400214015b01b1b0590fc8ff9,0xde800360071c01660160d8cfd0ff9,0x2103261583c1779,0x2103261582b97b9,0xf86c61580597b9,1726727688185,0xba0c8cfe0ff9,0x1609a2881580897f9,23102779985913,0xa8184068ff17e8,0x18c61a0890ff0ff9,0x50240405a9497f8,0x245e022861580b17f9,94595801473095545,0x185031e1881580d17f9],
[0x1e3c000de003ba005fe97883c2a982b0ffa,0x1a5801083e0584014fd17f9,0x1fc1e1301260143c1779,0x926014ff17f9,0x685861582d97f9,0x5c0b1fcaec1580297fa,433969238008,0x240a267fc0c1778,0xe3e8008901c8240e0cff8ff9,0xd9b003180c94020d000ff9,0x343303260242b97b9,0xe0f02187080442b97f9,39642699173881,0x3437030e0d010ff9,0x17024054a80b17f8,0x6030c302c0602b9f68,888681766459368,0x1811c3067060582b97f9,0x14220c30300682b9f68,0x1811bf0ca80602b9779,39642699239417,0xb0a0930c651020ff9,0x702140c187080682b97f9,0x20400b407204811f22f881419a982b8ffa,0x2ab8012034032840150017f9,0x2c200a0342b9f39,0x9261682b97f9,0x7194300a0602b9f79,0x63260150217f9,0x2d8030387d4844a0142b97fa,0x194057a00283580022c60143b17f9,598277673949176],
[598277741058040,0x16090200a0383b9bf8,0x4240274801048010040071007502a81ea1e19ca0143b97f9,0x15ae001d0042c300a024059fb9,0x12c300a024069f39,81100258452281336,6197128321701880,0x808580120500ca3a7,0x4a8120b00240a1bf8,0x45c010b00240c9fb8,0x65ef0013052b3160c6a1600497f9,5361501832255480,3581737213895,0x9a0c41f02c97f8,0x90280642ca3a7,0x310120502c9bf8,0x510120642c9fb8,0x193010120682c9fd8,0xcc820028a5e2160c6a0242c97f9,0x760e32860143c97f9,0xde049880143d17f9,0x6c1200a1ec071bf8,0x1e0080501c0683e23c7,0x1bc1200a0383e1bf8,0xe83300a024501bf8,0x1617098050120380ca3b8,0x1136098050120380d23d8,0xb23800905e2040e0463700a024071bf9,0x8c200a024521af8,0xc8c200a024079bf9,0xbea000d01c0422110400a024089ff9,0x340e11861680497f9],
[0xcc1420120502d9be8,0x1b8363260242d97f9,0x86804b0800ea007019051458282dca0143d97f9,0x145871c200a0683e1fe8,0x10d00961001d40be071438c42dca0143e17f9,0x3a0101818050120500b23e8,0x1610050120500c2368,0x18da003a817c0e4c0f05728050120500ca3a8,0x10500969001d40be070c08678c0216e600a0240a1bf9,0x594200a0240a9bf9,0x356f800220312170430400a0240b1ff9,0x44061c2c300a0240c1f79,0x10b00963001d40be070c6861e0ae500a0240c9fb9,0x4a0e230a1c040e1b0400a0240d1ff9,0x1f600215780196023011ff00024007b002b00b00b01662409d047c5aa27f4d092df40140497fa,0xf888480140517fa,0x2160172200184460144297f9,0x5320050ceca0144317f9,0x18ca003e14200a02c069f39,0x1b01016065029db7,1530031938999,0x37403090602d0295f8,0xc6b0017812041604517f8,0xc6b001a1a041604597f8,0x68e4130b002c0b1df8,0x630800a660d30b002c0c9fb8,0xc63001ff16a1600597f9,0x31b4006c12042282c97f8,0xc6d001a1a0422c2c97f8,0x11024130160582c9df8,0x63780024120160642c9fb8,0x18ca003e7836802c2c97f9],
[0x3c06061400a038451bf8,0x21200a038459bf8,0x39b0980501c02c0b21f8,0x3c420980501c02c0ca3b8,0x3e60a3400a038059bf9,0x194200a02c5119f8,0xfe14200a02c079bf9,0x6c120c9080144417f9,0x1080a040156817f8,0x1b20a1280144497f9,0x5bf001628026320d0400a02c089ff9,0x320c0072214300a02c099fb9,0xf011430b402c0b1de8,0x3204007c042861680597f9,0x3204005c328602c2d97f9,0x314400319e13a0715ce0144517f9,0xc51000c668f8ec80144597f9,0x90b423602c0b1df8,0x90b4016058f81df8,0x34146a0050d602c0b2578,0x11618050160580c2568,0x38f0e18050160580d25e8,0x318a19f441cea600a02c0b1df9,0xc89001be14200a02c0c1f79,0x18a20018c58441e155700a02c0c9fb9,0x190e0009cf1830500a02c0d1ff9,0xc200ac0311e4000e2001073002b00b0660740d8310c62ad7a7a60314ff40140597fa,0x86804710027048f003a80f600a08860144697f9,0x1778015050c308a0144717f9,0x1c02040310497f8,0x17812041604917f8,0x5801805c0ca6a7],
[0x310b00300b9ef8,0x510b00300c9fb8,0x237b801588225081600617f9,0x110b86c5050b0014061ff9,0x6c12042482c97f8,0xc02e0642ca6a7,0x1941201805c2c9ef8,0x510180642c9fb8,0x1c02040310717f8,0x11bfc004b88225080302c97f9,0x1c526110400a0302c9ff9,77124831757802488,0x3f0480280e01805c0caaa7,0xda0900501c0300ba2f8,0x2a0c88180501c0300c2378,0x37e0900501c0300ca3b8,0x5d506d471600a038061bf9,0x8dfa0078c86cb0400a038061ff9,0x5c648300a030079bf9,0x1520392040e0400a040061ff9,0x38c9060144817f9,0x24824183080144897f9,0x319c300a030099fb9,0x1c02040310797f8,4797444918190056,0x664800b0420b4058061fe8,0x5300b150015e03b8a808114cc1680617f9,0x308a630b4014061ff9,0x1c020484c0617f8,0xa1d001e40af0095c0a0114ca0302d97f9,0x501810050180602da768,0xa4418200a0302d9ff9],
[0xcd10005018100502c0300c2768,0x2c8050c800f605780e4a19c6400a058061ff9,0x1540286c007b01d40538f0de19ca0144917f9,0x5500a1b000b700f0418400a060499f68,0x2a8050d800f205d80f960860144997f9,0x5500a1b001e4073014e4c37867280501805c0ca6a8,0x420e100501805c0d26e8,0xaa01436003c80e6029c886216e500a0300b9ef9,688007323512,0x3e1c1818050180600d2768,0xaa01436003681320020b33f8d4400a0300c1f79,0x5500a1b001dc07301410d0a1416e500a0300c9fb9,0x363869b0400a0300d1ff9,0xaa0094050a0075809c0200080019802104a0884606501a69a7e4a4ab6e881c519c5f40140617fa,0x980c200abf0069978,0x980c200abf8069b58,0xc980c200a0344a1b79,0x4980c200a0344a9b79,0x64416c4b1778,0x70184015851778,0xed01d840144b1779,0x5824100501c03409a318,0x2c200a0384d9b78,0x16100501c0340d2358,0x1db06c400a038069b79,0x6c200a034079b79,0x6c300a044069f79,0x52c200a034099f39,0x926168069779,0x33840028f184480342d9779,0x7194300a0342d9f79,0x67c800d200a059851f78],
[0x337c0048c9300a058069f79,0x9260144d1779,0x66e800ce3f0d480144d9779,0x2449300a0340d1f79,0x190801e2003c80090800603076038740f40e27ebc954a01406977a,112692729335,0x7c441868169595f8,316831490479607,0x1a40e8ec040650297f8,79339623415,2415868941815,79473841911,0x1ea1c7064390297f8,4617241007607,0x1cc0e8ec0443d0297f8,0xd00836064410297f8,0x34980176c0011e20318088bfc1209028ff9,0x3cd003a20099c0120e09030ff9,0xd0c580240e09038ff9,4797170912632792,4797187421413336,0x670440a281602c97d9,0xc80610b00400c9fd8,0xb8051008ea1600817d9,1721112055,18229892599,0x6b04a0e960df8,0xb8a11c55040ff9,0x620448248f97f8,0x7a06207031455048ff9,0x6f005c010b00500c9fe8,0x71a80199c0698b15081600a17f9],
[0x695800bc14d061606997f8,0xc150008440430536a1600b17f9,0x1c12041606b17f8,0xb802041606c97f8,0x2581c10b005c0c9fe8,0x16e50014503e42c34146c1600b97f9,81100258455656440,0x8291812061607197f8,0x11014041607217f8,0xd600c5400fd60033008d83160c3c0718451752042863084f61600c97f9,0xbe00c5400ef01e82c080098290420440740f2224884e82818909e42c0ffa,0x44030386250b00148f9ff9,0x88743382660b00140b9ff9,0x194806140b0014911ff9,0x2e1683382650b00140c9ff9,0x58120b00164f1bf8,0x58120b00164f9df8,0x58120b0016501ef8,0x3f82c1c5150b0014871ff9,0x7c330386240b0014879ff9,0x194806140b0014881ff9,0x1280d0e4e2837084cc1600297fa,81100287574317048,79339787255,2415869105655,35069630199,0x1d1a07068288717f8,0xa0448288797f8,0x488c048288817f8,0x118ba00286004ec0c0e0d050ff9,0x6cd800c300a8309058ff9,0x561ce0150309060ff9],
[1930125450199,0x1a28201c0642c9fd8,0x641c580c6a0382c97d9,0xab01c10280642c9fe8,0x1c6e00118401209c1d06480502c97f9,0x1ada003614d061646997f8,0x305c0020900482783680582c97f9,0x3a0c41646b17f8,0x2cc041646c97f8,0x901c102e0642c9fe8,0x5b9c004fc0141f61a0c66e05c2c97f9,0x1c3a0c41647117f8,0x6c12041647197f8,0x11014041647217f8,0x188801bd400ee03b018b831a0c640685870a8bf08430bf40642c97f9,0xe0618d5068ff9,0x620448388f97f8,0x2702906207038255070ff9,0xb8736061647417d8,0x30c0620846a0682c97d9,0x188800710090e00110250760340d815019016070f244252b3e089be42c8ffa,0x1c38a460400a1648f9ff9,0xc230100501c0642ca3d8,0xc230100501c43c2ca3d8,0xfc50d038400a0382c9bd9,0x714541c400a05c2c9ff9,0x3804182a026400a0642c9ff9,0x1c023818460300a43c2c9ff9,0xf12816400a0682c9fd9,0x2e0020041bfe2868084cc0142c97fa,0x1d06200a0644e1bf8,0x64e002283001984c6a0144e13f9],
[0x8c200a038531bd8,0x361494500a038079bd9,0xa500b818c8180501c0400ca3d8,0x5180660a3400a038081bd9,0x10324180501c06009a358,0x110648300a038621bd8,0x2f81d43206142500a038099bd9,0x3a071c300a038699bf8,0xa2c079b400a0380b1bf9,0x3a170200a0386c9bf8,0xf40660e100501c05c0ca3e8,0x8e4070828c93700a0380b9bf9,0x2c200a0386f9b78,0x9404980501c0600d2348,0x5a00473011b500a0380c1b79,0x1c08450400a038719bf8,0x1a190200a038721bf8,0x1f8050880007003a032202078010410cdc33616297a00a0380c9bf9,0x460648300a038761bd8,0x6d019a81605a9600a0380d1bd9,0x3f00a26004ff000b818808c0320441040e2596d96d008b12f20140713fa,0x194200a038099fd9,0x8e01b81c38208184c0145017f9,0x160b0e180501c0500ca3e8,0x2c6430000a018858919600a0380a1bf9,0xe0861400a0386b1bf8,0x3e840052064342418400a0380b9ff9,0x6e0886200a038711bf8,0x11840442d013a1c3500a0380c9ff9,0x380716145063700a0380d1fd9,0x1a31d80021680cc07163e090a4bb8084466e0140717fa,0x3416300a0585119f8],
[0x1b20170100a2880c9bf8,0x991801fd40021016a03984c6a0145113f9,0x48528400a28c079af9,0x8c200a290531af8,0xfc494400a290079af9,0x1c088c200a298079bf9,0x1e1c6732400a058079bf9,0xc8420a6a6500a05c079bf9,0x5401049400a060079b79,0x189e0002c02dc03c189050a6400a064079bf9,0x158400ef01404002a06e01f00c80f05100e162bfb40b254e0140793fa,0x2201c482928a0145216f9,0xc741a852802c1c0823060145317f9,0x192036163d85cc4e0140797fa,0xf1a64a0145717f9,0x195003bc018a42e0400a0400b9ff9,0x2f8050c8000d01f600c80e81c2b0b02828600a0400c9ff9,0x3bc038c828c400a0400d1fd9,0x2980327001308004234001a006403201201901707cc2208c6c0140817fa,0x78c4015ba97f8,0x1b06200a068589fd8,0xcc012e003b804043c2a0145897f9,0x12e0052c51880145917f9,0x8700283446080145a17f9,0x1422300a044099fd9,0x6b076c1680897f9,0x3840c26c0442d97f9,0x528004e0920d028500a050089ff9,0x15ec00099003c3c39d0400a058089ff9,0xe80a04015c297f8,0x570329426e0145a97f9,0x1500a04015c497f8],
[0xc506c4826e0145b17f9,0x482414a20050220600d2748,0x5f073b600a0440c1f79,0x14306190400a0440c9ff9,0x58cb81c519500a0440d1fd9,0x144018a801c6033000700284d803f07e0c81c270320540680dc07f497f048308b12f60140897fa,0xec0670026860145f97f9,0x8052c51880146017f9,0x5480d852860146097f9,0x705861680997f9,0x1e8328604c2d97f9,0xe2d0002809cb030500a058099ff9,0x7360a1200503004c0d2748,0x1102382c300a060099f79,0xc904015e016f8,0x6104990a0146197f9,0xa601426003e8091002a07960860146217f9,0x64c220c71500a04c0d1fd9,0xa600c4400e06007d0220d03c14808981160ae0781c1a3e977838c859af60140997fa,0xc30002032bd0793f7,4616033375735,0x18a0068452c50797d7,0x18a0068452c90797e7,0x5e801f681c6484750797f8,0xb037f90795f7,0xc40e120884790797f8,0x192006204447d0797f8,0x33180057c0026c0060aa01820172838255078ff9,0x3f1801d3007020a968ff8,0xf0c00f0803ad00d1820d080ff9,0x1580411881690817f9,0xc1000f300f850a970ff8],
[0x2e16a80461a0891088ff9,0x9261690897f9,0x2902c603a024d090ff9,90365843146252264,0x6b80843b01281682d97e9,0x72a800a4120b41480b1fe8,0x39540024330b42280b1fe8,0xaee002a900360d901c42ec1680b17e9,0x4f0060a0074801a07fe0063401501a03a06c0283e1f400814156b4b048cc5e02d0ffa,0xd2c014266401c2e0686480150817f9,0xcca03280189260150897f9,0x8210230b4016579bf8,0x420220b4016581df8,0x8210230b4016589fd8,0x4210230b4016591fe8,0x1f2120d83250b40148e9ff9,0x24520e8a60b40148f1ff9,0x682220b40148f9ff9,0xba00180d300cb3e62ec1680297fa,80480932855,55054327,4616033506807,35674167255,35674200039,0x3eb80c6884c8e97f8,0x3a0b0484c8f17f8,0x6204484c8f97f8,0xc62480038807c80f2831455098ff9,0x356000a8020a978ff8,0x2b3e007bc03281820d0a0ff9,0x58102e8502d9ef8,0xcb8005828c61690a17f8],
[0x3625a8a8502d97f9,99924050701717496,0x5308d804c308910a8ff9,0x63268542d97f9,0x14a02b0088144d0b0ff9,0x192c00448006063260502d97e9,0x60a001dc03fd0012a000606e0a40d81b03e00409402e0042a04382cbe30211d82d8ffa,0xa080503016c8fa768,0x24122200a16c8f9ff9,0x140100a05d0a1ef8,0x1a1001f05300a8500c1f78,0x55b00140360098c780b6ca0150a17f9,0x329e8018e32860150a97f9,0x4c02810ec0c300a0602d9f69,0x1dc03701f08d01a1a1b8b01446c0142d97fa,0x143c00ff4012a8010a00881d0630c400a0500b1fe9,0xa060027806a8012c300a0500c1f69,0xad0099500002026805e00b0520ea01e0ae500a0500c9fe9,0xa700d1fc000a053fb0011a00f4014082050bc0160940870360507051d20bab520140a17fa,0x33b0250cb000823060146697f9,0xd300f9e0c6a0140a97fa,99398481485567992,0x4700020b0446e9897f8,0x684446c4517f8,0x2ca0050f14846e9917f8,0xa860010a000d8022403cc56063ae46c0b17f9,0xb0b04148f817f8,0x6844228f817f8,0xcc8048280a0487c29917f8,0x7d90014f8011e01e580c561b9b0058f817f9,0x671000c640cb140560140b1ff9,0x78c4015fc97f8],
[0x2f40395400599844a0146817f9,0xec3000640100a148359f78,0x1d86003f04898050a40580c2768,0xe470010819cfe1f0515600a1480b1ff9,94804565840271352,0x29a007461c0a844e0146897f9,0x76380054170200a1ac451f78,0x16040053e004e8033a22b700a1ac0b1f79,0x1d8e00038198051140580c2768,0xe410011808e169058f600a2280b1ff9,0x608800c601601408e01785415ce0146997f9,0x1d8e00387051400a2b80b1ff9,0x7d032010a64a0146a17f9,0x2bc8003f401640960320228051911b500a0580c1f69,0xc17000b3001868c400a0580d1fe9,0x69005404902000f03fd00081f400040fc150486602c1c5c1f00c058050740468f190440a095925fc60ecbf40140b17fa,0x44824130d462e60140b9ff9,0x1f900440f0f86300a05cfb9ff9,0x2f5000f640078c40160897f8,0x15e011d40016001d0008f006f03ec01609406602e80c2dcc0146b17f9,0x1c1e0b091500a1480b9ff9,0x2de000c0b06588c0146b97f9,0x3c060a060160f97f8,0x2a80501800de03c800601600c0b602a465c0b500146c97f9,0x5c1e0b091500a2d40b9ff9,0x3b804824183080146d17f9,0x2a802b980024401bc07d01f80b006061009816e500a05c0c9fe9,0x1c2c003580220659500a05c0d1fe9,0x55005c0a3c00e5002c031fc801c7f400a80301c01c07500cf41ce8782878b023c6502b5f30f0083295f60140b97fa,0x11600d6012046480146e9779,0x3b6c002406040161c1778,0x193e002b80ca0270f86c80146f9779],
[0x17800901481c6900606221b600a0600d1f69,0xb200b8400ef004c001e0012200ac022905c16022103209c0f0b60542a0e0081b60105c8d92f00140c177a,0xa9009af001b400813012401608409e01615ca0147117f9,0x38805807034805e1102dce0147197f9,0x164015b40012600da038801a01601c0d201615ca0147217f9,0x36804824183080147317f9,0x2c801e051e0029100009000b03470d06e0d170740a0701854061a0881808243c1c58e1c2405013008f1c1908715f60140c97fa,6335661249271800,0x2f0120630138141844a0147417f9,0x1b100370030d1880147497f9,0xea0006400c284480147517f9,0x24120a060163617f8,0xb2014020035808d00ec1e408c0e0f0ecc0147617f9,0xb200b6c0040804a700358050785e0641381e110a40430f0dc186b14709d816182352c06021592f60140d17fa,0xb20058148801b9401701bb00154001900010245868285a80a0c2852305704e0781a071f030f0512330e161a0a120208ae1618ce69bd8028ffb,0xea00cc19e600061a08910b8ff9,0x194201c02c2e19f8,0x2c64007e044602c2e15f9,0x1b807fc01506003c644ca1700617f9,0x78b8301c0582e19f8,0x370201c1700c9bf8,0x1900077000dcc680382e13f9,0xa2b001202048600c97f8,0x2874000a0448608797f8,0x1cd80046c272c006882a0d0c0ff9,0x8812048640897f8,0x361202c170089df8,0x2e0058800faa003485844a1700897f9,0x29003cc007830004e442881700997f9,0x30543094cd0c97f8,0x3051cc94d10c97f8,0x2a7000880c9e0009d29a0c48ba50c8ff9],
[0xac0420a40582e1df8,0x39a86415c0582e1df8,0x4df00110b8302c1700d1de8,0x25f800e538868484d500582e15f9,0xfe03b900131c00643644cc1700b97f9,0x4a01d680090a00178f808eca1700c97f9,0x4e01df8009120009464c6c1700d17f9,0x4e01df800d814280060c005db713d509d82e0ffa,0xc200d83e180028298d0d0ff9,0x6c5000180cc60302e96f9,0x28127800a833860382e93f9,0x5d70019061060402e97f9,0x38a01a34d800d0f0d0d8ff9,0x2c3b6008ea001409c80582e97f9,513447863,0x4a0a286129a8fb8,0xe1003e0a720045052910e0ff9,0x46f002cc605c2e96f9,0x1a1f7006a010804d9801fdb41143b9c2e8ffa,0xc5805294c80240317fa,0xfc0110f86c802c2f97b9,0x23200582214201c02c031bf9,433969631224,0x2b601906806062240317f9,0x2ddc005f40040428602c3097f9,0xbb5000eb004382bf1c11d4e02c0317fa,0x8a807c318301c030031bf9,0x2d44005e01018018561f78,0x7920e1104020030031ff9,0x4dc00c63060303097f9,0x30640022c01a1182c45242dce0300317fa,0x4c1c328c109c2f0ffa],
[0x812002305c32060d0e8ff9,0x1ec80130f02829910f0ff9,36579972983,36647081847,3442354822967,0x3984417c561778,0x108178c82b82f97f8,0xc54030c60411097f8,0x61020069111fc7,0x1954030c60411117f8,0xa610200642f9fb8,0x63010202017c0d1fd8,0x479c00d7982020114e0402f97f9,0x3316001ac00283c30880442f97f9,0x3880192090f8ff9,94583921840121,0x88020417c6a17f8,0x70120202c17c0d1fe8,0xa6005198f86c80582f97f9,0xba0090cd2995108ff9,0x480606c60691117e8,0x51f8a52995110ff9,0x48e2dca0642f97b9,0x8360417c7497f8,0x2780194da63a1cac17c0d17f9,0x7f800d81df00984871b8faaa4819a529c2f8ffa,0x60800f05294c817c0317fa,0xe032018562357,0x164063401c018561b58,0x5b8100e0200640323d8,0xcc0364063401c040031bd9,0x3300648201c04c031bd9],
[0x97006c064c2401c058031bf9,0x16807c318301c05c031bf9,0x68f80087004c061439e36501c064031bf9,0x4201e128301c068031bd9,0x6918008300b070c241f8898ec0380313fa,0x1ea03b071444cc03c0313fa,0x2b5c005e0102e018561f78,3442623258471,0x58350418c561778,0xa830009e121281032018561f78,0xa5f000a1e0a168c68018561779,0x1701020064309fd8,0xe900a2088480403097d9,0x1526002c1e0d0929b8ff8,0x58803c13145894e2b80317f9,0x8640030c521106502005c031ff9,0xc61020064319fe8,0x143b20006011f010794e0403197f9,0x1d5200230638484c428230e65020064031ff9,0x5a80440181785ca7020068031fd9,0x293800a02d0013401c0601028484ab8e0d0bcf00400317fa,8514899573020664,0x82007f80de0a5e080185917f9,0x29980046a006102c044319fe8,0xa66000bb8017607a010228402c044031ff9,0x7b8022063062d40317f9,0xf301b0f03062d80317f9,0x28f800500d4004100e404423c3214ca0443197f9,0xf101083183022068031fd9,0x51f000a0258005a0060181302fbc2c611a6f40440317fa,19076450717433,0x6102c3860d120ff9],
[0x3d8385b12a0300ffa,0x6284604c3097d9,0x18e600206004628480583097f9,0x3f400c630605c3097f9,0x32040006c015813098785ca0643097f9,0x11500621091128ff9,0x625060683097d9,0xc810001d00484860c3a090fe2223dc308ffa,0x6010828c9080186017f9,0x1b1e0005404a0180a0e4810f0b4e04c0317fa,9746351467042808,0x7bf800a4120a4058319fe8,0x753800aa07f0f8318450a4058031ff9,0xa317129c0ff8,0x20e002880d41644cc0186897f9,0x6030c62b90c97f8,0x3c124320580d1fe8,0xe90018c033f166f86ce8640b17f9,0x3e24000a05315c058319fe8,0x752800ba06fc39705515c058031ff9,0x3c0c30929c8ff8,0x1240e81a0f8b130483500317f9,0x29680010600508048708e824dd500583197e9,0x1c76002903e0fc1c9194c2602c068031fe9,0x521000c222004202282c1a342850a164bf4ef00580317fa,0xf407c318302e068031fe9,0x28f800a1290011048c20d0a1434248242dcc05c0317fa,0x21a02c3860d130ff9,0x130ca52998310ffa,0x3ce400360282dca0643197e9,0x2948000fe006f0060383a0a140c2994395b9c318ffa,0x730800f83a0d202050982d242dce0640317fa],
[0xe80f09403098480187497f9,0xbe02206863060187517f9,0x736800984a070e194c62305ccc083145f20680317fa,0x4ca0020ca0016400d5000ea009838d19a8547c18dc5e125d6516dbe8030ffb,0xb08868e504a01c061ff9,0x16110082404a01c8f9ff9,0xb08868e504a01c0b9ff9,0x5844061404a01c911ff9,0xb08868e504a01c0c9ff9,0x4c1204b278039bf8,0x4c1204a01e4f9df8,0x4c1204a01e501ef8,0x3c42951504a01c871ff9,0x16110082404a01c879ff9,0x5844061404a01c881ff9,0x531001e4ea34739cc0940397fa,0x50a1a0a11138ef9,9226045304868793,0xb09060d140ff9,9228227148287961,9226045304934377,0x549001f083046dbe8320ffa,286148414740472,0x22050200e031159ef8,524851127,0x3d80a0401e9d97f8,0x22050200e05d159ef8,0x26f8001830015912c18801d1597f9,286148414806008,0xc2401e9e97f8,0xc2401e9f17f8,0x50100e064aa1fb8],
[0x50100e550879fb8,0xc9c0029ff05818601caa17f9,0x5fe00171b468e500e030179ff9,4535999240184,0x310082300e47c179ff9,0x50100e065161fe8,0xb14000823c98318801d1617f9,0x1538006c4c3468e500e05c179ff9,0x2a700054da1468e500e064179ff9,4535999272952,0x6310082300e43c179ff9,0x14280048a52d5468e69f201c1797fa,0xfc0aa08fd8,0x153e000b402c30038870d168ff9,0x357000b09170ff9,0x37a00aaa00620441dc3297f8,81100260800370680,0xa0441f03297f8,0x30080902806432a3a7,0x10412012050329bf8,0x10601012064329fb8,0x805d0012eb001af60236a0243297f9,0x1c02041944697f8,0xc74001c02040311817f8,35328613815287,0x18e800980c042483297f8,0x18f800003024c329f67,0x63a0031c0424c3297f8,0xc02e06432a6a7,0x3101805c329ef8,0x31b0004f12018060329f78,0x18e800d1018064329fb8],
[0x62001422f7001497c10a084a0303297f9,37521265655,0xd600c040651797f8,79340999671,79408109047,79475218167,0x1f212068bc8717f8,0xa0448bc8797f8,0xa01c268bc8817f8,0xd1c0009e0809178ff9,0x620448c08f97f8,0x7f7000c2c001c3700838255180ff9,0xa80601028064329fe8,0xe3fb8012e5001a61d86664a0503297f9,0xf014041946b17f8,0x339000b802043643297f8,0x188800482102e064329fe8,0xfbe000845ea000830f63e86c05c3297f9,0x7df000c440024360236a060329779,73420411895,0xa1d1202061947113f8,81100259328071672,0x88532063903297f8,0x1f6c0066c0156400232994109e46da24114720643297f9,0x3eb800218b00551003c70612259914e828d8328ffa,0x22050200e064e11fd8,0x93c01ce11bd7,0x6100f27ce11dd7,0xf280e11ed7,0x708020200e438e11fd8,0x706050300e43ce11fd8,0x22050200e708881fd8],
[0x60e0013dc18401ce117d9,0x706e409801c721ef8,0x45e0a3438c4609801c0c9ff9,0xc141e1393c130039bf8,0xc141e1309801e4f9df8,0xc141e1309801e501ef8,0x29cc551e1609801c871ff9,0xc28114082509801c879ff9,0xc28d0e29509801c881ff9,0x44ea260bcc1300397fa,19851517169656,81243364142094200,0x4e4007a2001dc120e0d188ff9,0x1a080130f0c7080243317f9,0x19f801501020d190ff9,0xcc40088082020048331d58,0x32f003707040403315f9,0xd0400c209198ff9,0xcac00d70704048331779,0x506c055080a17f8,0x5e01040511a17e8,0x2c18c3028060331f68,0xc740031d215060503317f9,0x18c800a3020420d1a0ff9,0x18b800a31898728060331779,0xc5c00d64f6020aa89c330ffa,0x554c004b03206091a8ff9,0xdd4003e0519c25074024039ff9,0x5012041a43b97f8,0x6c12041a83b97f8,0x70200483ba557,0x3c100e0403b9df8],
[0x5c100e0483b9f78,2755963624423,5630463221408615,5630463288517543,0xf102801c3b9bf8,963485867000,0x19880a041ac3b97f8,0x11014041b03b97f8,0x440a0401d4617f8,0x440a0401d4697f8,0x85c04200e0603b9f78,0x8000e0643b9fb8,0xbd804ff001615e4002335003ea00360549fe4a519c5f401c3b97f9,0x1a053401804004b81c2401201c3b9ff9,0xf605840243397b9,0x20580c240f2024039ff9,0x40b038301201c3d1ff9,0x5012041ec3497f8,0x5012041a43e17f8,0x90281a40ca3a7,0x31012050349bf8,0x510121a40c9fb8,0x680ca4002c2b3160c6a0243497f9,0x1c54041ec3517f8,0x12010341f0351fc7,0x3c54041f03517f8,0x23008090280643523a7,0x17c12012050351bf8,0x14201012064351fb8,0xc1c12012068351fd8,0x1a032900130a5f60236a0243517f9,0x7b00e040092557],
[0x70200483e2557,0x240a0070200480cb106,0xc40481400e040092957,0x144048070200480cad17,0x680ca400060acc5831a80900e040092558,0x2910f601c081df8,0x88070200683e25c7,0x53100e0403e1df8,0xe440481400e0400ca9a7,0x14be0900902801c0821f8,0x62880900e0400ca5b8,0x63e0900900e0400d25d8,0xd01948002c14b8e0463501201c081df9,0x248a2a0401201c089ff9,0xf110f601c091f78,0xf1100e0483e1f78,0x3c440481400e0480cab27,0xd1880902801c092378,0x2c2880900e0480ca738,0x1a032900048145690463501201c091f79,0x110140401d4f97f8,4801980069191656,0x17b00a12002604c401ae801f50043029a0c53040450a992b61ec0397f9,0x174282350f6024039ff9,0x440a0401d5297f8,0x1d600050102801c3e1fe8,0x68482a026300e0683e1fe8,0x17d00ab20026200d7400fa801780a39a0452be409a0c49f401c3e17f9,0x61a1180902801c3e23e8,0x1080900e0643e27a8,0x39a42a023501201c3e1ff9,0x1a1111b0120500ca3a7],
[0x17c1a342360240a1bf8,0xd1980902806525a3a7,0x461a34012051259bf8,0x900e0646323a7,0x4502201201c631bf8,0x1a042d00902801c0cab27,0x1b83434185a01205003a378,0x36d0003402c060424012050359be8,0x6da000681e28c6200902801c0c2368,0x4065a00021cd023c2488f062412ac00902801c0ca3a8,0x101968000873408704497bc1e092f9012050039bf9,0x5f402794003ea003300f0a7200902801c0ca7a8,0xbe804f28007d4000e0314261e14e5012050039ff9,0x60101201c659bf8,0x36d0002c0dd41b401201c0a9bf9,0x14065200018023220c236e0243597f9,0x140652000881a5c08c6e0243617f9,0xb870eec00000900e05c0ca7a8,0x245c3864e0009814e0945878601201c0b9ff9,0xa0329001e81c30a022b701201c0c1f79,0x5f4028d8002812b006ba007d400bc051cd021c4854d41831204f901201c0c9fb9,0xd1e2e1491a86501201c0d1ff9,0x117d00a36000a0a520040801ba007d401882c461f411a34d269096bf44830cc23f60240397fa,37990733751,0x178020468d80b97f8,0x930062e000020223910951b0ff9,0x332302801c3e99f8,970468400567,0xa100e1f40b9df8,0x1c40015208c6a01c3e95f9,0x60102801c3f1bf8,0xd3c00440a0401d5597f8]],
[[0x60100e05c3f1ef8,0x217c0313001cb02c36a01c3f17f9,970602618679,0xa100e05c3f9f78,0x2eb00588c6a01c3f9779,0x3a100010272b0332402801c051bf9,0xec067e0009c228100e0286c9fb8,0x23b90004ddbe0c3c042500e05c051ff9,0x1b98004c062506664a01c4197f9,0x1d8800c426acc241446e01c0517fa,0x1af802fe4003c80b091b8ff9,0xf812619c4b15f9,0x26401a7003e80a8198d1c0ff9,0xf85091c8ff9,9149663539957753,0xe84428619c0897f9,0xe868619c0997b9,25310420634616,967729366274041,0x461a11111e0ff9,94595802613946233,0x30c418819c0d17f9,0x18f0050b0006d802a5003903f5f631021ea4338ffa,6872461613048,0x3e812a012601d1c17f9,776530601089016,0x4280218601d1e17f9,0x1a0e30ce01c6c9fb8,0x9604813c650ce01c0b9ff9,0xb04406140ce01c911ff9,0x12d45c3ee19c0397fa,0x24f700065091e8ff9],
[0x318400fc091f0ff9,0x1217030e0d1f8ff9,0x1a19c8832a060341779,0x3090f0d11200ff9,0x9e5001b9800c7fc48486d18340ffa,0x680e19c2507401c061ff9,0x68455180617f8,72340080144293368,72340031906455416,0x230800e23542500e030219ff9,0x440a0401d6f97f8,35361342788599,0x222e041ac4697f8,9816721943074808,0x702e06446a6a7,4504563248176888,0x21e04300e060469f78,0x6000e064469fb8,0x18300a26004d1001f100548055e5053608a01c4697f9,0x51782448437c01c061ff9,0x5012041a44917f8,0x6901805c0ca6a7,0x310d20300b9ef8,0x510d20300c9fb8,0x76042b000b9023242a1a40617f9,0x2428c0691c0617f8,0x6c12042483517f8,0x48080c02e0643526a7,0x1941201805c351ef8,0x14e01018064351fb8,0x81c02060312517f8,0xec08620035c890e042a0303517f9],
[0x7020248092557,0x1c0800c02e0480cb406,0xc40381001805c092c57,0x144038100180480cad17,0x76043f000b118c38a807020030092558,0x19100e040491df8,0x6440381001805c0caca7,0x4da090070200300ba4f8,0x3a18818070200300c2578,0x3688070200300ca5b8,0x7608f60079600aef011921500e040061df9,0x71100e248091f78,0x1c440380c02e0480cae27,0x51880701805c092678,0xc288070180480ca738,0x9e200760443001c5c811921500e030091f79,0x27c801c8114c002810281ac061fe8,0x4f900390229800cc14181400e0300c2768,0x4f9002f03114c00001400e0300ca7a8,0xc5804eb003978191b400f8401e99828402801c061ff9,0x1c02049300617f8,4786050233146872,0x440a0401d7917f8,0x60100e030659ef8,0x396001100e030661f78,0x9ee00720453001fe27828400e0300a9ff9,0x7fe001f02600c040312697f8,0x191009ee007608d60072a00240a35811e0e311f81ac0617f9,0x208868e50d601c061ff9,0x1c02049440617f8,0x27b801d8235801ca801d02e085046c0303617f9,0x1e01882e0401d7a17f8],
[0x31e013840022046b001eb005b80a38a243c6872463172b801c4917f9,0x1080e19c2500e248061ff9,0x5f001c0c1f67,0xc40a04be00397f8,0x18f00ae20012a80008802185204400e060499f68,0x63c02b88011a4007b4000b00d9831cb1ac01c4997f9,0x70180646b26a7,4504562512371448,0x63c027880128242800f6802940728e295054248a2ac00701805c0ca6a8,0xc7804f100250485001ed005280e51c52a1bc1448a2f900e0300b9ef9,0x4100e0306e1f78,0xc7804f1003d045d001fd00528088183852a3289110b900e0300c1f79,0x18f009e2007a08d6003de00a5014a48611a04b8738315800e0300c9fb9,0x31e013c400f41bb800f5002ee00e87422c010c59c70c25152908ba70467111f601c0617fa,0x6101c1a4711bd7,0x68b0201c1a40c9fd8,0x1e402880c680383497d9,0xe00e0407121d7,0x500180158080e00e0400ca5d8,0xa003003c2c063501c01c081dd9,0xe00e048712357,0x503be00158080e00e0480ca758,0x503be0010c063401c01c091f59,0x36cb0c50301c01c711bf8,0x217300a4e5800a7f600d97c7160b0401c01c0c9ff9,0x145cc0293960029fd80365a2c0c4c6e0380397fa,81100291265304568,0xa0449048797f8,0x41a018b80001403a6a11208ff9,0x980170100e2880c9df8,0xbd04b380002200561884a01c5115f9,0x370200e2900c9ef8],
[0x1584c6a01c5216f9,0x3e200170100e2940c9f78,0x138e0017c3e70069884a01c529779,0x1c540401da597f8,0x440a0401da617f8,0x60100e064531fb8,0x3603f36801c5317f9,0x22050200e03c711bf8,0xfd800060100e064541fe8,0x30a013aa0000480192497cd1e328500e064079ff9,0xf6800312664801c5417f9,0xc3804e980000a006491366121c47001c0797fa,316835584087031,0xd600c040652117f8,2415803831287,79408731639,79475840759,0x1f212064392117f8,0xa04443d2117f8,0xac008264412117f8,0x1aa800124009e0809210ff9,0x682000240120e09218ff9,0x121ac0240e09220ff9,0xa0285061a46317f8,0xa0285061a46417f8,0xcd01c10281a40c9fe8,0x1179800d8e0398b0a280503497f9,987115909451769,9295377956278265,0x3605812061a46b17f8,0x2cc041a46c97f8,0x2a81c10d205c0c9fe8],
[0x18fdc0029e073838386a1a40b97f9,0x1d0586e041a47117f8,0x11014041a47217f8,0x7e60004fe06c41d091458c36a421c59781a40c97f9,0x1ee0036f0038b001780b8310120c993521b94382ae8348ffa,0x3208868e50d201c0c9ff9,0x4c1293c1a4039bf8,0x4c120d201e4f9df8,0x4c120d201e501ef8,0x3b40c7e150d201c871ff9,0x6411008240d201c879ff9,0x1904406140d201c881ff9,0x2788524dce1a40397fa,0x2428c0691c8f97f8,39179589591,39179622359,0x3040291ca297d8,39130896343,0x7416090691c0997d8,0x2428c0691c0b97f8,0x2428c0691c9117f8,0x346c120691c0c97f8,2415803995127,39163237879,39163270903,0x1d1a070691c8717f8,0x346c120691c8797f8,0x346c120691c8817f8,39132207063,0x188338691c0d17d8,0x104e5000d2065c9aa340e0d238ff9,0x6d9500220209240ff9],
[0xb280f8509248ff9,0x46010261a8641f97,0x1f8420202804c351fd8,0x2828443103517d8,0x1d064604d2517d8,0x10f38146804c3517d9,0x6c12041a86317f8,0x29c54041a86417f8,0xe804201028064351fe8,0x22f30004bf008809ca0e0412a0503517f9,0x11c54061a86b17f8,0x49802061a86c97f8,0x8c04e0102e064351fe8,0x18fdc0029201c1e1f4341926e05c3517f9,0xe3412061a87117f8,0x78d1cb081a87217f8,0xf0e34186064351fd8,0x33e81a6805038117a38273946720643517f9,0x7828c069288f97f8,0xec04c1a2207038255250ff9,0x220e241a87617d8,0x401e1b844146a0683517d9,0xbf4000180960543610844ab0d86ccdc350ffa,0x7024064552557,0x55e001f43400e048551d58,9008163010715128,0x940c200e068551dd8,0x156800762c0c6a01c5515f9,0x70200645c2557,0x71801f43400e0405c1d58,0x70481007020048632557,0x70481007020048642557],
[0x1f807040a0070200480cad47,0x117b800c3900e62c28a01400e040092558,0x70200486b2557,0x70200486ca557,0x11c07040381002e0480cad47,0x18fdc0024101ce0e0e1a80702005c092558,0xe809300e0405e1d58,0x2b051300e0405e9d58,0x7020048712557,0x500807020048722557,0x13ae002ab0013d818a4030842650248cbc0070200480ca558,0x2c6801b1800e90049200ac00200a403084f64585f800e040091d59,0x343a071c300e040631df8,0x343a071c300e040641df8,0x1b0298a002801c0825d8,0x188078e081400e0400ca5e8,0x45ee0008310071ec829b502801c081df9,0xf1100e0406b1df8,0xf1100e0406c9df8,0xf4078e080702005c0ca5e8,0x345b0039b0023d0123b830a3500e0400b9df9,0x940498070200600d2548,0x7a03c6c4811b600e0400c1d79,0x1bc0f1100e040711df8,0x3c2e0100e040721df8,0x9f10014c8019dc022609e00c184269023322c6fb00e0400c9df9,0x6220c300e040741dd8,0xa8c001f0091e19240a3400e0400d1dd9,0xb2a006b20041c0115803907d0130510020c22ca920a260bf401c0815fa,0x2dd000248a2a0402801c089ff9,0x2a090e64a1ac0897f9,0x320a60c400e0440c1f79],
[0x1c143d0400e0440c9ff9,0x31200986000420e00a8c00140dd01f228a118387001c0897fa,0x1a0000e0645c1f78,0x384002c188b0a2a01c5c1779,0xd01c0e1300e048631f78,0xd01c0e1300e048641f78,0x7f00010801a0e081400e0480ca768,0x57900117e800c21001c1cc5851402801c091f79,0x341100e0486b1f78,0x341100e0486c9f78,0xc401a0e080702e0480ca768,0xaee0063f50008c400e0f21c1c3500e05c091f79,0x340783a801c5e1779,0xb0560a2601c5e9779,0x1a40341100e048711f78,0xd02e0100e048721f78,0x4d8800b14004e6063c1ac0881084c8c3030cb800e0480c9f79,0x57b00351001ce0092c000c0f201e0d6044084f77260bf201c09177a,0x440a0401dd717f8,0x3b0e12801c5f97f9,0x9c0541c200e04c641fb8,0x2590004a06971d0402801c099ff9,0xd8736a1ac0997f9,0x39b071400e060099f79,0x440a04f080397f8,0x195009cd000234005605e14462a01c6217f9,0x32a0139a0031f0066b007405ad29030c67001c0997fa,2355467163575,19004987319,0xd6122646c1f17f8,0x9480020b0446ea397f8,0x684446c3d97f8],
[9887102470985720,0x85007c1a342360500c9fe8,0x2810017f8003d807ca06330612e46c0a17f9,26997004215,0x16c0b0b060f92597f8,81100260816295928,0x45800c28235028065259fe8,0x8b80030100081005c5018aac26320512597f9,0x18c8006810b401cc91f37,0x317000b12307c168039f78,989093437239,0x18d8002810281acc91fa7,0x18d800001400e060c92727,0x17c800718ba8102801cc91fb8,0xc54003443307c050359fe8,0xc54003139a03e02801c0c2768,0x17a8007184e63810e7707c050039ff9,0x440a0401de797f8,0x9f00000e064631fe8,0x5d8016530019c03e0341106c1e43048535001c6317f9,0x321000540420b41ec039f78,0x102000a100a6985a02801c0ca768,0xaf600183800438038dd01332b80b4050039f79,0x321000bc120f6050359fe8,0x321000641987b02801c0c2768,0x30800234029e3661e1c550f6050039ff9,0x171400440a0401deb17f8,0x1728009411f00f80d0443c1a09c0619135001c6417f9,0x5120007402c1314140050039ff9,0xaea000cf80067014c0bd00629a3336c0503597e9,0x57500097c0027029817a00c50999b602801c0c1f69,0x19900556400904f80397003ae00f6029e00f01f01e0785c19232868281089a802801c0c9fe9],
[0xe33200aac801224e8011600838033ae004c0040482981d00780f80f05851a2c30c6d97e45826cbf60500397fa,0x620449308f97f8,0x316062e00172036c04471451260ff9,0x938006e80d08c6a01c6515f9,0x22c0bc4005303b600b02c36a01c6597f9,0x4ce800e8e5401b60188c6a01c661779,0x440a0401df397f8,0x16c80065c2081c203280412801c6697f9,0x2b980060e002b819e017531cb08c6e01c0a97fa,110077842423,0x1c40260e04935b593f8,4615968297975,80549942775,80617052119,80684160999,0x78b01844752697f8,0xb03a512693f7,0x2e4800a600c044792697f8,0x74320447d2697f8,0x968001fd001be038403172838255268ff9,0x69100195007020aa48ff8,0x1998017b00d1820d270ff9,0x4480130241aea517f8,0x8b03681ad2717f9,0x181ac0061a0891278ff9,0xd6e00130241aea597f8,0x3d8041281ad2797f9,0x6201100481c4d280ff9,6922944706844649,0x1b900aee006420042c016c8007013000811c0881e068255c604e447e8358ffa,6872461809656,0x5f403916064601d2717f9],
[6872461842424,0x1b4029ec0218601d2797f9,0x411008240d601c8f9ff9,0x3802d45c3ee1ac0397fa,0x620449448f97f8,0x1827d80003c03700831455288ff9,0xecf00220209290ff9,0x2a90090f0d11298ff9,0x1990088144d2a0ff9,0xaee0042b002d9005d03fc008f282847088e0360ffa,0x780a0200e05cc91fb8,0x5e0b0273607c01c0b9ff9,424777366607864,0xa0100f0400b9df8,0xa0100e05cd91f78,0x621001de08e171600e05c241ff9,0x440a0401e0997f8,0x1700000e0646b1fe8,0x1a700a9a00453001d3007980b40d80f03c2881a81818da35001c6b17f9,0xd0861304848638601c0b9ff9,0x541e0b091500e2480b9ff9,0x63b000082e050780397f8,0x69c02b98010b40074c005e01602c0f40d80f03c2c81663868a535201c6c97f9,0xd380547001a10b40074c000603781781b01e0784f028961491418fb00e05c0c9fe9,0xd380547001a18c801150027a000c0a800c02c16024031781b01e07841009b5f81148595f801c0b97fa,0x3d70007c00410464a01c6e1779,0x1740382418601c701779,0xd00c4c300e0600d1f69,0x34e015cc00c6c007f801e7001a06e0060d04c0170062c383c1b838c245157001c0c177a,0x5091a350f601c0c9ff9,530330550048760,72340104303910392],
[72340077594582904,0x54403e891a3500e064411ff9,0x7c01882e0401e2317f8,0x1a90099b000eb8030c0430010a83604c0f0d2048a046850a09d201c7117f9,0x90102a9c01c0c9bf8,0x9010200e066a19bf8,0xd31970d190647601c0c9ff9,0x5e091a3500e2480c9ff9,0x244814071340397f8,0x6a40266c003b200717e00280d81303c39810872f14dd201c7217f9,0x9010200e065e01ef8,0x7501b399c2600e30c0c9ff9,0xd48056d0008d00746004ec00081f038520743a0740912061504c81107020f8310508b529855d14df801c0c97fa,0x440a0401e2f17f8,0x4e0230e64801c7417f9,0x1d0800440a051ac0397f8,0x1ab0099900024400770120c1084a01c7617f9,0x6ac02664005a2000401a03501a0182103e0705a58182c4f201c0d17fa,0xd580195003a600468011a008d801430051a0d8060107601c2c08a130241426021501a06040c1a010b0a53c1020cec29bdc038ffb,0x356001d0518cca0e00417fa,0x62860d2a8ff9,0x1ad001641467298368ffa,0x38104020cf17d9,0x20c4006ba0a324cc0202097fa,81100292674590712,4574283389474808,0x20500071c00eb6006d82080d2b0ff9,0x431800e0c092b8ff9,0x143080026460243717f9,0x2fa006e500140428602c3717f9,0x21840030e04034371779,0x4308008878512c0ff9],
[0x10b2003c385912c8ff9,0x342a80021260503717f9,0x59c00dda0058b04480583717f9,0x214c00783854188060371779,0x2466048880643717f9,0x1650036d801fff72506d8370ffa,0xec20038104020e117d9,0xba0a324cc1300417fa,0x4418006c0b0d092a78ff8,81100292943026168,0x190b4049688817f8,0x58a002204007b1b0f83112d0ff9,0x1c3c3e061ec3797f8,0x1c3c3e061f03797f8,0x902806437a3a7,0x4a12012050379bf8,0x5f01012064379fb8,0x2ef0077f002b614260243797f9,0x3c38004c024d2d8ff9,0x1e140061c092e0ff9,0x1ddc00f81c1860443796f9,0x777000430e06048379779,0x1c3c3e063203797f8,0x31f01028064379fe8,0x185803b0801b98a0a81280503797f9,0x777003c382512e8ff9,0x7750005054186060379779,73890502391,787540507858680,0x627193c0a04108a0643797f9,0x189803aa8014fdea814010adc378ffa,0x1c900094520031011860203b17f9],
[0x86bc002e0a83092f0ff9,0x1b580393801b82c301202c041fb9,0xd22002c2012020069f39,0x6381060243917f9,0x1cc19860243997f9,0x14c3012020089ef9,0xe3c3012020091f79,0x1702c04908a1ec0417f9,0x5420c048880203e17f9,0x10f810090280580423e8,0x4610090280200c2368,0xd852220090280200ca3a8,0x543d2e5012050041bf9,0x3681c0830120200a9bf9,0x1820a01090705012058041ff9,0x18c8381080243a17f9,0x3cf1a880243a97f9,0xe042a0c30120200c1f79,0xb8713048440120200c9fb9,0x69e0020f806e30005036d800b0d1ff27f10a15033f560240417fa,0x842154003e0702092f8ff9,0x341800714460203f16f9,0x5061083028020051bf9,0xe0a06811881d40517f9,0x605008541880204197f9,0xd5a003f140c582ee0200517fa,0x10bc003705860204297f9,0xa86c602c3897b9,0x3ac801f0223016020069f39,0x863810802c3917f9,0xec22198802c3997f9,0x1a14c4016020089ef9],
[0xe13c4016020091f79,0x33025ca2280417f9,0x1d0a860204597f9,0x7890430160593b1df8,0x30186180b02c0200c2568,0x6228b65016058041df9,0x343c0428802c3a17f9,0x1cc28602c3a97f9,0x25261430160200c1f79,0xf0a808440160200c9fb9,0xb53000460171800281b640024130ffdf3c043126b5602c0417fa,0x1bd004a7000840e0c09300ff9,0x4c80bde006a061c09308ff9,0xe04261c04b96f9,0xf8509310ff9,0x93c30d318ff9,695311182436281,0x50240405aa817f8,0x2f806061880583817f9,0xa8309320ff9,33037042749433,0xa81261c00c1779,0x2b00b8401fe400fafe852424ccaa8380ffa,0x162900854c1c00417fa,0x646c001c198d330ff9,0x202600220209338ff9,80247323365369,0x6030c302c060389f68,0x31cc2860583897f9,0x516c16c8060389779,0x706198d348ff9,0x15dc006b7001705aea1e1a42b09c388ffa],
[0x380c20100344b9e79,0x50a100802203409a618,0xf0e0c3010044069e79,695304207472505,0x1b81c1860204c9779,0x474142010034099f39,0xa4c19402c020069f79,0xa81261d0069779,747943661049721,0xa81260204d1779,0x1e142860204d9779,0x13806c600db200120a81205ffa40c554e02006977a,0x14f80024041060383997d9,0x8808201c0205e9f58,0x3898008c2418208501c020091f59,0x846019c3c0028c2e022410c0380417fa,0xb88550015c070209350ff9,0x460df6001c7860205216f9,0xfc1618a81880205317f9,0x170d811880205417f9,0xa401c4c007c102c1210a0200797fa,0x1e83e080161c083020020091f59,0x1cdc1bdf801dc7c198a0400417fa,0x10c2003881fc0d358ff9,0x3c28012c061c09360ff9,0x91f0fc09368ff9,0x480c04052a897f8,0xf605831880503917f9,0xd41860583917f9,0xa8309370ff9,2181998022649,0x105000681c6400a80c1306bd8b0716133320390ffa],
[0x3a0a324cc1c80417fa,0x32c6003309380ff9,0x1a0b6003309388ff9,0xd20f8509390ff9,0x5c060b03140050399fd8,0x18b60919880503997f9,0x28ac19860583997f9,0xa3309398ff9,688708344453081,0x1c6400a83a0382d7960282a91c398ffa,0x3038483010068589ed8,0x3a88009c1840205896f9,0x1fcc00a1c1860205916f9,0x19069103010044099ed9,0x1893028020089ef9,0xcc09402c020089ef9,0x903898080220600d2648,0x38930100440c1e79,0x144707130100440d1ed9,0x5de00d41c0c001854070260f5b29052cc0200896fa,0x230542840205d9779,0x1893028020091f79,0x189302c020091f79,688707138885497,0xa83101040205e9779,0x5ce00fc1be400185407038e7c3f50a83298c02009177a,0x4704882c4436041080200997fa,0x9d200010c40ad3a17f8,0x1d9c005d018314056050041ff9,0x70400564a0031011860206297f9,0x132600118a6a5cc0a17f9,0x360102805aa91de7],
[0x64b200549800d40e04052a917f8,90388928160962552,0x26f80000b0018a120280593a1fe8,0x6a20018f0000040065d43a0212a0513a17f9,0xf816848f540417f8,0x6030d7025088134c0206417f9,0x140a38a060b05140050041ff9,0x36010295500b1be7,0x579001df4004a120280593b1fe8,0x15e400d9401c6c00e6053e725028058041fe9,0x19fc000080e4940280200c1f69,0x1e880024004024430280200c9fe9,0x386c400990185601b7c000c0d92003c3c3140b01418e7362eea15065ff80500417fa,0x132154002880702093a8ff9,0xeea001c7260206596f9,0x2e3c805008541880206697f9,0x67f001fc0ff07062c36e0200a97fa,0xa2e00010c40ad3b17f8,0x27001740cb14056058041ff9,0xa2a001383ce4c0206817f9,0x5418405a8a17d8,0x620baa70c0b17f9,0xe196801382003c540e055500b17f8,0x3c6b062293b17f8,0x57b002df007cb002580609c990cd0a0593b17f9,0xa0f8108a02c0200c2768,0x5140305044114058041ff9,0x1d40f0a809ca0206997f9,0xe96003c1e8186110c402c0200c1f69,0x1434d0005e016e800281b14006407025850a1a0a0c70e062b2ee819a5df80580417fa,0x859000fa02612513b8ff9,0x3bb8009a03c382513c0ff9],
[0x388a03a0d8d3c8ff9,0x51a8082093d0ff9,0x8409861d00d17e9,0x76016d800381c7400785848340181f101008284cc9683a0ffa,0xa028084ac1d00417fa,0x1f813fa000a8020aaa8ff8,0x14ef800d1820d3d8ff9,0x868800fc093e0ff9,0x3a40e0c093e8ff9,0x4b81e84d3f0ff9,0x6b400e8806c200e3a007020181b81be2150c4e583a8ffa,0x8a02a01040206f9779,0xac04104020701779,0x3b04204c30100600d1f69,0x19805b6000e06c1001e0f0785811211050e050f1d10486512e0200c177a,0xd20241a01071340416f8,0xb06c71380416f8,0xf3c0019c066809c80207216f9,0x1ce8004c1438f0214340280683e1a0ac309d00200c97fa,0x70a18b81c50900c08cca0200d17fa,0x1a90028400cc00550021c00381a7c004b42782c28309111208c4626145250258a684274829bdc040ffb,0x36ac0070a009260249417f9,0xac609c3c17f9,0x2938000a0b86c80249517f9,0x10804328809c3d17f9,0xa8600020c2304e024091ff9,0x3c1b06304e026ab1bf8,0x21b06304e026ab9df8,0x3c1b06304e026ac1ef8,0x81c204e026ac9fe8,0x790e0a836504e0253f9ff9,0x15340016204e024111ff9],
[0x90831826604e025401ff9,0xa6e001ece22b4c09c0497fa,0x4d80018c01ae8001ec000a0610d408ff9,0xf9c00230aad0ff8,0x2ed80100100109801d3006604591410ff9,673356520822777,0x141820280343b1bb8,0x6c426c3b17b8,0x2a78007c22c80343b17b9,0x4a0302005b28004b860383b17f9,0x36b600160609418ff9,0xdc120aad8ff8,0x6c400ba30018a0670d420ff9,0x559000b0c4609d4217f8,0x1c1020a103b1fd8,0xef031118aa103b17f9,0xcc801982d2c00127013cc0443b17f9,5631975116972967,4506349618273272,0x1c12040494297f8,0x1c12040494317f8,0x400240643b1fb8,0x1a065400d41682003f44404184a0483b17f9,0xb18017720008c20280603b1be8,0x14340038a16e50280643b1ba8,0x58c00b93001219adc80503b13f9,0x2c6005db80091840543b13f9,0x4601034089429fc7,0xba0c40894297f8,0x13411030880694297e8,0x6cc40018c101c1186119428ff9,91691881463],
[91758990839,91826099959,55218167,61801983317991,0x3f7058889fd4317f8,0x3a0c4a181117f8,0x198384a194017f8,0xca80174e0014539c1186115430ff9,0xac8002c0b27000300811860603b17f9,0x140c0030c142dca0643b17b9,0x59400020596800b061c13cc0683b17f9,0x72044b400a801013d80079801b900096008700bb5b4d218f840b6983b0ffa,0x905861583b17f9,0x79600220e11860254117f9,0x903810090160483b25b8,0x608090160883b25b8,0x1f89414301202c3b1db9,0x708c30120343b1fb9,0x78260eca1e43b17f9,0x2d02201202d421fb8,0x6201012041421fd8,0x1120f902264a0254217f9,0xb5a0002043820120483b1ff9,0xb5a00021620120883b1ff9,0xd28017560017077bf60adcc0243b17fa,0x206207541c049bf8,0x2062074026841fd8,0x2062074026849fe8,0x3f8241ca65074024bf9ff9,0xa4e09044074024c01ff9,0x426800cc19464074024101ff9,0x3a030519c26074024081ff9],
[0xa4e09044074025439ff9,0x1d018210105074024091ff9,0x742e19465074024111ff9,0x8140048600ff505189c4c0e80497fa,0x1c1204a200917f8,0x3a0c4a201117f8,0x70a0016300173000ff001ac26121115440ff9,0x15a803cd8012e8000f00f8509448ff9,0x1b5800e2e0201c0403b9fd8,0x1b5800e2e0201c0483b9fd8,0x3104003d401a680140f00368785ca0383b97f9,0x460441dc5517f8,0x2f4042b03b97f8,0x12f80130220200483b9fd8,0x89600166003413d400d298037b030e309ce0403b97f9,0x26aa00160609450ff9,0x18e003a300188509458ff9,0xb3006e0c3c00dd800924801842119c1080483b97f9,2762875837415,0x23c0150c0098c013c1420280583b9be8,2756772273127,0x46802a08019940131b0a640280603b9be8,0x39e002670024360ce50280643b9ba8,0x8d005430025f002cc6c19ca0503b93f9,0x8d0054300265004c6c19ca0543b93f9,0x722090d063483b97f8,0x9702302c0603b9fe8,0x89000b025c8012d80298205c80583b97f9,0x4e0c4a301017f8,0x14b500269005204140611460ff9,86390510583,86457620439],
[0xc34254697e7,0x1fc0a03065fd4697f8,0x586c04a34c017f8,0x4e0c4a341017f8,0xbb00543002690013a436060d468ff9,0x186c26041dc6e97f8,0x41800c812a40024ae006388205c80603b97f9,0xe580095c0030486c19ca0643b97b9,0x219800e8230801204c0e1013e400ea80029000340389e9cb8bd8040926a03b8ffa,0x2901fec0024162030121dc101ff9,0x83600110f05840120403b9ff9,0x82e00113211040120483b9ff9,0x482252040120883b9ff9,0x1481fd004b50059a0045a00341e6287809c4c0243b97fa,0xbff0009c5a0926024fc97f9,0x926024fe17f9,0x305861583d17f9,0x3c202800140ff4c1580497fa,150503034872,308139631515128,0x3a8035940005c02b100730230d470ff9,0x610001d00118800d601a6060d478ff9,0xf011430160583c1db8,0xc8308602d4997b8,0x4d80261801aa0a4802c3c17b9,0x1ac01083f900582383080443c17f9,0x3fa80320609480ff9,0x1c40016400b8230d488ff9,0x874055700b17f8,0xd6001a076a00ea5e0c3060583c17f9,0xf8a002309490ff9,0x750003f0019cdc32060d498ff9],
[0x1cc00540ef40061c11880683c17f9,0x4a802c20ec01502a06f004d001a403baf882408a983c0ffa,0x97e001200c011840254717f9,0x708c301202c3c1fb9,0x2c20120343c1f39,0xd861e43c17f9,583154105096185,0x8200e1c01dc0187e413ca0243c17fa,0x3c7c4a0243f97b9,0x1e3284884e0240517ba,0xc282012051631ba7,0x1b142012050439bb8,0x1640e040256317b8,0x302002bb00661506480244397b9,0x786861e40597b9,0x1011430160583d1db8,0x58308602d4e97b8,0x28d800763324a02c3d17b9,0x382c1636501202c3d1fb9,0x14640019281943012038059fb9,0x32a002b07e601202c089fb9,4801980339625399,1520156057015,0x902802c5ca1b7,0x758438401202c5c9db8,0x4cc0420f602c091fb8,0x1020420160483e1fb8,0x90282280923a7,0x48140160580929a7,0x132080902802c0923b8,0xd1012228091fb8,1238163103672],
[0x8903810090160580925b8,0xae40018e002a81ef4e28c401202c091fb9,0x31c7c15cc1ec0597b9,0x2a0ae50160683e1fa8,0x47c7c15cc02c3e17b9,0x5150ae5012050451ba8,0x78188048140d602c0b29a7,0x9004048140162b80b29a7,0x51f3b200902802c0b21a8,0x16100902802c0c23a8,0x5011bae4012050059bb9,0xc9301202c0a9bb9,0xe72a15ca0244517b9,0x58f8ec80244597b9,0x81a0718090d602c0b25b8,0x23b06218090162b80b25b8,0x11618090160580c25a8,0x14e6b30090160580d25a8,0x4c060229fcae501202c0b1db9,0xe6540c201202c0c1fb9,0x68d783e501202c0d1fb9,0x26d801d300738012600740eb80027006f802203851dec553b398dab500240597ba,0x78142012bf4069ab8,0x78142012bfc069ba8,0xc781420120344a1bb9,0x4781420120344a9bb9,0xb1420120504b1bb8,0x502840258517b8,0xbd800c6401aa05480244b17b9,0x786861e40697b9,0x3281840343d17b9,0x5630120343d1fb9],
[0x6c3012044069fb9,0x88090280598523a7,0xd8a100902805806a3a8,0xb1420120504d1ba8,0x48610090280340c2328,0x690023c93012050069bb9,0x1b1420120340a9bb9,0x14d2012059851fb8,0x38cc93012058069fb9,0x52c3260244d17b9,0x1a4068d840244d97b9,0x1c540c20120340c1f39,0x4930120340d1fb9,0x313801d10073801de0075400148023402604e0520ef657c954a0240697ba,0x653800dc120aae8ff8,0x24038e0058280050a02c670d4a0ff9,0x1750017a8008080a5094a8ff9,0x8d803af005680b0508d4b0ff9,90320902616324057,28596071501560,0x9320d4b8ff9,0x2991208914c0ff9,0x130240405aae97f8,0x4729061e40b17f9,0xf010c9081e40c17f9,7004309506824153,0x19c040f001881d100ddc01d823b800f80a1d579010218648a03c8ffa,0x5ff8005191c01a0b86c80254a17f9,0x13a0032ac09260254b17f9,0x4200863a0e1e4049bf8,0x20620f2026af9ef8,0x16008630f2026841fd8],
[0x42008630f2026849fe8,0x1e484163650f2024bf9ff9,0xe0401058a60f2024c01ff9,0x1b81630f2024101ff9,0x207002700d8062cfa2b4c1e40497fa,24215204925432,0xb03040594c95f8,0x454f000b7018a0670d4c8ff9,0x619c001980c6094d0ff9,0x331c00be04a0c8d4d8ff9,0x110140e260383d17d9,0x7874055800b17f8,0x440d16420c3060583d17f9,0xb00811860603d17f9,24215181725689,0x24018189c16060d4e8ff9,0x4bf003a201f8801b68002c05c0f06c0901163afc858c98983d0ffa,0x1b81630121e8101ff9,0x62010120414c9df8,0x130c00147180ebc0454c0254c97f9,0x49f001038021260254d97f9,0x1910071005036038142c2f502dca0243d17fa,0x6c120f6038081fd8,21991310368711,0xe20101c0403e1fd8,0x1281012280081fd8,0x1040480e0280400cab87,0x2e14100901c0500823d8,0x2d022012038571fd8,0x194080901c0400ca798,0x59028d000798005d00abae04635012038081fd9,0x6c120f6038091fd8],
[0x620101c0483e1fd8,0x1840480e0280480cab87,0x54080901c0500923d8,0x94080901c0480ca798,0x2c80efe001b4056904635012038091fd9,0x1c42e800084ff0005018a52432ac1ec0717f9,0xb7e001e1503c2862803e17e8,0x1221ec00563001503c36401c0683e1fc8,0x122164000c2a1800219fc4a05ca0383e17f9,0x68440259c17f8,0x5df0003c1a4240122800b1fe8,0xc21e4004f9000b058d8820822cc0245017f9,0x9b4180901c0500b23e8,0x21c40056700392261e17280901c0500ca3a8,0xa432800ace00714770272ce70120380a1bf9,0x5e50003c1e1180901c0580d27c8,0x1c082b9800160d0b761b3840120380b1ff9,0x3442a800085490028a09490ce50120380c9fb9,0x2d022012038749fd8,0xd10ea0027f800381c08d3808208a660120380d1fd9,0x1740687fa005303516003d400306ba0003009803c05144853b655a08213f20240717fa,0x15cc00914498a0245216f9,0x2a0119080e0025800823060245297f9,0x56f003c84444cc0240797fa,0x3047c0628c6252024081ff9,0xfa00f02a02823012041419ff9,81100260802631672,3581739868103,0x8a0441f05517f8,72340307335388135,0xe844025ab17f8,0x808090280645523a7],
[0x2c8f13012050551bf8,0x148f13012064551fb8,0x1cf12012068551fd8,0x194041b002c80efe0027c024bae0c8c6c0245517f9,0x4c15058c45012140081ff9,0x2a700130f0c7080245597f9,0xe80a041ec5617f8,0xe80a041f05617f8,0x2808090280645623a7,0x10412012050561bf8,0x780c0206025af17f8,0x30601012064561fb8,0x5200c18008b4016a02bd6502f00245617f9,0xf740110f6040091fd8,0xf740110200483e1fd8,0x3dd0044048140200480cab87,0xf6c0188090280400923d8,0x3d900288090200480ca798,0x14815e80170801098030405744635012040091fd9,4801980673171432,0x725800486c6002412394b0862e0bab41ec0817f9,0x174282350f6024081ff9,0xfc110280403e1fe8,2207352364999,0x39cc006c60024190f204e50200683e1fc8,0xe49000b0d8c00481c7194a50dc3df40403e17f9,0x1408090280403e23e8,0x108090200643e27a8,0x7890090200683e27c8,0x73a42a02350120403e1ff9,0x9028066682326,0x3b01012052681b77],
[0xac519370120500ca3a7,0x1b047526e0240a1bf8,0xd19809028065b223a7,0x583a33012051b21bf8,0xa04048a00280400cab87,0x2e1410091400500823d8,0x161e080383049420fac0090280400ca3a8,0x2c3c100714712dd02ffa012050081bf9,0xbae000581306e10090280400ca7a8,0xc2e980022c090450a4261dc5012050081ff9,0x326c1b950120400a9bf9,0x6844025b397f8,0x5e30003e0542a60a56b60245717f9,0x515058c450122b8081ff9,0x125c0b72c0245797f9,0x290080902005c0ca7a8,0x604090180902005c0d27c8,0xd8cce040120400b9ff9,0x3924002c3670012051450e17351220ef90120400c9fb9,0x3211012040741fd8,0x739800d7400981a044869c321b570120400d1fd9,0x3280842002901a1a10075806586003417d00560f190290150a8f94521142af5684809a8bf60240817fa,0x6844025b917f8,0x2d814e800c04005e1509c08a0245897f9,0x1700204025bb17f8,0x30d001a8738e3ce0245917f9,0xbc00180982080245997f9,0x5c04683081ec0897f9,0x2a01010f040220683e1fc8,0x6a8040c2880443e17f9,0x10f8100902805808a3e8,0xd8310090280440c23e8],
[0x17011a0c20090280440ca3a8,0x1c20234184012050089bf9,0x4202341840120440a9bf9,0x2a010f8180902c0440d27c8,0x19b16021f04012058089ff9,0x120d1a880245a97f9,0x88d1a880245b17f9,0x2d09818090220600d27c8,0x11919213040120440c1ff9,0x62e02341840120440c9fb9,0x7098468d440120440d1fd9,0xf201f98016c0a5400c20c0034077c01ed0052e03f02a0b83202f00b44ad7b04830866b560240897fa,81100260803090424,0xa0441f05c17f8,0x808090280645c23a7,0x104120120505c1bf8,0x106010120645c1fb8,0x290645002b381260245c17f9,316841756759543,0x17602d03c041ec5c97f8,0xbd00d03c041f05c97f8,0x90280645ca3a7,0x17a0310120505c9bf8,0x510120645c9fb8,0xb14016e02b614260245c97f9,0x1b40130f0c7080245d17f9,0x838040860494f17f8,4801980807389160,0x4de80076401b0a5c01340741f839cc9cb825df61ec0917f9,0x174282350f6024091ff9,0x1c1204a900917f8,4787824595181544]],
[[0x1d9006c1890007809a03a0fc1ce56490e3df40483e17f9,0x1408090280483e23e8,0x108090240643e27a8,0x29a42a02350120483e1ff9,0x90280669621a6,0x3b010120529619f7,0x2a789a080120500ca3a7,0x3ac14f144100240a1bf8,0x1a11009028065cfa3a7,0x461a34012051cf9bf8,0x332800774000090280580923e8,0x902804871a3a7,0x1f2600360c180054014801a00c16ba05aac0090280480ca3a8,0xf93001b060c002e009c00d01c515470385afa012050091bf9,0xaea005b00106e10090280480ca7a8,0x2ba8016c0b1bc68f0dc4012050091ff9,0x19a1b940120480a9bf9,0x6153c0005c02d501c4832424012058091ff9,0x290080902e0480ca7a8,0x16641e0401205c091ff9,0x9703312c0245e17f9,0x1040218a2a0245e97f9,0x380012048719fb8,0x4dc80076401b061c002602580e83f071c284426838392780120480c9fb9,0x2b6800a406869401e2003e802903b200d8784033380d80207010a8783c11c0741f839dd942d6a283c0830bf40240917fa,91692667895,1196101623,61801849886199,91826886391,91893995495,0x3fc58889fd4f17f8,0x3a0c40894f17f8],
[0x198384a014f17f8,0x88c00b2d000614e004839c11861154f0ff9,86391100407,86458210263,86525319143,0x1fc0a03065fd4f97f8,0x11014046014f97f8,0x1101404a7c1017f8,0x2aa009fe0042600e20c03f814060d4f8ff9,0x1150076e009540320609500ff9,0x542ee0160609508ff9,4801987917914088,4801987917979624,0x77a00220420c9383822a1ec3e17e9,0x2e8081a0023039600f100204004c07a401e3005b804a08c0f80f00602c1cf646d5be83d8ffa,0x2062a0e1ec049bf8,0x20620f6026af9ef8,0x20620f6026841fd8,0x81c20f6026b09fd8,0x2b0620f6026849fe8,0x1f9c1ca640f6024bf9ff9,0x161d090440f6024c01ff9,0x38e858540f6024101ff9,0x81c20f6026b11bf8,0x81c20f6026b19ef8,0x81c20f6026b21f78,0x81c20f6026b29f78,0x8c1c20f6026b31fe8,0x1fbc1c5c40f6025511ff9,0x161d090440f6025439ff9,0x261d031c40f6025519ff9,0x81c20f6026ab1bf8],
[0x81c20f6026ab9df8,0x81c20f6026b39df8,0x81c20f6026ac1ef8,0x8c1c20f6026ac9fe8,0x1fbc1c5c40f60253f9ff9,0x130e858540f6024111ff9,0x261d031c40f6025401ff9,0x77a00220420e74e9e9e6a1ec0497fa,0x501aaca900d1bc6,0x4a035595213f7,0x501aaea900d1dc6,0xf8c555d5215f7,0x5015495600d1ec6,0xf8c4a92ac16f7,0x248a05025480693f9fc7,45410457575,0x12f18246c8a913f97f8,0x1201548068111fc7,0xba0c4a901117f8,45417011175,0xcc3140a08a914017f8,0x58c0313e0886a900d17e8,0x78298800304012809670521115520ff9,86391297015,45474912215,45474944999,0x1f970306a94bf97f8,0xf074086a94c017f8,0x4e0c4a941017f8,0x4824300105801f601c180209528ff9,0xa63800c100f8509530ff9,0x198718088509538ff9],
[0x399c006b6008404c074138042dca0503e17e9,0x283021400683e1fe8,0x2302b80541206061f07417e8,0xec1215c0683e1fe8,0x82931780683e1fe8,0x43c8007bc00c3800340470318090730247f1306b500683e17e9,0x9560072c01e60089801ef0076c02b407e00c0680a81508c048070360a20e765e045be03e0ffa,0xda118090281f01023e8,0x108090321f01027a8,0x1c8348060540121f0101ff9,0x41a118090281f01123e8,0x108090321f01127a8,0xe090090341f01127c8,0x3d0748060540121f0111ff9,0xef4003c09a06213e1509850120503e1be9,0x3bd000f026818849c1ce250120643e1fa9,0x308020301930120683e1fe9,0xefc00340541501404f27c2a1e6e0243e17fa,0x3c0809028064a023a7,0x10412012050a01bf8,0x882b0b40240ca3a7,0x4212056168049bf8,0x9028064a123a7,0x31012050a11bf8,0x130082b0122800ca3a7,0x3e33056024501bf8,0x4345202b0120500c23e8,0x3c300328049610b7282b0120500ca3a8,0x78600650092ff0115570560240a1bf9,0x1d50004d4005c0ce4012064631ba8,0x1d700d7e40026600586819ca0246313f9,0x8080902805907a1e7],
[0x1a0080902806507a3a7,0x1901813012051079bf8,0x88090280650923a7,0x31012051091bf8,0x1905a0122800ca3a7,0x3e330b4024501bf8,0x56018105a0120502da3e8,0x10c81810a05a0120500b23e8,0x2810c00ba048488216ab05a0120500ca3a8,0x40200a043002e81212f3c15560b40240a1bf9,0x808090280599c21e7,0x1a110090280659c23a7,0xc4334240120519c1bf8,0x9090090280659d23a7,0x104120120519d1bf8,0x184b0920091400500b23e8,0x434520091400500c23e8,0x2050328123888216d30091400500ca3a8,0x40a0650247179042da70122800a1bf9,0xcc142012050661be8,0xd08c30120500a9be9,0x5d010090281480b23e8,0x20810090281ac4523a7,0x18fc001c20150d091a8090281ac0b23e8,0x4be001d70063400b06a284012050691be8,0x12008090282285723a7,0x1ace72b0090282280b23a8,0xc7e000e50041c090090282b80b23e8,0xac20068e0062e00714002a00940d503900c83d80228ab0404d5a80120500b1be9,0x96c003b600c98050c2830120506e9be8,0x5630034500315003c5009b01e81481509b803700d0b15878daa80120500c1be9,0x19a00a404416e5012050719ba8],
[0x2ec014182012050729ba8,0x563003b05960062e00714026c07a03e07401c0541905f013831a3a56f80120500c9ba9,0x563003b05960062e00714026c07a04e05c0140541904303427061085b50adf00240a13fa,0x21e40054b0010bc02e0c26ae80120500b1fe9,0xefa0011630120500c1fe9,0x21ec0041200d1401b806805e029216e60120500c9fa9,0x390d2000c41200cfc01b700d03e13098520f1f95aae0240a17fa,0x3d500c220017500186819ca0246593f9,0x2c19420123300a9bf9,0x158c0013c00f70063a006fc026c07a04e05c0240441d00480d0cfc5294ee0240a93fa,0x7e05620380145005820823060246617f9,0x1d5c0028134a528ac0240a97fa,0x78c44ac3597f8,0xbb801a0b1484ac7e97f8,0xb18864ac5717f8,0x12a01683844aeb417f8,0xd1542560580c1fe8,0x14802c6d42560580d1fe8,0xeb90000e803fe7898085ae4ac0b17f9,0x78c41ad4297f8,0x12400228060c8a147e97f8,6254308714780664,0xd15402c061429fe8,0xa729402c069429fe8,0x12ee001fa8e7898319b00594297f9,0x5c2001cd8650440560240b1ff9,0x6844025fe17f8,0xb60105a001cc22ca0246817f9,0x1e0083418440121480b1ff9,0x25c800384436ca0246897f9,0x8813006020121ac451fb8,0xc82000d3005871c6f078f60121ac0b1ff9],
[0x1f8078c003aa00bf80220a5c0236e0246917f9,0x4402401012228571fb8,0x88146a0091140580c27a8,0x5890091140580d27a8,0x241bb395570122280b1fb9,0x32080036400e1c90450d050b60122b80b1ff9,94804566109132792,0x3d405530532ce0246a17f9,0x158400fc1648003bc002d020201491468442a60120580c1fe9,0x3c0302012058741fe8,0x1b801f18001480660314813a0292294834112baa0120580d1fe9,0x5c094018852007e0e4803ec030e60036041600df805080ec0281f051a1e16048390441b00b80e78a56a4aa820ed5f40240b17fa,0x2f008b2400c6400ef4001c075011816e501205c0c9fa9,0xfb01082b6501205c0d1fe9,0x221780471c01f200c632006ec003a01d20120e81cc06a0d02dcc0240b97fa,0x681f840021260246e17f9,0x3f00ec8007b40171009c12046480246e97f9,0x8802040261a17f8,0x40a00ae0c8880246f17f9,0xfe0243312a0247017f9,0x36c04e0e0614c70120600d1fe9,0xaca007e0e5803f400650030181220900137200abc07a088560682b0b0ee032015014241caeb0914ff40240c17fa,0x1aa004c05e0882dca0247197b9,0x2bc02f0283040247297b9,0x1a80862007e0e5803f401090042200de805780f402c0d81100180f0740c4094043c0a3914adf20240c97ba,0x7103651c40122800d1ff9,0x68440262d97f8,0x2f011007c04f0061785242ca0247417f9,0xe601e03162950122b80d1ff9,0x702040262f97f8,0x1a804601a8738e3ce0247497f9,0xc089c060263217f8],
[0x7a80b186120430c0247517f9,0xf606e03162950122f00d1ff9,0x2740242c10e080247597f9,0x6a01f84001d0211002d6005a0520880862c3602330081831502301c3503718a9760c0e0b5f60240d17fa,0xd407f2000dc01f80c6e4013e4006f001d0316008700dd802e8054161c1606102144c82216144867c37a068360684c3e0e230132041b99c69bd8048ffb,1723111287,0x54742a12b48f78,0xbc80240cd60014402291540ff9,5632531580363239,4506356795612152,0x881204aa40897f8,6209630498530759,0x1b102c1f4089df8,0xc1f0102081f45a97f8,0x786c041f45b17f8,0x8880e130fa0440d1fd8,0x32007b0011d4002bf2090184a1f40897f9,0xd8110140a40583ea1e7,0xd8081415c0583ea1e7,0x59011ce00063e8484aa80280583e99e8,0x1540f0900077c0051e82cc54e0503e93f9,0x583858495a95497f8,76931272430360568,0x552003c02f100071bc29a14494a5548ff9,0x38b81230a40583e9df8,0x72604215c0583e9df8,0x2781bb8002e2001e2218c2402c1f40d1de8,0x13c0ddc00171000e33f43cc5500583e95f9,0x110180143041f46c97b8,0xc2e1c30fa05c0d1fe8,0x1dbc0010f1801e3ccc85294e1f40b97f9,0x3436041f47517f8],
[0x4d03c700047c00138ca60a060c6c1f40d17f9,0x4d03c7001f01bc800c7c0021d5000c13132a408918dc3e8ffa,0x4e0d50150a003c61060403f17f9,0x1bc058b4900070670d550ff9,0x13802201496003c61061f80917f9,0x18315c0048881830280583f1be8,0xc18aa0008c20281f80c1be8,0x4048600107801ec19c80503f13f9,0x1f09380492800dc70cc80583f17f9,0x286c004e0c4aac1017f8,0x2bc038a3ec80085400e42860d558ff9,0x7426601c340042e0064294c805c3f16f9,0x3a1390090f0014a241861f80c17f9,0x2413300d2039402cb400d38065b007ab943bdc3f0ffa,14585042871,0x545001780204605d5617f8,0x381001d60105a0022d00390f11095560ff9,0x2850059b8013d80120e09568ff9,0x40268482d43f97f8,0x5846020221fc0d1fd8,0xe0b500c3600730b0a280443f97f9,0xb90110e2e00220308d570ff9,0x7380dda0051a03091578ff9,0x1080a041fc6897f8,0x85b00242fa0154400841506480583f97f9,0x7086400714c41fc6c97b8,0xb1c202e1fc0d1fe8,0x180b800f9007086400dcc8e3464294e05c3f97f9,0x10f00117a400b1b0251580ff9,0x23a016d400c8240e0d588ff9,0x58674029d8009101280603f9779,0x3436041fc7517f8],
[0x786bc0285801e3390a2c3c12c1fc0d17f9,0xba00786bc02301d401c68400d20008803b5ba92011cf29c3f8ffa,0x43300035007888481fc0517fa,0x98460404097d9,0x5d802aa25028040051bf9,0x381800284868280416b60ff8,0x2cc02a385836d302b80517f9,0x2bbc0052010200286c9fb8,0x14670181002e0680527c8,0x6c66302502005c051ff9,0x76801a05544c0404197f9,0x2a4033868143537020068051fd9,0x16380116080012805c03056f181446c0400517fa,0xb34002a400d0487060285917f9,0x340f8081402c0440523e8,0x1100160460234184028044051bf9,0xd82202c044419fe8,0xd03b0f818160220680527c8,0x20a02f6030228402c044051ff9,0x4400b0060d8739c30a2d40517f9,0x22002c0da0e240882d80517f9,0x1f001a033472ca0444197f9,0x2c0090741830f2c285022068051fd9,0xc5d6000160070184c16fe1830412f40440517fa,0x3f028460484097d9,0x5900686a24028048051bf9,0x2b540052010240286c9fb8,0x166e110402e048051ff9,0x8100482d44a0484197f9,0xa0f001b20060382ba241446e0480517fa,2098449682169,0xa1e005306c38e0d598ff9],
[0x7208e16109c400ffa,0x3aa00614680584097f9,0x110630605c4097f9,0x3be00b70d5a0ff9,0x75c0108460684097d9,0x4488008d80640a1a16023f45808a8dc408ffa,0x1581b04b8120140a40580523e8,0x1581a814101415c0580523e8,0x112c002f00a098221f33a7028058051be9,0x28801c0a54028060051be9,0x1658018d801a30066400940386c1c28f1edb4c0500513fa,0x10c05c10c6a0540513fa,0x2c020461495497f8,0x2810d8240a4058419fe8,0x740a7b0085c1250a4058051ff9,5636275159076856,0x90e001a81883239d0c80286897f9,0x52042b95497f8,0x3c125520580d1fe8,0x8da000d40335a1307064eaa40b17f9,0xec1215c058419fe8,0x1d0146f1f0651515c058051ff9,0x3290ce16b70ff8,0x1f8108350ad44c3500517f9,0xb4c00ace00361c23e0e67500584197e9,0x2105e00c1cf1e36a2602c068051fe9,0x2cb001126c00320258086891e394592fd97500580517fa,0x36400048003da006c341c0302dc80286c97b9,0x2106c34520d66402e068051fe9,0x12c700318880063c008412210d0a047261c424485b5005c0517fa,150503657464,0x6404a0180e060286f17f9],
[0x1922001502c60604197e9,0xb79001780209703436848cc54e0600517fa,0x28e8011606c38e0d5a8ff9,0x36194218dc410ffa,0x16680188801a1002b4012600e050d0e39c5808ddb698418ffa,0x780c1851515c068051ff9,0x2200100d0487060287497f9,0xc089c071900517f8,0x7c01024290541858630a0287517f9,0x3600828c11ac5618c5778382a5520680517fa,0x36c01a70051130037401a1004a8068400c201b700d848485438a6633e311596516dbe8050ffb,0x6b180054159400f832602c9417f9,0xb110008832602c9517f9,0x12070204e02c5c9df8,0x1c20c2404e02c091ff9,0x784c304f558059bf8,0x78386304e02eab9df8,0x78386304e02eac1ef8,0xf1c204e02eac9fe8,0x7f43c0436504e02d3f9ff9,0xc16304e02c111ff9,0x23631c504e02d401ff9,0x2f60014cfe2b4c09c0597fa,0x41c66155b0ef9,0x360da86155b8f79,0x2eb801c460d5b8ff9,6786624211652569,7114358200766441,0x326001f2446dbe8420ffa,0x63f8003880063800f832602cae17f9,0xb3b0008832602d5d17f9,0x1582001cdc12b4e02c1897fa],
[0xa790005f005f900061413955d8ff9,0x301000cf00bbc00f85095e0ff9,0x5a38005840344297b9,0xb45000885095e8ff9,0x8b3f00026860384297f9,0x167e00010ac80444297f9,0x1c12040495f17f8,0x70102c048429df8,4787550187331512,0x1662001f42c30870a0484297f9,91693716471,91760825847,91827934967,61801985152999,0x1ff82849fd5f17f8,0x3a0c4af81117f8,0x198384af94017f8,0x58f80008e705211155f0ff9,3063188462071,0x1f14e40d6058429df8,0x2604215c058429df8,0x3c2202c2146e19e7,0x2c2c00222c302c060429de8,0x161a001e0456502c068429de8,0x15d600122b11ceca0584295f9,0xc2400250e042146e13f8,0xb07000d385860604297f9,0x5748001c348eca0644297b9,0x2c14001810ac80684297f9,0x26d4001d50034d007c8238b8e0f1d94428ffa,0x317800f832602ce617f9,0x8832602ce717f9],
[0x904d0309c02c091ff9,0x73c5342509c02c111ff9,0x3fa1e2b4e1380597fa,0x1c1204afc0917f8,0x3a0c4afc1117f8,0x1c2801722001ac261211155f8ff9,0x21d800cd400f8509600ff9,0xc7e001452860384317f9,0x31f80088509608ff9,0x318800a486821080484317f9,0x63d000410404c4317b9,0x340e30d6058431df8,0x637001454302c060431de8,0xc66003a25ca0584315f9,0x64300008110d610ff9,0x317800c10086c80604317f9,0x31a80008042860644317b9,0x5a8005a4007f798e18c4d9c430ffa,0x8832602d1d17f9,0x3e2b4c19c0597fa,0x7e0b0eb80ff8,6236706196001784,0x3a80175e001d60b0d618ff9,87846684338982904,0xbc0331800d1820d620ff9,0x8812040456317f8,0x3550034381280444397f9,0x6ba003a0c8d628ff9,0x6b20012090404c4397b9,0x2598002ce0094162860516317e8,0x2598002a60088d840504397f9,0xd408863644397b8],
[0x1a2c14528a05c4397f9,0x1200c055c16317f8,0x342c15050eb90ff8,0xb121a075cd6317f8,0x6c12055d16317f8,0x3afc003ea0054400c213d61a242d1961630ff9,0xd8c00380c146a0684397f9,0x1344001f5000f7801530025a4cea110a158438ffa,0x99c0058402c4a97b9,0x281420160344b1db9,0xe86862200697b9,0x3281840344497b9,0x193c0032a143016044069fb9,0xe868602c4c17b9,0x1011430160584c9db8,0x710e64802c4c97b9,0x3e0283180b15c05806a5b8,0x7808a180b02c0340c2528,0x808a180b02c0340d25a8,0x5de02364016058069db9,0xf832602c4d17b9,0x310f832802c4d97b9,0x33e1420160340c1f39,0x189064830160340d1fb9,0x56803e3001df007601d50034d000d03e89f31cf4e02c0697ba,0xd68073920014528602c4e97f9,0x1442000e80a042284f17f8,0x1442001a1a0422c4f17f8,0x4436130160584f1df8,0x288c0036120160644f1fb8,0x10b6002fa01c86007f146802c4f17f9,0x2580c9040384417d9],
[0xe0162e4712196,0x800e0160645ca597,0x4e0c201c02c5c9dd8,4786999981054935,0x14560011828201c228091fd8,0x145a00030101c048459fd8,0x681a0980e0160580925d8,0xe000e016048712397,0x5118005270900e0160480ca798,0x5118002d663401c02c091fd9,0xa31000648201c02c099f99,0x10114314002c0b1de8,0x51780058c9062800597f9,0x5178005c328602c5097f9,1967118687191,0x38c40e08880396913f8,0x210400281b5000a1c6a1b0b15ce0384517f9,0x4208005036a001438f8ec80384597f9,0x1b0101605a681d77,0xc8f526e02c0b1df8,0x90b4016059a01df8,0x34146a00e0162b80b25d8,0xca4180e0160580d25c8,0x140da80050c11ef839aa701c02c0b1df9,0x1810e04301c02c711bb8,0x108600140da8007010c43a155701c02c0c9fb9,0x14760004648201c02c0d1fd9,0x4eb0190a0074a013100f814e005163001660030e3000e0940ca8aed1730cff40380597fa,0x14e05878003f03591638ff9,0x4018001f1001a2044802c5115f9,0xf0d8802c5216f9,0x20f40032e0396003c0428602c5297f9],
[0x189032e00d8602c5317b9,0x10a60007ac007e238a9ad002c0797fa,0x2d14003f812242495640ff9,0x18fc0037008209648ff9,0xd74002600c15030d650ff9,28596072255224,616710283825145,7056738933411833,0x3068241882200c17f9,7004310513457113,0x551001f02fc0106801bd800b01c1af5878e50ca4a8440ffa,0x240f832602d6517f9,0x3e2b4c2200597fa,0x3014055d96697f8,0x1360248d9abb8ff8,0x1b0306075dd6697f8,0xa3048d92bc0ff8,0x1b078d8a0516693f8,0x790686b340a93f8,0x13154003f90b09010b19668ff9,0x2e2a0008209670ff9,0x181e004a0c8d678ff9,0x1f011c68a0516817e8,0x199f1aca0504497f9,787684297314296,0x66d81c32880544497f9,0x7c0a8605c4497f9,0x70e82436a0604497f9,0x1f0306075dd6817f8,0x1e27048d92bd0ff8,0xe80a055ed6817f8,0x1fd00020453e80c0498e5d680ff9],
[0x1a700b78018200ae80629003f018d2c95018246a58448ffa,0x18d801bbc00140c5a0802c5897f9,0x33280022c00e10e0602c5997f9,0x9868602c5a17b9,0x6f10014223016044099f99,0x2a1e16ca2280897f9,0x88842880444597f9,0xa0505200b02c0440c25e8,0x1030a180b02c0440d25c8,0x3e8544016058089df9,0x6c040428802c5a97f9,0x1cc28602c5b17f9,0x1810f2d050160440c1ff9,0x33061440160440c9fb9,0xa621430160440d1fd9,0x79808fa005b2002405d8020b00674011ac00e300560282b03fbfc8288866b5602c0897fa,316845246387191,0x340c042285c17f8,90283382992017400,0x1207020160585c1df8,0x1404130160645c1fb8,0x137800f6142602c5c17f9,0x72602c0c9db7,0x67030e06e4c0595f8,0x6808140160645ca5a7,0x290c01680c2428402802c5c9df8,0x2204211402c5c9df8,7941223499896312,0xe4000162e4711db7,0x33200560224896140160645c9db8,0x15600d602b016ab142802c5c95f9,0x31400b09070602c5d17f9],
[0x11d40024b0021028228091fe8,0x333800496003808140160580925e8,0x7880556800286808140160480ca7a8,0x4eb0188da00048e401ced0da2428502802c091ff9,0x1b0120a82e040496917f8,0x7d8082500114400634006c0f04d343320229df82280917f9,0x90f829212511402c091ff9,0x1c1204b580917f8,0x82500114400634006c0382c4361a3cb00484597f9,0x120702016048681df8,0x90b448a02c0b1df8,0x4a124016059d09df8,0x680830c40160585e1de8,0xe9010620022880067801f806c0d023d830114f7a016058091df9,0x2c11020160486c9fb8,0xc8268180b02e0480ca7a8,0xd8212110401605c091ff9,0x1a021d012802dd195f8,0x33b1146c02c5e17f9,0x5518a2a02c5e97f9,0x5604402042016048711fb8,0xf30104e002208006f80208064030cb0cd1830d1d590160480c9fb9,0x3cc0473002d7000e026401138034201906004d802e0f030483206403122a6655f0b7195f602c0917fa,0x2930071c4428802c5f97b9,0xf01143016058611db8,0xb808e0e64802c6117b9,0x38e8106b01605809a5b8,0x7808a180b02c06009a5a8,0x808a180b02c04c0d2588,0x17087344016058099db9,0x30c260c3016060099fb9,0x784428602c6197b9],
[0x5c4428602c6217b9,0x32214201604c0d1f99,0x349000380b900416007f4009c800a030d86a09c089f3818b288e02c0997ba,0x22f80015a008b00382a15ca0504517e9,0x8081401605926a1e7,0x31f8004fa00d850920140d602c0b25e8,0x80814016059b3a1e7,0x18fc0027f005e0918140162b80b25e8,0xa070010e40061c00b40240bcea502802c0b1de9,0x3340708ca00140802c202802c0c1fe9,0x1b60152a00088348ae602802c0c9fa9,0xb0cb00220a40042b000425200740b81900206791ab4e0500597fa,0xf0105878004f80d41251688ff9,0x4f0ad3000e4602c6515f9,0x82700190552003c0428602c6617f9,0x10c275005e092802c6697b9,0x4f1800746b0040428602c6717f9,0xdf0045f00077400940ff82354e02c0a97fa,112162575351,0x9860052c086b480f93f8,61801784480759,91761481207,91828590327,91895699431,0x1ff82849fd6917f8,0x4426040896917f8,61823326426103,0x3202a82e04a016917f8,0xb350007a02b01f032a70521115690ff9,0xc860027c02a0210d698ff9,0x6ce003980b1b02516a0ff9,0xe600902422abe17f8],
[0xfa0b282296a17f9,0xe040016301920abe8ff8,0x261140b1c4d6a8ff9,0x9c6000902422abf17f8,0xfe0ca82296a97f9,0x3400c84001602ec01038033e00970062400d0f8020e84c349510472be8450ffa,0x73014f832602d6a17f9,0x92068832602d6a97f9,0xf1c2aac228059bf8,0xf1c211402eab9df8,0xf1c211402eac1ef8,0xf1c211402eac9fe8,0xf7c1e34411402d3f9ff9,0x3c52c6411402c111ff9,0x11431c411402d401ff9,0x102cfe2b4c2280597fa,0x8c035596b13f7,0x78c4b5aab95f7,0x78c4b5aac16f7,48765900775,0x1f18246c8b593f97f8,0x3a0c4b581117f8,0x982c0a06b594017f8,0x1e19060006c0e705211156b0ff9,0x28130013090b956b8ff9,0x343400f85096c0ff9,0x9380885096c8ff9,0x1b58002ec00694004b8031200ac0283b0143c9e3958458ffa,0xac12016058a01df8,0x2da400030740561ac059df8,0x2a121182b016059f725b8,0xe412016058a11df8],
[0xb69000d833405602c571df8,0x2a121182b01605885a5b8,0x2c19c5282b0160580c25e8,0x9088582202b0160580d25e8,0x38a0014c07fcc3cea705602c0b1df9,0x16d600022c3016060681de8,0xab100072079d4a02c6815f9,0xac12016058f21df8,0x5f0540a41ac059df8,0x7190520520160580c25e8,0x1c4512e60a402c0b1df9,0x3fb800444602c6895f9,0xb02c935b5a1b7,0x953000a500140a468042016059269df8,0x2885186b016059b5a5b8,0x100caf0d602c0b21b7,0xe8086b01605a58a597,0x10086b01605a5925a7,0x74834010186b0160588ea5b8,0xa8010106b0160588f25b8,0xe412016059281df8,0x4530d602c571df8,0x320e8106b01605885a5b8,0x329b0a06b0160580d25e8,0xa0a0010300286e0019600881f800838c40e1927e08120228b670d602c0b1df9,0xaf50000201c008042016059b39df8,0xac12016059b49df8,0x4831180b15c059b5a5b8,0x7c0b0100b15c059f725b8,0x2183a80b15c0580c25e8,0x32080019600e403812b0361981604fd0a0d0114f690162b80b1df9,0x226000aa0022c30160586e1de8],
[0x3480b8c3016058701de8,0xc100686000f700083420026400cd00340b02d00b0781e06224178469aa90160580c1de9,0xaf0044303016058741de8,0x1bc08830c4016058759de8,0x282400439000cd006e09838940480203c04838d99124a80160580d1de9,0xbf00686003a066800cf8009b0033400b0340482501200838e4089b14da234ef002c0b15fa,0x3e03881c7c15cc02c6c97b9,0x181cdc007102c160ae601605c0c9fa9,0x88294301605c0d1fe9,0x1cc83331801da801a8010341b40e380c52b5002c0b97fa,0x8c8002680383858602c6e17f9,0x1cb003a0105ca02c6f17f9,0x174090704864802c7017f9,0x18b240160600d1fe9,0x1b200cb4000602bc00a1f7002d28024b8019e00581605280e03034121c3100c7e314ff402c0c17fa,0x35a007207701615ca02c7117b9,0x7c800867848a02c7297b9,0x5830871540597b8,0x55f8006503f0208802c7317b9,0xdb006560003018600346001cc00f3002c090160a4088143876008ad0c52ab002c0c97ba,0x15a00a1087cc02c7417f9,0x2b8068528602c7517f9,0x6300e1c2142802c7597f9,0x1ba020b4003f2008fc0068801500c161a2460c042416147008ce7e284b5f602c0d17fa,0x37406aa0039c01a900a280060314013f005d806a4012e00418029ba0cf0920301c1430921e0f048314482890a808c612629bdc058ffb,0x340709044074030c01ff9,0x32d8015a400b0d0341944c0e80617fa,0x4d80061c096d0ff9,0x5e3800934509109c460ffa,0x138801b560035b40021120628ab6c0617f9,0x6844032bf97f8,0x59d0005600d980156d002380503088030d317f9],
[0x26306030d397d9,0x2c500158c00cb61a0482672520302197fa,0x1df000be4008bd00045211156e0ff9,0x1b9800644007c400f85096e8ff9,0x1260011064d6f0ff9,0x170101c040469fd8,0x5908004046800750c08a0384697f9,0x1c02042a84697f8,0x33300010a000a68398e08c0404697f9,0x3103c086b7cc017f8,0x2ff0015fc00ce023c0d6f8ff9,9816728788178936,0xa030202c060469fe8,0x16b800afe006305c80584697f9,0xb6400581000870e402e064469ea8,0xb640057f0034b1c805c4696f9,0x6c26043744697f8,0x2cf0004af20013782960880604697f9,0x16b800af600109a19ca0644697b9,0xddc009520045e00ac200692c974669639c468ffa,0x8db0001074070108030e617f9,0x44686134e1380617fa,0x27e80005f80011186115700ff9,0x3fd80085c00260309708ff9,0xb34011c2000c63060384717f9,0x470800e3c09710ff9,0x169802374003890404c4717b9,0x23740030c3395718ff9,0x8d3001a184302e064471ea8,0x23440074308605c4716f9,0x8d300158130c308c0604717f9,0x8cd001b430860644717b9],
[0x2e700216003b5001f5e8cd8b3a0470ffa,0x2e011a1944c1c00617fa,0xc2000d10002309720ff9,63784739672056,0x1d01840597295f8,0x5e023ec007d024d728ff9,0x8c400e3c09730ff9,0x45e001418404c4797b9,0x1b0b4056000b17f8,0x11180125e0c3060584797f9,0x88400e5c32060d738ff9,0x5a300086400daee122c48960478ffa,0x8816042484e17f8,4996465584642040,0xc02e0644e26a7,0x15c1201805c4e1ef8,0x510180644e1fb8,0x36100223f80056614680304e17f9,0xb816042484f17f8,0xc02e0644f26a7,0x3101805c4f1ef8,0x911020180604f1f78,0xd10180644f1fb8,0x26e010a9000be30e280304f17f9,0x1a01020030509fd8,0x30e0201c030579fd8,0x241a1301c040491fd8,0x30e0201c040499fd8,0x440701001805c0cae87,0x1880e0200300ba6d8,0x1160900e0200300ca798,0x13004f77001383ade0842401c040061fd9],
[0x314c0063040384897d9,0x241a1301c248091fd8,0x440700c02e0480cae87,0x1880e01805c0926d8,0x1160900e0180480ca798,0x13004fed000bf12128401c030091fd9,0x3ff400334301c030099f99,0x18a0c9082800617f9,0x1c0204cf00617f8,0x1c02040319f17f8,0x2f9c003c738221810a0305097f9,0xc0b000a6d0b0401c058061ff9,0x183f7800b07860028238e121a19ca0384917f9,0xc1796001a061ce39608a0384997f9,0x307ed00160f140030c5240c17200e01805c0ca6a8,0x120e24180e01805c0d26c8,0x307ed00160f140030c51c610ae501c0300b9ef9,0x3cf001901868cb0401c0300c1ff9,0xc1fb400683c30014114504f010ae601c0300c9fb9,0x10c48648401c0300d1fd9,0xc39d803460041501ab90026a00d1898002c800284c2822cf7dec11a0472df80380617fa,0x186c0bc9000263062880617f9,0x57001640003804c60d740ff9,0xfe1000d0cb880305216f9,0x70901eb800263060305297f9,0x1ff80102c00405001f11a42b08e0300797fa,0x1c0204031ab17f8,0x160e802062485517f8,4996465585100792,0xc02e0645526a7,0xc02e0685526c7,0x7101805c551ef8],
[0xd1018064551fb8,0xc101018068551fd8,0x616000e80f730009c0f7c10a084a0305517f9,0x2f4042485617f8,0xc02e0645626a7,0x3101805c561ef8,0x91102018060561f78,0xd1018064561fb8,0x740719001f60185c005cd0630e2a0305617f9,0x3098011020248091fd8,0xc2600440800c02e0480cae87,0x308801881001805c0926d8,0xc1e00288100180480ca798,0x3a008a40060b001670119215020030091fd9,0xd008140200300ca7a8,0x171630e04028040061ff9,0x71630e040200300a9ff9,0x1c0204031b397f8,0x3e1c25082b80617f9,0x1c0204db00617f8,0xcc1d0c585080305797f9,0x1c7a000616ac000c02292121629ca0404917f9,0x3024000304c3a3450880404997f9,0x1c76000616b4000c1ca584858a7281001805c0ca6a8,0x54120e24181001805c0d26c8,0xe3b00030b5a000a0a524690b14e50200300b9ef9,0xbfa00243830d11040200300c1ff9,0xe3b00050b56000a0e3118278b14e50200300c9fb9,0xf023820830200300d1fd9,0x622000e80ac400aa8022600f9002853d002f00e0a3152f7dc0c5892bf80400617fa,0x93000ea0623c0d748ff9,0x8e1001340e3c09750ff9],
[0x118800d40e3c09758ff9,0xe0c2860584817f9,3420093550585,33037047205881,0x68c9082400c17f9,7004311050328025,0xb5c00f7400ab800ba800b8400ff3851428ccd20480ffa,0xe1c5244c2400617fa,0x4332000b81a020d770ff9,0x337e001a0209778ff9,0xaf7001a0209780ff9,0x2810b03060584897f9,0x810b03060604897f9,0x71616060d788ff9,0x8070007ae000680bf631451718488ffa,0xd008140180480ca7a8,0x6470e04028030091ff9,0x2470e040180480a9ff9,0x670e0402c030091ff9,0x116801e16b400440a8346c508a2480917f9,0x116801e16b400440a80e1b142280c02e0480ca6a8,0x45a00785ad001102609c36284501805c091ef9,0x1c0204031d117f8,0x2e121080305e17f9,0x22d003c2d680088070309a3628450180480c9fb9,0xccc01b1001d01598012f0045a00784fc01378008807074b2185861ae0300917fa,0x519302c030099fb9,0x1c48201805c619ea8,0xe24100c02e04c0d2688,0x74648301805c099eb9,0x61394018060099fb9,0x10d03260306197b9],
[0x1d06060306217b9,0x19e1c48301804c0d1f99,0xffc00acc00aa800ba80085400b1f05206fd1a1668c0300997ba,0x17b801fc004c800281028030691fe8,0x17b801fc08060045e00cce007a04e446028058061fe9,0x1fc004c8002810280306e9fe8,0x617c801fc022d001cd200520a3c57680280300c1fe9,0x17c801c40e117800bf200060881416e50280300c9fa9,0x142d5000a1c40e3fd00233005a900110060482ca1cadce0500617fa,0xc58703800e6900244891430a3280617f9,0x4e0c4bc81017f8,0x1202063e0029d8005e03a83820d790ff9,0x118110800cd60064294c80306596f9,0x1c0204031f117f8,0x3f8800c1083c004cd6005c440a14ca0306617f9,0x650dc0a863060306717f9,0x17b801fc02390017bc000c0f0aac45242dce0300a97fa,0x331844056058061ff9,0x1c0204031fd17f8,0xa0302018060681fe8,0x32dc00390d0cc30a0306817f9,0xd1c673c3597f8,0x9c04e0c473c7e97f8,0xd15439e0580c1fe8,0x1c211010aae73c0b17f9,0x78c41ad7997f8,0x2385402c061799fe8,0x50b800f10f818632b00597997f9,0xa0b0004d5828d50d6058061ff9,0x1c02050040617f8,0x2f7003f80476002908006202a1983361a84e0306917f9,0x3c18504415c058061ff9],
[0x1c02050280617f8,0x1d03e1c25080306a17f9,0x30102c0306e1fe8,0x785ee007f02a5002a200e1ac8004f004c224832871f3ab02c0300c1fe9,0x32f4001c13c402c0300d1fe9,0x82f5003f814d8018af80235004bc00fb80190140783c28e08516313552d61cb5f60580617fa,0xc341d7a13f7,86460995543,86528104423,0x7e11e065fd7a17f8,0x3103c0866017a17f8,0x4e0c40817a17f8,0xda400517001fc0723c097a0ff9,0x11ba00194030c33957a8ff9,0x1178009203206097b0ff9,0x1c0501606097b8ff9,0xb1c002d014c8016b0047a009380273001305818660f687188471568490ffa,0x840709044124030c01ff9,0x3508015c0208a1c6e2480617fa,0x2c008086be0c017f8,0x6a50023070606be00c17e8,0x906b200350801b018020d7c0ff9,0x505c8be40c17e8,0x549e00245211157c8ff9,0x2e2400f85097d0ff9,0x2b40e0c097d8ff9,0xa03020b4060499fe8,0x4c120d6060499fe8,0x3f300201801218035080089f960880604997e9,0xfcc008060048600b22002606a0317a2808e34535c498ffa,0x994006b1000870e40180646b1ea8,0x994006af0034b1c80306b16f9],
[0xb01c48201805c731ea8,0x177801940afc00b2802470050d00344a04c1b0e07015c28e2f801805c0c9ea9,0x3fa8003d300098070468090a30c6501805c0d1ee9,0x5da006502bf002ce009140143400d138130640405016d0b851c5f40300b96fa,0xa0408a640b40300c1ff9,0x1c02050ac0617f8,0x26100671000705c54040830a0306e17f9,0x24460e78550d60300c1ff9,0x1c02050bc0617f8,0x1010240089c014ac002b001c0f40a123ca500306e97f9,0x1631030182f00c1ff9,0x1c02050ec0617f8,0x2903e1c25080307017f9,0xa12002413c40180600d1fe9,0x5de000080a8400a5800211180021110047e400b1381302810e3823613010aab51e119bf60300c17fa,0x303c0e03040307317b9,0xbbc000101508016b0048600a1a00589c098361c11a83478c51c5f20300c97ba,0x3fc8003b700123e0a298a0210e0e83826a528c11d00300d17fa,0x5f200fa800080b1804fc016d0038c02be011300392002614138a84c0c24063c706282160e138a385b429bdc060ffb,0xe0c0ac08bf8,0x2b82841584a13f9,0x18400456003f0d481580697fa,0xc339917e0df9,857690230132473,0xc339917f0fd9,857690230198249,0x22f001eb516dbec4a0ffa,0x146c00130184bf00695f9,0x29a000f0284bf40696f9,0x147400130184bf80697d9,0x29e000f0284bfc0697e9,0x1e88004e400e7b1136df40344a17fa],
[0xb0b82841784a93f9,0x19ac0028ee04d4a0342f17fa,0xd7c01b6801814007b100150509800ff9,0xde800360012d000fc400e0c09808ff9,21728466112505,0x69d0011e0509818ff9,0xe0c09820ff9,0x1a6c005b0309828ff9,6421561739810808,0x7b10016d063404a93f8,0x1a5c007a8045880584a97f9,0x1a6c005840604a9779,0xd3600096112a0684a97f9,0x7da005c600d6800c09440006a00fef106142a9c4a8ffa,0x8500f440027200319d1cd1480344a97fa,0x7c9003e0b4a19c0697fa,0x360800b0ac10ff8,0xd7c00cfe001afc00721591830ff9,0x2640663002068004c024d838ff9,0x961311840ff9,0x3e680138309848ff9,0x1f2c00a1c18604c4b17b9,0x5e4000a05860504b17f9,0xe310c0ec18ff8,0x7a200179002c284d850ff9,0x7cd003215030d858ff9,5673769444775864,0x2a0a088805c4b17f9,0x3e88009101280604b1779,0xfa20050609880684b17f9,0x1f78017280133002de007126800b5801f55c906867e04b0ffa,0x1be8002680020cf1c80344b17fa]],
[[0x109c000600854a1c00697fa,0x6ca00547800b0ac20ff8,0xde805d200d68036f800ea0b0d860ff9,0x26402a3003f780130a50d868ff9,0xc52860384b97f9,0x48919880404b97f9,4600648956022776,0x420b0d0a11870ff9,0x21980188509878ff9,0x10cc00381428604c4b97b9,0x3030c302c0604b9f68,0x10c400a5c80584b97f9,0x5050651880ff9,0x10cc00820d8d888ff9,0x42b0008e816c80604b9779,0x7d6005ce005984003106400eb5e618e3116a44b8ffa,0x65f000e10040008010384480344b97fa,0xcc0c9040384c17d9,0x2bd800648201c034099f99,0x443e0c9082800697f9,0xafa00345860384d97f9,0x2be800140490c401c0340d1fd9,0x2a5c008500f2c0029e00020b1f11caee0380697fa,97042907436793,0x1a2400442e0e0c09890ff9,0x261a6c00320f8509898ff9,0x2b6800d86034529779,0x1f067400d860345317b9,0x15ec007f8954c0340797fa,0x6e0101a364561f37,0x7302202e034561f78,7907972912387960],
[0x2d0126035af1778,0x7740236a034561779,0x612836a2b80697f9,0x53b0620200346c9fb8,0x32b31e110502005c069ff9,0xa13c1280404d97f9,0x72502550200340d1fd9,0x1299001bd80029800a190af18042ec0400697fa,0x89e0050a143022034099f99,0x2c28a6910602c044069ff9,0x150442862d40697f9,0xd8541860444d17f9,0x506101101a0600d2748,0xc40a0c30220340c1f79,0x5b0d0a1450220340d1fd9,0x1758036b4021402d600df80240fa008c8007700060eb241bc7ae0440697fa,0xd3a0025c0e0c098a0ff9,0x1f3400f6061c098a8ff9,0x10cc00aa0a5098b0ff9,0xe04262604c97d9,0x130240405ac317f8,0x2881e022880584c17f9,0x74020ac38ef8,0x9320d8b8ff9,33037048614905,0x5de00e1802c3950011200f874b082481333aa84c0ffa,0x70681d4a2600697fa,47425261560,0xc904c640d17d8,0x2d36001781d60b0d8c8ff9,0x3f2c002e01e0c8d8d0ff9,0x186200620a83098d8ff9],
[0x345860504c97f9,0x67802473680584c97f9,0xe1c528805c4c97f9,0x472430ec48ff8,84471133223391225,99774302421684217,0xa18e260684c97d9,0x15c40072e000ac01e120c8284fae6121a325e44c8ffa,0x2814201a04c4c9f99,0x13016301a0684c9fd9,0x1cd18f012c80344c97fa,0x43a00706040345f97b9,0x1050071840346017b9,0xe4419402c034099fb9,0x10f0a180d03004c0d2708,0xfc19301a060099f39,0x4c71301a04c0d1f99,0x16b007040160710046c002b8012061a00836bd83354e0340997ba,0x120102960c0b1be7,0xf54001118012c0302028059851fe8,0x1ea80022300222c3028058069fe9,0x12d003c8162840504d17e9,0x225002c20280340c1f69,0xcd020021c03d3000a180010d8360487df4e0500697fa,0x1a3400695c0e0c098f0ff9,0x131a6c005901503098f8ff9,0x1e2f6800926034661779,0x874009260346697b9,0x446007c954a0340a97fa,0x1c2600160840ad8517f8,0xd60560b684056058069ff9,0x1a4e001b40d404258a0346817f9],
[0x2c020461498517f8,0x360d81185202c0340c2768,0xf60be0a1260a4058069ff9,0x5a0800483a05ca0346897f9,0x7c28405aa193f8,0xb206e045aa8ec0b17f9,0x1466d000f0a0012058060560c0b17f8,0x6102cc280f9f78,9291750127804344,0x6030c62b98517f8,0xc0e1302c069851fe8,0x2d50009a80167004d6002860057014667e1010f01044c0598517f9,0x506868302c035851ff9,0x133001391078385615c058069ff9,0x1900612836a0346a17f9,0x185c000e6005e0680c0632402c0340c1f69,0x988029e1732502c0340d1fe9,0x142cf0004d680438059401c1004821401170005e00d070787244891c51d54ff5076ff60580697fa,0x35032707c0697b8,0x980f81cc15ca0346c97b9,0x88294302e0340d1fe9,0x1995c00483e90006110a442307282b4c05c0697fa,0x34d8008f80b09900ff9,0x7cd003f40b1b0251908ff9,0x866006b80a8198d910ff9,0xb1a40081920d918ff9,0x2103262684d97e9,0x1a1009100b18038600d0408022e002bc0123a0183e08328315e44d0ffa,0x9502ea2680697fa,0x711001b3c000680b0ac50ff8,0x134b8002f01d1c91920ff9,0x3f2c000f0170f850d928ff9],
[0x618801a4028509930ff9,0xc8ec03c064d938ff9,0x2db00098800a8800810045c0011800a0901030f85a0ef241a08be04d8ffa,0x380c201a0604d9f69,0x5cf3c680344d97fa,0x194c005840346e1779,0x27f800e82840346f1779,0xa0cc15b501a0600d1f69,0x1a7007d00b8803860050448022e000ac0030287c0507260905ca1aee0340c177a,0x3681182921880347417f9,0x510230141860347497f9,0x10c06852860347517f9,0x22402ca009bc008b8002b000c1a0ac108431616e02021c175c0304baf60340d17fa,0x2e3001fa00c5805d403520112016e00af00e0802c10a008b803f600c6291f8fc694702146c6e518b0253444269bd8068ffb,0x1c101c4d4711b77,0x690201c0649a9f78,0x1c101d2789a9b77,2003545267575,2003612376695,0x1d9038201c4389a9f78,0x290201c43c9a9f78,0x290201c4409a9f78,0x6f380013989040389a9779,0x61f038e4052038711bf8,0x11b0842660520380c9ff9,0x30505305203a4f1bf8,0x30505305203a4f9df8,0x30505305203a501ef8,0x29f5c140856052038871ff9,0xc768a5052038879ff9,0xc4c0855052038881ff9,0x113d3484cc0a40717fa],
[0x95000e7800542000d0f0d940ff9,81100306834561016,79349191671,79416301047,79483410167,0x1ea1c706ca48717f8,0xa044ca48797f8,0x3300c26ca48817f8,0x2da80186a400331800270c0e09948ff9,0xd8801d2b000ad40088509950ff9,2475584004056,0x385c002180c680484e17d9,0x13f800f26000c228d5958ff9,0x8816043644e17f8,0x28201c102e0644e1fe8,0x9ac01f020c80069e8066146805c4e17f9,0x8816043904e17f8,0x267000e017300053a000923003045c851430821720644e17f9,0xe0500030e260684e17d9,0x4b200103805bc001528008f8008ae58c2e06042dc4e0ffa,7004302338168825,0x304106038c517f9,0xd860966e0f00717fa,0x1408019940002680024120e0d960ff9,0x15a80253c0068f001638e0d968ff9,0xc700528c002d3000e1209970ff9,0x59e000410404c4e97d9,0x33a01c98771800b0907060584e97f9,0x37601e2a000e1209978ff9,0x57e00041040684e97d9,0x31a006281824240037a00ff471b82321c4e8ffa,0xc7e00090620b0038711bf8],
[0x63d001b41b1c40b00380c9ff9,0x12120b003a4f1bf8,0x12120b003a4f9df8,0x12120b003a501ef8,0x3ac8285150b0038871ff9,0xb4128240b0038879ff9,0x2d04e140b0038881ff9,0x63d0004f680c33881600717fa,0x1d1e00120204cc00c97f8,0x1d1e00012799813f7,0x3a3c002327d9815f7,0x1d1e0000cc25016f7,0x74380072c1c706cc08717f8,0x7448000a044cc08797f8,0x74380028b404cc08817f8,0x1cd80045048004610004f5c0e0d980ff9,0x38a01adc00449000d0f0d988ff9,0x7100482800c040088509990ff9,0x410200644f1fd8,0x35b800d70716c0404f17d9,0xd5b0005c1cd0634c4f17f8,0x6b30010300685850013e200f3680584f17f9,0xb816043644f17f8,0x31201c102e0644f1fe8,0x1fa00f0fe2002c28066146805c4f17f9,0x115003a9000c228d5998ff9,0x3160061e0236c0604f1779,0xe80a042787197f8,0xb816042787217f8,0x6c1000f700b85770031ac009650050c27ccc91f00644f17f9,0x360800768073215dc0039805c4034b7a2223dc4f0ffa,0xa189060394c17f9],
[0x17580130c66a1e40717fa,39642728861688,0x240a26cd00d17d8,0x2f200695000fd401c8240e0d9a0ff9,0x6f016c6003c3001e0c20d9a8ff9,0x5c80e8e0079f006c38e0d9b0ff9,85691908328462328,888681776519144,0x1948302c0684f9fc8,0x7540261878019c3067060584f97f9,0x1df00cf4014d58d9b8ff9,0x1898014c50883280684f97d9,0x58e0011b001cd006160bcc0193b2d0228309c4f8ffa,0x7892880385297d9,0x65d001449880385317d9,0x659001d945b4d00380797da,0x50101c2b0711bd7,0x42b001f8060201c064561fd8,0x1290010300168340c6a0385617d9,0x2290032840385697d9,0x2f70018846a2800817d9,0x2cd00447800dc80488c6a0405097d9,0x2f90014080e0280400ca7c8,0x354800524003179800ba1442501c050081fd9,0xbe400f0846a0385717d9,0xb3c0111a0037e01d08c6a0385797d9,0xc4d000a80e1301c0406b1fd8,0x6520201c0406c9fd8,0x38201281100e02005c0ca7c8,0x82ab4011160036ec03a213501c0400b9fd9,0x183fc0068d08604401c040711bd8,0x170101c040711fd8],
[0xe2e0201c040721fd8,0x3200dc024a01a0900733b0012d201f0651771b0105188ba01c0400c9fd9,0x1424e01870050c006401b804940342e0030c008100b4807c3ac84a6011e5700380817da,0x48e00001c2e4711bd7,0x245005810201c0645c9fd8,0x17280122802180c680385c97d9,0x3ac032840385d97d9,0x30d0014080e0280480ca7c8,0x5fe4006616004c58a8401c050091fd9,0x6de8001c0e1301c048699fd8,0x7710005238021829b501c058091fd9,0x1c0e1301c0486b1fd8,0x6520201c0486c9fd8,0x3ae01281100e02e0480ca7c8,0x705e7600174403a213501c05c091fd9,0x14f0e280385e17d9,0x14ec0060500350b0a280385e97d9,1997495933911,0x145ce0047200d1082286401c048711bd8,0x170101c048711fd8,0x381090301c048719fd8,0xe2e0201c048721fd8,0x7c028e0073f001485400430c0043980686803503519f50d9197901c0480c9fd9,0xf8051c00a0801211f00d7200526200ed0032c007900d9006a01a81489d2505498f00380917da,0x442842846017d8,0x27300620c9060386017d9,0x4c0020c9060386117d9,7004312123840473,0x6e88006f8e4804c5097d9,0xdd9000d201c059de1fd8,0x6eb800620c71401c058099fd9,0x6b7001a82c301c060099fd9],
[0x30c9060386197d9,0xe4a001adc005c442860386217d9,0xc820a0040c01f0a380163003c0540300800e0f201ae02a201f81d7a4046844c0380997da,5352752808302584,0x76093c01a0600123801bc09108d59c0ff9,0x803b3c00530082099c8ff9,0xa8801b68003604a024d9d0ff9,0x12220003408850ac60ff8,0x5a00c0401d82708850d9d8ff9,7004312150317049,0x3c120562800b1fe8,4807066336697319,0x1bca001902341402280b1fe8,0x22027100030c013f80152cc4a2800b17e9,0x9033862800c17e9,0x5e0220808010500741611d001960037017e801780c3001dc0364061803c0635264804185b2e4500ffa,0x3b0718e260399d97f9,0x261666c2800717fa,0x62044cf08f97f8,0x258280002a00f8c8314559e0ff9,0x79600168120e0ec68ff8,0x8776001665919e8ff9,0x62044cf88f97f8,0x46b20001b004b0714519f0ff9,0x1ea80110240e0ec70ff8,0x178e006a919f8ff9,0x271002c7003168003d8065c00f01c0892d1602118dc508ffa,0x7588000851326e0500b1fe8,0x6e8800114100e0282b80b27c8,0x81c008c14f8005a40034300347a422501c0500b1fe9,0x17c032880066036d0016980030bc1490ce501c0500c9fe9,0x14c05102800e8353e0053400cc06b600185a6000c0f029188c4f500380a17fa],
[9301399415,82721707895,0x28d80053a00fa0618605a681778,0x307c003539484dc4517f8,0x1040c4802163884de9917f8,0x10d0028880052200e768288ee4dc0b17f9,0x145c386149a017f8,55858238455,0x1a0846229a017f8,0x271000c62002a30056e021830ca2e059a017f9,0x2201056038571fd8,0xa858982b01c0580d27c8,0x2dfc002e0cdf065140560380b1ff9,0x2d8042a004201c28003c299844c0386817f9,0x384c00045061cb1501c1480b1ff9,0x3c1204039fe97f8,0xce90013041060386897f9,1935845956567,2017047682007,0x880e02c0696923c7,0xbf5000c828ef0101c059691bf8,0xe2700025290301c228571fd8,0x38a40034a1a00e1140580d27c8,0x6ec8003c1923d20e6cb701c2280b1ff9,0x33f8001e002980072401580f80104c15cc0386997f9,0x681cec0028f0068704ca63601c2b80b1fd9,0x6809b4000cf003ca008e03822423501c0580d1fc9,0x1040583081400983c22e0189004a480078031001de0066030401c348048402a090f0504878080826d73f9acbf60380b17fa,0x92801216001638403a0897f8,0x32803ea004a0abc00a4801780c86000608c09c38861cc0386b17f9,0xb2c01a0e000c63060386b97f9,0x1d806790003402c700103004c0580609c0981419ca0386c97f9],
[0x1380063040386d17d9,0xec033c8001a016480080802602c030520360ae501c05c0c9fe9,0x343d14000ce00659401c05c0d1fc9,0x7600e07880103000e0f1ca6c00453400340f00f0009700047f802602c0303e07ec25c04595f80380b97fa,0x24041060386f17f9,0xe6600345860386f97f9,0x733000480c6301c0600d1fc9,0xc8405001380c5400ecc015300ac010f1683904512f00380c17fa,0x5e02821c08803a2293f8,0x1818009f801107e0482d03504e29cc0387113f9,0x6100ca6001580bcc008c0bd400482f01785ca0387117f9,0x880086001d7006605e00413c0e1cc0387197f9,0x1d8067b0004402b9001090064048160bc0e240e1ca0387217f9,0x7600a0778005a4001101c034025a00dc80230482fc0060ce01466804c3c6c0902c147407008f4870c135f60380c97fa,0xb3400da00c108480387497d9,0x41008309060387597d9,0x4428403a3617d8,0xe16001a7400210250786880387617d9,0x3d00303bc008880320b0898017700140340076801a80cf001cc031401d8070e82c3c061a8041045440898ee0380d17da,0xf400c0ef0022200c82c226018f0055400540500d0095804b4012e01a80cf001cc0314009804861061e0a46382c1c58461990104a32229bdc070ffb,0x511050763da097f8,0x193006301400362930d4b1da08ff9,0xac0420a4058511df8,0x1ab80072f001f8244e4e0585115f9,0x18c012400a6f0006863062880b97f9,0xc200ce0031d0009a8030fc800f808eca2880c97f9,0xd600e600fa0409002010026e004bf4009c40081002f283316dc510ffa,0x24132882945196f9,0x320b03062985196f9,0x1ccc006d0282d895028c0796fa,0x41047585216f9,0x381049a85216f9],
[0x686306ba05216f9,0x12c410a0585216f9,0xf86306d085216f9,85729482380154617,0x105800282dca2900c96f9,0x12b004560034c00198019e01fdc331298520efa,0x729001c6832862905296f9,0x365001eb801cd228b8a2905316f9,0x39980031b438e1989502900796fa,0x280d8008b400121060585217f9,0x790085de001f0c60da10ff9,0x21100031f0c22805c5216f9,0xa0620021b00062c1862900c17f9,0x281b802180bc8072e801496004a5007c43413be4520ffa,81100254247753720,0xa04443da197f8,0xc6a00081fe00112800eb82a11a18ff9,0x8d40174a0070300120e09a20ff9,0x8928006d400f300240e09a28ff9,0xc82000b04980649000ce6480585297f9,0x582940318800a630605c5297f9,0x2780a36d800ac1251a30ff9,0xac0351800c20650da38ff9,0x18b4001e0928060529779,0xc9e000b05880f4807086c00283c15ca2940c97f9,0x75800594002a0b5019407c80523a010d0034c007300c301a7008e03ff70114f12a4528ffa,0x3550008380103000823062945317f9,0x33008001d00e121582cc4a2940797fa,0x16ba0015c200d0400b0230da40ff9,0xd5c004668006780220d0c611a48ff9,0xfdc0147a0042c0320609a50ff9,0x582fc00d480010885880585317f9],
[0x2c1a20065c0068241860605317f9,0x6c2604d2c1017f8,0xd1802b401173801d1711a58ff9,0x4e0c4d301017f8,0xea8038c02870035851711a60ff9,0x5380066c00e2dca0645317b9,0x11300c980426004d40119004880341d200e40790043680638054e017407a5a60d1129c530ffa,0x6ca002af00074038385891444ca2980797fa,9746351476742136,0x745800782c130a4058541fe8,0x1c4600128304142c140a4058079ff9,546208418893816,0x335c00370322e190803c6897f9,0xcbf0011c0658f06718cd040b17f9,0x12c80155803234007901954e4c0585417e9,0x259002a50067f400dd6002a094085121c2fd9af40580797fa,0x259002a30011fd0037c80058142632110582add005c0797fa,150504771576,0x6c0d210803c6f17f9,0x1998000580ac60605417e9,0x94a0037f800c818308c143918954e0600797fa,0x1c5000640282dca03c7113f9,0x30fc0012e800282dca0645417e9,0x6ff000a08007240048709051821e4222dd00640797fa,17997349949177,0x60f0011c1c650da70ff9,0xbe8009a1a3860da78ff9,0x72811c251e0538ffa,0x259002a70034100226018e4001a02c1c5890ccc94395b9c540ffa,0x36c0045dc010700518d007fc01bc405c22e011300838054c020c01c4031c053800901cc23324271112626e16dbe4078ffb,0x5409020200649a9f78,0x93c0409a9b77],
[0x1c102127c9a9d77,2278490283639,0x1d903820204389a9f78,0x2c16090302043c9a9f78,0x5409020204409a9f78,0x82280013a207040409a9779,0x21501826e60520400c9ff9,0x46e053053278081bf8,0x46e0530520424f9df8,0x46e053052042501ef8,0x19dc68a80856052040871ff9,0x10a80c08a5052040879ff9,0x10a80c0855052040881ff9,0x27440024f2824dcc0a40817fa,0x1a04006810a0da80ff9,0xeb800e83860da88ff9,0x9e3000c7042166a0548ffa,0x1106106040b216f9,495056230881272,495056230914040,0x901020064b31fb8,0x901020598879fb8,0x154c0012e00fec00f440a26040b317f9,0x901020065a91fe8,0x20ba000ca208848041a917f9,0x8238002c8f0691c46020064199ff9,4536606005240,0x32a01071c2502043c199ff9,0x103900023156307d9720401997fa,0xa6d0013700ddb001e84da98ff9,81100309720242168,79350600695],
[79417710071,79484819191,0x1fe10406d508717f8,0xa044d508797f8,0x1200c26d508817f8,0xb24001c60052a0009e0809aa0ff9,0xb130003101e480261f0d91aa8ff9,0x1108000024064551fd8,0x39cc0010f800d818680485517d9,0xa044d59b597f8,0x62044d588f97f8,57337976311,0xe18187084ddab17f8,57366288343,0xd601405655ab17f8,94364856813819896,113374860791,113441970135,0x19429302c08d5acb97f8,0x2014004ad0018a26051ab17e8,0x7e200402800ce400af8029774d70083825dab0ff9,0x95a004831c3028064551fe8,0x47ca0067fb001494e00298782884c0505517f9,0xe03000ccc042a86b17f8,0xb802043645517f8,0x5e401c102e064551fe8,0x1e8200179000e071302e068551fc8,0x1ee800cf3900045c401f6134046c05c5517f9,81100263958583288,0x7432043905517f8,0x72a80060c01ccd400c4f40063413730a31458f00645517f9,0xf8400275000c88033f002e600671418e443700685517d9],
[0x7c20013a800644019f801370008a9099bdd0b86d8550ffa,0x4c15058c45028140081ff9,0x25d801e84831b88e1400817fa,0xa04008a48001c2e0dab8ff9,0x1524002df001638e0dac0ff9,0x1bd400005000e1209ac8ff9,0xa07056600a17f8,0x712800a41215080505597f9,0x1c46000e1209ad0ff9,0xe1f000709040685597d9,0x159800554004bd0035e614de179a0558ffa,0x4415058c450d20400c9ff9,0xec1293c1a4081bf8,0xec120d20424f9df8,0xec120d2042501ef8,0xfa02120e150d2040871ff9,0x882a028240d2040879ff9,0x220a80e140d2040881ff9,0x4fd0916148c1a40817fa,0x224a001f00c04d6c0c97f8,0x44940023279ad93f7,0x224a0000d6e4f95f7,0x224a0000d6e5016f7,0x88e80072c1c706d6c8717f8,0x223e001f00c04d6c8797f8,0x223a001f00c04d6c8817f8,0x39b000887f80013b41a0e0dad8ff9,0x201caa00220209ae0ff9,0x1f78000c40088509ae8ff9,0x2f4042b06317f8,0x1c0f05076640a17f8,0x15205063205617f8],
[0x9e2000601028064561fe8,0x21e90010c8034e9003d41e0aee0505617f9,0xe80a042b06b17f8,0xd002cc043645617f8,0x70401c102e064561fe8,0x367f002ea0151c0056600090077838386a05c5617f9,0x9f00c06d79b597f8,0x161a030d096cd0ff8,0x10f800768000680318118cd9af0ff9,76581412162377592,0xe380261e0236c060561779,0xee00e80a042b07117f8,0x4c80a062b07217f8,0x5433134064561f78,0x1750081c00ccc4004aa8011402c139c9a20a378f20645617f9,0x3428017500844019c802cc0518028806c2644ec121b9dc560ffa,776531207886840,0x1082104480e260416417f9,0x1415058c45028220081ff9,0xa0a80e14110041af9ff9,776626455975928,0x44817060416617f9,0xd6504996e2200817fa,0x2f2011350006509b00ff9,0xa60746800fc09b08ff9,0x2600d1c006c38e0db10ff9,0x6900261f0d91b18ff9,0x6500261c8832a0685697d9,0x605000e98011201f6242e04d98568ffa,0x16180000200645c1fd8,0x2cd00160800d818680405c17d9,0xb0c001c0e13020048631fd8],
[0xb0c001c0e13020048641fd8,0x19f0052500108140200480ca7c8,0xabb003b100199006a3e007608514028040091fd9,0xec4002c300110200486b1fd8,0x2c300110200486c9fd8,0x1334007dc01281101002e0480ca7c8,0xd5e801da801324004f88039c1c1c3502005c091fd9,0x5860038e260405e17d9,0xb0400560a260405e97d9,0x2c30011020048711fd8,0x1618005412020048721fd8,0x7b100174801870013310064dc00b4021099a0248df90200480c9fd9,0x83e0057a0035c0174800aa013b00cdc009b801680427af0e48b0bf40400917da,2804105320951,0x610293b1b39b77,0x115b0000029341b39b77,0x8a98007d838226e051b39bf8,2833363246455,0x4b8126e0519c1df8,26951030582,27018139446,6601270892407,0xdf014044dcc897b7,7424060833732535,0xff014044dc1f17f8,0x610c126e052761f78,8294766455,82722428791,0xa7a00281028066681f67,0x9d0020640052d0019d303186052681778,0x3c38126e052681f78,0xcb1464dc3d97f8],
[0x612024044dea417f8,0x14e40063047526e0500c9fe8,0x21e0024c0081b000bd40015802a49f50c2660c4b24dc0a17f9,0xd40420280419c1df8,0x721b0b24626e050081ff9,27006212023,0x1740b0b060f9b217f8,0x68441edb217f8,0x54d0028234028065b21fe8,0x108c0081d00118400be013f07018c42630051b217f9,4807065923559319,0x686430282028040c91fb8,0x5b0e2307c280081fd8,0xd0ce458273607c050081ff9,0x1be00b75800ac0263000281f05c2e089cc0406317f9,0x17c4006c120f6280081fd8,0x2a9800204420a2a1a960f6050081ff9,0xac063c00ed00479c000c1182214bb520406417f9,0x208a00297500824d7,0x208a0029754082557,0x3208a0028041eca5d8,0x85810a00280419c25d8,0x2201056280081fd8,0x208a0028041eda5d8,0x1b0210a0028040c025d8,0x1a3a0014210a00280400b27c8,0xada001890a00280400ca7c8,0x3950055e007860035e00a9e00667fa848e3326140050081fd9,0x1bca001680d780161a00a8807f805c01801070a0961705da80280400c9fe9,0x904c00a59601af00a8319001680c4800e096e002b8029601bfc038a5406010040984aa8d50626cbf60500817fa,1724815223,18233595767],
[0x1b40a0e0ece8f78,0x9c427c00004062151b28ff9,0x741614003c61060406597f9,0x6642ae8009888372c0406697f9,0x6c41402a260406717d9,0x279005405dc0061a0096c004f1c1b08c6e0400a97fa,0x20200070256785717f8,0x38814682b9b317f9,0x309c0567db397f8,113509635575,4649062209511,0x64840e189681b397f8,5634269191051256,0x6844d9db597f8,0x6204447db397f8,0x42d00208c0061a0051c0052037985c04e75db38ff9,0x618022a005a0d042bad097f8,0x638814682b9b397f9,0xe230002a008209b40ff9,0x18d800ae04a024db48ff9,0x34800d409120891b50ff9,0x8f1800070256885717f8,0xe2046282b9b517f9,6922949203073001,0x217800c900d8804c1bd0000402b601318016a01820132014202b4047c0042ebc183c25b2e8570ffa,0xe526042d097f8,0x840460047102846041b397f9,0xa2a0282415c041b59ff9,90531602896888,0x35029c41706041b517f9,0xb360056504996e2b80817fa,0x62044db08f97f8],
[0x25ad80053200e417031455b60ff9,0xfa9800fc09b68ff9,0x281a003471451b70ff9,0x93900261f0d91b78ff9,0x5560017b0018680296013f0011fba0d066dc578ffa,0x208801618018b800a40013001f601700608a068ca29cc0406b17f9,0x37a4002900358002e8027405880fb00b8030450361629ca0406c97f9,0xde9000a406e401888029601f601700608a05844e502005c0c9fe9,0x1568005ec002c400610028a005d004483871502005c0d1fc9,0x102c00b13980360db800020163005203760058800b20024b80b301fa01500607e07b19049ff80400b97fa,0x11071860406f17f9,0x280e5406198a0406f97f9,0xdbc0071630200600d1fc9,0x64186800dc044a0029401a1006c108070e5824512f00400c17fa,0x5091a350f60400c9ff9,1733203831,0x830020568c0c97f8,0x90102020066221fd8,0xbf20067839a35020064411ff9,0x37a4002d017b00295003f601f0742a80a09821cc0407117f9,0x1c68783c0865960400c9ff9,0x2465c071340817f8,0x6f48005a04bb002ae01f601f0742b81e8719bce0407217f9,0x540560c634250202680c9ff9,0x220c0001402c600b405dc01d01a4009f00a534022c01c0b0581c1b08c0b8384d6283ce32bf80400c97fa,0x1b300243003160150906348c0407417d9,0x67031260407597d9,0x20f800c500d980641b7000140011003660057805e8053804a809d00170051282443009630c03011ee0400d17da,0x96400e38018a01b300c836e000280584018803500bf802bc02f4029c025405b809701a412042046c394084601070a518471b1829bdc080ffb,0xcc4003a030678a0f00897fa,0x43080061c09b80ff9,0x76e0073e0db88ff9],
[0x333000c901867298580ffa,0x35e80013a030678a0442297fa,0x42ac0022052d217e7,0x111002e64002c824051b917f8,0x46400fdc00f990008c63852d20ff8,0x3fc007d6800a040206dc80d17d8,0x25280097801e880039a002ed801cc260411b90ff9,0x369000f4800584004c3c0db98ff9,0x367c007a402d5006bc0dba0ff9,0x38b007b1800a85e0604c5897d9,0x26e003d4c0008608506051ba97e8,0x35a00716006cc01346002930c10a11ba8ff9,0x9b800f4f000a39c2028058589fe8,0x4352001387007a7800e2d862c80505897f9,0x1948056900b17f8,0x3ecc003a0d043405897f8,0x9b800f670006148302c068589fc8,0xa1b300385007a680010b983045080585897f9,0x4888483030068589fc8,0x3758005141860605897f9,0x36a00706006ac001b400137000e12e585060685897d9,0x6d400e0c00d58003680159002540052c00e911650504252c1c588ffa,0x32070678a1400897fa,0x3888005e0e3c0ed28ff8,0x54804051bb17f8,0x198c00488800bfe0069846715bb0ff9,0x13c000c280061c09bb8ff9,0x4d6800be401c684dbc0ff9,0x548056980a17f8,0x1f920009441c2848a0505917f9,0x3f44004d0487060545917f9,0x7e880071209bc8ff9],
[0x7e7800e141860605917f9,0x3f3c00389040685917d9,0x3ee0000804da00ad802a401ac801af82026c539c590ffa,0x32070678a1c80897fa,0x1c500393800287120dbd0ff9,0x201fd2000101821c11bd8ff9,0x5ca0061a00e3c09be0ff9,0x4e00c0569c0a17f8,0xcc800a602185080505997f9,0xbee000cd800e10e060585997f9,0xcd80071209be8ff9,0x28126060599779,0x17ec00bb801220030a006bc1030849198598ffa,0xb028b38a2400897fa,0x378039c80030e020dbf0ff9,0x2981ff600220209bf8ff9,0x1700d7800fc09c00ff9,0x1948302c0685a1fc8,0x321007a06060585a17f9,0x864830300685a1fc8,0x31f007a06060605a17f9,0x64e00b818a0c11c08ff9,0x319002de506080685a17d9,0xdc20001640021c031100697c87042b0985a0ffa,0xc419402c044099fd9,0xe34262d40997d9,0x1e1428604c5b17d9,0x385194022060099fd9,0x70e260446197d9,0x1e142860446217d9,0x197003a100356000d6007de0002400a1801f07e70c86844c0440997da,0x8758001a0586080acc497f8],
[0x439c00110040860adc117f8,0x7e3a0c315056050089ff9,0x2c4004617800127013cc0446297f9,0xa40102805ad41de7,0x832400c1b000de1c828052d417f8,8185340689717240,0x438400322078041953120500b1fe8,0x1114553120500c1fe8,0x185000ea6000cf31ac08f2e6240a17f9,0x360102805ad49de7,0x20c3002e64000781540c826052d497f8,0x78c4169c117f8,0x23a003cf4000f03620d3028059c11fe8,0x1507854028061c11fe8,0x17d003a1007a5800b402179898b062c051c117f9,0x509e3c0e03150b4050089ff9,0x2802827000f018383080446397f9,0x23405048f540897f8,0x2d4013b5003e3810b04c0446417f9,0xa40102805a8f1be7,0x43dc0026c03130287680b1fe8,0x36010296a80b1be7,0x10f9000ce0313028059c21fe8,0x18bb801ce8005c400284019e801a8282174fa8028058089fe9,0xca20051c1e0aa50280440c1fe9,0x145800673000e02341840280440c9fe9,0x1611220037c004cdc01381a5002814003d003856c0289d0067a00041c4c34a699cf008cb5f60500897fa,0x17421b2001840c26c3280897f9,0x2106ed0001e01c1c4dc18ff9,0x5c518800340c26a0446617f9,0x168cce000e0d11080446697f9,0x568009c02ea002fc801c83f50c386282f40440a97fa],
[0x44bc00110285060aced17f8,0x44ac00110285060adc217f8,0x7f9800a858982b02c0440d27c8,0x1fda003f8f828d5056058089ff9,3599700983,0x1040a85047681a97f8,0x7fb8004407098160220681aa7c8,0x13b001fe60039878f828d602c0441a9ff9,0xcc8006e90006605b0735500446817f9,0x3c20920007c018332702605a8f17f8,0x21ce0012184840889ac7680b17f9,0x340ad80078d0006844020c8296a80b17f8,0xa900003f0007063ac060c129ae059c217f9,0x1000410b140d6058089ff9,0x8c2002a090e64a0446917f9,0x1b0f8108a02c0440d27c8,0x44185044114058089ff9,0x219002a1e16ca0446997f9,0x17cc002170039638c402c0440c1fe9,0x22e0005a40027403bc01510003046021820c148302c0440d1fc9,0x340b78019b8033033200f900068007a0070b580274039c010e20122015100440c53e12094b5e7839a5df80580897fa,0x31400f7400f9d0018c0e3c0ad58ff8,0xad801dc80199004ce800aa078c10a11c28ff9,0xfd1000c40e3c09c30ff9,0x19b000740e3c09c38ff9,0xc9c00240d8623c11c40ff9,0xfe0036c01a28037033200f7012480322009d00ef0071009100cf803b07ec85262b116c5a8ffa,0x16051652c2d40897fa,0x11e003ed800560fc0ed60ff8,0x2aa002aa20053d800e8664215c48ff9,0x823400220209c50ff9,0x1243001e84dc58ff9],
[0x7bb006bc0dc60ff9,0x7b004950019b007a803b20027403bc019f000081bf2023453e05b0ffa,0xa9300070e480446e17f9,0x122c0026241880446e97f9,0x8812050e00897f8,0x46600f0a08880446f97f9,0x2f8016f001160029a000c09c01852c4840220600d1fc9,0x67200dc0c5800c3f2008f401216f002240071008f0094d005870639b0a8042b1c0908b12f60440c17fa,0x1ab4003f6006dc01a07900083580498068c01b07c0a0e198861d00440c97fa,0xd8120471e080447617d9,0xf2003a4019c8037033e00f10136802e2009900f1006f009300a6802c2c29780e1bf0a28b08b00440d17da,0x3c800e900634035a01b819f007880024003d00485c4013201e200de0126011d006a432262a399062c29a52af829bdc088ffb,0x12038582650b00480c9ff9,0x901c0e140b0048881ff9,0x22640068905c184cc1600917fa,0x135c00e0c09c68ff9,0x113e002e1386699c5b8ffa,0xc610688c0916f9,495056365983736,495056366016504,0x901024065121fb8,0x4c90007a019d400f50440a280491217f9,0x901024065c71fe8,0x5d7800248498318a049c717f9,0x172600124491265024064301ff9,0xb8900188b4482a1588b20483017fa,81100313679665144,0xac00826e3c8817f8,0x349800e32001634006c82080dc78ff9,0x3cd000c280028d001e84dc80ff9,0xd4800634012e80150309c88ff9,0xbc9000a0438255c90ff9],
[0xdca0006010280645c1fe8,0x2dc40024db0036e3003e3431880505c17f9,90283387823855608,0xb0800497c00dc3680585c17f9,0x1c12043585c17f8,0x2706005df800bc108d062c05c5c17f9,81100264898107384,0xa3320638c5c17f8,0x5e60075400420c018098003b00a536c0cde2a0645c17f9,0xe2c00bcc00ee80089000130007a01d25a4c219e35c5c0ffa,0x3e038582650d20480c9ff9,0x1f01c0e140d2048881ff9,0x19a0a6604cc1a40917fa,0x13780120204e4c0c97f8,0xd1c826e4c8817f8,0xf6300031e00136801afc120dc98ff9,0x13c0015880061c09ca0ff9,0x490014080150309ca8ff9,65168774647,0x17e20020c05043145c95f8,0xd03c043185c97f8,0x1a1b05063205c97f8,0x438013e801c10280645c9fe8,0x10d0800acc0188700275003d82262a0505c97f9,0x3410013d800a0438255cb0ff9,0xd03c042e46b17f8,0x186ac002d9800a43242805c5c97f9,0xc7800f1006e042e47117f8,0x54200211a0063c0069800c33ccf1ac0645c97f9,0xd8800aa400468018f001aa00e94a4808e34535c5c8ffa,0x3c0c12ca1c80917fa,0x2800c1d000c80e120dcb8ff9],
[0x54900175c0024120e0dcc0ff9,0x2448014f800e1209cc8ff9,0x1d06c056bc0a17f8,0x167800a41215080505d17f9,0x168800b0907060585d17f9,0x5a2000e1209cd0ff9,0x4a5001b50023400a0400d711ac24e185d0ffa,0x1a0a2c184cc2600917fa,0x2e406168006509cd8ff9,72589424201720,0x4c02f3800c8240e0dce0ff9,0x170172800fc09ce8ff9,0x4a024056c00b17f8,0x210284059cf17e8,0x2a9006c3067060585d97f9,0xa94004418110dcf0ff9,0x816004d8041400bb287161224a05d8ffa,0x11314056050091ff9,0x203804086049e597f8,0x1f4019a06001f0880808d08c0486297f9,26954044854,27021153718,6601273906679,0xc701404820c897b7,0x6d02820c917b7,0xe7014040f90417f8,27008145335,0x15c0b0b060f9cf97f8,0x9281028048c91fb8,0xba702023607c050091ff9,0x1c1204f340917f8,0xcd00ebf002d804ee000d600a82705089cc0486317f9],
[8297780727,88896443895,0xe7a00281028066961de7,0x865001c8c0051d3031860529615f8,0x2502048203d97f8,0x9a1a04822a417f8,0xe720012943144100500c9fe8,0x10ce00392800a3e214319833b28200a17f9,0x68441edcf97f8,0x74300061a34028065cf9fe8,0x69a0051d003928012398a3162630051cf97f9,0x74b0009a8f03140f6050091ff9,0x1c1204f540917f8,0x2d80f7801020140e001ac02f04e1ccbb520486417f9,0x11f90000028048699fe8,0x48e00586001a700036802b6c00eb095028058091fe9,0x1d2c000028048719fe8,0x71000928008dc016c0834008650022d804c400ea003f0068420dcc205da70280480c9fe9,0x20e200724014af400050010e00246e00b600a402a18f001822a8005400b60131003a800fc01a1234250846a4ad026cbf40500917fa,0x6c1ea4003c610632c0917f9,0x2b177e000b81f81c4dd00ff9,0x48873b00120b72a0486697f9,0x27e00fc0e260486717d9,0x21bc0058600106007e9cb08c6e0480a97fa,0x66514056058091ff9,0x1c1204049fd97f8,0x1cc40017080110106670a0486817f9,0x9050b140a4058091ff9,0x1c1204ff40917f8,0x105000c86821080486897f9,921842055714808,0x2d00a0449169917f8],
[0xba400c4340c56e9140b17f9,0x6844229d097f8,0x36100175801a6021437170059d097f9,0x24331140585e1fe8,0xcad09828d5114058091ff9,0x1c12050140917f8,0x2ca80018b000c4800b3001901e188490524ce0486997f9,0x5de0013a0636a0585e17e9,0x2891c00b0401234011a802060150db800d200104b0087015600b30006050180c2ac92e61acbf60580917fa,0x1c12050440917f8,0x2d70011a008dc015c0007000710021802c1081086648ca0486b17f9,0x1c12050540917f8,0x2bf00048c00320c585080486b97f9,0x23700570031800290025804cc00e20113000c1a1108a0486c97f9,0x11b802b81088007b0012c026600710089806436284502e0480c9fe9,0x1c400e1801c57a00c48802370057004a01ed0028800ac008e00a660071001f802c1080b943c61126ab805c0917fa,0x6204447dd117f8,0x7ee003d3006302207038255d10ff9,0x1b680093c006a0641c6d5d18ff9,0xb44001d008209d20ff9,0x5c0f850ad88ff8,0x2b1000b03d0d0dd28ff9,0x178160e282f1d297f9,0xcf400904018c0118054376003e80096010202c401c4020200a35e8504b0b25ec5e0ffa,0x340578160e28049d297f9,0x1a2c184ee2f00917fa,0x2cbb000a0431455d30ff9,0x167f000a0431455d38ff9,0x9be800fc09d40ff9,0xe96001e0509d48ff9,0x4be000ae01bb001f400bd800e2011f00de4c20c1145c5e8ffa,0x5091a350f60480c9ff9],
[530337328044024,0x90102024066221fd8,0x3e48018439a35024064411ff9,0x1a5001c12051140917f8,0x46e00b603ba002c400be8026d001d802c2881086648ca0487117f9,0x26091a351140480c9ff9,0x1c12051240917f8,0xa3e000be0067c005380098168210ca29cc0487197f9,0x2465c071340917f8,0x21c12071380917f8,0x235005b0264801450035804f40391a34508a0487217f9,0x709683c08562e0480c9ff9,0x1c40026200235005b01d9005c05d000407a00c7f017e00d60003009010450ac1b018655b71461021df60480c97fa,0x38801db002cc000d0013200768052402d801d00a86fc009600330023804080bd006b00028023010c308898140c187042668d429bdc090ffb,0x15740088318c4a1e40997fa,0x56180061c09d50ff9,0xabe007c38672985f0ffa,0xc904ac80996f9,0x129001b10258c4c04c4017fa,0x24f0003ea000f8c009120891d58ff9,0x2ea00c130004b400d6851d60ff9,0x8d80086c0071600e0c09d68ff9,5031703315748856,0x85000a2800ca023c0dd70ff9,0x110648302c0685f9fc8,0xa1800d242c80585f97f9,0x11064830300685f9fc8,0x514005141860605f97f9,0x27e0012e506060685f97d9,0xcfe0021b0011e007ec01e900d4401a4b6381c0b985f8ffa,0x1c3c244a2200997fa,0xb1800dc120ad98ff8]],
[[0xdba0002c2002c670dd78ff9,0x135a000a2801c684dd80ff9,0x124007460061c09d88ff9,0x38887cc0506017f9,0x15090e8328a0546017f9,0xffc00e3c09d90ff9,0xff400e141860606017f9,0x7fa0071e040686017d9,0xc0302800428026c039e00fff1b042118600ffa,0x88318c4a2400997fa,0x25ac000ba800a509d98ff9,0x6f500104400a509da0ff9,0x244801da80150309da8ff9,0x1590003052860586097f9,0xac801464ddb0ff9,0x2ae00341c52880606097f9,0xab800d070e280686097d9,0x8c400afc00c9800af400149003ff214465c608ffa,0x24028244a2600997fa,0x15dc00185000b0508ddb8ff9,0x3ef00210801c508ddc0ff9,0x1728005ac00e3c09dc8ff9,0x3505860506117f9,0xdd8078a00e141860586117f9,0x7860071209dd0ff9,0x28126060611779,0x1c100c300f9803fb1c14084919c610ffa,0x170326f540997b8,0x60f0015415ca04c6417b9,0x12010296d00b1be7,0x253e001640302028059de1fe8,0x253e0017c023e6028058099fe9],
[0x350564028060099fe9,0x319cc00432001fc00e3c007440070a6fe1ab4e0500997fa,0x2d128f000e832863280997f9,0x4461180027c2863300997f9,0x2c1470007819209dd8ff9,0x69038018e2604c6717d9,0x499c00361f4878f4e04c0a97fa,0x95e80078440adde17f8,0x11018102b02c04c0d27c8,0x38865044056058099ff9,0x95f8005c39acc04c6817f9,0x90e3861adde17f8,0x1d18017010b140d6058099ff9,0x317800e6c146a04c6917f9,0x4428405aba96f8,0x461c5aab2c0b17f9,0x601f200033e000e0c806056d00b17f8,0x12061302c061de1fe8,0x6670008bc0101800c109e21ca6d0a059de17f9,0xeb4004e1732502c060099fe9,0x48648302c04c741fc8,0x7110006720042091c942402c04c0d1fc9,0x1433680085c00418015f002f00120130770110a301b50001802414085155ab10da5df80580997fa,0x179000b068605c6197e9,0x1790011048202e04c0d1fc9,0x5c2f9001f403638d8528a05c0997fa,0x18c60007058604c6e17f9,0xc96002c718604c6e97f9,0x9048203004c741fc8,0x90a0035900050310b0a3503004c0d1fc9,0x9098024180161002d001a0150730110a101b90000803830a3870e5420411252f60600997fa,0xa3800220623c0dde8ff9],
[0x7fe006e0e3c09df0ff9,7004314503452409,0x19bc00634800a31c51e00ef9,0x98e2630de016f9,0x159002d0387120de00ff9,0x3c300360e3c09e08ff9,0x337800516002ca0066001c0360e2034c06e400ee0023fc4246c2b24ec618ffa,0x8c90404de016f9,0x18812c66e30c0997fa,0xc8d0003ee00221b0f192da8ff8,0xe02404f08c017f8,0xf2008f4800de16070511e10ff9,0xc8b002448651e18ff9,0x4ea801a0c0de20ff9,0x4168003c064de28ff9,0xcde002130028f00082014300dc8024c019ee3c24155c620ffa,0x466001090e5060604c7417d9,0x16200481c284804c7517d9,0x19bc00291001610031001201909f012e037a0007007060b0661c39030a6ee04c0d17da,0x18801dd002c4000f0034a00ef001180082004100e6804a806200240320de022146037201c201271511111c60433042e6e429bdc098ffb,0x238a001d0a183056050f19bf8,0x238e001f06183056050841fe8,0x311905618620e0ac0a1ff9,0x2532001c41689f97f8,55513079,79323726878712,0x63d000e87820280609f9fe8,0x115400034002270005a624094cc0509f97f9,26921146295,26988255159,0x6c31c80f8a017f8,21622233015],
[0x1301056060c91fa7,0x4ee0000d002c8a2c30a0acc917b8,26921211831,0x1a60840f8a117f8,0x94a30560f80c1fe8,0x2de80010e001d38004ee0013c02fc032f2c09ca9520ac1f17f9,0x8f480018e63056051269bf8,0x5e15022842360ac0a1ff9,55545847,8193994486159352,98257868663,2765499670375,0x1e1028500109f78,39865561389048,6201541977708536,0xff600781028064a01fe8,0x1fb0007ac0054600fae0038de633062cc050a017f9,0x23fe001d0e63056052db1bf8,0x69f0015818e64056051e31ff9,0xd1c60ad0817f8,0x1001e330561680c9fe8,0x27f001c21b0022700134800f8a00643a808aee0ac2d17f9,0xc36dc0a17f8,0xb19054040aedc17f8,0x58e620560507c9fe8,0xe873182b02806010a768,0x51fd0e63056050109ff9,39865561454584,0x6c34630561ec0c1fe8,0x297005dd8002810000e80346ac44cc0ac3d97f9,0x2432001306283056051b39bf8,0xe62056052761f78],
[0xc2283056052681f78,0x7a86a8426e0ac0a1ff9,6201542111926264,0x6c00281028064a11fe8,0x5fc00891000f5c0000c0110e6a184e412d0050a117f9,0x5bc024aa001ec040aedc97f8,0x2452001d0dc3056052dd1bf8,0x2456001d0dc3056052dd9fe8,0x23803d1e1cdc5056051e39ff9,0x125d000c302056281ec9df8,0x15b80020420562819c1df8,431286348716024,0x2201056281519fd8,0x2b001e330562800c9fe8,0xb7807c18b00224c00163001320026022a01f88231e084af60ac5017f9,0x2a04c76f00a17f8,2339403470327,8796233394984952,0x117a000bd0dc3056051e41ff9,506148877375480,0x68360c60aedf97f8,0x31630575580a1bf8,0x3163056052ab9df8,0x3163056052ac1ef8,0x1a0e63056052ac9fe8,0xfde1c91660560513f9ff9,0x3163056050111ff9,0x3e803837000a17f8,668643449935351,9302146182846456,0xab031c55056051401ff9,0x4460026f001f040050b0c382a1c4aa80560500c1fe9],
[0x2b5003cd0001d0033c2838020e7770560500c9fe9,0x4460077a000d40081003cd000fc010808b00c508c2ccc4c4a13927a4c3dab560ac0a17fa,0xd0201ee117b7,98919520183,8657030820728760,0x8f00173801306001140c491e48ff9,0x5910025ee00345c00560b0de50ff9,91702531063,91769640439,91836749559,65207572455,0xfe3086f2d3f97f8,0x3a0c4f2c1117f8,0x198384f2d4017f8,0x1950009d72003718003300fc610de58ff9,0x4fe0044180062e00621091e60ff9,0x24fe0004ac80606297e9,0x44c0328a6b0003160008c0094022394395b9c628ffa,0x59e00006450797b7,26995038135,0x68800166800610b4040f90797f8,0xb4648101f37,0x1e2207c168101f78,35580876727,0x96d00000b416cc91fa7,0x9058006810b4058c91fa7,0xacf00121384000dc012e470c308168c917b8,26928027575,0x4a8c40f90917f8,4797471023538087,0x1296000c98107c1682d9fe8,0x3978002d9000a312307c1680b1fe8],
[0x5ec01cd80161cf80120ee40014801b802225dc0a121262500f82d17f9,98998753207,0x184070c60fae197f8,4961959892556727,0x3ca307d41c0a1bf8,2835228467095,0x1301029424c91fa7,0x96108830285fcc91fb8,0xdca307c052841fd8,0xdca307c052849fe8,0xb758734a607c050bf9ff9,99065862071,0x4e121a060fae217f8,4787922516122551,0x52207c052e29bf8,0x917800681029718c91fa7,0x912800252282028648c01fb8,0x245600092207c052e31fe8,0x911800258e0b12507c050c01ff9,77121230775,77121263543,0x7f014040fa3e97f8,0x13010283d8c91fa7,5632825047918375,0xf82fc282028648101fb8,0x328a307c0507b1fe8,0xc98145203e028060102768,0x7c3731ca407c050101ff9,113964029879,114031138743,0x1c4082060864ae397b8,101884434359],
[114098247607,0x1dac00648246d0864a9017b8,27004770231,27004835767,0x928800681140058c91fa7,0x1301140060c91fa7,0x1a6a000702e8025403ec138c30a280c917b8,99334297527,4787922784558007,0x681029728c91fa7,0x72282028a1cc91fb8,77456807863,0x13010283f0c91fa7,0xfc282028088c91fb8,0x12610000028648691fa7,0x35ae001c74002e0516182028058c91fa8,2775764082599,0x2b540059a4006f03438d808183028060c91fa8,0x4e8004760009f40018c022c03302c18114cc264bb0304050c917b9,0xb0b046459c17b7,0x615853860f99c17f8,26937726903,0x50d3840f99d17f8,0x248600070d8312407c2800b1fe8,0xe14a307c2800c1fe8,0x64600303800240b6009b00d0b8c24334c0f85017f9,0x1c0e121a060fae417f8,0x1c12207c052e49bf8,0xe02812307c052e51fe8,0x10f90b12507c051439ff9,77456775095,0x1c3f014040fa4117f8],
[0x4828a307c0507e1fe8,0x143341ca407c050111ff9,0x494c001212242307c050691fe8,0x48680102802ef4003b1001730084021c59973607c0500b1fe9,0x121782307c0506e9fe8,0xdee0068776004ec4002ec03680f0e48e448273707c0500c1fe9,0x6f700343bd0003a000be000dc015809100dc05020c3c3842259010adf20f80a17fa,65352668151,0x3d050572de697f8,0x1d0504f36e617f8,0x3c1205735e697f8,0x3a0c4f341117f8,0x17040063e001834001aa01f1068084911de68ff9,0x56600a9f00378400560b0de70ff9,86401061879,86468171735,86535280615,0x1ee1c3065fde797f8,0xb80204f3cc017f8,0x4e0c4f3c1017f8,0x17600409e001ef000e9800e483860de78ff9,0x1bb00fe7001f0801a0209e80ff9,0x48200297000998001c0219ca0646317e9,0x1dc0313de8014b801f080063006d8079dc7c08b98630ffa,0xb033c10795f7,0xe2c00210b40483ea397f8,75224470675494904,75224497814509560,0x225c0009d800c406094028059079de8,0x5700f170002760005812028065079fe8,0xd600ae013f8023f0039d002bf00030800d2c0f93b01280510797f9,88963520247],
[0x14844260529697f8,0xb7c003e68000e0313028059081fe8,0x2e3000e08001040046b0009200c73828c1080510817f9,0x3a010b41ec101f78,22273382225912,0x7bc003a010b41ec2d9fe8,0x2562001b0b0430b41ec0b1fe8,0x6540010d001609c2001da0063c408588a1683d97f9,0x3a0c484aa417f8,0x53c00281028065091fe8,0x44d800c92000ac028804ce0e81860510917f9,83843828455416,0xe120b4281ee1f78,0x2a600320b42800c9fe8,0x14480185400a020009a00e60c68af01685017f9,0x3010b416ea41fe8,0x1f08012f4000710013c05190d804718c60b40502d9fe9,0x698011c80099400038800760318e230713b80b40500b1fe9,0xaa100090a9c018f4009d00a60241182042da70b40500c9fe9,0x1a2004720077c00dd80120110025c014340031013a00b80f40233117882c246df561680a17fa,0x2a7001bac00695800ac1251e88ff9,0x3840166400d0b00028298de90ff9,0x3a8012a900086c002c3860de98ff9,0x8a802218000460068b0dea0ff9,0x12cb000a4120a4058639fe8,0x707001a10071180088e480586397e9,0x1c1c0068401d20131f6c0009200eb20890e699c638ffa,7894867354949624,0xe62a0e1ec0a1bf8,0xe620f6052af9ef8,0xe620f6052841fd8,0xdc20f6052b09fd8],
[0xe620f6052849fe8,0xfea1a640f6050bf9ff9,0x502041eee217f8,0x410f6052e29bf8,0x25ba000410f6052e31fe8,0x25ae001d45428440f6050c01ff9,7894776657385464,0xa20f60507b1fe8,0x2705187b028060102768,0x38398e630f6050101ff9,0x30c461ed9c17f8,0xc441ed9d17f8,0xb41c20f6281519fd8,0x12eb000d858d40f62800b1fe8,0x2e0530f62800c1fe8,0xef7001282d980010358053403e88219cc1ec5017f9,6817255273207800,0xdc20f75880a1bf8,0xdc20f6052b19ef8,0xdc20f6052b21f78,0xdc20f6052b29f78,0xdc20f6052b31fe8,0xfea15c40f6051511ff9,0x502041eee417f8,0x410f6052e49bf8,0x410f6052e51fe8,0x1d45428440f6051439ff9,0x30c461eedc97f8,0xf15150dc40f6051519ff9,0x1f83841eedf97f8,0x78087baac0500c2367,0x1dc20f75580a1bf8],
[0x78087b02955c0c2567,0x1dc20f6052ab9df8,0xdc20f6052b39df8,0xf8087b0295600c2667,0x1dc20f6052ac1ef8,0x2c945878187b0280613fa768,0xdc20f6052ac9fe8,0x255ea15c40f60513f9ff9,7894776657549304,0xa20f60507e1fe8,0x19a0e630f6050111ff9,0x30c461eee097f8,0xf078107b028061402768,0x35150dc40f6051401ff9,0x4ca4000106820f6050691fe8,0x356e001f7c001e00c1cc1140f60500b1fe9,0x3613020f60506e9fe8,0xab500168900132028f0e122047350f60500c1fe9,0x156e0024f00421000ee014a0154054084a7089c6c9795aae1ec0a17fa,0x880204773dea97f8,0x1d0505741ea97f8,0x1d0504f56e897f8,6565335031,0x1682b14af541097f8,65889605559,334454816970680,65889638263,65889671031,0x7d0505749ea97f8,0x110a0848f56e997f8,0x1c640c48f55e417f8,0xa03559ea93f7],
[6565466103,0x78c555dea95f7,0x78c4f56ac16f7,0xa02f56ac97e7,0x7ca0d0f14af553f97f8,0x3a0c4f541117f8,0x982c1684af554017f8,0x1548037cc002ce0086a001b80be02c4034b74f668422c4a5ea8ff9,0x1656000141deb13f7,0x16560000f5a8417d7,0x16520000f5a8497e7,0x1646001ee1c306f58bf97f8,0x164e001101404f58c017f8,0x5918004e0c4f581017f8,0x15e01c263001d080040c007540209eb0ff9,0x43c02fc8010e5001215030deb8ff9,0x3be01e580068800b70dec0ff9,0x23d003c50002a01d30035806883c0043006e02f80d700e7db698640ffa,0x3d00a2c00e2843140051b39bf8,1398117879,0x13404226e051ec9df8,0xa2401e63140052761f78,0x7038283140052681f78,0x281002e50a8326e2800a1ff9,0x14210a00297500b24e7,0x24d006842140052ea1ef8,0x1a5200127802842140052ea9f78,0xe62140052eb1f78,0x12471418a0028059eca5e8,0x1a52000158002e00cf104e5846140051ec9ff9,99012580855,0xa0e0519c19f7],
[2835242294743,2835309403623,0x1e410285fd9c1df8,0x80120c2028ce0101df8,0x50c46ce2a417f8,99348125175,2848194304503,2848261414375,0xe41028a1d9c1df8,0x113a0008fc002e78232470280599c1de8,0x4e3c0028420280599c1fe8,0x1480796800241000981030280659c1fe8,0x10d0084a014780227c0038d00021274001c05a031032798e51c262d00519c17f9,2849133828599,2849200938471,0xa0230028ce1ed1df8,0x1c1410a00280599c25e8,0x19b60003802b0012c0310e28441400519c1ff9,0x1803000b1a4282e417f8,0x1fa0052842140052eb9bf8,0x1fe0052842140052ec1fe8,0x53600de842140051ed1ff9,0x43c00d8182140050c51fe8,0x9e0881041853122800a1ff9,0x14086428052ec97f8,0x5560023f400220b020280599c9fe8,0x23f400220b020280619c9fe8,0x2af00072a00107001900901b01cc2c1210a0519c97f9,0x180821841400519c9ff9,0x4102805aed1de7,79303667423224,9034128824312],
[0xa81204282ee17f8,0x641410a00297740b21e7,0x6842140052ee9bf8,0x2842140052ef1fd8,0x132210a0028059eda5e8,0x2842140052ef9fe8,0x28f006bc42c44140051ed9ff9,0x262001a0e63140051d11bf8,0x28082844140052f01df8,0x7038283140052961df8,1398151031,0x4f062410051ee1f78,0x355404382844102800a1ff9,0x7310a0028061ee2768,0xfc02b8e63140051ee1ff9,0x198384ceaa417f8,0x50e001c2820280659d1fe8,0x450800c660027c00480300901a83198318c0519d17f9,2849804983159,0x8c201028ce9ee9f78,0x4e070e641400519d1ff9,0x28e006e62140052f09bf8,0x590029a0e63140051ee9ff9,0x3cc77880a17f8,506051618248696,0xdc110a2970c5017f8,0x6e011e64a0e2800a1bf8,0xe62140052af9ef8,0x72011314140052841fd8,0x72011314140052849fe8,0x2b07f50a9986140050bf9ff9,0x4fbc00082052f217f8],
[0x183800837940a17f8,0x32030c6282e217f8,0x3414e4140052e29bf8,0x2842140052f31fd8,0x13f7000341c54140052e31fe8,0x68e80059e00fce070e64140050c01ff9,0xe03163140050101ff9,2850181357415,30925156227064,0xc37a00a17f8,0x1c1204282dc17f8,0xe621400507c9fe8,0x67310a002806010a768,0x1fe62140050109ff9,0x4518011b8009ac00137000607d001b01e3005a01f02c6861c2a011cedaaa1400500b1fe9,0x2284004ef003c600b40b201c3e18408c4aa81400500c1fe9,0x28a000e840098164033c02080fa01600412042da71400500c9fe9,0x1460046a00786000540099003a1002603600fc06780ae05600c0440a7861112a28b64239e78c0408dab542800a17fa,0x64c018220003ec00621091ef0ff9,0xf2005e600034c00c609ef8ff9,0x27806e700117a006a0b0df00ff9,0x15a0178800851801a3860df08ff9,0x14f200064c00c9084a0586497e9,0x193002502c60606497e9,0x508001db000190186b003f840c54498648ffa,0xb34007863280506617e9,0xa11860506697e9,0xb2c007704884c0500a97ea,2755975551975,0x468142028058f19be8,0x4fbc002842028058f19fe8,0x142002dcc00368e3028148359fe8],
[0xa0c8007601028058f31fe8,0xa0c800642843028148571fe8,0x1403c80062ebc009c200318073a00092008b01f78189832a422a0281480b1fe9,0x9042028229269be7,0x308800e7e006f018314028059269be8,0x141d0004c042028059271fe8,0x410281ad691be7,0x4f4000b6c00698d1a50281ac451fe8,0x264008c4004ea0033a01cd40065661b99b80281ac0b1fe9,0x132000f7800adc00eb8017f8016403701a3336c0506917e9,0x1b700082193028059691be8,0x508400046820280596a9fe8,72341827083279335,0x9d800173800d0423028228571fe8,0x4530013a40024a001b70035584d5580282280b1fe9,0x132c0014b80061802a15ca0506997e9,0x611001d340027415418c5028059b39be8,0x5044002842028059b39fe8,0x14270004c042028059b41fe8,0xa03d801ce004b0013c800590041006a401d8803b60091b9e0918949690282b80b1fe9,0x501ec00e6c8012c00c7801103ba000c8014e00e25801b803072014202cc00436a0062030819201d008b41fc011229649edb4e0500b17ea,0x1e900160801d1002ff002c80960246664a0506e97e9,0x1429000bc162860521c17e8,0x114a000e0c00d840506f97e9,0x1380e101568029b2004b003be0076c010c8015200a258020800ec027c06c40754002201fc0182b02c81f4011d0591b254e0500c17ea,0x18900536001a600882dca0507197e9,0x6d60071600283040507297e9,0x734c047600cc1ca004b003be007740019002b4004be807076013a034c01f400ec01880df01b40c83e804c1c615b500500c97ea,0x1480e69808ec019819b6004b0031600540ee8003201c500d201124010c0076013e02c40040fa007600c405f0004004158030c873107c2081cd3026edbdc0a0ffb,0x3f02e80390134c0077a005298011c803e20035000f00fb802408918dc650ffa,0x4c18812a002d005df800130096600724017b4006a00bc01ae0088143be0658ffa,0x2b98006204447df117f8],
[0x1374003b00613580125c00a4a00721e1451f10ff9,0x1f500607800f5200120e09f18ff9,0x8ad8007bc00e4c00240e09f20ff9,0x1408800fb801be004681451f28ff9,0x34c04e300181007408803a004d006088017600c480104025c0587001780be06b400f0792011c11dc660ffa,0x12bc00d7c00e64000823063306697f9,0x4a9000a8c00320f3c446c3300a97fa,0x1692000c71600eee005e0230df30ff9,0x4e0c4f9c1017f8,0xfea004bc03853c00a76007c6428611f38ff9,0xf1c0156a003a300320609f40ff9,0x325c00354000780160609f48ff9,0x36c00aa0075400f48002201bf00c41f40fe004c030e4027402144006e00bc05f035a00d81765129e0668ffa,0x8a7c002e0114a528ac3340a97fa,0x448018760007e014100719808811a0318803100ae8104c0145808a8dc670ffa,0x6880d59803640680e400ea8024400b20008801660048202201d001f804c805f804a8035006202f81ab000c1d153b28a9be40a8ffb,0x242205605a4a1fb8,0x2e8305605a459fb8,0x2b02001502283056058841fe8,0x1e61618420e0ac0b1ff9,0x2caa001cc41ac9f97f8,56004599,369594761910264,0x4c04202c0609f9fe8,0x522007205701c4ea8002f45c18cca0589f97f9,0x2b48001e8024fa001a2a040aef497f8,0x2b2200150d8305605a781df8,0x1c6205605af51f78,0xd8205605af59f78,0x2b2e00150d8305605af61fe8,0x2eec003f50d83056058a19ff9,0x150d8305605af69df8],
[0x22010561480d9ef8,0x95c00565000a750d830560580d9ff9,0xcdcc8148a017f8,0x1e1cb060acf317f8,0x2da20009814630561480c1fe8,0x6110dc40561480d1fe8,0xad2005302b9001f280132e00241002f78441261115560ac2917f9,0xad580031c63056059079df8,0x5e15022842360ac0b1ff9,56037367,77067402849327096,102485727095,3040377577319,0x1e102c500109f78,0x844228a017f8,56070135,369594864310264,0x162001a3000d03281ce120074d00046a98ac0c2cc058a017f9,0xae0800541c6305605af71df8,0xff30015831c64056059e31ff9,0x3fdc0031c630560580f9ff9,5009790198028280,506057417857016,0x27d002426b0026700123800f18072f000307e046e66500ac3597f9,0xc37bc0b17f8,0x1c620577c00b1bf8,0x1082a040aef897f8,0x1c620577c80b1df8,0x1c6205605af99fe8,0xfd41c63056059f51ff9,475366175741944,0x1c03040aefa97f8],
[0xd8205605afb1df8,0x5a9000f50d83056059f59ff9,0xc36dc0b17f8,0x8838fc040aefb97f8,0x441c620560587c9fe8,0x2a0e3182b02c06010a768,0x587d41c63056058109ff9,0x2bd6001a423056058961fe8,0x6930e842560ac0b1ff9,56102903,369594896127992,93665757990262776,56135671,0x1a0846506b417f8,105706985399,3102251982263,0x1a102c42ca09fb8,0x404202c060a09fe8,0x404202c068a09fe8,0xaf4000580e40e0fc8004856fcf1301044c058a097f9,0xb0280054242305605afc1fe8,0xe14005e1a424056058a21ff9,0x389001a423056059b59ff9,0xb458000844228a117f8,0xa08460ad6a97f8,0xb468004e0a30562280c1fe8,0x51230562280d1fe8,0x13d80343158005d900085c004c1f20c13ced00ac4517f9,0x48453c80b17f8,0x2f2800082230572bc0b1bf8,0x68360460aefc97f8,0x1824230572c00b1df8],
[0x2f48000822305605afd1f78,0x242205605afd9f78,0x2f58000822305605a589fd8,0x39c205605afe1fd8,0x2f68000822305605a591fe8,0xbb6001ffa8082240560588e9ff9,0x37078460aefe97f8,0x11c2305605aff1df8,0xf46d840560588f1ff9,0x2f9800082230560588f9ff9,4638498297848,0x24220578000b1bf8,0xf074040af0097f8,0x24220578080b1df8,0x242205605b019fe8,0xfd42423056059f61ff9,0xc38100b17f8,0x38fc040af0297f8,0xa858982b02c061f6a768,0x1c6205605b031fe8,0x7d41c63056059f69ff9,4639035168760,0xf074040af0417f8,0x242205605b049df8,0x7ef003d42423056059f71ff9,0x2c9e00130e830560599c1df8,0x1c6205605a761f78,0xc228305605a681f78,0x7a86a8426e0ac0b1ff9,56168439,369594998527992,0xcbe000a6802106204644003c124418c4a058a117f9],
[0x2c6014d009a58001c16040af0517f8,0xb2f8005439c305605b059df8,0x39c205605b061fb8,0x39c205605b069fb8,0xb328005439c305605add9fe8,0xadc00fd439c3056059e39ff9,0x22010562b9f79fd8,0x5439c305605b071fe8,0x1e0902b02c069f7a7c8,0x56e0053d439c3056059f79ff9,0x185c3860adb417f8,0xb18056009a0008ec007940155006b40297006e026c78463c1095560ac5717f9,0x738583c0b17f8,0x39c20578400b1bf8,0x1d83840af0897f8,0x39c20578480b1df8,0x39c205605b099f78,0x39c205605b0a1f78,0x39c205605b0a9fb8,0x39c205605b0b1fb8,0x39c205605b0b9fe8,0xffd439c3056059f81ff9,0x1282a040af0c17f8,0xd8205605b0c9df8,0x324800710d83056058a29ff9,0xf816040af0d17f8,0x39c205605b0d9fe8,0x2c1ce182b02c069e427c8,0x3f439c3056059e41ff9,998730086684664,0x1d0e102baac0580d23c7,0x260930575580b1bf8],
[0xf80a0c60af0e17f8,0xb102baae0580d25c7,0x2616305755c0b1df8,0xb102b02d5600d26c7,0x2616305605aac1ef8,0x39c205605b0e9ef8,0x18082b02d8780d2787,0x2609305605b0f1fb8,0x39c205605b0f9fb8,0x196d9e0e3202b02c0693fa7c8,0x3c1c6305605aac9fe8,0x54abea061640560593f9ff9,0xa858982b02c0681127c8,0x26163056058111ff9,0x8c010c60af1017f8,0x105305605b109fe8,0x370cb14056059401ff9,61815451752440,0x39c205788c0b1bf8,0xf816040af1217f8,0x39c20578940b1df8,0x39c205605b131fe8,0xfd439c3056059f89ff9,4620714448888,0x2a80f074040af1397f8,0x550242205605a499df8,0xf3e004f03d42423056058859ff9,0x73858a00b17f8,0x6607040af1497f8,0x39c205605b151fe8,0xf018102b02c069f927c8,0x7d439c3056059f91ff9],
[0x4e20023b001e500e5600580c12044c0e8150e62a70560580c1fe9,0x83c683056058741fe8,0x23b001e50043c001835e000d000ec00d8043a03868c50d71e1258980560580d1fe9,0xb0c002263003120067d20030401ceb806d809b019e039af002b018c005400ca66230ba846270ac51b46109a844a313c2d4232b30f6df40ac0b17fa,0x4c2c64615f98ef9,0x360da8615fa0f79,0x162001c460dfa0ff9,0x741432a15fa8fb9,0x409000c460dfa8ff9,0x642c64615fb0fd9,0x13d3000fece69be8678ffa,0x433800a0c19e2001903828308059fb97f9,0x1c03040d4f193f8,0xb0b04148b417f8,0x1e1cb067981a97f8,0xc0c2e1c40a40681a9fe8,0x77e40038f007da0a141c163101481a97f9,0x16fe002e805580085007e800138a80458a058b417f9,6254308705474552,0x4568000404202c5a40d1fe8,0x54f0000a401438227800d20080458a058b497f9,0xf4300021419a80122e14708059fc17f9,0x6607040d5b393f8,0x185c386da01a97f8,0x1f3800f1d001cd8009b060d056361102b81a97f9,0x1e3a00379005825286246c63802c0681a9fe9,0x13c0078e800de400219dd8c01076ff80581a97fa,8176311592785912,0x14b20003f003ae0009c8005991399fc8ff9,80496890871,80564000247,68356184023],
[68356216807,0x78b0184fe88e97f8,0x3a0b04fe88f17f8,0x62044fe88f97f8,0x532000308023f801b7c00f2838255fd0ff9,91704103927,91771213303,91838322423,68428797927,0x1ff8284fed3f97f8,0x3a0c4fec1117f8,0x198384fed4017f8,0x15ce00025004f60054200e70521115fd8ff9,5352765961639928,0x18b4001038014a007e80122ccd9fe0ff9,0x669000dd01be4008854a0606817e9,0x1e7001fb801f3800d10075c037404b80dd01b7002501840694002042fb1298680ffa,0x13d7000158078c41acf197f8,0xa83d0c83f4f197f8,0x2a05853882b8f197f8,0x6d00afd80030b81202c060f19fe8,0x2c0a001f00c090302c068f19fe8,0x4da0111e0046a0028780076402241fb4220d0488c058f197f9,0x3c0c414b1597f8,0x1c620a43bc0b1df8,0x1c620a405b161fb8,0x1c620a4058789fd8,0x1c620a4058791fe8,0x1ff4146640a40580f1ff9,0x1f0140414a3d97f8,0x64010a41ac0f9f78,0x14620a40587a1fe8],
[0x120a3185202c0600fa768,0x7b1c630a40580f9ff9,0x583846228f217f8,0x2dc800294000f7001440ca82ca058f217f9,0xc1c006be8002600c041492697f8,0x62065830a41ac0d9ef8,0x1706b061acf297f8,0x20400184bc00578012023c006d809aa0009402c53a18308f070a84541483597f9,0x1706b067947e97f8,0x404202c060f29fe8,0xe3a002e8a86058f297f9,0x338461496a17f8,0x61230a42280c1fe8,0x49580018cc316ca1484517f9,9077848430254072,0x6c1f0105202c061f6a768,0x14620a405b031fe8,0x7f87c1c640a4059f69ff9,0xe270006b4001c0570024044106058f317f9,0x420e5388149b397f8,0x16fc0030a80009400106978a1485717f9,0x145c38614a4217f8,0x582930a40587e1fe8,0xf8f0b140a4058111ff9,0x3213020a40586e1fe8,0x4280161bd801d8023c006e809500f1c00a10120c6c6270385871f3290a40580c1fe9,0x28ae000aa00d0160496960a40580d1fe9,0x4180161fa800a602930019e002500b900dd012a036403902020046008f0009015401a0a3113625659c08783949541480b17fa,68574352887,0x350d058b5fe97f8,94804634041260024,94804633990436856],
[0x3c12058bdfe97f8,0x3a0c4ff41117f8,0xb820035b8005d70006d80303007e44868104519fe8ff9,0x3578017ba003c38251ff0ff9,0x3f080018f000e8110dff8ff9,0x3cdc00167000820a000ff9,0x3ca8002209040686897e9,0xe88014c035f0009c02dc02e201b601c80118030b007dc5c3b998688ffa,0xb033bd2693f7,0xdbd000a600c054c52697f8,106319746039,3130043832823,19006131379127,0x2e20173400f90102c935b59bf8,0xe7b00009356913f7,0x279e00093005a08462292697f8,0x28e8c94c92697f8,0x44004e8012f8017f00054800d5e006680340902c0458b03a80592697f9,0x7e0b041aef497f8,0x14620d605af69df8,0xe2a000d83bc0cd840d60580d9ff9,90841847543,0x14844275240b17f8,0x29cc007e80761000840e501e37828c1080592717f9,0x1a37008461af1817f8,0xd1ca30d605b189df8,0x341808230d6229b59fb8,0x4fc0038fa4230d6059b59ff9,0x704c62b92797f8,0x404202c069279fe8,0x30b8017bc00ec443e044a0592797f9,0xd6b480f9b77],
[0x13cf00048800c2239481ad6917f8,0x88020461ad6997f8,0x30c2c630d62280f9f78,0x36030c62292817f8,0x741a1240d62280d1fe8,0x1be4005dc01e2b2004d4002835e000a60012600488038a7d870106296c22945a1ac4517f9,0x6250002de00242295e1ac0b1bf8,7885979503073272,0x24220d72c00b1df8,0x6250002e60024220d605a589fd8,0x6250002e60024220d605a591fe8,0x312800169001fe4063240d60588e9ff9,0xf80a041aefe97f8,0x14620d605aff1df8,0x5cc00630d830d60588f1ff9,7885979504941048,0xa20d605a5b1df8,0x3ce80061824230d60588f9ff9,0x36030c69429917f8,0x10c801a3803c571860592817f9,0xb04c61adb517f8,0x86a000a780088461c54a1ac5717f9,0x90e3861af0c17f8,0xb1d020d605b0c9df8,0x1ea40031010b140d6058a29ff9,7885979504580600,0xa20d605a499df8,0xc3800d208824240d6058859ff9,0x29a003910f0b9b60d60580d1fe9,0x970026f002da00d1ee800d5007cc032404980644004e02c81b9003e05080541b13729b25b608060e3b25541ac0b17fa,56233975,4615982584823],
[68825912823,68825946071,68825978855,0x1f486470048e97f8,0x3a0b050048f17f8,0x620450048f97f8,0x2a70011ce001f3400f2838256008ff9,0x440e0180f198ff8,0x1e600821000d1820e010ff9,0x9b20010b8001868652018ff9,0x1f88003de003a024e020ff9,0x18be00189860686917e9,0x25c001e100163801bd0064200ff01b9007d802fb872a298690ffa,76997530615,3040055204839,6195796476142439,0xbee003a0f30102cb480f9bf8,0x5368483f56917f8,0x310400241800a82e042b96917f8,61808495367159,0x483002a82e055a16917f8,3072116792295,0x7080aec8000080a4481202c061691fe8,0x283c00110489000481202c069691fe8,0x1c600236000514002da006080340840841a5fe05a80596917f9,0x8802046b4c7e97f8,0x4c04202c061699fe8,0x1d7c00a8620e8a860596997f9,0x1e0081cc622a3d97f8,0xf1ca31140587a1fe8,0x78e85188a02c0600fa768,0x74123b1c631140580f9ff9],
[0xb72003960163400860241a09102ca0596a17f9,0x3c0c422afb97f8,0xa21140587c9fe8,0x1a0f8108a02c06010a768,0x1c30341c64114058109ff9,0x1d838422b0517f8,0x56031c31142b9f79fd8,0x62211405b071fe8,0x3a078108a02c069f7a7c8,0xfa41b9c4114059f79ff9,94333310935,0x4f02c275f40b17f8,0x4bd0006ae006e402d806700d20633880596a97f9,0x2796001430030c46229b397f8,0x740e386229b497f8,0x24011142b9b59fb8,0xd8041241142b80c1fe8,0x434000e08b009ec005034c004f802160090e7e9c66404532d42285717f9,0x3c6b0622b0d17f8,0x121f0211405b0d9fe8,0x90f8108a02c069e427c8,0x1ec0c39c4114059e41ff9,0x780d561140580c2367,0x780d561140580d23c7,0xf9c2aac2280b1bf8,0x1d838422b0e17f8,0x78088aaae0580c2567,0x78088aaae0580d25c7,0xf9c211555c0b1df8,0xf8088a02d5600c2667,0xf8088a02d5600d26c7,0xf9c211405aac1ef8],
[0x4d8305878188a02c0613fa768,0x4d8305878188a02c0693fa7c8,0x39c211405aac9fe8,0x1dbef073441140593f9ff9,0x3c0c422a4217f8,0xa21140587e1fe8,0x381988a02c0681127c8,0x3bc1c63114058111ff9,0x4c020422b1017f8,0x62211405b109fe8,0x3a078108a02c061402768,0x38439c3114059401ff9,0x2f00878231140586e1fe8,0x7033114058701fe8,0x1be40040c00140f8c0057800a0d58002c800b68019c055008465808285a60ce173271140580c1fe9,0x2d02114058741fe8,0x740f02114058759fe8,0x10f000280d3001506cc00a402de00d5013806122c30c778112b271140580d1fe9,0x6f700187007c6002c400506a40136039406cc00a4057037e016c06501882706248ccc2682136a60a08edd542280b17fa,56266743,61801794540535,69099820535,69099853559,69099886567,0x7fc6870153f97f8,0x3a0c50141117f8,0x1983850154017f8,0x1548021ea00009c00e70521116028ff9,0x1b60118a00058110e030ff9,0x4680685800b1b0252038ff9,0x58c85c0f1a0ff8,0x23a00295002c670e040ff9],
[0x1bdc0061c01f18002a800d38036600560093006640358848e1298698ffa,0x983963894c9b397f8,0x1af01dea00311800464009900bfc01b30122a0383a81482081870e12c059b397f9,0x6fb8003a20031006c04201c8044106059b417f9,0x740e386da69917f8,0x83400e6400282d057186059b497f9,7886078914009080,0x2422c6c2b80b1df8,0x242215c05b1b9ef8,0x242215c05b1c1f78,0x242215c05b1c9fe8,0x1fb40942415c05a049ff9,0x2c12042bb1817f8,0x62215c05b189df8,0x3d2003b07a42315c059b59ff9,0x404202c061b51fe8,0x4cc028b005903c744422044a059b517f9,0xa1cb062bb1917f8,0x4c1c2315c05a5b1df8,0xcc44242415c0588f9ff9,7072345395304440,0x62215c05b049df8,0x138800f8f8242415c059f71ff9,0x3ce003f00870b9b615c0580c1fe9,0xfa00578032400c280144036500084034c030c04e80b10090d1801680be072400c401b0390030390460aa65b740c1e3589542b80b17fa,0x3014058ea0517f8,69446866919,0x350d058ee0517f8,94804634914134008,94804634890508280,0x620450288f97f8,0xc9802050022bc0036a000b3000bc9e2208c31a050ff9]],
[[0x240242c000820a058ff9,0x10203534004a024e060ff9,0x3c80602002448652068ff9,0xb6400e2c60606a17e9,0x578031c00c28014c036500084012a009b002a80167801f50980998986a0ffa,0xf900098800c701cb4002901981c4464a0586e17e9,0x20f00006801981736a0587017e9,0x8100204009dc007b800681ef800d9007cc031404c80144006e00ac059015b003e0540560130485b8d17500580c17ea,0x25e001f30035c01078015b006e80cc1e11348c0587417e9,0x4120001300330599880587597e9,0x7f002bc00ce008c0c18014c011600b74003e01ae0182026403d806c1b300290174056c00f006048b41e0681783f099b4e0580d17ea,0x10a023c05e200af0033802303060053004580002006e8007c015c0008182026406a80520698039005202e81bd009f01c083417048b41e0681a221236e9bdc0b0ffb,0xa0e05cc91bb7,0xda0a307d41c0b9bf8,3247545327511,0x58102f424c91fa7,0x2d7018202e5fcc91fb8,0x35a0a307c05e841fd8,0x35a0a307c05e849fe8,0x375041414a607c05cbf9ff9,0x780a0202e648c01fb8,0x2f098312507c05cc01ff9,0xf03130302e648101fb8,0xbc2614a507c05c101ff9,0x2b5001a9a000890a030405cc917b9,0x1d800d5100096c809a6c0f80b97fa,0x6320007838e0e070ff9,0x19bc0073e0e078ff9,0x3664003e8528411e06a8ffa,0x6200295c0075840052cc90400b97f9,0xc205f1e97f8,0xa0102e6c8101f78],
[0x69617026502e120101ff9,424687962101752,0x5a30006f003c2005ac6001450308605cd917f9,0xf8630605cda17d9,0x57200355400132d50227ab205c2417fa,69868984295,0x163b000f293030841e0897f8,0x4e0c50440f97f8,0x70cc058fe0897f8,69916661495,69916694503,0x7c38287c090472017f8,69916727031,0x81012059060897f8,0x3a0c50441117f8,0x1b0014a026c800fe801754001b6001760079723828192111e088ff9,0x1af8009dc0174a00142a0c92090ff9,86403290103,86470399959,86537508839,0x1c1011e065fe0997f8,0x381208704cc017f8,0x4e0c504c1017f8,0x2c5800fd4004280044400723c0a098ff9,0x2688003cc0102801c684e0a0ff9,0x33b003850024d8001ee00221a19ca0646b17e9,0x3b7006760061c00ff8024d8013d00488012c0065801e70814060b986b0ffa,389503580772344,0x129a001d0c480cc605cf197f9,0xe0f0f8640a405c0f9ff9,28950630471672,0x4c5800438110605cf217f9],
[0x7220015640492ae1480b97fa,0x3a0c50541117f8,0xeea000fa20003b400a41d01861160a8ff9,0xc300179200142a0c920b0ff9,0xa4100025e0039c61120b8ff9,0x10200087400e3c0a0c0ff9,0x422004ca800389040686b97e9,0x108801f1002e9800374003b400f840a1608b9c6b8ffa,0x303c3a0440e805e0c9ff9,0x44259080b97f8,0x1d0f14a0108605d3b97f9,0x442590c0b97f8,0x2518110605d3c17f9,0xc0f80025640492ae1d00b97fa,0x384010d5000230a0d0ff9,0x798026c400142a0c920d8ff9,0x377000514002c3860e0e0ff9,0x2370008cc00e3c0a0e8ff9,0x17c20009033860686c17e9,0x9dc0159400bd7001f6282c0cc986c0ffa,0x2d062a0e2480b9bf8,0x2d06212405e841fd8,0x2d06212405e849fe8,0x3bc1c5346512405cbf9ff9,0xa83c3a04412405cc01ff9,0x2a0f0f86412405c101ff9,0x1b8e003bc1c28e32c2480b97fa,0x10d1000c341e0f13f7,0x21a2000107a8417d7,0x219e000107a8497e7,0x8648007241c307078bf97f8,0x219a000082e05078c017f8],
[0x2192000082e050781017f8,0x15e01c2d9001ba6003cc0a060e0f0ff9,0x1109818f197220ff8,0x60082e0707c0f97f8,0xdb00fc800fe4007e100330c6139a0f8ff9,0xb60605800a830a100ff9,0xebc0096c007120a108ff9,0x3c801004007fc01e5801ae01aa021c06c80478013c0094801bf4061b69c6c8ffa,0x4790003e1000783851c22e2d40b97fa,0x3c808588002c220e110ff9,0x240277c001a020a118ff9,0x48182a001a020a120ff9,0x6c017b001a3860e128ff9,0x1ba40063c00b9e0036a0097c00f5030112289a06d0ffa,0x3bc000de000e030405c7317e9,0x3a7004d02770031e007ec0155803ee01ea0282008d002780530002801582b60c51c5f405c0c97ea,0x3980123c3890805c7617e9,0x7f017a802070062063c007a0293001ae001f00d900f500ca03740234023e0103a0048e872010924ce05c0d17ea,0x7f011380278152005f0062063c007a00bd006b8035c003e01b2019e00e0ca037401b03cc011802b01540f0401843429ca53962c4ac829bdc0b8ffb,0x1600cc8004ab000a81260610817f9,0x5f7000580c4e001501260610897f9,0x702230b52bc0c1bf8,0x78220b52c00c1df8,0xd078230b4062589fd8,0xd078230b4062591fe8,0x1ef068243250b40608e9ff9,0x14e74650b40608f1ff9,0x702230b40608f9ff9,0x1510002be002cf2042ec1680c17fa,7109964461182457,0x1705044616138ef9,0x741432a16140fb9],
[0x739000c460e140ff9,0x705044616148fd9,0x586001f928a9be86d8ffa,0x85c01009000a81270a80c17f9,0x4cb0035e00ebe001501260611317f9,0x2548007390422ee0603117fa,80498496503,4616051070455,71644518359,71644551143,0x78b01850ac8e97f8,0x3a0b050ac8f17f8,0x620450ac8f97f8,0xcc60044b8009ca000c5800f2838256158ff9,0x1e180084c006308007020a160ff9,0xd1800864000660015030a168ff9,0x88500014800bf80030228d6170ff9,0x9dc0072802a30055a00fb807c807f00bd803c4072e001101e582408c946e0ffa,0x73b800a81260612717f9,0x1ce6001501260612797f9,0x782295e1ac0c1bf8,0x78220d72c00c1df8,0x78220d6062589fd8,0x78220d6062591fe8,0x3e30243240d60608e9ff9,0x29c65840d60608f1ff9,0x1a1c08240d60608f9ff9,0x32e002cf2042ec1ac0c17fa,0xd4032be1793f7,71912920567,0x68450be5897d7,0x68450be5917e7],
[0x1f681c6490bc8e97f8,0x881c02070bc8f17f8,0x620450bc8f97f8,0x224000d6c000d8800f2838256178ff9,0x30c00645800a830a180ff9,0x32c0002e800f850a188ff9,0xcde000d4800381c6d6190ff9,0x3a5c0071840686e97e9,0x100c007040173801f3005ea00f101b50047401f208114986e8ffa,94595797332301817,0x32042ec1d00c17fa,0x1b050e073ea1997f8,0x23405d24002d038c93228ff8,0x3c120591a1997f8,0x2fa033802a6000a3a001ca170668b1a198ff9,0x23050e073ea1a17f8,0x63740035038c93238ff8,0xb802059221a17f8,0x26ea006af002f9003de800ed0b85310411e1a0ff9,0x50b0001dc003a0d8e1a8ff9,0xdb4001c3000820a1b0ff9,0x329c002209040686f17e9,0xfa02b04001be001b00d900bb805e803a078808120013dc04246a1186f0ffa,0x1a81260619117f9,0x32042ec2680c17fa,0x10a50010f002998006a0b0e1b8ff9,0xf82e053ee1c17f8,0xc75800441b030f248ff8,0x110140592a1c17f8,0x243120792e1c17f8,0x246d001290046801ec80069400a4803e201030cf14a21c0ff9,0x5b032fc00160d8e1c8ff9],
[0x320185c0f260ff8,0x33d001d7002c670e1d0ff9,0x1b740064401ec80210801aa011a006a01a50028a00656212864986f8ffa,0x58a8126061d217f9,0x18b1c08251780608f9ff9,0xec801950126061d297f9,0x1f3001fa12042ee2f00c17fa,0x620450ec8f97f8,0x27803530003f20022070382561d8ff9,0x10203b74001e024e1e0ff9,0x120669800a830a1e8ff9,0xa0052800f850a1f0ff9,0x3f600394019e00f980004000b80017c008501e60e1e32c9c700ffa,0x43a00246002c32c80607417e9,0x8de0071840607497e9,0x80a0037200f867807067803e600010075009e031018c01606a03bc00d500344432586254e0600d17ea,0x75017b8029c019a0038400cc0370041803e19e01c19e001900db0000802d80b17e00d81e600d4010809e06d403be01ac0a690a2c29094129b229bdc0c0ffb,0x9862a0e1ec0c9bf8,0x98620f74200c9fd8,0x98620f74240c9fe8,0xf2396650f65fc0c9ff9,0x284890440f6064c01ff9,0xa122c640f6064101ff9,0x284890440f6065439ff9,0xa122c640f6064111ff9,0x3cd00297000c6007ac00fb39ce6c1ec0c97fa,0x3251109a1f8df9,0x4c50e12200ef9,337129467055993,0x24f8002f0e0e208ff9,0x2e0c11e12210fd9,0x1bbc007d328a9be8708ffa],
[0xc20672697f8,72434315888172920,0x722c63032208101ff9,0x16e0052c8009318008ce0038b0628910c0c97f9,530241213110264,530241213143032,0x170d2803e200498200101801b741c306ad40c97f9,0xc20672817f8,0x322c63032088411ff9,0x4330010e012f80508800705e2880662217f9,0xad8028480061003de0018e5f19a2df40644117fa,0x3a0c51141117f8,0x2230005d2000ec800f700211002981921116228ff9,86404961271,73459308503,73459341287,0x7e11e07118bf97f8,0x23074087118c017f8,0x4e0c51181017f8,0xaa80016c00455000a2400723c0a230ff9,0x8a800a9c0007e800f850a238ff9,0xe3c0b288ef8,0x4d3001050016d003c5160e240ff9,0x46d001018015700286004d4012e07e8031802110039550d0481398710ffa,28863903963128,0x13c4007d06860656a17f9,28956536117240,0x13b4007f06c60656a97f9,0x4c122c64114064111ff9,0x452002d8305ee2280c97fa,0x3a0c51241117f8,0x2154003c58008c400a606186116248ff9],
[0x1482000a9c000a0610e250ff9,0x32c0008a800de04312258ff9,0x23a800614007120a260ff9,0x2538015f00734007c800650039a00fd86658b3a0718ffa,0x9862a0e2480c9bf8,0x98621254200c9fd8,0x98621254240c9fe8,0x38c2448651245fc0c9ff9,0x2f0489044124064c01ff9,0xbc122c64124064101ff9,0x780800f239a6c2480c97fa,0xc341e2693f7,73929070551,73929103335,0x1fc0a0307134bf97f8,0x24481407134c017f8,0x244814071341017f8,0x2465c071354397f8,73943291639,73943324407,0xde03135e416f8,0x2465c071341117f8,0x43a0039f0033c05cc028d800670049a007df814060e268ff9,0x1c785c071381117f8,0xf8e0001b0016c80097400ac26121116270ff9,0xa16000a1800f850a278ff9,0x7040046b4007120a280ff9,0xdb60032a0082c01a2013f80179004a801a4012c800b943c6db9c720ffa,0x44240672917f8,0x2612a06860659097f9,0x2b0489044134065439ff9,0xa594c0c97f8],
[0x4b808860659197f9,0x99a00558305ee2680c97fa,0xe42004f9800230a288ff9,0x9b2002a5800de04312290ff9,0xddc002ed001a6060e298ff9,0xe80070400e3c0a2a0ff9,0xf98055c019f80108803fe1bc66318728ffa,0xa0e065e01af7,0x91e13a0e30c0c9bf8,0xa10065e01ed7,9465834751663847,0x2ee0f022fe065e01ef8,0x311e13a1030c0c9fd8,0x311e13a1230c0c9fe8,0xdf75a162fe30c0c9ff9,0x90102032601e01ef8,0x2ce63045186064c01ff9,0x90102032f00101ef8,0x93cf15186064101ff9,0x15cc001d1000890c284065e016f9,0xf4700096c51c26c30c0c97fa,0x706800ad00a7801324001c16060e2a8ff9,0x86da001e40569000104a0e2b0ff9,0x360188800c60a2b8ff9,0x14017f000a2920e2c0ff9,0x469000136003ec00ef000288011e03cb058d9718730ffa,0x19c05ee00a700688019700198036c019a02f200aa005c011400e817600102b80e500540018010804900d40d58015200aa051c58a53830a33433e29bdc0c8ffb,0x1a0e040004a0018e260699d97f9,0x1c500380801a385b8a2800d17fa,0xabe001cc20e2c8ff9,0x22d40073e0e2d0ff9,0x382801ab891dc738ffa],
[0x4104d340d16f9,0x541d60117a0018e26d3c0d17f9,0x6c0013085666e0685397fa,0x702059522d97f8,0x2be006b01f4a001b58015a400d2021375e2d8ff9,0xff800010026500257c0041f001c384a122e0ff9,0x54402574002eb0025062522e8ff9,86405747703,86472857559,86539966439,0x1dc11e065fe2f17f8,0x70205178c017f8,0x4e0c51781017f8,0x18f000b4016ac0042e00723c0a2f0ff9,0x118c0041a00a6c01f300b58026808a804bc0371004580de07cea52c539c740ffa,0xaba0078820882848069b397f9,0x5750018e26069b517f9,0x2601f54007470b52c2b80d17fa,0x33980008f000174007088c562f8ff9,0x1020010e400e3c0a300ff9,0xcde001828004b045096308ff9,0xe3c0b2a8ef8,0x8ea0022b00230e50e310ff9,0x17806fa000880924019200aa011b4000901ad0609139c748ffa,0xa38652a2d40d17fa,0x7420000d200284d2318ff9,0x2c1e0d0932b0ff8,110229591799,0x5e031908f96f8,0x1da003d100022012b801644005041e1c52320ff9,0xdb400317003c38252328ff9,0x7040048dc00a50a330ff9],
[0xba02f900411000bc037f00044036c02da00af8005e008440027b010a1098750ffa,0x7838520882848069d117f9,0x3190018e26069d297f9,0x480800ce1470b52e2f00d17fa,0xeae0001f4002c1c4e338ff9,0x1f8800b4a0071c4e340ff9,0x23700117400e3c0a348ff9,0x3a00245001920a350ff9,0x7a401330025c007600194005b807ea5084919c758ffa,0x49a0038904069e016f9,0x3451652c30c0d17fa,56496119,0xc341e3593f7,75942336471,75942369255,0x3d6c71acbf97f8,56528887,9009480504311,0x3456001bc0851acc017f8,0x4e0c51ac1017f8,0xd4ce0031600ea40008f001b8838d12358ff9,0x982e053fa3617f8,0x1a3b00028020f1932b8ff8,0x2e0a079623617f8,0x8ca0037b8016a800920170c00e781c584211e360ff9,0xebc0120400083871212368ff9,0xcf400d2c0066c92370ff9,0x8be00209007c30036201f6002a800090027586281398760ffa,0x53017c8028c01a20068c005600df006280384001a01ba01ea01dc023800e01302ec00e0fe00406c05f0246e2009e03d02d81b48d488cc4308429bdc0d0ffb,0x14c05f200a30068801a300158037c018a00e10006806e807a8077019a00a81fe007c022809a064c00e1b9009e03d02a80140d37b07fc]]]

set_option maxRecDepth 100000 in
def data1 : List (List (List Nat)) := [
[[0x190cc30808c0017e7,463932788710,9244646,950117968843750,0x39260c258b0a1c128fe7,0x787045080940017e7,0xcc02020131766,950116426126310,463933181926,0x5cd0309c24c18130fe7,0x1b01052014039965,687665912165,0x1b01000160039965,472684901,0x1e23683000014039966,0x336020a40293e6,26388615992294,0x336020002c13e6,26388281988070,0x7fa1e046d0a0000293e7,0x130105201c091d45,91866535714592230,0xe260201c1515e6,1924615708997,0x7100000380399e6,0x464c40100001c091d66,0x3958a023870450c0000395e7,0x583606c040000417e7,668643265222118,5172380336527206,10129254,10129382],
[950118246946662,99747835062851526,0xd14e7fe1e0c2708e08a24148fe7,10131302,0x170470450a0a40017e7,10293222,0x52469a0611c4c14150fe7,944642534,0xd020004f13e6,0x500000038091bc6,0x8a39e3b1c48cc30c0000713e7,0x1e06c040000897e7,0x808102342044040000917e7,0x12451cf1227638e7042520000fe8,7424177526182886,668640980342694,0x630c103080080397e7,0x2b0e186101d8fa7,0x79c32214010fe8,14389222,0x33806020c258fe7,668640779834854,0x3f06c040140217e7,14847974,9359326647324647,0x128207044214020fe8,0x1b0785060940297e7,950116427633638,463939801062,0x23053b13031cf1a182a0fe7,0x2404083080e00297e7,0x13010b001c081d45],
[0x9c1d02160039766,0x520d0201c2c9766,0x501c01c082145,0xc41000a038039b66,0x2b064240100a01c081d66,0x941590503870450c014039767,0x78d041623795e6,16944614,16945126,950121407878630,0xd021604f1766,81733439707420614,0x20f829fb2c4c0c708e08a242c0fe7,352490982,0x14c0470450a1600297e7,17108966,0x3e071b626061a1a142c8fe7,668640849302502,688139475814,0x30000a038081bc6,0x90c80468f30081040830c0140713e7,0x34560e084848040140817e7,0x1e06c040140897e7,0x1e0701379c489e6010e7042520028fe8,0x23038d060940397e7,18321382,0x2a05c151b03020a0a18328fe7,668640993155014,0xb60238d081300397e7,0x50e26060240397e7,668640996987878,0xc6070450819c0397e7],
[0x7c0e260601c0617e7,326521851878,668641451612102,0x3060001c01c081dc6,0xc6c0001c01c091f46,0x8a19106e87b602785080380397e7,18943974,0x21804e8a3c0c712061c348fe7,0x23038d061a40397e7,19107814,0x6c320404c3517c6,0xb183898e6c18350fe7,963286211909,0x660201c5515e6,963152452933,0x2e06c0b61c68300e040091d46,0x1f07c142d1e010238d0c01c0815e7,0xf024260601c0897e7,0x4d0201c5c1766,0xf012071ba36010238d0c01c091767,668640984733414,0xa2b0709e0801c0997e7,0xd0682c0e09558b994a3090639ce08a24038fe8,19599334,0x9902820c370fe7,19730406,0x2840420c378fe7,0x76028207044214040fe8,0x2824040240817e7,0x2824040240917e7,0x3e1f08e18614048fe8,23236582],
[0xa207850c438fe7,23564262,0xb203850c448fe7,950116229617126,0x860240402c0917e7,0x4bce04514058fe8,0x1a054da10060fe8,25464806,0xd207850c4b0fe7,950116363409254,0xb6024040400697e7,26021862,0x8700450c4c8fe7,0x4bce04514068fe8,949655398,0x650247045080a40717e7,1305696571366,668641721718726,0x28f8020f833406384f0a184e0fe7,1925224209862,0xe2c81f045060384e17e7,956470758,0x170247045081600717e7,7902766567398,0xd020404f17c6,0x140961683340639e08a184f0fe7,1925358493510,0x208812785060384f17e7,88099314341830,0x11e308184f415830450c0380817c7,88099314767814,0x11981360304ca04e15850c0380917c7],
[0x205008182a0c964948e089518070fe8,1083873126,0x9e0238d080a40817e7,27922406,0xc4000485517c6,0x1702d07e1e061c4c14550fe7,0xf078d061a40817e7,2611368267750,0x501c1c7c3c0c38f0a18560fe7,0xac18d082200817e7,0xe4000405c17c6,0x2a0241582948742c38d0a0400917c7,0x1380a0624683833555c2c3847044220080fe8,0x5c170e40904608a14088fe8,1224906214,0xee0238d081600917e7,29855718,0x6831052c34061a1a145c0fe7,0x370126061a40917e7,6116063416294,0x321705858680c3408a185c8fe7,0x2709e082600917e7,0x82e121472e1208abf82c3847044220090fe8,0x1c054da10608ee7,0x1408204604514098fe8,0x19ce87c19b9e1c244c2e439c114307e9]]]

set_option maxRecDepth 100000 in
def data2 : List (List (List Nat)) := [
[[806557526,1544755030,1133948112726,2557613653,8514757163423574,0xd4e120a0e10130f57,0xb828b80c958fd6,88476470349782,5361462090181,0x1b0104e0500c9b85,0x1c418409c0a13d6,0x34418409c0b15d6,7705517544478614,0xee431905d0a31c138fd7,76587859708319190,0x26010000504519c5,2749518094725,0xcb80c20000500599d6,7142564977513942,387165536490966,0x4581e0200002c0c9d96,0x6f480c12c8518e0000595d7,0x681c22040000617d7,0x281840ac6295d6,10522582,0x20c7303858a314158fd7,0xc10000506299d6,1349097925,0x1c91b83820000500b19c6,0x14d800000500c9bc6,0x70c2f4441860000a13d7,8796099941846],
[0x7146cc34441880000b15d7,0x204c043c060000b97d7,0x1f03c020007216d6,0x54a230cc2008487080000c97d7,0x408e62a8c125050a31c000fd8,0x61040081b96d7,0xb038204e008049ad6,0x1c83083004024059a96,0x6083e19880080492d7,6210316686169815,0x140c20560080a1ad6,565700215349445,0x2c1004050629ad6,0xb0820040500b1ac6,0xcc20040500c1a46,0x5fe19860080a12d7,0xd9840080b16d7,0xd9840080c1657,0x21c01040080e1657,0xda7c8b828c214010ed8,0x78c2081b8fd7,0x5c1a0c210010fd8,0x2c4870402c0d96d7,0xe141840580d96d7,0xe1f01840600d9657,0x14d87040700d9657,0x37c898250e140d8ed8,37392119631832,0x1508c040140b97d7,343021270,0x7c388c060140c97d7,0x1520cb0e10028fd8],
[477238998,0x230040401c0c97d7,0x230ccb0e14038fd8,37392119762904,0xe83c39d070809c0497d7,2750460664709,96895808246742,21172182,0xc00643b1796,0x1983d8c8020a3143b0fd7,0x7c01041ec059796,17730367264662,1238297287557,0x902802c0b2185,0x6c1012050059b96,0xcb0104024451796,17730233538454,0x4cc201202c0b1d96,0x1c1dee0c1c130518c024059797,21958614,0x5201041ec641796,0x900c6d01818f02143d8fd7,0xe0f0581081ec0497d7,88476482670550,0x285f0d04c02103e0fd7,0x9028060642305,0x2b01012050641b96,0x240e800120500b1bc6,0x18a0c20120500c1b46,0x720e0c260f020120500c9b86,0x1c80448f784c1e060240a13d7,0x609012826e419880240b17d7],
[0x99840240c1757,0xe1040240e1757,0x1c839a18d0c8581080240c9797,0x170c830c6aa7fa030d63318048fd8,0x78095070809c0597d7,0x60b8095f0fd6,26527198778838,950117167437718,0x310390b0020a314428fd7,37261270,0x760e80601040504517c6,0x2c0e808102802c0b1dc6,0x38e4022008202802c0c9f86,0x21366025c3c8819860500597d7,0x60b809690fd6,0x91d82e04b394b150f021c450fd7,0x14146c1e082280597d7,88476484308950,0x760f82b2a150f0214458fd7,26526463038934,0xd80a0c30160580c1d46,0x3070160c11d247c347810c02c0b15d7,77713757468104535,0xc870402c0e1757,0x22d06c1920a09c28087810e02c0c9797,0x4242c640a0462ade504701804331c058fd8,0x2480703852c14060fd8,3861310246872,0x3825014441860ac0a17d7,0x60b809e58fd6,0x4840486106888310628fd7,0x1481b01028058629dc6],
[0x18a09c0c41840506297d7,0x2900820f60500c1f46,0x1b04f0581061ec0a17d7,88476492664790,0xa42a12c190b0210640fd7,0x190081028060641f46,0x81028064641f86,0x145c1d81040506417d7,0x16c01020506997c6,0xc1d078a40c7a1707060500b17c7,0x7405808ca419860500c1747,0x40b0aa0cc8581060500c97c7,0x3060680c78f092597582811633180a0fd8,0x6c14441880ac0b17d7,0x60b809fd8fd6,0x3502e1784c0d0310680fd7,0xf0f021140580c1f46,0xd221e1e082280b17d7,33722326,0x8409828f0e150f0214698fd7,0x190208a419880580c1747,0x1c087110042890224ba7432c33180b0fd8,0x2e0d4070612c100b8fd8,5656164309112663,0x38881a09051b314283140c0f58,37946177589207,0x4810283100c0fd8,0xe22068060d31490e140e0f58,446779789014,0x2e19c81780412c10720ed7,0x2e192162c18381429c28082b021c0c8fd8,0xf0992682068630314ba8e0940858307d9]]]

set_option maxRecDepth 100000 in
def data3 : List (List (List Nat)) := [
[[8656806,0x4b05830608c0017b7,879749226960310,652911349686,9244598,0x4c020940713b6,2483524534,429573115830,9310134,879749224994614,2483951414,0x3ff204120b414128fb7,879746743932342,0x2d81a040940017b7,492719186319158,2551224118,0x4c020381313b6,652911742902,9637814,0x37c2020a09810130fb7,879746749142454,0x62d81a040007697b7,0x62010000142a19b6,5635332872501,687665912117,0x2601000160039935,472684853,0x1901000168039935,472750389,339056949,339089717,0x1fe10140d03000014039936],
[0x44010000140399b6,0x284c020a40293b6,87961267147702,0xa1a020002c13b6,87960933143478,6040525221,92077639198380982,0x7000002d93b6,688671957285,0x8d00000140b19b6,0x1c200000140c1b36,343906613,4503599963839286,0x63eaaac70281a080000293b7,0x6201000014039d36,0x114170281a060000297b7,0x60440100001c0319b6,0x88020a40313b6,457534279291830,0xdd8b074060000313b7,0x160440100001c0f9d36,0x189872d81a040000f97b7,5635467451669,0x3e14c020a40395b6,70369215321526,1924615708949,0x827c010000380399b6,475175221,4503600097630646,0x1b0c4000001c091d36,16777451829,4503600098254134],
[1345690021,2749249626405,0x58300000500399b6,476453173,4503600097827254,0x70332020003595b6,0x44000003615b6,0x68288c0100001c0c1d36,17045887285,4503600098057526,0x74226a55975e3038060000395b7,0xec070dc040000417b7,240622571446,492718656295862,492718656329142,8165286,0x1d83d87832060001097b7,0x4c020a49a1736,223415537462,10129334,0x4c020a49a9736,0x7c1a020a4091796,40374069,0x4e1b8089b8fb6,10227638,4925952283711382,0x1d00852a1ebae12a0a0c341c148fb7,10098486,10131254,0x64a81c1a080a40017b7,10293174,429574197174],
[0x340501370c11b810150fb7,457534281290678,0x2600000038091b96,0x26010002800b19a5,0x5a020005013b6,457534281388982,0xc8080001c0580d2185,0x1a3c010000380b19b6,0x11810000380d1b96,0x38383c0f055641050385830c0000713b7,0x81038040000717b7,0x84000005293b6,0x2d03605a80203060000793b7,0x20dc040000897b7,0x4150885890a038040000917b7,37326774,0x4a04c020007d13b6,0x4c020007d95b6,0x1083b038040001117b7,10489782,10555318,457537162581926,0x108190e21360b0614158fb7,0x58441a060ac0017b7,10719158,41652021,9964402020278,90564850380838822,0x25a8d4060c160fb7,1349065125,0xb80e0a86c1820000500b19a6,0xfa000000500c1ba6],
[0x19014150db0583060000a13b7,0xf4000006613b6,457534282863542,1745525670,0x3907d83040000a93b7,17592192931254,0xcf4000000580c1da6,0x60c19010000580d1da6,0x320281e1ce9b0583080000b15b7,0x5b025c13a051cda038040000c17b7,37359542,0x7032020007f13b6,0x43032020007f95b6,8394422,0x283600c0f60201c060000e17b7,7673526,0x13821c0410468c81e060000d17b7,0x142a2882225858a3631590961084b15820a070b0618000fb8,5905617846,5972726710,337253302,0x2581f30583060140093b7,941102006,11276214,11308982,0xb80e70b060c180fb7,1925353347990,0x4c042630583060380093b7,457535485777814,0xd4199c60b06101a0fb7,0x3324b0c4040480097b7,16777253814],
[37392310,0x610c4040880097b7,0x108977e070b0610008fb8,492718785729462,0xe8dc040080397b7,0x164e0d0210010fb8,240598683574,492719120061878,0x2c36785c0610200fb7,204641206,492719120127798,472094614,0x5778784c0601c0197b7,13602742,0x136a1d0b0610210fb7,0x12a1d0b0610238f97,0x3116c04070d0214018fb8,99536892843923126,0x4600401060102516b7,282826422,0xc600401060102596b7,1924416542901,550765205685,284628149,284660917,284693685,284726453,551369186357,551637621813,0xff1c020102a14b6,0xd0100a0102a1cb6,285381813],
[0xd010b0010081c95,0xda021600216b6,0xe1a020102c96b6,0x501c010082095,0x68a60100a038021ab6,0x78000a010079ab6,0xc6c840100a010081cb6,285709493,0xd010b40100b1ca5,0xda021680216b6,0xc1a020102d96b6,0x50080580c2425,0xf1a2c0100a0100b1cb6,0x10590100a0100c1e36,0x50000a0100e1e36,0x3abd5fa161a09a0a0140216b7,0x68440a3b0eb6,0x3422040107794b6,0x342204010789696,0x2403040107916a6,0x3d703416810a0100f16b7,0xe008040032095,4505524041358006,550832741525,0x2a601008040031cb6,4398318130870,0x312e4140b05830a0100316b7,551240211621,2199299692214,0x402c0600fa425,0xb9010080580f9cb6,9007750622191158],
[0x3042fa161a09a0a0100f96b7,99536940222781110,0x4304201060107716b7,30400452278,0xc304201060102696b7,550834740373,2199296874166,0xc5008222008201c010081c96,0xd0001c010091e96,0x62804384050681080380216b7,0xdc020a3c0eb6,295802037,0x5a020105296b6,0x482a90e8583080100796b7,550839688245,0xebc0d03052010081cb6,0xe0d02008040199cb6,0xbc0d020081a4081cb6,0x2506160083008040091c96,0x287811faf0681080100814b7,0xf0284081681080100916b7,306222261,0x5a023e80216b6,0x5784201060101116b7,0x2103c0d00830280100b1ca6,0x1a000280100c1ea6,0x7c1ca0b11080500216b7,301012149,0x5a020106616b6,0x566e01060100a96b7,0x220d020560100b1cb6,551251515573],
[0xbc220d030081ac0b1cb6,0x28d020080587e9cb6,551239425189,0x3140b07b00820080580c1ca6,0x285428aaf088681080100b14b7,0xc00106e16b6,0x4285414284050681080100c16b7,306386101,0x5a023f80216b6,0x78020a3c8eb6,0x6205cc389a080100e16b7,0x2b832944984a76dc44d8d020c020eb8,14389174,0xc408c008020c258fb7,492718919390646,0x7a1101c060140217b7,14847926,0x32086084020c268fb7,0x12b0d058d0214020fb8,0x901583060140e96b7,0x170020da080380e96b7,0x3c460d83080600e96b7,0x8ee3b06140e8eb8,0x2b0090d81a060940297b7,879747213694390,0x248000382a13b6,0x2480003c2a13b6,5016537993142,5016538025910,5016538058678,5016538091446,0x248000602a1736],
[0x248000702a1736,0x188d80317046028ff920b40c2a0fb7,0x440100a01c2a1d36,0x90fe0260920420281a060142a17b7,0x668dc060e00297b7,0x1101c040142a97b7,0xb001c081d15,0x36014c02160039736,0x3a00001c2c9736,0x501c01c082115,0x4a01000a038039b36,687669844277,4504287292398390,0x1f00c4000a01c081d36,0x9c01a02168039736,0x4e00001c2d9736,0x9c03202014359736,0x4e000014361736,0x78e900ca5ff020281a08014039737,0x2c3c405c39281a060140397b7,6040852278,6107961142,343611190,0x175c09a06014101737,7902756769718,879752649676694,0x9a0241a02160081796,43388341,0x7a1b809040fb6,17076150,0x82f80f8268030d69b0440c2c0fb7,0xa5078041600297b7],
[17108918,879747683620758,598374995103670,429581078454,879748488927126,0xbe03e06605818317db044082c8fb7,688137214870,0x2c4d8020142c97b7,340661174,0x9a0020000a038081b96,0x741cc8180501c0600d2305,0x1ac190200a0380c1b36,0xb990200a0380d1b96,0xc823805600c320ab983422060140713b7,0x358a78c4060140717b7,633319038456758,0xfe01580500c0a2403040140793b7,0xe82580560142c781110c4040140817b7,3161113202614,17371062,879752783959974,0x47003601a021680b17a6,0x1f047012c0a08687c78060c2d0fb7,0x30e074041680297b7,17403830,429581340598,879748354774950,0x4c020682d97a6,0x11c02700a14b0504bc7806082d8fb7,688808369958,0x3174020142d97b7,0x11c01480000a0580c1f26],
[0x1408e01180702c0a3858040140b17b7,342791990,0x110a0e0200a0600d1f26,0xc08e0128030b81412c82403060140c1737,0x228315074060140c17b7,0xea0000147f9736,0xa045009400e02b422040140e1737,343217846,0x288478e3321e040140d17b7,0x140a681a8008042285d8939a2a559625a94702b0610028fb8,0x3422051e87794b6,396116385828279,0x201b804858684410778fb7,0x5868440c780eb7,0x1c80684408788f97,0x7200480608790fa7,0xbc07d94e1134180f0fb8,879747213956534,942543798,18416837332918,0x8fa06080f5004060c2e0fb7,0x5800a01f809981a0401c0317b7,1924553644821,0x4301001c040031b96,0x96037805819983422060380313b7,0x4900c0018561736,0x8e01a02040309796,0x4f006e008bcb0c4060400317b7,0x2780960560e2a460b0610308fb7,0x4f003e0384edde0b060c030fb8,429601427382,16308246326],
[0xc0e80b901ce02440c798fb7,457534753871670,0xc4021ac0f9736,0x3f401f034b0c40601c0f9737,0xa601a020587a17a6,0x1d40441b47034134107a0fb7,3312494549797,0x72023400f93b6,0x14c02002c0600f9f26,0x410045bcf074060580f97b7,0x120321a88703422060600f9737,0x57002603810c89b41340c0f8fb8,0x3481981a040940397b7,0x3340321981a0401c1797b7,18321334,429582192566,879748355102518,0x620291e0020e379090f86410328fb7,484513686,0x11c09a061300397b7,457535219079062,0xd640001c01c081d96,0xcbb00001c01c091f16,0x52836d80d540e2078040380397b7,18911158,0x17404c0201c5115b6,475141814,0xc1004c0201c529736,0x16838405903de0b01c0601c0797b7,18943926,53250997,512063334158262],
[19074998,0x9180185c303413414348fb7,0x5781a061a40397b7,19107766,53283765,3882736750518,0x73204068351796,0x2586068440c350fb7,963286211861,2199498593718,0x190100e0405e1d15,0x3840028054d0200e040091d16,0xc808070200600d2505,0xa8c0100e0400c1d36,0x2590100e0400d1d96,0x3b4051012097bc09a0801c0815b7,0x51a0201c5e1736,0x6a80be02c19bc09a0601c091737,0x1d20003e8039736,457534754133814,963818626838,0x1ca01e9a0401c111737,0x3b401a020503597a6,0xed00002801c0c1f26,0x3706c80110186074040500397b7,19271606,879747217561014,0x3c40320201c661736,0xeb00ef0c40401c0a97b7,879753959445430,223424711606,879753941128118],
[19304374,19402678,0x78021ac0d17a6,0x7a0d700940d83c39faa106110a341c358fb7,77041210294,489067446,0x6a7051a081ac0397b7,19435446,429583372214,0x1ae00940139090d8810360fb7,0x110dc0401c0b97b7,457534753085238,457534753216310,0xc110100e0600d1f26,0x7a0cf01140d86e243a487c089a0c01c0c1737,0x908f80401c0c17b7,0x2220003f8039736,0x3f042c016701220601c0e1737,477435574,0x38211343867781e0601c0d17b7,0xfc0d40101a02140d062444632c108989cda4a5486c8113418038fb8,37654454,37687222,16442464054,0x5a0044048310391340c7a8fb7,457535626352550,2750390738726,0x2180275074040501017b7,37719990,13691262774,0x610c4040541017b7,0x1b00502526008134107b0fb7],
[0xd4018d4cc09a06060101737,0x76009b7c8113410100fb8,0x12f0064e0d0210040fb8,37752758,0x47200909a05507134107b8fb7,0x52201f400c1e130e44107c0fb7,0x4bc01507134107c8fa7,0x92802ec6c14d0214108fb8,949655350,0xd09504c080a40717b7,26513334,1213077398,598375004475318,1749948310,0x1c0626804501ee320b034144e0fb7,0x17405078041600717b7,87136323243958,0x6401a020404f1796,598375004737462,879748356970294,0x2c031025048e703d701134104f0fb7,0x3f800038561796,0x90104280081796,17730704021398,0xc0104038571796,0x420104038579796,0x1381e1d06c2e4027f8a306810a038081797,0x98020385e1796,0x163101d003401a04ac00857012206038091797,598375004901302,27070390,0x9c800601042800b17a6],
[0xe8022800c17a6,0x2c58807501cf11e82210500fb7,0x70a3c1e082800717b7,27135926,429591039926,0x4940142c4420f0210508fb7,879747687519158,0x50c021008201c0580d1f86,0x848c039cd7601060380b17b7,879747687912374,0x1020383c0201c0600d1f86,0x7851002186351081e060380c17b7,0xf192010c038d232c20d110a0380d1797,0x78c603a02e0541e2a83e094065944cedba740e162218070fb8,0x52303e802607580c1050040614510fb7,0x6b0261d0b0610520eb7,20615870386102,0xc0250384805058dac0de0b060c528fb7,0x1808e01903181a920a58b0614078fb8,0x960000409a9736,0x124038901c1a080a40817b7,0xb4012c0320e2961a0a0401997b7,27922358,0x2f800048551796,27987894,879748491581334,0x4f805b03f08b1b810550fb7,0x5500d781a061a40817b7,0x654001ad8fb6,598375006146486,879748357429046,0x8814807838a068440c560fb7],
[0x3680901040405e1796,0xec0110318164031c409a06040091797,0x27e00c80501a01060500817b7,47091509,9964419714998,0x90104040671796,0x810200680a9f86,0x7884201060400a97b7,28544950,28610486,0x3401042b80c17a6,0x48803302107462c060f0218570fb7,0xd82c681082b80817b7,28708790,429592612790,0x940b1010840210578fb7,0x4800200820200600d1f86,0x34630128a64401060400c17b7,0x156004401c1ca2842250681080400d1797,0xcc03d01501a0d05c0a85922b09cb8878182d0218080fb8,0xc780681c1b414088fb8,0xf301f074040500917b7,30412726,879747955890070,0x6b0c4040480a97b7,0x601040585e17a6,0xd40447601060580917b7,30478262,598375008407478,0x8e00c0b8058260bd0b80202105e0fb7,0x2102d00a811c0081700b02432dc8113410090fb8,40956845920182],
[37818294,37851062,879763519248278,0x5f02f00881c24090ac03603db044087d0fb7,53316533,3882755428278,16845182870,0x1184028d8318186068440c7d8fb7,0x4c020507e17a6,0x235074040501117b7,1782749061,1111658422,9010774077939590,0x610c4040541117b7,0x601040587e17a6,0x8102c068111f86,0x18f7601060581117b7,0x540666a6d0b80202107e0fb7,0x3a0094da3078106068111797,0x1f02d01f400980611137c8113410110fb8,0x35e0000506917a6,0xea03b021804c05605f0583060500b17a7,1349425062,0xa3a81b401e04701a05a05100203060500c17a7,0x147501c811401c0680301c121217e070b06100a0fb8,13556848550,0xa2c0a201aa0560a8d4060c650fb7,53051468615606,32673718,0x4c023300d17a6,0x7701a814b0281d02140cc02c1c780608660fb7,0x7f801043c230a2011e82210670fb7],
[0x14700341609830781060680a97a7,0x3980fe0050130060b07089fe070b06100a8fb8,0xc90078441a060ac0b17b7,0x96001fd0fb6,598375011323830,0xbf0000606817a6,0x2300fe03b0388e4060c680fb7,0x1a20000592693b6,0x33c02f02851a081ac0b17b7,33591222,33689526,0x4c020686917a6,0x3e8011805876828d8810690fb7,0x8500aa00501351a0a0587e97b7,0x282c681082b80b17b7,429597724598,33951670,0x401040606a17a6,0x481f588402106a0fb7,0x38c01a020586e17a6,17731108738982,0x61ec04a0284c08a03c32090bc61f06810a0580c17a7,0x3b8076011281a190716050681080580d17a7,0xa1e40720260d402c01c1e1a0cb0444c9bc9829622180b0fb8,0x5d0070241b06140b8fb8,0x1f800e074041680c17b7,0xf2002158fb6,598375012962230,0x4605416140207a0aa07344070b06106e0fb7,1629918134,0x28301432081ac0c17b7,35098550],
[598375013093302,1752078246,0x1140c82d60260ea1a185034146e8fb7,0x474021e082f00c17b7,429599330230,35524534,0x18c04820c010f4320f0210700fb7,0x820389c0a01051181498020f810a0600d17a7,0x1ec0f00c0b1341981c460b80d048a87409913b1c05022d02180c0fb8,71743171661750,0xfb00e814b0904e03980b41340c7f0fb7,0x2b300f40a386f0090d90244147f8fb7,0x7fc03c713410800eb7,0x7901c815c06f00bb8e1134140e0fb8,1889889554102,0x2c405701e407e0f0b410750eb7,0x16202b80e81c7c38e161a1a03011f83891d02180d0fb8,0xc3386e07089c0e58d04c0b161a06060a85830c3421066d39468207b9]]]

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

def insert (w : Nat) : List Nat → List Nat
  | [] => [w]
  | x :: xs => if w <= x then w :: x :: xs else x :: insert w xs

def ordered : List Nat → List Nat
  | [] => []
  | w :: ws => insert w (ordered ws)

def programWord : Nat → Nat → Nat
  | 0,index => inputs.getD index 0
  | fuel+1,index =>
    if index < 7 then inputs.getD index 0 else
      forceNat (getCode wordData (index-7)) (fun code =>
      forceNat (programWord fuel ((code >>> 2) &&& 2047)) (fun a =>
      forceNat (programWord fuel ((code >>> 13) &&& 2047)) (fun b =>
        let o := code &&& 3
        if o == 0 then a &&& b else if o == 1 then a ||| b
        else if o == 2 then a ^^^ (a &&& b) else b ^^^ (a &&& b))))

def extraWords : Nat → Nat → List Nat
  | 0,_ => []
  | count+1,code => programWord 12 ((code &&& 2047)+7) :: extraWords count (code >>> 11)

def nodeFromCode (code : Nat) : Nat × List Nat :=
  let rootMask := (code >>> 4) &&& 127
  let count := (code >>> 11) &&& 15
  let rootWords := (inputs.zipIdx).filterMap (fun (w,i) =>
    if rootMask.testBit i then some w else none)
  (code &&& 15,ordered (rootWords ++ extraWords count (code >>> 15)))

def codeRow (code index : Nat) : CodeRow :=
  let count := (code >>> 11) &&& 15
  let rem := code >>> (15+11*count)
  match readCuts (rem &&& 15) 0 (rem >>> 4) with
  | (cuts,deps) => (0,0,cuts,readDeps 512 index deps)

def row (forest index : Nat) : CodeRow :=
  codeRow (getCode (forestCodes forest) index) index

def node (forest index : Nat) : Nat × List Nat :=
  nodeFromCode (getCode (forestCodes forest) index)

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

namespace PEqualNP.Outside.L_meta_10760
namespace RestrictionSixProof

lemma autoPool_var_eq_xN {v : Nat} (hv : v < 7) : AutoPool.var v = xN v := by
  interval_cases v <;> rfl

lemma autoPool_var_eq_zero {v : Nat} (hv : 7 ≤ v) : AutoPool.var v = 0 := by
  apply List.getD_eq_default
  simpa only [AutoPool.inputs, List.length_cons, List.length_nil] using hv

lemma autoPool_op_eq_nb (o a b : Nat) : AutoPool.op o a b = nb o a b := by
  cases h0 : (o == 0) <;> cases h1 : (o == 1) <;> cases h2 : (o == 2) <;>
    simp_all [AutoPool.op, nb]

lemma autoPool_poolRun_eq_mkPool (pool : List Nat) (cs : List (Nat × Nat × Nat)) :
    AutoPool.poolRun pool cs = mkPool pool cs := by
  induction cs generalizing pool with
  | nil => rfl
  | cons c cs ih =>
    obtain ⟨o, a, b⟩ := c
    rw [AutoPool.poolRun, mkPool, autoPool_op_eq_nb]
    exact ih _

lemma autoPool_available_eq_av (d : Nat) (pool : List Nat) :
    AutoPool.available d pool = av d pool := by
  funext raw
  have hx (a w : Nat) : w = a ^^^ d ↔ a = d ^^^ w := by
    constructor
    · intro h
      rw [h, Nat.xor_comm a d, ← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor]
    · intro h
      rw [h, Nat.xor_comm (d ^^^ w) d, ← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor]
  have hp : (fun a => (raw &&& d == a || raw &&& d == (a ^^^ d))) =
      (fun a => (a == raw &&& d || a == (d ^^^ (raw &&& d)))) := by
    funext a
    apply Bool.eq_iff_iff.mpr
    simp only [Bool.or_eq_true, beq_iff_eq]
    exact or_congr eq_comm (hx a (raw &&& d))
  simp only [AutoPool.available, av, hp]
  rfl

lemma autoPool_countConstants_eq_sumc (d : Nat) (ws : List Nat) :
    ws.countP (fun w => w &&& d == 0 || w &&& d == d) = sumc d ws := by
  induction ws with
  | nil => rfl
  | cons w ws ih =>
    cases h : (w &&& d == 0 || w &&& d == d) <;>
      simp_all [sumc, cn, Nat.add_comm]

def autoProgramCut (s : SliceD) (cs : List (Nat × Nat × Nat)) : CutV :=
  (s.1, s.2.1, cs.length,
    AutoPool.poolRun (s.2.2.map (fun v => AutoPool.var v &&& s.1)) cs)

lemma autoProgramCut_sound {R T s} (hs : SliceN R T s)
    (cs : List (Nat × Nat × Nat)) : CutP R T (autoProgramCut s cs) := by
  obtain ⟨⟨f, roots, dom, base, nc, lo⟩, hv⟩ := hs
  have ps : PS f (roots.map observe)
      (s.2.2.map (fun v => AutoPool.var v &&& s.1)) := by
    intro w hw
    obtain ⟨v, hvs, rfl⟩ := List.mem_map.mp hw
    change Available true (roots.map observe) (RF f (Nat.land (AutoPool.var v) s.1))
    rw [rf_land dom]
    by_cases h7 : v < 7
    · rw [autoPool_var_eq_xN h7]
      exact base _ (List.mem_map_of_mem (hv v hvs))
    · rw [autoPool_var_eq_zero (by omega)]
      exact Or.inr (Or.inl ⟨false, rf_zero⟩)
  obtain ⟨bank, hb, hp⟩ :=
    mkPool_ok cs (Reach.start (u := true) (roots := roots.map observe)) ps
  refine ⟨f, roots, bank, dom, nc, ?_, ?_, lo⟩
  · simpa [autoProgramCut] using hb
  · simpa only [autoProgramCut, autoPool_poolRun_eq_mkPool] using hp

lemma cutEval_of_whole_list (d L paid : Nat) (pool : List Nat)
    (k : Nat) (rest : List Nat) (a b z : Nat) (ka kb : Bool)
    (ha : (z :: kept ka a (kept kb b rest)).all (av d pool) = true)
    (hl : k + paid < L + sumc d (z :: kept ka a (kept kb b rest))) :
    cutEval k rest a b z ka kb (d, L, paid, pool) = true := by
  cases ka <;> cases kb <;>
    simp_all [kept, keepB, keepC, sumc, cutEval, Nat.blt_eq] <;> omega

lemma autoCut_to_cutEval (s : SliceD) (k : Nat) (rest : List Nat)
    (a b z : Nat) (ka kb : Bool)
    (h : AutoPool.autoCut k (z :: kept ka a (kept kb b rest)) s = true) :
    cutEval k rest a b z ka kb
      (autoProgramCut s (AutoPool.guess s.1 s.2.2
        (z :: kept ka a (kept kb b rest)))) = true := by
  obtain ⟨d, L, vs⟩ := s
  dsimp only [AutoPool.autoCut] at h
  split at h
  · cases h
  · simp only [Bool.and_eq_true] at h
    obtain ⟨hl, ha⟩ := h
    apply cutEval_of_whole_list
    · simpa only [autoPool_available_eq_av] using ha
    · simpa only [autoPool_countConstants_eq_sumc] using of_decide_eq_true hl

lemma autoCut_sound {R T s k rest a b o ka kb}
    (hs : SliceN R T s)
    (nd : (kidW rest a b (nb o a b) ka kb).Nodup)
    (h : AutoPool.autoCut k (nb o a b :: kept ka a (kept kb b rest)) s = true) :
    Impossible true (W T) k (kidW rest a b (nb o a b) ka kb).toFinset :=
  cut_sound (autoProgramCut_sound hs _ ) nd
    (autoCut_to_cutEval s k rest a b (nb o a b) ka kb h)

lemma autoCuts_sound {R T k rest a b o ka kb} {Z : List SliceD}
    (hZ : ∀ s ∈ Z, SliceN R T s)
    (nd : (kidW rest a b (nb o a b) ka kb).Nodup)
    (h : Z.any (AutoPool.autoCut k (nb o a b :: kept ka a (kept kb b rest))) = true) :
    Impossible true (W T) k (kidW rest a b (nb o a b) ka kb).toFinset := by
  obtain ⟨s, hs, hc⟩ := List.any_eq_true.mp h
  exact autoCut_sound (hZ s hs) nd hc

lemma append_child_eq_kept {α : Type} (z a b : α) (rest : List α) (ka kb : Bool) :
    z :: ((if ka then [a] else []) ++ (if kb then [b] else []) ++ rest) =
      z :: kept ka a (kept kb b rest) := by
  cases ka <;> cases kb <;> rfl

end RestrictionSixProof

namespace RestrictionSixProof
open PEqualNP.CircuitLowerBounds
private lemma physical_live_proper {u target k S} (h : Live u target k S) : ∀ a ∈ S, proper a := by
  induction h using Live.ind with
  | stop hp => simpa using hp
  | binary hd ha hb hab hf _ ih =>
    simp only [Finset.forall_mem_insert]
    exact ⟨ha,hb,fun a h => ih a (Finset.mem_insert_of_mem h)⟩

private lemma physical_bit_zero (i) : bit i zero = false := by simp [bit,zero]
private lemma physical_bit_one (i) : bit i one = true := by unfold bit one; rw [BitVec.getLsbD_allOnes]; simp
private lemma physical_bit_neg (i) (a : Sig) : bit i (neg a) = !(bit i a) := by simp [bit,neg,i.isLt]
def physical_gv (w : List Sig) (g : Gate) : Sig :=
  let xs := g.inputs.map (fun i => w.getD i zero)
  match g.op with
  | .and => xs.foldr (prime false) one
  | .or => xs.foldr (prime true) zero
  | .not => neg (xs.headD zero)
  | _ => zero

def physical_execute (gs : List Gate) (w : List Sig) : List Sig :=
  gs.foldl (fun l g => l ++ [physical_gv l g]) w

private lemma physical_neg_laws : neg zero = one ∧ neg one = zero := by simp [neg,zero,one]

private lemma physical_get_rep {u} (w : List Sig) (i : Nat) : Repr u (w.map (nrm u)) (w.getD i zero) := by
  simp only [List.getD_eq_getElem?_getD]
  cases h : w[i]? with
  | none => exact repr_const (Or.inl rfl)
  | some a => exact Or.inl (List.mem_map_of_mem (List.mem_of_getElem? h))
lemma physical_repr_neg {w a} (h : Repr true w a) : Repr true w (neg a) := by
  unfold Repr
  rwa [nrm_neg]

def physical_isNot (g : Gate) : Bool := match g.op with
  | .not => true
  | _ => false
private lemma physical_gate_rep (u : Bool) (w : List Sig) (g : Gate)
    (h : g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ g.inputs.length≤2)
    (mono : u=false → physical_isNot g=false) :
    Repr u (w.map (nrm u)) (physical_gv w g) ∨ (physical_isNot g=false ∧ witness u (w.map (nrm u)) (nrm u (physical_gv w g))) := by
  obtain ⟨o,l⟩ := g
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at h
  obtain ⟨ho,hl⟩ := h
  have prim (d : Bool) : Repr u (w.map (nrm u)) ((l.map (fun i => w.getD i zero)).foldr (prime d) (if d then zero else one)) ∨
      witness u (w.map (nrm u)) (nrm u ((l.map (fun i => w.getD i zero)).foldr (prime d) (if d then zero else one))) := by
    have unit (v : Sig) : prime d v (if d then zero else one) = v := by
      apply bit_ext
      intro i
      cases d <;> simp [bit_prime,physical_bit_zero,physical_bit_one]
    cases l with
    | nil => exact Or.inl (repr_const (by cases d <;> simp))
    | cons i l =>
      cases l with
      | nil =>
        simp only [List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,unit]
        exact Or.inl (physical_get_rep w i)
      | cons j l =>
        cases l with
        | cons a l => simp at hl
        | nil =>
          simp only [List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,unit]
          exact prime_rep d (physical_get_rep w i) (physical_get_rep w j)
  rcases ho with rfl | rfl | rfl
  · exact (prim false).imp id (fun h => ⟨rfl,h⟩)
  · exact (prim true).imp id (fun h => ⟨rfl,h⟩)
  · cases u
    · exact absurd (mono rfl) (by simp [physical_isNot])
    left
    cases l with
    | nil => exact repr_const (Or.inr (by simp [physical_gv,physical_neg_laws]))
    | cons i l => exact physical_repr_neg (physical_get_rep w i)

-- Remove a last computed signal from a backward derivation. A gate whose value
-- is already available, or is unused by the suffix, needs no entry in the plan.
private lemma physical_pull_gate {u target} {w : List Sig} {z : Sig} {k S c} (h : Live u target k S)
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
    · have hp := physical_live_proper h z hm
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

private lemma physical_extract {u target} (gs : List Gate) (w : List Sig)
    (legal : ∀ g ∈ gs, g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ g.inputs.length≤2)
    (mono : u=false → ∀ g ∈ gs, physical_isNot g=false)
    (hp : proper target) (hout : target ∈ (physical_execute gs w).map (nrm u)) :
    ∃ k S, k ≤ gs.countP (fun g => !physical_isNot g) ∧ Live u target k S ∧ ∀ a ∈ S, a ∈ w.map (nrm u) := by
  induction gs generalizing w with
  | nil => exact ⟨0,{target},by simp,Live.stop hp,by simpa [physical_execute] using hout⟩
  | cons g gs ih =>
    obtain ⟨k,S,hk,ht,hs⟩ := ih (w++[physical_gv w g]) (fun a ha => legal a (by simp [ha]))
      (fun hu a ha => mono hu a (by simp [ha])) hout
    have rep := physical_gate_rep u w g (legal g (by simp)) (fun hu => mono hu g (by simp))
    rw [List.map_append] at hs
    have rep' : represented (w.map (nrm u)) (nrm u (physical_gv w g)) ∨
        ((if physical_isNot g then 0 else 1)=1 ∧ witness u (w.map (nrm u)) (nrm u (physical_gv w g))) :=
      rep.imp id (fun h => ⟨by simp [h.1],h.2⟩)
    obtain ⟨l,T,hl,hu,hT⟩ := physical_pull_gate ht rep' hs
    refine ⟨l,T,?_,hu,hT⟩
    rw [List.countP_cons]
    cases hn : physical_isNot g <;> simp [hn] at hl ⊢ <;> omega

private lemma physical_b_read (i) (w : List Sig) (j : Nat) :
    (w.map (bit i)).getD j false = bit i (w.getD j zero) := by
  simp only [List.getD_eq_getElem?_getD,List.getElem?_map]
  cases w[j]? with
  | none => exact (physical_bit_zero _).symm
  | some a => rfl

private lemma physical_run_bit (i) (g : Gate) (w : List Sig)
    (hg : g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp)) :
    bit i (physical_gv w g) = g.op.eval (g.inputs.map fun j => (w.map (bit i)).getD j false) := by
  obtain ⟨o,l⟩ := g
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hg
  simp only [physical_b_read]
  rcases hg with rfl | rfl | rfl
  · induction l with
    | nil => exact physical_bit_one _
    | cons a l ih =>
      change bit i (prime false _ _) = (_ && _)
      rw [bit_prime]; exact congrArg (fun x => bit i (w.getD a zero) && x) ih
  · induction l with
    | nil => exact physical_bit_zero _
    | cons a l ih =>
      change bit i (prime true _ _) = (_ || _)
      rw [bit_prime]; exact congrArg (fun x => bit i (w.getD a zero) || x) ih
  · cases l with
    | nil =>
      change bit i (neg zero) = !false
      rw [physical_bit_neg,physical_bit_zero]
    | cons a l => exact physical_bit_neg _ _

private lemma physical_execute_bits (gs : List Gate) (i) (w : List Sig)
    (hg : ∀ g ∈ gs, g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp)) :
    (physical_execute gs w).map (bit i) =
    gs.foldl (fun (l : List Bool) g => l++[g.op.eval (g.inputs.map fun j => l.getD j false)]) (w.map (bit i)) := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    change (physical_execute gs (w++[physical_gv w g])).map _ = _
    rw [ih _ (fun a ha => hg a (by simp [ha]))]
    simp only [List.foldl_cons,List.map_append,List.map_singleton,physical_run_bit i g w (hg g (by simp))]

lemma physical_lower_bound {roots : List Sig} {T : Sig} {L : Nat}
    (hp : proper T) (hT : plainWord T = true) (hroots : roots.all plainWord = true)
    (lower : Lower true roots T L) (C : Circuit)
    (legal : PEqualNP.MetaComplexity.FanInTwo C)
    (computes : ∀ r : Row, C.eval (roots.map (bit r)) = bit r T) :
    L ≤ C.gates.countP (fun g => !physical_isNot g) := by
  classical
  have goalEq : (physical_execute C.gates roots).getD C.output zero = T := by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    let r : Row := ⟨j, hj⟩
    have evalEq : bit r ((physical_execute C.gates roots).getD C.output zero) =
        C.eval (roots.map (bit r)) := by
      rw [←physical_b_read, physical_execute_bits _ _ _ (fun g hg => (legal g hg).1)]
      rfl
    exact evalEq.trans (computes r)
  have out := physical_get_rep (u := true) (physical_execute C.gates roots) C.output
  rw [goalEq] at out
  unfold Repr at out
  have ht : bit 0 T = false := by simpa [plainWord] using hT
  rw [nrm_id ht] at out
  obtain ⟨k, S, hk, run, sub⟩ := physical_extract (u := true) C.gates roots legal
    (by simp) hp (out.resolve_right (fun hn => hn hp))
  rw [nrm_map hroots] at sub
  have steps := list_run run S.toList (Finset.nodup_toList _) (by simp)
  have supplied : supply true (roots.map observe) (S.toList.map observe) := by
    intro f hf
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hf
    exact Or.inl (List.mem_map_of_mem (sub a (by simpa using ha)))
  obtain ⟨q, bank, built, hit, limit⟩ := contraction (observe_proper hp)
    steps (roots.map observe) Reach.start supplied
  have bound := lower q bank built hit
  omega

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
lemma originalG_input_rows : ∀ r : Row,
    (rootsW originalGRoots).map (bit r) =
      List.ofFn (fun i : Fin 7 => r.val.testBit i.val) := by
  decide

lemma posted_binary_lower (L : Nat)
    (lower : LowN originalGRoots originalGWord L) (C : Circuit)
    (legal : PEqualNP.MetaComplexity.FanInTwo C)
    (computes : ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = postedEdgeFun x) :
    L ≤ C.gates.countP (fun g => !physical_isNot g) := by
  have base := baseOK_ok originalG_baseOK
  apply physical_lower_bound base.prop base.plain base.plainR lower C legal
  intro r
  rw [originalG_input_rows r]
  exact (computes (fun i => r.val.testBit i.val)).trans (originalG_posted_table r)

def graphWitness14Gates : List Gate :=
  [⟨GateOp.or, [0, 1]⟩, ⟨GateOp.or, [0, 4]⟩,
   ⟨GateOp.or, [1, 5]⟩, ⟨GateOp.or, [4, 5]⟩,
   ⟨GateOp.or, [0, 2]⟩, ⟨GateOp.or, [11, 3]⟩,
   ⟨GateOp.or, [12, 5]⟩, ⟨GateOp.and, [13, 6]⟩,
   ⟨GateOp.and, [3, 9]⟩, ⟨GateOp.and, [2, 8]⟩,
   ⟨GateOp.and, [7, 10]⟩, ⟨GateOp.or, [14, 15]⟩,
   ⟨GateOp.or, [18, 16]⟩, ⟨GateOp.or, [19, 17]⟩]

lemma graphWitness14_basis : ∀ g ∈ graphWitness14Gates,
    (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
  simp [graphWitness14Gates]

lemma graphWitness14_length : graphWitness14Gates.length = 14 := rfl

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
lemma graphWitness14_correct : ∀ x : Fin 7 → Bool,
    Circuit.eval ⟨graphWitness14Gates, 20⟩ (List.ofFn x) = postedEdgeFun x := by
  decide

lemma graph_replacement_of_fourteen_le (k : ℕ) (hk : 14 ≤ k) :
    ∃ (gs : List Gate) (out : ℕ),
      (∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) ∧
      gs.length ≤ k ∧
      ∀ x : Fin 7 → Bool, Circuit.eval ⟨gs, out⟩ (List.ofFn x) = postedEdgeFun x :=
  ⟨graphWitness14Gates, 20, graphWitness14_basis,
    by simpa only [graphWitness14_length] using hk, graphWitness14_correct⟩

lemma physical_count_lt_of_not (gs : List Gate)
    (hasNot : ∃ g ∈ gs, g.op = GateOp.not) :
    gs.countP (fun g => !physical_isNot g) < gs.length := by
  by_contra! hn
  have eq : gs.countP (fun g => !physical_isNot g) = gs.length :=
    Nat.le_antisymm List.countP_le_length hn
  have all := List.countP_eq_length.mp eq
  obtain ⟨g, hg, hop⟩ := hasNot
  simpa [physical_isNot, hop] using all g hg

lemma positive_replacement_of_lowN13
    (lower : LowN originalGRoots originalGWord 13) (C : Circuit)
    (legal : PEqualNP.MetaComplexity.FanInTwo C)
    (computes : ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = postedEdgeFun x) :
    ∃ (gs : List Gate) (out : Nat),
      (∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) ∧
      gs.length ≤ C.gates.length ∧
      ∀ x : Fin 7 → Bool, Circuit.eval ⟨gs, out⟩ (List.ofFn x) = postedEdgeFun x := by
  by_cases hasNot : ∃ g ∈ C.gates, g.op = GateOp.not
  · have bound := posted_binary_lower 13 lower C legal computes
    have strict := physical_count_lt_of_not C.gates hasNot
    exact graph_replacement_of_fourteen_le _ (by omega)
  · refine ⟨C.gates, C.output, ?_, Nat.le_refl _, computes⟩
    intro g hg
    refine ⟨?_, (legal g hg).2⟩
    rcases (legal g hg).1 with ha | ho | hn
    · exact Or.inl ha
    · exact Or.inr ho
    · exact False.elim (hasNot ⟨g, hg, hn⟩)

end RestrictionSixProof

end PEqualNP.Outside.L_meta_10760

namespace PEqualNP.Outside.L_meta_10760.RestrictionSixProof

lemma unit_mass_append {R} (a b : List (Wire R)) : mass (a++b) = mass a + mass b := by
  simp [mass]

lemma unit_mass_constants {R} (xs : List (Wire R)) (hc : ∀ x ∈ xs, Constant x) :
    mass xs = xs.length := by
  induction xs with
  | nil => simp [mass]
  | cons a xs ih =>
    have ha := hc a (by simp)
    simp only [mass_cons,List.length_cons,cost,ite_eq_left ha,ih (fun x hx => hc x (by simp [hx]))]
    omega

lemma lower_slice_rows {u} {roots other : List Sig} {T G : Sig}
    (pT : proper T) (nT : plainWord T = true) (nR : roots.all plainWord = true)
    (pG : proper G) (rows : Row → Row)
    (target_eq : restrictRows rows (observe T) = observe G)
    (covered : ∀ a ∈ roots, Available u (other.map observe) (restrictRows rows (observe a)))
    (singles : Finset Sig) (necessary : ∀ a ∈ singles, Essential T roots a)
    (constant : ∀ a ∈ singles, Constant (restrictRows rows (observe a)))
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
  have fe : front.toFinset = S := by
    ext a
    simp [front,Finset.union_sdiff_of_subset subS]
  have run' := list_run run front nd fe
  have supp : supply u (other.map observe) ((front.map observe).map (restrictRows rows)) := by
    intro v hv
    obtain ⟨_,hm,rfl⟩ := List.mem_map.mp hv
    obtain ⟨a,hmem,rfl⟩ := List.mem_map.mp hm
    exact covered a (sub _ (fe ▸ List.mem_toFinset.mpr hmem))
  have bound := projected_bound rows run' (target_eq ▸ observe_proper pG)
    Reach.start supp (L := L) (target_eq ▸ prior)
  have massLo : singles.card ≤ mass ((front.map observe).map (restrictRows rows)) := by
    simp only [front,List.map_append,unit_mass_append]
    let xs := (singles.toList.map observe).map (restrictRows rows)
    have only : ∀ v ∈ xs, Constant v := by
      intro v hv
      obtain ⟨_,hm,rfl⟩ := List.mem_map.mp hv
      obtain ⟨a,hmem,rfl⟩ := List.mem_map.mp hm
      exact constant _ (Finset.mem_toList.mp hmem)
    have sz := unit_mass_constants xs only
    simp only [xs,List.length_map,Finset.length_toList] at sz
    change singles.card ≤ mass xs + _
    rw [sz]
    omega
  omega

def unitLiftChk (R : List Nat) (T : Nat) (R' : List Nat) (G : Nat)
    (U vs : List Nat) (w : Nat) : Bool :=
  decide (W T ≠ zero ∧ W T ≠ one) && plainWord (W T) && (rootsW R).all plainWord &&
  decide (W G ≠ zero ∧ W G ≠ one) && decide (rootsW U).Nodup &&
  (List.range 128).all (fun r => let q := rowOf vs w r
    Nat.blt q 128 && (T.testBit q == G.testBit r)) &&
  R.all (fun i => (List.range 128).all (fun r => !((xN i).testBit (rowOf vs w r))) ||
    (List.range 128).all (fun r => (xN i).testBit (rowOf vs w r)) ||
    R'.any (fun j => (List.range 128).all (fun r =>
      (xN i).testBit (rowOf vs w r) == (xN j).testBit r))) &&
  U.all (fun i => Nat.blt (1 <<< i) 128 && (T.testBit 0 != T.testBit (1 <<< i)) &&
    R.all (fun j => j == i || (xN j).testBit 0 == (xN j).testBit (1 <<< i)) &&
    (List.range 128).all (fun r => !((xN i).testBit (rowOf vs w r))))

lemma mkUnitLift {R T R' G U vs w L}
    (prior : LowN R' G L) (checked : unitLiftChk R T R' G U vs w = true) :
    LowN R T (L + U.length) := by
  simp only [unitLiftChk,Bool.and_eq_true,List.all_eq_true,List.mem_range,
    Bool.or_eq_true,beq_iff_eq,Bool.not_eq_true',List.any_eq_true,Nat.blt_eq,
    decide_eq_true_eq,bne_iff_ne] at checked
  obtain ⟨⟨⟨⟨⟨⟨⟨pT,nT⟩,nR⟩,pG⟩,ndU⟩,hr⟩,hR⟩,hU⟩ := checked
  let rows : Row → Row := fun r => ⟨rowOf vs w r.val,(hr r.val r.isLt).1⟩
  have fe (r : Row) (a : Nat) : bit (rows r) (W a) = a.testBit (rowOf vs w r.val) := bit_W _ _
  have target_eq : restrictRows rows (observe (W T)) = observe (W G) := by
    funext r
    exact (fe r T).trans ((hr r.val r.isLt).2.trans (bit_W r G).symm)
  have covered : ∀ a ∈ rootsW R,
      Available true ((rootsW R').map observe) (restrictRows rows (observe a)) := by
    intro a ha
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp ha
    rcases hR i hi with (h | h) | ⟨j,hj,h⟩
    · exact Or.inr (Or.inl ⟨false,funext fun r => (fe r _).trans (h r.val r.isLt)⟩)
    · exact Or.inr (Or.inl ⟨true,funext fun r => (fe r _).trans (h r.val r.isLt)⟩)
    · have e : restrictRows rows (observe (W (xN i))) = observe (W (xN j)) := by
        funext r
        exact (fe r _).trans ((h r.val r.isLt).trans (bit_W r _).symm)
      rw [e]
      exact Or.inl (List.mem_map_of_mem (List.mem_map_of_mem hj))
  have necessary : ∀ a ∈ (rootsW U).toFinset, Essential (W T) (rootsW R) a := by
    intro a ha
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp ha)
    obtain ⟨⟨⟨hbound,hdiff⟩,hisolate⟩,hconstant⟩ := hU i hi
    refine ⟨0,⟨1 <<< i,hbound⟩,?_,?_⟩
    · simpa only [bit_W,Fin.val_zero] using hdiff
    · intro v hv hne
      obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hv
      rcases hisolate j hj with he | he
      · exact False.elim (hne (by subst j; rfl))
      · simpa only [bit_W,Fin.val_zero] using he
  have constant : ∀ a ∈ (rootsW U).toFinset, Constant (restrictRows rows (observe a)) := by
    intro a ha
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp ha)
    refine ⟨false,funext fun r => ?_⟩
    exact (fe r _).trans ((hU i hi).2 r.val r.isLt)
  have result := lower_slice_rows pT nT (List.all_eq_true.mpr nR) pG rows target_eq covered
    (rootsW U).toFinset necessary constant L prior
  have cardU : (rootsW U).toFinset.card = U.length := by
    rw [List.toFinset_card_of_nodup ndU]
    simp only [rootsW,List.length_map]
  change Lower true (rootsW R) (W T) (L + U.length)
  rw [← cardU]
  exact result

end PEqualNP.Outside.L_meta_10760.RestrictionSixProof


namespace PEqualNP.Outside.L_meta_10760.RestrictionSixProof

def freezeRow (free one r : Nat) : Nat := (r &&& free) ||| one

def freezeSliceChk (R : List Nat) (T : Nat) (F : List Nat)
    (B d free one : Nat) : Bool :=
  F.all (fun v => R.contains v) &&
  (List.range 128).all (fun r => let q := freezeRow free one r
    Nat.blt q 128 && d.testBit q && (T.testBit q == B.testBit r)) &&
  R.all (fun i => (List.range 128).all (fun r => !((xN i).testBit (freezeRow free one r))) ||
    (List.range 128).all (fun r => (xN i).testBit (freezeRow free one r)) ||
    F.any (fun j => (List.range 128).all (fun r =>
      (xN i).testBit (freezeRow free one r) == (xN j).testBit r)))

lemma mkFreezeSlice {R T F B d free one L}
    (prior : LowN F B L) (positive : 0 < L)
    (checked : freezeSliceChk R T F B d free one = true) : SliceN R T (d, L, F) := by
  simp only [freezeSliceChk, Bool.and_eq_true, List.all_eq_true, List.mem_range,
    Bool.or_eq_true, beq_iff_eq, Bool.not_eq_true', List.any_eq_true, Nat.blt_eq,
    List.contains_eq_mem, decide_eq_true_eq] at checked
  obtain ⟨⟨hF, hr⟩, hR⟩ := checked
  let f : Row → Row := fun r => ⟨freezeRow free one r.val, (hr r.val r.isLt).1.1⟩
  have fe (r : Row) (a : Nat) : bit (f r) (W a) = a.testBit (freezeRow free one r.val) :=
    bit_W _ _
  have obs : restrictRows f (observe (W T)) = observe (W B) := by
    funext r
    exact (fe r T).trans ((hr r.val r.isLt).2.trans (bit_W r B).symm)
  refine ⟨⟨f, rootsW F, ?_, ?_, ?_, ?_⟩, hF⟩
  · intro r
    exact (fe r d).trans (hr r.val r.isLt).1.2
  · intro a ha
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp ha
    rcases hR i hi with (h | h) | ⟨j, hj, h⟩
    · exact Or.inr (Or.inl ⟨false, funext fun r => (fe r _).trans (h r.val r.isLt)⟩)
    · exact Or.inr (Or.inl ⟨true, funext fun r => (fe r _).trans (h r.val r.isLt)⟩)
    · have eq : restrictRows f (observe (W (xN i))) = observe (W (xN j)) := by
        funext r
        exact (fe r _).trans ((h r.val r.isLt).trans (bit_W r _).symm)
      rw [eq]
      exact Or.inl (List.mem_map_of_mem (List.mem_map_of_mem hj))
  · rw [obs]
    intro constant
    have impossible := prior 0 _ Reach.start (Or.inr (Or.inl constant))
    omega
  · rw [obs]
    exact prior

end PEqualNP.Outside.L_meta_10760.RestrictionSixProof


namespace PEqualNP.Outside.L_meta_10760.RestrictionSixProof.PackedRestrictions

abbrev BaseD := List Nat × Nat × Nat
abbrev RecordD := Nat × List Nat × Nat × List Nat × List Nat × Nat × Nat × Nat

end PEqualNP.Outside.L_meta_10760.RestrictionSixProof.PackedRestrictions

namespace PEqualNP.Outside.L_meta_10760.RestrictionSixProof.Restriction92

open PackedRestrictions

def compactBases : List BaseD := [
  ([0,1,2],0xe8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8,4),
  ([0,1,2,3],0xeac8eac8eac8eac8eac8eac8eac8eac8,4),
  ([0,1,2,3],0xeae8eae8eae8eae8eae8eae8eae8eae8,5),
  ([0,1,2,3],0xeee8eee8eee8eee8eee8eee8eee8eee8,5),
  ([0,1,2,3,4],0xfeeafcc8feeafcc8feeafcc8feeafcc8,7),
  ([0,1,2,3,4],0xfeeafce8feeafce8feeafce8feeafce8,7),
  ([0,1,2,3,4],0xfeeefac0feeefac0feeefac0feeefac0,7),
  ([0,1,2,3,4],0xfeeefac8feeefac8feeefac8feeefac8,6),
  ([0,1,2,3,4],0xfeeefae8feeefae8feeefae8feeefae8,7),
  ([1,2,3,4,5,6],0xfffffffffffcfff0fffcffccfcfccc00,10),
  ([0,2,3,4,5,6],0xfffffffffffafffafffaffaafafaa0a0,10),
  ([0,1,3,4,5,6],0xffffffffffeeffaaffeeffeeeeeecc00,10)]

def compactRecords : List RecordD := [
  (0x55555555555555555555555555555555,[1,2,3,4,5,6],0xfffffffffffcfff0fffcffccfcfccc00,[],[0,1,2,3,4,5,6],126,0,9),
  (0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f,[0,1,3,4,5,6],0xffffffffffeeffaaffeeffeeeeeecc00,[],[0,1,2,3,4,5,6],123,0,11),
  (0xff00ff00ff00ff00ff00ff00ff00ff,[0,1,2,4,5,6],0xfffffffffefefafafefeeeeefefea0a0,[],[5,4,3,2,1,0,6],119,0,11),
  (0xffffffff00000000ffffffff,[0,1,2,3,4,6],0xfffefffafffefffafefeeca0fefeeca0,[],[5,6,1,0,3,2,4],95,0,9),
  (0x33003300,[0,2,4],0xfafaa0a0fafaa0a0fafaa0a0fafaa0a0,[],[0,2,4],21,8,0),
  (0x505000005050,[1,3,5],0xffccffcccc00cc00ffccffcccc00cc00,[],[1,3,5],42,4,0),
  (0x33333333333333333333333333333333,[0,2,3,4,5,6],0xfffffffffffafffafffaffaafafaa0a0,[],[0,1,2,3,4,5,6],125,0,10),
  (0x1010000010100000101000001010000,[3,5,6],0xffffffffff00ff00ff00ff0000000000,[],[3,5,6],104,16,0),
  (0x50500000505,[1,3,5],0xffccffcccc00cc00ffccffcccc00cc00,[],[1,3,5],42,0,0),
  (0x5555555555555555,[1,2,3,4,5],0xfffcffccfcfccc00fffcffccfcfccc00,[],[4,1,3,5,2],62,0,4),
  (0x330033,[0,2,4],0xfafaa0a0fafaa0a0fafaa0a0fafaa0a0,[],[0,2,4],21,0,0),
  (0xcc00000000000000cc,[0,2,6],0xfafafafafafafafaa0a0a0a0a0a0a0a0,[],[0,2,6],69,2,0),
  (0xffff0000ffff0000ffff0000ffff,[0,1,2,3,5,6],0xfffffffffffafffaffeeffeeeca0eca0,[],[6,4,0,1,2,3,5],111,0,10),
  (0x555555550000000055555555,[1,2,3,4,6],0xfffcfff0fffcfff0fcfccc00fcfccc00,[],[1,2,6,3,4],94,0,6),
  (0xffffffff,[0,1,2,3,4],0xfefeeca0fefeeca0fefeeca0fefeeca0,[],[1,4,0,2,3],31,0,4),
  (0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,[0,1,3,4,5,6],0xffffffffffffffffffffffeeffffeeaa,[0,4,6],[1,3,5],123,4,0),
  (0x5050505050505050,[1,3,4,5],0xffffffccffffcc00ffffffccffffcc00,[4],[1,3,5],58,4,0),
  (0xff00ff00ff00ff00ff00ff00ff00ff00,[0,1,2,4,5,6],0xfffffffffffffffffffffffffefeecec,[1,5,6],[0,2,4],119,8,0),
  (0xff00ff00,[0,1,2,4],0xfefeececfefeececfefeececfefeecec,[1],[0,2,4],23,8,0),
  (0xcccccccccccccccccccccccccccccccc,[0,2,3,4,5,6],0xfffffffffffffffaffffffffffffffa0,[3,4,5],[0,2,6],125,2,0),
  (0x3333333333333333,[0,2,3,4,5],0xfffaffaafafaa0a0fffaffaafafaa0a0,[],[5,0,2,4,3],61,0,4),
  (0xf0f0f0f000000000f0f0f0f,[0,1,3,4,6],0xffeeffaaffeeffaaeeeecc00eeeecc00,[],[0,1,3,6,4],91,0,6),
  (0x101000001010000010100000101,[3,5,6],0xffffffffff00ff00ff00ff0000000000,[],[3,5,6],104,0,0),
  (0x3000000030000000300000003,[0,5,6],0xffffffffaaaaaaaaaaaaaaaa00000000,[],[0,5,6],97,0,0),
  (0x550055005500550055005500550055,[1,2,4,5,6],0xfffffffffcfcf0f0fcfcccccfcfc0000,[],[1,2,6,5,4],118,0,6),
  (0xffff0000ffff,[0,1,2,3,5],0xffeeffeeeca0eca0ffeeffeeeca0eca0,[],[0,5,1,3,2],47,0,4),
  (0xf0f0f0f0f0f0f0f0,[0,1,3,4,5],0xffffffeeffffeeaaffffffeeffffeeaa,[0,4],[1,3,5],59,4,0),
  (0x5050505050505050505050505050505,[1,3,4,5,6],0xffffffffffccff00ffccffcccccccc00,[],[1,3,5,6,4],122,0,5),
  (0x11111111111111111111111111111111,[2,3,4,5,6],0xfffffffffff0fff0fff0ff00f0f00000,[],[2,6,3,5,4],124,0,4),
  (0xcc00cc0000000000cc00cc,[0,2,4,6],0xfffffafafffffafaffffa0a0ffffa0a0,[4],[0,2,6],85,2,0),
  (0x5050000050500000505000005050000,[1,3,5,6],0xffffffffffccffccffccffcccccccccc,[1],[3,5,6],106,16,0),
  (0x330000000000000033,[0,2,6],0xfafafafafafafafaa0a0a0a0a0a0a0a0,[],[0,2,6],69,0,0),
  (0xff00ff00ff00ff00,[0,1,2,4,5],0xfffffffffefeececfffffffffefeecec,[1,5],[0,2,4],55,8,0),
  (0xffff0000ffff0000ffff0000ffff0000,[0,1,2,3,5,6],0xfffffffffffefffefffefffefefefefe,[0,1,2],[3,5,6],111,16,0),
  (0xf0f00000f0f00000f0f00000f0f,[0,1,3,5,6],0xffffffffffaaffaaffeeffeecc00cc00,[],[5,3,6,0,1],107,0,8),
  (0x50505050505050505050505050505050,[1,3,4,5,6],0xffffffffffffffffffffffccffffcc00,[4,6],[1,3,5],122,4,0),
  (0x330033000000000033003300,[0,2,4,6],0xfffffffffffffffffafaa0a0fafaa0a0,[6],[0,2,4],85,8,0),
  (0x11110000111100001111000011110000,[2,3,5,6],0xfffffffffff0fff0fff0fff0f0f0f0f0,[2],[3,5,6],108,16,0),
  (0x330033003300330033003300330033,[0,2,4,5,6],0xfffffffffafafafafafaaaaafafaa0a0,[],[0,2,6,5,4],117,0,8),
  (0x55555555,[1,2,3,4],0xfcfccc00fcfccc00fcfccc00fcfccc00,[],[1,4,2,3],30,0,1),
  (0x3030303030303030303030303030303,[0,3,4,5,6],0xffffffffffaaffaaffaaffaaaaaa0000,[],[0,5,6,3,4],121,0,5),
  (0xff00ff0000000000ff00ff,[0,1,2,4,6],0xfefefafafefefafafefea0a0fefea0a0,[],[4,0,2,6,1],87,0,5),
  (0x33330000333300003333000033330000,[0,2,3,5,6],0xfffffffffffafffafffafffafafafafa,[0,2],[3,5,6],109,16,0),
  (0xcccc000000000000cccc,[0,2,3,6],0xfffafffafffafffaffa0ffa0ffa0ffa0,[3],[0,2,6],77,2,0),
  (0x55550000555500005555000055550000,[1,2,3,5,6],0xfffffffffffcfffcfffcfffcfcfcfcfc,[1,2],[3,5,6],110,16,0),
  (0x505050505050505,[1,3,4,5],0xffccffcccccccc00ffccffcccccccc00,[],[1,3,5,4],58,0,2),
  (0x5050000050500000505000005050,[1,3,5,6],0xffffffffffffffffffccffcccc00cc00,[6],[1,3,5],106,4,0),
  (0x3300330033003300,[0,2,4,5],0xfffffffffafaa0a0fffffffffafaa0a0,[5],[0,2,4],53,8,0),
  (0x33003300330033003300330033003300,[0,2,4,5,6],0xfffffffffffffffffffffffffafaa0a0,[5,6],[0,2,4],117,8,0),
  (0xf0f00000f0f0,[0,1,3,5],0xffeeffeeeeaaeeaaffeeffeeeeaaeeaa,[0],[1,3,5],43,4,0),
  (0xcccc0000cccc0000cccc0000cccc,[0,2,3,5,6],0xfffffffffffafffaffffffffffa0ffa0,[3,5],[0,2,6],109,2,0),
  (0x3030000030300000303000003030000,[0,3,5,6],0xffffffffffaaffaaffaaffaaaaaaaaaa,[0],[3,5,6],105,16,0),
  (0xffff000000000000ffff,[0,1,2,3,6],0xfffafffafffafffaeca0eca0eca0eca0,[],[3,6,0,2,1],79,0,4),
  (0xff00ff0000000000ff00ff00,[0,1,2,4,6],0xfffffffffffffffffefeececfefeecec,[1,6],[0,2,4],87,8,0),
  (0xcc000000cc000000cc000000cc,[0,2,5,6],0xfffffffffafafafaffffffffa0a0a0a0,[5],[0,2,6],101,2,0),
  (0xf0f0f0f0f0f0f0f,[0,1,3,4,5],0xffeeffeeeeeecc00ffeeffeeeeeecc00,[],[1,5,0,4,3],59,0,7),
  (0x5555000055550000555500005555,[1,2,3,5,6],0xfffffffffff0fff0ffccffcccc00cc00,[],[6,3,5,1,2],110,0,5),
  (0xf0f00000f0f00000f0f00000f0f0,[0,1,3,5,6],0xffffffffffffffffffeeffeeeeaaeeaa,[0,6],[1,3,5],107,4,0),
  (0xf0f00000f0f00000f0f00000f0f0000,[0,1,3,5,6],0xffffffffffeeffeeffeeffeeeeeeeeee,[0,1],[3,5,6],107,16,0),
  (0x3333000033330000333300003333,[0,2,3,5,6],0xfffffffffffafffaffaaffaaa0a0a0a0,[],[6,0,5,3,2],109,0,8),
  (0xcccccccc00000000cccccccc,[0,2,3,4,6],0xfffffffafffffffaffffffa0ffffffa0,[3,4],[0,2,6],93,2,0),
  (0x333333330000000033333333,[0,2,3,4,6],0xfffafffafffafffafafaa0a0fafaa0a0,[],[6,0,2,4,3],93,0,5),
  (0xff00ff,[0,1,2,4],0xfefea0a0fefea0a0fefea0a0fefea0a0,[],[4,0,2,1],23,0,2),
  (0xcc00cc00cc00cc00cc00cc00cc00cc,[0,2,4,5,6],0xfffffffffffffafaffffffffffffa0a0,[4,5],[0,2,6],117,2,0),
  (0xff000000ff000000ff000000ff,[0,1,2,5,6],0xfffffffffafafafaeeeeeeeea0a0a0a0,[],[5,0,6,2,1],103,0,5),
  (0xff00ff00ff00ff,[0,1,2,4,5],0xfefeeeeefefea0a0fefeeeeefefea0a0,[],[0,4,1,5,2],55,0,7),
  (0xf0f0f0f,[0,1,3,4],0xeeeecc00eeeecc00eeeecc00eeeecc00,[],[1,4,0,3],27,0,1),
  (0x111111110000000011111111,[2,3,4,6],0xfff0fff0fff0fff0f0f00000f0f00000,[],[2,6,3,4],92,0,1),
  (0x50505050000000005050505,[1,3,4,6],0xffccff00ffccff00cccccc00cccccc00,[],[1,3,6,4],90,0,1),
  (0x55005500550055,[1,2,4,5],0xfcfcccccfcfc0000fcfcccccfcfc0000,[],[1,4,2,5],54,0,1),
  (0x303030303030303,[0,3,4,5],0xffaaffaaaaaa0000ffaaffaaaaaa0000,[],[0,5,3,4],57,0,1),
  (0xf000f000f000f000f000f000f000f,[0,1,4,5,6],0xffffffffeeeeaaaaeeeeeeeeeeee0000,[],[0,5,1,4,6],115,0,7),
  (0xf0f00000f0f,[0,1,3,5],0xffeeffeecc00cc00ffeeffeecc00cc00,[],[5,1,3,0],43,0,2),
  (0x5500550000000000550055,[1,2,4,6],0xfcfcf0f0fcfcf0f0fcfc0000fcfc0000,[],[2,4,1,6],86,0,1),
  (0x33003300330033,[0,2,4,5],0xfafaaaaafafaa0a0fafaaaaafafaa0a0,[],[0,2,4,5],53,0,2),
  (0x55550000000000005555,[1,2,3,6],0xfff0fff0fff0fff0cc00cc00cc00cc00,[],[6,3,1,2],78,0,1),
  (0x30003000300030003000300030003,[0,4,5,6],0xffffffffaaaaaaaaaaaaaaaaaaaa0000,[],[0,5,6,4],113,0,2),
  (0xf0000000f0000000f0000000f,[0,1,5,6],0xffffffffaaaaaaaaeeeeeeee00000000,[],[5,0,6,1],99,0,2),
  (0xf000f00000000000f000f,[0,1,4,6],0xeeeeaaaaeeeeaaaaeeee0000eeee0000,[],[0,4,1,6],83,0,1),
  (0x30303030000000003030303,[0,3,4,6],0xffaaffaaffaaffaaaaaa0000aaaa0000,[],[0,6,3,4],89,0,1),
  (0x50005000500050005000500050005,[1,4,5,6],0xffffffffcccc0000cccccccccccc0000,[],[1,5,6,4],114,0,1),
  (0xff000000ff,[0,1,2,5],0xeeeeeeeea0a0a0a0eeeeeeeea0a0a0a0,[],[0,5,1,2],39,0,1),
  (0x505000005050000050500000505,[1,3,5,6],0xffffffffff00ff00ffccffcccc00cc00,[],[3,5,1,6],106,0,3),
  (0x1111000011110000111100001111,[2,3,5,6],0xfffffffffff0fff0ff00ff0000000000,[],[6,3,5,2],108,0,2),
  (0x333300003333,[0,2,3,5],0xffaaffaaa0a0a0a0ffaaffaaa0a0a0a0,[],[0,5,3,2],45,0,1),
  (0x3300330000000000330033,[0,2,4,6],0xfafafafafafafafafafaa0a0fafaa0a0,[],[0,2,4,6],85,0,3),
  (0x33330000000000003333,[0,2,3,6],0xfffafffafffafffaa0a0a0a0a0a0a0a0,[],[6,0,2,3],77,0,2),
  (0x110011001100110011001100110011,[2,4,5,6],0xfffffffff0f0f0f0f0f00000f0f00000,[],[2,6,5,4],116,0,1),
  (0xf0f0000000000000f0f,[0,1,3,6],0xffaaffaaffaaffaacc00cc00cc00cc00,[],[3,6,0,1],75,0,1),
  (0x55000000550000005500000055,[1,2,5,6],0xfffffffff0f0f0f0cccccccc00000000,[],[6,5,1,2],102,0,1),
  (0x303000003030000030300000303,[0,3,5,6],0xffffffffffaaffaaffaaffaa00000000,[],[5,6,0,3],105,0,3),
  (0x33000000330000003300000033,[0,2,5,6],0xfffffffffafafafaaaaaaaaaa0a0a0a0,[],[0,6,2,5],101,0,3)]

end PEqualNP.Outside.L_meta_10760.RestrictionSixProof.Restriction92
namespace PEqualNP.Outside.L_meta_10760.RestrictionSixProof.PackedRestrictions

def recordIndex (c : RecordD) : Nat := c.2.2.2.2.2.2.2

def recordSpec (bases : List BaseD) (c : RecordD) : SliceD :=
  let (d,F,_,U,_,_,_,i) := c
  let base := bases.getD i ([],0,0)
  (d,base.2.2 + U.length,F)

def recordCheck (R : List Nat) (T : Nat) (bases : List BaseD) (c : RecordD) : Bool :=
  let (d,F,B,U,vs,free,one,i) := c
  let base := bases.getD i ([],0,0)
  decide (i < bases.length) && unitLiftChk F B base.1 base.2.1 U vs 0 &&
    freezeSliceChk R T F B d free one && decide (0 < base.2.2 + U.length)

lemma record_sound {R : List Nat} {T : Nat} {bases : List BaseD} {c : RecordD}
    (prior : ∀ b ∈ bases, LowN b.1 b.2.1 b.2.2)
    (checked : recordCheck R T bases c = true) : SliceN R T (recordSpec bases c) := by
  obtain ⟨d,F,B,U,vs,free,one,i⟩ := c
  simp only [recordCheck,Bool.and_eq_true,decide_eq_true_eq] at checked
  obtain ⟨⟨⟨hi,hu⟩,hf⟩,hp⟩ := checked
  have hm : bases.getD i ([],0,0) ∈ bases := by
    simpa only [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hi,Option.getD_some]
      using (List.getElem_mem hi : bases[i] ∈ bases)
  exact mkFreezeSlice (mkUnitLift (prior _ hm) hu) hp hf

lemma records_sound {R : List Nat} {T : Nat} {bases : List BaseD} {records : List RecordD}
    (prior : ∀ b ∈ bases, LowN b.1 b.2.1 b.2.2)
    (checked : records.all (recordCheck R T bases) = true) :
    ∀ s ∈ records.map (recordSpec bases), SliceN R T s := by
  intro s hs
  obtain ⟨c,hc,rfl⟩ := List.mem_map.mp hs
  exact record_sound prior ((List.all_eq_true.mp checked) c hc)

end PEqualNP.Outside.L_meta_10760.RestrictionSixProof.PackedRestrictions
namespace PEqualNP.Outside.L_meta_10760.RestrictionSixProof.Restriction92

lemma compactBases_sound
    (h1 : LowN [1,2,3,4,5,6] 0xfffffffffffcfff0fffcffccfcfccc00 10)
    (h2 : LowN [0,2,3,4,5,6] 0xfffffffffffafffafffaffaafafaa0a0 10)
    (h3 : LowN [0,1,3,4,5,6] 0xffffffffffeeffaaffeeffeeeeeecc00 10) :
    ∀ b ∈ compactBases, LowN b.1 b.2.1 b.2.2 := by
  intro b hb
  simp only [compactBases,List.mem_cons,List.mem_nil_iff,or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact d55
  · exact d37
  · exact d68
  · exact d81
  · exact d258
  · exact d137
  · exact d436
  · exact d150
  · exact d167
  · exact h1
  · exact h2
  · exact h3

lemma compactSmallBases_sound :
    ∀ b ∈ compactBases.take 9, LowN b.1 b.2.1 b.2.2 := by
  intro b hb
  simp only [compactBases,List.take,List.mem_cons,List.mem_nil_iff,or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact d55
  · exact d37
  · exact d68
  · exact d81
  · exact d258
  · exact d137
  · exact d436
  · exact d150
  · exact d167

end PEqualNP.Outside.L_meta_10760.RestrictionSixProof.Restriction92

namespace PEqualNP.Outside.L_meta_10760.RestrictionSixProof.Restriction92

open PackedRestrictions

def sliceSpecs : List SliceD := compactRecords.map (recordSpec compactBases)

def compactSmallRecords : List RecordD :=
  compactRecords.filter (fun r => decide (recordIndex r < 9))

def smallSliceSpecs : List SliceD :=
  compactSmallRecords.map (recordSpec (compactBases.take 9))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma compactChecks :
    compactRecords.all (recordCheck originalGRoots originalGWord compactBases) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma compactSmallChecks :
    compactSmallRecords.all (recordCheck originalGRoots originalGWord (compactBases.take 9)) = true := by
  decide +kernel

lemma slices_sound
    (h1 : LowN [1,2,3,4,5,6] 0xfffffffffffcfff0fffcffccfcfccc00 10)
    (h2 : LowN [0,2,3,4,5,6] 0xfffffffffffafffafffaffaafafaa0a0 10)
    (h3 : LowN [0,1,3,4,5,6] 0xffffffffffeeffaaffeeffeeeeeecc00 10) :
    ∀ s ∈ sliceSpecs, SliceN originalGRoots originalGWord s :=
  records_sound (compactBases_sound h1 h2 h3) compactChecks

lemma slices_sound_small :
    ∀ s ∈ smallSliceSpecs, SliceN originalGRoots originalGWord s :=
  records_sound compactSmallBases_sound compactSmallChecks

end PEqualNP.Outside.L_meta_10760.RestrictionSixProof.Restriction92


namespace PEqualNP.Outside.L_meta_10760.RestrictionSixProof

lemma SliceN_mono_roots_target {R R' : List Nat} {T T' : Nat} {s : SliceD}
    (hs : SliceN R T s)
    (rootsSubset : ∀ v ∈ R', v ∈ R)
    (varsSubset : ∀ v ∈ s.2.2, v ∈ R')
    (target_eq : ∀ r : Row, bit r (W s.1) = true → bit r (W T') = bit r (W T)) :
    SliceN R' T' s := by
  obtain ⟨⟨f, roots, dom, base, nc, lo⟩, _⟩ := hs
  have heq : restrictRows f (observe (W T')) = restrictRows f (observe (W T)) := by
    funext r
    exact target_eq (f r) (dom r)
  refine ⟨⟨f, roots, dom, ?_, ?_, ?_⟩, varsSubset⟩
  · intro a ha
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp ha
    exact base _ (List.mem_map_of_mem (rootsSubset v hv))
  · rwa [heq]
  · rwa [heq]

def sliceTransferCheck (R' : List Nat) (T T' : Nat) (s : SliceD) : Bool :=
  s.2.2.all (fun v => decide (v ∈ R')) &&
    (List.range 128).all (fun r => !s.1.testBit r || (T'.testBit r == T.testBit r))

lemma sliceTransferCheck_sound {R R' : List Nat} {T T' : Nat} {s : SliceD}
    (hs : SliceN R T s) (rootsSubset : ∀ v ∈ R', v ∈ R)
    (checked : sliceTransferCheck R' T T' s = true) : SliceN R' T' s := by
  simp only [sliceTransferCheck, Bool.and_eq_true, List.all_eq_true,
    List.mem_range, decide_eq_true_eq, Bool.or_eq_true, Bool.not_eq_true',
    beq_iff_eq] at checked
  apply SliceN_mono_roots_target hs rootsSubset checked.1
  intro r hr
  rw [bit_W] at hr
  rw [bit_W, bit_W]
  rcases checked.2 r.val r.isLt with hzero | heq
  · rw [hr] at hzero
    contradiction
  · exact heq

lemma sliceTransferCheck_all_sound {R R' : List Nat} {T T' : Nat}
    (specs : List SliceD) (rootsSubset : ∀ v ∈ R', v ∈ R)
    (valid : ∀ s ∈ specs, SliceN R T s)
    (checked : specs.all (sliceTransferCheck R' T T') = true) :
    ∀ s ∈ specs, SliceN R' T' s := by
  intro s hs
  exact sliceTransferCheck_sound (valid s hs) rootsSubset ((List.all_eq_true.mp checked) s hs)

lemma sliceTransferCheck_filter_sound {R R' : List Nat} {T T' : Nat}
    (specs : List SliceD) (rootsSubset : ∀ v ∈ R', v ∈ R)
    (valid : ∀ s ∈ specs, SliceN R T s) :
    ∀ s ∈ specs.filter (sliceTransferCheck R' T T'), SliceN R' T' s := by
  intro s hs
  obtain ⟨hs, checked⟩ := List.mem_filter.mp hs
  exact sliceTransferCheck_sound (valid s hs) rootsSubset checked

end PEqualNP.Outside.L_meta_10760.RestrictionSixProof


namespace PEqualNP.Outside.L_meta_10760.RestrictionSixProof.Restriction92.Forests

def forest1Roots : List Nat := [1, 2, 3, 4, 5, 6]
def forest1Target : Nat := 0xfffffffffffcfff0fffcffccfcfccc00
def forest1Indices : List Nat := [5, 7, 8, 9, 13, 16, 22, 24, 27, 28, 30, 35, 37, 39, 44, 45, 46, 56, 67, 68, 69, 73, 75, 80, 82, 83, 87, 89]
def forest1Specs : List SliceD :=
  smallSliceSpecs.filter (sliceTransferCheck forest1Roots originalGWord forest1Target)

lemma forest1Roots_subset : ∀ v ∈ forest1Roots, v ∈ originalGRoots := by
  have h : forest1Roots.all (fun v => decide (v ∈ originalGRoots)) = true := by decide +kernel
  intro v hv
  exact of_decide_eq_true ((List.all_eq_true.mp h) v hv)

lemma forest1Specs_sound : ∀ s ∈ forest1Specs, SliceN forest1Roots forest1Target s :=
  sliceTransferCheck_filter_sound smallSliceSpecs forest1Roots_subset slices_sound_small

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
lemma forest1Specs_eq_indices : forest1Specs =
    forest1Indices.map (fun i => sliceSpecs.getD i (0, 0, [])) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
lemma forest1Specs_length : forest1Specs.length = 28 := by
  decide +kernel

def forest2Roots : List Nat := [0, 2, 3, 4, 5, 6]
def forest2Target : Nat := 0xfffffffffffafffafffaffaafafaa0a0
def forest2Indices : List Nat := [4, 7, 10, 11, 20, 22, 23, 28, 31, 36, 37, 38, 40, 42, 47, 48, 51, 59, 61, 67, 70, 74, 76, 79, 83, 84, 85, 86, 87, 90, 91]
def forest2Specs : List SliceD :=
  smallSliceSpecs.filter (sliceTransferCheck forest2Roots originalGWord forest2Target)

lemma forest2Roots_subset : ∀ v ∈ forest2Roots, v ∈ originalGRoots := by
  have h : forest2Roots.all (fun v => decide (v ∈ originalGRoots)) = true := by decide +kernel
  intro v hv
  exact of_decide_eq_true ((List.all_eq_true.mp h) v hv)

lemma forest2Specs_sound : ∀ s ∈ forest2Specs, SliceN forest2Roots forest2Target s :=
  sliceTransferCheck_filter_sound smallSliceSpecs forest2Roots_subset slices_sound_small

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
lemma forest2Specs_eq_indices : forest2Specs =
    forest2Indices.map (fun i => sliceSpecs.getD i (0, 0, [])) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
lemma forest2Specs_length : forest2Specs.length = 31 := by
  decide +kernel

def forest3Roots : List Nat := [0, 1, 3, 4, 5, 6]
def forest3Target : Nat := 0xffffffffffeeffaaffeeffeeeeeecc00
def forest3Indices : List Nat := [5, 7, 8, 21, 22, 23, 27, 30, 34, 40, 45, 51, 55, 58, 66, 68, 70, 71, 72, 76, 77, 78, 79, 80, 82, 88, 90]
def forest3Specs : List SliceD :=
  smallSliceSpecs.filter (sliceTransferCheck forest3Roots originalGWord forest3Target)

lemma forest3Roots_subset : ∀ v ∈ forest3Roots, v ∈ originalGRoots := by
  have h : forest3Roots.all (fun v => decide (v ∈ originalGRoots)) = true := by decide +kernel
  intro v hv
  exact of_decide_eq_true ((List.all_eq_true.mp h) v hv)

lemma forest3Specs_sound : ∀ s ∈ forest3Specs, SliceN forest3Roots forest3Target s :=
  sliceTransferCheck_filter_sound smallSliceSpecs forest3Roots_subset slices_sound_small

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
lemma forest3Specs_eq_indices : forest3Specs =
    forest3Indices.map (fun i => sliceSpecs.getD i (0, 0, [])) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
lemma forest3Specs_length : forest3Specs.length = 27 := by
  decide +kernel

def runtimeSliceGuard (deleted : Nat) (s : SliceD) : Bool :=
  decide (s.2.1 ≤ 7) && decide (s.1 &&& xN deleted = 0)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
lemma forest1RuntimeCheck : sliceSpecs.all (fun s =>
    !runtimeSliceGuard 0 s || decide (s ∈ forest1Specs)) = true := by
  decide +kernel

lemma forest1_guard_sound {s : SliceD} (hs : s ∈ sliceSpecs)
    (hLower : s.2.1 ≤ 7) (hZero : s.1 &&& xN 0 = 0) :
    SliceN forest1Roots forest1Target s := by
  have checked := (List.all_eq_true.mp forest1RuntimeCheck) s hs
  have hguard : runtimeSliceGuard 0 s = true := by
    simp [runtimeSliceGuard, hLower, hZero]
  apply forest1Specs_sound s
  simpa only [hguard, Bool.not_true, Bool.false_or, decide_eq_true_eq] using checked

lemma forest1_index_guard_sound (i : Nat) (hi : i < sliceSpecs.length)
    (hLower : (sliceSpecs.getD i (0, 0, [])).2.1 ≤ 7)
    (hZero : (sliceSpecs.getD i (0, 0, [])).1 &&& xN 0 = 0) :
    SliceN forest1Roots forest1Target (sliceSpecs.getD i (0, 0, [])) := by
  apply forest1_guard_sound ?_ hLower hZero
  rw [List.getD_eq_getElem _ _ hi]
  exact List.getElem_mem hi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
lemma forest2RuntimeCheck : sliceSpecs.all (fun s =>
    !runtimeSliceGuard 1 s || decide (s ∈ forest2Specs)) = true := by
  decide +kernel

lemma forest2_guard_sound {s : SliceD} (hs : s ∈ sliceSpecs)
    (hLower : s.2.1 ≤ 7) (hZero : s.1 &&& xN 1 = 0) :
    SliceN forest2Roots forest2Target s := by
  have checked := (List.all_eq_true.mp forest2RuntimeCheck) s hs
  have hguard : runtimeSliceGuard 1 s = true := by
    simp [runtimeSliceGuard, hLower, hZero]
  apply forest2Specs_sound s
  simpa only [hguard, Bool.not_true, Bool.false_or, decide_eq_true_eq] using checked

lemma forest2_index_guard_sound (i : Nat) (hi : i < sliceSpecs.length)
    (hLower : (sliceSpecs.getD i (0, 0, [])).2.1 ≤ 7)
    (hZero : (sliceSpecs.getD i (0, 0, [])).1 &&& xN 1 = 0) :
    SliceN forest2Roots forest2Target (sliceSpecs.getD i (0, 0, [])) := by
  apply forest2_guard_sound ?_ hLower hZero
  rw [List.getD_eq_getElem _ _ hi]
  exact List.getElem_mem hi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
lemma forest3RuntimeCheck : sliceSpecs.all (fun s =>
    !runtimeSliceGuard 2 s || decide (s ∈ forest3Specs)) = true := by
  decide +kernel

lemma forest3_guard_sound {s : SliceD} (hs : s ∈ sliceSpecs)
    (hLower : s.2.1 ≤ 7) (hZero : s.1 &&& xN 2 = 0) :
    SliceN forest3Roots forest3Target s := by
  have checked := (List.all_eq_true.mp forest3RuntimeCheck) s hs
  have hguard : runtimeSliceGuard 2 s = true := by
    simp [runtimeSliceGuard, hLower, hZero]
  apply forest3Specs_sound s
  simpa only [hguard, Bool.not_true, Bool.false_or, decide_eq_true_eq] using checked

lemma forest3_index_guard_sound (i : Nat) (hi : i < sliceSpecs.length)
    (hLower : (sliceSpecs.getD i (0, 0, [])).2.1 ≤ 7)
    (hZero : (sliceSpecs.getD i (0, 0, [])).1 &&& xN 2 = 0) :
    SliceN forest3Roots forest3Target (sliceSpecs.getD i (0, 0, [])) := by
  apply forest3_guard_sound ?_ hLower hZero
  rw [List.getD_eq_getElem _ _ hi]
  exact List.getElem_mem hi

end PEqualNP.Outside.L_meta_10760.RestrictionSixProof.Restriction92.Forests


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

namespace PEqualNP.Outside.L_meta_10760.AutoPool
open RestrictionSixProof

lemma autoCut_sound_any {R : List Nat} {T k : Nat} {ws : List Nat} {s : SliceD}
    (hs : SliceN R T s) (nd : (ws.map W).Nodup)
    (h : autoCut k ws s = true) :
    Impossible true (W T) k (ws.map W).toFinset := by
  cases ws with
  | nil =>
      intro n hn run
      cases n with
      | zero => simp [Live] at run
      | succ n =>
          obtain ⟨U,a,b,d,hd,hS,hrest⟩ := run
          have ha := congrArg (fun S : Finset Sig => a ∈ S) hS
          simpa using ha
  | cons z rest =>
      have hz : nb 1 z 0 = z := by simp [nb]
      have hc := RestrictionSixProof.autoCut_sound
        (R := R) (T := T) (s := s) (k := k) (rest := rest)
        (a := z) (b := 0) (o := 1) (ka := false) (kb := false) hs
      simp only [hz, kept, kidW] at hc
      exact hc nd h

end PEqualNP.Outside.L_meta_10760.AutoPool

namespace PEqualNP.Outside.L_meta_10760.RestrictionDAG

lemma indexed_sound {α : Type} (node : Nat → α) (P : α → Prop) (count : Nat)
    (step : ∀ i, i < count → (∀ j, j < i → P (node j)) → P (node i)) :
    ∀ i, i < count → P (node i) := by
  intro i
  induction i using Nat.strong_induction_on with
  | ind i ih =>
    intro hi
    exact step i hi (fun j hj => ih j hj (hj.trans hi))

lemma indexed_checks_sound {α : Type} (node : Nat → α) (P : α → Prop)
    (count : Nat) (check : Nat → Bool)
    (checked : ∀ i, i < count → check i = true)
    (step : ∀ i, i < count → (∀ j, j < i → P (node j)) →
      check i = true → P (node i)) : ∀ i, i < count → P (node i) := by
  exact indexed_sound node P count (fun i hi prior => step i hi prior (checked i hi))

open RestrictionSixProof

lemma legacy_indexed_sound (T count : Nat) (node : Nat → Nat × List Nat)
    (step : ∀ i, i < count →
      (∀ j, j < i → Impossible true (W T) (node j).1 ((node j).2.map W).toFinset) →
      Impossible true (W T) (node i).1 ((node i).2.map W).toFinset) :
    ∀ i, i < count → Impossible true (W T) (node i).1 ((node i).2.map W).toFinset :=
  indexed_sound node (fun q => Impossible true (W T) q.1 (q.2.map W).toFinset) count step

lemma legacy_indexed_checks_sound (T count : Nat) (node : Nat → Nat × List Nat)
    (check : Nat → Bool) (checked : ∀ i, i < count → check i = true)
    (step : ∀ i, i < count →
      (∀ j, j < i → Impossible true (W T) (node j).1 ((node j).2.map W).toFinset) →
      check i = true → Impossible true (W T) (node i).1 ((node i).2.map W).toFinset) :
    ∀ i, i < count → Impossible true (W T) (node i).1 ((node i).2.map W).toFinset :=
  indexed_checks_sound node (fun q => Impossible true (W T) q.1 (q.2.map W).toFinset)
    count check checked step

lemma legacy_indexed_dependencies_sound {T i : Nat} {node : Nat → Nat × List Nat}
    (prior : ∀ j, j < i → Impossible true (W T) (node j).1 ((node j).2.map W).toFinset)
    (refs : List Nat) (backward : ∀ j ∈ refs, j < i) :
    ∀ q ∈ refs.map node, Impossible true (W T) q.1 (q.2.map W).toFinset := by
  intro q hq
  obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hq
  exact prior j (backward j hj)

lemma legacy_indexed_dependency_sound {T i j childCap : Nat} {node : Nat → Nat × List Nat}
    (prior : ∀ j, j < i → Impossible true (W T) (node j).1 ((node j).2.map W).toFinset)
    (backward : j < i) (capFits : childCap ≤ (node j).1) :
    Impossible true (W T) childCap ((node j).2.map W).toFinset := by
  intro n hn
  exact prior j backward n (hn.trans capFits)

lemma legacy_indexed_lowN {T K count root : Nat} {R : List Nat}
    {E : List (Nat × Nat × Nat)} (node : Nat → Nat × List Nat)
    (base : baseOK T R E = true)
    (verified : ∀ i, i < count → Impossible true (W T) (node i).1 ((node i).2.map W).toFinset)
    (rootBound : root < count) (rootCap : (node root).1 = K)
    (rootWords : (node root).2 = R.map xN) : LowN R T (K+1) := by
  apply lowOf base
  have h := verified root rootBound
  rw [rootCap, rootWords] at h
  simpa only [rootsW, List.map_map, Function.comp_def] using h

end PEqualNP.Outside.L_meta_10760.RestrictionDAG

namespace PEqualNP.Outside.L_meta_10760.RestrictionData

def negativeRows0 : List Nat := [0,1,2,3,4,6,8,9,12,16,24,32,36,48,64,66,80]
def negativeRows1 : List Nat := [0,2,4,6,8,12,16,24,32,36,48,64,66,80]
def negativeRows2 : List Nat := [0,1,4,8,9,12,16,24,32,36,48,64,80]
def negativeRows3 : List Nat := [0,1,2,3,8,9,16,24,32,48,64,66,80]

def negativeRows (forest : Nat) : List Nat :=
  if forest == 0 then negativeRows0 else if forest == 1 then negativeRows1
  else if forest == 2 then negativeRows2 else negativeRows3

def ascending : List Nat → Bool
  | [] => true
  | [w] => decide (w < 2^128)
  | a :: b :: ws => decide (a < b) && ascending (b :: ws)

def stateOK (ws : List Nat) : Bool :=
  ascending ws && ws.all (fun w => w != 0 && !w.testBit 0)

def cutSpecs (forest index : Nat) : List (Nat × Nat × List Nat) :=
  (row forest index).cuts.map (fun i => specs.getD i (0,0,[]))

def dependencies (forest index : Nat) : List (Nat × List Nat) :=
  (row forest index).deps.map (node forest)

def specScope (forest : Nat) (s : Nat × Nat × List Nat) : Bool :=
  forest == 0 || (decide (s.2.1 ≤ 7) && s.1 &&& inputs.getD (forest-1) 0 == 0)

def decodedMetadata (forest index : Nat) : Bool :=
  decide (forest < 4) && decide (index < forestSize forest) &&
  decide (0 < (node forest index).1) && stateOK (node forest index).2 &&
  (row forest index).cuts.all (fun i => decide (i < specs.length)) &&
  (row forest index).deps.all (fun i => decide (i < index)) &&
  (cutSpecs forest index).all (specScope forest) &&
  (negativeRows forest).all (fun i => decide (i < 128) && !(forestTarget forest).testBit i)

def decodedNodeCheck (forest index : Nat) : Bool :=
  decodedMetadata forest index &&
  AutoPool.nodeCheck (forestTarget forest) (negativeRows forest)
    ((node forest index).1-1) (node forest index).2
    (cutSpecs forest index) (dependencies forest index)

def decodedForestCheck (forest : Nat) : Bool :=
  (List.range (forestSize forest)).all (decodedNodeCheck forest)

def decodedAllCheck : Bool := (List.range 4).all decodedForestCheck

end PEqualNP.Outside.L_meta_10760.RestrictionData

namespace PEqualNP.Outside.L_meta_10760.RestrictionData

lemma decodedNodeCheck_parts {forest index : Nat}
    (h : decodedNodeCheck forest index = true) :
    decodedMetadata forest index = true ∧
    AutoPool.nodeCheck (forestTarget forest) (negativeRows forest)
      ((node forest index).1-1) (node forest index).2
      (cutSpecs forest index) (dependencies forest index) = true := by
  simpa only [decodedNodeCheck, Bool.and_eq_true] using h

lemma decodedMetadata_parts {forest index : Nat}
    (h : decodedMetadata forest index = true) :
    forest < 4 ∧ index < forestSize forest ∧
    0 < (node forest index).1 ∧ stateOK (node forest index).2 = true ∧
    (∀ i ∈ (row forest index).cuts, i < specs.length) ∧
    (∀ i ∈ (row forest index).deps, i < index) ∧
    (∀ s ∈ cutSpecs forest index, specScope forest s = true) ∧
    (∀ i ∈ negativeRows forest, i < 128 ∧ (forestTarget forest).testBit i = false) := by
  simpa [decodedMetadata, and_assoc] using h

lemma dependencies_mem {forest index : Nat} {d : Nat × List Nat}
    (h : d ∈ dependencies forest index) :
    ∃ i ∈ (row forest index).deps, node forest i = d := by
  exact List.mem_map.mp h

lemma cutSpecs_mem {forest index : Nat} {s : Nat × Nat × List Nat}
    (h : s ∈ cutSpecs forest index) :
    ∃ i ∈ (row forest index).cuts, specs.getD i (0,0,[]) = s := by
  exact List.mem_map.mp h

lemma checkedDependencies_before {forest index : Nat} {d : Nat × List Nat}
    (h : decodedNodeCheck forest index = true) (hd : d ∈ dependencies forest index) :
    ∃ i < index, node forest i = d := by
  obtain ⟨i,hi,rfl⟩ := dependencies_mem hd
  exact ⟨i,(decodedMetadata_parts (decodedNodeCheck_parts h).1).2.2.2.2.2.1 i hi,rfl⟩

end PEqualNP.Outside.L_meta_10760.RestrictionData

namespace PEqualNP.Outside.L_meta_10760.RestrictionData
open RestrictionSixProof

def rootVars (f : Nat) : List Nat :=
  (List.range 7).filter (fun i => f == 0 || i+1 != f)

def rootE (f : Nat) : List (Nat × Nat × Nat) :=
  if f == 0 then [(0,4,5), (1,8,10), (2,1,5), (3,2,10), (4,1,17), (5,1,33), (6,1,65)] else
  if f == 1 then [(1,8,10), (2,16,20), (3,2,10), (4,2,18), (5,2,34), (6,4,68)] else
  if f == 2 then [(0,4,5), (2,1,5), (3,32,40), (4,1,17), (5,1,33), (6,1,65)] else
  [(0,16,17), (1,8,10), (3,2,10), (4,1,17), (5,1,33), (6,1,65)]

lemma rootBaseOK (f : Fin 4) :
    baseOK (forestTarget f) (rootVars f) (rootE f) = true := by
  fin_cases f <;> decide +kernel

lemma rootNode (f : Fin 4) :
    node f (forestSize f - 1) = (rootBudget f, (rootVars f).map xN) := by
  fin_cases f <;> decide +kernel

end PEqualNP.Outside.L_meta_10760.RestrictionData

namespace PEqualNP.Outside.L_meta_10760.RestrictionData

open RestrictionSixProof

lemma ascending_eq_asc (ws : List Nat) : ascending ws = asc ws := by
  have blt (a b : Nat) : decide (a < b) = Nat.blt a b := by
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq, Nat.blt_eq]
  induction ws with
  | nil => rfl
  | cons a ws ih =>
    cases ws with
    | nil => exact blt a (2^128)
    | cons b rest => simp only [ascending, asc, ih, blt]

def ScopedSlices (f : Nat) : Prop :=
  ∀ s ∈ specs, specScope f s = true → SliceN (rootVars f) (forestTarget f) s

def MatrixSound (f : Nat) : Prop :=
  ∀ k a b rest o keep, o < 4 → keep < 4 →
    (∀ x ∈ a :: b :: rest, x < 2^128) →
    (AutoPool.phaseMatrix (forestTarget f) (negativeRows f) a b rest &&&
      AutoPool.collisionMasks.getD (4*o+keep) 0 != 0) = true →
    Impossible true (W (forestTarget f)) k
      ((AutoPool.rawChild a b (nb o a b) rest keep).map W).toFinset

def AutoSound (f : Nat) : Prop :=
  ∀ k child spec, SliceN (rootVars f) (forestTarget f) spec →
    (child.map W).Nodup → AutoPool.autoCut k child spec = true →
      Impossible true (W (forestTarget f)) k (child.map W).toFinset

lemma decoded_step_sound (f : Fin 4) (i : Nat)
    (hSlices : ScopedSlices f) (hMatrix : MatrixSound f) (hAuto : AutoSound f)
    (prior : ∀ j, j < i → Impossible true (W (forestTarget f))
      (node f j).1 ((node f j).2.map W).toFinset)
    (checked : decodedNodeCheck f i = true) :
    Impossible true (W (forestTarget f)) (node f i).1 ((node f i).2.map W).toFinset := by
  obtain ⟨hmeta, hcheck⟩ := decodedNodeCheck_parts checked
  obtain ⟨_, _, hpos, hstate, hcuts, hdeps, hscope, _⟩ := decodedMetadata_parts hmeta
  have hAsc : asc (node f i).2 = true := by
    simp only [stateOK, Bool.and_eq_true] at hstate
    have h := hstate.1
    rwa [ascending_eq_asc] at h
  have cutsSound : ∀ spec ∈ cutSpecs f i, SliceN (rootVars f) (forestTarget f) spec := by
    intro spec hspec
    obtain ⟨id, hid, he⟩ := cutSpecs_mem hspec
    have hi := hcuts id hid
    have hm : specs.getD id (0,0,[]) ∈ specs := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
      exact List.getElem_mem hi
    exact hSlices spec (he ▸ hm) (hscope spec hspec)
  have depsSound : ∀ q ∈ dependencies f i,
      Impossible true (W (forestTarget f)) q.1 (q.2.map W).toFinset := by
    intro q hq
    obtain ⟨j, hj, rfl⟩ := checkedDependencies_before checked hq
    exact prior j hj
  have result := AutoPool.legacyNodeCheck_sound
    (baseOK_ok (rootBaseOK f)).lt hAsc cutsSound depsSound
    (hMatrix ((node f i).1-1)) (hAuto ((node f i).1-1)) hcheck
  have budget : (node f i).1 - 1 + 1 = (node f i).1 := by omega
  simpa only [budget] using result

lemma decoded_checks_impossible (f : Fin 4)
    (hSlices : ScopedSlices f) (hMatrix : MatrixSound f) (hAuto : AutoSound f)
    (checked : ∀ i, i < forestSize f → decodedNodeCheck f i = true) :
    ∀ i, i < forestSize f → Impossible true (W (forestTarget f))
      (node f i).1 ((node f i).2.map W).toFinset := by
  apply RestrictionDAG.legacy_indexed_checks_sound
    (forestTarget f) (forestSize f) (node f) (decodedNodeCheck f) checked
  intro i hi prior hc
  exact decoded_step_sound f i hSlices hMatrix hAuto prior hc

lemma decoded_forest_impossible (f : Fin 4)
    (hSlices : ScopedSlices f) (hMatrix : MatrixSound f) (hAuto : AutoSound f)
    (checked : decodedForestCheck f = true) :
    ∀ i, i < forestSize f → Impossible true (W (forestTarget f))
      (node f i).1 ((node f i).2.map W).toFinset := by
  apply decoded_checks_impossible f hSlices hMatrix hAuto
  intro i hi
  exact List.all_eq_true.mp checked i (List.mem_range.mpr hi)

lemma decoded_checks_lowN (f : Fin 4)
    (hSlices : ScopedSlices f) (hMatrix : MatrixSound f) (hAuto : AutoSound f)
    (nonempty : 0 < forestSize f)
    (checked : ∀ i, i < forestSize f → decodedNodeCheck f i = true) :
    LowN (rootVars f) (forestTarget f) (rootBudget f + 1) := by
  exact RestrictionDAG.legacy_indexed_lowN (node f) (rootBaseOK f)
    (decoded_checks_impossible f hSlices hMatrix hAuto checked)
    (by omega) (congrArg Prod.fst (rootNode f)) (congrArg Prod.snd (rootNode f))

lemma decoded_forest_lowN (f : Fin 4)
    (hSlices : ScopedSlices f) (hMatrix : MatrixSound f) (hAuto : AutoSound f)
    (nonempty : 0 < forestSize f) (checked : decodedForestCheck f = true) :
    LowN (rootVars f) (forestTarget f) (rootBudget f + 1) := by
  apply decoded_checks_lowN f hSlices hMatrix hAuto nonempty
  intro i hi
  exact List.all_eq_true.mp checked i (List.mem_range.mpr hi)

lemma decoded_forestSize_pos (f : Fin 4) : 0 < forestSize f := by
  fin_cases f <;> decide +kernel

lemma decoded_all_forestChecked (f : Fin 4) (checked : decodedAllCheck = true) :
    decodedForestCheck f = true := by
  exact List.all_eq_true.mp checked f.val (List.mem_range.mpr f.isLt)

lemma decoded_all_lowN (f : Fin 4)
    (hSlices : ScopedSlices f) (hMatrix : MatrixSound f) (hAuto : AutoSound f)
    (checked : decodedAllCheck = true) :
    LowN (rootVars f) (forestTarget f) (rootBudget f + 1) :=
  decoded_forest_lowN f hSlices hMatrix hAuto (decoded_forestSize_pos f)
    (decoded_all_forestChecked f checked)

end PEqualNP.Outside.L_meta_10760.RestrictionData

namespace PEqualNP.Outside.L_meta_10760.RestrictionData
open RestrictionSixProof

lemma autoSound (f : Fin 4) : AutoSound f := by
  intro k child spec hs nd hc
  exact AutoPool.autoCut_sound_any hs nd hc

lemma matrixSound (f : Fin 4) : MatrixSound f := by
  have hbound : forestTarget f < 2^128 := by fin_cases f <;> decide +kernel
  have hneg : (negativeRows f).all (fun r => decide (r < 128) &&
      !(forestTarget f).testBit r) = true := by fin_cases f <;> decide +kernel
  have hn : ∀ r ∈ negativeRows f, r < 128 ∧ (forestTarget f).testBit r = false := by
    intro r hr
    simpa using List.all_eq_true.mp hneg r hr
  intro k a b rest o keep ho hk _ hb
  have h := AutoPool.phaseMatrix_impossible_raw (target := forestTarget f) (k := k)
    (rest := rest) (a := a) (b := b) (negativeRows f) hbound hn
    ⟨o, ho⟩ ⟨keep, hk⟩ (by simpa using hb)
  simpa only [AutoPool.rawChild, AutoPool.op_eq_nb] using h

end PEqualNP.Outside.L_meta_10760.RestrictionData

namespace PEqualNP.Outside.L_meta_10760.RestrictionData

open RestrictionSixProof

lemma specs_eq_sliceSpecs : specs = Restriction92.sliceSpecs := by rfl

lemma scopedSlices1 : ScopedSlices 1 := by
  intro s hs hscope
  have hs' : s ∈ Restriction92.sliceSpecs := by rwa [specs_eq_sliceSpecs] at hs
  change (false || (decide (s.2.1 ≤ 7) && s.1 &&& xN 0 == 0)) = true at hscope
  simp only [Bool.false_or, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hscope
  exact Restriction92.Forests.forest1_guard_sound hs' hscope.1 hscope.2

lemma scopedSlices2 : ScopedSlices 2 := by
  intro s hs hscope
  have hs' : s ∈ Restriction92.sliceSpecs := by rwa [specs_eq_sliceSpecs] at hs
  change (false || (decide (s.2.1 ≤ 7) && s.1 &&& xN 1 == 0)) = true at hscope
  simp only [Bool.false_or, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hscope
  exact Restriction92.Forests.forest2_guard_sound hs' hscope.1 hscope.2

lemma scopedSlices3 : ScopedSlices 3 := by
  intro s hs hscope
  have hs' : s ∈ Restriction92.sliceSpecs := by rwa [specs_eq_sliceSpecs] at hs
  change (false || (decide (s.2.1 ≤ 7) && s.1 &&& xN 2 == 0)) = true at hscope
  simp only [Bool.false_or, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hscope
  exact Restriction92.Forests.forest3_guard_sound hs' hscope.1 hscope.2

lemma scopedSlices0
    (h1 : LowN (rootVars 1) (forestTarget 1) (rootBudget 1 + 1))
    (h2 : LowN (rootVars 2) (forestTarget 2) (rootBudget 2 + 1))
    (h3 : LowN (rootVars 3) (forestTarget 3) (rootBudget 3 + 1)) :
    ScopedSlices 0 := by
  intro s hs _
  apply Restriction92.slices_sound h1 h2 h3 s
  rwa [specs_eq_sliceSpecs] at hs

lemma decoded_all_original_lowN
    (hMatrix : ∀ f : Fin 4, MatrixSound f)
    (hAuto : ∀ f : Fin 4, AutoSound f)
    (checked : decodedAllCheck = true) : LowN originalGRoots originalGWord 13 := by
  have h1 := decoded_all_lowN (1 : Fin 4) scopedSlices1 (hMatrix 1) (hAuto 1) checked
  have h2 := decoded_all_lowN (2 : Fin 4) scopedSlices2 (hMatrix 2) (hAuto 2) checked
  have h3 := decoded_all_lowN (3 : Fin 4) scopedSlices3 (hMatrix 3) (hAuto 3) checked
  exact decoded_all_lowN (0 : Fin 4) (scopedSlices0 h1 h2 h3)
    (hMatrix 0) (hAuto 0) checked

lemma decoded_lowN13_of_check (checked : decodedAllCheck = true) :
    LowN originalGRoots originalGWord 13 :=
  decoded_all_original_lowN matrixSound autoSound checked

end PEqualNP.Outside.L_meta_10760.RestrictionData

namespace PEqualNP.Outside.L_meta_10760

lemma posted_of_checked (checked : RestrictionData.decodedAllCheck = true) :
    ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 7 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 2, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 2, 6, 3, 6, 5, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 2, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 2, 6, 3, 6, 5, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 2, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 2, 6, 3, 6, 5, 6] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 7 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 2, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 2, 6, 3, 6, 5, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 2, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 2, 6, 3, 6, 5, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 2, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 2, 6, 3, 6, 5, 6] : List ℕ).getD (2 * i + 1) 0) false = true) := by
  intro gates o legal _singleNot computes
  exact RestrictionSixProof.positive_replacement_of_lowN13
    (RestrictionData.decoded_lowN13_of_check checked) ⟨gates, o⟩ legal computes

end PEqualNP.Outside.L_meta_10760
