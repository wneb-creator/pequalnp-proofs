import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_10760

open PEqualNP.CircuitLowerBounds

def edgeFunction (x : Fin 7 → Bool) : Bool :=
  (x 0 && x 2) || (x 1 && x 3) || (x 0 && x 4) || (x 1 && x 4) || (x 2 && x 4) || (x 0 && x 5) || (x 1 && x 5) || (x 3 && x 5) || (x 0 && x 6) || (x 2 && x 6) || (x 3 && x 6) || (x 5 && x 6)

def monotoneWitness : List Gate :=
  [
    ⟨GateOp.or, [0, 2]⟩,
    ⟨GateOp.or, [3, 5]⟩,
    ⟨GateOp.or, [7, 8]⟩,
    ⟨GateOp.and, [6, 9]⟩,
    ⟨GateOp.or, [1, 5]⟩,
    ⟨GateOp.and, [3, 11]⟩,
    ⟨GateOp.or, [0, 1]⟩,
    ⟨GateOp.or, [4, 5]⟩,
    ⟨GateOp.and, [13, 14]⟩,
    ⟨GateOp.or, [0, 4]⟩,
    ⟨GateOp.and, [2, 16]⟩,
    ⟨GateOp.or, [10, 12]⟩,
    ⟨GateOp.or, [15, 17]⟩,
    ⟨GateOp.or, [18, 19]⟩
  ]

lemma witness_size : monotoneWitness.length = 14 := rfl

lemma witness_allowed : ∀ g ∈ monotoneWitness,
    (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
  simp [monotoneWitness]

set_option maxHeartbeats 2000000 in
lemma witness_eval : ∀ x : Fin 7 → Bool,
    Circuit.eval ⟨monotoneWitness, 20⟩ (List.ofFn x) = edgeFunction x := by
  decide +kernel

set_option maxHeartbeats 2000000 in
lemma edgeFunction_posted : ∀ x : Fin 7 → Bool,
    decide (∃ i < ([0, 2, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 2, 6, 3, 6, 5, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 2, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 2, 6, 3, 6, 5, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 2, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 2, 6, 3, 6, 5, 6] : List ℕ).getD (2 * i + 1) 0) false = true) = edgeFunction x := by
  decide +kernel


def pairInput (i j : Fin 7) : Fin 7 → Bool :=
  fun k => decide (k = i ∨ k = j)

set_option maxHeartbeats 8000000 in
lemma positive_pair : ∀ x : Fin 7 → Bool, edgeFunction x = true →
    ∃ i j : Fin 7, i ≠ j ∧ pairInput i j ≤ x ∧ edgeFunction (pairInput i j) = true := by
  decide +kernel

set_option maxHeartbeats 8000000 in
lemma negative_pair : ∀ x : Fin 7 → Bool, edgeFunction x = false →
    ∃ i j : Fin 7, i ≠ j ∧ x ≤ pairInput i j ∧ edgeFunction (pairInput i j) = false := by
  decide +kernel

lemma pair_table_suffices (g : (Fin 7 → Bool) → Bool) (hg : Monotone g)
    (hpair : ∀ i j : Fin 7, i ≠ j → g (pairInput i j) = edgeFunction (pairInput i j)) :
    ∀ x : Fin 7 → Bool, g x = edgeFunction x := by
  intro x
  cases hx : edgeFunction x with
  | false =>
    obtain ⟨i, j, hij, hle, hf⟩ := negative_pair x hx
    have h := hg hle
    rw [hpair i j hij, hf] at h
    exact Bool.eq_false_of_le_false h
  | true =>
    obtain ⟨i, j, hij, hle, hf⟩ := positive_pair x hx
    have h := hg hle
    rw [hpair i j hij, hf] at h
    exact Bool.eq_true_of_true_le h

lemma monotone_target_order {α β : Type*} [Preorder β]
    (target : α → Bool) (F : β → Bool) (hF : Monotone F)
    (u v : α → β) (hcorrect : ∀ x, F (u x) = target x)
    (hpositive : ∀ x, target x = true → u x ≤ v x)
    (hnegative : ∀ x, target x = false → v x ≤ u x) :
    ∀ x, F (v x) = target x := by
  intro x
  cases hx : target x with
  | false =>
    have h := hF (hnegative x hx)
    rw [hcorrect x, hx] at h
    exact Bool.eq_false_of_le_false h
  | true =>
    have h := hF (hpositive x hx)
    rw [hcorrect x, hx] at h
    exact Bool.eq_true_of_true_le h

lemma replace_dominated_signal {α : Type*} {n : ℕ}
    (target : α → Bool) (F : (Fin n → Bool) → Bool) (hF : Monotone F)
    (w : α → Fin n → Bool) (i j : Fin n)
    (hcorrect : ∀ x, F (w x) = target x)
    (hpositive : ∀ x, target x = true → w x i ≤ w x j)
    (hnegative : ∀ x, target x = false → w x j ≤ w x i) :
    ∀ x, F (fun k => if k = i then w x j else w x k) = target x := by
  apply monotone_target_order target F hF w _ hcorrect
  · intro x hx k
    by_cases hk : k = i
    · simpa [hk] using hpositive x hx
    · simp [hk]
  · intro x hx k
    by_cases hk : k = i
    · simpa [hk] using hnegative x hx
    · simp [hk]

namespace NatFlip

lemma xor_pow_of_testBit_false {r i : Nat} (hr : r.testBit i = false) :
    r ^^^ 2 ^ i = r + 2 ^ i := by
  have hpow : 0 < 2 ^ i := Nat.two_pow_pos i
  have hbit : (r / 2 ^ i).testBit 0 = false := by
    simpa only [Nat.testBit_div_two_pow, Nat.zero_add] using hr
  have heven : Even (r / 2 ^ i) :=
    Nat.even_iff.mpr (Nat.mod_two_eq_zero_iff_testBit_zero.mpr hbit)
  have hdiv : (r ^^^ 2 ^ i) / 2 ^ i = r / 2 ^ i + 1 := by
    rw [Nat.xor_div_two_pow, Nat.div_self hpow, Nat.xor_one_of_even heven]
  have hmod : (r ^^^ 2 ^ i) % 2 ^ i = r % 2 ^ i := by
    rw [Nat.xor_mod_two_pow, Nat.mod_self, Nat.xor_zero]
  calc
    r ^^^ 2 ^ i = (r ^^^ 2 ^ i) % 2 ^ i + 2 ^ i * ((r ^^^ 2 ^ i) / 2 ^ i) :=
      (Nat.mod_add_div _ _).symm
    _ = r % 2 ^ i + 2 ^ i * (r / 2 ^ i + 1) := by rw [hmod, hdiv]
    _ = r + 2 ^ i := by
      rw [Nat.mul_add, Nat.mul_one, ← Nat.add_assoc, Nat.mod_add_div]

lemma xor_pow_of_testBit_true {r i : Nat} (hr : r.testBit i = true) :
    r ^^^ 2 ^ i = r - 2 ^ i := by
  have hbit : (r ^^^ 2 ^ i).testBit i = false := by
    simp [Nat.testBit_xor, hr]
  have h := xor_pow_of_testBit_false hbit
  rw [Nat.xor_xor_cancel_right] at h
  omega

lemma testBit_sub_pow {r i : Nat} (h : 2 ^ i ≤ r) :
    (r - 2 ^ i).testBit i = !r.testBit i := by
  have hflip := Nat.testBit_two_pow_add_eq (r - 2 ^ i) i
  rw [Nat.add_sub_of_le h] at hflip
  simpa using (congrArg Bool.not hflip).symm

def flipCoordinate (B mask i : Nat) : Nat :=
  ((B &&& mask) <<< (2 ^ i)) ||| ((B >>> (2 ^ i)) &&& mask)

lemma flipCoordinate_testBit (B mask i N r : Nat)
    (hmask : ∀ t < N, mask.testBit t = !t.testBit i)
    (hr : r < N) :
    (flipCoordinate B mask i).testBit r = B.testBit (r ^^^ 2 ^ i) := by
  simp only [flipCoordinate, Nat.testBit_or, Nat.testBit_shiftLeft,
    Nat.testBit_shiftRight, Nat.testBit_and]
  have hm := hmask r hr
  cases hbit : r.testBit i with
  | false =>
    rw [xor_pow_of_testBit_false hbit]
    by_cases hle : 2 ^ i ≤ r
    · have hs : r - 2 ^ i < N := (Nat.sub_le r _).trans_lt hr
      have hms := hmask (r - 2 ^ i) hs
      have hsub := testBit_sub_pow hle
      simp [hle, hm, hms, hsub, hbit, Nat.add_comm]
    · simp [hle, hm, hbit, Nat.add_comm]
  | true =>
    rw [xor_pow_of_testBit_true hbit]
    have hle : 2 ^ i ≤ r := Nat.ge_two_pow_of_testBit hbit
    have hs : r - 2 ^ i < N := (Nat.sub_le r _).trans_lt hr
    have hms := hmask (r - 2 ^ i) hs
    have hsub := testBit_sub_pow hle
    simp [hle, hm, hms, hsub, hbit]

lemma flipCoordinate_testBit_of_mask (B mask m i r : Nat)
    (hmask : ∀ t, mask.testBit t = decide (t < 2 ^ m ∧ t.testBit i = false))
    (hr : r < 2 ^ m) :
    (flipCoordinate B mask i).testBit r = B.testBit (r ^^^ 2 ^ i) := by
  apply flipCoordinate_testBit B mask i (2 ^ m) r ?_ hr
  intro t ht
  simp [hmask, ht]

end NatFlip

namespace BitmapCollision

def collisionMask (flip : Nat → Nat) (domainBits P N G : Nat) : Nat :=
  (P &&& flip N) &&& (domainBits ^^^ (G ^^^ flip G))

lemma collisionMask_testBit (flip delta : Nat → Nat) (domainBits P N G p : Nat)
    (hflip : ∀ B, (flip B).testBit p = B.testBit (delta p))
    (hdomain : domainBits.testBit p = true) :
    (collisionMask flip domainBits P N G).testBit p = true ↔
      P.testBit p = true ∧ N.testBit (delta p) = true ∧
        G.testBit p = G.testBit (delta p) := by
  simp only [collisionMask, Nat.testBit_and, Nat.testBit_xor, hflip, hdomain]
  cases P.testBit p <;> cases N.testBit (delta p) <;>
    cases G.testBit p <;> cases G.testBit (delta p) <;> decide

lemma collisionMask_ne_zero_iff (flip delta : Nat → Nat) (domainBits P N G : Nat)
    (hflip : ∀ B q, P.testBit q = true → (flip B).testBit q = B.testBit (delta q))
    (hsupport : ∀ p, P.testBit p = true → domainBits.testBit p = true) :
    collisionMask flip domainBits P N G ≠ 0 ↔
      ∃ p, P.testBit p = true ∧ N.testBit (delta p) = true ∧
        G.testBit p = G.testBit (delta p) := by
  constructor
  · intro hnonzero
    obtain ⟨p, hp⟩ := Nat.exists_testBit_of_ne_zero hnonzero
    have hP : P.testBit p = true := by
      have h := hp
      simp only [collisionMask, Nat.testBit_and, Bool.and_eq_true] at h
      exact h.1.1
    exact ⟨p, (collisionMask_testBit flip delta domainBits P N G p
      (fun B => hflip B p hP) (hsupport p hP)).mp hp⟩
  · rintro ⟨p, hp, hn, hg⟩ hzero
    have h := (collisionMask_testBit flip delta domainBits P N G p
      (fun B => hflip B p hp) (hsupport p hp)).mpr ⟨hp, hn, hg⟩
    simp only [hzero, Nat.zero_testBit, Bool.false_eq_true] at h

lemma selfMask_ne_zero_iff (flip delta : Nat → Nat) (P N G : Nat)
    (hflip : ∀ B q, P.testBit q = true → (flip B).testBit q = B.testBit (delta q)) :
    collisionMask flip P P N G ≠ 0 ↔
      ∃ p, P.testBit p = true ∧ N.testBit (delta p) = true ∧
        G.testBit p = G.testBit (delta p) :=
  collisionMask_ne_zero_iff flip delta P P N G hflip (fun _ hp => hp)

lemma projected_overlap_of_collision
    (flip delta f : Nat → Nat) (domainBits P N G projectedP projectedN : Nat)
    (hflip : ∀ B q, P.testBit q = true → (flip B).testBit q = B.testBit (delta q))
    (hsupport : ∀ p, P.testBit p = true → domainBits.testBit p = true)
    (himageP : ∀ q, projectedP.testBit q = true ↔
      ∃ p, P.testBit p = true ∧ f p = q)
    (himageN : ∀ q, projectedN.testBit q = true ↔
      ∃ p, N.testBit p = true ∧ f p = q)
    (hmap : ∀ p, P.testBit p = true → N.testBit (delta p) = true →
      G.testBit p = G.testBit (delta p) → f p = f (delta p))
    (hnonzero : collisionMask flip domainBits P N G ≠ 0) :
    projectedP &&& projectedN ≠ 0 := by
  obtain ⟨p, hp, hn, hg⟩ :=
    (collisionMask_ne_zero_iff flip delta domainBits P N G hflip hsupport).mp hnonzero
  have hP : projectedP.testBit (f p) = true :=
    (himageP (f p)).mpr ⟨p, hp, rfl⟩
  have hN : projectedN.testBit (f p) = true :=
    (himageN (f p)).mpr ⟨delta p, hn, (hmap p hp hn hg).symm⟩
  intro hzero
  have hbit : (projectedP &&& projectedN).testBit (f p) = true := by
    simp only [Nat.testBit_and, hP, hN, Bool.and_self]
  simp only [hzero, Nat.zero_testBit, Bool.false_eq_true] at hbit

lemma projected_overlap_of_selfMask
    (flip delta f : Nat → Nat) (P N G projectedP projectedN : Nat)
    (hflip : ∀ B q, P.testBit q = true → (flip B).testBit q = B.testBit (delta q))
    (himageP : ∀ q, projectedP.testBit q = true ↔
      ∃ p, P.testBit p = true ∧ f p = q)
    (himageN : ∀ q, projectedN.testBit q = true ↔
      ∃ p, N.testBit p = true ∧ f p = q)
    (hmap : ∀ p, P.testBit p = true → N.testBit (delta p) = true →
      G.testBit p = G.testBit (delta p) → f p = f (delta p))
    (hnonzero : collisionMask flip P P N G ≠ 0) :
    projectedP &&& projectedN ≠ 0 :=
  projected_overlap_of_collision flip delta f P P N G projectedP projectedN
    hflip (fun _ hp => hp) himageP himageN hmap hnonzero

end BitmapCollision

namespace GateCollision

def gate (op : Fin 4) (a b : Bool) : Bool :=
  match op.val with
  | 0 => a && b
  | 1 => a || b
  | 2 => a && !b
  | _ => b && !a

lemma same_left : ∀ (op : Fin 4) (a b : Bool),
    (gate op a b == gate op (!a) b) =
      (if op.val = 0 ∨ op.val = 3 then !b else b) := by
  decide +kernel

lemma same_right : ∀ (op : Fin 4) (a b : Bool),
    (gate op a b == gate op a (!b)) =
      (if op.val = 0 ∨ op.val = 2 then !a else a) := by
  decide +kernel

lemma same_both : ∀ (op : Fin 4) (a b : Bool),
    (gate op a b == gate op (!a) (!b)) =
      (if op.val < 2 then a != b else a == b) := by
  decide +kernel

end GateCollision

end PEqualNP.Outside.L_meta_10760

namespace PEqualNP.Outside.L_meta_10760.SupportCompression

lemma eq_of_updates {n : Nat} (f : (Fin n → Bool) → Bool) (D : Finset (Fin n)) :
    (∀ i ∈ D, ∀ x b, f (Function.update x i b) = f x) →
    ∀ x y, (∀ i ∉ D, x i = y i) → f x = f y := by
  induction D using Finset.induction_on with
  | empty =>
    intro _ x y hxy
    exact congrArg f (funext fun i => hxy i (by simp))
  | @insert i D hi ih =>
    intro hstep x y hxy
    calc
      f x = f (Function.update x i (y i)) := (hstep i (by simp) x (y i)).symm
      _ = f y := by
        apply ih (fun j hj => hstep j (Finset.mem_insert_of_mem hj))
        intro j hj
        by_cases hji : j = i
        · subst j; simp
        · simpa [hji] using hxy j (by simp [hji, hj])

lemma eq_of_agree_on {n : Nat} (f : (Fin n → Bool) → Bool) (S : Finset (Fin n))
    (hstep : ∀ i ∉ S, ∀ x b, f (Function.update x i b) = f x)
    (x y : Fin n → Bool) (hxy : ∀ i ∈ S, x i = y i) : f x = f y := by
  apply eq_of_updates f (Finset.univ \ S)
  · intro i hi
    exact hstep i (Finset.mem_sdiff.mp hi).2
  · intro i hi
    apply hxy i
    simpa using hi

lemma update_of_flip {n : Nat} (f : (Fin n → Bool) → Bool) (S : Finset (Fin n))
    (hflip : ∀ i ∉ S, ∀ x, f (Function.update x i (!(x i))) = f x) :
    ∀ i ∉ S, ∀ x b, f (Function.update x i b) = f x := by
  intro i hi x b
  by_cases h : b = x i
  · apply congrArg f
    funext j
    by_cases hji : j = i
    · subst j; simpa using h
    · simp [hji]
  · have hb : b = !(x i) := by
      cases hx : x i <;> cases b <;> simp_all
    rw [hb]
    exact hflip i hi x

lemma eq_of_flip_invariant {n : Nat} (f : (Fin n → Bool) → Bool) (S : Finset (Fin n))
    (hflip : ∀ i ∉ S, ∀ x, f (Function.update x i (!(x i))) = f x)
    (x y : Fin n → Bool) (hxy : ∀ i ∈ S, x i = y i) : f x = f y :=
  eq_of_agree_on f S (update_of_flip f S hflip) x y hxy

end PEqualNP.Outside.L_meta_10760.SupportCompression


namespace PEqualNP.Outside.L_meta_10760.RestrictionSixProof
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

def bit (i : Fin 128) (a : Sig) : Bool := a.getLsbD i.val
abbrev Row := Fin 128
def W (a : Nat) : Sig := BitVec.ofNat 128 a
lemma bit_W (r : Row) (a : Nat) : bit r (W a) = a.testBit r.val := by
  unfold bit W
  rw [BitVec.getLsbD_ofNat]
  simp [r.isLt]
def Impossible (u : Bool) (T : Sig) (cap : Nat) (S : Finset Sig) : Prop :=
  ∀ k, k ≤ cap → ¬Live u T k S

end PEqualNP.Outside.L_meta_10760.RestrictionSixProof

namespace PEqualNP.Outside.L_meta_10760

section Live

variable {α : Type} [DecidableEq α]

def live (ops : α → α → Finset α) (goal : α) : ℕ → Finset α → Prop
  | 0, s => s = {goal}
  | k + 1, s => live ops goal k s ∨
    ∃ a ∈ s, ∃ b ∈ s, a ≠ b ∧ ∃ z ∈ ops a b, z ∉ s ∧
      ∃ rest : Finset α, s = insert a (insert b rest) ∧ live ops goal k (insert z rest)

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

lemma live_clique_card_bound {width k : Nat} {target g : BitVec width}
    {S C : Finset (BitVec width)} (run : live basicOps g k S)
    (hg : g = target ∨ g = ~~~target) (sub : C ⊆ S)
    (clique : ∀ c ∈ C, ∀ d ∈ C, c ≠ d → criticalPair target S c d) :
    C.card + S.card ≤ k + 2 := by
  induction k generalizing S C with
  | zero =>
    change S = {g} at run
    subst S
    have := Finset.card_le_card sub
    simpa using Nat.add_le_add_right this 1
  | succ k ih =>
    rcases run with skip | ⟨a, ha, b, hb, hab, z, hz, fresh, U, rfl, tail⟩
    · have := ih skip sub clique
      omega
    · let V := if a ∈ U then C.erase a else C
      let W := if b ∈ U then V.erase b else V
      have hWC : W ⊆ C := by
        intro c hc
        by_cases haU : a ∈ U <;> by_cases hbU : b ∈ U <;>
          simp only [W, V, haU, hbU, ite_true, ite_false, Finset.mem_erase] at hc <;>
          tauto
      have hna : ∀ c ∈ W, c = a → a ∉ U := by
        intro c hc eq hm
        subst c
        by_cases hbU : b ∈ U <;> simp [W, V, hm, hbU] at hc
      have hnb : ∀ c ∈ W, c = b → b ∉ U := by
        intro c hc eq hm
        subst c
        simp [W, hm] at hc
      have step : ∀ c ∈ W, ∀ d ∈ W, c ≠ d →
          criticalPair target (insert z U)
            (ChromRelation.moved a b z c) (ChromRelation.moved a b z d) := by
        intro c hc d hd hcd
        exact ChromRelation.criticalPair_step hab hz fresh tail hg
          (hna c hc) (hnb c hc) (hna d hd) (hnb d hd)
          (clique c (hWC hc) d (hWC hd) hcd)
      let D := W.image (ChromRelation.moved a b z)
      have hD : D ⊆ insert z U := by
        intro c hc
        obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hc
        exact ChromRelation.moved_mem (sub (hWC hw))
      have hclique : ∀ c ∈ D, ∀ d ∈ D, c ≠ d →
          criticalPair target (insert z U) c d := by
        intro c hc d hd hcd
        obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hc
        obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hd
        exact step w hw v hv (fun eq => hcd (congrArg _ eq))
      have hcard : D.card = W.card := by
        apply Finset.card_image_of_injOn
        intro c hc d hd eq
        by_contra hne
        exact (step c hc d hd hne).2.2.1 eq
      have loss : C.card ≤ W.card +
          ((if a ∈ U then 1 else 0) + (if b ∈ U then 1 else 0)) := by
        have h₁ := Finset.pred_card_le_card_erase (s := C) (a := a)
        have h₂ := Finset.pred_card_le_card_erase (s := C) (a := b)
        have h₃ := Finset.pred_card_le_card_erase (s := C.erase a) (a := b)
        by_cases haU : a ∈ U <;> by_cases hbU : b ∈ U <;>
          simp only [W, V, haU, hbU, ite_true, ite_false] <;> omega
      have bound := ih tail hD hclique
      have count := ChromGeneric.retained_card hab fresh
      omega

end PEqualNP.Outside.L_meta_10760

namespace PEqualNP.Outside.L_meta_10760.RestrictionSixProof

lemma live_to_basic {u target k S} (h : Live u target k S) :
    live basicOps target k S := by
  induction h using Live.ind with
  | stop hp => rfl
  | @binary k U a b d hd ha hb hab hf tail ih =>
    refine Or.inr ⟨a, by simp, b, by simp, hab, bin d a b, ?_, hf, U, rfl, ih⟩
    rcases allowed_four hd with rfl | rfl | ⟨_,rfl⟩ | ⟨_,rfl⟩ <;>
      simp [basicOps, ops, bin, BitVec.and_comm]

lemma impossible_of_criticalClique {u : Bool} {target : Sig} {cap : Nat}
    {S C : Finset Sig} (sub : C ⊆ S)
    (clique : ∀ c ∈ C, ∀ d ∈ C, c ≠ d → criticalPair target S c d)
    (bound : cap + 2 - S.card < C.card) : Impossible u target cap S := by
  intro k hk run
  have := live_clique_card_bound (live_to_basic run) (Or.inl rfl) sub clique
  omega

end PEqualNP.Outside.L_meta_10760.RestrictionSixProof
namespace PEqualNP.Outside.L_meta_10760
open RestrictionSixProof (W)

namespace SixRowWitness

def sep (ws : List Nat) (a p q : Nat) : Bool :=
  (!(a.testBit p == a.testBit q)) &&
    ws.all (fun w => w == a || w.testBit p == w.testBit q)

lemma sep_ok {ws a p q} (h : sep ws a p q = true) :
    a.testBit p ≠ a.testBit q ∧
      ∀ w ∈ ws, w = a ∨ w.testBit p = w.testBit q := by
  simpa [sep, Bool.and_eq_true, Bool.or_eq_true, List.all_eq_true] using h

lemma word_bit (w r : Nat) (hr : r < 128) :
    (W w)[r] = w.testBit r := by
  simpa [RestrictionSixProof.bit, W, hr] using RestrictionSixProof.bit_W ⟨r, hr⟩ w

lemma sep_sound {ws a p q} (hp : p < 128) (hq : q < 128)
    (h : sep ws a p q = true) :
    uniqueSep ((ws.map W).toFinset) (W a) ⟨p, hp⟩ ⟨q, hq⟩ := by
  obtain ⟨diff, same⟩ := sep_ok h
  constructor
  · simpa only [word_bit] using diff
  · intro w hw hwa
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hw)
    have vne : v ≠ a := fun he => hwa (congrArg W he)
    simpa only [word_bit] using (same v hv).resolve_left vne

def check (T : Nat) (ws : List Nat) (a b p q ra rb sa sb : Nat) : Bool :=
  decide (p < 128 ∧ q < 128 ∧ ra < 128 ∧ rb < 128 ∧ sa < 128 ∧ sb < 128 ∧
    a ∈ ws ∧ b ∈ ws ∧ a ≠ b ∧
    T.testBit p = true ∧ T.testBit q = false ∧
    T.testBit ra = false ∧ T.testBit rb = false ∧
    T.testBit sa = true ∧ T.testBit sb = true ∧
    sep ws a p ra = true ∧ sep ws b p rb = true ∧
    sep ws a sa q = true ∧ sep ws b sb q = true ∧
    a.testBit p = a.testBit sa ∧ b.testBit p = b.testBit sb)

lemma sound {T ws a b p q ra rb sa sb}
    (h : check T ws a b p q ra rb sa sb = true) :
    criticalPair (W T) ((ws.map W).toFinset) (W a) (W b) := by
  obtain ⟨hp, hq, hra, hrb, hsa, hsb, ha, hb, hab,
    tp, tq, tra, trb, tsa, tsb, pa, pb, aq, bq, crossa, crossb⟩ :=
    of_decide_eq_true h
  have diff := (sep_ok pa).1
  have same : b.testBit p = b.testBit ra :=
    ((sep_ok pa).2 b hb).resolve_left (Ne.symm hab)
  have wab : W a ≠ W b := by
    intro he
    have ep := congrArg (fun w : BitVec 128 => w[p]) he
    have er := congrArg (fun w : BitVec 128 => w[ra]) he
    have ep' : a.testBit p = b.testBit p := by simpa only [word_bit] using ep
    have er' : a.testBit ra = b.testBit ra := by simpa only [word_bit] using er
    exact diff (ep'.trans (same.trans er'.symm))
  refine ⟨List.mem_toFinset.mpr (List.mem_map.mpr ⟨a, ha, rfl⟩),
    List.mem_toFinset.mpr (List.mem_map.mpr ⟨b, hb, rfl⟩), wab,
    ⟨p, hp⟩, ⟨q, hq⟩, ⟨ra, hra⟩, ⟨rb, hrb⟩, ⟨sa, hsa⟩, ⟨sb, hsb⟩,
    ?_, ?_, ?_, ?_, ?_, ?_, sep_sound hp hra pa, sep_sound hp hrb pb,
    sep_sound hsa hq aq, sep_sound hsb hq bq, ?_, ?_⟩
  all_goals simp only [word_bit]; assumption

end SixRowWitness
end PEqualNP.Outside.L_meta_10760
namespace PEqualNP.Outside.L_meta_10760.HTWitnessData
def sixRows : Nat := 0xe160c30a0e385820c2838e148324a09b852062680be148120a08b8510482822e1440a0a0878410482822e0e0c5061638382141858e0d024061138340901805e0c40c0610722c120d20bc8940c049071430282121c160c30a0e30582082828c120c3080e304820c2038c12062480b30481282028c12042080a30480082028c110303801f0411082028c104186801f0410282821c1040a084870410282021c1040a000870410212005c0e0c5021630283141058c0a08504163028181900ec0a0483402f0281101048c0a044021230281100048c0a01c2410f022062500bc084c5041630210709043c0840c061070210301041b1c0818a0e2c702062828b180818a0e2c602062828b14830ca03ac52062680bb148120a08ac52042280ab148089a02ec386140c70b0e10403182c384100860b0e085031c2c382140c60b0e00c03106c282140c60b0702403112c190300c41b028150114aa51123280da5c1206a09a970400a822a5c0002a08a95830c2838a560483a02e958100a80aa560002a02a94648c2134a51861884729460842114a51809084469460042114a50d23084d29431262119a50c09084469430042111a50449884669410242011a4ac09084469270842114a48c09084469140908846a428450056290748c213498b01c2190e60d614067098340c019064c1022610a92a5040138248d61404f0923523012d2460483202c918100880a24602062038918000880a2428410046090a1040018242801004609028324109a40a04804228d0c186841e343041a1078d0c086841634302121058d04186841e341061a1058d04106841e341021a1058d04084841632641003608c980400d8231421082528c384400d2230e01003488c1d0400d8230707083438c1c1820d0e30705083438c1c1420d0630703003418c1c0c005062416092034890448c8036241123000d8904186801e241041a00789040a4801624102120058904084001624100120058850c090866214200421188140c0090620503000418814090084620501002418748c0984661d200061118718303841e1c60c0a1078718103841e1c4040e105868d85007c21a341001e08648c09046618b11001c8862c440052218b11000c8862c04007221870d081c6861c302071a18705081c6838100180860e000060218320c3080e20c8189202c831830184160c40c0e007831020180160c4040e007828504003820a10d080c6824582402d20870d08146821461802720850d080c68214240031208509000448214142031a08501000c47348108a029c70206185871808186161c5820c0c707148189a02dc32062580b70c81086029c3106198077088189602dc22042180a7070303301dc1c0300c4170681203089c190280c217048189602da70001184468c448c6035a31121180568c4186601da31061180568c4106601da31021180568b21504949a2c0301241689a1504949a26044121268980904845a25854125268944984865a25044121268940904845a250041211684448c6035a110619807683a1504949a07854125268144984865a05024121164e0483602d8b4182580d62d0303601d8b4090184462d020160158b4040d807589830c4839626083120e5898189482d626022520b5838324189960e0c902265838304189960e089062658340c0190560d02806215266842134948b85404d2522c324129948b08904a6522c1201289460802104851808184161460002104850c8189602d432042180a509830c48394220c3100e508830c4029422062500b50881894029422043100a50881094029422042100a50881080029422002100a508430c40394210c3100a5084188402d421042100a502c324129940a0c904265028120128940a04804225028120008940a00804224cd2842494933481092524cd0802484932c081920e4cb0083482d32c000920a4ca0206482931630243194c386240cb130e181032c4c382240cb1307189032c4c1c0a00c8530702403114b9200149052b430252194ad080148452b40005211470e020078118b30c01b8462c83006e118b10c01a8462c42406a118b10801a8462c22406b118730c01b844a06064039128120d00b44a04024029128000900a4428c3004e110a189012c442842004a110a1080028442802004a10e0840d043438200141050e01025049438000141050c830c2038432083080e10c40c0e0074310103801d0c180800e0430402003810a2102500b428830c4039091303009c42146180270e588010c4439600043110e191230c0d38644883034e191030c0d383a1501948e0e044061238380101848e0d126061938344981064e0d122061938344181864d194818c263362103310ccd88004c4133600013104cd2042280a32e10013084cb80004c2132706093034c9c1820c0d32704093034c9c040cc0732683243098c8d186049c32346081270c8d106049c322e1501348c8b04804a2322c1101248c8b0040492322a1501348c85186049c2c984980c64b07024031128c448c6034a31123080d28981104848a128490826284448c2034a11061880728441862014a11023080528440842014a11021000528440042014a07024031128144980864a05024021128140900044a050040211261d23006d09870840194261523006d09431260119225020120148940004805222e150034888548c00b42214618027088508400942214210005088500400941cb02061898726481032c1c9820c0cb071ca1086521c70802184871c00086121ab1001188469c30246191a70c09106469c30206191a704091864699302049c1a6440c127069410246111a3a150194868e0c906261a2e15013485c380201c8170c00807205a940084a216a40021288599a1084d2166500212885990008492163523012d058d41004e014a100210885280008422148800804a03c680043410f181030d0c3c6040c3410f0c10607183c104181c60e990010c8438e41003600e386240cb02c480042410b1000109042c180100c40b0410603182c100100c40a50801084429400042110a4582402d02910010094
end PEqualNP.Outside.L_meta_10760.HTWitnessData
namespace PEqualNP.Outside.L_meta_10760.HTFinite
open PEqualNP.Outside.L_meta_10760

def vertex (code i : Nat) : Nat := (code >>> (2+4*i)) &&& 15
def pairIndices (c : Nat) : List (Nat × Nat) :=
  (List.range c).flatMap (fun i => ((List.range c).filter (fun j => i < j)).map (fun j => (i,j)))
def rowAt (rows t : Nat) : Nat := (rows >>> (7*t)) &&& 127

def pairCheck (T : Nat) (ws : List Nat) (code c e i j : Nat) : Bool :=
  let id := (code >>> (2+4*c+9*e)) &&& 511
  let rows := (HTWitnessData.sixRows >>> (42*id)) &&& 4398046511103
  decide (id < 418) && SixRowWitness.check T ws
    (ws.getD (vertex code i) 0) (ws.getD (vertex code j) 0)
    (rowAt rows 0) (rowAt rows 1) (rowAt rows 2)
    (rowAt rows 3) (rowAt rows 4) (rowAt rows 5)

def leafCheck (T cap : Nat) (ws : List Nat) (code : Nat) : Bool :=
  let tag := code &&& 3
  let c := tag+1
  decide (1 ≤ tag ∧ tag ≤ 3 ∧ cap+2-ws.length ≤ tag) &&
  (List.range c).all (fun i => decide (vertex code i < ws.length)) &&
  (pairIndices c).all (fun (i,j) => decide (vertex code i < vertex code j)) &&
  (code >>> (2+4*c+9*(c*(c-1)/2)) == 0) &&
  ((pairIndices c).zipIdx).all (fun ((i,j),e) => pairCheck T ws code c e i j)

end PEqualNP.Outside.L_meta_10760.HTFinite
namespace PEqualNP.Outside.L_meta_10760.HTFinite

open RestrictionSixProof (W)

private lemma pairIndices_mem {c i j : Nat} (hi : i < c) (hj : j < c)
    (hij : i < j) : (i, j) ∈ pairIndices c := by
  apply List.mem_flatMap.mpr
  refine ⟨i, List.mem_range.mpr hi, ?_⟩
  apply List.mem_map.mpr
  exact ⟨j, List.mem_filter.mpr ⟨List.mem_range.mpr hj, by simpa using hij⟩, rfl⟩

private lemma pairCheck_sound {T : Nat} {ws : List Nat} {code c e i j : Nat}
    (h : pairCheck T ws code c e i j = true) :
    criticalPair (W T) ((ws.map W).toFinset)
      (W (ws.getD (vertex code i) 0)) (W (ws.getD (vertex code j) 0)) := by
  simp only [pairCheck, Bool.and_eq_true] at h
  exact SixRowWitness.sound h.2

lemma leafCheck_sound {u : Bool} {T cap : Nat} {ws : List Nat} {code : Nat}
    (h : leafCheck T cap ws code = true) (hn : (ws.map W).Nodup) :
    RestrictionSixProof.Impossible u (W T) cap ((ws.map W).toFinset) := by
  simp only [leafCheck, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    beq_iff_eq] at h
  obtain ⟨⟨⟨⟨htags, hverts⟩, _⟩, _⟩, hpairs⟩ := h
  let n := (code &&& 3) + 1
  let f : Nat → BitVec 128 := fun i => W (ws.getD (vertex code i) 0)
  let C := (Finset.range n).image f
  have edges : ∀ i, i < n → ∀ j, j < n → i < j →
      criticalPair (W T) ((ws.map W).toFinset) (f i) (f j) := by
    intro i hi j hj hij
    obtain ⟨e, he⟩ := List.mem_iff_getElem?.mp (pairIndices_mem hi hj hij)
    exact pairCheck_sound (hpairs ((i,j),e)
      (List.mk_mem_zipIdx_iff_getElem?.mpr he))
  have injective : Set.InjOn f (Finset.range n) := by
    intro i hi j hj eq
    by_contra ne
    rcases lt_or_gt_of_ne ne with lt | gt
    · exact (edges i (Finset.mem_range.mp hi) j (Finset.mem_range.mp hj) lt).2.2.1 eq
    · exact (edges j (Finset.mem_range.mp hj) i (Finset.mem_range.mp hi) gt).2.2.1 eq.symm
  have hC : C.card = n := by
    rw [Finset.card_image_of_injOn injective, Finset.card_range]
  apply RestrictionSixProof.impossible_of_criticalClique (C := C)
  · intro a ha
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp ha
    have hv := hverts i (List.mem_range.mpr (Finset.mem_range.mp hi))
    apply List.mem_toFinset.mpr
    apply List.mem_map.mpr
    refine ⟨ws.getD (vertex code i) 0, ?_, rfl⟩
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hv, Option.getD_some]
    exact List.getElem_mem _
  · intro a ha b hb ne
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hb
    have ij : i ≠ j := fun eq => ne (congrArg f eq)
    rcases lt_or_gt_of_ne ij with lt | gt
    · exact edges i (Finset.mem_range.mp hi) j (Finset.mem_range.mp hj) lt
    · exact ChromRelation.criticalPair_symm
        (edges j (Finset.mem_range.mp hj) i (Finset.mem_range.mp hi) gt)
  · have hs := List.toFinset_card_of_nodup hn
    rw [hs, List.length_map, hC]
    exact Nat.lt_succ_of_le htags.2.2

end PEqualNP.Outside.L_meta_10760.HTFinite
