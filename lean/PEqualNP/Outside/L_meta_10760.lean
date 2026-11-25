import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_10760

-- The LRAT checker below is adapted from PEqualNP/Library/LRAT/Checker.lean.


namespace LRAT

noncomputable section Core

def neg (l : Nat) : Nat :=
  match Nat.beq (Nat.mod l (nat_lit 2)) (nat_lit 0) with
  | true => Nat.add l (nat_lit 1)
  | false => Nat.sub l (nat_lit 1)

def bit (T l : Nat) : Bool := Nat.beq (Nat.land (Nat.shiftRight T l) (nat_lit 1)) (nat_lit 1)

def setBit (T u : Nat) : Nat := Nat.lor T (Nat.shiftLeft (nat_lit 1) u)

lemma bit_eq_testBit (T l : Nat) : bit T l = T.testBit l := by
  have h : Nat.land (Nat.shiftRight T l) 1 = (T >>> l) % 2 := Nat.and_one_is_mod _
  unfold bit
  rw [h, Nat.testBit_eq_decide_div_mod_eq, Nat.shiftRight_eq_div_pow, Bool.eq_iff_iff,
    decide_eq_true_eq]
  exact ⟨Nat.eq_of_beq_eq_true, fun h => h ▸ Nat.beq_refl _⟩

lemma bit_setBit (T u l : Nat) : bit (setBit T u) l = (bit T l || decide (u = l)) := by
  have h : setBit T u = T ||| (1 <<< u) := rfl
  rw [h, bit_eq_testBit, bit_eq_testBit, Nat.testBit_or, Nat.one_shiftLeft, Nat.testBit_two_pow]

def litVal (a : Nat → Bool) (l : Nat) : Bool := a (l / 2) == (l % 2 == 0)

def ClauseSat (a : Nat → Bool) (c : List Nat) : Prop := ∃ l ∈ c, litVal a l = true

def FormulaSat (F : List (List Nat)) : Prop := ∃ a : Nat → Bool, ∀ c ∈ F, ClauseSat a c

lemma litVal_neg (a : Nat → Bool) (l : Nat) : litVal a (neg l) = !litVal a l := by
  have hn : neg l = if l % 2 = 0 then l + 1 else l - 1 := by
    unfold neg
    cases hb : Nat.beq (Nat.mod l 2) 0 with
    | false =>
      have h1 : ¬ (l % 2 = 0) := Nat.ne_of_beq_eq_false hb
      rw [ite_eq_right_of_eq_false _ _ (eq_false h1)]; rfl
    | true =>
      have h1 : l % 2 = 0 := Nat.eq_of_beq_eq_true hb
      rw [ite_eq_left_of_eq_true _ _ (eq_true h1)]
  rw [hn]
  unfold litVal
  by_cases h : l % 2 = 0
  · have h1 : (l + 1) / 2 = l / 2 := by omega
    have h2 : (l + 1) % 2 = 1 := by omega
    rw [ite_eq_left_of_eq_true _ _ (eq_true h), h1, h2, h]
    cases a (l / 2) <;> rfl
  · have h1 : (l - 1) / 2 = l / 2 := by omega
    have h2 : (l - 1) % 2 = 0 := by omega
    have h3 : l % 2 = 1 := by omega
    rw [ite_eq_right_of_eq_false _ _ (eq_false h), h1, h2, h3]
    cases a (l / 2) <;> rfl

abbrev Trie : Type := BinaryTree (Option Nat)

namespace Trie

def get (t : Trie) : Nat → Option Nat :=
  BinaryTree.rec (motive := fun _ => Nat → Option Nat) (fun _ => none)
    (fun v _ _ ihl ihr k =>
      Bool.rec
        (Bool.rec (ihr (Nat.sub (Nat.div k (nat_lit 2)) (nat_lit 1))) (ihl (Nat.div k (nat_lit 2)))
          (Nat.beq (Nat.mod k (nat_lit 2)) (nat_lit 1)))
        v (Nat.beq k (nat_lit 0))) t

def root (t : Trie) : Option Nat := BinaryTree.rec (motive := fun _ => Option Nat) none (fun v _ _ _ _ => v) t
def left (t : Trie) : Trie := BinaryTree.rec (motive := fun _ => Trie) BinaryTree.nil (fun _ l _ _ _ => l) t
def right (t : Trie) : Trie := BinaryTree.rec (motive := fun _ => Trie) BinaryTree.nil (fun _ _ r _ _ => r) t

def set (fuel : Nat) : Trie → Nat → Option Nat → Trie :=
  Nat.rec (motive := fun _ => Trie → Nat → Option Nat → Trie) (fun t _ _ => t)
    (fun _ ih t k o =>
      Bool.rec
        (Bool.rec (BinaryTree.node t.root t.left (ih t.right (Nat.sub (Nat.div k (nat_lit 2)) (nat_lit 1)) o))
          (BinaryTree.node t.root (ih t.left (Nat.div k (nat_lit 2)) o) t.right)
          (Nat.beq (Nat.mod k (nat_lit 2)) (nat_lit 1)))
        (BinaryTree.node o t.left t.right) (Nat.beq k (nat_lit 0))) fuel

def All (P : Nat → Prop) : Trie → Prop
  | BinaryTree.nil => True
  | BinaryTree.node v l r => (∀ c, v = some c → P c) ∧ All P l ∧ All P r

lemma All.get {P : Nat → Prop} :
    ∀ {t : Trie} {k : Nat} {c : Nat}, All P t → t.get k = some c → P c
  | BinaryTree.nil, _, _, _, h => by simp [Trie.get] at h
  | BinaryTree.node v l r, k, c, ⟨hv, hl, hr⟩, h => by
    change Bool.rec (Bool.rec (Trie.get r _) (Trie.get l _) _) v _ = some c at h
    cases h0 : Nat.beq k 0
    · rw [h0] at h
      cases h1 : Nat.beq (Nat.mod k 2) 1
      · rw [h1] at h; exact All.get hr h
      · rw [h1] at h; exact All.get hl h
    · rw [h0] at h; exact hv c h

lemma All.root {P : Nat → Prop} {t : Trie} (h : All P t) :
    ∀ c, t.root = some c → P c := by
  cases t with
  | nil => intro c hc; cases hc
  | node v l r => exact h.1

lemma All.left {P : Nat → Prop} {t : Trie} (h : All P t) : All P t.left := by
  cases t with
  | nil => trivial
  | node v l r => exact h.2.1

lemma All.right {P : Nat → Prop} {t : Trie} (h : All P t) : All P t.right := by
  cases t with
  | nil => trivial
  | node v l r => exact h.2.2

lemma All.set {P : Nat → Prop} :
    ∀ (fuel : Nat) {t : Trie} (k : Nat) {o : Option Nat},
      All P t → (∀ c, o = some c → P c) → All P (Trie.set fuel t k o)
  | 0, _, _, _, ht, _ => ht
  | fuel + 1, t, k, o, ht, ho => by
    change All P (Bool.rec (Bool.rec (BinaryTree.node t.root t.left (Trie.set fuel t.right _ o))
      (BinaryTree.node t.root (Trie.set fuel t.left _ o) t.right) _) (BinaryTree.node o t.left t.right) _)
    cases h0 : Nat.beq k 0
    · cases h1 : Nat.beq (Nat.mod k 2) 1
      · exact ⟨ht.root, ht.left, All.set fuel _ ht.right ho⟩
      · exact ⟨ht.root, All.set fuel _ ht.left ho, ht.right⟩
    · exact ⟨ho, ht.left, ht.right⟩

end Trie

lemma bit_land (x y l : Nat) : bit (Nat.land x y) l = (bit x l && bit y l) := by
  rw [bit_eq_testBit, bit_eq_testBit, bit_eq_testBit]
  exact Nat.testBit_and x y l

lemma bit_xor (x y l : Nat) : bit (Nat.xor x y) l = (bit x l ^^ bit y l) := by
  rw [bit_eq_testBit, bit_eq_testBit, bit_eq_testBit]
  exact Nat.testBit_xor x y l

lemma bit_zero (l : Nat) : bit 0 l = false := by
  rw [bit_eq_testBit]; exact Nat.zero_testBit l

lemma bit_pow (u l : Nat) : bit (Nat.shiftLeft 1 u) l = decide (u = l) := by
  have h : Nat.shiftLeft 1 u = 1 <<< u := rfl
  rw [bit_eq_testBit, h, Nat.one_shiftLeft, Nat.testBit_two_pow]

def mask : List Nat → Nat
  | [] => 0
  | l :: ls => setBit (mask ls) l

lemma bit_mask : ∀ (c : List Nat) (l : Nat), bit (mask c) l = true ↔ l ∈ c
  | [], l => by simp [mask, bit_zero]
  | x :: xs, l => by
    rw [mask, bit_setBit, Bool.or_eq_true, bit_mask xs l, decide_eq_true_eq, List.mem_cons]
    exact ⟨fun h => h.elim Or.inr (fun h => Or.inl h.symm),
      fun h => h.elim (fun h => Or.inr h.symm) Or.inl⟩

abbrev Cont := Trie → Nat → Bool → Nat → Nat → Nat → Bool

def stepRead (k : Cont) (db : Trie) (id C F P x : Nat) : Bool :=
  Bool.rec
    (Bool.rec (k db id false (setBit C x) F P) (k db id true C C 0) (Nat.beq x (nat_lit 0)))
    (k db (Nat.succ x) false C F P)
    (Nat.beq id (nat_lit 0))

def stepUnit (k : Cont) (db : Trie) (id C F P x : Nat) : Bool :=
  Bool.rec false (k db id true C (setBit F (neg x)) 0) (Nat.beq P (Nat.shiftLeft (nat_lit 1) x))

def stepClause (k : Cont) (db : Trie) (id C F D : Nat) : Bool :=
  Bool.rec (k db id true C F (Nat.xor D (Nat.land D F)))
    (Bool.rec (k (db.set 64 (Nat.sub id (nat_lit 1)) (some C)) 0 false 0 0 0) true
      (Nat.beq C (nat_lit 0)))
    (Nat.beq (Nat.xor D (Nat.land D F)) (nat_lit 0))

def stepHint (k : Cont) (db : Trie) (id C F x : Nat) : Bool :=
  Option.rec false (stepClause k db id C F) (db.get x)

def tokenStep (k : Cont) (x : Nat) : Cont := fun db id mode C F P =>
  Bool.rec (stepRead k db id C F P x)
    (Bool.rec (stepUnit k db id C F P x) (stepHint k db id C F x) (Nat.beq P (nat_lit 0)))
    mode

def stop : Cont := fun _ _ _ _ _ _ => false

def runS (e : Cont) (toks : List Nat) : Cont :=
  List.rec (motive := fun _ => Cont) e (fun x _ k => tokenStep k x) toks

def runWord (W M fuel w : Nat) (k : Cont) : Cont :=
  Nat.rec (motive := fun _ => Nat → Cont) (fun _ => k)
    (fun _ ih w =>
      Bool.rec (tokenStep (ih (Nat.shiftRight w W)) (Nat.land w M)) k (Nat.beq w (nat_lit 1)))
    fuel w

def fuelW : Nat := 1024

def runW (e : Cont) (W : Nat) (words : List Nat) : Cont :=
  List.rec (motive := fun _ => Cont) e
    (fun w _ k => runWord W (Nat.sub (Nat.shiftLeft (nat_lit 1) W) (nat_lit 1)) fuelW w k) words

def entryIn (db : Trie) (e : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) false
    (fun q lits _ =>
      Option.rec false (fun D => Nat.beq D (mask lits)) (db.get (Nat.sub q (nat_lit 1)))) e

def verify (B : List (List Nat)) : Cont := fun db _ _ _ _ _ =>
  List.rec (motive := fun _ => Bool) true (fun e _ ih => Bool.rec false ih (entryIn db e)) B

def loadF : List (List Nat) → List Nat → Trie → Trie
  | [], _, t => t
  | _ :: _, [], t => t
  | c :: cs, q :: qs, t =>
    loadF cs qs (Bool.rec (t.set 64 (Nat.sub q 1) (some (mask c))) t (Nat.beq q 0))

def loadB : List (List Nat) → Trie → Trie
  | [], t => t
  | [] :: es, t => loadB es t
  | (q :: lits) :: es, t => loadB es (t.set 64 (Nat.sub q 1) (some (mask lits)))

def check (F : List (List Nat)) (fk : List Nat) (toks : List Nat) : Bool :=
  runS stop toks (loadF F fk .nil) 0 false 0 0 0

def checkW (F : List (List Nat)) (fk : List Nat) (W : Nat) (words : List Nat) : Bool :=
  runW stop W words (loadF F fk .nil) 0 false 0 0 0

def checkFirst (F : List (List Nat)) (fk : List Nat) (W : Nat) (words : List Nat)
    (B : List (List Nat)) : Bool :=
  runW (verify B) W words (loadF F fk .nil) 0 false 0 0 0

def checkSeg (B : List (List Nat)) (W : Nat) (words : List Nat) (B' : List (List Nat)) : Bool :=
  runW (verify B') W words (loadB B .nil) 0 false 0 0 0

def checkLast (B : List (List Nat)) (W : Nat) (words : List Nat) : Bool :=
  runW stop W words (loadB B .nil) 0 false 0 0 0

section Soundness

variable (a : Nat → Bool)

def MaskSat (m : Nat) : Prop := ∃ l, bit m l = true ∧ litVal a l = true

def BitsFalse (F : Nat) : Prop := ∀ l, bit F l = true → litVal a l = false

def EntriesSat (B : List (List Nat)) : Prop := ∀ e ∈ B, ClauseSat a e.tail

def HintInv (C F P : Nat) : Prop :=
  (∀ x, bit C x = true → litVal a x = false) →
    BitsFalse a F ∧ (P = 0 ∨ ∃ w, bit P w = true ∧ litVal a w = true)

lemma witness_U {F D : Nat} (hF : BitsFalse a F) (hD : MaskSat a D) :
    ∃ w, bit (Nat.xor D (Nat.land D F)) w = true ∧ litVal a w = true := by
  obtain ⟨w, hwD, hwv⟩ := hD
  have hwF : bit F w = false := by
    cases hb : bit F w
    · rfl
    · rw [hF w hb] at hwv; exact absurd hwv (by simp)
  exact ⟨w, by rw [bit_xor, bit_land, hwD, hwF]; rfl, hwv⟩

def Good (Q : Prop) (k : Cont) : Prop :=
  ∀ db id mode C F P, db.All (MaskSat a) → (mode = true → HintInv a C F P) →
    k db id mode C F P = true → Q

lemma stop_good (Q : Prop) : Good a Q stop := by
  intro _ _ _ _ _ _ _ _ h
  exact absurd h (by simp [stop])

lemma tokenStep_good {Q : Prop} {k : Cont} (hk : Good a Q k) (x : Nat) :
    Good a Q (tokenStep k x) := by
  intro db id mode C F P hdb hinv h
  change Bool.rec (stepRead k db id C F P x)
    (Bool.rec (stepUnit k db id C F P x) (stepHint k db id C F x) (Nat.beq P 0)) mode = true at h
  cases mode with
  | false =>
    change Bool.rec
      (Bool.rec (k db id false (setBit C x) F P) (k db id true C C 0) (Nat.beq x 0))
      (k db (Nat.succ x) false C F P) (Nat.beq id 0) = true at h
    cases hi : Nat.beq id 0
    · rw [hi] at h
      cases hx : Nat.beq x 0
      · rw [hx] at h
        exact hk db id false _ F P hdb (by simp) h
      · rw [hx] at h
        exact hk db id true C C 0 hdb (fun _ hC => ⟨hC, Or.inl rfl⟩) h
    · rw [hi] at h
      exact hk db _ false C F P hdb (by simp) h
  | true =>
    have hinv := hinv rfl
    cases hP : Nat.beq P 0
    ·
      rw [hP] at h
      change Bool.rec false (k db id true C (setBit F (neg x)) 0)
        (Nat.beq P (Nat.shiftLeft 1 x)) = true at h
      cases hu : Nat.beq P (Nat.shiftLeft 1 x)
      · rw [hu] at h; exact absurd h (by simp)
      · rw [hu] at h
        refine hk db id true C _ 0 hdb (fun _ hC => ⟨?_, Or.inl rfl⟩) h
        obtain ⟨hF, hPw⟩ := hinv hC
        rcases hPw with hP0 | ⟨w, hw, hwv⟩
        · rw [hP0] at hP; exact absurd hP (by simp)
        · rw [Nat.eq_of_beq_eq_true hu, bit_pow, decide_eq_true_eq] at hw
          subst hw
          intro l hl
          rw [bit_setBit, Bool.or_eq_true, decide_eq_true_eq] at hl
          rcases hl with hl | rfl
          · exact hF l hl
          · rw [litVal_neg, hwv]; rfl
    ·
      rw [hP] at h
      change Option.rec false (stepClause k db id C F) (db.get x) = true at h
      cases hg : db.get x with
      | none => rw [hg] at h; exact absurd h (by simp)
      | some D =>
        rw [hg] at h
        have hD : MaskSat a D := Trie.All.get hdb hg
        change Bool.rec (k db id true C F (Nat.xor D (Nat.land D F)))
          (Bool.rec (k (db.set 64 (Nat.sub id 1) (some C)) 0 false 0 0 0) true
            (Nat.beq C 0))
          (Nat.beq (Nat.xor D (Nat.land D F)) 0) = true at h
        cases hU : Nat.beq (Nat.xor D (Nat.land D F)) 0
        · rw [hU] at h
          refine hk db id true C F _ hdb (fun _ hC => ⟨(hinv hC).1, Or.inr ?_⟩) h
          exact witness_U a (hinv hC).1 hD
        · rw [hU] at h

          have hCsat : MaskSat a C := by
            apply Classical.byContradiction
            intro hn
            have hC : ∀ y, bit C y = true → litVal a y = false := by
              intro y hy
              cases hv : litVal a y
              · rfl
              · exact absurd ⟨y, hy, hv⟩ hn
            obtain ⟨w, hw, _⟩ := witness_U a (hinv hC).1 hD
            rw [Nat.eq_of_beq_eq_true hU, bit_zero] at hw
            exact absurd hw (by simp)
          cases hC0 : Nat.beq C 0
          · rw [hC0] at h
            exact hk _ _ false 0 0 0
              (Trie.All.set 64 _ hdb (fun c hc => by cases hc; exact hCsat)) (by simp) h
          · obtain ⟨w, hw, _⟩ := hCsat
            rw [Nat.eq_of_beq_eq_true hC0, bit_zero] at hw
            exact absurd hw (by simp)

lemma runS_good {Q : Prop} {e : Cont} (he : Good a Q e) :
    ∀ toks : List Nat, Good a Q (runS e toks)
  | [] => he
  | x :: xs => tokenStep_good a (runS_good he xs) x

lemma runWord_good {Q : Prop} (W M : Nat) {k : Cont} (hk : Good a Q k) :
    ∀ fuel w, Good a Q (runWord W M fuel w k)
  | 0, _ => hk
  | fuel + 1, w => by
    change Good a Q (Bool.rec (tokenStep (runWord W M fuel (Nat.shiftRight w W) k)
      (Nat.land w M)) k (Nat.beq w 1))
    cases Nat.beq w 1
    · exact tokenStep_good a (runWord_good W M hk fuel _) _
    · exact hk

lemma runW_good {Q : Prop} {e : Cont} (he : Good a Q e) (W : Nat) :
    ∀ words : List Nat, Good a Q (runW e W words)
  | [] => he
  | w :: ws => by
    have h := runWord_good a W (Nat.sub (Nat.shiftLeft 1 W) 1) (runW_good he W ws) fuelW w
    exact h

lemma clauseSat_of_maskSat {c : List Nat} (h : MaskSat a (mask c)) : ClauseSat a c := by
  obtain ⟨l, hl, hv⟩ := h
  exact ⟨l, (bit_mask c l).mp hl, hv⟩

lemma maskSat_of_clauseSat {c : List Nat} (h : ClauseSat a c) : MaskSat a (mask c) := by
  obtain ⟨l, hl, hv⟩ := h
  exact ⟨l, (bit_mask c l).mpr hl, hv⟩

lemma verify_good (B : List (List Nat)) : Good a (EntriesSat a B) (verify B) := by
  intro db _ _ _ _ _ hdb _ h
  induction B with
  | nil => intro e he; simp at he
  | cons e es ih =>
    change Bool.rec false (List.rec (motive := fun _ => Bool) true
      (fun e _ ih => Bool.rec false ih (entryIn db e)) es) (entryIn db e) = true at h
    cases he : entryIn db e
    · rw [he] at h; exact absurd h (by simp)
    · rw [he] at h
      intro e' he'
      rcases List.mem_cons.mp he' with rfl | he'
      · cases e' with
        | nil => simp [entryIn] at he
        | cons q lits =>
          change Option.rec false (fun D => Nat.beq D (mask lits)) (db.get (Nat.sub q 1)) = true
            at he
          cases hg : db.get (Nat.sub q 1) with
          | none => rw [hg] at he; exact absurd he (by simp)
          | some D =>
            rw [hg] at he
            have hD := Trie.All.get hdb hg
            rw [Nat.eq_of_beq_eq_true he] at hD
            exact clauseSat_of_maskSat a hD
      · exact ih h e' he'

lemma loadF_all : ∀ (F : List (List Nat)) (fk : List Nat) {t : Trie}, t.All (MaskSat a) →
    (∀ c ∈ F, ClauseSat a c) → (loadF F fk t).All (MaskSat a)
  | [], _, _, ht, _ => ht
  | _ :: _, [], _, ht, _ => ht
  | c :: cs, q :: qs, t, ht, hF => by
    unfold loadF
    apply loadF_all cs qs _ (fun c' hc' => hF c' (List.mem_cons_of_mem _ hc'))
    cases Nat.beq q 0
    · exact Trie.All.set 64 _ ht (fun c' hc' => by
        cases hc'; exact maskSat_of_clauseSat a (hF c List.mem_cons_self))
    · exact ht

lemma loadB_all : ∀ (B : List (List Nat)) {t : Trie}, t.All (MaskSat a) →
    EntriesSat a B → (loadB B t).All (MaskSat a)
  | [], _, ht, _ => ht
  | [] :: es, _, ht, hB => loadB_all es ht (fun e he => hB e (List.mem_cons_of_mem _ he))
  | (q :: lits) :: es, t, ht, hB => by
    unfold loadB
    apply loadB_all es _ (fun e he => hB e (List.mem_cons_of_mem _ he))
    exact Trie.All.set 64 _ ht (fun c' hc' => by
      cases hc'; exact maskSat_of_clauseSat a (hB _ List.mem_cons_self))

end Soundness

lemma check_sound (F : List (List Nat)) (fk toks : List Nat) (h : check F fk toks = true) :
    ¬ FormulaSat F := by
  rintro ⟨a, ha⟩
  exact runS_good a (stop_good a False) toks _ _ false 0 0 0
    (loadF_all a F fk (t := .nil) trivial ha) (by simp) h

lemma checkW_sound (F : List (List Nat)) (fk : List Nat) (W : Nat) (words : List Nat)
    (h : checkW F fk W words = true) : ¬ FormulaSat F := by
  rintro ⟨a, ha⟩
  exact runW_good a (stop_good a False) W words _ _ false 0 0 0
    (loadF_all a F fk (t := .nil) trivial ha) (by simp) h

lemma checkFirst_sound (F : List (List Nat)) (fk : List Nat) (W : Nat) (words : List Nat)
    (B : List (List Nat)) (h : checkFirst F fk W words B = true) :
    ∀ a, (∀ c ∈ F, ClauseSat a c) → EntriesSat a B := fun a ha =>
  runW_good a (verify_good a B) W words _ _ false 0 0 0
    (loadF_all a F fk (t := .nil) trivial ha) (by simp) h

lemma checkSeg_sound (B : List (List Nat)) (W : Nat) (words : List Nat) (B' : List (List Nat))
    (h : checkSeg B W words B' = true) : ∀ a, EntriesSat a B → EntriesSat a B' := fun a hB =>
  runW_good a (verify_good a B') W words _ _ false 0 0 0
    (loadB_all a B (t := .nil) trivial hB) (by simp) h

lemma checkLast_sound (B : List (List Nat)) (W : Nat) (words : List Nat)
    (h : checkLast B W words = true) : ∀ a, EntriesSat a B → False := fun a hB =>
  runW_good a (stop_good a False) W words _ _ false 0 0 0
    (loadB_all a B (t := .nil) trivial hB) (by simp) h

def unpackWord (W M fuel w : Nat) (rest : List Nat) : List Nat :=
  Nat.rec (motive := fun _ => Nat → List Nat) (fun _ => rest)
    (fun _ ih w => Bool.rec (Nat.land w M :: ih (Nat.shiftRight w W)) rest (Nat.beq w (nat_lit 1)))
    fuel w

def unpack (W : Nat) (words : List Nat) : List Nat :=
  List.rec (motive := fun _ => List Nat) []
    (fun w _ ih => unpackWord W (Nat.sub (Nat.shiftLeft (nat_lit 1) W) (nat_lit 1)) 1024 w ih)
    words

def decodeF (toks : List Nat) : List (List Nat) :=
  List.rec (motive := fun _ => List (List Nat)) []
    (fun x _ acc =>
      Bool.rec (List.rec (motive := fun _ => List (List Nat)) [[x]] (fun c cs _ => (x :: c) :: cs) acc)
        ([] :: acc) (Nat.beq x (nat_lit 0)))
    toks

end Core

end LRAT

namespace CNF

open PEqualNP.CircuitLowerBounds

def litVal (a : Nat → Bool) (l : Nat) : Bool := a (l / 2) == (l % 2 == 0)
def ClauseSat (a : Nat → Bool) (c : List Nat) : Prop := ∃ l ∈ c, litVal a l = true
def FormulaSat (F : List (List Nat)) : Prop := ∃ a : Nat → Bool, ∀ c ∈ F, ClauseSat a c

abbrev Model := (ℕ → ℕ) × (ℕ → ℕ) × (ℕ → ℕ) × ℕ × (ℕ → ℕ → Bool)
def Model.op (M : Model) := M.1
def Model.s1 (M : Model) := M.2.1
def Model.s2 (M : Model) := M.2.2.1
def Model.so (M : Model) := M.2.2.2.1
def Model.w (M : Model) := M.2.2.2.2

variable (input : ℕ → ℕ → Bool)

def Model.sv (n : ℕ) (M : Model) (j k r : ℕ) : Bool :=
  if k < n then input k r else if k < n + j then M.w (k - n) r else false

def gfun (t : ℕ) (a b : Bool) : Bool :=
  if t = 0 then a && b else if t = 1 then a || b else if t = 3 then !a else true

def Valid (n s : ℕ) (g : ℕ → Bool) (R : ℕ → Prop) (M : Model) : Prop :=
  (∀ j < s, M.op j < 4) ∧
  (∀ j < s, M.op j = 3 → M.s1 j = M.s2 j) ∧
  (∀ j < s, M.s1 j ≤ n + j) ∧
  (∀ j < s, M.s2 j ≤ n + j) ∧
  M.so ≤ n + s ∧
  (∀ j < s, ∀ r, R r →
    M.w j r = gfun (M.op j) (M.sv input n j (M.s1 j) r) (M.sv input n j (M.s2 j) r)) ∧
  (∀ r, R r → M.sv input n s M.so r = g r)

lemma Valid.op_lt {input : ℕ → ℕ → Bool} {n s : ℕ} {g : ℕ → Bool} {R : ℕ → Prop} {M : Model}
    (h : Valid input n s g R M) : ∀ j < s, M.op j < 4 := h.1

lemma Valid.not_eq {input : ℕ → ℕ → Bool} {n s : ℕ} {g : ℕ → Bool} {R : ℕ → Prop} {M : Model}
    (h : Valid input n s g R M) : ∀ j < s, M.op j = 3 → M.s1 j = M.s2 j := h.2.1

lemma Valid.s1_le {input : ℕ → ℕ → Bool} {n s : ℕ} {g : ℕ → Bool} {R : ℕ → Prop} {M : Model}
    (h : Valid input n s g R M) : ∀ j < s, M.s1 j ≤ n + j := h.2.2.1

lemma Valid.s2_le {input : ℕ → ℕ → Bool} {n s : ℕ} {g : ℕ → Bool} {R : ℕ → Prop} {M : Model}
    (h : Valid input n s g R M) : ∀ j < s, M.s2 j ≤ n + j := h.2.2.2.1

lemma Valid.so_le {input : ℕ → ℕ → Bool} {n s : ℕ} {g : ℕ → Bool} {R : ℕ → Prop} {M : Model}
    (h : Valid input n s g R M) : M.so ≤ n + s := h.2.2.2.2.1

lemma Valid.w_eq {input : ℕ → ℕ → Bool} {n s : ℕ} {g : ℕ → Bool} {R : ℕ → Prop} {M : Model}
    (h : Valid input n s g R M) : ∀ j < s, ∀ r, R r → M.w j r = gfun (M.op j) (M.sv input n j (M.s1 j) r) (M.sv input n j (M.s2 j) r) := h.2.2.2.2.2.1

lemma Valid.out_eq {input : ℕ → ℕ → Bool} {n s : ℕ} {g : ℕ → Bool} {R : ℕ → Prop} {M : Model}
    (h : Valid input n s g R M) : ∀ r, R r → M.sv input n s M.so r = g r := h.2.2.2.2.2.2

section formula
variable (n s : ℕ)


def wd : ℕ := 128 + n + s + 2


def ix (kd j a : ℕ) : ℕ := (kd * (s + 1) + j) * wd n s + a


def P (v : ℕ) : ℕ := 2 * v + 2

def Q (v : ℕ) : ℕ := 2 * v + 3

def L (v : ℕ) (b : Bool) : ℕ := if b then P v else Q v


def pairs (m : ℕ) : List (ℕ × ℕ) :=
  (List.range m).flatMap fun b => (List.range b).map fun a => (a, b)


def fOp : List (List ℕ) :=
  (List.range s).map fun j => [P (ix n s 0 j 0), P (ix n s 0 j 1), P (ix n s 0 j 2),
    P (ix n s 0 j 3)]


def fSrcAlo : List (List ℕ) :=
  [1, 2].flatMap fun e => (List.range s).map fun j =>
    (List.range (n + j + 1)).map fun k => P (ix n s e j k)


def srcEq (e j k r : ℕ) : List (List ℕ) :=
  if k < n then [[Q (ix n s e j k), L (ix n s (e + 3) j r) (input k r)]]
  else if k < n + j then
    [[Q (ix n s e j k), Q (ix n s (e + 3) j r), P (ix n s 3 (k - n) r)],
     [Q (ix n s e j k), P (ix n s (e + 3) j r), Q (ix n s 3 (k - n) r)]]
  else [[Q (ix n s e j k), Q (ix n s (e + 3) j r)]]

def fSrcEq (rows : List ℕ) : List (List ℕ) :=
  [1, 2].flatMap fun e => (List.range s).flatMap fun j => rows.flatMap fun r =>
    (List.range (n + j + 1)).flatMap fun k => srcEq input n s e j k r


def gateCl (j r : ℕ) : List (List ℕ) :=
  [[Q (ix n s 0 j 0), Q (ix n s 3 j r), P (ix n s 4 j r)],
   [Q (ix n s 0 j 0), Q (ix n s 3 j r), P (ix n s 5 j r)],
   [Q (ix n s 0 j 0), P (ix n s 3 j r), Q (ix n s 4 j r), Q (ix n s 5 j r)],
   [Q (ix n s 0 j 1), P (ix n s 3 j r), Q (ix n s 4 j r)],
   [Q (ix n s 0 j 1), P (ix n s 3 j r), Q (ix n s 5 j r)],
   [Q (ix n s 0 j 1), Q (ix n s 3 j r), P (ix n s 4 j r), P (ix n s 5 j r)],
   [Q (ix n s 0 j 2), P (ix n s 3 j r)],
   [Q (ix n s 0 j 3), P (ix n s 3 j r), P (ix n s 4 j r)],
   [Q (ix n s 0 j 3), Q (ix n s 3 j r), Q (ix n s 4 j r)]]

def fGate (rows : List ℕ) : List (List ℕ) :=
  (List.range s).flatMap fun j => rows.flatMap fun r => gateCl n s j r


def fOutAlo : List (List ℕ) := [(List.range (n + s + 1)).map fun k => P (ix n s 6 0 k)]


def outEq (g : ℕ → Bool) (k r : ℕ) : List (List ℕ) :=
  if k < n then (if input k r = g r then [] else [[Q (ix n s 6 0 k)]])
  else if k < n + s then [[Q (ix n s 6 0 k), L (ix n s 3 (k - n) r) (g r)]]
  else if g r = true then [[Q (ix n s 6 0 k)]] else []

def fOutEq (g : ℕ → Bool) (rows : List ℕ) : List (List ℕ) :=
  rows.flatMap fun r => (List.range (n + s + 1)).flatMap fun k => outEq input n s g k r

def enc (g : ℕ → Bool) (rows : List ℕ) : List (List ℕ) :=
  fOp n s ++ fSrcAlo n s ++ fSrcEq input n s rows ++ fGate n s rows ++
    fOutAlo n s ++ fOutEq input n s g rows

end formula

def meaning (n : ℕ) (M : Model) (kd j a : ℕ) : Bool :=
  if kd = 0 then M.op j == a else if kd = 1 then M.s1 j == a else if kd = 2 then M.s2 j == a
  else if kd = 3 then M.w j a else if kd = 4 then M.sv input n j (M.s1 j) a
  else if kd = 5 then M.sv input n j (M.s2 j) a else if kd = 6 then M.so == a else false

def val (n s : ℕ) (M : Model) (x : ℕ) : Bool :=
  meaning input n M ((x - 1) / wd n s / (s + 1)) ((x - 1) / wd n s % (s + 1)) ((x - 1) % wd n s)

lemma val_ix (n s : ℕ) (M : Model) {kd j a : ℕ} (hj : j ≤ s) (ha : a < wd n s) :
    val input n s M (ix n s kd j a + 1) = meaning input n M kd j a := by
  have hw : 0 < wd n s := Nat.succ_pos _
  unfold val ix
  rw [Nat.add_sub_cancel]
  have h1 : ((kd * (s + 1) + j) * wd n s + a) / wd n s = kd * (s + 1) + j := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hw, Nat.div_eq_of_lt ha, Nat.zero_add]
  have h2 : ((kd * (s + 1) + j) * wd n s + a) % wd n s = a := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt ha]
  have h3 : (kd * (s + 1) + j) / (s + 1) = kd := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt (by omega),
      Nat.zero_add]
  have h4 : (kd * (s + 1) + j) % (s + 1) = j := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (by omega)]
  rw [h1, h2, h3, h4]

lemma litVal_P (a : ℕ → Bool) (v : ℕ) : litVal a (P v) = a (v + 1) := by
  unfold litVal P
  rw [show (2 * v + 2) / 2 = v + 1 by omega, show (2 * v + 2) % 2 = 0 by omega]
  cases a (v + 1) <;> rfl

lemma litVal_Q (a : ℕ → Bool) (v : ℕ) : litVal a (Q v) = !a (v + 1) := by
  unfold litVal Q
  rw [show (2 * v + 3) / 2 = v + 1 by omega, show (2 * v + 3) % 2 = 1 by omega]
  cases a (v + 1) <;> rfl

lemma litVal_L (a : ℕ → Bool) (v : ℕ) (b : Bool) : litVal a (L v b) = (a (v + 1) == b) := by
  cases b <;> simp [L, litVal_P, litVal_Q]

lemma cs_cons (a : ℕ → Bool) (l : ℕ) (c : List ℕ) :
    ClauseSat a (l :: c) ↔ litVal a l = true ∨ ClauseSat a c := by
  simp [ClauseSat]

lemma cs_nil (a : ℕ → Bool) : ClauseSat a [] ↔ False := by simp [ClauseSat]

lemma cs_of_mem {a : ℕ → Bool} {c : List ℕ} {l : ℕ} (h : l ∈ c) (hl : litVal a l = true) :
    ClauseSat a c := ⟨l, h, hl⟩

section vlemmas
variable {n s : ℕ} (M : Model) {j a : ℕ}

lemma wd_lt1 (h : a ≤ n + s + 2) : a < wd n s := by
  unfold wd; omega
lemma wd_lt2 (h : a < 128) : a < wd n s := by unfold wd; omega

lemma v_op (hj : j ≤ s) (ha : a < wd n s) : val input n s M (ix n s 0 j a + 1) = (M.op j == a) := by
  rw [val_ix input n s M hj ha]; simp [meaning]
lemma v_s1 (hj : j ≤ s) (ha : a < wd n s) : val input n s M (ix n s 1 j a + 1) = (M.s1 j == a) := by
  rw [val_ix input n s M hj ha]; simp [meaning]
lemma v_s2 (hj : j ≤ s) (ha : a < wd n s) : val input n s M (ix n s 2 j a + 1) = (M.s2 j == a) := by
  rw [val_ix input n s M hj ha]; simp [meaning]
lemma v_w (hj : j ≤ s) (ha : a < wd n s) : val input n s M (ix n s 3 j a + 1) = M.w j a := by
  rw [val_ix input n s M hj ha]; simp [meaning]
lemma v_u1 (hj : j ≤ s) (ha : a < wd n s) :
    val input n s M (ix n s 4 j a + 1) = M.sv input n j (M.s1 j) a := by
  rw [val_ix input n s M hj ha]; simp [meaning]
lemma v_u2 (hj : j ≤ s) (ha : a < wd n s) :
    val input n s M (ix n s 5 j a + 1) = M.sv input n j (M.s2 j) a := by
  rw [val_ix input n s M hj ha]; simp [meaning]
lemma v_so (ha : a < wd n s) : val input n s M (ix n s 6 0 a + 1) = (M.so == a) := by
  rw [val_ix input n s M (Nat.zero_le _) ha]; simp [meaning]
end vlemmas


def Model.src (M : Model) (e j : ℕ) : ℕ := if e = 1 then M.s1 j else M.s2 j

lemma v_src {n s : ℕ} (M : Model) {e j a : ℕ} (he : e = 1 ∨ e = 2) (hj : j ≤ s)
    (ha : a < wd n s) : val input n s M (ix n s e j a + 1) = (M.src e j == a) := by
  rcases he with rfl | rfl
  · exact v_s1 input M hj ha
  · exact v_s2 input M hj ha

lemma v_u {n s : ℕ} (M : Model) {e j a : ℕ} (he : e = 1 ∨ e = 2) (hj : j ≤ s)
    (ha : a < wd n s) : val input n s M (ix n s (e + 3) j a + 1) = M.sv input n j (M.src e j) a := by
  rcases he with rfl | rfl
  · exact v_u1 input M hj ha
  · exact v_u2 input M hj ha

section sound
variable {n s : ℕ} {g : ℕ → Bool} {rows : List ℕ} {M : Model}
  (hrows : ∀ r ∈ rows, r < 128) (hv : Valid input n s g (· ∈ rows) M)
include hv

lemma src_le {e j : ℕ} (he : e = 1 ∨ e = 2) (hj : j < s) : M.src e j ≤ n + j := by
  rcases he with rfl | rfl
  · simpa [Model.src] using hv.s1_le j hj
  · simpa [Model.src] using hv.s2_le j hj

lemma s_fOp : ∀ c ∈ fOp n s, ClauseSat (val input n s M) c := by
  intro c hc
  simp only [fOp, List.mem_map, List.mem_range] at hc
  obtain ⟨j, hj, rfl⟩ := hc
  have := hv.op_lt j hj
  simp (disch := (first | omega | (apply wd_lt1; omega) | (apply wd_lt2; assumption))) only [cs_cons, cs_nil, litVal_P, v_op, beq_iff_eq, or_false]
  omega

lemma s_fSrcAlo : ∀ c ∈ fSrcAlo n s, ClauseSat (val input n s M) c := by
  intro c hc
  simp only [fSrcAlo, List.mem_flatMap, List.mem_map, List.mem_range, List.mem_cons,
    List.not_mem_nil, or_false] at hc
  obtain ⟨e, he, j, hj, rfl⟩ := hc
  have hle := src_le input hv he hj
  apply cs_of_mem (List.mem_map.2 ⟨M.src e j, List.mem_range.2 (by omega), rfl⟩)
  rw [litVal_P, v_src input M he (by omega) (wd_lt1 (by omega))]
  simp

include hrows in
lemma s_fSrcEq : ∀ c ∈ fSrcEq input n s rows, ClauseSat (val input n s M) c := by
  intro c hc
  simp only [fSrcEq, List.mem_flatMap, List.mem_range, List.mem_cons, List.not_mem_nil,
    or_false] at hc
  obtain ⟨e, he, j, hj, r, hr, k, hk, hc⟩ := hc
  have hr' := hrows r hr
  unfold srcEq at hc
  split_ifs at hc with h1 h2
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    subst hc
    simp (disch := (first | omega | (apply wd_lt1; omega) | (apply wd_lt2; assumption))) only [cs_cons, cs_nil, litVal_Q, litVal_L, v_src input M he, v_u input M he,
      or_false]
    by_cases hs : M.src e j = k
    · right; rw [hs]; simp [Model.sv, h1]
    · left; simp [hs]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl <;>
    · simp (disch := (first | omega | (apply wd_lt1; omega) | (apply wd_lt2; assumption))) only [cs_cons, cs_nil, litVal_Q, litVal_P, v_src input M he, v_u input M he, v_w,
        or_false]
      by_cases hs : M.src e j = k
      · rw [hs]
        have : M.sv input n j k r = M.w (k - n) r := by simp [Model.sv, h1, h2]
        rw [this]
        cases M.w (k - n) r <;> simp
      · simp [hs]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    subst hc
    simp (disch := (first | omega | (apply wd_lt1; omega) | (apply wd_lt2; assumption))) only [cs_cons, cs_nil, litVal_Q, v_src input M he, v_u input M he, or_false]
    by_cases hs : M.src e j = k
    · right; rw [hs]; simp [Model.sv, h1, h2]
    · left; simp [hs]

omit hv in
lemma gate_fact (t : ℕ) (ht : t < 4) (x a b : Bool) (hw : x = gfun t a b) :
    ((!(t == 0) || !x || a) = true) ∧ ((!(t == 0) || !x || b) = true) ∧
    ((!(t == 0) || x || !a || !b) = true) ∧ ((!(t == 1) || x || !a) = true) ∧
    ((!(t == 1) || x || !b) = true) ∧ ((!(t == 1) || !x || a || b) = true) ∧
    ((!(t == 2) || x) = true) ∧ ((!(t == 3) || x || a) = true) ∧
    ((!(t == 3) || !x || !a) = true) := by
  interval_cases t <;> cases x <;> cases a <;> cases b <;> simp_all [gfun]

include hrows in
lemma s_fGate : ∀ c ∈ fGate n s rows, ClauseSat (val input n s M) c := by
  intro c hc
  simp only [fGate, List.mem_flatMap, List.mem_range] at hc
  obtain ⟨j, hj, r, hr, hc⟩ := hc
  have hr' := hrows r hr
  have G := gate_fact _ (hv.op_lt j hj) _ _ _ (hv.w_eq j hj r hr)
  simp only [gateCl, List.mem_cons, List.not_mem_nil, or_false] at hc
  obtain ⟨G1, G2, G3, G4, G5, G6, G7, G8, G9⟩ := G
  simp only [Bool.or_eq_true, or_assoc] at G1 G2 G3 G4 G5 G6 G7 G8 G9
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp (disch := (first | omega | (apply wd_lt1; omega) | (apply wd_lt2; assumption))) only [cs_cons, cs_nil, litVal_Q, litVal_P, v_op, v_w, v_u1, v_u2,
      or_false, or_assoc] <;> assumption

lemma s_fOutAlo : ∀ c ∈ fOutAlo n s, ClauseSat (val input n s M) c := by
  intro c hc
  simp only [fOutAlo, List.mem_cons, List.not_mem_nil, or_false] at hc
  subst hc
  have := hv.so_le
  apply cs_of_mem (List.mem_map.2 ⟨M.so, List.mem_range.2 (by omega), rfl⟩)
  rw [litVal_P, v_so input M (wd_lt1 (by omega))]
  simp

include hrows in
lemma s_fOutEq : ∀ c ∈ fOutEq input n s g rows, ClauseSat (val input n s M) c := by
  intro c hc
  simp only [fOutEq, List.mem_flatMap, List.mem_range] at hc
  obtain ⟨r, hr, k, hk, hc⟩ := hc
  have hr' := hrows r hr
  have ho := hv.out_eq r hr
  unfold outEq at hc
  by_cases h1 : k < n
  · rw [if_pos h1] at hc
    by_cases h2 : input k r = g r
    · rw [if_pos h2] at hc; simp at hc
    · rw [if_neg h2] at hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      subst hc
      simp (disch := (first | omega | (apply wd_lt1; omega) | (apply wd_lt2; assumption))) only [cs_cons, cs_nil, litVal_Q, v_so, or_false]
      by_cases e : M.so = k
      · rw [e] at ho
        simp only [Model.sv, if_pos h1] at ho
        exact absurd ho h2
      · simp [e]
  · rw [if_neg h1] at hc
    by_cases h3 : k < n + s
    · rw [if_pos h3] at hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      subst hc
      simp (disch := (first | omega | (apply wd_lt1; omega) | (apply wd_lt2; assumption))) only [cs_cons, cs_nil, litVal_Q, litVal_L, v_so, v_w, or_false]
      by_cases e : M.so = k
      · rw [e] at ho
        simp only [Model.sv, if_neg h1, if_pos h3] at ho
        right; rw [ho]; simp
      · simp [e]
    · rw [if_neg h3] at hc
      by_cases h4 : g r = true
      · rw [if_pos h4] at hc
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
        subst hc
        simp (disch := (first | omega | (apply wd_lt1; omega) | (apply wd_lt2; assumption))) only [cs_cons, cs_nil, litVal_Q, v_so, or_false]
        by_cases e : M.so = k
        · rw [e] at ho
          simp only [Model.sv, if_neg h1, if_neg h3] at ho
          rw [h4] at ho
          exact absurd ho Bool.false_ne_true
        · simp [e]
      · rw [if_neg h4] at hc; simp at hc

end sound

lemma enc_sat {n s : ℕ} {g : ℕ → Bool} {rows : List ℕ} {M : Model}
    (hrows : ∀ r ∈ rows, r < 128) (hv : Valid input n s g (· ∈ rows) M) :
    ∀ c ∈ enc input n s g rows, ClauseSat (val input n s M) c := by
  intro c hc
  simp only [enc, List.mem_append] at hc
  rcases hc with (((((h | h) | h) | h) | h) | h)
  · exact s_fOp input hv c h
  · exact s_fSrcAlo input hv c h
  · exact s_fSrcEq input hrows hv c h
  · exact s_fGate input hrows hv c h
  · exact s_fOutAlo input hv c h
  · exact s_fOutEq input hrows hv c h

section extra
variable (n s : ℕ)

def fOpAMO : List (List ℕ) :=
  (List.range s).flatMap fun j => (List.range 4).flatMap fun t =>
    (List.range t).map fun u => [Q (ix n s 0 j t), Q (ix n s 0 j u)]
def fSrcAMO : List (List ℕ) :=
  [1, 2].flatMap fun e => (List.range s).flatMap fun j =>
    (List.range (n + j + 1)).flatMap fun k =>
      (List.range k).map fun l => [Q (ix n s e j k), Q (ix n s e j l)]
def fOutAMO : List (List ℕ) :=
  (List.range (n + s + 1)).flatMap fun k =>
    (List.range k).map fun l => [Q (ix n s 6 0 k), Q (ix n s 6 0 l)]
def fNot : List (List ℕ) :=
  (List.range s).flatMap fun j => (List.range (n + j + 1)).map fun k =>
    [Q (ix n s 0 j 3), Q (ix n s 1 j k), P (ix n s 2 j k)]
def fNoTrue : List (List ℕ) :=
  (List.range s).map fun j => [Q (ix n s 0 j 2)]
def fStrict : List (List ℕ) :=
  ([1, 2].flatMap fun e => (List.range s).map fun j => [Q (ix n s e j (n + j))]) ++
    [[Q (ix n s 6 0 (n + s))]]
def fOrdered : List (List ℕ) :=
  (List.range s).flatMap fun j => (List.range (n + j + 1)).flatMap fun k =>
    (List.range k).map fun l => [Q (ix n s 1 j k), Q (ix n s 2 j l)]
def fLast : List (List ℕ) := [[P (ix n s 6 0 (n + s - 1))]]
def notAtMost : List (List ℕ) :=
  (List.range s).flatMap fun j => (List.range j).map fun i =>
    [Q (ix n s 0 j 3), Q (ix n s 0 i 3)]
def notAtLeast : List (List ℕ) :=
  [(List.range s).map fun j => P (ix n s 0 j 3)]
def encOne (g : ℕ → Bool) (rows : List ℕ) : List (List ℕ) :=
  enc input n s g rows ++ notAtMost n s ++ notAtLeast n s

end extra

section extraSound
variable {n s : ℕ} {M : Model}

lemma s_fOpAMO : ∀ c ∈ fOpAMO n s, ClauseSat (val input n s M) c := by
  intro c hc
  simp only [fOpAMO, List.mem_flatMap, List.mem_map, List.mem_range] at hc
  obtain ⟨j, hj, t, ht, u, hu, rfl⟩ := hc
  simp (disch := (first | omega | (apply wd_lt1; omega))) only
    [cs_cons, cs_nil, litVal_Q, v_op, or_false, Bool.not_eq_true', beq_eq_false_iff_ne]
  omega

lemma s_fSrcAMO : ∀ c ∈ fSrcAMO n s, ClauseSat (val input n s M) c := by
  intro c hc
  simp only [fSrcAMO, List.mem_flatMap, List.mem_map, List.mem_range,
    List.mem_cons, List.not_mem_nil, or_false] at hc
  obtain ⟨e, he, j, hj, k, hk, l, hl, rfl⟩ := hc
  simp (disch := (first | omega | (apply wd_lt1; omega))) only
    [cs_cons, cs_nil, litVal_Q, v_src input M he, or_false, Bool.not_eq_true',
     beq_eq_false_iff_ne]
  omega

lemma s_fOutAMO : ∀ c ∈ fOutAMO n s, ClauseSat (val input n s M) c := by
  intro c hc
  simp only [fOutAMO, List.mem_flatMap, List.mem_map, List.mem_range] at hc
  obtain ⟨k, hk, l, hl, rfl⟩ := hc
  simp (disch := (first | omega | (apply wd_lt1; omega))) only
    [cs_cons, cs_nil, litVal_Q, v_so, or_false, Bool.not_eq_true', beq_eq_false_iff_ne]
  omega

lemma s_fNot {g : ℕ → Bool} {rows : List ℕ} (hv : Valid input n s g (· ∈ rows) M) :
    ∀ c ∈ fNot n s, ClauseSat (val input n s M) c := by
  intro c hc
  simp only [fNot, List.mem_flatMap, List.mem_map, List.mem_range] at hc
  obtain ⟨j, hj, k, hk, rfl⟩ := hc
  have hn := hv.not_eq j hj
  simp (disch := (first | omega | (apply wd_lt1; omega))) only
    [cs_cons, cs_nil, litVal_Q, litVal_P, v_op, v_s1, v_s2, or_false,
     Bool.not_eq_true', beq_eq_false_iff_ne, beq_iff_eq]
  omega

lemma s_fNoTrue (h : ∀ j < s, M.op j ≠ 2) :
    ∀ c ∈ fNoTrue n s, ClauseSat (val input n s M) c := by
  intro c hc
  simp only [fNoTrue, List.mem_map, List.mem_range] at hc
  obtain ⟨j, hj, rfl⟩ := hc
  simp (disch := (first | omega | (apply wd_lt1; omega))) only
    [cs_cons, cs_nil, litVal_Q, v_op, or_false, Bool.not_eq_true', beq_eq_false_iff_ne]
  exact h j hj

lemma s_fStrict (h : ∀ j < s, M.s1 j < n + j ∧ M.s2 j < n + j) (ho : M.so < n + s) :
    ∀ c ∈ fStrict n s, ClauseSat (val input n s M) c := by
  intro c hc
  simp only [fStrict, List.mem_append, List.mem_flatMap, List.mem_map, List.mem_range,
    List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with ⟨e, he, j, hj, rfl⟩ | rfl
  · have hh := h j hj
    rcases he with rfl | rfl <;>
      simp (disch := (first | omega | (apply wd_lt1; omega))) only
        [cs_cons, cs_nil, litVal_Q, v_s1, v_s2, or_false, Bool.not_eq_true',
         beq_eq_false_iff_ne] <;> omega
  · simp (disch := (first | omega | (apply wd_lt1; omega))) only
      [cs_cons, cs_nil, litVal_Q, v_so, or_false, Bool.not_eq_true', beq_eq_false_iff_ne]
    omega

lemma s_fOrdered (h : ∀ j < s, M.s1 j ≤ M.s2 j) :
    ∀ c ∈ fOrdered n s, ClauseSat (val input n s M) c := by
  intro c hc
  simp only [fOrdered, List.mem_flatMap, List.mem_map, List.mem_range] at hc
  obtain ⟨j, hj, k, hk, l, hl, rfl⟩ := hc
  have hh := h j hj
  simp (disch := (first | omega | (apply wd_lt1; omega))) only
    [cs_cons, cs_nil, litVal_Q, v_s1, v_s2, or_false, Bool.not_eq_true',
     beq_eq_false_iff_ne]
  omega

lemma s_fLast (h : M.so = n + s - 1) :
    ∀ c ∈ fLast n s, ClauseSat (val input n s M) c := by
  intro c hc
  simp only [fLast, List.mem_cons, List.not_mem_nil, or_false] at hc
  subst c
  simp (disch := (first | omega | (apply wd_lt1; omega))) only
    [cs_cons, cs_nil, litVal_P, v_so, or_false, beq_iff_eq]
  exact h

lemma s_notAtMost (h : ∀ i < s, ∀ j < s, M.op i = 3 → M.op j = 3 → i = j) :
    ∀ c ∈ notAtMost n s, ClauseSat (val input n s M) c := by
  intro c hc
  simp only [notAtMost, List.mem_flatMap, List.mem_map, List.mem_range] at hc
  obtain ⟨j, hj, i, hi, rfl⟩ := hc
  have hh := h i (by omega) j hj
  simp (disch := (first | omega | (apply wd_lt1; omega))) only
    [cs_cons, cs_nil, litVal_Q, v_op, or_false, Bool.not_eq_true', beq_eq_false_iff_ne]
  omega

lemma s_notAtLeast (h : ∃ j < s, M.op j = 3) :
    ∀ c ∈ notAtLeast n s, ClauseSat (val input n s M) c := by
  intro c hc
  simp only [notAtLeast, List.mem_cons, List.not_mem_nil, or_false] at hc
  subst c
  obtain ⟨j, hj, hop⟩ := h
  apply cs_of_mem (List.mem_map.2 ⟨j, List.mem_range.2 hj, rfl⟩)
  rw [litVal_P, v_op input M (by omega) (wd_lt1 (by omega)), hop]
  rfl

end extraSound

lemma encOne_sat {n s : ℕ} {g : ℕ → Bool} {rows : List ℕ} {M : Model}
    (hrows : ∀ r ∈ rows, r < 128) (hv : Valid input n s g (· ∈ rows) M)
    (hnot : ∀ i < s, ∀ j < s, M.op i = 3 → M.op j = 3 → i = j)
    (hex : ∃ j < s, M.op j = 3) : FormulaSat (encOne input n s g rows) := by
  refine ⟨val input n s M, ?_⟩
  intro c hc
  simp only [encOne, List.mem_append] at hc
  rcases hc with (hc | hc) | hc
  · exact enc_sat input hrows hv c hc
  · exact s_notAtMost input hnot c hc
  · exact s_notAtLeast input hex c hc

def notNone (n s : ℕ) : List (List ℕ) :=
  (List.range s).map fun j => [Q (ix n s 0 j 3)]

lemma s_notNone {n s : ℕ} {M : Model} (h : ∀ j < s, M.op j ≠ 3) :
    ∀ c ∈ notNone n s, ClauseSat (val input n s M) c := by
  intro c hc
  simp only [notNone, List.mem_map, List.mem_range] at hc
  obtain ⟨j, hj, rfl⟩ := hc
  simp (disch := (first | omega | (apply wd_lt1; omega))) only
    [cs_cons, cs_nil, litVal_Q, v_op, or_false, Bool.not_eq_true', beq_eq_false_iff_ne]
  exact h j hj

def encTight (n s : ℕ) (g : ℕ → Bool) (rows : List ℕ) : List (List ℕ) :=
  enc input n s g rows ++ fOpAMO n s ++ fSrcAMO n s ++ fOutAMO n s ++ fNot n s ++
    fNoTrue n s ++ fStrict n s ++ fOrdered n s ++ fLast n s ++
    notAtMost n s ++ notAtLeast n s

lemma encTight_sat {n s : ℕ} {g : ℕ → Bool} {rows : List ℕ} {M : Model}
    (hrows : ∀ r ∈ rows, r < 128) (hv : Valid input n s g (· ∈ rows) M)
    (hnoTrue : ∀ j < s, M.op j ≠ 2)
    (hstrict : ∀ j < s, M.s1 j < n + j ∧ M.s2 j < n + j) (hout : M.so < n + s)
    (hordered : ∀ j < s, M.s1 j ≤ M.s2 j) (hlast : M.so = n + s - 1)
    (hnot : ∀ i < s, ∀ j < s, M.op i = 3 → M.op j = 3 → i = j)
    (hex : ∃ j < s, M.op j = 3) : FormulaSat (encTight input n s g rows) := by
  refine ⟨val input n s M, ?_⟩
  intro c hc
  simp only [encTight, List.mem_append] at hc
  rcases hc with ((((((((((hc | hc) | hc) | hc) | hc) | hc) | hc) | hc) | hc) | hc) | hc)
  · exact enc_sat input hrows hv c hc
  · exact s_fOpAMO input c hc
  · exact s_fSrcAMO input c hc
  · exact s_fOutAMO input c hc
  · exact s_fNot input hv c hc
  · exact s_fNoTrue input hnoTrue c hc
  · exact s_fStrict input hstrict hout c hc
  · exact s_fOrdered input hordered c hc
  · exact s_fLast input hlast c hc
  · exact s_notAtMost input hnot c hc
  · exact s_notAtLeast input hex c hc

def basisGate (g : Gate) : Prop :=
  (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2

def padRun (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun v g => v ++ [g.op.eval (g.inputs.map fun i => v.getD i false)]) w

lemma padRun_append (gs hs : List Gate) (w : List Bool) :
    padRun (gs ++ hs) w = padRun hs (padRun gs w) := by
  simp only [padRun, List.foldl_append]

lemma padRun_length (gs : List Gate) (w : List Bool) :
    (padRun gs w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp [padRun]
  | cons g gs ih =>
    change (padRun gs (w ++ [_])).length = _
    rw [ih]
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega

lemma padRun_prefix (gs : List Gate) (w : List Bool) :
    ∃ tail, padRun gs w = w ++ tail := by
  induction gs generalizing w with
  | nil => exact ⟨[], by simp [padRun]⟩
  | cons g gs ih =>
    obtain ⟨tail, ht⟩ := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    exact ⟨_ :: tail, by simpa only [padRun, List.foldl_cons, List.append_assoc,
      List.singleton_append] using ht⟩

lemma padRun_getD (gs : List Gate) (w : List Bool) (o : ℕ) (ho : o < w.length) :
    (padRun gs w).getD o false = w.getD o false := by
  obtain ⟨tail, ht⟩ := padRun_prefix gs w
  rw [ht, List.getD_append _ _ _ _ ho]


lemma wires_eq (C : Circuit) (x : List Bool) : C.wires x = padRun C.gates x := rfl

variable (input : ℕ → ℕ → Bool)

def xr (n r : ℕ) : List Bool := List.ofFn fun i : Fin n => input i r


def nm (n j a : ℕ) : ℕ := if a < n + j then a else n + j


def code (n : ℕ) (g : Gate) (j : ℕ) : ℕ × ℕ × ℕ :=
  match g.op, g.inputs with
  | .and, [] => (2, n + j, n + j)
  | .and, [a] => (0, nm n j a, nm n j a)
  | .and, a :: b :: _ => (0, nm n j a, nm n j b)
  | .or, [] => (1, n + j, n + j)
  | .or, [a] => (1, nm n j a, nm n j a)
  | .or, a :: b :: _ => (1, nm n j a, nm n j b)
  | .not, [] => (3, n + j, n + j)
  | .not, a :: _ => (3, nm n j a, nm n j a)
  | _, _ => (2, n + j, n + j)


def gateAt (C : Circuit) (j : ℕ) : Gate := C.gates.getD j ⟨.and, []⟩


def ofCirc (n s : ℕ) (C : Circuit) : Model :=
  ((fun j => (code n (gateAt C j) j).1),
   (fun j => (code n (gateAt C j) j).2.1),
   (fun j => (code n (gateAt C j) j).2.2),
   (if C.output < n + C.gates.length then C.output else n + s),
   (fun j r => if j < C.gates.length then (C.wires (xr input n r)).getD (n + j) false else true))

lemma xr_length (n r : ℕ) : (xr input n r).length = n := by simp [xr]

lemma xr_getD (n r a : ℕ) (ha : a < n) : (xr input n r).getD a false = input a r := by
  simp [xr, List.getD_eq_getElem?_getD, ha]

lemma code_le (n : ℕ) (g : Gate) (j : ℕ) :
    (code n g j).1 < 4 ∧ (code n g j).2.1 ≤ n + j ∧ (code n g j).2.2 ≤ n + j := by
  have h : ∀ a, nm n j a ≤ n + j := fun a => by unfold nm; split_ifs <;> omega
  rcases g with ⟨op, ins⟩
  cases op <;> rcases ins with _ | ⟨a, _ | ⟨b, l⟩⟩ <;> simp [code, h]

lemma code_not (n : ℕ) (g : Gate) (j : ℕ) (h : (code n g j).1 = 3) :
    (code n g j).2.1 = (code n g j).2.2 := by
  rcases g with ⟨op, ins⟩
  cases op <;> rcases ins with _ | ⟨a, _ | ⟨b, l⟩⟩ <;> simp_all [code]

lemma code_eval (n : ℕ) (g : Gate) (hop : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp))
    (hlen : g.inputs.length ≤ 2) (j : ℕ) (S : ℕ → Bool) (hS : S (n + j) = false) :
    g.op.eval (g.inputs.map fun i => S (nm n j i)) =
      gfun (code n g j).1 (S (code n g j).2.1) (S (code n g j).2.2) := by
  rcases g with ⟨op, ins⟩
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
  dsimp only at hlen
  rcases hop with rfl | rfl | rfl <;>
    rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;>
    simp_all [code, GateOp.eval, gfun]


lemma wire_gate (C : Circuit) (x : List Bool) (j : ℕ) (hj : j < C.gates.length) :
    (C.wires x).getD (x.length + j) false =
      (gateAt C j).op.eval ((gateAt C j).inputs.map fun i =>
        (padRun (C.gates.take j) x).getD i false) ∧
    ∀ i, (padRun (C.gates.take j) x).getD i false =
      if i < x.length + j then (C.wires x).getD i false else false := by
  have hsplit : C.gates = C.gates.take j ++ (gateAt C j :: C.gates.drop (j + 1)) := by
    rw [gateAt, List.getD_eq_getElem _ _ hj, List.cons_getElem_drop_succ, List.take_append_drop]
  set V := padRun (C.gates.take j) x with hV
  have hVl : V.length = x.length + j := by
    rw [hV, padRun_length, List.length_take]; omega
  set e := (gateAt C j).op.eval ((gateAt C j).inputs.map fun i => V.getD i false)
  have hw : C.wires x = padRun (C.gates.drop (j + 1)) (V ++ [e]) := by
    rw [wires_eq]
    conv_lhs => rw [hsplit]
    rw [padRun_append]; rfl
  have hpre : ∀ i < x.length + j + 1, (C.wires x).getD i false = (V ++ [e]).getD i false := by
    intro i hi
    rw [hw, padRun_getD _ _ _ (by simp [hVl]; omega)]
  refine ⟨?_, ?_⟩
  · rw [hpre _ (by omega), ← hVl, getD_snoc_eq]
  · intro i
    split_ifs with hi
    · rw [hpre i (by omega), List.getD_append _ _ _ _ (by omega)]
    · exact List.getD_eq_default _ _ (by omega)
  where
    getD_snoc_eq {α : Type} (L : List α) (S d : α) : (L ++ [S]).getD L.length d = S := by simp

lemma wires_length (C : Circuit) (x : List Bool) :
    (C.wires x).length = x.length + C.gates.length := by
  rw [wires_eq, padRun_length]

lemma ofCirc_sv (n s : ℕ) (C : Circuit) (j r k : ℕ) (hj : k < n + C.gates.length)
    (hk : k < n + j) : (ofCirc input n s C).sv input n j k r = (C.wires (xr input n r)).getD k false := by
  unfold Model.sv
  by_cases h6 : k < n
  · rw [if_pos h6, wires_eq, padRun_getD _ _ _ (by rw [xr_length]; exact h6),
      xr_getD input n r k h6]
  · rw [if_neg h6, if_pos hk]
    simp only [ofCirc, Model.w, show k - n < C.gates.length by omega, if_true]
    congr 1
    omega


lemma valid_ofCirc (n s : ℕ) (g : ℕ → Bool) (R : ℕ → Prop) (C : Circuit)
    (hC : ∀ gate ∈ C.gates, basisGate gate)
    (hsz : C.gates.length ≤ s) (hev : ∀ r, R r → C.eval (xr input n r) = g r) :
    Valid input n s g R (ofCirc input n s C) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro j _; exact (code_le n _ j).1
  · intro j _ h; exact code_not n _ j h
  · intro j _; exact (code_le n _ j).2.1
  · intro j _; exact (code_le n _ j).2.2
  · change (if C.output < n + C.gates.length then C.output else n + s) ≤ n + s
    split_ifs <;> omega
  · intro j hj r _
    by_cases hjl : j < C.gates.length
    · have hmem : gateAt C j ∈ C.gates := by
        rw [gateAt, List.getD_eq_getElem _ _ hjl]; exact List.getElem_mem hjl
      have hg := hC (gateAt C j) hmem
      obtain ⟨h1, h2⟩ := wire_gate C (xr input n r) j hjl
      rw [xr_length] at h1 h2
      have hS : ∀ i, (padRun (C.gates.take j) (xr input n r)).getD i false =
          (ofCirc input n s C).sv input n j (nm n j i) r := by
        intro i
        rw [h2 i]
        unfold nm
        split_ifs with hi
        · rw [ofCirc_sv input n s C j r i (by omega) hi]
        · simp [Model.sv]
      simp only [hS] at h1
      have hw : (ofCirc input n s C).w j r = if j < C.gates.length then
          (C.wires (xr input n r)).getD (n + j) false else true := rfl
      have hgop : (gateAt C j).op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) := by
        simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hg.1
      rw [hw, if_pos hjl, h1, code_eval n _ hgop hg.2 j
        (fun k => (ofCirc input n s C).sv input n j k r) (by simp [Model.sv])]
      rfl
    · have hga : gateAt C j = ⟨.and, []⟩ := by
        rw [gateAt, List.getD_eq_default _ _ (by omega)]
      simp [ofCirc, Model.w, Model.op, Model.s1, Model.s2, hjl, hga, code, gfun]
  · intro r hr
    rw [← hev r hr, Circuit.eval]
    have hso : (ofCirc input n s C).so =
        if C.output < n + C.gates.length then C.output else n + s := rfl
    rw [hso]
    split_ifs with ho
    · by_cases h6 : C.output < n
      · simp only [Model.sv, if_pos h6]
        rw [wires_eq, padRun_getD _ _ _ (by rw [xr_length]; exact h6), xr_getD input n r _ h6]
      · rw [ofCirc_sv input n s C s r _ ho (by omega)]
    · rw [List.getD_eq_default _ _ (by rw [wires_length, xr_length]; omega)]
      simp [Model.sv]

lemma code_op_not_iff (n : ℕ) (g : Gate) (j : ℕ) : (code n g j).1 = 3 ↔ g.op = GateOp.not := by
  rcases g with ⟨op, ins⟩
  cases op <;> rcases ins with _ | ⟨a, _ | ⟨b, l⟩⟩ <;> simp [code]

lemma ofCirc_op_not_iff (n s : ℕ) (C : Circuit) (j : ℕ) :
    (ofCirc input n s C).op j = 3 ↔
      ∃ hj : j < C.gates.length, (C.gates[j]).op = GateOp.not := by
  change (code n (gateAt C j) j).1 = 3 ↔ _
  rw [code_op_not_iff]
  by_cases hj : j < C.gates.length
  · rw [gateAt, List.getD_eq_getElem _ _ hj]
    constructor
    · intro h; exact ⟨hj, h⟩
    · rintro ⟨_, h⟩; exact h
  · rw [gateAt, List.getD_eq_default _ _ (by omega)]
    simp [hj]

lemma circuit_encOne_sat (n s : ℕ) (g : ℕ → Bool) (rows : List ℕ)
    (hrows : ∀ r ∈ rows, r < 128) (C : Circuit)
    (hC : ∀ gate ∈ C.gates, basisGate gate) (hsz : C.gates.length ≤ s)
    (hev : ∀ r ∈ rows, C.eval (xr input n r) = g r)
    (hu : ∀ i j : Fin C.gates.length,
      (C.gates.get i).op = GateOp.not → (C.gates.get j).op = GateOp.not → i = j)
    (hn : ∃ i : Fin C.gates.length, (C.gates.get i).op = GateOp.not) :
    FormulaSat (encOne input n s g rows) := by
  have hv := valid_ofCirc input n s g (· ∈ rows) C hC hsz hev
  apply encOne_sat input hrows hv
  · intro i hi j hj hni hnj
    obtain ⟨hil, hiop⟩ := (ofCirc_op_not_iff input n s C i).mp hni
    obtain ⟨hjl, hjop⟩ := (ofCirc_op_not_iff input n s C j).mp hnj
    have he := hu ⟨i, hil⟩ ⟨j, hjl⟩ hiop hjop
    exact congrArg Fin.val he
  · obtain ⟨i, hi⟩ := hn
    refine ⟨i.val, lt_of_lt_of_le i.isLt hsz, ?_⟩
    exact (ofCirc_op_not_iff input n s C i.val).mpr ⟨i.isLt, hi⟩

def raw7Input (k r : ℕ) : Bool := r.testBit k

def rowFun7 (f : (Fin 7 → Bool) → Bool) (r : ℕ) : Bool := f fun i => r.testBit i

lemma raw7_link (s : ℕ) (f : (Fin 7 → Bool) → Bool) (rows : List ℕ)
    (hrows : ∀ r ∈ rows, r < 128) (gs : List Gate) (o : ℕ)
    (hgs : ∀ gate ∈ gs, basisGate gate) (hsz : gs.length ≤ s)
    (hu : ∀ i j : Fin gs.length,
      (gs.get i).op = GateOp.not → (gs.get j).op = GateOp.not → i = j)
    (hn : ∃ i : Fin gs.length, (gs.get i).op = GateOp.not)
    (hev : ∀ x : Fin 7 → Bool, Circuit.eval ⟨gs, o⟩ (List.ofFn x) = f x) :
    FormulaSat (encOne raw7Input 7 s (rowFun7 f) rows) := by
  apply circuit_encOne_sat raw7Input 7 s (rowFun7 f) rows hrows ⟨gs, o⟩ hgs hsz
  · intro r _
    exact hev (fun i => r.testBit i)
  · exact hu
  · exact hn

end CNF

end PEqualNP.Outside.L_meta_10760
