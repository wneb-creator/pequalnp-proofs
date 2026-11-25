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


namespace NFCount

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

lemma wires_eq (C : Circuit) (x : List Bool) : C.wires x = wiresFrom C.gates x := rfl

lemma wiresFrom_append (gs gs' : List Gate) (w : List Bool) :
    wiresFrom (gs ++ gs') w = wiresFrom gs' (wiresFrom gs w) := by
  simp [wiresFrom, List.foldl_append]

lemma wiresFrom_prefix (gs : List Gate) : ∀ w : List Bool,
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

lemma length_wiresFrom (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := wiresFrom_prefix gs w
  rw [ht]; simp [hl]

lemma getD_wiresFrom (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := wiresFrom_prefix gs w
  rw [ht, List.getD_append _ _ _ _ h]

def litVal (a : Nat → Bool) (l : Nat) : Bool := a (l / 2) == (l % 2 == 0)

def ClauseSat (a : Nat → Bool) (c : List Nat) : Prop := ∃ l ∈ c, litVal a l = true

def FormulaSat (F : List (List Nat)) : Prop := ∃ a : Nat → Bool, ∀ c ∈ F, ClauseSat a c

def Model : Type := (ℕ → ℕ) × (ℕ → ℕ) × (ℕ → ℕ) × ℕ × (ℕ → ℕ → Bool)

def Model.mk (op s1 s2 : ℕ → ℕ) (so : ℕ) (w : ℕ → ℕ → Bool) : Model :=
  (op, s1, s2, so, w)

def Model.op (M : Model) : ℕ → ℕ := M.1
def Model.s1 (M : Model) : ℕ → ℕ := M.2.1
def Model.s2 (M : Model) : ℕ → ℕ := M.2.2.1
def Model.so (M : Model) : ℕ := M.2.2.2.1
def Model.w (M : Model) : ℕ → ℕ → Bool := M.2.2.2.2

@[local simp] lemma Model.op_mk (op s1 s2 : ℕ → ℕ) (so : ℕ) (w : ℕ → ℕ → Bool) :
    (Model.mk op s1 s2 so w).op = op := rfl

@[local simp] lemma Model.s1_mk (op s1 s2 : ℕ → ℕ) (so : ℕ) (w : ℕ → ℕ → Bool) :
    (Model.mk op s1 s2 so w).s1 = s1 := rfl

@[local simp] lemma Model.s2_mk (op s1 s2 : ℕ → ℕ) (so : ℕ) (w : ℕ → ℕ → Bool) :
    (Model.mk op s1 s2 so w).s2 = s2 := rfl

@[local simp] lemma Model.so_mk (op s1 s2 : ℕ → ℕ) (so : ℕ) (w : ℕ → ℕ → Bool) :
    (Model.mk op s1 s2 so w).so = so := rfl

@[local simp] lemma Model.w_mk (op s1 s2 : ℕ → ℕ) (so : ℕ) (w : ℕ → ℕ → Bool) :
    (Model.mk op s1 s2 so w).w = w := rfl

def Model.sv (n : ℕ) (M : Model) (j k r : ℕ) : Bool :=
  if k < n then r.testBit k else if k < n + j then M.w (k - n) r else false

def gfun (t : ℕ) (a b : Bool) : Bool :=
  if t = 0 then a && b else if t = 1 then a || b else if t = 3 then !a else true

def Valid (n s : ℕ) (g : ℕ → Bool) (R : ℕ → Prop) (M : Model) : Prop :=
  (∀ j < s, M.op j < 4) ∧
  (∀ j < s, M.op j = 3 → M.s1 j = M.s2 j) ∧
  (∀ j < s, M.s1 j ≤ n + j) ∧
  (∀ j < s, M.s2 j ≤ n + j) ∧
  (M.so ≤ n + s) ∧
  (∀ j < s, ∀ r, R r →
    M.w j r = gfun (M.op j) (M.sv n j (M.s1 j) r) (M.sv n j (M.s2 j) r)) ∧
  (∀ r, R r → M.sv n s M.so r = g r)

lemma Valid.op_lt {n s : ℕ} {g : ℕ → Bool} {R : ℕ → Prop} {M : Model} (h : Valid n s g R M) :
    ∀ j < s, M.op j < 4 := h.1

lemma Valid.not_eq {n s : ℕ} {g : ℕ → Bool} {R : ℕ → Prop} {M : Model} (h : Valid n s g R M) :
    ∀ j < s, M.op j = 3 → M.s1 j = M.s2 j := h.2.1

lemma Valid.s1_le {n s : ℕ} {g : ℕ → Bool} {R : ℕ → Prop} {M : Model} (h : Valid n s g R M) :
    ∀ j < s, M.s1 j ≤ n + j := h.2.2.1

lemma Valid.s2_le {n s : ℕ} {g : ℕ → Bool} {R : ℕ → Prop} {M : Model} (h : Valid n s g R M) :
    ∀ j < s, M.s2 j ≤ n + j := h.2.2.2.1

lemma Valid.so_le {n s : ℕ} {g : ℕ → Bool} {R : ℕ → Prop} {M : Model} (h : Valid n s g R M) :
    M.so ≤ n + s := h.2.2.2.2.1

lemma Valid.w_eq {n s : ℕ} {g : ℕ → Bool} {R : ℕ → Prop} {M : Model} (h : Valid n s g R M) :
    ∀ j < s, ∀ r, R r →
    M.w j r = gfun (M.op j) (M.sv n j (M.s1 j) r) (M.sv n j (M.s2 j) r) := h.2.2.2.2.2.1

lemma Valid.out_eq {n s : ℕ} {g : ℕ → Bool} {R : ℕ → Prop} {M : Model} (h : Valid n s g R M) :
    ∀ r, R r → M.sv n s M.so r = g r := h.2.2.2.2.2.2

def Model.pad (n : ℕ) (M : Model) (j : ℕ) : Prop :=
  M.op j = 2 ∧ M.s1 j = n + j ∧ M.s2 j = n + j

def Model.decPad (n : ℕ) (M : Model) (j : ℕ) : Decidable (M.pad n j) := by
  unfold Model.pad; infer_instance

def NF (n s : ℕ) (M : Model) : Prop :=
  (∀ j, j + 1 < s → M.pad n (j + 1) → M.pad n j) ∧
  (∀ j < s, M.op j = 2 → M.pad n j) ∧
  (∀ j < s, ¬ M.pad n j → M.s1 j ≠ n + j ∧ M.s2 j ≠ n + j) ∧
  (∀ j < s, ∀ i < j, M.pad n i → M.s1 j ≠ n + i ∧ M.s2 j ≠ n + i) ∧
  (∀ j < s, ¬ M.pad n j → M.s1 j < M.s2 j ∨ (M.op j = 3 ∧ M.s1 j = M.s2 j)) ∧
  (∀ j < s, ∀ i < j, M.op j = 3 → M.op i = 3 → M.s1 j ≠ n + i) ∧
  (∀ j, j + 1 < s → ¬ M.pad n j → ∃ i, j < i ∧ i < s ∧ (M.s1 i = n + j ∨ M.s2 i = n + j)) ∧
  (0 < s → M.so = n + s - 1 ∨ M.pad n (s - 1))

lemma NF.pre {n s : ℕ} {M : Model} (h : NF n s M) :
    ∀ j, j + 1 < s → M.pad n (j + 1) → M.pad n j := h.1

lemma NF.padOp {n s : ℕ} {M : Model} (h : NF n s M) :
    ∀ j < s, M.op j = 2 → M.pad n j := h.2.1

lemma NF.noF {n s : ℕ} {M : Model} (h : NF n s M) :
    ∀ j < s, ¬ M.pad n j → M.s1 j ≠ n + j ∧ M.s2 j ≠ n + j := h.2.2.1

lemma NF.noPadRd {n s : ℕ} {M : Model} (h : NF n s M) :
    ∀ j < s, ∀ i < j, M.pad n i → M.s1 j ≠ n + i ∧ M.s2 j ≠ n + i := h.2.2.2.1

lemma NF.ord {n s : ℕ} {M : Model} (h : NF n s M) :
    ∀ j < s, ¬ M.pad n j → M.s1 j < M.s2 j ∨ (M.op j = 3 ∧ M.s1 j = M.s2 j) := h.2.2.2.2.1

lemma NF.notNot {n s : ℕ} {M : Model} (h : NF n s M) :
    ∀ j < s, ∀ i < j, M.op j = 3 → M.op i = 3 → M.s1 j ≠ n + i := h.2.2.2.2.2.1

lemma NF.used {n s : ℕ} {M : Model} (h : NF n s M) :
    ∀ j, j + 1 < s → ¬ M.pad n j → ∃ i, j < i ∧ i < s ∧ (M.s1 i = n + j ∨ M.s2 i = n + j) := h.2.2.2.2.2.2.1

lemma NF.out {n s : ℕ} {M : Model} (h : NF n s M) :
    0 < s → M.so = n + s - 1 ∨ M.pad n (s - 1) := h.2.2.2.2.2.2.2

section formula
variable (n s : ℕ)

def wd : ℕ := 2 ^ n + n + s + 2

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
  if k < n then [[Q (ix n s e j k), L (ix n s (e + 3) j r) (r.testBit k)]]
  else if k < n + j then
    [[Q (ix n s e j k), Q (ix n s (e + 3) j r), P (ix n s 3 (k - n) r)],
     [Q (ix n s e j k), P (ix n s (e + 3) j r), Q (ix n s 3 (k - n) r)]]
  else [[Q (ix n s e j k), Q (ix n s (e + 3) j r)]]

def fSrcEq (rows : List ℕ) : List (List ℕ) :=
  [1, 2].flatMap fun e => (List.range s).flatMap fun j => rows.flatMap fun r =>
    (List.range (n + j + 1)).flatMap fun k => srcEq n s e j k r

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
  if k < n then (if r.testBit k = g r then [] else [[Q (ix n s 6 0 k)]])
  else if k < n + s then [[Q (ix n s 6 0 k), L (ix n s 3 (k - n) r) (g r)]]
  else if g r = true then [[Q (ix n s 6 0 k)]] else []

def fOutEq (g : ℕ → Bool) (rows : List ℕ) : List (List ℕ) :=
  rows.flatMap fun r => (List.range (n + s + 1)).flatMap fun k => outEq n s g k r

def fOut : List (List ℕ) :=
  if s = 0 then [] else [[P (ix n s 6 0 (n + s - 1)), P (ix n s 7 (s - 1) 0)]]

def fPad : List (List ℕ) :=
  (List.range s).flatMap fun j =>
    [[Q (ix n s 7 j 0), P (ix n s 0 j 2)], [Q (ix n s 7 j 0), P (ix n s 1 j (n + j))],
     [Q (ix n s 7 j 0), P (ix n s 2 j (n + j))], [P (ix n s 7 j 0), Q (ix n s 0 j 2)],
     [P (ix n s 7 j 0), Q (ix n s 1 j (n + j))], [P (ix n s 7 j 0), Q (ix n s 2 j (n + j))]]

def fPre : List (List ℕ) :=
  (List.range (s - 1)).map fun j => [Q (ix n s 7 (j + 1) 0), P (ix n s 7 j 0)]

def fPadRd : List (List ℕ) :=
  (List.range s).flatMap fun j => (List.range j).flatMap fun i =>
    [[Q (ix n s 7 i 0), Q (ix n s 1 j (n + i))], [Q (ix n s 7 i 0), Q (ix n s 2 j (n + i))]]

def fNot : List (List ℕ) :=
  (List.range s).flatMap fun j => (List.range (n + j + 1)).map fun k =>
    [Q (ix n s 0 j 3), Q (ix n s 1 j k), P (ix n s 2 j k)]

def fNotNot : List (List ℕ) :=
  (List.range s).flatMap fun j => (List.range j).map fun i =>
    [Q (ix n s 0 j 3), Q (ix n s 0 i 3), Q (ix n s 1 j (n + i))]

def fOrd : List (List ℕ) :=
  (List.range s).flatMap fun j => (List.range (n + j + 1)).flatMap fun k =>
    (List.range (k + 1)).map fun l =>
      [Q (ix n s 1 j k), Q (ix n s 2 j l), P (ix n s 7 j 0)] ++
        if l = k then [P (ix n s 0 j 3)] else []

def fUsed : List (List ℕ) :=
  (List.range (s - 1)).map fun j =>
    ((List.range (s - 1 - j)).map fun t => P (ix n s 1 (j + 1 + t) (n + j))) ++
    ((List.range (s - 1 - j)).map fun t => P (ix n s 2 (j + 1 + t) (n + j))) ++
      [P (ix n s 7 j 0)]

def enc (g : ℕ → Bool) (rows : List ℕ) : List (List ℕ) :=
  fOp n s ++ fSrcAlo n s ++ fSrcEq n s rows ++ fGate n s rows ++ fOutAlo n s ++
    fOutEq n s g rows ++ fOut n s ++ fPad n s ++ fPre n s ++ fPadRd n s ++ fOrd n s ++
    fUsed n s ++ fNot n s ++ fNotNot n s

end formula

def rowFun (n : ℕ) (f : (Fin n → Bool) → Bool) (r : ℕ) : Bool := f fun i => r.testBit i

def meaning (n : ℕ) (M : Model) (kd j a : ℕ) : Bool :=
  if kd = 0 then M.op j == a else if kd = 1 then M.s1 j == a else if kd = 2 then M.s2 j == a
  else if kd = 3 then M.w j a else if kd = 4 then M.sv n j (M.s1 j) a
  else if kd = 5 then M.sv n j (M.s2 j) a else if kd = 6 then M.so == a
  else if kd = 7 then @decide (M.pad n j) (Model.decPad n M j) else false

def val (n s : ℕ) (M : Model) (x : ℕ) : Bool :=
  meaning n M ((x - 1) / wd n s / (s + 1)) ((x - 1) / wd n s % (s + 1)) ((x - 1) % wd n s)

lemma val_ix (n s : ℕ) (M : Model) {kd j a : ℕ} (hj : j ≤ s) (ha : a < wd n s) :
    val n s M (ix n s kd j a + 1) = meaning n M kd j a := by
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
  have := Nat.one_le_two_pow (n := n); unfold wd; omega
lemma wd_lt2 (h : a < 2 ^ n) : a < wd n s := by unfold wd; omega

lemma v_op (hj : j ≤ s) (ha : a < wd n s) : val n s M (ix n s 0 j a + 1) = (M.op j == a) := by
  rw [val_ix n s M hj ha]; simp [meaning]
lemma v_s1 (hj : j ≤ s) (ha : a < wd n s) : val n s M (ix n s 1 j a + 1) = (M.s1 j == a) := by
  rw [val_ix n s M hj ha]; simp [meaning]
lemma v_s2 (hj : j ≤ s) (ha : a < wd n s) : val n s M (ix n s 2 j a + 1) = (M.s2 j == a) := by
  rw [val_ix n s M hj ha]; simp [meaning]
lemma v_w (hj : j ≤ s) (ha : a < wd n s) : val n s M (ix n s 3 j a + 1) = M.w j a := by
  rw [val_ix n s M hj ha]; simp [meaning]
lemma v_u1 (hj : j ≤ s) (ha : a < wd n s) :
    val n s M (ix n s 4 j a + 1) = M.sv n j (M.s1 j) a := by
  rw [val_ix n s M hj ha]; simp [meaning]
lemma v_u2 (hj : j ≤ s) (ha : a < wd n s) :
    val n s M (ix n s 5 j a + 1) = M.sv n j (M.s2 j) a := by
  rw [val_ix n s M hj ha]; simp [meaning]
lemma v_so (ha : a < wd n s) : val n s M (ix n s 6 0 a + 1) = (M.so == a) := by
  rw [val_ix n s M (Nat.zero_le _) ha]; simp [meaning]
lemma v_pad (hj : j ≤ s) : val n s M (ix n s 7 j 0 + 1) = @decide (M.pad n j) (Model.decPad n M j) := by
  rw [val_ix n s M hj (wd_lt1 (by omega))]; simp [meaning]

end vlemmas

def Model.src (M : Model) (e j : ℕ) : ℕ := if e = 1 then M.s1 j else M.s2 j

lemma v_src {n s : ℕ} (M : Model) {e j a : ℕ} (he : e = 1 ∨ e = 2) (hj : j ≤ s)
    (ha : a < wd n s) : val n s M (ix n s e j a + 1) = (M.src e j == a) := by
  rcases he with rfl | rfl
  · exact v_s1 M hj ha
  · exact v_s2 M hj ha

lemma v_u {n s : ℕ} (M : Model) {e j a : ℕ} (he : e = 1 ∨ e = 2) (hj : j ≤ s)
    (ha : a < wd n s) : val n s M (ix n s (e + 3) j a + 1) = M.sv n j (M.src e j) a := by
  rcases he with rfl | rfl
  · exact v_u1 M hj ha
  · exact v_u2 M hj ha

section sound
variable {n s : ℕ} {g : ℕ → Bool} {rows : List ℕ} {M : Model}
  (hrows : ∀ r ∈ rows, r < 2 ^ n) (hv : Valid n s g (· ∈ rows) M) (hn : NF n s M)
include hv

lemma src_le {e j : ℕ} (he : e = 1 ∨ e = 2) (hj : j < s) : M.src e j ≤ n + j := by
  rcases he with rfl | rfl
  · simpa [Model.src] using hv.s1_le j hj
  · simpa [Model.src] using hv.s2_le j hj

lemma s_fOp : ∀ c ∈ fOp n s, ClauseSat (val n s M) c := by
  intro c hc
  simp only [fOp, List.mem_map, List.mem_range] at hc
  obtain ⟨j, hj, rfl⟩ := hc
  have := hv.op_lt j hj
  simp (disch := first | omega | (apply wd_lt1; omega) | (apply wd_lt2; assumption)) only [cs_cons, cs_nil, litVal_P, v_op, beq_iff_eq, or_false]
  omega

lemma s_fSrcAlo : ∀ c ∈ fSrcAlo n s, ClauseSat (val n s M) c := by
  intro c hc
  simp only [fSrcAlo, List.mem_flatMap, List.mem_map, List.mem_range, List.mem_cons,
    List.not_mem_nil, or_false] at hc
  obtain ⟨e, he, j, hj, rfl⟩ := hc
  have hle := src_le hv he hj
  apply cs_of_mem (List.mem_map.2 ⟨M.src e j, List.mem_range.2 (by omega), rfl⟩)
  rw [litVal_P, v_src M he (by omega) (wd_lt1 (by omega))]
  simp

include hrows in
lemma s_fSrcEq : ∀ c ∈ fSrcEq n s rows, ClauseSat (val n s M) c := by
  intro c hc
  simp only [fSrcEq, List.mem_flatMap, List.mem_range, List.mem_cons, List.not_mem_nil,
    or_false] at hc
  obtain ⟨e, he, j, hj, r, hr, k, hk, hc⟩ := hc
  have hr' := hrows r hr
  unfold srcEq at hc
  split_ifs at hc with h1 h2
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    subst hc
    simp (disch := first | omega | (apply wd_lt1; omega) | (apply wd_lt2; assumption)) only [cs_cons, cs_nil, litVal_Q, litVal_L, v_src M he, v_u M he,
      or_false]
    by_cases hs : M.src e j = k
    · right; rw [hs]; simp [Model.sv, h1]
    · left; simp [hs]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl <;>
    · simp (disch := first | omega | (apply wd_lt1; omega) | (apply wd_lt2; assumption)) only [cs_cons, cs_nil, litVal_Q, litVal_P, v_src M he, v_u M he, v_w,
        or_false]
      by_cases hs : M.src e j = k
      · rw [hs]
        have : M.sv n j k r = M.w (k - n) r := by simp [Model.sv, h1, h2]
        rw [this]
        cases M.w (k - n) r <;> simp
      · simp [hs]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    subst hc
    simp (disch := first | omega | (apply wd_lt1; omega) | (apply wd_lt2; assumption)) only [cs_cons, cs_nil, litVal_Q, v_src M he, v_u M he, or_false]
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
lemma s_fGate : ∀ c ∈ fGate n s rows, ClauseSat (val n s M) c := by
  intro c hc
  simp only [fGate, List.mem_flatMap, List.mem_range] at hc
  obtain ⟨j, hj, r, hr, hc⟩ := hc
  have hr' := hrows r hr
  have G := gate_fact _ (hv.op_lt j hj) _ _ _ (hv.w_eq j hj r hr)
  simp only [gateCl, List.mem_cons, List.not_mem_nil, or_false] at hc
  obtain ⟨G1, G2, G3, G4, G5, G6, G7, G8, G9⟩ := G
  simp only [Bool.or_eq_true, or_assoc] at G1 G2 G3 G4 G5 G6 G7 G8 G9
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp (disch := first | omega | (apply wd_lt1; omega) | (apply wd_lt2; assumption)) only [cs_cons, cs_nil, litVal_Q, litVal_P, v_op, v_w, v_u1, v_u2,
      or_false, or_assoc] <;> assumption

lemma s_fOutAlo : ∀ c ∈ fOutAlo n s, ClauseSat (val n s M) c := by
  intro c hc
  simp only [fOutAlo, List.mem_cons, List.not_mem_nil, or_false] at hc
  subst hc
  have := hv.so_le
  apply cs_of_mem (List.mem_map.2 ⟨M.so, List.mem_range.2 (by omega), rfl⟩)
  rw [litVal_P, v_so M (wd_lt1 (by omega))]
  simp

include hrows in
lemma s_fOutEq : ∀ c ∈ fOutEq n s g rows, ClauseSat (val n s M) c := by
  intro c hc
  simp only [fOutEq, List.mem_flatMap, List.mem_range] at hc
  obtain ⟨r, hr, k, hk, hc⟩ := hc
  have hr' := hrows r hr
  have ho := hv.out_eq r hr
  unfold outEq at hc
  by_cases h1 : k < n
  · rw [if_pos h1] at hc
    by_cases h2 : r.testBit k = g r
    · rw [if_pos h2] at hc; simp at hc
    · rw [if_neg h2] at hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      subst hc
      simp (disch := first | omega | (apply wd_lt1; omega) | (apply wd_lt2; assumption)) only [cs_cons, cs_nil, litVal_Q, v_so, or_false]
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
      simp (disch := first | omega | (apply wd_lt1; omega) | (apply wd_lt2; assumption)) only [cs_cons, cs_nil, litVal_Q, litVal_L, v_so, v_w, or_false]
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
        simp (disch := first | omega | (apply wd_lt1; omega) | (apply wd_lt2; assumption)) only [cs_cons, cs_nil, litVal_Q, v_so, or_false]
        by_cases e : M.so = k
        · rw [e] at ho
          simp only [Model.sv, if_neg h1, if_neg h3] at ho
          rw [h4] at ho
          exact absurd ho Bool.false_ne_true
        · simp [e]
      · rw [if_neg h4] at hc; simp at hc

include hn

lemma s_fOut : ∀ c ∈ fOut n s, ClauseSat (val n s M) c := by
  intro c hc
  unfold fOut at hc
  split_ifs at hc with hs
  · simp at hc
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    subst hc
    simp (disch := first | omega | (apply wd_lt1; omega) | (apply wd_lt2; assumption)) only [cs_cons, cs_nil, litVal_P, v_so, v_pad, or_false, beq_iff_eq,
      decide_eq_true_eq]
    exact hn.out (by omega)

lemma s_fPad : ∀ c ∈ fPad n s, ClauseSat (val n s M) c := by
  intro c hc
  simp only [fPad, List.mem_flatMap, List.mem_range, List.mem_cons, List.not_mem_nil,
    or_false] at hc
  obtain ⟨j, hj, hc⟩ := hc
  have h1 := hn.padOp j hj
  have h2 := hn.noF j hj
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;>
  · simp (disch := first | omega | (apply wd_lt1; omega) | (apply wd_lt2; assumption)) only [cs_cons, cs_nil, litVal_Q, litVal_P, v_op, v_s1, v_s2, v_pad,
      or_false, beq_iff_eq, decide_eq_true_eq, Bool.not_eq_true', decide_eq_false_iff_not,
      beq_eq_false_iff_ne, ne_eq]
    unfold Model.pad at *
    tauto

lemma s_fPre : ∀ c ∈ fPre n s, ClauseSat (val n s M) c := by
  intro c hc
  simp only [fPre, List.mem_map, List.mem_range] at hc
  obtain ⟨j, hj, rfl⟩ := hc
  simp (disch := first | omega | (apply wd_lt1; omega) | (apply wd_lt2; assumption)) only [cs_cons, cs_nil, litVal_Q, litVal_P, v_pad, or_false,
    decide_eq_true_eq, Bool.not_eq_true', decide_eq_false_iff_not]
  by_cases h : M.pad n (j + 1)
  · exact Or.inr (hn.pre j (by omega) h)
  · exact Or.inl h

lemma s_fPadRd : ∀ c ∈ fPadRd n s, ClauseSat (val n s M) c := by
  intro c hc
  simp only [fPadRd, List.mem_flatMap, List.mem_range, List.mem_cons, List.not_mem_nil,
    or_false] at hc
  obtain ⟨j, hj, i, hi, hc⟩ := hc
  have h1 := hn.noPadRd j hj i hi
  rcases hc with rfl | rfl <;>
  · simp (disch := first | omega | (apply wd_lt1; omega) | (apply wd_lt2; assumption)) only [cs_cons, cs_nil, litVal_Q, v_s1, v_s2, v_pad, or_false,
      Bool.not_eq_true', decide_eq_false_iff_not, beq_eq_false_iff_ne, ne_eq]
    tauto

lemma s_fOrd : ∀ c ∈ fOrd n s, ClauseSat (val n s M) c := by
  intro c hc
  simp only [fOrd, List.mem_flatMap, List.mem_map, List.mem_range] at hc
  obtain ⟨j, hj, k, hk, l, hl, rfl⟩ := hc
  by_cases hlk : l = k
  · rw [if_pos hlk]
    simp (disch := first | omega | (apply wd_lt1; omega) | (apply wd_lt2; assumption)) only [List.cons_append, List.nil_append, cs_cons, cs_nil, litVal_Q,
      litVal_P, v_s1, v_s2, v_op, v_pad, or_false, Bool.not_eq_true', beq_eq_false_iff_ne, ne_eq,
      decide_eq_true_eq, beq_iff_eq]
    by_cases hp : M.pad n j
    · exact Or.inr (Or.inr (Or.inl hp))
    · have := hn.ord j hj hp
      omega
  · rw [if_neg hlk]
    simp (disch := first | omega | (apply wd_lt1; omega) | (apply wd_lt2; assumption)) only [List.append_nil, cs_cons, cs_nil, litVal_Q, litVal_P, v_s1, v_s2,
      v_pad, or_false, Bool.not_eq_true', beq_eq_false_iff_ne, ne_eq, decide_eq_true_eq]
    by_cases hp : M.pad n j
    · exact Or.inr (Or.inr hp)
    · have := hn.ord j hj hp
      omega

lemma s_fNot : ∀ c ∈ fNot n s, ClauseSat (val n s M) c := by
  intro c hc
  simp only [fNot, List.mem_flatMap, List.mem_map, List.mem_range] at hc
  obtain ⟨j, hj, k, hk, rfl⟩ := hc
  have := hv.not_eq j hj
  simp (disch := first | omega | (apply wd_lt1; omega) | (apply wd_lt2; assumption)) only [cs_cons, cs_nil, litVal_Q, litVal_P, v_op, v_s1, v_s2, or_false,
    Bool.not_eq_true', beq_eq_false_iff_ne, ne_eq, beq_iff_eq]
  omega

lemma s_fNotNot : ∀ c ∈ fNotNot n s, ClauseSat (val n s M) c := by
  intro c hc
  simp only [fNotNot, List.mem_flatMap, List.mem_map, List.mem_range] at hc
  obtain ⟨j, hj, i, hi, rfl⟩ := hc
  have := hn.notNot j hj i hi
  simp (disch := first | omega | (apply wd_lt1; omega) | (apply wd_lt2; assumption)) only [cs_cons, cs_nil, litVal_Q, v_op, v_s1, or_false,
    Bool.not_eq_true', beq_eq_false_iff_ne, ne_eq]
  tauto

lemma s_fUsed : ∀ c ∈ fUsed n s, ClauseSat (val n s M) c := by
  intro c hc
  simp only [fUsed, List.mem_map, List.mem_range] at hc
  obtain ⟨j, hj, rfl⟩ := hc
  by_cases hp : M.pad n j
  · apply cs_of_mem (l := P (ix n s 7 j 0)) (by simp)
    rw [litVal_P, v_pad M (by omega)]
    simpa using hp
  · obtain ⟨i, hji, hi, h | h⟩ := hn.used j (by omega) hp
    · apply cs_of_mem (l := P (ix n s 1 (j + 1 + (i - j - 1)) (n + j)))
      · apply List.mem_append_left; apply List.mem_append_left
        exact List.mem_map.2 ⟨i - j - 1, List.mem_range.2 (by omega), rfl⟩
      · rw [litVal_P, v_s1 M (by omega) (wd_lt1 (by omega)),
          show j + 1 + (i - j - 1) = i by omega]
        simpa using h
    · apply cs_of_mem (l := P (ix n s 2 (j + 1 + (i - j - 1)) (n + j)))
      · apply List.mem_append_left; apply List.mem_append_right
        exact List.mem_map.2 ⟨i - j - 1, List.mem_range.2 (by omega), rfl⟩
      · rw [litVal_P, v_s2 M (by omega) (wd_lt1 (by omega)),
          show j + 1 + (i - j - 1) = i by omega]
        simpa using h

include hrows in

lemma enc_sat : ∀ c ∈ enc n s g rows, ClauseSat (val n s M) c := by
  intro c hc
  simp only [enc, List.append_assoc, List.mem_append] at hc
  rcases hc with h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · exact s_fOp hv c h
  · exact s_fSrcAlo hv c h
  · exact s_fSrcEq hrows hv c h
  · exact s_fGate hrows hv c h
  · exact s_fOutAlo hv c h
  · exact s_fOutEq hrows hv c h
  · exact s_fOut hv hn c h
  · exact s_fPad hv hn c h
  · exact s_fPre hv hn c h
  · exact s_fPadRd hv hn c h
  · exact s_fOrd hv hn c h
  · exact s_fUsed hv hn c h
  · exact s_fNot hv hn c h
  · exact s_fNotNot hv hn c h

end sound

section circuit
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def xr (n r : ℕ) : List Bool := List.ofFn fun i : Fin n => r.testBit i

def nm (n j a : ℕ) : ℕ := if a < n + j then a else n + j

def code (n : ℕ) (g : Gate) (j : ℕ) : ℕ × ℕ × ℕ :=
  match g.op, g.inputs with
  | .and, [] => (2, n + j, n + j)
  | .and, [a] => (0, nm n j a, nm n j a)
  | .and, a :: b :: _ => (0, nm n j a, nm n j b)
  | .or, [] => (1, n + j, n + j)
  | .or, [a] => (1, nm n j a, nm n j a)
  | .or, a :: b :: _ => (1, nm n j a, nm n j b)
  | .not, a :: _ => (3, nm n j a, nm n j a)
  | _, _ => (2, n + j, n + j)

def gateAt (C : Circuit) (j : ℕ) : Gate := C.gates.getD j ⟨.and, []⟩

def ofCirc (n s : ℕ) (C : Circuit) : Model :=
  Model.mk (fun j => (code n (gateAt C j) j).1)
    (fun j => (code n (gateAt C j) j).2.1)
    (fun j => (code n (gateAt C j) j).2.2)
    (if C.output < n + C.gates.length then C.output else n + s)
    (fun j r => if j < C.gates.length then (C.wires (xr n r)).getD (n + j) false else true)

lemma xr_length (n r : ℕ) : (xr n r).length = n := by simp [xr]

lemma xr_getD (n r a : ℕ) (ha : a < n) : (xr n r).getD a false = r.testBit a := by
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
        (wiresFrom (C.gates.take j) x).getD i false) ∧
    ∀ i, (wiresFrom (C.gates.take j) x).getD i false =
      if i < x.length + j then (C.wires x).getD i false else false := by
  have hsplit : C.gates = C.gates.take j ++ (gateAt C j :: C.gates.drop (j + 1)) := by
    rw [gateAt, List.getD_eq_getElem _ _ hj, List.cons_getElem_drop_succ, List.take_append_drop]
  set V := wiresFrom (C.gates.take j) x with hV
  have hVl : V.length = x.length + j := by
    rw [hV, length_wiresFrom, List.length_take]; omega
  set e := (gateAt C j).op.eval ((gateAt C j).inputs.map fun i => V.getD i false)
  have hw : C.wires x = wiresFrom (C.gates.drop (j + 1)) (V ++ [e]) := by
    rw [wires_eq]
    conv_lhs => rw [hsplit]
    rw [wiresFrom_append]; rfl
  have hpre : ∀ i < x.length + j + 1, (C.wires x).getD i false = (V ++ [e]).getD i false := by
    intro i hi
    rw [hw, getD_wiresFrom _ _ _ (by simp [hVl]; omega)]
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
  rw [wires_eq, length_wiresFrom]

lemma ofCirc_sv (n s : ℕ) (C : Circuit) (j r k : ℕ) (hj : k < n + C.gates.length)
    (hk : k < n + j) : (ofCirc n s C).sv n j k r = (C.wires (xr n r)).getD k false := by
  unfold Model.sv
  by_cases h6 : k < n
  · rw [if_pos h6, wires_eq, getD_wiresFrom _ _ _ (by rw [xr_length]; exact h6),
      xr_getD n r k h6]
  · rw [if_neg h6, if_pos hk]
    simp only [ofCirc, Model.op_mk, Model.s1_mk, Model.s2_mk, Model.so_mk, Model.w_mk, show k - n < C.gates.length by omega, if_true]
    congr 1
    omega

lemma valid_ofCirc (n s : ℕ) (g : ℕ → Bool) (R : ℕ → Prop) (C : Circuit) (hC : FanInTwo C)
    (hsz : C.gates.length ≤ s) (hev : ∀ r, R r → C.eval (xr n r) = g r) :
    Valid n s g R (ofCirc n s C) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro j _
    exact (code_le n _ j).1
  · intro j _ h
    exact code_not n _ j h
  · intro j _
    exact (code_le n _ j).2.1
  · intro j _
    exact (code_le n _ j).2.2
  · exact by simp only [ofCirc, Model.op_mk, Model.s1_mk, Model.s2_mk, Model.so_mk, Model.w_mk]; split_ifs <;> omega
  · intro j hj r _
    by_cases hjl : j < C.gates.length
    · have hmem : gateAt C j ∈ C.gates := by
        rw [gateAt, List.getD_eq_getElem _ _ hjl]; exact List.getElem_mem hjl
      have hg := hC (gateAt C j) hmem
      obtain ⟨h1, h2⟩ := wire_gate C (xr n r) j hjl
      rw [xr_length] at h1 h2
      have hS : ∀ i, (wiresFrom (C.gates.take j) (xr n r)).getD i false =
          (ofCirc n s C).sv n j (nm n j i) r := by
        intro i
        rw [h2 i]
        unfold nm
        split_ifs with hi
        · rw [ofCirc_sv n s C j r i (by omega) hi]
        · simp [Model.sv]
      simp only [hS] at h1
      have hw : (ofCirc n s C).w j r = if j < C.gates.length then
          (C.wires (xr n r)).getD (n + j) false else true := rfl
      rw [hw, if_pos hjl, h1, code_eval n _ hg.1 hg.2 j (fun k => (ofCirc n s C).sv n j k r)
        (by simp [Model.sv])]
      rfl
    · have hga : gateAt C j = ⟨.and, []⟩ := by
        rw [gateAt, List.getD_eq_default _ _ (by omega)]
      simp [ofCirc, Model.op_mk, Model.s1_mk, Model.s2_mk, Model.so_mk, Model.w_mk, hjl, hga, code, gfun]
  · intro r hr
    rw [← hev r hr, Circuit.eval]
    have hso : (ofCirc n s C).so =
        if C.output < n + C.gates.length then C.output else n + s := rfl
    rw [hso]
    split_ifs with ho
    · by_cases h6 : C.output < n
      · simp only [Model.sv, if_pos h6]
        rw [wires_eq, getD_wiresFrom _ _ _ (by rw [xr_length]; exact h6), xr_getD n r _ h6]
      · rw [ofCirc_sv n s C s r _ ho (by omega)]
    · rw [List.getD_eq_default _ _ (by rw [wires_length, xr_length]; omega)]
      simp [Model.sv]

end circuit

def phi (n d k : ℕ) : ℕ := if k < n then k else if k < n + d then k + 1 else k

def rd (n d t j k : ℕ) : ℕ :=
  if k = n + d then (if t = 0 then n + j else if t = 1 then n else phi n d (t - 2)) else phi n d k

def tval (n : ℕ) (M : Model) (d t r : ℕ) : Bool :=
  if t = 0 then false else if t = 1 then true else M.sv n d (t - 2) r

def mv (n s : ℕ) (M : Model) (d t : ℕ) : Model :=
  Model.mk (fun j => if j = 0 then 2 else if j ≤ d then M.op (j - 1) else M.op j)
    (fun j => if j = 0 then n else if j ≤ d then phi n d (M.s1 (j - 1)) else rd n d t j (M.s1 j))
    (fun j => if j = 0 then n else if j ≤ d then phi n d (M.s2 (j - 1)) else rd n d t j (M.s2 j))
    (rd n d t s M.so)
    (fun j r => if j = 0 then true else if j ≤ d then M.w (j - 1) r else M.w j r)

def Model.Read (n s : ℕ) (M : Model) (d : ℕ) : Prop :=
  (∃ j, d < j ∧ j < s ∧ (M.s1 j = n + d ∨ M.s2 j = n + d)) ∨ M.so = n + d

def TgtOk (n d t : ℕ) : Prop := t = 0 ∨ t = 1 ∨ (2 ≤ t ∧ t - 2 < n + d)

section move
variable {n s : ℕ} {g : ℕ → Bool} {R : ℕ → Prop} {M : Model} {d t : ℕ}

lemma sv_shift (hd : d < s) {i k r : ℕ} (hi : i < d) (hk : k ≤ n + i) :
    (mv n s M d t).sv n (i + 1) (phi n d k) r = M.sv n i k r := by
  unfold Model.sv phi
  by_cases h6 : k < n
  · simp [h6]
  · by_cases h7 : k < n + i
    · simp only [if_neg h6, if_pos (show k < n + d by omega), if_neg (show ¬ k + 1 < n by omega),
        if_pos (show k + 1 < n + (i + 1) by omega), if_pos h7, mv, Model.op_mk, Model.s1_mk, Model.s2_mk, Model.so_mk, Model.w_mk,
        if_neg (show ¬ k + 1 - n = 0 by omega), if_pos (show k + 1 - n ≤ d by omega)]
      congr 1 <;> omega
    · simp only [if_neg h6, if_pos (show k < n + d by omega), if_neg (show ¬ k + 1 < n by omega),
        if_neg (show ¬ k + 1 < n + (i + 1) by omega), if_neg h7]

lemma sv_later {j k r : ℕ} (hj : d < j) (hkd : k ≠ n + d) :
    (mv n s M d t).sv n j (phi n d k) r = M.sv n j k r := by
  unfold Model.sv phi
  by_cases h6 : k < n
  · simp [h6]
  · by_cases h7 : k < n + d
    · simp only [if_neg h6, if_pos h7, if_neg (show ¬ k + 1 < n by omega),
        if_pos (show k + 1 < n + j by omega), if_pos (show k < n + j by omega), mv, Model.op_mk, Model.s1_mk, Model.s2_mk, Model.so_mk, Model.w_mk,
        if_neg (show ¬ k + 1 - n = 0 by omega), if_pos (show k + 1 - n ≤ d by omega)]
      congr 1 <;> omega
    · simp only [if_neg h6, if_neg h7]
      by_cases h8 : k < n + j
      · simp only [if_pos h8, mv, Model.op_mk, Model.s1_mk, Model.s2_mk, Model.so_mk, Model.w_mk, if_neg (show ¬ k - n = 0 by omega),
          if_neg (show ¬ k - n ≤ d by omega)]
      · simp only [if_neg h8]

lemma sv_rd (ht : TgtOk n d t) {j k r : ℕ} (hj : d < j)
    (htr : k = n + d → M.w d r = tval n M d t r) :
    (mv n s M d t).sv n j (rd n d t j k) r = M.sv n j k r := by
  unfold rd
  by_cases hkd : k = n + d
  · rw [if_pos hkd]
    have hw := htr hkd
    have hold : M.sv n j k r = M.w d r := by
      unfold Model.sv
      simp only [if_neg (show ¬ k < n by omega), if_pos (show k < n + j by omega)]
      congr 1; omega
    rw [hold, hw]
    unfold tval
    rcases ht with rfl | rfl | ⟨h2, hc⟩
    · simp [Model.sv]
    · simp [Model.sv, mv, Model.op_mk, Model.s1_mk, Model.s2_mk, Model.so_mk, Model.w_mk, show 0 < j by omega]
    · simp only [if_neg (show ¬ t = 0 by omega), if_neg (show ¬ t = 1 by omega)]
      rw [sv_later hj (by omega)]
      unfold Model.sv
      by_cases h6 : t - 2 < n
      · simp [h6]
      · simp only [if_neg h6, if_pos (show t - 2 < n + j by omega), if_pos hc]
  · rw [if_neg hkd]
    exact sv_later hj hkd

lemma valid_mv (hv : Valid n s g R M) (hd : d < s) (ht : TgtOk n d t)
    (htr : M.Read n s d → ∀ r, R r → M.w d r = tval n M d t r) :
    Valid n s g R (mv n s M d t) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro j hj
    simp only [mv, Model.op_mk, Model.s1_mk, Model.s2_mk, Model.so_mk, Model.w_mk]; split_ifs
    · omega
    · exact hv.op_lt _ (by omega)
    · exact hv.op_lt _ hj
  · intro j hj h3
    simp only [mv, Model.op_mk, Model.s1_mk, Model.s2_mk, Model.so_mk, Model.w_mk] at h3 ⊢
    by_cases h0 : j = 0
    · rw [if_pos h0] at h3; omega
    · by_cases h1 : j ≤ d
      · simp only [if_neg h0, if_pos h1] at h3 ⊢
        rw [hv.not_eq (j - 1) (by omega) h3]
      · simp only [if_neg h0, if_neg h1] at h3 ⊢
        rw [hv.not_eq j hj h3]
  · intro j hj
    simp only [mv, Model.op_mk, Model.s1_mk, Model.s2_mk, Model.so_mk, Model.w_mk]; split_ifs with h0 h1
    · omega
    · have := hv.s1_le (j - 1) (by omega); unfold phi; split_ifs <;> omega
    · have := hv.s1_le j hj
      unfold rd phi; rcases ht with rfl | rfl | ⟨_, _⟩ <;> split_ifs <;> omega
  · intro j hj
    simp only [mv, Model.op_mk, Model.s1_mk, Model.s2_mk, Model.so_mk, Model.w_mk]; split_ifs with h0 h1
    · omega
    · have := hv.s2_le (j - 1) (by omega); unfold phi; split_ifs <;> omega
    · have := hv.s2_le j hj
      unfold rd phi; rcases ht with rfl | rfl | ⟨_, _⟩ <;> split_ifs <;> omega
  ·
    have := hv.so_le
    simp only [mv, Model.op_mk, Model.s1_mk, Model.s2_mk, Model.so_mk, Model.w_mk]; unfold rd phi; rcases ht with rfl | rfl | ⟨_, _⟩ <;> split_ifs <;> omega
  · intro j hj r hr
    by_cases h0 : j = 0
    · subst h0; simp [mv, Model.op_mk, Model.s1_mk, Model.s2_mk, Model.so_mk, Model.w_mk, gfun]
    · by_cases h1 : j ≤ d
      · obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
        have e1 := sv_shift (M := M) (t := t) hd (i := i) (r := r) (by omega)
          (hv.s1_le i (by omega))
        have e2 := sv_shift (M := M) (t := t) hd (i := i) (r := r) (by omega)
          (hv.s2_le i (by omega))
        simp only [mv, Model.op_mk, Model.s1_mk, Model.s2_mk, Model.so_mk, Model.w_mk, if_neg h0, if_pos h1, Nat.add_sub_cancel] at e1 e2 ⊢
        rw [e1, e2]
        exact hv.w_eq i (by omega) r hr
      · have e1 := sv_rd (s := s) (M := M) ht (j := j) (k := M.s1 j) (r := r) (by omega)
          (fun h => htr (Or.inl ⟨j, by omega, hj, Or.inl h⟩) r hr)
        have e2 := sv_rd (s := s) (M := M) ht (j := j) (k := M.s2 j) (r := r) (by omega)
          (fun h => htr (Or.inl ⟨j, by omega, hj, Or.inr h⟩) r hr)
        simp only [mv, Model.op_mk, Model.s1_mk, Model.s2_mk, Model.so_mk, Model.w_mk, if_neg h0, if_neg h1] at e1 e2 ⊢
        rw [e1, e2]
        exact hv.w_eq j hj r hr
  · intro r hr
    have e := sv_rd (s := s) (M := M) ht (j := s) (k := M.so) (r := r) hd
      (fun h => htr (Or.inr h) r hr)
    simp only [mv, Model.op_mk, Model.s1_mk, Model.s2_mk, Model.so_mk, Model.w_mk] at e ⊢
    rw [e]
    exact hv.out_eq r hr

lemma pad_mv0 : (mv n s M d t).pad n 0 := by simp [Model.pad, mv, Model.op_mk, Model.s1_mk, Model.s2_mk, Model.so_mk, Model.w_mk]

lemma pad_mv_shift (hv : Valid n s g R M) {i : ℕ} (hi : i < d) (hd : d < s) :
    (mv n s M d t).pad n (i + 1) ↔ M.pad n i := by
  have h1 := hv.s1_le i (by omega)
  have h2 := hv.s2_le i (by omega)
  simp only [Model.pad, mv, Model.op_mk, Model.s1_mk, Model.s2_mk, Model.so_mk, Model.w_mk, if_neg (show ¬ i + 1 = 0 by omega), if_pos (show i + 1 ≤ d by omega),
    Nat.add_sub_cancel]
  unfold phi
  constructor
  · rintro ⟨a, b, c⟩; refine ⟨a, ?_, ?_⟩ <;> split_ifs at b c <;> omega
  · rintro ⟨a, b, c⟩; refine ⟨a, ?_, ?_⟩ <;> split_ifs <;> omega

lemma pad_mv_later {j : ℕ} (hj : d < j) (h : M.pad n j) : (mv n s M d t).pad n j := by
  obtain ⟨a, b, c⟩ := h
  simp only [Model.pad, mv, Model.op_mk, Model.s1_mk, Model.s2_mk, Model.so_mk, Model.w_mk, if_neg (show ¬ j = 0 by omega), if_neg (show ¬ j ≤ d by omega)]
  refine ⟨a, ?_, ?_⟩ <;> unfold rd phi <;> split_ifs <;> omega

end move

def ind (n : ℕ) (M : Model) (j : ℕ) : ℕ := @ite ℕ (M.pad n j) (Model.decPad n M j) 0 1

lemma ind_congr {n : ℕ} {M M' : Model} {j j' : ℕ} (h : M.pad n j ↔ M'.pad n j') :
    ind n M j = ind n M' j' := by
  unfold ind
  by_cases h1 : M.pad n j
  · simp [h1, h.1 h1]
  · simp [h1, (not_congr h).1 h1]

def muf (s : ℕ) (a : ℕ → ℕ) : ℕ := ∑ j ∈ Finset.range s, (s - j) * a j

def ssum (s : ℕ) (M : Model) : ℕ := ∑ j ∈ Finset.range s, M.s1 j

def meas (n s : ℕ) (M : Model) : ℕ := (s * (n + s) + 1) * muf s (ind n M) + ssum s M

lemma muf_lt (s : ℕ) (a b : ℕ → ℕ) (d : ℕ) (hd : d < s) (hb0 : b 0 = 0)
    (hsh : ∀ i < d, b (i + 1) = a i) (hle : ∀ j, d < j → j < s → b j ≤ a j)
    (hpos : 0 < a d ∨ ∃ i < d, 0 < a i) : muf s b < muf s a := by
  have base : ∑ j ∈ Finset.range (d + 1), (s - j) * b j <
      ∑ j ∈ Finset.range (d + 1), (s - j) * a j := by
    rw [Finset.sum_range_succ', Finset.sum_range_succ, hb0, Nat.mul_zero, Nat.add_zero]
    have e1 : ∑ i ∈ Finset.range d, (s - (i + 1)) * b (i + 1) =
        ∑ i ∈ Finset.range d, (s - (i + 1)) * a i :=
      Finset.sum_congr rfl fun i hi => by rw [hsh i (Finset.mem_range.1 hi)]
    have e2 : ∑ i ∈ Finset.range d, (s - i) * a i =
        ∑ i ∈ Finset.range d, (s - (i + 1)) * a i + ∑ i ∈ Finset.range d, a i := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i hi => ?_
      have := Finset.mem_range.1 hi
      rw [show s - i = (s - (i + 1)) + 1 by omega, Nat.add_mul, Nat.one_mul]
    rw [e1, e2]
    have : 0 < ∑ i ∈ Finset.range d, a i + (s - d) * a d := by
      rcases hpos with h | ⟨i, hi, h⟩
      · have : 0 < (s - d) * a d := Nat.mul_pos (by omega) h
        omega
      · have := Finset.single_le_sum (f := a) (fun _ _ => Nat.zero_le _)
          (Finset.mem_range.2 hi)
        omega
    omega
  have step : ∀ m, d + 1 ≤ m → m ≤ s → ∑ j ∈ Finset.range m, (s - j) * b j <
      ∑ j ∈ Finset.range m, (s - j) * a j := by
    intro m hm hms
    induction m with
    | zero => omega
    | succ m ih =>
      by_cases h : m + 1 = d + 1
      · rw [h]; exact base
      · rw [Finset.sum_range_succ, Finset.sum_range_succ]
        have := ih (by omega) (by omega)
        have : (s - m) * b m ≤ (s - m) * a m :=
          Nat.mul_le_mul_left _ (hle m (by omega) (by omega))
        omega
  exact step s (by omega) le_rfl

lemma ssum_le {n s : ℕ} {g : ℕ → Bool} {R : ℕ → Prop} {M : Model} (hv : Valid n s g R M) :
    ssum s M ≤ s * (n + s) := by
  calc ssum s M ≤ ∑ j ∈ Finset.range s, (n + s) :=
        Finset.sum_le_sum fun j hj => by
          have := hv.s1_le j (Finset.mem_range.1 hj); have := Finset.mem_range.1 hj; omega
    _ = s * (n + s) := by simp

lemma meas_mv {n s : ℕ} {g : ℕ → Bool} {R : ℕ → Prop} {M : Model} {d t : ℕ}
    (hv : Valid n s g R M) (hv' : Valid n s g R (mv n s M d t)) (hd : d < s)
    (hpos : ¬ M.pad n d ∨ ∃ i < d, ¬ M.pad n i) : meas n s (mv n s M d t) < meas n s M := by
  have hlt : muf s (ind n (mv n s M d t)) < muf s (ind n M) := by
    apply muf_lt s (ind n M) (ind n (mv n s M d t)) d hd
    · simp [ind, pad_mv0]
    · intro i hi; exact ind_congr (pad_mv_shift hv hi hd)
    · intro j hj _
      unfold ind
      by_cases h1 : (mv n s M d t).pad n j
      · simp [h1]
      · have h2 : ¬ M.pad n j := fun h => h1 (pad_mv_later hj h)
        simp [h1, h2]
    · rcases hpos with h | ⟨i, hi, h⟩
      · left; simp [ind, h]
      · right; exact ⟨i, hi, by simp [ind, h]⟩
  have b1 := ssum_le hv'
  unfold meas
  have : (s * (n + s) + 1) * muf s (ind n (mv n s M d t)) + (s * (n + s) + 1) ≤
      (s * (n + s) + 1) * muf s (ind n M) := by
    rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hlt
  omega

def sw (M : Model) (j : ℕ) : Model :=
  Model.mk M.op (fun i => if i = j then M.s2 j else M.s1 i)
    (fun i => if i = j then M.s1 j else M.s2 i) M.so M.w

lemma valid_sw {n s : ℕ} {g : ℕ → Bool} {R : ℕ → Prop} {M : Model} (hv : Valid n s g R M)
    (j : ℕ) : Valid n s g R (sw M j) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact hv.op_lt
  · intro i hi h3
    have := hv.not_eq i hi h3
    simp only [sw, Model.op_mk, Model.s1_mk, Model.s2_mk, Model.so_mk, Model.w_mk]; split_ifs with h
    · subst h; exact this.symm
    · exact this
  · intro i hi
    simp only [sw, Model.op_mk, Model.s1_mk, Model.s2_mk, Model.so_mk, Model.w_mk]; split_ifs with h
    · subst h; exact hv.s2_le i hi
    · exact hv.s1_le i hi
  · intro i hi
    simp only [sw, Model.op_mk, Model.s1_mk, Model.s2_mk, Model.so_mk, Model.w_mk]; split_ifs with h
    · subst h; exact hv.s1_le i hi
    · exact hv.s2_le i hi
  · exact hv.so_le
  · intro i hi r hr
    have := hv.w_eq i hi r hr
    have hsv : ∀ k, (sw M j).sv n i k r = M.sv n i k r := fun k => rfl
    simp only [hsv]
    simp only [sw, Model.op_mk, Model.s1_mk, Model.s2_mk, Model.so_mk, Model.w_mk]
    split_ifs with h1
    · subst h1
      by_cases h3 : M.op i = 3
      · rw [this, hv.not_eq i hi h3]
      · rw [this]; unfold gfun
        simp only [if_neg h3]
        split_ifs <;> simp [Bool.and_comm, Bool.or_comm]
    · exact this
  · intro r hr
    exact hv.out_eq r hr

lemma pad_sw {n : ℕ} {M : Model} {j : ℕ} (i : ℕ) : (sw M j).pad n i ↔ M.pad n i := by
  simp only [Model.pad, sw, Model.op_mk, Model.s1_mk, Model.s2_mk, Model.so_mk, Model.w_mk]
  split_ifs with h
  · subst h; constructor <;> rintro ⟨a, b, c⟩ <;> exact ⟨a, c, b⟩
  · rfl

lemma meas_sw {n s : ℕ} {M : Model} {j : ℕ} (hj : j < s) (hlt : M.s2 j < M.s1 j) :
    meas n s (sw M j) < meas n s M := by
  have hind : ind n (sw M j) = ind n M := by funext i; exact ind_congr (pad_sw (n := n) (M := M) (j := j) i)
  unfold meas
  rw [hind]
  have : ssum s (sw M j) < ssum s M := by
    apply Finset.sum_lt_sum
    · intro i _
      simp only [sw, Model.op_mk, Model.s1_mk, Model.s2_mk, Model.so_mk, Model.w_mk]; split_ifs with h
      · subst h; omega
      · exact le_rfl
    · exact ⟨j, Finset.mem_range.2 hj, by simp [sw, Model.op_mk, Model.s1_mk, Model.s2_mk, Model.so_mk, Model.w_mk, hlt]⟩
  omega

section triv
variable {n s : ℕ} {g : ℕ → Bool} {R : ℕ → Prop} {M : Model} (hv : Valid n s g R M) {j : ℕ}
  (hj : j < s)
include hv hj

lemma copy_tgt {k : ℕ} (hk : k ≤ n + j) (hw : ∀ r, R r → M.w j r = M.sv n j k r) :
    ∃ t, TgtOk n j t ∧ ∀ r, R r → M.w j r = tval n M j t r := by
  by_cases hk' : k < n + j
  · refine ⟨k + 2, Or.inr (Or.inr ⟨by omega, by omega⟩), fun r hr => ?_⟩
    rw [hw r hr]; simp [tval]
  · refine ⟨0, Or.inl rfl, fun r hr => ?_⟩
    rw [hw r hr]; simp [tval, Model.sv, show ¬ k < n by omega, hk']

omit hv hj in
lemma const_tgt (c : Bool) (hw : ∀ r, R r → M.w j r = c) :
    ∃ t, TgtOk n j t ∧ ∀ r, R r → M.w j r = tval n M j t r := by
  cases c
  · exact ⟨0, Or.inl rfl, fun r hr => by rw [hw r hr]; simp [tval]⟩
  · exact ⟨1, Or.inr (Or.inl rfl), fun r hr => by rw [hw r hr]; simp [tval]⟩

lemma op2_triv (h2 : M.op j = 2) :
    ∃ t, TgtOk n j t ∧ ∀ r, R r → M.w j r = tval n M j t r :=
  const_tgt true fun r hr => by rw [hv.w_eq j hj r hr, h2]; simp [gfun]

lemma false_src
    (h : (∀ r, R r → M.sv n j (M.s1 j) r = false) ∨ (∀ r, R r → M.sv n j (M.s2 j) r = false)) :
    ∃ t, TgtOk n j t ∧ ∀ r, R r → M.w j r = tval n M j t r := by
  have hop := hv.op_lt j hj
  have hw := hv.w_eq j hj
  by_cases h0 : M.op j = 0
  · refine const_tgt false fun r hr => ?_
    rw [hw r hr, h0]
    rcases h with h | h <;> simp [gfun, h r hr]
  · by_cases h1 : M.op j = 1
    · rcases h with h | h
      · exact copy_tgt hv hj (hv.s2_le j hj) fun r hr => by rw [hw r hr, h1]; simp [gfun, h r hr]
      · exact copy_tgt hv hj (hv.s1_le j hj) fun r hr => by rw [hw r hr, h1]; simp [gfun, h r hr]
    · by_cases h3 : M.op j = 3
      · have he := hv.not_eq j hj h3
        refine const_tgt true fun r hr => ?_
        rw [hw r hr, h3]
        rcases h with h | h
        · simp [gfun, h r hr]
        · rw [he]; simp [gfun, h r hr]
      · exact op2_triv hv hj (by omega)

lemma true_src
    (h : (∀ r, R r → M.sv n j (M.s1 j) r = true) ∨ (∀ r, R r → M.sv n j (M.s2 j) r = true)) :
    ∃ t, TgtOk n j t ∧ ∀ r, R r → M.w j r = tval n M j t r := by
  have hop := hv.op_lt j hj
  have hw := hv.w_eq j hj
  by_cases h0 : M.op j = 0
  · rcases h with h | h
    · exact copy_tgt hv hj (hv.s2_le j hj) fun r hr => by rw [hw r hr, h0]; simp [gfun, h r hr]
    · exact copy_tgt hv hj (hv.s1_le j hj) fun r hr => by rw [hw r hr, h0]; simp [gfun, h r hr]
  · by_cases h1 : M.op j = 1
    · refine const_tgt true fun r hr => ?_
      rw [hw r hr, h1]
      rcases h with h | h <;> simp [gfun, h r hr]
    · by_cases h3 : M.op j = 3
      · have he := hv.not_eq j hj h3
        refine const_tgt false fun r hr => ?_
        rw [hw r hr, h3]
        rcases h with h | h
        · simp [gfun, h r hr]
        · rw [he]; simp [gfun, h r hr]
      · exact op2_triv hv hj (by omega)

lemma notnot_triv {i : ℕ} (hi : i < j) (h3 : M.op j = 3) (hi3 : M.op i = 3)
    (he : M.s1 j = n + i) : ∃ t, TgtOk n j t ∧ ∀ r, R r → M.w j r = tval n M j t r := by
  have hle := hv.s1_le i (by omega)
  refine copy_tgt hv hj (k := if M.s1 i < n + i then M.s1 i else n + j) (by split_ifs <;> omega)
    fun r hr => ?_
  have e1 : M.sv n j (n + i) r = M.w i r := by
    unfold Model.sv
    simp only [if_neg (show ¬ n + i < n by omega), if_pos (show n + i < n + j by omega),
      show n + i - n = i by omega]
  rw [hv.w_eq j hj r hr, h3, he, e1, hv.w_eq i (by omega) r hr, hi3]
  simp only [gfun, show ¬ (3 : ℕ) = 0 by omega, show ¬ (3 : ℕ) = 1 by omega, if_true, if_false,
    Bool.not_not]
  unfold Model.sv
  by_cases h6 : M.s1 i < n + i
  · simp only [if_pos h6]
    by_cases h7 : M.s1 i < n
    · simp [h7]
    · simp only [if_neg h7, if_pos (show M.s1 i < n + j by omega)]
  · simp only [if_neg h6, if_neg (show ¬ M.s1 i < n by omega), if_neg (show ¬ n + j < n by omega),
      if_neg (show ¬ n + j < n + j by omega)]

lemma same_src (h3 : M.op j ≠ 3) (he : M.s1 j = M.s2 j) :
    ∃ t, TgtOk n j t ∧ ∀ r, R r → M.w j r = tval n M j t r := by
  have := hv.op_lt j hj
  by_cases h2 : M.op j = 2
  · exact op2_triv hv hj h2
  refine copy_tgt hv hj (hv.s1_le j hj) fun r hr => ?_
  rw [hv.w_eq j hj r hr, ← he]
  unfold gfun
  simp only [if_neg h3]
  split_ifs <;> first | omega | cases M.sv n j (M.s1 j) r <;> rfl

end triv

lemma pad_w {n s : ℕ} {g : ℕ → Bool} {R : ℕ → Prop} {M : Model} (hv : Valid n s g R M)
    {i : ℕ} (hi : i < s) (hp : M.pad n i) {r : ℕ} (hr : R r) : M.w i r = true := by
  rw [hv.w_eq i hi r hr, hp.1]
  simp [gfun]

def lexWord (B : ℕ) (a : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | m + 1 => lexWord B a m * B + a m

lemma lexWord_lt {B : ℕ} {a : ℕ → ℕ} : ∀ m, (∀ i < m, a i < B) → lexWord B a m < B ^ m
  | 0, _ => by simp [lexWord]
  | m + 1, h => by
    have ih := lexWord_lt m (fun i hi => h i (by omega))
    have hm := h m (by omega)
    have h2 : (lexWord B a m + 1) * B ≤ B ^ m * B := Nat.mul_le_mul_right _ ih
    rw [Nat.add_mul, Nat.one_mul] at h2
    simp only [lexWord, pow_succ]
    omega

lemma lexWord_congr {B : ℕ} {a b : ℕ → ℕ} :
    ∀ m, (∀ i < m, a i = b i) → lexWord B a m = lexWord B b m
  | 0, _ => rfl
  | m + 1, h => by
    simp only [lexWord, lexWord_congr m (fun i hi => h i (by omega)), h m (by omega)]

lemma lexWord_lt_of {B : ℕ} {a b : ℕ → ℕ} {j : ℕ} (hab : ∀ i < j, a i = b i) (hj : b j < a j) :
    ∀ m, j < m → (∀ i < m, b i < B) → lexWord B b m < lexWord B a m
  | 0, h, _ => by omega
  | m + 1, hjm, hb => by
    by_cases h : m = j
    · subst h
      simp only [lexWord, lexWord_congr m hab]
      omega
    · have ih := lexWord_lt_of hab hj m (by omega) (fun i hi => hb i (by omega))
      have hm := hb m (by omega)
      have h2 : (lexWord B b m + 1) * B ≤ lexWord B a m * B := Nat.mul_le_mul_right _ ih
      rw [Nat.add_mul, Nat.one_mul] at h2
      simp only [lexWord]
      omega

def lexKey (n s : ℕ) (M : Model) (j : ℕ) : ℕ := M.s1 j * (4 * (n + s + 1)) + M.s2 j * 4 + M.op j

def lexB (n s : ℕ) : ℕ := 4 * (n + s + 1) * (n + s + 1)

lemma lex3 (K x1 y1 z1 x2 y2 z2 : ℕ) (hy : y1 * 4 + z1 < K) (hz : z1 < 4)
    (h : x1 < x2 ∨ (x1 = x2 ∧ (y1 < y2 ∨ (y1 = y2 ∧ z1 < z2)))) :
    x1 * K + y1 * 4 + z1 < x2 * K + y2 * 4 + z2 := by
  rcases h with h | ⟨rfl, h | ⟨rfl, h⟩⟩
  · have : (x1 + 1) * K ≤ x2 * K := Nat.mul_le_mul_right _ h
    rw [Nat.add_mul, Nat.one_mul] at this
    omega
  · omega
  · omega

section keys
variable {n s : ℕ} {g : ℕ → Bool} {R : ℕ → Prop} {M : Model}

lemma lexKey_lt (hv : Valid n s g R M) {j : ℕ} (hj : j < s) : lexKey n s M j < lexB n s := by
  have h1 := hv.s1_le j hj
  have h2 := hv.s2_le j hj
  have h3 := hv.op_lt j hj
  have : M.s1 j * (4 * (n + s + 1)) ≤ (n + s) * (4 * (n + s + 1)) :=
    Nat.mul_le_mul_right _ (by omega)
  have e : (n + s) * (4 * (n + s + 1)) + 4 * (n + s + 1) = 4 * (n + s + 1) * (n + s + 1) := by
    ring
  unfold lexKey lexB
  omega

def meas2 (n s : ℕ) (M : Model) : ℕ :=
  lexB n s ^ s * muf s (ind n M) + lexWord (lexB n s) (lexKey n s M) s

lemma lexWord_lt_pow (hv : Valid n s g R M) :
    lexWord (lexB n s) (lexKey n s M) s < lexB n s ^ s :=
  lexWord_lt s fun _ hi => lexKey_lt hv hi

end keys

lemma meas2_mv {n s : ℕ} {g : ℕ → Bool} {R : ℕ → Prop} {M : Model} {d t : ℕ}
    (hv : Valid n s g R M) (hv' : Valid n s g R (mv n s M d t)) (hd : d < s)
    (hpos : ¬ M.pad n d ∨ ∃ i < d, ¬ M.pad n i) : meas2 n s (mv n s M d t) < meas2 n s M := by
  have hlt : muf s (ind n (mv n s M d t)) < muf s (ind n M) := by
    apply muf_lt s (ind n M) (ind n (mv n s M d t)) d hd
    · simp [ind, pad_mv0]
    · intro i hi; exact ind_congr (pad_mv_shift hv hi hd)
    · intro j hj _
      unfold ind
      by_cases h1 : (mv n s M d t).pad n j
      · simp [h1]
      · have h2 : ¬ M.pad n j := fun h => h1 (pad_mv_later hj h)
        simp [h1, h2]
    · rcases hpos with h | ⟨i, hi, h⟩
      · left; simp [ind, h]
      · right; exact ⟨i, hi, by simp [ind, h]⟩
  have b1 := lexWord_lt_pow hv'
  have : lexB n s ^ s * muf s (ind n (mv n s M d t)) + lexB n s ^ s ≤
      lexB n s ^ s * muf s (ind n M) := by
    rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hlt
  unfold meas2
  omega

lemma meas2_sw {n s : ℕ} {g : ℕ → Bool} {R : ℕ → Prop} {M : Model} {j : ℕ}
    (hv : Valid n s g R M) (hj : j < s) (hlt : M.s2 j < M.s1 j) :
    meas2 n s (sw M j) < meas2 n s M := by
  have hind : ind n (sw M j) = ind n M := by funext i; exact ind_congr (pad_sw (n := n) (M := M) (j := j) i)
  unfold meas2
  rw [hind]
  have hk : lexKey n s (sw M j) j < lexKey n s M j := by
    have h1 := hv.s1_le j hj
    have : (M.s2 j + 1) * (4 * (n + s + 1)) ≤ M.s1 j * (4 * (n + s + 1)) :=
      Nat.mul_le_mul_right _ hlt
    rw [Nat.add_mul, Nat.one_mul] at this
    simp only [lexKey, sw, Model.op_mk, Model.s1_mk, Model.s2_mk, Model.so_mk, Model.w_mk, if_pos rfl, ↓reduceIte]
    omega
  have := lexWord_lt_of (B := lexB n s) (a := lexKey n s M) (b := lexKey n s (sw M j)) (j := j)
    (fun i hi => by simp [lexKey, sw, Model.op_mk, Model.s1_mk, Model.s2_mk, Model.so_mk, Model.w_mk, show i ≠ j by omega]) hk s hj
    (fun i hi => lexKey_lt (valid_sw hv j) hi)
  omega

def tsw (n j k : ℕ) : ℕ := if k = n + j then n + j + 1 else if k = n + j + 1 then n + j else k

def xsw (n : ℕ) (M : Model) (j : ℕ) : Model :=
  Model.mk (fun i => if i = j then M.op (j + 1) else if i = j + 1 then M.op j else M.op i)
    (fun i => if i = j then M.s1 (j + 1) else if i = j + 1 then M.s1 j
    else if j + 1 < i then tsw n j (M.s1 i) else M.s1 i)
    (fun i => if i = j then M.s2 (j + 1) else if i = j + 1 then M.s2 j
    else if j + 1 < i then tsw n j (M.s2 i) else M.s2 i)
    (tsw n j M.so)
    (fun i r => if i = j then M.w (j + 1) r else if i = j + 1 then M.w j r else M.w i r)

section xsw
variable {n s : ℕ} {g : ℕ → Bool} {R : ℕ → Prop} {M : Model} {j : ℕ}

lemma sv_xsw_low {i i' k r : ℕ} (hk : k < n + j) (hi : j ≤ i) (hi' : j ≤ i') :
    (xsw n M j).sv n i k r = M.sv n i' k r := by
  unfold Model.sv
  by_cases h6 : k < n
  · simp [h6]
  · simp only [if_neg h6, if_pos (show k < n + i by omega), if_pos (show k < n + i' by omega),
      xsw, Model.op_mk, Model.s1_mk, Model.s2_mk, Model.so_mk, Model.w_mk, if_neg (show k - n ≠ j by omega), if_neg (show k - n ≠ j + 1 by omega)]

lemma sv_xsw_early {i k r : ℕ} (hi : i < j) : (xsw n M j).sv n i k r = M.sv n i k r := by
  unfold Model.sv
  by_cases h6 : k < n
  · simp [h6]
  · by_cases h7 : k < n + i
    · simp only [if_neg h6, if_pos h7, xsw, Model.op_mk, Model.s1_mk, Model.s2_mk, Model.so_mk, Model.w_mk, if_neg (show k - n ≠ j by omega),
        if_neg (show k - n ≠ j + 1 by omega)]
    · simp only [if_neg h6, if_neg h7]

lemma sv_xsw_late {i k r : ℕ} (hi : j + 1 < i) :
    (xsw n M j).sv n i (tsw n j k) r = M.sv n i k r := by
  unfold tsw
  by_cases h1 : k = n + j
  · subst h1
    simp only [if_pos rfl, ↓reduceIte]
    unfold Model.sv
    simp only [if_neg (show ¬ n + j + 1 < n by omega), if_pos (show n + j + 1 < n + i by omega),
      if_neg (show ¬ n + j < n by omega), if_pos (show n + j < n + i by omega), xsw, Model.op_mk, Model.s1_mk, Model.s2_mk, Model.so_mk, Model.w_mk,
      show n + j + 1 - n = j + 1 by omega, show n + j - n = j by omega,
      if_neg (show j + 1 ≠ j by omega), if_pos rfl, ↓reduceIte]
  · by_cases h2 : k = n + j + 1
    · subst h2
      simp only [if_neg h1, if_pos rfl, ↓reduceIte]
      unfold Model.sv
      simp only [if_neg (show ¬ n + j + 1 < n by omega), if_pos (show n + j + 1 < n + i by omega),
        if_neg (show ¬ n + j < n by omega), if_pos (show n + j < n + i by omega), xsw, Model.op_mk, Model.s1_mk, Model.s2_mk, Model.so_mk, Model.w_mk,
        show n + j + 1 - n = j + 1 by omega, show n + j - n = j by omega, if_pos rfl, ↓reduceIte]
    · simp only [if_neg h1, if_neg h2]
      unfold Model.sv
      by_cases h6 : k < n
      · simp [h6]
      · by_cases h7 : k < n + i
        · simp only [if_neg h6, if_pos h7, xsw, Model.op_mk, Model.s1_mk, Model.s2_mk, Model.so_mk, Model.w_mk, if_neg (show k - n ≠ j by omega),
            if_neg (show k - n ≠ j + 1 by omega)]
        · simp only [if_neg h6, if_neg h7]

lemma tsw_le {i k : ℕ} (hi : j + 1 ≤ i) (hk : k ≤ n + i) : tsw n j k ≤ n + i := by
  unfold tsw; split_ifs <;> omega

lemma tsw_eq_iff {i k : ℕ} (hi : j + 1 < i) : tsw n j k = n + i ↔ k = n + i := by
  unfold tsw; split_ifs <;> omega

variable (hv : Valid n s g R M) (hj : j + 1 < s) (h1 : M.s1 j < n + j) (h2 : M.s2 j < n + j)
  (h3 : M.s1 (j + 1) < n + j) (h4 : M.s2 (j + 1) < n + j)
include hv hj h1 h2 h3 h4

lemma valid_xsw : Valid n s g R (xsw n M j) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi
    simp only [xsw, Model.op_mk, Model.s1_mk, Model.s2_mk, Model.so_mk, Model.w_mk]; split_ifs
    · exact hv.op_lt _ hj
    · exact hv.op_lt _ (by omega)
    · exact hv.op_lt _ hi
  · intro i hi h
    simp only [xsw, Model.op_mk, Model.s1_mk, Model.s2_mk, Model.so_mk, Model.w_mk] at h ⊢
    split_ifs at h ⊢ with a b c
    · exact hv.not_eq _ hj h
    · exact hv.not_eq _ (by omega) h
    · rw [hv.not_eq i hi h]
    · exact hv.not_eq i hi h
  · intro i hi
    simp only [xsw, Model.op_mk, Model.s1_mk, Model.s2_mk, Model.so_mk, Model.w_mk]; split_ifs with a b c
    · omega
    · omega
    · exact tsw_le (by omega) (hv.s1_le i hi)
    · exact hv.s1_le i hi
  · intro i hi
    simp only [xsw, Model.op_mk, Model.s1_mk, Model.s2_mk, Model.so_mk, Model.w_mk]; split_ifs with a b c
    · omega
    · omega
    · exact tsw_le (by omega) (hv.s2_le i hi)
    · exact hv.s2_le i hi
  · exact tsw_le (by omega) hv.so_le
  · intro i hi r hr
    by_cases a : i = j
    · subst a
      have e1 : (xsw n M i).s1 i = M.s1 (i + 1) := by simp [xsw, Model.op_mk, Model.s1_mk, Model.s2_mk, Model.so_mk, Model.w_mk]
      have e2 : (xsw n M i).s2 i = M.s2 (i + 1) := by simp [xsw, Model.op_mk, Model.s1_mk, Model.s2_mk, Model.so_mk, Model.w_mk]
      have e3 : (xsw n M i).op i = M.op (i + 1) := by simp [xsw, Model.op_mk, Model.s1_mk, Model.s2_mk, Model.so_mk, Model.w_mk]
      have e4 : (xsw n M i).w i r = M.w (i + 1) r := by simp [xsw, Model.op_mk, Model.s1_mk, Model.s2_mk, Model.so_mk, Model.w_mk]
      rw [e1, e2, e3, e4, sv_xsw_low h3 le_rfl (Nat.le_succ i),
        sv_xsw_low h4 le_rfl (Nat.le_succ i)]
      exact hv.w_eq (i + 1) hj r hr
    · by_cases b : i = j + 1
      · subst b
        have e1 : (xsw n M j).s1 (j + 1) = M.s1 j := by simp [xsw, Model.op_mk, Model.s1_mk, Model.s2_mk, Model.so_mk, Model.w_mk]
        have e2 : (xsw n M j).s2 (j + 1) = M.s2 j := by simp [xsw, Model.op_mk, Model.s1_mk, Model.s2_mk, Model.so_mk, Model.w_mk]
        have e3 : (xsw n M j).op (j + 1) = M.op j := by simp [xsw, Model.op_mk, Model.s1_mk, Model.s2_mk, Model.so_mk, Model.w_mk]
        have e4 : (xsw n M j).w (j + 1) r = M.w j r := by simp [xsw, Model.op_mk, Model.s1_mk, Model.s2_mk, Model.so_mk, Model.w_mk]
        rw [e1, e2, e3, e4, sv_xsw_low h1 (Nat.le_succ j) le_rfl,
          sv_xsw_low h2 (Nat.le_succ j) le_rfl]
        exact hv.w_eq j (by omega) r hr
      · by_cases c : j + 1 < i
        · have e1 : (xsw n M j).s1 i = tsw n j (M.s1 i) := by simp [xsw, Model.op_mk, Model.s1_mk, Model.s2_mk, Model.so_mk, Model.w_mk, a, b, c]
          have e2 : (xsw n M j).s2 i = tsw n j (M.s2 i) := by simp [xsw, Model.op_mk, Model.s1_mk, Model.s2_mk, Model.so_mk, Model.w_mk, a, b, c]
          have e3 : (xsw n M j).op i = M.op i := by simp [xsw, Model.op_mk, Model.s1_mk, Model.s2_mk, Model.so_mk, Model.w_mk, a, b]
          have e4 : (xsw n M j).w i r = M.w i r := by simp [xsw, Model.op_mk, Model.s1_mk, Model.s2_mk, Model.so_mk, Model.w_mk, a, b]
          rw [e1, e2, e3, e4, sv_xsw_late c, sv_xsw_late c]
          exact hv.w_eq i hi r hr
        · have e1 : (xsw n M j).s1 i = M.s1 i := by simp [xsw, Model.op_mk, Model.s1_mk, Model.s2_mk, Model.so_mk, Model.w_mk, a, b, c]
          have e2 : (xsw n M j).s2 i = M.s2 i := by simp [xsw, Model.op_mk, Model.s1_mk, Model.s2_mk, Model.so_mk, Model.w_mk, a, b, c]
          have e3 : (xsw n M j).op i = M.op i := by simp [xsw, Model.op_mk, Model.s1_mk, Model.s2_mk, Model.so_mk, Model.w_mk, a, b]
          have e4 : (xsw n M j).w i r = M.w i r := by simp [xsw, Model.op_mk, Model.s1_mk, Model.s2_mk, Model.so_mk, Model.w_mk, a, b]
          rw [e1, e2, e3, e4, sv_xsw_early (by omega), sv_xsw_early (by omega)]
          exact hv.w_eq i hi r hr
  · intro r hr
    have e : (xsw n M j).so = tsw n j M.so := rfl
    rw [e, sv_xsw_late hj]
    exact hv.out_eq r hr

omit hv hj in
lemma ind_xsw : ind n (xsw n M j) = ind n M := by
  funext i
  unfold ind
  have hp : (xsw n M j).pad n i ↔ M.pad n i := by
    by_cases a : i = j
    · subst a
      simp only [Model.pad, xsw, Model.op_mk, Model.s1_mk, Model.s2_mk, Model.so_mk, Model.w_mk, if_pos rfl, ↓reduceIte]
      omega
    · by_cases b : i = j + 1
      · subst b
        simp only [Model.pad, xsw, Model.op_mk, Model.s1_mk, Model.s2_mk, Model.so_mk, Model.w_mk, if_neg a, if_pos rfl, ↓reduceIte]
        omega
      · by_cases c : j + 1 < i
        · simp only [Model.pad, xsw, Model.op_mk, Model.s1_mk, Model.s2_mk, Model.so_mk, Model.w_mk, if_neg a, if_neg b, if_pos c, tsw_eq_iff c]
        · simp only [Model.pad, xsw, Model.op_mk, Model.s1_mk, Model.s2_mk, Model.so_mk, Model.w_mk, if_neg a, if_neg b, if_neg c]
  by_cases h : M.pad n i
  · simp [h, hp.2 h]
  · have h' : ¬ (xsw n M j).pad n i := fun h' => h (hp.1 h')
    simp [h, h']

lemma meas2_xsw (hlt : lexKey n s M (j + 1) < lexKey n s M j) :
    meas2 n s (xsw n M j) < meas2 n s M := by
  unfold meas2
  rw [ind_xsw h1 h2 h3 h4]
  have hk : lexKey n s (xsw n M j) j = lexKey n s M (j + 1) := by simp [lexKey, xsw, Model.op_mk, Model.s1_mk, Model.s2_mk, Model.so_mk, Model.w_mk]
  have := lexWord_lt_of (B := lexB n s) (a := lexKey n s M) (b := lexKey n s (xsw n M j))
    (j := j)
    (fun i hi => by
      simp [lexKey, xsw, Model.op_mk, Model.s1_mk, Model.s2_mk, Model.so_mk, Model.w_mk, show i ≠ j by omega, show i ≠ j + 1 by omega,
        show ¬ j + 1 < i by omega])
    (by rw [hk]; exact hlt) s (by omega)
    (fun i hi => lexKey_lt (valid_xsw hv hj h1 h2 h3 h4) hi)
  omega

end xsw

def LexNF (n s : ℕ) (M : Model) : Prop :=
  ∀ j, j + 1 < s → ¬ M.pad n j → M.s1 (j + 1) ≠ n + j → M.s2 (j + 1) ≠ n + j →
    M.s1 j < M.s1 (j + 1) ∨ (M.s1 j = M.s1 (j + 1) ∧ (M.s2 j < M.s2 (j + 1) ∨
      (M.s2 j = M.s2 (j + 1) ∧ M.op j = 0 ∧ M.op (j + 1) = 1)))

section formula
variable (n s : ℕ)

def lexBase (j : ℕ) : List ℕ :=
  [P (ix n s 7 j 0), P (ix n s 1 (j + 1) (n + j)), P (ix n s 2 (j + 1) (n + j))]

def fLex : List (List ℕ) :=
  (List.range (s - 1)).flatMap fun j =>
    (List.range (n + j + 1)).flatMap fun a =>
      ((List.range a).map fun b => [Q (ix n s 1 j a), Q (ix n s 1 (j + 1) b)] ++ lexBase n s j) ++
      (List.range (n + j + 1)).flatMap fun c =>
        ((List.range c).map fun d =>
          [Q (ix n s 1 j a), Q (ix n s 1 (j + 1) a), Q (ix n s 2 j c), Q (ix n s 2 (j + 1) d)] ++
            lexBase n s j) ++
        [[Q (ix n s 1 j a), Q (ix n s 1 (j + 1) a), Q (ix n s 2 j c), Q (ix n s 2 (j + 1) c),
            Q (ix n s 0 j 1)] ++ lexBase n s j,
         [Q (ix n s 1 j a), Q (ix n s 1 (j + 1) a), Q (ix n s 2 j c), Q (ix n s 2 (j + 1) c),
            Q (ix n s 0 (j + 1) 0)] ++ lexBase n s j]

def enc2 (g : ℕ → Bool) (rows : List ℕ) : List (List ℕ) := enc n s g rows ++ fLex n s

end formula

lemma s_fLex {n s : ℕ} {g : ℕ → Bool} {R : ℕ → Prop} {M : Model} (hv : Valid n s g R M)
    (hn : NF n s M) (hl : LexNF n s M) : ∀ c ∈ fLex n s, ClauseSat (val n s M) c := by
  intro c hc
  simp only [fLex, List.mem_flatMap, List.mem_append, List.mem_map, List.mem_range,
    List.mem_cons, List.not_mem_nil, or_false] at hc
  obtain ⟨j, hj, a, ha, hc⟩ := hc
  have hj1 : j + 1 < s := Nat.add_lt_of_lt_sub hj
  have hj0 : j < s := Nat.lt_of_succ_lt hj1
  have hb1 : ClauseSat (val n s M) (lexBase n s j) ↔
      M.pad n j ∨ M.s1 (j + 1) = n + j ∨ M.s2 (j + 1) = n + j := by
    simp (disch := first | omega | (apply wd_lt1; omega) | (apply wd_lt2; assumption)) only [lexBase, cs_cons, cs_nil, litVal_P, v_pad, v_s1, v_s2, or_false,
      beq_iff_eq, decide_eq_true_eq]
  have happ : ∀ c', ClauseSat (val n s M) (lexBase n s j) →
      ClauseSat (val n s M) (c' ++ lexBase n s j) := fun c' ⟨l, hl', hv'⟩ =>
    ⟨l, List.mem_append_right _ hl', hv'⟩
  have hfront : ∀ c', (∃ l ∈ c', litVal (val n s M) l = true) →
      ClauseSat (val n s M) (c' ++ lexBase n s j) := fun c' ⟨l, hl', hv'⟩ =>
    ⟨l, List.mem_append_left _ hl', hv'⟩
  by_cases hesc : M.pad n j ∨ M.s1 (j + 1) = n + j ∨ M.s2 (j + 1) = n + j
  · rcases hc with ⟨b, hb, rfl⟩ | ⟨c', hc', ⟨d, hd, rfl⟩ | rfl | rfl⟩ <;>
      exact happ _ (hb1.2 hesc)
  have hnp : ¬ M.pad n j := fun h => hesc (Or.inl h)
  have L := hl j hj1 hnp (fun h => hesc (Or.inr (Or.inl h)))
    (fun h => hesc (Or.inr (Or.inr h)))
  have hop0 := hn.padOp j hj0
  rcases hc with ⟨b, hb, rfl⟩ | ⟨c', hc', ⟨d, hd, rfl⟩ | rfl | rfl⟩ <;> apply hfront <;>
    simp (disch := first | omega | (apply wd_lt1; omega) | (apply wd_lt2; assumption)) only [List.mem_cons, List.not_mem_nil, or_false, exists_eq_or_imp,
      exists_eq_left, litVal_Q, v_s1, v_s2, v_op, Bool.not_eq_true', beq_eq_false_iff_ne,
      ne_eq] <;> omega

lemma enc2_sat {n s : ℕ} {g : ℕ → Bool} {rows : List ℕ} {M : Model}
    (hrows : ∀ r ∈ rows, r < 2 ^ n) (hv : Valid n s g (· ∈ rows) M) (hn : NF n s M)
    (hl : LexNF n s M) : ∀ c ∈ enc2 n s g rows, ClauseSat (val n s M) c := by
  intro c hc
  rcases List.mem_append.1 hc with h | h
  · exact enc_sat hrows hv hn c h
  · exact s_fLex hv hn hl c h

def UniqueNot (s : ℕ) (M : Model) : Prop :=
  ∀ i < s, ∀ j < s, M.op i = 3 → M.op j = 3 → i = j

lemma unique_sw {s : ℕ} {M : Model} (h : UniqueNot s M) (d : ℕ) :
    UniqueNot s (sw M d) := h

lemma unique_mv {n s d t : ℕ} {M : Model} (h : UniqueNot s M) :
    UniqueNot s (mv n s M d t) := by
  intro i hi j hj hi3 hj3
  have hi0 : i ≠ 0 := by intro hi0; subst i; simp [mv, Model.op_mk, Model.s1_mk, Model.s2_mk, Model.so_mk, Model.w_mk] at hi3
  have hj0 : j ≠ 0 := by intro hj0; subst j; simp [mv, Model.op_mk, Model.s1_mk, Model.s2_mk, Model.so_mk, Model.w_mk] at hj3
  have hi3' : M.op (if i ≤ d then i - 1 else i) = 3 := by
    by_cases hdi : i ≤ d <;> simpa [mv, Model.op_mk, Model.s1_mk, Model.s2_mk, Model.so_mk, Model.w_mk, hi0, hdi] using hi3
  have hj3' : M.op (if j ≤ d then j - 1 else j) = 3 := by
    by_cases hdj : j ≤ d <;> simpa [mv, Model.op_mk, Model.s1_mk, Model.s2_mk, Model.so_mk, Model.w_mk, hj0, hdj] using hj3
  have hil : (if i ≤ d then i - 1 else i) < s := by split <;> omega
  have hjl : (if j ≤ d then j - 1 else j) < s := by split <;> omega
  have he := h _ hil _ hjl hi3' hj3'
  split_ifs at he <;> omega

lemma unique_xsw {n s d : ℕ} {M : Model} (h : UniqueNot s M) (hd : d + 1 < s) :
    UniqueNot s (xsw n M d) := by
  intro i hi j hj hi3 hj3
  have hi3' : M.op (if i = d then d + 1 else if i = d + 1 then d else i) = 3 := by
    by_cases h1 : i = d
    · simpa [xsw, Model.op_mk, Model.s1_mk, Model.s2_mk, Model.so_mk, Model.w_mk, h1] using hi3
    · by_cases h2 : i = d + 1 <;> simpa [xsw, Model.op_mk, Model.s1_mk, Model.s2_mk, Model.so_mk, Model.w_mk, h1, h2] using hi3
  have hj3' : M.op (if j = d then d + 1 else if j = d + 1 then d else j) = 3 := by
    by_cases h1 : j = d
    · simpa [xsw, Model.op_mk, Model.s1_mk, Model.s2_mk, Model.so_mk, Model.w_mk, h1] using hj3
    · by_cases h2 : j = d + 1 <;> simpa [xsw, Model.op_mk, Model.s1_mk, Model.s2_mk, Model.so_mk, Model.w_mk, h1, h2] using hj3
  have hil : (if i = d then d + 1 else if i = d + 1 then d else i) < s := by
    split_ifs <;> omega
  have hjl : (if j = d then d + 1 else if j = d + 1 then d else j) < s := by
    split_ifs <;> omega
  have he := h _ hil _ hjl hi3' hj3'
  split_ifs at he <;> omega

lemma nf_of_min_unique {n s : ℕ} {g : ℕ → Bool} {R : ℕ → Prop} {M : Model} (hv : Valid n s g R M)
    (hu : UniqueNot s M)
    (hmin : ∀ M', Valid n s g R M' → UniqueNot s M' → meas2 n s M' < meas2 n s M → False) : NF n s M := by
  classical
  have hmv : ∀ d t, d < s → TgtOk n d t →
      (M.Read n s d → ∀ r, R r → M.w d r = tval n M d t r) →
      (¬ M.pad n d ∨ ∃ i < d, ¬ M.pad n i) → False := by
    intro d t hd ht htr hpos
    have hv' := valid_mv hv hd ht htr
    exact hmin _ hv' (unique_mv hu) (meas2_mv hv hv' hd hpos)
  have htriv : ∀ d < s, ¬ M.pad n d →
      (∃ t, TgtOk n d t ∧ ∀ r, R r → M.w d r = tval n M d t r) → False := by
    intro d hd hnp ⟨t, ht, hw⟩
    exact hmv d t hd ht (fun _ => hw) (Or.inl hnp)
  have padOp : ∀ j < s, M.op j = 2 → M.pad n j := by
    intro j hj h2
    by_contra hnp
    exact htriv j hj hnp (op2_triv hv hj h2)
  have noF : ∀ j < s, ¬ M.pad n j → M.s1 j ≠ n + j ∧ M.s2 j ≠ n + j := by
    intro j hj hnp
    by_contra hc
    have hF : M.s1 j = n + j ∨ M.s2 j = n + j := by tauto
    refine htriv j hj hnp (false_src hv hj ?_)
    rcases hF with h | h
    · exact Or.inl fun r _ => by rw [h]; simp [Model.sv]
    · exact Or.inr fun r _ => by rw [h]; simp [Model.sv]
  have padRd : ∀ j < s, ∀ i < j, M.pad n i → M.s1 j ≠ n + i ∧ M.s2 j ≠ n + i := by
    intro j hj i hi hpi
    by_contra hc
    have hT : M.s1 j = n + i ∨ M.s2 j = n + i := by tauto
    have hnp : ¬ M.pad n j := fun hp' => by
      rcases hT with h | h
      · have := hp'.2.1; omega
      · have := hp'.2.2; omega
    have e : ∀ r, R r → M.sv n j (n + i) r = true := by
      intro r hr
      unfold Model.sv
      simp only [if_neg (show ¬ n + i < n by omega), if_pos (show n + i < n + j by omega),
        show n + i - n = i by omega]
      exact pad_w hv (by omega) hpi hr
    refine htriv j hj hnp (true_src hv hj ?_)
    rcases hT with h | h
    · exact Or.inl fun r hr => by rw [h]; exact e r hr
    · exact Or.inr fun r hr => by rw [h]; exact e r hr
  have notNot : ∀ j < s, ∀ i < j, M.op j = 3 → M.op i = 3 → M.s1 j ≠ n + i := by
    intro j hj i hi h3 hi3 he
    exact htriv j hj (fun hp => by have := hp.1; omega) (notnot_triv hv hj hi h3 hi3 he)
  have ord : ∀ j < s, ¬ M.pad n j → M.s1 j < M.s2 j ∨ (M.op j = 3 ∧ M.s1 j = M.s2 j) := by
    intro j hj hnp
    by_contra hc
    by_cases he : M.s1 j = M.s2 j
    · exact htriv j hj hnp (same_src hv hj (fun h3 => hc (Or.inr ⟨h3, he⟩)) he)
    · exact hmin _ (valid_sw hv j) (unique_sw hu j) (meas2_sw hv hj (by omega))
  have pre : ∀ j, j + 1 < s → M.pad n (j + 1) → M.pad n j := by
    intro j hj hp1
    by_contra hnp
    exact hmv (j + 1) 1 hj (Or.inr (Or.inl rfl))
      (fun _ r hr => by rw [pad_w hv hj hp1 hr]; simp [tval]) (Or.inr ⟨j, by omega, hnp⟩)
  have rd : ∀ j < s, ¬ M.pad n j → M.Read n s j := by
    intro j hj hnp
    by_contra hc
    exact hmv j 0 hj (Or.inl rfl) (fun h => absurd h hc) (Or.inl hnp)
  refine ⟨pre, padOp, noF, padRd, ord, notNot, ?_, ?_⟩
  · intro j hj hnp
    rcases rd j (by omega) hnp with h | h
    · exact h
    · exfalso
      by_cases hl : M.pad n (s - 1)
      · have hall : ∀ m, m < s → M.pad n (s - 1 - m) := by
          intro m
          induction m with
          | zero => intro _; simpa using hl
          | succ m ih =>
            intro hm
            have := pre (s - 1 - (m + 1)) (by omega)
              (by rw [show s - 1 - (m + 1) + 1 = s - 1 - m by omega]; exact ih (by omega))
            exact this
        exact hnp (by
          have := hall (s - 1 - j) (by omega)
          rwa [show s - 1 - (s - 1 - j) = j by omega] at this)
      · rcases rd (s - 1) (by omega) hl with ⟨i, hi1, hi2, _⟩ | h'
        · omega
        · omega
  · intro hs
    by_cases h6 : M.pad n (s - 1)
    · exact Or.inr h6
    · rcases rd (s - 1) (by omega) h6 with ⟨j, hj1, hj2, _⟩ | h
      · omega
      · left; omega

lemma lex_of_min_unique {n s : ℕ} {g : ℕ → Bool} {R : ℕ → Prop} {M : Model} (hv : Valid n s g R M)
    (hu : UniqueNot s M)
    (hmin : ∀ M', Valid n s g R M' → UniqueNot s M' → meas2 n s M' < meas2 n s M → False) : LexNF n s M := by
  have hnf := nf_of_min_unique hv hu hmin
  intro j hj hnp ha hb
  have hnp1 : ¬ M.pad n (j + 1) := fun h => hnp (hnf.pre j hj h)
  have f0 := hnf.noF j (by omega) hnp
  have f1 := hnf.noF (j + 1) hj hnp1
  have l1 := hv.s1_le j (by omega)
  have l2 := hv.s2_le j (by omega)
  have l3 := hv.s1_le (j + 1) hj
  have l4 := hv.s2_le (j + 1) hj
  have h1 : M.s1 j < n + j := by omega
  have h2 : M.s2 j < n + j := by omega
  have h3 : M.s1 (j + 1) < n + j := by omega
  have h4 : M.s2 (j + 1) < n + j := by omega
  have o0 := hv.op_lt j (by omega)
  have o1 := hv.op_lt (j + 1) hj
  have o0' : M.op j ≠ 2 := fun h => hnp (hnf.padOp j (by omega) h)
  have o1' : M.op (j + 1) ≠ 2 := fun h => hnp1 (hnf.padOp (j + 1) hj h)
  
  have hx : lexKey n s M (j + 1) < lexKey n s M j → False := fun hlt =>
    hmin _ (valid_xsw hv hj h1 h2 h3 h4) (unique_xsw hu hj) (meas2_xsw hv hj h1 h2 h3 h4 hlt)
  have hK : ∀ y z : ℕ, y < n + j → z < 4 → y * 4 + z < 4 * (n + s + 1) := by
    intro y z hy hz; omega
  by_contra hc
  rcases lt_trichotomy (M.s1 j) (M.s1 (j + 1)) with e1 | e1 | e1
  · exact hc (Or.inl e1)
  · rcases lt_trichotomy (M.s2 j) (M.s2 (j + 1)) with e2 | e2 | e2
    · exact hc (Or.inr ⟨e1, Or.inl e2⟩)
    · by_cases e3 : M.op j = M.op (j + 1)
      · 
        have hw : ∀ r, R r → M.w (j + 1) r = M.sv n (j + 1) (n + j) r := by
          intro r hr
          have hs : ∀ k, k < n + j → M.sv n (j + 1) k r = M.sv n j k r := by
            intro k hk
            unfold Model.sv
            by_cases h6 : k < n
            · simp [h6]
            · simp only [if_neg h6, if_pos hk, if_pos (show k < n + (j + 1) by omega)]
          rw [hv.w_eq (j + 1) hj r hr, hs _ h3, hs _ h4, ← e1, ← e2, ← e3,
            ← hv.w_eq j (by omega) r hr]
          unfold Model.sv
          simp only [if_neg (show ¬ n + j < n by omega), if_pos (show n + j < n + (j + 1) by omega),
            show n + j - n = j by omega]
        obtain ⟨t, ht, htw⟩ := copy_tgt hv hj (k := n + j) (by omega) hw
        have hv' := valid_mv hv hj ht (fun _ => htw)
        exact hmin _ hv' (unique_mv hu) (meas2_mv hv hv' hj (Or.inl hnp1))
      · have q0 := hnf.ord j (by omega) hnp
        have q1 := hnf.ord (j + 1) hj hnp1
        have n0 := hv.not_eq j (by omega)
        have n1 := hv.not_eq (j + 1) hj
        have : M.op j = 0 ∧ M.op (j + 1) = 1 ∨ M.op (j + 1) < M.op j := by omega
        rcases this with h | h
        · exact hc (Or.inr ⟨e1, Or.inr ⟨e2, h⟩⟩)
        · apply hx
          unfold lexKey
          exact lex3 _ _ _ _ _ _ _ (hK _ _ h4 o1) o1 (Or.inr ⟨e1.symm, Or.inr ⟨e2.symm, h⟩⟩)
    · apply hx
      unfold lexKey
      exact lex3 _ _ _ _ _ _ _ (hK _ _ h4 o1) o1 (Or.inr ⟨e1.symm, Or.inl e2⟩)
  · apply hx
    unfold lexKey
    exact lex3 _ _ _ _ _ _ _ (hK _ _ h4 o1) o1 (Or.inl e1)

lemma exists_nf_unique {n s : ℕ} {g : ℕ → Bool} {R : ℕ → Prop}
    (h : ∃ M, Valid n s g R M ∧ UniqueNot s M) :
    ∃ M, Valid n s g R M ∧ UniqueNot s M ∧ NF n s M ∧ LexNF n s M := by
  classical
  have hex : ∃ m, ∃ M, Valid n s g R M ∧ UniqueNot s M ∧ meas2 n s M = m := by
    obtain ⟨M, h1, h2⟩ := h
    exact ⟨_, M, h1, h2, rfl⟩
  obtain ⟨M, hv, hu, hm⟩ := Nat.find_spec hex
  have hmin : ∀ M', Valid n s g R M' → UniqueNot s M' →
      meas2 n s M' < meas2 n s M → False := by
    intro M' h1 h2 h3
    exact Nat.find_min hex (hm ▸ h3) ⟨M', h1, h2, rfl⟩
  exact ⟨M, hv, hu, nf_of_min_unique hv hu hmin, lex_of_min_unique hv hu hmin⟩

open PEqualNP.CircuitLowerBounds

lemma code_op_not {n j : ℕ} {g : Gate} (h : (code n g j).1 = 3) : g.op = .not := by
  rcases g with ⟨op, ins⟩
  cases op <;> cases ins with
  | nil => simp [code] at h
  | cons a ins => cases ins <;> simp_all [code]

lemma gateAt_not_lt {C : Circuit} {j : ℕ} (h : (gateAt C j).op = .not) :
    j < C.gates.length := by
  by_contra hj
  rw [gateAt, List.getD_eq_default _ _ (by omega)] at h
  cases h

lemma unique_ofCirc (n s : ℕ) (C : Circuit)
    (h : ∀ i j : Fin C.gates.length, (C.gates.get i).op = .not →
      (C.gates.get j).op = .not → i = j) : UniqueNot s (ofCirc n s C) := by
  intro i hi j hj hi3 hj3
  have hip : (gateAt C i).op = .not := code_op_not hi3
  have hjp : (gateAt C j).op = .not := code_op_not hj3
  have hil := gateAt_not_lt hip
  have hjl := gateAt_not_lt hjp
  have hie : C.gates.get ⟨i, hil⟩ = gateAt C i := by
    simpa [gateAt] using (List.getElem_eq_getD (l := C.gates) (i := i) (h := hil) ⟨.and, []⟩)
  have hje : C.gates.get ⟨j, hjl⟩ = gateAt C j := by
    simpa [gateAt] using (List.getElem_eq_getD (l := C.gates) (i := j) (h := hjl) ⟨.and, []⟩)
  exact congrArg Fin.val (h ⟨i, hil⟩ ⟨j, hjl⟩ (hie.symm ▸ hip) (hje.symm ▸ hjp))

def modelGate (M : Model) (j : ℕ) : Gate :=
  if M.op j = 0 then ⟨.and, [M.s1 j, M.s2 j]⟩
  else if M.op j = 1 then ⟨.or, [M.s1 j, M.s2 j]⟩
  else if M.op j = 3 then ⟨.not, [M.s1 j]⟩ else ⟨.and, []⟩

def modelCircuit (s : ℕ) (M : Model) : Circuit :=
  ⟨(List.range s).map (modelGate M), M.so⟩

lemma modelGate_eval (M : Model) (j : ℕ) (S : ℕ → Bool) :
    (modelGate M j).op.eval ((modelGate M j).inputs.map S) =
      gfun (M.op j) (S (M.s1 j)) (S (M.s2 j)) := by
  unfold modelGate gfun
  split_ifs <;> simp [GateOp.eval]

lemma modelCircuit_length (s : ℕ) (M : Model) : (modelCircuit s M).gates.length = s := by
  simp [modelCircuit]

lemma modelCircuit_gate {s j : ℕ} (M : Model) (hj : j < s) :
    gateAt (modelCircuit s M) j = modelGate M j := by
  unfold gateAt
  rw [List.getD_eq_getElem _ _ (by simpa [modelCircuit] using hj)]
  simp [modelCircuit]

lemma modelCircuit_mono {s : ℕ} {M : Model} (hn : ∀ j < s, M.op j ≠ 3) :
    ∀ g ∈ (modelCircuit s M).gates,
      (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hg
  have hj' := List.mem_range.mp hj
  have hnot := hn j hj'
  simp only [modelGate]
  split_ifs <;> simp_all

open PEqualNP.MetaComplexity

lemma modelCircuit_wire {n s : ℕ} {g : ℕ → Bool} {R : ℕ → Prop} {M : Model}
    (hv : Valid n s g R M) {r : ℕ} (hr : R r) :
    ∀ j < s, ((modelCircuit s M).wires (xr n r)).getD (n + j) false = M.w j r := by
  intro j
  induction j using Nat.strong_induction_on with
  | ind j ih =>
    intro hj
    obtain ⟨hgate, hpre⟩ := wire_gate (modelCircuit s M) (xr n r) j
      (by simpa only [modelCircuit_length] using hj)
    rw [xr_length, modelCircuit_gate M hj] at hgate
    have hsource : ∀ k,
        (wiresFrom ((modelCircuit s M).gates.take j) (xr n r)).getD k false = M.sv n j k r := by
      intro k
      rw [hpre k, xr_length]
      by_cases hkn : k < n
      · rw [if_pos (by omega), Model.sv, if_pos hkn]
        rw [wires_eq, getD_wiresFrom _ _ _ (by simpa only [xr_length] using hkn), xr_getD n r k hkn]
      · by_cases hkj : k < n + j
        · rw [if_pos hkj, Model.sv, if_neg hkn, if_pos hkj]
          have he : n + (k - n) = k := by omega
          simpa only [he] using ih (k - n) (by omega) (by omega)
        · simp [hkj, Model.sv, hkn]
    rw [hv.w_eq j hj r hr, ← modelGate_eval M j (fun k => M.sv n j k r)]
    simpa only [hsource] using hgate

lemma modelCircuit_eval {n s : ℕ} {g : ℕ → Bool} {R : ℕ → Prop} {M : Model}
    (hv : Valid n s g R M) {r : ℕ} (hr : R r) :
    (modelCircuit s M).eval (xr n r) = g r := by
  rw [← hv.out_eq r hr]
  change ((modelCircuit s M).wires (xr n r)).getD M.so false = M.sv n s M.so r
  by_cases hkn : M.so < n
  · rw [Model.sv, if_pos hkn]
    rw [wires_eq, getD_wiresFrom _ _ _ (by simpa only [xr_length] using hkn), xr_getD n r _ hkn]
  · by_cases hks : M.so < n + s
    · rw [Model.sv, if_neg hkn, if_pos hks]
      have he : n + (M.so - n) = M.so := by omega
      simpa only [he] using modelCircuit_wire hv hr (M.so - n) (by omega)
    · rw [List.getD_eq_default _ _ (by rw [wires_length, xr_length, modelCircuit_length]; omega)]
      simp [Model.sv, hkn, hks]

def inputRow : (n : ℕ) → (Fin n → Bool) → ℕ
  | 0, _ => 0
  | n + 1, x => Nat.bit (x 0) (inputRow n (fun i => x i.succ))

lemma inputRow_bit : ∀ (n : ℕ) (x : Fin n → Bool) (i : Fin n),
    (inputRow n x).testBit i = x i := by
  intro n
  induction n with
  | zero => intro x i; exact Fin.elim0 i
  | succ n ih =>
    intro x i
    refine Fin.cases ?_ (fun i => ?_) i
    · simp [inputRow, Nat.testBit_bit_zero]
    · simpa only [inputRow, Fin.val_succ, Nat.testBit_bit_succ] using ih (fun i => x i.succ) i

lemma inputRow_lt : ∀ (n : ℕ) (x : Fin n → Bool), inputRow n x < 2 ^ n := by
  intro n
  induction n with
  | zero => intro x; simp [inputRow]
  | succ n ih =>
    intro x
    have h := ih (fun i => x i.succ)
    simp only [inputRow, Nat.bit_val, pow_succ]
    have hb : (x 0).toNat ≤ 1 := by cases x 0 <;> decide
    omega

lemma xr_inputRow (n : ℕ) (x : Fin n → Bool) : xr n (inputRow n x) = List.ofFn x := by
  unfold xr
  congr 1
  funext i
  exact inputRow_bit n x i

lemma modelCircuit_eval_all {n s : ℕ} {f : (Fin n → Bool) → Bool} {M : Model}
    (hv : Valid n s (rowFun n f) (fun r => r < 2 ^ n) M) :
    ∀ x : Fin n → Bool, (modelCircuit s M).eval (List.ofFn x) = f x := by
  intro x
  have h := modelCircuit_eval hv (inputRow_lt n x)
  rw [xr_inputRow] at h
  have he : (fun i : Fin n => (inputRow n x).testBit i) = x := by
    funext i; exact inputRow_bit n x i
  simpa only [rowFun, he] using h

lemma zero_not_reconstruction {n s : ℕ} {f : (Fin n → Bool) → Bool} {M : Model}
    (hv : Valid n s (rowFun n f) (fun r => r < 2 ^ n) M)
    (hn : ∀ j < s, M.op j ≠ 3) :
    ∃ (gates : List Gate) (o : ℕ),
      (∀ gate ∈ gates, (gate.op = .and ∨ gate.op = .or) ∧ gate.inputs.length ≤ 2) ∧
      gates.length = s ∧ ∀ x : Fin n → Bool, Circuit.eval ⟨gates, o⟩ (List.ofFn x) = f x := by
  exact ⟨(modelCircuit s M).gates, (modelCircuit s M).output, modelCircuit_mono hn,
    modelCircuit_length s M, modelCircuit_eval_all hv⟩

def fOneNot (n s : ℕ) : List (List ℕ) :=
  [(List.range s).map fun j => P (ix n s 0 j 3)] ++
    (List.range s).flatMap fun j => (List.range j).map fun i =>
      [Q (ix n s 0 i 3), Q (ix n s 0 j 3)]

lemma fOneNot_sat {n s : ℕ} {M : Model} (hu : UniqueNot s M)
    (hex : ∃ j < s, M.op j = 3) :
    ∀ c ∈ fOneNot n s, ClauseSat (val n s M) c := by
  have hw : 3 < wd n s := by
    obtain ⟨j, hj, _⟩ := hex
    have hp : 0 < 2 ^ n := pow_pos (by omega) _
    unfold wd
    omega
  intro c hc
  rcases List.mem_append.mp hc with hc | hc
  · have hc' : c = (List.range s).map (fun j => P (ix n s 0 j 3)) := by simpa using hc
    subst c
    obtain ⟨j, hj, hj3⟩ := hex
    refine cs_of_mem (List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩) ?_
    rw [litVal_P, v_op M (by omega) hw, hj3]
    decide
  · simp only [List.mem_flatMap, List.mem_map, List.mem_range] at hc
    obtain ⟨j, hj, i, hi, rfl⟩ := hc
    by_cases hi3 : M.op i = 3
    · have hj3 : M.op j ≠ 3 := by intro hj3; have := hu i (by omega) j hj hi3 hj3; omega
      refine cs_of_mem (l := Q (ix n s 0 j 3)) (by simp) ?_
      rw [litVal_Q, v_op M (by omega) hw]
      simpa using hj3
    · refine cs_of_mem (l := Q (ix n s 0 i 3)) (by simp) ?_
      rw [litVal_Q, v_op M (by omega) hw]
      simpa using hi3

lemma normalize_or_replacement (n : ℕ) (C : Circuit) (f : (Fin n → Bool) → Bool)
    (hC : FanInTwo C)
    (hnot : ∀ i j : Fin C.gates.length, (C.gates.get i).op = .not →
      (C.gates.get j).op = .not → i = j)
    (hev : ∀ x : Fin n → Bool, C.eval (List.ofFn x) = f x) :
    (∃ (gates : List Gate) (o : ℕ),
      (∀ gate ∈ gates, (gate.op = .and ∨ gate.op = .or) ∧ gate.inputs.length ≤ 2) ∧
      gates.length = C.gates.length ∧
      ∀ x : Fin n → Bool, Circuit.eval ⟨gates, o⟩ (List.ofFn x) = f x) ∨
    ∃ M, Valid n C.gates.length (rowFun n f) (fun r => r < 2 ^ n) M ∧
      UniqueNot C.gates.length M ∧ NF n C.gates.length M ∧ LexNF n C.gates.length M ∧
      ∃ j < C.gates.length, M.op j = 3 := by
  have hv := valid_ofCirc n C.gates.length (rowFun n f) (fun r => r < 2 ^ n) C hC
    (Nat.le_refl _) (fun r _ => hev (fun i => r.testBit i))
  obtain ⟨M, hM, hu, hnf, hlex⟩ := exists_nf_unique ⟨_, hv, unique_ofCirc n C.gates.length C hnot⟩
  by_cases hex : ∃ j < C.gates.length, M.op j = 3
  · exact Or.inr ⟨M, hM, hu, hnf, hlex, hex⟩
  · left
    exact zero_not_reconstruction hM (fun j hj h3 => hex ⟨j, hj, h3⟩)

lemma one_not_nf_sat {n s : ℕ} {g : ℕ → Bool} {rows : List ℕ} {M : Model}
    (hrows : ∀ r ∈ rows, r < 2 ^ n) (hv : Valid n s g (· ∈ rows) M)
    (hu : UniqueNot s M) (hn : NF n s M) (hl : LexNF n s M)
    (hex : ∃ j < s, M.op j = 3) : FormulaSat (enc2 n s g rows ++ fOneNot n s) := by
  refine ⟨val n s M, ?_⟩
  intro c hc
  rcases List.mem_append.mp hc with hc | hc
  · exact enc2_sat hrows hv hn hl c hc
  · exact fOneNot_sat hu hex c hc

lemma prefix_endpoints {n s : ℕ} {g : ℕ → Bool} {R : ℕ → Prop} {M : Model}
    (hv : Valid n s g R M) (hn : NF n s M) (hzero : R 0) (hone : R (2 ^ n - 1)) :
    ∀ j < s, (∀ i ≤ j, M.op i ≠ 3) →
      M.w j (2 ^ n - 1) = true ∧ (¬ M.pad n j → M.w j 0 = false) := by
  intro j
  induction j using Nat.strong_induction_on with
  | ind j ih =>
    intro hj hnot
    by_cases hp : M.pad n j
    · exact ⟨pad_w hv hj hp hone, fun hnp => False.elim (hnp hp)⟩
    have hs : ∀ k, k < n + j →
        (∀ i < j, M.pad n i → k ≠ n + i) →
        M.sv n j k (2 ^ n - 1) = true ∧ M.sv n j k 0 = false := by
      intro k hk hkp
      by_cases hkn : k < n
      · simp [Model.sv, hkn, Nat.testBit_two_pow_sub_one]
      · have hkj : k - n < j := by omega
        have hi := ih (k - n) hkj (by omega) (fun i hij => hnot i (by omega))
        have hnp : ¬ M.pad n (k - n) := by
          intro hpad
          exact hkp (k - n) hkj hpad (by omega)
        simpa only [Model.sv, if_neg hkn, if_pos hk] using And.intro hi.1 (hi.2 hnp)
    have hf := hn.noF j hj hp
    have hs1 := hs (M.s1 j) (by have := hv.s1_le j hj; omega)
      (fun i hi hpad => (hn.noPadRd j hj i hi hpad).1)
    have hs2 := hs (M.s2 j) (by have := hv.s2_le j hj; omega)
      (fun i hi hpad => (hn.noPadRd j hj i hi hpad).2)
    have ho : M.op j = 0 ∨ M.op j = 1 := by
      have := hv.op_lt j hj
      have := hnot j (Nat.le_refl j)
      have htwo : M.op j ≠ 2 := fun h => hp (hn.padOp j hj h)
      omega
    constructor
    · rw [hv.w_eq j hj (2 ^ n - 1) hone]
      rcases ho with ho | ho <;> simp [gfun, ho, hs1.1, hs2.1]
    · intro _
      rw [hv.w_eq j hj 0 hzero]
      rcases ho with ho | ho <;> simp [gfun, ho, hs1.2, hs2.2]

lemma before_not_endpoints {n s k : ℕ} {g : ℕ → Bool} {R : ℕ → Prop} {M : Model}
    (hv : Valid n s g R M) (hn : NF n s M) (hu : UniqueNot s M)
    (hzero : R 0) (hone : R (2 ^ n - 1)) (hk : k < s) (hnot : M.op k = 3)
    (j : ℕ) (hj : j < k) :
    M.w j (2 ^ n - 1) = true ∧ (¬ M.pad n j → M.w j 0 = false) := by
  apply prefix_endpoints hv hn hzero hone j (by omega)
  intro i hij hi3
  have := hu i (by omega) k hk hi3 hnot
  omega

def fPrefixEndpoints (n s k : ℕ) : List (List ℕ) :=
  (List.range k).flatMap fun j =>
    [[P (ix n s 3 j (2 ^ n - 1))], [P (ix n s 7 j 0), Q (ix n s 3 j 0)]]

lemma prefix_formula_sat {n s k : ℕ} {g : ℕ → Bool} {R : ℕ → Prop} {M : Model}
    (hv : Valid n s g R M) (hn : NF n s M) (hu : UniqueNot s M)
    (hzero : R 0) (hone : R (2 ^ n - 1)) (hk : k < s) (hnot : M.op k = 3) :
    ∀ c ∈ fPrefixEndpoints n s k, ClauseSat (val n s M) c := by
  intro c hc
  simp only [fPrefixEndpoints, List.mem_flatMap, List.mem_range, List.mem_cons,
    List.not_mem_nil, or_false] at hc
  obtain ⟨j, hj, hc⟩ := hc
  have he := before_not_endpoints hv hn hu hzero hone hk hnot j hj
  have hw : 2 ^ n - 1 < wd n s := wd_lt2 (Nat.sub_lt (Nat.two_pow_pos n) (by decide))
  have hz : 0 < wd n s := Nat.succ_pos _
  rcases hc with rfl | rfl
  · refine cs_of_mem (l := P (ix n s 3 j (2 ^ n - 1))) (by simp) ?_
    rw [litVal_P, v_w M (by omega) hw]
    exact he.1
  · by_cases hp : M.pad n j
    · refine cs_of_mem (l := P (ix n s 7 j 0)) (by simp) ?_
      rw [litVal_P, v_pad M (by omega)]
      simpa using hp
    · refine cs_of_mem (l := Q (ix n s 3 j 0)) (by simp) ?_
      rw [litVal_Q, v_w M (by omega) hz, he.2 hp]
      rfl


end NFCount


section SignedSearchBase

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

def canonical (w : BitVec width) : BitVec width :=
  if w.toNat ≤ (~~~w).toNat then w else ~~~w

lemma canonical_of_msb_false {w : BitVec width} (h : w.msb = false) :
    canonical w = w := by
  have bound := BitVec.msb_eq_false_iff_two_mul_lt.mp h
  have order : w.toNat ≤ (~~~w).toNat := by
    rw [BitVec.toNat_not]
    omega
  simp only [canonical, if_pos order]

lemma canonical_msb_false (w : BitVec width) : (canonical w).msb = false := by
  unfold canonical
  split_ifs with order
  · apply BitVec.msb_eq_false_iff_two_mul_lt.mpr
    rw [BitVec.toNat_not] at order
    have bound := w.isLt
    omega
  · apply BitVec.msb_eq_false_iff_two_mul_lt.mpr
    rw [BitVec.toNat_not] at order ⊢
    have bound := w.isLt
    omega

lemma ops_msb_false {a b w : BitVec width} (ha : a.msb = false)
    (hb : b.msb = false) (hw : w ∈ ops a b) : w.msb = false := by
  simp only [ops, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl <;> simp [ha, hb]

lemma canonical_ops {a b : BitVec width} (ha : a.msb = false)
    (hb : b.msb = false) : (ops a b).map canonical = ops a b := by
  have one (w : BitVec width) (hw : w ∈ ops a b) : canonical w = w :=
    canonical_of_msb_false (ops_msb_false ha hb hw)
  simpa only [List.map_id'] using List.map_congr_left one

open PEqualNP.CircuitLowerBounds

def holds (av : Finset (BitVec width)) (z : (BitVec width)) : Prop :=
  z = 0 ∨ z = ~~~0 ∨ ∃ a ∈ av, z = a ∨ z = ~~~a

lemma holds_insert {av : Finset (BitVec width)} {z a : (BitVec width)} (h : holds av z) : holds (insert a av) z := by
  rcases h with h|h|⟨u,hu,he⟩
  · exact .inl h
  · exact .inr (.inl h)
  · exact .inr (.inr ⟨u,Finset.mem_insert_of_mem hu,he⟩)

lemma holds_not {av : Finset (BitVec width)} {z : (BitVec width)} (h : holds av z) : holds av (~~~z) := by
  rcases h with rfl|rfl|⟨a,ha,he⟩
  · exact .inr (.inl rfl)
  · exact .inl BitVec.not_not
  · rcases he with he|he <;> rw [he]
    · exact .inr (.inr ⟨a, ha, .inr rfl⟩)
    · exact .inr (.inr ⟨a, ha, .inl BitVec.not_not⟩)

def reachable (av : Finset (BitVec width)) (z : (BitVec width)) : Prop :=
  holds av z ∨ ∃ a ∈ av, ∃ b ∈ av, a ≠ b ∧ ∃ w ∈ basicOps a b, holds (insert w av) z

lemma reachable_not {av : Finset (BitVec width)} {z : (BitVec width)} (h : reachable av z) : reachable av (~~~z) := by
  rcases h with h|⟨a,ha,b,hb,ne,w,hop,hw⟩
  · exact .inl (holds_not h)
  · exact .inr ⟨a,ha,b,hb,ne,w,hop,holds_not hw⟩

set_option maxRecDepth 5000 in
lemma and_reach {av : Finset (BitVec width)} {x y : (BitVec width)} (hx : holds av x) (hy : holds av y) :
    reachable av (x &&& y) := by
  have const : holds av (0 : (BitVec width)) := .inl rfl
  have oldx := hx
  rcases hx with rfl|rfl|⟨a,ha,ea⟩
  · rw [show (0 : (BitVec width)) &&& y = 0 from BitVec.zero_and]; exact .inl const
  · have he : (~~~(0 : BitVec width)) &&& y = y := by
      apply BitVec.eq_of_getLsbD_eq
      intro i
      simp
    rw [he]
    exact .inl hy
  rcases hy with rfl|rfl|⟨b,hb,eb⟩
  · rw [show x &&& (0 : (BitVec width)) = 0 from BitVec.and_zero]; exact .inl const
  · have he : x &&& ~~~(0 : BitVec width) = x := by
      apply BitVec.eq_of_getLsbD_eq
      intro i
      simp
    rw [he]
    exact .inl oldx
  by_cases h : a = b
  · subst b
    rcases ea with ea|ea <;> rcases eb with eb|eb <;> rw [ea,eb] <;>
      simp only [BitVec.and_self, BitVec.and_not_self, BitVec.not_and_self] <;>
      first | exact .inl const | exact .inl (.inr (.inr ⟨a,ha,.inl rfl⟩)) |
        exact .inl (.inr (.inr ⟨a,ha,.inr rfl⟩))
  have add (w : (BitVec width)) (hw : w ∈ basicOps a b) (z : (BitVec width)) (hz : z = w ∨ z = ~~~w) :
      reachable av z :=
    .inr ⟨a,ha,b,hb,h,w,hw,.inr (.inr ⟨w,Finset.mem_insert_self ..,hz⟩)⟩
  rcases ea with ea|ea <;> rcases eb with eb|eb <;> rw [ea,eb]
  · exact add _ (by simp [basicOps,ops] : a &&& b ∈ basicOps a b) _ (.inl rfl)
  · exact add _ (by simp [basicOps,ops] : a &&& ~~~b ∈ basicOps a b) _ (.inl rfl)
  · exact add _ (by simp [basicOps,ops] : b &&& ~~~a ∈ basicOps a b) _ (.inl (BitVec.and_comm ..))
  · exact add _ (by simp [basicOps,ops] : a ||| b ∈ basicOps a b) _ (.inr BitVec.not_or.symm)

lemma or_reach {av : Finset (BitVec width)} {x y : (BitVec width)} (hx : holds av x) (hy : holds av y) :
    reachable av (x ||| y) := by
  simpa only [BitVec.not_and, BitVec.not_not] using reachable_not (and_reach (holds_not hx) (holds_not hy))

private def bit (k : Fin width) (z : (BitVec width)) : Bool := z[k.val]
private def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private lemma read_bit (w : List (BitVec width)) (i : ℕ) (k : Fin width) :
    (w.map (bit k)).getD i false = bit k (w.getD i 0) := by
  by_cases h : i < w.length
  · simp [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem h]
  · simp [List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_eq_none (Nat.le_of_not_gt h), bit]

def legal (g : Gate) : Prop := (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2

def action (w : List (BitVec width)) (g : Gate) : (BitVec width) := match g.op with
  | .not => ~~~(g.inputs.head?.map (fun i => w.getD i 0)).getD 0
  | .and => (g.inputs.map fun i => w.getD i 0).foldr (· &&& ·) (~~~0)
  | .or => (g.inputs.map fun i => w.getD i 0).foldr (· ||| ·) 0
  | _ => 0

lemma evalAnd (xs : List Bool) : GateOp.and.eval xs = xs.all id := rfl
lemma evalOr (xs : List Bool) : GateOp.or.eval xs = xs.any id := rfl
lemma evalNot (xs : List Bool) : GateOp.not.eval xs = !(xs.headD false) := rfl

set_option maxRecDepth 5000 in
lemma action_spec (w : List (BitVec width)) (g : Gate) (hg : legal g) (k : Fin width) :
    step (w.map (bit k)) g = (w ++ [action w g]).map (bit k) := by
  obtain ⟨op,args⟩ := g
  obtain ⟨hop,cap⟩ := hg
  change op = .and ∨ op = .or ∨ op = .not at hop
  change args.length ≤ 2 at cap
  rcases args with _|⟨i,_|⟨j,_|⟨u,tail⟩⟩⟩ <;> try simp at cap
  all_goals have bit0 : (0 : (BitVec width))[k.val] = false := by change (0 : BitVec width)[k.val] = false; simp
  all_goals rcases hop with rfl|rfl|rfl <;>
    simp only [step, List.map_cons,List.map_nil,read_bit,List.map_append] <;>
    simp only [action, evalAnd, evalOr, evalNot, List.foldr_cons,List.foldr_nil,List.head?_cons,List.head?_nil,
      List.headD_cons,List.headD_nil,Option.map_some,Option.map_none,Option.getD_some,Option.getD_none,
      List.all_cons,List.all_nil,List.any_cons,List.any_nil,List.map_cons,List.map_nil,id_eq,
      Bool.and_true,Bool.or_false, bit,BitVec.getElem_and,BitVec.getElem_or,BitVec.getElem_not,
      BitVec.getElem_zero,bit0,Bool.not_false] <;> rfl

def isBinary (g : Gate) : Bool := match g.op with
  | .not => false
  | _ => true
def binaryCost (gs : List Gate) := (gs.filter isBinary).length

lemma available_read {av : Finset (BitVec width)} {w : List (BitVec width)} (hw : ∀ u ∈ w, holds av u) (i : ℕ) :
    holds av (w.getD i 0) := by
  by_cases h : i < w.length
  · exact hw _ (by simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h])
  · rw [List.getD_eq_default _ _ (Nat.le_of_not_gt h)]
    exact .inl rfl

set_option maxRecDepth 5000 in
lemma gate_reach (w : List (BitVec width)) (av : Finset (BitVec width)) (hw : ∀ u ∈ w, holds av u)
    (g : Gate) (hg : legal g) :
    if isBinary g then reachable av (action w g) else holds av (action w g) := by
  obtain ⟨op,args⟩ := g
  obtain ⟨hop,cap⟩ := hg
  change op = .and ∨ op = .or ∨ op = .not at hop
  change args.length ≤ 2 at cap
  rcases args with _|⟨i,_|⟨j,_|⟨u,tail⟩⟩⟩ <;> try simp at cap
  all_goals rcases hop with rfl|rfl|rfl <;> simp only [isBinary,Bool.false_eq_true,ite_false,ite_true,
    action,List.head?_nil,List.head?_cons,List.map_nil,List.map_cons,List.foldr_nil,List.foldr_cons,
    Option.map_none,Option.map_some,Option.getD_none,Option.getD_some,
    show ∀ x : (BitVec width), x ||| (0 : (BitVec width)) = x from fun x => BitVec.or_zero,
    show ∀ x : (BitVec width), x &&& ~~~0 = x from fun x => by simp]
  all_goals first
    | exact .inl (.inl rfl)
    | exact .inl (.inr (.inl rfl))
    | exact .inr (.inl rfl)
    | exact .inl (available_read hw _)
    | exact holds_not (available_read hw _)
    | exact and_reach (available_read hw _) (available_read hw _)
    | exact or_reach (available_read hw _) (available_read hw _)

set_option maxRecDepth 4000 in
lemma compile {goal : BitVec width} (nonzero : goal ≠ 0) (nonones : goal ≠ ~~~0) (gs : List Gate) (out : ℕ) (hg : ∀ g ∈ gs, legal g)
    (w : List (BitVec width)) (av : Finset (BitVec width)) (hw : ∀ u ∈ w, holds av u)
    (he : ∀ k, (gs.foldl step (w.map (bit k))).getD out false = bit k goal) :
    ∃ t, (t = goal ∨ t = ~~~goal) ∧ build basicOps t (binaryCost gs) av := by
  induction gs generalizing w av with
  | nil =>
    have hv : w.getD out 0 = goal := by
      apply BitVec.eq_of_getElem_eq
      intro i hi
      simpa only [List.foldl_nil, read_bit, bit] using he ⟨i,hi⟩
    have h := hv ▸ available_read hw out
    rcases h with zero|ones|⟨t,ht,eq|eq⟩
    · exact False.elim (nonzero zero)
    · exact False.elim (nonones ones)
    · exact ⟨t, .inl eq.symm, ht⟩
    · exact ⟨t, .inr (by rw [eq, BitVec.not_not]), ht⟩
  | cons g gs ih =>
    let z := action w g
    have stepOK := action_spec w g (hg g (by simp))
    have nextEval : ∀ k, (gs.foldl step ((w ++ [z]).map (bit k))).getD out false = bit k goal := by
      intro k; simpa only [List.foldl_cons, stepOK] using he k
    have tail := ih (fun t ht => hg t (by simp [ht])) (w ++ [z])
    have cont (A : Finset (BitVec width)) (hold : ∀ u ∈ w, holds A u) (new : holds A z) :=
      tail A (by
        intro u hu
        rcases List.mem_append.mp hu with hu|hu
        · exact hold u hu
        · exact (List.mem_singleton.mp hu) ▸ new) nextEval
    have stepClass := gate_reach w av hw g (hg g (by simp))
    cases neg : isBinary g
    · simp only [neg,Bool.false_eq_true,ite_false] at stepClass
      simpa [binaryCost,neg] using cont av hw stepClass
    · simp only [neg,ite_true] at stepClass
      have len : binaryCost (g::gs) = binaryCost gs+1 := by simp [binaryCost,neg]
      rw [len]
      rcases stepClass with existing|⟨a,ha,b,hb,ne,new,op,rep⟩
      · obtain ⟨t,ht,run⟩ := cont av hw existing
        exact ⟨t,ht,Or.inl run⟩
      · obtain ⟨t,ht,run⟩ := cont (insert new av) (fun u hu => holds_insert (hw u hu)) rep
        exact ⟨t,ht,Or.inr ⟨a,ha,b,hb,ne,new,op,run⟩⟩

lemma bound_from_samples {inputCount budget : Nat} {goal : BitVec width}
    (nonzero : goal ≠ 0) (nonones : goal ≠ ~~~0)
    (target : (Fin inputCount → Bool) → Bool) (ins : List (BitVec width))
    (roots : Finset (BitVec width)) (represented : ∀ u ∈ ins, holds roots u)
    (inputLength : ins.length = inputCount)
    (row : ∀ j : Fin width,
      target (fun i => (ins.getD i.val 0)[j.val]) = goal[j.val])
    (rejection : ∀ z, z = goal ∨ z = ~~~goal →
      ¬ build basicOps z budget roots)
    (gs : List Gate) (out : Nat) (legalGates : ∀ g ∈ gs, legal g)
    (computes : ∀ x : Fin inputCount → Bool,
      Circuit.eval ⟨gs, out⟩ (List.ofFn x) = target x) :
    budget < binaryCost gs := by
  by_contra! low
  have evaluate (k : Fin width) :
      (gs.foldl step (ins.map (bit k))).getD out false = bit k goal := by
    let x (i : Fin inputCount) : Bool := bit k (ins.getD i.val 0)
    have same : List.ofFn x = ins.map (bit k) := by
      apply List.ext_getElem
      · simp [inputLength]
      · intro i hi hj
        have hlt : i < ins.length := by simpa using hj
        simp only [List.getElem_ofFn, List.getElem_map, x,
          List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt, Option.getD_some]
    change Circuit.eval ⟨gs, out⟩ (ins.map (bit k)) = bit k goal
    rw [← same, computes]
    exact row k
  obtain ⟨z, hz, run⟩ := compile nonzero nonones gs out legalGates ins roots
    represented evaluate
  have lift {a b : Nat} (h : a ≤ b) (hr : build basicOps z a roots) :
      build basicOps z b roots := by
    induction h with
    | refl => exact hr
    | step _ ih => exact Or.inl ih
  exact rejection z hz (lift low run)

lemma replace_from_samples {inputCount replacementSize : Nat} {goal : BitVec width}
    (nonzero : goal ≠ 0) (nonones : goal ≠ ~~~0)
    (target : (Fin inputCount → Bool) → Bool) (ins : List (BitVec width))
    (roots : Finset (BitVec width)) (represented : ∀ u ∈ ins, holds roots u)
    (inputLength : ins.length = inputCount)
    (row : ∀ j : Fin width,
      target (fun i => (ins.getD i.val 0)[j.val]) = goal[j.val])
    (rejection : ∀ z, z = goal ∨ z = ~~~goal →
      ¬ build basicOps z (replacementSize - 2) roots)
    (upper : ∃ (gs : List Gate) (out : Nat),
      (∀ g ∈ gs, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2) ∧
      gs.length = replacementSize ∧
      ∀ x : Fin inputCount → Bool, Circuit.eval ⟨gs, out⟩ (List.ofFn x) = target x)
    (gs : List Gate) (out : Nat) (legalGates : ∀ g ∈ gs, legal g)
    (computes : ∀ x : Fin inputCount → Bool,
      Circuit.eval ⟨gs, out⟩ (List.ofFn x) = target x) :
    ∃ (ds : List Gate) (newOut : Nat),
      (∀ g ∈ ds, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2) ∧
      ds.length ≤ gs.length ∧
      ∀ x : Fin inputCount → Bool, Circuit.eval ⟨ds, newOut⟩ (List.ofFn x) = target x := by
  by_cases present : ∃ g ∈ gs, g.op = .not
  · obtain ⟨g, member, op⟩ := present
    have cut : binaryCost gs < gs.length :=
      (List.length_filter_lt_length_iff_exists (p := isBinary)).mpr
        ⟨g, member, by simp [isBinary, op]⟩
    have lower := bound_from_samples nonzero nonones target ins roots represented inputLength row rejection
      gs out legalGates computes
    obtain ⟨ds, newOut, ok, size, evaluates⟩ := upper
    exact ⟨ds, newOut, ok, by omega, evaluates⟩
  · refine ⟨gs, out, ?_, le_rfl, computes⟩
    intro g member
    obtain ⟨op, arity⟩ := legalGates g member
    exact ⟨op.elim Or.inl (fun h => h.elim Or.inr
      (fun eq => (present ⟨g, member, eq⟩).elim)), arity⟩


namespace SearchKernel

open PEqualNP.Outside.L_meta_10760

variable {width : Nat}

def singles {α : Type} : List α → List (α × List α)
  | [] => []
  | a :: rest => (a, rest) :: (singles rest).map (fun (b, bs) => (b, a :: bs))

def pairs {α : Type} : List α → List (α × α × List α)
  | [] => []
  | a :: rest => (singles rest).map (fun (b, bs) => (a, b, bs)) ++
      (pairs rest).map (fun (b, c, bs) => (b, c, a :: bs))

set_option maxRecDepth 100000 in
lemma pick_one {α : Type} {a : α} {ws : List α} (h : a ∈ ws) :
    ∃ rest, (a, rest) ∈ singles ws ∧ ws.Perm (a :: rest) := by
  induction ws with
  | nil => simp at h
  | cons x xs ih =>
    rcases List.mem_cons.mp h with e | h
    · subst x; exact ⟨xs, by simp [singles], .refl _⟩
    · obtain ⟨rest, hm, hp⟩ := ih h
      refine ⟨x :: rest, List.mem_cons_of_mem _ (List.mem_map.mpr ⟨(a, rest), hm, rfl⟩), ?_⟩
      exact (hp.cons x).trans (.swap _ _ _)

set_option maxRecDepth 100000 in
lemma pick_two {α : Type} {a b : α} {ws : List α} (ha : a ∈ ws) (hb : b ∈ ws) (hne : a ≠ b) :
    ∃ rest, ((a, b, rest) ∈ pairs ws ∨ (b, a, rest) ∈ pairs ws) ∧
      ws.Perm (a :: b :: rest) := by
  induction ws with
  | nil => simp at ha
  | cons x xs ih =>
    rcases List.mem_cons.mp ha with h | ha
    · subst x
      obtain ⟨r, hm, hp⟩ := pick_one ((List.mem_cons.mp hb).resolve_left (Ne.symm hne))
      exact ⟨r, .inl (List.mem_append_left _ (List.mem_map.mpr ⟨(b, r), hm, rfl⟩)), hp.cons a⟩
    · rcases List.mem_cons.mp hb with h | hb
      · subst x
        obtain ⟨r, hm, hp⟩ := pick_one (ws := xs) (a := a) (by assumption)
        exact ⟨r, .inr (List.mem_append_left _ (List.mem_map.mpr ⟨(a, r), hm, rfl⟩)),
          (hp.cons b).trans (.swap _ _ _)⟩
      · obtain ⟨r, hm, hp⟩ := ih ha hb
        refine ⟨x :: r, ?_,
          (hp.cons x).trans ((List.Perm.swap _ _ _).trans ((List.Perm.swap _ _ _).cons a))⟩
        rcases hm with hm | hm
        · exact .inl (List.mem_append_right _ (List.mem_map.mpr ⟨(a, b, r), hm, rfl⟩))
        · exact .inr (List.mem_append_right _ (List.mem_map.mpr ⟨(b, a, r), hm, rfl⟩))

lemma ops_swap (a b : (BitVec width)) : basicOps a b = basicOps b a := by
  ext z
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false]
  rw [BitVec.and_comm a b, BitVec.or_comm a b]
  tauto

def keepChoices (a b : (BitVec width)) (r : List (BitVec width)) : List (List (BitVec width)) := [r, a :: r, b :: r, a :: b :: r]

set_option maxRecDepth 100000 in
lemma recover_kept {ws r : List (BitVec width)} {a b : (BitVec width)} {needed : Finset (BitVec width)}
    (hp : ws.Perm (a :: b :: r)) (hn : ws.Nodup)
    (hs : ws.toFinset = insert a (insert b needed)) :
    ∃ kept ∈ keepChoices a b r, kept.Nodup ∧ kept.toFinset = needed := by
  have habr := hp.nodup_iff.mp hn
  have hbase : ws.toFinset = insert a (insert b r.toFinset) := by
    ext v
    simp [hp.mem_iff]
  have henne : ∀ v, v ∈ r ↔ v ∈ needed ∧ v ≠ a ∧ v ≠ b := by
    intro v
    have he : (v ∈ insert a (insert b r.toFinset)) ↔ v ∈ insert a (insert b needed) := by
      rw [← hbase, ← hs]
    simp only [Finset.mem_insert, List.mem_toFinset] at he
    simp only [List.nodup_cons, List.mem_cons, not_or] at habr
    grind
  by_cases ha : a ∈ needed <;> by_cases hb : b ∈ needed
  · refine ⟨a :: b :: r, by simp [keepChoices], habr, ?_⟩
    ext v; simp [henne]; grind
  · refine ⟨a :: r, by simp [keepChoices], ?_, ?_⟩
    · simp_all [List.nodup_cons]
    · ext v; simp [henne]; grind
  · refine ⟨b :: r, by simp [keepChoices], (List.nodup_cons.mp habr).2, ?_⟩
    ext v; simp [henne]; grind
  · refine ⟨r, by simp [keepChoices], (List.nodup_cons.mp (List.nodup_cons.mp habr).2).2, ?_⟩
    ext v; simp [henne]; grind

set_option maxRecDepth 100000 in
lemma singleton_list {goal : (BitVec width)} {ws : List (BitVec width)} (hn : ws.Nodup) (hs : ws.toFinset = {goal}) : ws = [goal] := by
  have hc := List.toFinset_card_of_nodup hn
  rw [hs] at hc
  cases ws with
  | nil => simp at hc
  | cons w ws =>
    cases ws with
    | nil => simpa using hs
    | cons => simp at hc

def rowClass (j : Fin width) (w : BitVec width) : BitVec width :=
  if w[j.val] then w else ~~~w

def survivors (goal : BitVec width) (j : Fin width) (ws : List (BitVec width)) : BitVec width :=
  ws.foldr (fun w r => rowClass j w &&& r) goal

def separates (goal : BitVec width) (rows : List (Fin width))
    (ws : List (BitVec width)) : Bool :=
  rows.all (fun j => goal[j.val] || (survivors goal j ws == 0))

lemma rowClass_bit (i j : Fin width) (w : BitVec width) :
    (rowClass j w)[i.val] = true ↔ w[i.val] = w[j.val] := by
  unfold rowClass
  split <;> simp_all

lemma survivors_bit (goal : BitVec width) (i j : Fin width) (ws : List (BitVec width)) :
    (survivors goal j ws)[i.val] = true ↔
      goal[i.val] = true ∧ ∀ w ∈ ws, w[i.val] = w[j.val] := by
  induction ws with
  | nil => simp [survivors]
  | cons w ws ih =>
    simp only [survivors, List.foldr_cons, BitVec.getElem_and, Bool.and_eq_true]
    change (rowClass j w)[i.val] = true ∧ (survivors goal j ws)[i.val] = true ↔ _
    rw [rowClass_bit, ih]
    simp only [List.mem_cons, forall_eq_or_imp]
    tauto

lemma ops_separate (i j : Fin width) (a b z : BitVec width) (hz : z ∈ basicOps a b)
    (hd : z[i.val] ≠ z[j.val]) : a[i.val] ≠ a[j.val] ∨ b[i.val] ≠ b[j.val] := by
  by_contra h
  push Not at h
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with rfl | rfl | rfl | rfl <;> apply hd <;>
    simp only [BitVec.getElem_and, BitVec.getElem_or, BitVec.getElem_not, h.1, h.2]

lemma separates_complete {goal g : BitVec width} (hg : g = goal ∨ g = ~~~goal)
    (rows : List (Fin width))
    {k : Nat} {ws : List (BitVec width)} (h : live basicOps g k ws.toFinset) :
    separates goal rows ws = true := by
  rw [separates, List.all_eq_true]
  intro j hj
  cases he : goal[j.val] with
  | true => simp [he]
  | false =>
    simp only [he, Bool.false_or, beq_iff_eq]
    apply BitVec.eq_of_getElem_eq
    intro i hi
    have zi : (0 : BitVec width)[i] = false := by simp
    rw [zi]
    cases hs : (survivors goal j ws)[i] with
    | false => rfl
    | true =>
      obtain ⟨hgoal, hagree⟩ := (survivors_bit goal ⟨i,hi⟩ j ws).mp hs
      have diff : g[i] ≠ g[j.val] := by
        rcases hg with rfl | rfl <;> simp [hgoal, he]
      obtain ⟨w, hw, hd⟩ := live_separates (fun w : BitVec width => w[i] ≠ w[j.val])
        diff (ops_separate ⟨i,hi⟩ j) h
      exact False.elim (hd (hagree w (List.mem_toFinset.mp hw)))


def dispatch (goal : BitVec width) (rows : List (Fin width)) (extra : Nat)
    (next : Nat → List (BitVec width) → Bool) (a b : BitVec width)
    (r : List (BitVec width)) : Bool :=
  (ops a b).any fun z => !(a :: b :: r).contains z &&
    (keepChoices a b r).any fun kept =>
    decide (kept.length ≤ extra + r.length) && separates goal rows (z :: kept) &&
      next (extra + r.length - kept.length) (z :: kept)

def optimized (goal : BitVec width) (rows : List (Fin width)) : Nat → Nat → List (BitVec width) → Bool
  | 0, _, ws => (ws == [goal] || ws == [~~~goal])
  | k + 1, extra, ws => (ws == [goal] || ws == [~~~goal]) ||
    (pairs ws).any (fun (a, b, r) => dispatch goal rows extra (optimized goal rows k) a b r)

lemma dispatch_complete {goal : BitVec width} {rows : List (Fin width)} {k extra : Nat} {a b z : BitVec width}
    {r kept : List (BitVec width)} (next : Nat → List (BitVec width) → Bool)
    (hz : z ∈ basicOps a b) (hnew : z ∉ a :: b :: r) (hk : kept ∈ keepChoices a b r)
    (he : extra + r.length = k) (hn : kept.length ≤ k)
    (hc : separates goal rows (z :: kept) = true)
    (ht : next (k - kept.length) (z :: kept) = true) :
    dispatch goal rows extra next a b r = true := by
  apply List.any_eq_true.mpr
  refine ⟨z, List.mem_toFinset.mp hz, ?_⟩
  rw [Bool.and_eq_true]
  refine ⟨by simpa using hnew, ?_⟩
  apply List.any_eq_true.mpr
  refine ⟨kept, hk, ?_⟩
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨⟨by omega, hc⟩, by simpa only [he] using ht⟩

set_option maxRecDepth 100000 in
lemma optimized_complete {goal g : (BitVec width)} (hg : g = goal ∨ g = ~~~goal) (rows : List (Fin width)) (n : ℕ) (ws : List (BitVec width)) (extra : ℕ) (hn : ws.Nodup)
    (room : extra + ws.length = n + 1) (h : live basicOps g n ws.toFinset) :
    optimized goal rows n extra ws = true := by
  induction n generalizing ws extra with
  | zero => rcases hg with rfl | rfl <;> simp [optimized, singleton_list hn h]
  | succ k ih =>
    rcases first_live h with done | ⟨a, ha, b, hb, hab, z, hz, hout, needed, hs, tail⟩
    · rcases hg with rfl | rfl <;> simp [optimized, singleton_list hn done]
    · obtain ⟨r, hm, hp⟩ := pick_two (List.mem_toFinset.mp ha) (List.mem_toFinset.mp hb) hab
      have go {a b : (BitVec width)} (perm : ws.Perm (a :: b :: r))
          (hset : ws.toFinset = insert a (insert b needed)) (hop : z ∈ basicOps a b) :
          dispatch goal rows extra (optimized goal rows k) a b r = true := by
        obtain ⟨kept, hk, hnk, hfin⟩ := recover_kept perm hn hset
        have hznew : z ∉ kept := by
          intro hu
          apply hout
          rw [hset]
          exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (hfin ▸ (List.mem_toFinset.mpr hu)))
        have hnd : (z :: kept).Nodup := List.nodup_cons.mpr ⟨hznew, hnk⟩
        have hl : live basicOps g k (z :: kept).toFinset := by
          simpa [hfin] using tail
        have hc := live_card hl
        rw [List.toFinset_card_of_nodup hnd, List.length_cons] at hc
        have len := perm.length_eq
        simp only [List.length_cons] at len
        apply dispatch_complete (k := k) (extra := extra) (optimized goal rows k) hop (by
          intro hz
          exact hout (List.mem_toFinset.mpr (perm.mem_iff.mpr hz))) hk (by omega) (by omega) (separates_complete hg rows hl)
        apply ih _ _ hnd _ hl
        simp; omega
      simp only [optimized, Bool.or_eq_true, List.any_eq_true]
      right
      rcases hm with direct | swap
      · exact ⟨(a, b, r), direct, go hp hs hz⟩
      · exact ⟨(b, a, r), swap, go (hp.trans (.swap _ _ _)) (by rw [hs, Finset.insert_comm]) (ops_swap a b ▸ hz)⟩

def falseRows (goal : BitVec width) : List (Fin width) :=
  (List.finRange width).filter (fun j => !goal[j.val])

def search (goal : BitVec width) (n : ℕ) (inputs : List (BitVec width)) : Bool :=
  let rows := falseRows goal
  inputs.sublists.any fun ws =>
    decide (ws.length ≤ n+1) && separates goal rows ws && optimized goal rows n (n+1-ws.length) ws

set_option maxRecDepth 100000 in
lemma search_complete {goal g : (BitVec width)} (hg : g = goal ∨ g = ~~~goal) (n : ℕ) (inputs : List (BitVec width))
    (hn : inputs.Nodup) (h : build basicOps g n inputs.toFinset) : search goal n inputs = true := by
  classical
  obtain ⟨s,hs,hl⟩ := compress h
  let ws := inputs.filter (· ∈ s)
  have eq : ws.toFinset = s := by
    ext w
    simp only [ws, List.mem_toFinset, List.mem_filter, decide_eq_true_eq, and_iff_right_iff_imp]
    exact fun hw => List.mem_toFinset.mp (hs hw)
  have hnd : ws.Nodup := hn.filter _
  have hl' : live basicOps g n ws.toFinset := eq.symm ▸ hl
  have sz := live_card hl'
  rw [List.toFinset_card_of_nodup hnd] at sz
  exact List.any_eq_true.mpr ⟨ws,List.mem_sublists.mpr (List.filter_sublist ..),
    by simp [sz, separates_complete hg (falseRows goal) hl', optimized_complete hg (falseRows goal) n ws _ hnd (by omega : n+1-ws.length+ws.length=n+1) hl']⟩

lemma no_build {goal g : BitVec width} (hg : g = goal ∨ g = ~~~goal)
    (n : Nat) (inputs : List (BitVec width)) (hn : inputs.Nodup)
    (rejected : search goal n inputs = false) :
    ¬ build basicOps g n inputs.toFinset := by
  intro h
  have found := search_complete hg n inputs hn h
  rw [rejected] at found
  contradiction

end SearchKernel

end SignedSearchBase




namespace PackedKeyWide

def packWords {w : Nat} : List (BitVec w) → Nat
  | [] => 1
  | a :: xs => packWords xs * 2 ^ (w + 1) + a.toNat

lemma packWords_pos {w : Nat} (xs : List (BitVec w)) : 0 < packWords xs := by
  induction xs with
  | nil => simp [packWords]
  | cons a xs ih =>
    have h := Nat.mul_pos ih (Nat.two_pow_pos (w + 1))
    simp only [packWords]
    omega

lemma base_ge_two (w : Nat) : 2 ≤ 2 ^ (w + 1) := by
  have h := Nat.two_pow_pos w
  simp only [pow_succ]
  omega

lemma packWords_cons_gt_one {w : Nat} (a : BitVec w) (xs : List (BitVec w)) :
    1 < packWords (a :: xs) := by
  have h := packWords_pos xs
  have hb := base_ge_two w
  have hm := Nat.mul_le_mul_right (2 ^ (w + 1)) h
  simp only [packWords, Nat.one_mul] at *
  omega

lemma packWords_inj {w : Nat} {xs ys : List (BitVec w)}
    (h : packWords xs = packWords ys) : xs = ys := by
  induction xs generalizing ys with
  | nil =>
    cases ys with
    | nil => rfl
    | cons a ys =>
      have hc := packWords_cons_gt_one a ys
      change 1 = packWords (a :: ys) at h
      omega
  | cons a xs ih =>
    cases ys with
    | nil =>
      have hc := packWords_cons_gt_one a xs
      change packWords (a :: xs) = 1 at h
      omega
    | cons b ys =>
      have ha0 := a.isLt
      have ha : a.toNat < 2 ^ (w + 1) := by rw [pow_succ]; omega
      have hb0 := b.isLt
      have hb : b.toNat < 2 ^ (w + 1) := by rw [pow_succ]; omega
      have hd := congrArg (fun v => v % 2 ^ (w + 1)) h
      simp only [packWords, Nat.add_mod, Nat.mul_mod_left, Nat.zero_add,
        Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at hd
      have hab : a = b := BitVec.eq_of_toNat_eq hd
      subst b
      have ht : packWords xs * 2 ^ (w + 1) = packWords ys * 2 ^ (w + 1) := by
        simp only [packWords] at h
        omega
      have he : packWords xs = packWords ys := Nat.eq_of_mul_eq_mul_right (Nat.two_pow_pos (w + 1)) ht
      exact congrArg (a :: ·) (ih he)

def packBudget : Nat → Nat → Nat
  | 0, p => 2 * p + 1
  | k + 1, p => 2 * packBudget k p

lemma packBudget_inj {k j p q : Nat} (h : packBudget k p = packBudget j q) : k = j ∧ p = q := by
  induction k generalizing j with
  | zero =>
    cases j with
    | zero => simp only [packBudget] at h; exact ⟨rfl, by omega⟩
    | succ j => simp only [packBudget] at h; omega
  | succ k ih =>
    cases j with
    | zero => simp only [packBudget] at h; omega
    | succ j =>
      have he : packBudget k p = packBudget j q := by simpa only [packBudget, Nat.mul_right_inj (by decide : 2 ≠ 0)] using h
      obtain ⟨rfl, rfl⟩ := ih he
      exact ⟨rfl, rfl⟩

def key {w : Nat} (k : Nat) (xs : List (BitVec w)) : Nat := packBudget k (packWords xs)

lemma key_inj {w : Nat} {k j : Nat} {xs ys : List (BitVec w)}
    (h : key k xs = key j ys) : k = j ∧ xs = ys := by
  obtain ⟨hkj, hxy⟩ := packBudget_inj h
  exact ⟨hkj, packWords_inj hxy⟩

end PackedKeyWide


namespace RawLaws

lemma empty_wf : (∅ : Std.TreeSet.Raw Nat compare).WF :=
  ⟨⟨⟨(∅ : Std.TreeSet Nat compare).inner.inner.wf⟩⟩⟩

lemma insert_wf {t : Std.TreeSet.Raw Nat compare} (h : t.WF) (a : Nat) : (t.insert a).WF :=
  ⟨⟨⟨h.out.out.out.insertIfNew!⟩⟩⟩

lemma contains_insert {t : Std.TreeSet.Raw Nat compare} (h : t.WF) (k a : Nat) :
    (t.insert k).contains a = (compare k a == .eq || t.contains a) := by
  exact Std.DTreeMap.Internal.Impl.contains_insertIfNew! h.out.out.out

end RawLaws

namespace Memo

variable {α κ : Type}

def plain (done : α → Bool) (children : Nat → α → List α) : Nat → α → Bool
  | 0, x => done x
  | k + 1, x => done x || (children k x).any (plain done children k)

def scan (next : α → κ → Bool × κ) : List α → κ → Bool × κ
  | [], cache => (false, cache)
  | x :: xs, cache =>
    match next x cache with
    | (true, cache') => (true, cache')
    | (false, cache') => scan next xs cache'

lemma scan_correct (Good : κ → Prop)
    (f : α → Bool) (next : α → κ → Bool × κ)
    (hnext : ∀ x cache, Good cache →
      (next x cache).1 = f x ∧ Good (next x cache).2)
    (xs : List α) (cache : κ) (hc : Good cache) :
    (scan next xs cache).1 = xs.any f ∧ Good (scan next xs cache).2 := by
  induction xs generalizing cache with
  | nil => exact ⟨rfl, hc⟩
  | cons x xs ih =>
    have hs := hnext x cache hc
    cases he : next x cache with
    | mk b cache' =>
      simp only [he] at hs
      cases b with
      | false =>
        have ht := ih cache' hs.2
        simpa only [scan, he, hs.1.symm, List.any_cons, Bool.false_or] using ht
      | true =>
        simp only [scan, he, hs.1.symm, List.any_cons, Bool.true_or]
        exact ⟨trivial, hs.2⟩

def search (hit : Nat → α → κ → Bool) (put : Nat → α → κ → κ) (done : α → Bool) (children : Nat → α → List α) :
    Nat → α → κ → Bool × κ
  | 0, x, cache =>
    if hit 0 x cache then (false, cache)
    else if done x then (true, cache)
    else (false, put 0 x cache)
  | k+1, x, cache =>
    if hit (k+1) x cache then (false, cache)
    else if done x then (true, cache)
    else match scan (search hit put done children k) (children k x) cache with
    | (true, cache') => (true, cache')
    | (false, cache') => (false, put (k+1) x cache')

lemma search_correct (hit : Nat → α → κ → Bool) (put : Nat → α → κ → κ)
    (done : α → Bool) (children : Nat → α → List α) (Good : κ → Prop)
    (hit_sound : ∀ k x cache, Good cache → hit k x cache = true → plain done children k x = false)
    (put_good : ∀ k x cache, Good cache → plain done children k x = false → Good (put k x cache))
    (k : Nat) (x : α) (cache : κ) (hc : Good cache) :
    (search hit put done children k x cache).1 = plain done children k x ∧
      Good (search hit put done children k x cache).2 := by
  induction k generalizing x cache with
  | zero =>
    by_cases hh : hit 0 x cache = true
    · simp only [search, hh, Bool.true_eq, ite_true, Prod.fst, Prod.snd]
      exact ⟨(hit_sound 0 x cache hc hh).symm, hc⟩
    · have hh' : hit 0 x cache = false := Bool.eq_false_iff.mpr hh
      by_cases hd : done x = true
      · simp [search, hh', hd, plain, hc]
      · have hd' : done x = false := Bool.eq_false_iff.mpr hd
        simp only [search, hh', Bool.false_eq_true, ite_false, hd', Prod.fst, Prod.snd,
          plain]
        exact ⟨trivial, put_good 0 x cache hc hd'⟩
  | succ k ih =>
    by_cases hh : hit (k+1) x cache = true
    · simp only [search, hh, Bool.true_eq, ite_true, Prod.fst, Prod.snd]
      exact ⟨(hit_sound (k+1) x cache hc hh).symm, hc⟩
    · have hh' : hit (k+1) x cache = false := Bool.eq_false_iff.mpr hh
      by_cases hd : done x = true
      · simp [search, hh', hd, plain, hc]
      · have hd' : done x = false := Bool.eq_false_iff.mpr hd
        have hs := scan_correct Good (plain done children k) (search hit put done children k)
          (fun y c h => ih y c h) (children k x) cache hc
        cases he : scan (search hit put done children k) (children k x) cache with
        | mk b cache' =>
          simp only [he] at hs
          cases b with
          | false =>
            have hx : plain done children (k+1) x = false := by
              simp only [plain, hd', Bool.false_or]
              exact hs.1.symm
            simp only [search, hh', Bool.false_eq_true, ite_false, hd', he, Prod.fst,
              Prod.snd]
            exact ⟨hx.symm, put_good (k+1) x cache' hs.2 hx⟩
          | true =>
            simp only [search, hh', Bool.false_eq_true, ite_false, hd', he, Prod.fst,
              Prod.snd]
            constructor
            · simp only [plain, hd', Bool.false_or]
              exact hs.1
            · exact hs.2

lemma search_run (hit : Nat → α → κ → Bool) (put : Nat → α → κ → κ)
    (done : α → Bool) (children : Nat → α → List α) (Good : κ → Prop)
    (hit_sound : ∀ k x cache, Good cache → hit k x cache = true → plain done children k x = false)
    (put_good : ∀ k x cache, Good cache → plain done children k x = false → Good (put k x cache))
    (k : Nat) (x : α) (cache : κ) (hc : Good cache) :
    (search hit put done children k x cache).1 = plain done children k x :=
  (search_correct hit put done children Good hit_sound put_good k x cache hc).1


variable {width : Nat}

abbrev States (width : Nat) := List (BitVec width)
abbrev TreeCache := Std.TreeSet.Raw Nat

def key (k : Nat) (ws : States width) : Nat :=
  PackedKeyWide.key k ws

def forceNat {β : Type} (n : Nat) (f : Nat → β) : β :=
  Nat.rec (f 0) (fun k _ => f (k+1)) n

lemma forceNat_eq {β : Type} (n : Nat) (f : Nat → β) : forceNat n f = f n := by
  cases n <;> rfl

def treeHit (k : Nat) (ws : States width) (cache : TreeCache) : Bool := forceNat (key k ws) (fun q => cache.contains q)
def treePut (k : Nat) (ws : States width) (cache : TreeCache) : TreeCache := forceNat (key k ws) (fun q => cache.insert q)

lemma key_inj {k j : Nat} {ws vs : States width} (h : key k ws = key j vs) : k = j ∧ ws = vs :=
  PackedKeyWide.key_inj h

def TreeGood (done : States width → Bool) (children : Nat → States width → List (States width)) (cache : TreeCache) : Prop :=
  cache.WF ∧ ∀ k ws, treeHit k ws cache = true → plain done children k ws = false

lemma tree_good_empty (done : States width → Bool) (children : Nat → States width → List (States width)) :
    TreeGood done children ∅ := by
  refine ⟨RawLaws.empty_wf, ?_⟩
  intro k ws h
  simp only [treeHit, forceNat_eq] at h
  change false = true at h
  contradiction

lemma tree_put_good {done : States width → Bool} {children : Nat → States width → List (States width)}
    (k : Nat) (ws : States width) (cache : TreeCache) (hc : TreeGood done children cache)
    (h : plain done children k ws = false) : TreeGood done children (treePut k ws cache) := by
  simp only [treePut, forceNat_eq]
  refine ⟨RawLaws.insert_wf hc.1 _, ?_⟩
  intro j vs hh
  simp only [treeHit, forceNat_eq, RawLaws.contains_insert hc.1, Bool.or_eq_true] at hh
  rcases hh with he | hold
  · have heq : key k ws = key j vs := Std.LawfulEqCmp.eq_of_compare (beq_iff_eq.mp he)
    obtain ⟨rfl, rfl⟩ := key_inj heq
    exact h
  · exact hc.2 j vs (by simpa only [treeHit, forceNat_eq] using hold)

def run (done : States width → Bool) (children : Nat → States width → List (States width)) (k : Nat) (ws : States width) : Bool :=
  (search treeHit treePut done children k ws ∅).1

lemma run_correct (done : States width → Bool) (children : Nat → States width → List (States width)) (k : Nat) (ws : States width) :
    run done children k ws = plain done children k ws := by
  exact search_run treeHit treePut done children (TreeGood done children)
    (fun k ws cache hc hh => hc.2 k ws hh)
    (fun k ws cache hc hh => tree_put_good k ws cache hc hh)
    k ws ∅ (tree_good_empty done children)


lemma plain_complete (done : α → Bool) (children : Nat → α → List α)
    (Sol : Nat → α → Prop)
    (base : ∀ x, Sol 0 x → done x = true)
    (step : ∀ k x, Sol (k+1) x → done x = true ∨ ∃ y ∈ children k x, Sol k y)
    (k : Nat) (x : α) (h : Sol k x) : plain done children k x = true := by
  induction k generalizing x with
  | zero => exact base x h
  | succ k ih =>
    rcases step k x h with hd | ⟨y, hy, hs⟩
    · simp only [plain, hd, Bool.true_or]
    · simp only [plain, Bool.or_eq_true, List.any_eq_true]
      exact Or.inr ⟨y, hy, ih y hs⟩

lemma run_reject (done : States width → Bool) (children : Nat → States width → List (States width))
    (Sol : Nat → States width → Prop)
    (base : ∀ x, Sol 0 x → done x = true)
    (step : ∀ k x, Sol (k+1) x → done x = true ∨ ∃ y ∈ children k x, Sol k y)
    (k : Nat) (ws : States width) (h : run done children k ws = false) : ¬ Sol k ws := by
  intro hs
  have ht := plain_complete done children Sol base step k ws hs
  rw [← run_correct, h] at ht
  contradiction


def treeHitFrom (threshold k : Nat) (ws : States width) (cache : TreeCache) : Bool :=
  decide (threshold ≤ k) && treeHit k ws cache

lemma tree_hitFrom_sound {done : States width → Bool} {children : Nat → States width → List (States width)}
    (threshold k : Nat) (ws : States width) (cache : TreeCache) (hc : TreeGood done children cache)
    (h : treeHitFrom threshold k ws cache = true) : plain done children k ws = false := by
  simp only [treeHitFrom, Bool.and_eq_true] at h
  exact hc.2 k ws h.2

def treePutFrom (threshold k : Nat) (ws : States width) (cache : TreeCache) : TreeCache :=
  if threshold ≤ k then treePut k ws cache else cache

lemma tree_putFrom_good {done : States width → Bool} {children : Nat → States width → List (States width)}
    (threshold k : Nat) (ws : States width) (cache : TreeCache) (hc : TreeGood done children cache)
    (h : plain done children k ws = false) : TreeGood done children (treePutFrom threshold k ws cache) := by
  unfold treePutFrom
  split_ifs
  · exact tree_put_good k ws cache hc h
  · exact hc

def runFrom (threshold : Nat) (done : States width → Bool) (children : Nat → States width → List (States width))
    (k : Nat) (ws : States width) : Bool :=
  (search (treeHitFrom threshold) (treePutFrom threshold) done children k ws ∅).1

lemma runFrom_correct (threshold : Nat) (done : States width → Bool) (children : Nat → States width → List (States width))
    (k : Nat) (ws : States width) : runFrom threshold done children k ws = plain done children k ws := by
  exact search_run (treeHitFrom threshold) (treePutFrom threshold) done children (TreeGood done children)
    (fun k ws cache hc hh => tree_hitFrom_sound threshold k ws cache hc hh)
    (fun k ws cache hc hh => tree_putFrom_good threshold k ws cache hc hh)
    k ws ∅ (tree_good_empty done children)

end Memo

namespace MemoActual

open SearchKernel
variable {width : Nat}

abbrev State := List (BitVec width)

def insertW (v : BitVec width) : List (BitVec width) → List (BitVec width)
  | [] => [v]
  | x :: xs => if v ≤ x then v :: x :: xs else x :: insertW v xs

def ordered (ws : List (BitVec width)) := ws.foldr insertW []

lemma insertW_perm (v : BitVec width) (ws : List (BitVec width)) :
    (insertW v ws).Perm (v :: ws) := by
  induction ws with
  | nil => exact .refl _
  | cons x xs ih =>
    simp only [insertW]
    split
    · exact .refl _
    · exact (ih.cons x).trans (.swap _ _ _)

lemma ordered_perm (ws : List (BitVec width)) : (ordered ws).Perm ws := by
  induction ws with
  | nil => exact .refl _
  | cons x xs ih => exact (insertW_perm x (ordered xs)).trans (ih.cons x)

lemma perm_set {u v : List (BitVec width)} (p : u.Perm v) : u.toFinset = v.toFinset := by
  ext a
  simpa only [List.mem_toFinset] using (p.mem_iff : a ∈ u ↔ a ∈ v)

def done (goal : BitVec width) (ws : List (BitVec width)) : Bool :=
  ws == [goal] || ws == [~~~goal]

def children (goal : BitVec width) (rows : List (Fin width)) (k : Nat)
    (ws : List (BitVec width)) : List (List (BitVec width)) :=
  (pairs ws).flatMap fun (a,b,r) =>
    (ops a b).flatMap fun z =>
      if z ∈ a :: b :: r then [] else
        (keepChoices a b r).filterMap fun kept =>
          if kept.length ≤ k ∧ separates goal rows (z :: kept) = true
          then some (ordered (z :: kept)) else none

lemma base_complete {goal g : BitVec width} (hg : g = goal ∨ g = ~~~goal)
    (ws : List (BitVec width)) (h : ws.Nodup ∧ live basicOps g 0 ws.toFinset) :
    done goal ws = true := by
  have he := singleton_list h.1 h.2
  rcases hg with rfl | rfl <;> simp [done, he]

lemma step_complete {goal g : BitVec width} (hg : g = goal ∨ g = ~~~goal)
    (rows : List (Fin width)) (k : Nat) (ws : List (BitVec width))
    (h : ws.Nodup ∧ live basicOps g (k+1) ws.toFinset) :
    done goal ws = true ∨ ∃ child ∈ children goal rows k ws,
      child.Nodup ∧ live basicOps g k child.toFinset := by
  obtain ⟨hn, hlive⟩ := h
  rcases first_live hlive with hend | ⟨a, ha, b, hb, hab, z, hz, hout, needed, hs, tail⟩
  · left
    have he := singleton_list hn hend
    rcases hg with rfl | rfl <;> simp [done, he]
  · right
    obtain ⟨r, hm, hp⟩ := pick_two (List.mem_toFinset.mp ha) (List.mem_toFinset.mp hb) hab
    have go {a b : BitVec width} (perm : ws.Perm (a :: b :: r))
        (hmem : (a,b,r) ∈ pairs ws)
        (hset : ws.toFinset = insert a (insert b needed)) (hop : z ∈ basicOps a b) :
        ∃ child ∈ children goal rows k ws,
          child.Nodup ∧ live basicOps g k child.toFinset := by
      obtain ⟨kept, hk, hnk, hfin⟩ := recover_kept perm hn hset
      have hznew : z ∉ kept := by
        intro hu
        apply hout
        rw [hset]
        exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (hfin ▸ List.mem_toFinset.mpr hu))
      have hnd : (z :: kept).Nodup := List.nodup_cons.mpr ⟨hznew, hnk⟩
      have hl : live basicOps g k (z :: kept).toFinset := by simpa [hfin] using tail
      have hc := live_card hl
      rw [List.toFinset_card_of_nodup hnd, List.length_cons] at hc
      have fresh : z ∉ a :: b :: r := by
        intro hzmem
        exact hout (List.mem_toFinset.mpr (perm.mem_iff.mpr hzmem))
      refine ⟨ordered (z :: kept), ?_, (ordered_perm _).nodup_iff.mpr hnd, ?_⟩
      · apply List.mem_flatMap.mpr
        refine ⟨(a,b,r), hmem, List.mem_flatMap.mpr ⟨z, List.mem_toFinset.mp hop, ?_⟩⟩
        simp only [if_neg fresh]
        exact List.mem_filterMap.mpr ⟨kept, hk, by simp [show kept.length ≤ k by omega,
          separates_complete hg rows hl]⟩
      · rwa [perm_set (ordered_perm _)]
    rcases hm with direct | swap
    · exact go hp direct hs hz
    · exact go (hp.trans (.swap _ _ _)) swap (by rw [hs, Finset.insert_comm]) (ops_swap a b ▸ hz)

lemma run_complete {goal g : BitVec width} (hg : g = goal ∨ g = ~~~goal)
    (rows : List (Fin width)) (threshold k : Nat) (ws : List (BitVec width))
    (hn : ws.Nodup) (h : live basicOps g k ws.toFinset) :
    Memo.runFrom threshold (done goal) (children goal rows) k ws = true := by
  rw [Memo.runFrom_correct]
  exact Memo.plain_complete (done goal) (children goal rows)
    (fun k ws => ws.Nodup ∧ live basicOps g k ws.toFinset)
    (base_complete hg) (step_complete hg rows) k ws ⟨hn,h⟩

def search (goal : BitVec width) (threshold n : Nat) (inputs : List (BitVec width)) : Bool :=
  let rows := falseRows goal
  inputs.sublists.any fun ws => decide (ws.length ≤ n+1) && separates goal rows ws &&
    Memo.runFrom threshold (done goal) (children goal rows) n ws

lemma search_complete {goal g : BitVec width} (hg : g = goal ∨ g = ~~~goal)
    (threshold n : Nat) (inputs : List (BitVec width)) (hn : inputs.Nodup)
    (h : build basicOps g n inputs.toFinset) : search goal threshold n inputs = true := by
  classical
  obtain ⟨s,hs,hl⟩ := compress h
  let ws := inputs.filter (· ∈ s)
  have eq : ws.toFinset = s := by
    ext w
    simp only [ws, List.mem_toFinset, List.mem_filter, decide_eq_true_eq, and_iff_right_iff_imp]
    exact fun hw => List.mem_toFinset.mp (hs hw)
  have hnd : ws.Nodup := hn.filter _
  have hl' : live basicOps g n ws.toFinset := eq.symm ▸ hl
  have sz := live_card hl'
  rw [List.toFinset_card_of_nodup hnd] at sz
  exact List.any_eq_true.mpr ⟨ws,List.mem_sublists.mpr (List.filter_sublist ..),
    by simp [sz, separates_complete hg (falseRows goal) hl', run_complete hg (falseRows goal) threshold n ws hnd hl']⟩

lemma no_build {goal g : BitVec width} (hg : g = goal ∨ g = ~~~goal)
    (threshold n : Nat) (inputs : List (BitVec width)) (hn : inputs.Nodup)
    (rejected : search goal threshold n inputs = false) : ¬ build basicOps g n inputs.toFinset := by
  intro h
  have found := search_complete hg threshold n inputs hn h
  rw [rejected] at found
  contradiction

end MemoActual


namespace MemoPruned

variable {α κ : Type}

def plain (admissible : Nat → α → Bool) (done : α → Bool) (children : Nat → α → List α) : Nat → α → Bool
  | 0, x => if admissible 0 x then done x else false
  | k + 1, x => if admissible (k+1) x then done x || (children k x).any (plain admissible done children k) else false

def scan (next : α → κ → Bool × κ) : List α → κ → Bool × κ
  | [], cache => (false, cache)
  | x :: xs, cache =>
    match next x cache with
    | (true, cache') => (true, cache')
    | (false, cache') => scan next xs cache'

lemma scan_correct (Good : κ → Prop)
    (f : α → Bool) (next : α → κ → Bool × κ)
    (hnext : ∀ x cache, Good cache →
      (next x cache).1 = f x ∧ Good (next x cache).2)
    (xs : List α) (cache : κ) (hc : Good cache) :
    (scan next xs cache).1 = xs.any f ∧ Good (scan next xs cache).2 := by
  induction xs generalizing cache with
  | nil => exact ⟨rfl, hc⟩
  | cons x xs ih =>
    have hs := hnext x cache hc
    cases he : next x cache with
    | mk b cache' =>
      simp only [he] at hs
      cases b with
      | false =>
        have ht := ih cache' hs.2
        simpa only [scan, he, hs.1.symm, List.any_cons, Bool.false_or] using ht
      | true =>
        simp only [scan, he, hs.1.symm, List.any_cons, Bool.true_or]
        exact ⟨trivial, hs.2⟩

def search (hit : Nat → α → κ → Bool) (put : Nat → α → κ → κ) (admissible : Nat → α → Bool) (done : α → Bool) (children : Nat → α → List α) :
    Nat → α → κ → Bool × κ
  | 0, x, cache =>
    if hit 0 x cache then (false, cache)
    else if !admissible 0 x then (false, cache)
    else if done x then (true, cache)
    else (false, put 0 x cache)
  | k+1, x, cache =>
    if hit (k+1) x cache then (false, cache)
    else if !admissible (k+1) x then (false, cache)
    else if done x then (true, cache)
    else match scan (search hit put admissible done children k) (children k x) cache with
    | (true, cache') => (true, cache')
    | (false, cache') => (false, put (k+1) x cache')

lemma search_correct (hit : Nat → α → κ → Bool) (put : Nat → α → κ → κ)
    (admissible : Nat → α → Bool) (done : α → Bool) (children : Nat → α → List α) (Good : κ → Prop)
    (hit_sound : ∀ k x cache, Good cache → hit k x cache = true → plain admissible done children k x = false)
    (put_good : ∀ k x cache, Good cache → plain admissible done children k x = false → Good (put k x cache))
    (k : Nat) (x : α) (cache : κ) (hc : Good cache) :
    (search hit put admissible done children k x cache).1 = plain admissible done children k x ∧
      Good (search hit put admissible done children k x cache).2 := by
  induction k generalizing x cache with
  | zero =>
    by_cases hh : hit 0 x cache = true
    · simp only [search, hh, Bool.true_eq, ite_true, Prod.fst, Prod.snd]
      exact ⟨(hit_sound 0 x cache hc hh).symm, hc⟩
    · have hh' : hit 0 x cache = false := Bool.eq_false_iff.mpr hh
      by_cases ha : admissible 0 x = true
      · by_cases hd : done x = true
        · simp [search, hh', ha, hd, plain, hc]
        · have hd' : done x = false := Bool.eq_false_iff.mpr hd
          have hx : plain admissible done children 0 x = false := by simp [plain, ha, hd']
          simpa only [search, hh', Bool.false_eq_true, ite_false, ha, Bool.not_true,
            hd', Prod.fst, Prod.snd] using And.intro hx.symm (put_good 0 x cache hc hx)
      · have ha' : admissible 0 x = false := Bool.eq_false_iff.mpr ha
        simp [search, hh', ha', plain, hc]
  | succ k ih =>
    by_cases hh : hit (k+1) x cache = true
    · simp only [search, hh, Bool.true_eq, ite_true, Prod.fst, Prod.snd]
      exact ⟨(hit_sound (k+1) x cache hc hh).symm, hc⟩
    · have hh' : hit (k+1) x cache = false := Bool.eq_false_iff.mpr hh
      by_cases ha : admissible (k+1) x = true
      · by_cases hd : done x = true
        · simp [search, hh', ha, hd, plain, hc]
        · have hd' : done x = false := Bool.eq_false_iff.mpr hd
          have hs := scan_correct Good (plain admissible done children k) (search hit put admissible done children k)
            (fun y c h => ih y c h) (children k x) cache hc
          cases he : scan (search hit put admissible done children k) (children k x) cache with
          | mk b cache' =>
            simp only [he] at hs
            cases b with
            | false =>
              have hx : plain admissible done children (k+1) x = false := by
                simp only [plain, ha, Bool.true_eq, ite_true, hd', Bool.false_or]
                exact hs.1.symm
              simp only [search, hh', Bool.false_eq_true, ite_false, ha, Bool.not_true,
                hd', he, Prod.fst, Prod.snd]
              exact ⟨hx.symm, put_good (k+1) x cache' hs.2 hx⟩
            | true =>
              simp only [search, hh', Bool.false_eq_true, ite_false, ha, Bool.not_true,
                hd', he, Prod.fst, Prod.snd]
              constructor
              · simp only [plain, ha, Bool.true_eq, ite_true, hd', Bool.false_or]
                exact hs.1.symm
              · exact hs.2
      · have ha' : admissible (k+1) x = false := Bool.eq_false_iff.mpr ha
        simp [search, hh', ha', plain, hc]

lemma search_run (hit : Nat → α → κ → Bool) (put : Nat → α → κ → κ)
    (admissible : Nat → α → Bool) (done : α → Bool) (children : Nat → α → List α) (Good : κ → Prop)
    (hit_sound : ∀ k x cache, Good cache → hit k x cache = true → plain admissible done children k x = false)
    (put_good : ∀ k x cache, Good cache → plain admissible done children k x = false → Good (put k x cache))
    (k : Nat) (x : α) (cache : κ) (hc : Good cache) :
    (search hit put admissible done children k x cache).1 = plain admissible done children k x :=
  (search_correct hit put admissible done children Good hit_sound put_good k x cache hc).1


variable {width : Nat}

abbrev States (width : Nat) := List (BitVec width)
abbrev TreeCache := Std.TreeSet.Raw Nat

def key (k : Nat) (ws : States width) : Nat :=
  PackedKeyWide.key k ws

def forceNat {β : Type} (n : Nat) (f : Nat → β) : β :=
  Nat.rec (f 0) (fun k _ => f (k+1)) n

lemma forceNat_eq {β : Type} (n : Nat) (f : Nat → β) : forceNat n f = f n := by
  cases n <;> rfl

def treeHit (k : Nat) (ws : States width) (cache : TreeCache) : Bool := forceNat (key k ws) (fun q => cache.contains q)
def treePut (k : Nat) (ws : States width) (cache : TreeCache) : TreeCache := forceNat (key k ws) (fun q => cache.insert q)

lemma key_inj {k j : Nat} {ws vs : States width} (h : key k ws = key j vs) : k = j ∧ ws = vs :=
  PackedKeyWide.key_inj h

def TreeGood (admissible : Nat → States width → Bool) (done : States width → Bool) (children : Nat → States width → List (States width)) (cache : TreeCache) : Prop :=
  cache.WF ∧ ∀ k ws, treeHit k ws cache = true → plain admissible done children k ws = false

lemma tree_good_empty (admissible : Nat → States width → Bool) (done : States width → Bool) (children : Nat → States width → List (States width)) :
    TreeGood admissible done children ∅ := by
  refine ⟨RawLaws.empty_wf, ?_⟩
  intro k ws h
  simp only [treeHit, forceNat_eq] at h
  change false = true at h
  contradiction

lemma tree_put_good {admissible : Nat → States width → Bool} {done : States width → Bool} {children : Nat → States width → List (States width)}
    (k : Nat) (ws : States width) (cache : TreeCache) (hc : TreeGood admissible done children cache)
    (h : plain admissible done children k ws = false) : TreeGood admissible done children (treePut k ws cache) := by
  simp only [treePut, forceNat_eq]
  refine ⟨RawLaws.insert_wf hc.1 _, ?_⟩
  intro j vs hh
  simp only [treeHit, forceNat_eq, RawLaws.contains_insert hc.1, Bool.or_eq_true] at hh
  rcases hh with he | hold
  · have heq : key k ws = key j vs := Std.LawfulEqCmp.eq_of_compare (beq_iff_eq.mp he)
    obtain ⟨rfl, rfl⟩ := key_inj heq
    exact h
  · exact hc.2 j vs (by simpa only [treeHit, forceNat_eq] using hold)

def run (admissible : Nat → States width → Bool) (done : States width → Bool) (children : Nat → States width → List (States width)) (k : Nat) (ws : States width) : Bool :=
  (search treeHit treePut admissible done children k ws ∅).1

lemma run_correct (admissible : Nat → States width → Bool) (done : States width → Bool) (children : Nat → States width → List (States width)) (k : Nat) (ws : States width) :
    run admissible done children k ws = plain admissible done children k ws := by
  exact search_run treeHit treePut admissible done children (TreeGood admissible done children)
    (fun k ws cache hc hh => hc.2 k ws hh)
    (fun k ws cache hc hh => tree_put_good k ws cache hc hh)
    k ws ∅ (tree_good_empty admissible done children)


lemma plain_complete (admissible : Nat → α → Bool) (done : α → Bool) (children : Nat → α → List α)
    (Sol : Nat → α → Prop)
    (admissible_complete : ∀ k x, Sol k x → admissible k x = true)
    (base : ∀ x, Sol 0 x → done x = true)
    (step : ∀ k x, Sol (k+1) x → done x = true ∨ ∃ y ∈ children k x, Sol k y)
    (k : Nat) (x : α) (h : Sol k x) : plain admissible done children k x = true := by
  induction k generalizing x with
  | zero => simp only [plain, admissible_complete 0 x h, Bool.true_eq, ite_true, base x h]
  | succ k ih =>
    simp only [plain, admissible_complete (k+1) x h, Bool.true_eq, ite_true]
    rcases step k x h with hd | ⟨y, hy, hs⟩
    · simp only [hd, Bool.true_or]
    · simp only [Bool.or_eq_true, List.any_eq_true]
      exact Or.inr ⟨y, hy, ih y hs⟩

lemma run_reject (admissible : Nat → States width → Bool) (done : States width → Bool)
    (children : Nat → States width → List (States width)) (Sol : Nat → States width → Prop)
    (admissible_complete : ∀ k x, Sol k x → admissible k x = true)
    (base : ∀ x, Sol 0 x → done x = true)
    (step : ∀ k x, Sol (k+1) x → done x = true ∨ ∃ y ∈ children k x, Sol k y)
    (k : Nat) (ws : States width) (h : run admissible done children k ws = false) : ¬ Sol k ws := by
  intro hs
  have ht := plain_complete admissible done children Sol admissible_complete base step k ws hs
  rw [← run_correct, h] at ht
  contradiction


def treeHitFrom (threshold k : Nat) (ws : States width) (cache : TreeCache) : Bool :=
  decide (threshold ≤ k) && treeHit k ws cache

lemma tree_hitFrom_sound {admissible : Nat → States width → Bool} {done : States width → Bool} {children : Nat → States width → List (States width)}
    (threshold k : Nat) (ws : States width) (cache : TreeCache) (hc : TreeGood admissible done children cache)
    (h : treeHitFrom threshold k ws cache = true) : plain admissible done children k ws = false := by
  simp only [treeHitFrom, Bool.and_eq_true] at h
  exact hc.2 k ws h.2

def treePutFrom (threshold k : Nat) (ws : States width) (cache : TreeCache) : TreeCache :=
  if threshold ≤ k then treePut k ws cache else cache

lemma tree_putFrom_good {admissible : Nat → States width → Bool} {done : States width → Bool} {children : Nat → States width → List (States width)}
    (threshold k : Nat) (ws : States width) (cache : TreeCache) (hc : TreeGood admissible done children cache)
    (h : plain admissible done children k ws = false) : TreeGood admissible done children (treePutFrom threshold k ws cache) := by
  unfold treePutFrom
  split_ifs
  · exact tree_put_good k ws cache hc h
  · exact hc

def runFrom (threshold : Nat) (admissible : Nat → States width → Bool) (done : States width → Bool) (children : Nat → States width → List (States width))
    (k : Nat) (ws : States width) : Bool :=
  (search (treeHitFrom threshold) (treePutFrom threshold) admissible done children k ws ∅).1

lemma runFrom_correct (threshold : Nat) (admissible : Nat → States width → Bool) (done : States width → Bool) (children : Nat → States width → List (States width))
    (k : Nat) (ws : States width) : runFrom threshold admissible done children k ws = plain admissible done children k ws := by
  exact search_run (treeHitFrom threshold) (treePutFrom threshold) admissible done children (TreeGood admissible done children)
    (fun k ws cache hc hh => tree_hitFrom_sound threshold k ws cache hc hh)
    (fun k ws cache hc hh => tree_putFrom_good threshold k ws cache hc hh)
    k ws ∅ (tree_good_empty admissible done children)

end MemoPruned

namespace MemoActualPruned

open SearchKernel
variable {width : Nat}

abbrev State := List (BitVec width)

def insertW (v : BitVec width) : List (BitVec width) → List (BitVec width)
  | [] => [v]
  | x :: xs => if v ≤ x then v :: x :: xs else x :: insertW v xs

def ordered (ws : List (BitVec width)) := ws.foldr insertW []

lemma insertW_perm (v : BitVec width) (ws : List (BitVec width)) :
    (insertW v ws).Perm (v :: ws) := by
  induction ws with
  | nil => exact .refl _
  | cons x xs ih =>
    simp only [insertW]
    split
    · exact .refl _
    · exact (ih.cons x).trans (.swap _ _ _)

lemma ordered_perm (ws : List (BitVec width)) : (ordered ws).Perm ws := by
  induction ws with
  | nil => exact .refl _
  | cons x xs ih => exact (insertW_perm x (ordered xs)).trans (ih.cons x)

lemma perm_set {u v : List (BitVec width)} (p : u.Perm v) : u.toFinset = v.toFinset := by
  ext a
  simpa only [List.mem_toFinset] using (p.mem_iff : a ∈ u ↔ a ∈ v)

def done (goal : BitVec width) (ws : List (BitVec width)) : Bool :=
  ws == [goal] || ws == [~~~goal]

def children (goal : BitVec width) (rows : List (Fin width)) (k : Nat)
    (ws : List (BitVec width)) : List (List (BitVec width)) :=
  (pairs ws).flatMap fun (a,b,r) =>
    (ops a b).flatMap fun z =>
      if z ∈ a :: b :: r then [] else
        (keepChoices a b r).filterMap fun kept =>
          if kept.length ≤ k ∧ separates goal rows (z :: kept) = true
          then some (ordered (z :: kept)) else none

lemma base_complete {goal g : BitVec width} (hg : g = goal ∨ g = ~~~goal)
    (ws : List (BitVec width)) (h : ws.Nodup ∧ live basicOps g 0 ws.toFinset) :
    done goal ws = true := by
  have he := singleton_list h.1 h.2
  rcases hg with rfl | rfl <;> simp [done, he]

lemma step_complete {goal g : BitVec width} (hg : g = goal ∨ g = ~~~goal)
    (rows : List (Fin width)) (k : Nat) (ws : List (BitVec width))
    (h : ws.Nodup ∧ live basicOps g (k+1) ws.toFinset) :
    done goal ws = true ∨ ∃ child ∈ children goal rows k ws,
      child.Nodup ∧ live basicOps g k child.toFinset := by
  obtain ⟨hn, hlive⟩ := h
  rcases first_live hlive with hend | ⟨a, ha, b, hb, hab, z, hz, hout, needed, hs, tail⟩
  · left
    have he := singleton_list hn hend
    rcases hg with rfl | rfl <;> simp [done, he]
  · right
    obtain ⟨r, hm, hp⟩ := pick_two (List.mem_toFinset.mp ha) (List.mem_toFinset.mp hb) hab
    have go {a b : BitVec width} (perm : ws.Perm (a :: b :: r))
        (hmem : (a,b,r) ∈ pairs ws)
        (hset : ws.toFinset = insert a (insert b needed)) (hop : z ∈ basicOps a b) :
        ∃ child ∈ children goal rows k ws,
          child.Nodup ∧ live basicOps g k child.toFinset := by
      obtain ⟨kept, hk, hnk, hfin⟩ := recover_kept perm hn hset
      have hznew : z ∉ kept := by
        intro hu
        apply hout
        rw [hset]
        exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (hfin ▸ List.mem_toFinset.mpr hu))
      have hnd : (z :: kept).Nodup := List.nodup_cons.mpr ⟨hznew, hnk⟩
      have hl : live basicOps g k (z :: kept).toFinset := by simpa [hfin] using tail
      have hc := live_card hl
      rw [List.toFinset_card_of_nodup hnd, List.length_cons] at hc
      have fresh : z ∉ a :: b :: r := by
        intro hzmem
        exact hout (List.mem_toFinset.mpr (perm.mem_iff.mpr hzmem))
      refine ⟨ordered (z :: kept), ?_, (ordered_perm _).nodup_iff.mpr hnd, ?_⟩
      · apply List.mem_flatMap.mpr
        refine ⟨(a,b,r), hmem, List.mem_flatMap.mpr ⟨z, List.mem_toFinset.mp hop, ?_⟩⟩
        simp only [if_neg fresh]
        exact List.mem_filterMap.mpr ⟨kept, hk, by simp [show kept.length ≤ k by omega,
          separates_complete hg rows hl]⟩
      · rwa [perm_set (ordered_perm _)]
    rcases hm with direct | swap
    · exact go hp direct hs hz
    · exact go (hp.trans (.swap _ _ _)) swap (by rw [hs, Finset.insert_comm]) (ops_swap a b ▸ hz)

lemma run_complete {goal g : BitVec width} (hg : g = goal ∨ g = ~~~goal)
    (admissible : Nat → List (BitVec width) → Bool)
    (admissible_complete : ∀ k ws, ws.Nodup → live basicOps g k ws.toFinset → admissible k ws = true)
    (rows : List (Fin width)) (threshold k : Nat) (ws : List (BitVec width))
    (hn : ws.Nodup) (h : live basicOps g k ws.toFinset) :
    MemoPruned.runFrom threshold admissible (done goal) (children goal rows) k ws = true := by
  rw [MemoPruned.runFrom_correct]
  exact MemoPruned.plain_complete admissible (done goal) (children goal rows)
    (fun k ws => ws.Nodup ∧ live basicOps g k ws.toFinset)
    (fun k ws h => admissible_complete k ws h.1 h.2)
    (base_complete hg) (step_complete hg rows) k ws ⟨hn,h⟩

def search (goal : BitVec width) (admissible : Nat → List (BitVec width) → Bool)
    (threshold n : Nat) (inputs : List (BitVec width)) : Bool :=
  let rows := falseRows goal
  inputs.sublists.any fun ws => decide (ws.length ≤ n+1) && separates goal rows ws &&
    MemoPruned.runFrom threshold admissible (done goal) (children goal rows) n ws

lemma search_complete {goal g : BitVec width} (hg : g = goal ∨ g = ~~~goal)
    (admissible : Nat → List (BitVec width) → Bool)
    (admissible_complete : ∀ k ws, ws.Nodup → live basicOps g k ws.toFinset → admissible k ws = true)
    (threshold n : Nat) (inputs : List (BitVec width)) (hn : inputs.Nodup)
    (h : build basicOps g n inputs.toFinset) : search goal admissible threshold n inputs = true := by
  classical
  obtain ⟨s,hs,hl⟩ := compress h
  let ws := inputs.filter (· ∈ s)
  have eq : ws.toFinset = s := by
    ext w
    simp only [ws, List.mem_toFinset, List.mem_filter, decide_eq_true_eq, and_iff_right_iff_imp]
    exact fun hw => List.mem_toFinset.mp (hs hw)
  have hnd : ws.Nodup := hn.filter _
  have hl' : live basicOps g n ws.toFinset := eq.symm ▸ hl
  have sz := live_card hl'
  rw [List.toFinset_card_of_nodup hnd] at sz
  exact List.any_eq_true.mpr ⟨ws,List.mem_sublists.mpr (List.filter_sublist ..),
    by simp [sz, separates_complete hg (falseRows goal) hl',
      run_complete hg admissible admissible_complete (falseRows goal) threshold n ws hnd hl']⟩

lemma no_build {goal g : BitVec width} (hg : g = goal ∨ g = ~~~goal)
    (admissible : Nat → List (BitVec width) → Bool)
    (admissible_complete : ∀ k ws, ws.Nodup → live basicOps g k ws.toFinset → admissible k ws = true)
    (threshold n : Nat) (inputs : List (BitVec width)) (hn : inputs.Nodup)
    (rejected : search goal admissible threshold n inputs = false) : ¬ build basicOps g n inputs.toFinset := by
  intro h
  have found := search_complete hg admissible admissible_complete threshold n inputs hn h
  rw [rejected] at found
  contradiction

end MemoActualPruned



namespace MemoPruned

variable {width : Nat}

def runBatchFrom (threshold : Nat) (admissible : Nat → States width → Bool)
    (done : States width → Bool) (children : Nat → States width → List (States width))
    (k : Nat) (starts : List (States width)) : Bool :=
  (scan (search (treeHitFrom threshold) (treePutFrom threshold) admissible done children k) starts ∅).1

lemma runBatchFrom_correct (threshold : Nat) (admissible : Nat → States width → Bool)
    (done : States width → Bool) (children : Nat → States width → List (States width))
    (k : Nat) (starts : List (States width)) :
    runBatchFrom threshold admissible done children k starts =
      starts.any (plain admissible done children k) := by
  exact (scan_correct (TreeGood admissible done children) (plain admissible done children k)
    (search (treeHitFrom threshold) (treePutFrom threshold) admissible done children k)
    (fun ws cache hc => search_correct (treeHitFrom threshold) (treePutFrom threshold)
      admissible done children (TreeGood admissible done children)
      (fun j vs c hgood hhit => tree_hitFrom_sound threshold j vs c hgood hhit)
      (fun j vs c hgood hfalse => tree_putFrom_good threshold j vs c hgood hfalse)
      k ws cache hc)
    starts ∅ (tree_good_empty admissible done children)).1

lemma runBatchFrom_reject (threshold : Nat) (admissible : Nat → States width → Bool)
    (done : States width → Bool) (children : Nat → States width → List (States width))
    (Sol : Nat → States width → Prop)
    (admissible_complete : ∀ k x, Sol k x → admissible k x = true)
    (base : ∀ x, Sol 0 x → done x = true)
    (step : ∀ k x, Sol (k+1) x → done x = true ∨ ∃ y ∈ children k x, Sol k y)
    (k : Nat) (starts : List (States width))
    (rejected : runBatchFrom threshold admissible done children k starts = false)
    {ws : States width} (hws : ws ∈ starts) : ¬ Sol k ws := by
  intro hs
  have hp := plain_complete admissible done children Sol admissible_complete base step k ws hs
  have ha : starts.any (plain admissible done children k) = true :=
    List.any_eq_true.mpr ⟨ws,hws,hp⟩
  rw [← runBatchFrom_correct, rejected] at ha
  contradiction

end MemoPruned

namespace MemoActualPruned

variable {width : Nat}

lemma batch_no_live {goal g : BitVec width} (hg : g = goal ∨ g = ~~~goal)
    (admissible : Nat → List (BitVec width) → Bool)
    (admissible_complete : ∀ k ws, ws.Nodup → live basicOps g k ws.toFinset → admissible k ws = true)
    (rows : List (Fin width)) (threshold k : Nat) (starts : List (List (BitVec width)))
    (rejected : MemoPruned.runBatchFrom threshold admissible (done goal) (children goal rows) k starts = false)
    {ws : List (BitVec width)} (hws : ws ∈ starts) (hn : ws.Nodup) :
    ¬ live basicOps g k ws.toFinset := by
  intro hl
  exact MemoPruned.runBatchFrom_reject threshold admissible (done goal) (children goal rows)
    (fun j vs => vs.Nodup ∧ live basicOps g j vs.toFinset)
    (fun j vs h => admissible_complete j vs h.1 h.2)
    (base_complete hg) (step_complete hg rows) k starts rejected hws ⟨hn,hl⟩

end MemoActualPruned



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

section EndpointGraphBase


variable {width : Nat}

def positiveEndpoint (target : BitVec width) (S : Finset (BitVec width))
    (a : BitVec width) (p : Fin width) : Prop :=
  target[p.val] = true ∧ ∃ q : Fin width, target[q.val] = false ∧ uniqueSep S a p q

def negativeEndpoint (target : BitVec width) (S : Finset (BitVec width))
    (a : BitVec width) (q : Fin width) : Prop :=
  target[q.val] = false ∧ ∃ p : Fin width, target[p.val] = true ∧ uniqueSep S a p q

lemma bool_eq_of_common_ne (x y z : Bool) (hx : x ≠ z) (hy : y ≠ z) : x = y := by
  cases x <;> cases y <;> cases z <;> simp_all

lemma criticalPair_iff_endpointWitness (target : BitVec width)
    (S : Finset (BitVec width)) (a b : BitVec width) :
    criticalPair target S a b ↔ a ∈ S ∧ b ∈ S ∧ a ≠ b ∧
      ∃ p q : Fin width, positiveEndpoint target S a p ∧ positiveEndpoint target S b p ∧
        negativeEndpoint target S a q ∧ negativeEndpoint target S b q ∧
        a[p.val] ≠ a[q.val] ∧ b[p.val] ≠ b[q.val] := by
  constructor
  · rintro ⟨ha,hb,hab,p,q,ra,rb,sa,sb,hp,hq,hra,hrb,hsa,hsb,ua,ub,va,vb,ea,eb⟩
    refine ⟨ha,hb,hab,p,q,⟨hp,ra,hra,ua⟩,⟨hp,rb,hrb,ub⟩,
      ⟨hq,sa,hsa,va⟩,⟨hq,sb,hsb,vb⟩,?_,?_⟩
    · rw [ea]; exact va.1
    · rw [eb]; exact vb.1
  · rintro ⟨ha,hb,hab,p,q,⟨hp,ra,hra,ua⟩,⟨_,rb,hrb,ub⟩,
      ⟨hq,sa,hsa,va⟩,⟨_,sb,hsb,vb⟩,ea,eb⟩
    exact ⟨ha,hb,hab,p,q,ra,rb,sa,sb,hp,hq,hra,hrb,hsa,hsb,ua,ub,va,vb,
      bool_eq_of_common_ne _ _ _ ea va.1, bool_eq_of_common_ne _ _ _ eb vb.1⟩

namespace EndpointSpec

def same (w : BitVec width) (q : Fin width) : BitVec width :=
  if w[q.val] then w else ~~~w

lemma same_bit (w : BitVec width) (p q : Fin width) :
    (same w q)[p.val] = true ↔ w[p.val] = w[q.val] := by
  unfold same
  split <;> simp_all

def intersectSame (target : BitVec width) (ws : List (BitVec width))
    (q : Fin width) : BitVec width := ws.foldr (fun w acc => same w q &&& acc) target

lemma intersectSame_bit (target : BitVec width) (ws : List (BitVec width)) (p q : Fin width) :
    (intersectSame target ws q)[p.val] = true ↔
      target[p.val] = true ∧ ∀ w ∈ ws, w[p.val] = w[q.val] := by
  induction ws with
  | nil => simp [intersectSame]
  | cons w ws ih =>
    simp only [intersectSame, List.foldr_cons, BitVec.getElem_and, Bool.and_eq_true]
    change (same w q)[p.val] = true ∧ (intersectSame target ws q)[p.val] = true ↔ _
    rw [same_bit, ih]
    simp only [List.mem_cons, forall_eq_or_imp]
    tauto

def uniqueMask (target : BitVec width) (ws : List (BitVec width))
    (a : BitVec width) (q : Fin width) : BitVec width :=
  intersectSame target (ws.filter (fun w => w != a)) q &&& ~~~same a q

lemma uniqueMask_bit (target : BitVec width) (ws : List (BitVec width))
    (a : BitVec width) (p q : Fin width) :
    (uniqueMask target ws a q)[p.val] = true ↔
      target[p.val] = true ∧ uniqueSep ws.toFinset a p q := by
  have hs : (same a q)[p.val] = false ↔ a[p.val] ≠ a[q.val] := by
    cases hp : a[p.val] <;> cases hq : a[q.val] <;> simp [same, hp, hq]
  simp only [uniqueMask, BitVec.getElem_and, Bool.and_eq_true, BitVec.getElem_not,
    Bool.not_eq_true', intersectSame_bit, hs]
  simp only [uniqueSep, List.mem_filter, bne_iff_ne, List.mem_toFinset]
  constructor
  · rintro ⟨⟨ht,hu⟩,hd⟩
    exact ⟨ht,hd,fun w hw hwa => hu w ⟨hw,hwa⟩⟩
  · rintro ⟨ht,hd,hu⟩
    exact ⟨⟨ht,fun w hw => hu w hw.1 hw.2⟩,hd⟩

lemma nonzero_iff_bit (v : BitVec width) :
    v ≠ 0 ↔ ∃ p : Fin width, v[p.val] = true := by
  constructor
  · intro hn
    by_contra h
    push_neg at h
    apply hn
    apply BitVec.eq_of_getElem_eq
    intro i hi
    simpa using Bool.eq_false_iff.mpr (h ⟨i,hi⟩)
  · rintro ⟨p,hp⟩ he
    simpa [he] using hp

def negativeRows (target : BitVec width) : List (Fin width) :=
  (List.finRange width).filter (fun q => !target[q.val])

def orMasks {α : Type} (f : α → BitVec width) (xs : List α) : BitVec width :=
  xs.foldr (fun x acc => f x ||| acc) 0

lemma orMasks_bit {α : Type} (f : α → BitVec width) (xs : List α) (p : Fin width) :
    (orMasks f xs)[p.val] = true ↔ ∃ x ∈ xs, (f x)[p.val] = true := by
  induction xs with
  | nil => simp [orMasks]
  | cons x xs ih =>
    simp only [orMasks, List.foldr_cons, BitVec.getElem_or, Bool.or_eq_true]
    change (f x)[p.val] = true ∨ (orMasks f xs)[p.val] = true ↔ _
    rw [ih]
    simp

def positiveMask (target : BitVec width) (ws : List (BitVec width))
    (a : BitVec width) : BitVec width :=
  orMasks (uniqueMask target ws a) (negativeRows target)

lemma positiveMask_bit (target : BitVec width) (ws : List (BitVec width))
    (a : BitVec width) (p : Fin width) :
    (positiveMask target ws a)[p.val] = true ↔ positiveEndpoint target ws.toFinset a p := by
  simp only [positiveMask, orMasks_bit, uniqueMask_bit, positiveEndpoint]
  simp only [negativeRows, List.mem_filter, List.mem_finRange, Bool.not_eq_true,
    true_and]
  aesop

def ofBits (f : Fin width → Bool) : BitVec width :=
  (BitVec.ofBoolListLE (List.ofFn f)).cast (by simp)

lemma ofBits_bit (f : Fin width → Bool) (p : Fin width) : (ofBits f)[p.val] = f p := by
  simp only [ofBits, BitVec.getElem_cast]
  rw [← BitVec.getLsbD_eq_getElem, BitVec.getLsbD_ofBoolListLE]
  simp [List.getD_eq_getElem?_getD]

def negativeMask (target : BitVec width) (ws : List (BitVec width))
    (a : BitVec width) : BitVec width :=
  ofBits (fun q => !target[q.val] && (uniqueMask target ws a q != 0))

lemma negativeMask_bit (target : BitVec width) (ws : List (BitVec width))
    (a : BitVec width) (q : Fin width) :
    (negativeMask target ws a)[q.val] = true ↔ negativeEndpoint target ws.toFinset a q := by
  simp only [negativeMask, ofBits_bit, Bool.and_eq_true, Bool.not_eq_true', bne_iff_ne,
    nonzero_iff_bit, uniqueMask_bit, negativeEndpoint]

end EndpointSpec

namespace EndpointSpec

variable {width : Nat}

def phaseMask (w : BitVec width) (phase : Bool) : BitVec width :=
  if phase then w else ~~~w

lemma phaseMask_bit (w : BitVec width) (phase : Bool) (p : Fin width) :
    (phaseMask w phase)[p.val] = true ↔ w[p.val] = phase := by
  cases phase <;> simp [phaseMask]

def phaseHits (p n a b : BitVec width) (u v : Bool) : Bool :=
  (p &&& phaseMask a u &&& phaseMask b v != 0) &&
    (n &&& phaseMask a (!u) &&& phaseMask b (!v) != 0)

lemma phaseHits_bit (p n a b : BitVec width) (u v : Bool) :
    phaseHits p n a b u v = true ↔ ∃ x y : Fin width,
      p[x.val] = true ∧ n[y.val] = true ∧ a[x.val] = u ∧ b[x.val] = v ∧
      a[y.val] = !u ∧ b[y.val] = !v := by
  simp only [phaseHits, Bool.and_eq_true, bne_iff_ne, nonzero_iff_bit]
  constructor
  · rintro ⟨⟨x,hx⟩,⟨y,hy⟩⟩
    simp only [BitVec.getElem_and, Bool.and_eq_true, phaseMask_bit] at hx hy
    exact ⟨x,y,hx.1.1,hy.1.1,hx.1.2,hx.2,hy.1.2,hy.2⟩
  · rintro ⟨x,y,hp,hn,ha,hb,hna,hnb⟩
    refine ⟨⟨x,?_⟩,⟨y,?_⟩⟩ <;>
      simp only [BitVec.getElem_and, Bool.and_eq_true, phaseMask_bit]
    · exact ⟨⟨hp,ha⟩,hb⟩
    · exact ⟨⟨hn,hna⟩,hnb⟩

def edge (a b : BitVec width) (ea eb : BitVec width × BitVec width) : Bool :=
  let p := ea.1 &&& eb.1
  let n := ea.2 &&& eb.2
  ((p &&& a &&& b != 0) && (n &&& ~~~a &&& ~~~b != 0)) ||
  ((p &&& a &&& ~~~b != 0) && (n &&& ~~~a &&& b != 0)) ||
  ((p &&& ~~~a &&& b != 0) && (n &&& a &&& ~~~b != 0)) ||
  ((p &&& ~~~a &&& ~~~b != 0) && (n &&& a &&& b != 0))

lemma edge_phase (a b : BitVec width) (ea eb : BitVec width × BitVec width) :
    edge a b ea eb = true ↔ ∃ u v : Bool,
      phaseHits (ea.1 &&& eb.1) (ea.2 &&& eb.2) a b u v = true := by
  constructor
  · intro h
    simp only [edge, Bool.or_eq_true] at h
    rcases h with ((h | h) | h) | h
    · exact ⟨true,true,by simpa [phaseHits, phaseMask] using h⟩
    · exact ⟨true,false,by simpa [phaseHits, phaseMask] using h⟩
    · exact ⟨false,true,by simpa [phaseHits, phaseMask] using h⟩
    · exact ⟨false,false,by simpa [phaseHits, phaseMask] using h⟩
  · rintro ⟨u,v,h⟩
    cases u <;> cases v <;> simp only [phaseHits, phaseMask, Bool.not_true,
      Bool.not_false, Bool.true_eq, Bool.false_eq_true, ite_true, ite_false] at h <;>
      simp only [edge, Bool.or_eq_true] <;> tauto

lemma bool_other_eq_not (a b : Bool) (h : a ≠ b) : b = !a := by
  cases a <;> cases b <;> simp_all

lemma edge_bit (a b : BitVec width) (ea eb : BitVec width × BitVec width) :
    edge a b ea eb = true ↔ ∃ p q : Fin width,
      ea.1[p.val] = true ∧ eb.1[p.val] = true ∧
      ea.2[q.val] = true ∧ eb.2[q.val] = true ∧
      a[p.val] ≠ a[q.val] ∧ b[p.val] ≠ b[q.val] := by
  rw [edge_phase]
  simp_rw [phaseHits_bit]
  constructor
  · rintro ⟨u,v,p,q,hp,hq,ha,hb,hna,hnb⟩
    simp only [BitVec.getElem_and, Bool.and_eq_true] at hp hq
    refine ⟨p,q,hp.1,hp.2,hq.1,hq.2,?_,?_⟩
    · rw [ha,hna]; cases u <;> decide
    · rw [hb,hnb]; cases v <;> decide
  · rintro ⟨p,q,hpa,hpb,hna,hnb,ha,hb⟩
    refine ⟨a[p.val],b[p.val],p,q,?_,?_,rfl,rfl,
      bool_other_eq_not _ _ ha,bool_other_eq_not _ _ hb⟩ <;>
      simp only [BitVec.getElem_and, Bool.and_eq_true]
    · exact ⟨hpa,hpb⟩
    · exact ⟨hna,hnb⟩

lemma edge_correct (target : BitVec width) (S : Finset (BitVec width))
    (a b : BitVec width) (ea eb : BitVec width × BitVec width)
    (ha : a ∈ S) (hb : b ∈ S) (hab : a ≠ b)
    (hpa : ∀ p : Fin width, ea.1[p.val] = true ↔ positiveEndpoint target S a p)
    (hpb : ∀ p : Fin width, eb.1[p.val] = true ↔ positiveEndpoint target S b p)
    (hna : ∀ q : Fin width, ea.2[q.val] = true ↔ negativeEndpoint target S a q)
    (hnb : ∀ q : Fin width, eb.2[q.val] = true ↔ negativeEndpoint target S b q) :
    edge a b ea eb = true ↔ criticalPair target S a b := by
  rw [edge_bit, criticalPair_iff_endpointWitness]
  simp only [ha,hb,hab,true_and]
  simp_rw [hpa,hpb,hna,hnb]
  tauto

lemma referenceEdge_correct (target : BitVec width) (ws : List (BitVec width))
    (a b : BitVec width) (ha : a ∈ ws) (hb : b ∈ ws) (hab : a ≠ b) :
    edge a b (positiveMask target ws a, negativeMask target ws a)
      (positiveMask target ws b, negativeMask target ws b) = true ↔
      criticalPair target ws.toFinset a b := by
  exact edge_correct target ws.toFinset a b _ _ (List.mem_toFinset.mpr ha)
    (List.mem_toFinset.mpr hb) hab (positiveMask_bit target ws a)
    (positiveMask_bit target ws b) (negativeMask_bit target ws a)
    (negativeMask_bit target ws b)

end EndpointSpec


namespace Endpoint64

abbrev Mask := BitVec 64

def full : Mask := ~~~0

def same (w : Mask) (q : Nat) : Mask := if w.getLsbD q then w else ~~~w

def suffixes : List Mask → List Mask
  | [] => [full]
  | w :: ws =>
    let ss := suffixes ws
    (w &&& ss.headD full) :: ss

def rowMasksAux (q : Nat) (acc : Mask) : List Mask → List Mask → List Mask
  | w :: ws, s :: ss =>
    (acc &&& s &&& ~~~same w q) :: rowMasksAux q (acc &&& same w q) ws ss
  | _, _ => []

def rowMasks (goal : Mask) (ws : List Mask) (q : Nat) : List Mask :=
  rowMasksAux q goal ws (suffixes (ws.map (same · q))).tail

def addRow (qbit : Mask) : List Mask → List (Mask × Mask) → List (Mask × Mask)
  | p :: ps, (pos, neg) :: es =>
    (pos ||| p, if p == 0 then neg else neg ||| qbit) :: addRow qbit ps es
  | _, _ => []

def endpoints (goal : Mask) (ws : List Mask) : List (Mask × Mask) :=
  ((List.range 64).filter fun q => !goal.getLsbD q).foldl
    (fun es q => addRow ((1 : Mask) <<< q) (rowMasks goal ws q) es)
    (ws.map fun _ => (0, 0))

def edge (a b : Mask) (ea eb : Mask × Mask) : Bool :=
  let p := ea.1 &&& eb.1
  let n := ea.2 &&& eb.2
  ((p &&& a &&& b != 0) && (n &&& ~~~a &&& ~~~b != 0)) ||
  ((p &&& a &&& ~~~b != 0) && (n &&& ~~~a &&& b != 0)) ||
  ((p &&& ~~~a &&& b != 0) && (n &&& a &&& ~~~b != 0)) ||
  ((p &&& ~~~a &&& ~~~b != 0) && (n &&& a &&& b != 0))

def adjacencyRow (i : Nat) (a : Mask × (Mask × Mask))
    (others : List (Mask × (Mask × Mask))) : Nat :=
  others.zipIdx.foldl (fun mask (b,j) =>
    if i != j && edge a.1 b.1 a.2 b.2 then mask ||| (1 <<< j) else mask) 0

def graph (goal : Mask) (ws : List Mask) : List Nat :=
  let es := ws.zip (endpoints goal ws)
  es.zipIdx.map fun (a,i) => adjacencyRow i a es

end Endpoint64

namespace Endpoint64

lemma edge_correct (target : Mask) (S : Finset Mask) (a b : Mask) (ea eb : Mask × Mask)
    (ha : a ∈ S) (hb : b ∈ S) (hab : a ≠ b)
    (hpa : ∀ p : Fin 64, ea.1[p.val] = true ↔ positiveEndpoint target S a p)
    (hpb : ∀ p : Fin 64, eb.1[p.val] = true ↔ positiveEndpoint target S b p)
    (hna : ∀ q : Fin 64, ea.2[q.val] = true ↔ negativeEndpoint target S a q)
    (hnb : ∀ q : Fin 64, eb.2[q.val] = true ↔ negativeEndpoint target S b q) :
    edge a b ea eb = true ↔ criticalPair target S a b :=
  EndpointSpec.edge_correct target S a b ea eb ha hb hab hpa hpb hna hnb

end Endpoint64
namespace Endpoint64
def allMask (ws : List Mask) : Mask := ws.foldr (· &&& ·) full

lemma suffixes_head (ws : List Mask) : (suffixes ws).headD full = allMask ws := by
  induction ws with
  | nil => rfl
  | cons w ws ih =>
    change w &&& (suffixes ws).headD full = w &&& allMask ws
    rw [ih]

lemma suffixes_cons_tail (ws : List Mask) :
    suffixes ws = allMask ws :: (suffixes ws).tail := by
  cases ws with
  | nil => rfl
  | cons w ws =>
    change (w &&& (suffixes ws).headD full) :: suffixes ws =
      (w &&& allMask ws) :: suffixes ws
    rw [suffixes_head]

lemma rowMasks_nil (goal : Mask) (q : Nat) : rowMasks goal [] q = [] := rfl

lemma rowMasks_cons (acc w : Mask) (ws : List Mask) (q : Nat) :
    rowMasks acc (w :: ws) q =
      (acc &&& allMask (ws.map (same · q)) &&& ~~~same w q) ::
        rowMasks (acc &&& same w q) ws q := by
  simp only [rowMasks, List.map_cons, suffixes, List.tail_cons]
  conv_lhs => rw [suffixes_cons_tail (ws.map (same · q))]
  rfl

lemma rowMasks_length (goal : Mask) (ws : List Mask) (q : Nat) :
    (rowMasks goal ws q).length = ws.length := by
  induction ws generalizing goal with
  | nil => rfl
  | cons w ws ih => simp only [rowMasks_cons, List.length_cons, ih]

lemma same_getLsbD (w : Mask) (q p : Nat) (hp : p < 64) :
    (same w q).getLsbD p = (w.getLsbD p == w.getLsbD q) := by
  cases h : w.getLsbD q <;> simp [same, h, hp]

lemma allMask_getLsbD (ws : List Mask) (q p : Nat) (hp : p < 64) :
    (allMask (ws.map (same · q))).getLsbD p = true ↔
      ∀ w ∈ ws, w.getLsbD p = w.getLsbD q := by
  induction ws with
  | nil =>
    change (~~~(0 : Mask)).getLsbD p = true ↔ ∀ w ∈ ([] : List Mask), _
    simp only [BitVec.getLsbD_not, hp, decide_true, Bool.true_and, List.not_mem_nil, false_implies, forall_const]
    simp [BitVec.getLsbD]
  | cons w ws ih =>
    change (same w q &&& allMask (ws.map (same · q))).getLsbD p = true ↔ _
    rw [BitVec.getLsbD_and, Bool.and_eq_true, same_getLsbD w q p hp, beq_iff_eq, ih]
    simp only [List.mem_cons, forall_eq_or_imp]

lemma not_same_getLsbD (w : Mask) (q p : Nat) (hp : p < 64) :
    (~~~same w q).getLsbD p = true ↔ w.getLsbD p ≠ w.getLsbD q := by
  rw [BitVec.getLsbD_not, same_getLsbD w q p hp]
  cases h₁ : w.getLsbD p <;> cases h₂ : w.getLsbD q <;> simp [hp]

lemma all_getD_iff (ws : List Mask) (P : Mask → Prop) :
    (∀ w ∈ ws, P w) ↔ ∀ j, j < ws.length → P (ws.getD j 0) := by
  constructor
  · intro h j hj
    exact h _ (by simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj])
  · intro h w hw
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hw
    simpa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi] using h i hi

lemma except_zero (w : Mask) (ws : List Mask) (P : Mask → Prop) :
    (∀ j, j < (w :: ws).length → j ≠ 0 → P ((w :: ws).getD j 0)) ↔
      ∀ j, j < ws.length → P (ws.getD j 0) := by
  constructor
  · intro h j hj
    simpa using h (j+1) (by simpa using hj) (by omega)
  · intro h j hj hn
    cases j with
    | zero => contradiction
    | succ j => simpa using h j (by simpa using hj)

lemma except_succ (w : Mask) (ws : List Mask) (P : Mask → Prop) (i : Nat) :
    (∀ j, j < (w :: ws).length → j ≠ i+1 → P ((w :: ws).getD j 0)) ↔
      P w ∧ ∀ j, j < ws.length → j ≠ i → P (ws.getD j 0) := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · simpa using h 0 (by simp) (by omega)
    · intro j hj hn
      simpa using h (j+1) (by simpa using hj) (by omega)
  · rintro ⟨hw,h⟩ j hj hn
    cases j with
    | zero => simpa using hw
    | succ j => simpa using h j (by simpa using hj) (by omega)

lemma rowMasks_spec_getD (goal : Mask) (ws : List Mask) (q p i : Nat)
    (hp : p < 64) (hi : i < ws.length) :
    ((rowMasks goal ws q).getD i 0).getLsbD p = true ↔
      goal.getLsbD p = true ∧
      (ws.getD i 0).getLsbD p ≠ (ws.getD i 0).getLsbD q ∧
      ∀ j, j < ws.length → j ≠ i → (ws.getD j 0).getLsbD p = (ws.getD j 0).getLsbD q := by
  induction ws generalizing goal i with
  | nil => simp at hi
  | cons w ws ih =>
    cases i with
    | zero =>
      rw [rowMasks_cons]
      simp only [List.getD_cons_zero, BitVec.getLsbD_and, Bool.and_eq_true]
      rw [not_same_getLsbD w q p hp, allMask_getLsbD ws q p hp, all_getD_iff]
      rw [except_zero w ws (fun x => x.getLsbD p = x.getLsbD q)]
      tauto
    | succ i =>
      rw [rowMasks_cons]
      simp only [List.getD_cons_succ]
      rw [ih (goal &&& same w q) i (by simpa using hi)]
      rw [except_succ w ws (fun x => x.getLsbD p = x.getLsbD q) i]
      simp only [BitVec.getLsbD_and, Bool.and_eq_true, same_getLsbD w q p hp,
        beq_iff_eq]
      tauto

end Endpoint64
namespace Endpoint64

lemma addRow_length (qbit : Mask) (ps : List Mask) (es : List (Mask × Mask))
    (h : ps.length = es.length) : (addRow qbit ps es).length = es.length := by
  induction ps generalizing es with
  | nil => cases es <;> simp_all [addRow]
  | cons p ps ih =>
    cases es with
    | nil => simp at h
    | cons e es =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at h
      simp [addRow, ih es h]

lemma addRow_getD (qbit : Mask) (ps : List Mask) (es : List (Mask × Mask))
    (i : Nat) (hp : i < ps.length) (he : i < es.length) :
    (addRow qbit ps es).getD i (0,0) =
      ((es.getD i (0,0)).1 ||| ps.getD i 0,
        if ps.getD i 0 == 0 then (es.getD i (0,0)).2
        else (es.getD i (0,0)).2 ||| qbit) := by
  induction ps generalizing es i with
  | nil => simp at hp
  | cons p ps ih =>
    cases es with
    | nil => simp at he
    | cons e es =>
      cases i with
      | zero => simp [addRow]
      | succ i =>
        simp only [List.length_cons, Nat.succ_lt_succ_iff] at hp he
        simpa [addRow] using ih es i hp he

lemma addRow_pos_bit (qbit : Mask) (ps : List Mask) (es : List (Mask × Mask))
    (i p : Nat) (hp : i < ps.length) (he : i < es.length) :
    ((addRow qbit ps es).getD i (0,0)).1.getLsbD p = true ↔
      (es.getD i (0,0)).1.getLsbD p = true ∨ (ps.getD i 0).getLsbD p = true := by
  rw [addRow_getD qbit ps es i hp he]
  simp [BitVec.getLsbD_or]

lemma addRow_neg_bit (qbit : Mask) (ps : List Mask) (es : List (Mask × Mask))
    (i p : Nat) (hp : i < ps.length) (he : i < es.length) :
    ((addRow qbit ps es).getD i (0,0)).2.getLsbD p = true ↔
      (es.getD i (0,0)).2.getLsbD p = true ∨
        ps.getD i 0 ≠ 0 ∧ qbit.getLsbD p = true := by
  rw [addRow_getD qbit ps es i hp he]
  simp only [Prod.snd]
  cases hh : (ps.getD i 0 == 0) with
  | false =>
    have hn : ps.getD i 0 ≠ 0 := beq_eq_false_iff_ne.mp hh
    simp only [hh, Bool.false_eq_true, ite_false, BitVec.getLsbD_or, Bool.or_eq_true]
    tauto
  | true =>
    have hz : ps.getD i 0 = 0 := beq_iff_eq.mp hh
    simp only [hh, Bool.true_eq, ite_true]
    tauto

def accumulate (masks : Nat → List Mask) (rows : List Nat) (es : List (Mask × Mask)) :=
  rows.foldl (fun acc q => addRow ((1 : Mask) <<< q) (masks q) acc) es

lemma accumulate_length (masks : Nat → List Mask) (rows : List Nat) (es : List (Mask × Mask))
    (n : Nat) (he : es.length = n) (hm : ∀ q ∈ rows, (masks q).length = n) :
    (accumulate masks rows es).length = n := by
  induction rows generalizing es with
  | nil => exact he
  | cons q qs ih =>
    change (accumulate masks qs (addRow ((1 : Mask) <<< q) (masks q) es)).length = n
    apply ih
    · rw [addRow_length _ _ _ ((hm q (by simp)).trans he.symm),he]
    · intro r hr; exact hm r (by simp [hr])

lemma accumulate_pos_bit (masks : Nat → List Mask) (rows : List Nat) (es : List (Mask × Mask))
    (n i p : Nat) (he : es.length = n) (hi : i < n)
    (hm : ∀ q ∈ rows, (masks q).length = n) :
    ((accumulate masks rows es).getD i (0,0)).1.getLsbD p = true ↔
      (es.getD i (0,0)).1.getLsbD p = true ∨
        ∃ q ∈ rows, ((masks q).getD i 0).getLsbD p = true := by
  induction rows generalizing es with
  | nil => simp [accumulate]
  | cons q qs ih =>
    have hq := hm q (by simp)
    have htail : ∀ r ∈ qs, (masks r).length = n := fun r hr => hm r (by simp [hr])
    have hlen : (addRow ((1 : Mask) <<< q) (masks q) es).length = n := by
      rw [addRow_length _ _ _ (hq.trans he.symm),he]
    change ((accumulate masks qs (addRow ((1 : Mask) <<< q) (masks q) es)).getD i (0,0)).1.getLsbD p = true ↔ _
    rw [ih _ hlen htail, addRow_pos_bit _ _ _ _ _ (hq ▸ hi) (he ▸ hi)]
    simp only [List.mem_cons]
    aesop

lemma accumulate_neg_bit (masks : Nat → List Mask) (rows : List Nat) (es : List (Mask × Mask))
    (n i p : Nat) (he : es.length = n) (hi : i < n)
    (hm : ∀ q ∈ rows, (masks q).length = n) :
    ((accumulate masks rows es).getD i (0,0)).2.getLsbD p = true ↔
      (es.getD i (0,0)).2.getLsbD p = true ∨
        ∃ q ∈ rows, (masks q).getD i 0 ≠ 0 ∧ ((1 : Mask) <<< q).getLsbD p = true := by
  induction rows generalizing es with
  | nil => simp [accumulate]
  | cons q qs ih =>
    have hq := hm q (by simp)
    have htail : ∀ r ∈ qs, (masks r).length = n := fun r hr => hm r (by simp [hr])
    have hlen : (addRow ((1 : Mask) <<< q) (masks q) es).length = n := by
      rw [addRow_length _ _ _ (hq.trans he.symm),he]
    change ((accumulate masks qs (addRow ((1 : Mask) <<< q) (masks q) es)).getD i (0,0)).2.getLsbD p = true ↔ _
    rw [ih _ hlen htail, addRow_neg_bit _ _ _ _ _ (hq ▸ hi) (he ▸ hi)]
    simp only [List.mem_cons]
    aesop

lemma onebit_bit (p q : Nat) (hp : p < 64) :
    ((1 : Mask) <<< q).getLsbD p = true ↔ p = q := by
  simp [BitVec.getLsbD_shiftLeft, BitVec.getLsbD_one, hp]
  omega

lemma endpoints_length_of (goal : Mask) (ws : List Mask)
    (hm : ∀ q, (rowMasks goal ws q).length = ws.length) :
    (endpoints goal ws).length = ws.length := by
  exact accumulate_length (rowMasks goal ws) _ _ ws.length (by simp) (fun q _ => hm q)

lemma endpoints_pos_raw (goal : Mask) (ws : List Mask) (i p : Nat)
    (hi : i < ws.length) (hm : ∀ q, (rowMasks goal ws q).length = ws.length) :
    ((endpoints goal ws).getD i (0,0)).1.getLsbD p = true ↔
      ∃ q < 64, goal.getLsbD q = false ∧ (rowMasks goal ws q |>.getD i 0).getLsbD p = true := by
  have h := accumulate_pos_bit (rowMasks goal ws)
    ((List.range 64).filter fun q => !goal.getLsbD q) (ws.map fun _ => (0,0))
    ws.length i p (by simp) hi (fun q _ => hm q)
  change ((endpoints goal ws).getD i (0,0)).1.getLsbD p = true ↔ _ at h
  simpa [List.getD_eq_getElem?_getD, hi, and_assoc] using h

lemma endpoints_neg_raw (goal : Mask) (ws : List Mask) (i p : Nat)
    (hi : i < ws.length) (hp : p < 64)
    (hm : ∀ q, (rowMasks goal ws q).length = ws.length) :
    ((endpoints goal ws).getD i (0,0)).2.getLsbD p = true ↔
      goal.getLsbD p = false ∧ (rowMasks goal ws p).getD i 0 ≠ 0 := by
  have h := accumulate_neg_bit (rowMasks goal ws)
    ((List.range 64).filter fun q => !goal.getLsbD q) (ws.map fun _ => (0,0))
    ws.length i p (by simp) hi (fun q _ => hm q)
  change ((endpoints goal ws).getD i (0,0)).2.getLsbD p = true ↔ _ at h
  simp only [onebit_bit p _ hp] at h
  simpa [List.getD_eq_getElem?_getD, hi, hp] using h

end Endpoint64
namespace Endpoint64

lemma getD_ne_iff (ws : List Mask) (hn : ws.Nodup) (i j : Nat)
    (hi : i < ws.length) (hj : j < ws.length) :
    ws.getD i 0 ≠ ws.getD j 0 ↔ i ≠ j := by
  rw [List.getD_eq_getElem _ _ hi, List.getD_eq_getElem _ _ hj]
  exact not_congr hn.getElem_inj_iff

lemma except_index_iff (ws : List Mask) (hn : ws.Nodup) (i : Nat)
    (hi : i < ws.length) (P : Mask → Prop) :
    (∀ j, j < ws.length → j ≠ i → P (ws.getD j 0)) ↔
      ∀ w ∈ ws, w ≠ ws.getD i 0 → P w := by
  constructor
  · intro h w hw hne
    obtain ⟨j,hj,rfl⟩ := List.mem_iff_getElem.mp hw
    have hnij : j ≠ i := by
      intro he
      subst j
      exact hne (List.getD_eq_getElem _ _ hi).symm
    simpa only [List.getD_eq_getElem _ _ hj] using h j hj hnij
  · intro h j hj hne
    exact h _ (by rw [List.getD_eq_getElem _ _ hj]; exact List.getElem_mem hj)
      ((getD_ne_iff ws hn j i hj hi).mpr hne)

lemma rowMasks_unique_bit (goal : Mask) (ws : List Mask) (hn : ws.Nodup)
    (i : Nat) (hi : i < ws.length) (p q : Fin 64) :
    ((rowMasks goal ws q.val).getD i 0)[p.val] = true ↔
      goal[p.val] = true ∧ uniqueSep ws.toFinset (ws.getD i 0) p q := by
  have h := rowMasks_spec_getD goal ws q.val p.val i p.isLt hi
  rw [except_index_iff ws hn i hi (fun w => w.getLsbD p.val = w.getLsbD q.val)] at h
  simpa only [uniqueSep, List.mem_toFinset, BitVec.getLsbD_eq_getElem p.isLt, BitVec.getLsbD_eq_getElem q.isLt] using h

lemma endpoints_positive_bit (goal : Mask) (ws : List Mask) (hn : ws.Nodup)
    (i : Nat) (hi : i < ws.length) (p : Fin 64) :
    ((endpoints goal ws).getD i (0,0)).1[p.val] = true ↔
      positiveEndpoint goal ws.toFinset (ws.getD i 0) p := by
  rw [← BitVec.getLsbD_eq_getElem, endpoints_pos_raw goal ws i p.val hi (rowMasks_length goal ws)]
  constructor
  · rintro ⟨q,hq,hfalse,hrow⟩
    have hr := (rowMasks_unique_bit goal ws hn i hi p ⟨q,hq⟩).mp
      (by simpa only [BitVec.getLsbD_eq_getElem p.isLt] using hrow)
    exact ⟨hr.1,⟨q,hq⟩,by simpa only [BitVec.getLsbD_eq_getElem hq] using hfalse,hr.2⟩
  · rintro ⟨hp,q,hq,hu⟩
    refine ⟨q.val,q.isLt,by simpa only [BitVec.getLsbD_eq_getElem q.isLt] using hq,?_⟩
    have hr := (rowMasks_unique_bit goal ws hn i hi p q).mpr ⟨hp,hu⟩
    simpa only [BitVec.getLsbD_eq_getElem p.isLt] using hr

lemma endpoints_negative_bit (goal : Mask) (ws : List Mask) (hn : ws.Nodup)
    (i : Nat) (hi : i < ws.length) (q : Fin 64) :
    ((endpoints goal ws).getD i (0,0)).2[q.val] = true ↔
      negativeEndpoint goal ws.toFinset (ws.getD i 0) q := by
  rw [← BitVec.getLsbD_eq_getElem,
    endpoints_neg_raw goal ws i q.val hi q.isLt (rowMasks_length goal ws)]
  simp only [EndpointSpec.nonzero_iff_bit, negativeEndpoint, BitVec.getLsbD_eq_getElem q.isLt]
  simp_rw [rowMasks_unique_bit goal ws hn i hi]

lemma edge_endpoints_correct (goal : Mask) (ws : List Mask) (hn : ws.Nodup)
    (i j : Nat) (hi : i < ws.length) (hj : j < ws.length) (hij : i ≠ j) :
    edge (ws.getD i 0) (ws.getD j 0)
      ((endpoints goal ws).getD i (0,0)) ((endpoints goal ws).getD j (0,0)) = true ↔
      criticalPair goal ws.toFinset (ws.getD i 0) (ws.getD j 0) := by
  apply edge_correct goal ws.toFinset
  · exact List.mem_toFinset.mpr (by rw [List.getD_eq_getElem _ _ hi]; exact List.getElem_mem hi)
  · exact List.mem_toFinset.mpr (by rw [List.getD_eq_getElem _ _ hj]; exact List.getElem_mem hj)
  · exact (getD_ne_iff ws hn i j hi hj).mpr hij
  · exact endpoints_positive_bit goal ws hn i hi
  · exact endpoints_positive_bit goal ws hn j hj
  · exact endpoints_negative_bit goal ws hn i hi
  · exact endpoints_negative_bit goal ws hn j hj

end Endpoint64

namespace Endpoint64

lemma selected_bits {α : Type} (test : α → Bool) (index : α → Nat)
    (xs : List α) (acc p : Nat) :
    (xs.foldl (fun mask x => if test x then mask ||| (1 <<< index x) else mask) acc).testBit p = true ↔
      acc.testBit p = true ∨ ∃ x ∈ xs, test x = true ∧ index x = p := by
  induction xs generalizing acc with
  | nil => simp
  | cons x xs ih =>
    rw [List.foldl_cons, ih]
    cases ht : test x <;>
      simp only [ht, Bool.true_eq, Bool.false_eq_true, ite_true, ite_false,
        Nat.testBit_or, Nat.one_shiftLeft, Nat.testBit_two_pow, Bool.or_eq_true,
        decide_eq_true_eq, List.mem_cons]
    all_goals aesop

lemma adjacencyRow_bit (i j : Nat) (a : Mask × (Mask × Mask))
    (others : List (Mask × (Mask × Mask))) (hj : j < others.length) :
    (adjacencyRow i a others).testBit j = true ↔
      i ≠ j ∧ edge a.1 (others.getD j (0,(0,0))).1 a.2 (others.getD j (0,(0,0))).2 = true := by
  have h := selected_bits
    (fun x : (Mask × (Mask × Mask)) × Nat => i != x.2 && edge a.1 x.1.1 a.2 x.1.2)
    Prod.snd others.zipIdx 0 j
  change (adjacencyRow i a others).testBit j = true ↔ _ at h
  simp only [List.exists_mem_zipIdx', Bool.and_eq_true, bne_iff_ne] at h
  simpa [hj, List.getD_eq_getElem _ _ hj] using h

lemma endpoints_length (goal : Mask) (ws : List Mask) :
    (endpoints goal ws).length = ws.length :=
  endpoints_length_of goal ws (rowMasks_length goal ws)

lemma graph_length (goal : Mask) (ws : List Mask) : (graph goal ws).length = ws.length := by
  simp [graph, endpoints_length]

lemma zip_endpoints_getD (goal : Mask) (ws : List Mask) (i : Nat) (hi : i < ws.length) :
    (ws.zip (endpoints goal ws)).getD i (0,(0,0)) =
      (ws.getD i 0, (endpoints goal ws).getD i (0,0)) := by
  have hz : i < (ws.zip (endpoints goal ws)).length := by simp [endpoints_length,hi]
  have he : i < (endpoints goal ws).length := by simpa [endpoints_length] using hi
  rw [List.getD_eq_getElem _ _ hz, List.getD_eq_getElem _ _ hi, List.getD_eq_getElem _ _ he]
  simp only [List.getElem_zip]

lemma graph_getD (goal : Mask) (ws : List Mask) (i : Nat) (hi : i < ws.length) :
    (graph goal ws).getD i 0 =
      adjacencyRow i (ws.getD i 0, (endpoints goal ws).getD i (0,0))
        (ws.zip (endpoints goal ws)) := by
  have hg : i < (graph goal ws).length := by simpa [graph_length] using hi
  rw [List.getD_eq_getElem _ _ hg]
  simp only [graph, List.getElem_map, List.getElem_zipIdx, Nat.zero_add]
  have hz : i < (ws.zip (endpoints goal ws)).length := by simp [endpoints_length,hi]
  rw [← List.getD_eq_getElem _ _ hz, zip_endpoints_getD goal ws i hi]

lemma graph_bit (goal : Mask) (ws : List Mask) (hn : ws.Nodup)
    (i j : Nat) (hi : i < ws.length) (hj : j < ws.length) :
    ((graph goal ws).getD i 0).testBit j = true ↔
      criticalPair goal ws.toFinset (ws.getD i 0) (ws.getD j 0) := by
  rw [graph_getD goal ws i hi, adjacencyRow_bit]
  · rw [zip_endpoints_getD goal ws j hj]
    simp only [Prod.fst, Prod.snd]
    by_cases hij : i = j
    · subst j
      simp [criticalPair]
    · rw [edge_endpoints_correct goal ws hn i j hi hj hij]
      constructor
      · exact And.right
      · intro h; exact ⟨hij,h⟩
  · simpa [endpoints_length] using hj

end Endpoint64


end EndpointGraphBase

namespace Endpoint64

lemma graph_colorable_of_live {goal g : Mask} {k : Nat} {ws : List Mask}
    (hg : g = goal ∨ g = ~~~goal) (hn : ws.Nodup)
    (hl : live basicOps g k ws.toFinset) :
    graphColorable (graph goal ws) (k + 2 - ws.length) := by
  obtain ⟨color, hbound, hproper⟩ := live_criticalPair_coloring hl hg
  have hm {i : Nat} (hi : i < ws.length) : ws.getD i 0 ∈ ws.toFinset := by
    apply List.mem_toFinset.mpr
    rw [List.getD_eq_getElem _ _ hi]
    exact List.getElem_mem hi
  refine ⟨fun i => color (ws.getD i 0), ?_, ?_⟩
  · intro i hi
    have hi' : i < ws.length := by simpa only [graph_length] using hi
    simpa only [List.toFinset_card_of_nodup hn] using hbound _ (hm hi')
  · intro i hi j hj he
    have hi' : i < ws.length := by simpa only [graph_length] using hi
    have hj' : j < ws.length := by simpa only [graph_length] using hj
    exact hproper _ _ ((graph_bit goal ws hn i j hi' hj').mp he)

def admissible (goal : Mask) (k : Nat) (ws : List Mask) : Bool :=
  let colors := k + 2 - ws.length
  if ws.length > k + 1 then false
  else if colors > 4 then true
  else if ws.length ≤ colors then true
  else graphColorDegreeFast (graph goal ws) colors

lemma admissible_complete {goal g : Mask} (hg : g = goal ∨ g = ~~~goal)
    (k : Nat) (ws : List Mask) (hn : ws.Nodup)
    (hl : live basicOps g k ws.toFinset) : admissible goal k ws = true := by
  have hc := live_card hl
  rw [List.toFinset_card_of_nodup hn] at hc
  unfold admissible
  dsimp only
  simp only [show ¬ws.length > k + 1 by omega, ite_false]
  split_ifs
  · rfl
  · rfl
  · exact graphColorDegreeFast_complete (graph_colorable_of_live hg hn hl)

lemma no_live_of_run {goal g : Mask} (hg : g = goal ∨ g = ~~~goal)
    (threshold k : Nat) (ws : List Mask) (hn : ws.Nodup)
    (rejected : MemoPruned.runFrom threshold (admissible goal) (MemoActualPruned.done goal)
      (MemoActualPruned.children goal (SearchKernel.falseRows goal)) k ws = false) :
    ¬live basicOps g k ws.toFinset := by
  intro hl
  have found := MemoActualPruned.run_complete hg (admissible goal)
    (admissible_complete hg) (SearchKernel.falseRows goal) threshold k ws hn hl
  rw [rejected] at found
  contradiction

lemma no_build_of_search {goal g : Mask} (hg : g = goal ∨ g = ~~~goal)
    (threshold k : Nat) (ws : List Mask) (hn : ws.Nodup)
    (rejected : MemoActualPruned.search goal (admissible goal) threshold k ws = false) :
    ¬build basicOps g k ws.toFinset :=
  MemoActualPruned.no_build hg (admissible goal) (admissible_complete hg)
    threshold k ws hn rejected

end Endpoint64



namespace Endpoint64

def hasEdge (goal : Mask) (ws : List Mask) : Bool :=
  let es := endpoints goal ws
  (List.range ws.length).any fun i => (List.range i).any fun j =>
    edge (ws.getD i 0) (ws.getD j 0) (es.getD i (0,0)) (es.getD j (0,0))

lemma hasEdge_false {goal : Mask} {ws : List Mask} (hn : ws.Nodup)
    (hc : graphColorable (graph goal ws) 1) : hasEdge goal ws = false := by
  apply Bool.eq_false_iff.mpr
  intro he
  obtain ⟨i,hi,hrow⟩ := List.any_eq_true.mp he
  obtain ⟨j,hj,hedge⟩ := List.any_eq_true.mp hrow
  have hi' : i < ws.length := List.mem_range.mp hi
  have hj' : j < i := List.mem_range.mp hj
  have hjlen : j < ws.length := hj'.trans hi'
  have hcritical := (edge_endpoints_correct goal ws hn i j hi' hjlen (by omega)).mp hedge
  have hbit := (graph_bit goal ws hn i j hi' hjlen).mpr hcritical
  obtain ⟨color,hbound,hproper⟩ := hc
  have hiG : i < (graph goal ws).length := by simpa only [graph_length] using hi'
  have hjG : j < (graph goal ws).length := by simpa only [graph_length] using hjlen
  have hne := hproper i hiG j hjG hbit
  have hbi := hbound i hiG
  have hbj := hbound j hjG
  omega

def admissibleFast (goal : Mask) (k : Nat) (ws : List Mask) : Bool :=
  let colors := k + 2 - ws.length
  if ws.length > k + 1 then false
  else if colors > 4 then true
  else if ws.length ≤ colors then true
  else if colors = 1 then !hasEdge goal ws
  else graphColorDegreeFast (graph goal ws) colors

lemma admissibleFast_complete {goal g : Mask} (hg : g = goal ∨ g = ~~~goal)
    (k : Nat) (ws : List Mask) (hn : ws.Nodup)
    (hl : live basicOps g k ws.toFinset) : admissibleFast goal k ws = true := by
  have hc := live_card hl
  rw [List.toFinset_card_of_nodup hn] at hc
  unfold admissibleFast
  dsimp only
  simp only [show ¬ws.length > k + 1 by omega, ite_false]
  split_ifs with hlarge hsmall hone
  · rfl
  · rfl
  · have hgcol := graph_colorable_of_live hg hn hl
    rw [hone] at hgcol
    simp only [hasEdge_false hn hgcol, Bool.not_false]
  · exact graphColorDegreeFast_complete (graph_colorable_of_live hg hn hl)

lemma no_live_of_runFast {goal g : Mask} (hg : g = goal ∨ g = ~~~goal)
    (threshold k : Nat) (ws : List Mask) (hn : ws.Nodup)
    (rejected : MemoPruned.runFrom threshold (admissibleFast goal) (MemoActualPruned.done goal)
      (MemoActualPruned.children goal (SearchKernel.falseRows goal)) k ws = false) :
    ¬live basicOps g k ws.toFinset := by
  intro hl
  have found := MemoActualPruned.run_complete hg (admissibleFast goal)
    (admissibleFast_complete hg) (SearchKernel.falseRows goal) threshold k ws hn hl
  rw [rejected] at found
  contradiction

lemma no_build_of_searchFast {goal g : Mask} (hg : g = goal ∨ g = ~~~goal)
    (threshold k : Nat) (ws : List Mask) (hn : ws.Nodup)
    (rejected : MemoActualPruned.search goal (admissibleFast goal) threshold k ws = false) :
    ¬build basicOps g k ws.toFinset :=
  MemoActualPruned.no_build hg (admissibleFast goal) (admissibleFast_complete hg)
    threshold k ws hn rejected

end Endpoint64


namespace PNGraphBridge

variable {width : Nat}

def pat (ws : List (BitVec width)) (r : Fin width) : Nat :=
  (BitVec.ofBoolListLE (ws.map (fun w => w[r.val]))).toNat

lemma pat_bit (ws : List (BitVec width)) (r : Fin width) (i : Nat) :
    (pat ws r).testBit i = (ws.getD i 0)[r.val] := by
  simp only [pat, BitVec.testBit_toNat, BitVec.getLsbD_ofBoolListLE]
  simpa using
    (List.getD_map ws (0 : BitVec width) (n := i) (fun w => w[r.val]))

lemma xor_uniqueSep (ws : List (BitVec width)) (i : Nat)
    (p q : Fin width) (he : pat ws q = pat ws p ^^^ 2^i) :
    uniqueSep ws.toFinset (ws.getD i 0) p q := by
  have bits (j : Nat) :
      (ws.getD j 0)[q.val] = ((ws.getD j 0)[p.val] ^^ decide (i = j)) := by
    have h := congrArg (fun n : Nat => n.testBit j) he
    simpa only [pat_bit, Nat.testBit_xor, Nat.testBit_two_pow] using h
  constructor
  · have h := bits i
    simp only [decide_true, Bool.bne_true] at h
    rw [h]
    cases (ws.getD i 0)[p.val] <;> decide
  · intro w hw hne
    obtain ⟨j,hj,rfl⟩ := List.mem_iff_getElem.mp (List.mem_toFinset.mp hw)
    have hji : i ≠ j := by
      intro h
      subst j
      exact hne (List.getD_eq_getElem _ _ hj).symm
    have h := bits j
    simp only [hji, decide_false, Bool.bne_false] at h
    simpa only [List.getD_eq_getElem _ _ hj] using h.symm

lemma uniqueSep_swap {S : Finset (BitVec width)} {a : BitVec width}
    {p q : Fin width} (h : uniqueSep S a p q) : uniqueSep S a q p := by
  exact ⟨h.1.symm, fun w hw hne => (h.2 w hw hne).symm⟩

lemma getD_ne (ws : List (BitVec width)) (hn : ws.Nodup) (i j : Nat)
    (hi : i < ws.length) (hj : j < ws.length) (hne : i ≠ j) :
    ws.getD i 0 ≠ ws.getD j 0 := by
  rw [List.getD_eq_getElem _ _ hi, List.getD_eq_getElem _ _ hj]
  exact (not_congr hn.getElem_inj_iff).mpr hne

lemma pat_lt (ws : List (BitVec width)) (r : Fin width) :
    pat ws r < 2^ws.length := by
  simpa only [pat, List.length_map] using
    (BitVec.ofBoolListLE (ws.map (fun w => w[r.val]))).isLt

lemma witness_criticalPair (goal : BitVec width) (ws : List (BitVec width))
    (hn : ws.Nodup) (i j : Nat) (hi : i < ws.length) (hj : j < ws.length)
    (hij : i ≠ j) (P N p q : Nat)
    (hP : ∀ x, P.testBit x = true →
      ∃ r : Fin width, goal[r.val] = true ∧ pat ws r = x)
    (hN : ∀ x, N.testBit x = true →
      ∃ r : Fin width, goal[r.val] = false ∧ pat ws r = x)
    (hp : P.testBit p = true) (hq : N.testBit q = true)
    (hpi : N.testBit (p ^^^ 2^i) = true) (hpj : N.testBit (p ^^^ 2^j) = true)
    (hqi : P.testBit (q ^^^ 2^i) = true) (hqj : P.testBit (q ^^^ 2^j) = true)
    (hphasei : p.testBit i ≠ q.testBit i)
    (hphasej : p.testBit j ≠ q.testBit j) :
    criticalPair goal ws.toFinset (ws.getD i 0) (ws.getD j 0) := by
  obtain ⟨rp,hrp,erp⟩ := hP p hp
  obtain ⟨rq,hrq,erq⟩ := hN q hq
  obtain ⟨ri,hri,eri⟩ := hN _ hpi
  obtain ⟨rj,hrj,erj⟩ := hN _ hpj
  obtain ⟨si,hsi,esi⟩ := hP _ hqi
  obtain ⟨sj,hsj,esj⟩ := hP _ hqj
  have ui := xor_uniqueSep ws i rp ri (by rw [erp]; exact eri)
  have uj := xor_uniqueSep ws j rp rj (by rw [erp]; exact erj)
  have vi := uniqueSep_swap (xor_uniqueSep ws i rq si (by rw [erq]; exact esi))
  have vj := uniqueSep_swap (xor_uniqueSep ws j rq sj (by rw [erq]; exact esj))
  have mem (a : Nat) (ha : a < ws.length) : ws.getD a 0 ∈ ws.toFinset := by
    apply List.mem_toFinset.mpr
    rw [List.getD_eq_getElem _ _ ha]
    exact List.getElem_mem ha
  apply (criticalPair_iff_endpointWitness goal ws.toFinset _ _).mpr
  refine ⟨mem i hi, mem j hj, getD_ne ws hn i j hi hj hij,
    rp,rq,⟨hrp,ri,hri,ui⟩,⟨hrp,rj,hrj,uj⟩,
    ⟨hrq,si,hsi,vi⟩,⟨hrq,sj,hsj,vj⟩,?_,?_⟩
  · simpa only [← pat_bit, erp, erq] using hphasei
  · simpa only [← pat_bit, erp, erq] using hphasej

def maskWitness (P N : Nat) (flip : Nat → Nat → Nat) (i j : Nat) : Prop :=
  ∃ p q,
    (P &&& flip i N).testBit p = true ∧ (P &&& flip j N).testBit p = true ∧
    (N &&& flip i P).testBit q = true ∧ (N &&& flip j P).testBit q = true ∧
    p.testBit i ≠ q.testBit i ∧ p.testBit j ≠ q.testBit j

lemma maskWitness_criticalPair (goal : BitVec width) (ws : List (BitVec width))
    (hn : ws.Nodup) (i j : Nat) (hi : i < ws.length) (hj : j < ws.length)
    (hij : i ≠ j) (P N : Nat) (flip : Nat → Nat → Nat)
    (hP : ∀ x, P.testBit x = true →
      ∃ r : Fin width, goal[r.val] = true ∧ pat ws r = x)
    (hN : ∀ x, N.testBit x = true →
      ∃ r : Fin width, goal[r.val] = false ∧ pat ws r = x)
    (hflip : ∀ a, a < ws.length → ∀ B x, x < 2^ws.length →
      (flip a B).testBit x = B.testBit (x ^^^ 2^a))
    (h : maskWitness P N flip i j) :
    criticalPair goal ws.toFinset (ws.getD i 0) (ws.getD j 0) := by
  obtain ⟨p,q,hpi,hpj,hqi,hqj,phasei,phasej⟩ := h
  simp only [Nat.testBit_and, Bool.and_eq_true] at hpi hpj hqi hqj
  have hpbound : p < 2^ws.length := by
    obtain ⟨r,_,hr⟩ := hP p hpi.1
    rw [← hr]
    exact pat_lt ws r
  have hqbound : q < 2^ws.length := by
    obtain ⟨r,_,hr⟩ := hN q hqi.1
    rw [← hr]
    exact pat_lt ws r
  rw [hflip i hi N p hpbound] at hpi
  rw [hflip j hj N p hpbound] at hpj
  rw [hflip i hi P q hqbound] at hqi
  rw [hflip j hj P q hqbound] at hqj
  exact witness_criticalPair goal ws hn i j hi hj hij P N p q hP hN
    hpi.1 hqi.1 hpi.2 hpj.2 hqi.2 hqj.2 phasei phasej

lemma graph_colorable_of_live {goal g : BitVec width} {k : Nat}
    {ws : List (BitVec width)} (hg : g = goal ∨ g = ~~~goal) (hn : ws.Nodup)
    (hl : live basicOps g k ws.toFinset) (P N : Nat) (flip : Nat → Nat → Nat)
    (hP : ∀ x, P.testBit x = true →
      ∃ r : Fin width, goal[r.val] = true ∧ pat ws r = x)
    (hN : ∀ x, N.testBit x = true →
      ∃ r : Fin width, goal[r.val] = false ∧ pat ws r = x)
    (hflip : ∀ a, a < ws.length → ∀ B x, x < 2^ws.length →
      (flip a B).testBit x = B.testBit (x ^^^ 2^a))
    (graph : List Nat) (hlen : graph.length = ws.length)
    (hedge : ∀ i, i < ws.length → ∀ j, j < ws.length →
      (graph.getD i 0).testBit j = true → i ≠ j ∧ maskWitness P N flip i j) :
    graphColorable graph (k + 2 - ws.length) := by
  obtain ⟨color,hbound,hproper⟩ := live_criticalPair_coloring hl hg
  have mem (a : Nat) (ha : a < ws.length) : ws.getD a 0 ∈ ws.toFinset := by
    apply List.mem_toFinset.mpr
    rw [List.getD_eq_getElem _ _ ha]
    exact List.getElem_mem ha
  refine ⟨fun i => color (ws.getD i 0), ?_, ?_⟩
  · intro i hi
    rw [hlen] at hi
    simpa only [List.toFinset_card_of_nodup hn] using hbound _ (mem i hi)
  · intro i hi j hj he
    rw [hlen] at hi hj
    obtain ⟨hne,hw⟩ := hedge i hi j hj he
    exact hproper _ _ (maskWitness_criticalPair goal ws hn i j hi hj hne P N flip
      hP hN hflip hw)

end PNGraphBridge

end PEqualNP.Outside.L_meta_10760
