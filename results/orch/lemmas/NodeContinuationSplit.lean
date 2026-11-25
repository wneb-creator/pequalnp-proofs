import ContinuationSplit

namespace PEqualNP.Outside.L_meta_10760_aux

lemma ins_cons_split (o w : W) (v : List W) (F : List W → Bool) :
    ins o (w :: v) F = Bool.rec (motive := fun _ => Bool)
      (ins o v (fun r => F (w :: r)))
      (Bool.rec (motive := fun _ => Bool) (F (o :: w :: v)) false
        (Nat.beq o.s w.s)) (Nat.ble w.s o.s) := rfl

lemma ins_or_split (o : W) (v : List W) (F G : List W → Bool) :
    ins o v (fun r => F r || G r) = (ins o v F || ins o v G) := by
  induction v generalizing F G with
  | nil => rfl
  | cons w v ih =>
    cases h₁ : Nat.ble w.s o.s <;> cases h₂ : Nat.beq o.s w.s <;>
      simp only [ins_cons_split, h₁, h₂, ih, Bool.or_false]

lemma put_or_split (m s x y : ℕ) (v : List W) (F G : List W → Bool) :
    put m s x y v (fun r => F r || G r) = (put m s x y v F || put m s x y v G) := by
  simp only [put, st_eq]
  cases Nat.beq s 0 <;> cases Nat.beq s m <;>
    simp only [ins_or_split, Bool.or_false]

lemma kids_child_or_split (F G : ℕ → List W → Bool)
    (g e n z x y a c : ℕ) (oa oc : Bool) (mk : (List W → Bool) → Bool)
    (hmk : ∀ A B : List W → Bool, mk (fun r => A r || B r) = (mk A || mk B)) :
    kids (child (fun z r => F z r || G z r) g) e n z x y a c oa oc mk =
      (kids (child F g) e n z x y a c oa oc mk ||
        kids (child G g) e n z x y a c oa oc mk) := by
  have hr (a b : ℕ) : ∀ A B : List W → Bool,
      mk (fun r => rm a b r (fun s => A s || B s)) =
        (mk (fun r => rm a b r A) || mk (fun r => rm a b r B)) := by
    intro A B
    simp_rw [rm_or_split]
    exact hmk _ _
  have h₀ (z : ℕ) := child_or_split F G g z mk hmk
  have h₁ (z : ℕ) := child_or_split F G g z (fun h => mk (fun r => rm a a r h)) (hr a a)
  have h₂ (z : ℕ) := child_or_split F G g z (fun h => mk (fun r => rm c c r h)) (hr c c)
  have h₃ (z : ℕ) := child_or_split F G g z (fun h => mk (fun r => rm a c r h)) (hr a c)
  simp only [kids]
  simp_rw [h₀, h₁, h₂, h₃]
  cases oa <;> cases oc <;> cases Nat.ble (Nat.succ n) e <;>
    cases Nat.ble (Nat.succ (Nat.succ n)) e <;>
      simp only [rec_branch_or_simple, Bool.false_or, Bool.or_false,
        Bool.or_assoc, Bool.or_left_comm, Bool.or_comm]

lemma mid_or_split (F G : ℕ → List W → Bool) (m g e n z : ℕ)
    (v : List W) (a c : W) (da dc s x y : ℕ) :
    mid (fun z r => F z r || G z r) m g e n z v a c da dc s x y =
      (mid F m g e n z v a c da dc s x y || mid G m g e n z v a c da dc s x y) := by
  simp only [mid, st_eq]
  rw [kids_child_or_split F G]
  · exact rec_guard_distrib _ _ _
  · exact put_or_split m s x y v

lemma modeF_or_split (H J : W → W → ℕ → ℕ → ℕ → ℕ → ℕ → Bool)
    (n e : ℕ) (a c : W) (da dc s x y : ℕ) :
    modeF n e (fun a c da dc s x y => H a c da dc s x y || J a c da dc s x y)
      a c da dc s x y =
      (modeF n e H a c da dc s x y || modeF n e J a c da dc s x y) := by
  cases h₁ : Nat.ble n e <;> cases h₂ : Nat.ble (Nat.succ n) e <;>
    simp only [modeF, h₁, h₂, Bool.cond_false, Bool.cond_true, f0, f1, f2]
  all_goals first | rfl | exact rec_guard_distrib _ _ _

lemma pair_or_split (H J : W → W → ℕ → ℕ → ℕ → ℕ → ℕ → Bool) (a c : X) :
    pair (fun a c da dc s x y => H a c da dc s x y || J a c da dc s x y) a c =
      (pair H a c || pair J a c) := by
  cases a
  cases c
  simp only [pair, rec_branch_or_simple]
  ac_rfl

lemma node_or_split (F G : ℕ → List W → Bool) (d : Bool) (l m g e n z : ℕ)
    (v : List W) (go : (X → X → Bool) → List X → Bool)
    (hgo : ∀ H J xs, go (fun a c => H a c || J a c) xs = (go H xs || go J xs)) :
    node (fun z r => F z r || G z r) d l m g e n z v go =
      (node F d l m g e n z v go || node G d l m g e n z v go) := by
  simp only [node_eq]
  have hm : mid (fun z r => F z r || G z r) m g e (Nat.pred n) z v =
      (fun a c da dc s x y => mid F m g e (Nat.pred n) z v a c da dc s x y ||
        mid G m g e (Nat.pred n) z v a c da dc s x y) := by
    funext a c da dc s x y
    exact mid_or_split F G m g e (Nat.pred n) z v a c da dc s x y
  rw [hm]
  have hmode (H J : W → W → ℕ → ℕ → ℕ → ℕ → ℕ → Bool) :
      modeF n e (fun a c da dc s x y => H a c da dc s x y || J a c da dc s x y) =
        (fun a c da dc s x y => modeF n e H a c da dc s x y ||
          modeF n e J a c da dc s x y) := by
    funext a c da dc s x y
    exact modeF_or_split H J n e a c da dc s x y
  rw [hmode]
  have hp (H J : W → W → ℕ → ℕ → ℕ → ℕ → ℕ → Bool) :
      pair (fun a c da dc s x y => H a c da dc s x y || J a c da dc s x y) =
        (fun a c => pair H a c || pair J a c) := by
    funext a c
    exact pair_or_split H J a c
  rw [hp]
  exact hgo _ _ _

lemma rec_false_distrib (a b c : Bool) :
    Bool.rec (motive := fun _ => Bool) (a || b) false c =
      (Bool.rec (motive := fun _ => Bool) a false c ||
        Bool.rec (motive := fun _ => Bool) b false c) := by
  cases c <;> simp

lemma pairs_cons_split (H : X → X → Bool) (a : X) (xs : List X) :
    pairs H (a :: xs) = (scan (H a) xs || pairs H xs) := by
  exact rec_branch_or_simple _ _

lemma pairs_or_split (H J : X → X → Bool) (xs : List X) :
    pairs (fun a c => H a c || J a c) xs = (pairs H xs || pairs J xs) := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    simp only [pairs_cons_split, scan_or_split, ih]
    ac_rfl

lemma pairsP_or_split (q : ℕ) (H J : X → X → Bool) (xs : List X) :
    pairsP q (fun a c => H a c || J a c) xs = (pairsP q H xs || pairsP q J xs) := by
  simp only [pairsP]
  simp_rw [rec_false_distrib, scan_or_split, rec_guard_distrib, scan_or_split]

lemma pairsQ_or_split (q q' : ℕ) (H J : X → X → Bool) (xs : List X) :
    pairsQ q q' (fun a c => H a c || J a c) xs = (pairsQ q q' H xs || pairsQ q q' J xs) := by
  simp only [pairsQ]
  simp_rw [rec_guard_distrib, scan_or_split, rec_guard_distrib, scan_or_split]

lemma pairsN_or_split (H J : X → X → Bool) (xs : List X) :
    pairsN (fun a c => H a c || J a c) xs = (pairsN H xs || pairsN J xs) := by
  simp only [pairsN, rec_branch_or_simple]
  simp_rw [pairs_or_split, scan_or_split]
  ac_rfl

lemma pairsS_or_split (H J : X → X → Bool) (xs : List X) :
    pairsS (fun a c => H a c || J a c) xs = (pairsS H xs || pairsS J xs) := by
  exact pairs_or_split H J (fs xs)

lemma pairsC_cons_split (K : ℕ) (H : X → X → Bool) (a : X) (xs : List X) :
    pairsC K H (a :: xs) =
      (scan (fun c => Bool.rec (motive := fun _ => Bool) false (H a c)
        (hb K (Nat.add a.s c.s))) xs || pairsC K H xs) := by
  exact rec_branch_or_simple _ _

lemma pairsC_or_split (K : ℕ) (H J : X → X → Bool) (xs : List X) :
    pairsC K (fun a c => H a c || J a c) xs = (pairsC K H xs || pairsC K J xs) := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    simp only [pairsC_cons_split]
    simp_rw [rec_guard_distrib, scan_or_split]
    rw [ih]
    ac_rfl

end PEqualNP.Outside.L_meta_10760_aux
