import Mathlib.Data.List.GetD

namespace PEqualNP.Outside.L_meta_4930

def normStep (ws : List Bool) (g : Bool × ℕ × ℕ) : List Bool :=
  ws ++ [if g.1 then ws.getD g.2.1 false && ws.getD g.2.2 false
    else ws.getD g.2.1 false || ws.getD g.2.2 false]

def normRun (gs : List (Bool × ℕ × ℕ)) (ws : List Bool) : List Bool :=
  gs.foldl normStep ws

def normStateLE (ws vs : List Bool) : Prop :=
  ws.length = vs.length ∧ ∀ i, ws.getD i false ≤ vs.getD i false

lemma normStateLE_refl (ws : List Bool) : normStateLE ws ws := by
  have refl : ∀ b : Bool, b ≤ b := by decide
  exact ⟨rfl, fun _ => refl _⟩

lemma normStateLE_append {ws vs : List Bool} {b c : Bool}
    (h : normStateLE ws vs) (hbc : b ≤ c) :
    normStateLE (ws ++ [b]) (vs ++ [c]) := by
  refine ⟨by simp [h.1], ?_⟩
  intro i
  by_cases hi : i < ws.length
  · rw [List.getD_append _ _ _ _ hi,
      List.getD_append _ _ _ _ (by simpa [← h.1] using hi)]
    exact h.2 i
  · have hwi : ws.length ≤ i := Nat.le_of_not_gt hi
    rw [List.getD_append_right _ _ _ _ hwi,
      List.getD_append_right _ _ _ _ (by simpa [← h.1] using hwi), ← h.1]
    cases i - ws.length with
    | zero => simpa using hbc
    | succ k => simp

lemma normBinary_mono : ∀ op a b c d : Bool, a ≤ c → b ≤ d →
    (if op then a && b else a || b) ≤ (if op then c && d else c || d) := by
  decide

lemma normStep_mono {ws vs : List Bool} (h : normStateLE ws vs)
    (g : Bool × ℕ × ℕ) : normStateLE (normStep ws g) (normStep vs g) := by
  apply normStateLE_append h
  exact normBinary_mono g.1 _ _ _ _ (h.2 g.2.1) (h.2 g.2.2)

lemma normRun_mono (gs : List (Bool × ℕ × ℕ)) {ws vs : List Bool}
    (h : normStateLE ws vs) : normStateLE (normRun gs ws) (normRun gs vs) := by
  induction gs generalizing ws vs with
  | nil => exact h
  | cons g gs ih => exact ih (normStep_mono h g)

lemma normRun_force_false_le (gs : List (Bool × ℕ × ℕ)) (ws : List Bool)
    (b : Bool) (out : ℕ) :
    (normRun gs (ws ++ [false])).getD out false ≤
      (normRun gs (ws ++ [b])).getD out false := by
  exact (normRun_mono gs
    (normStateLE_append (normStateLE_refl ws) (Bool.false_le b))).2 out

lemma normRun_le_force_true (gs : List (Bool × ℕ × ℕ)) (ws : List Bool)
    (b : Bool) (out : ℕ) :
    (normRun gs (ws ++ [b])).getD out false ≤
      (normRun gs (ws ++ [true])).getD out false := by
  exact (normRun_mono gs
    (normStateLE_append (normStateLE_refl ws) (Bool.le_true b))).2 out

lemma normSubstitute_preserves_samples {R : Type} (gs : List (Bool × ℕ × ℕ))
    (ws : R → List Bool) (b replacement target : R → Bool) (out : ℕ)
    (hle : ∀ r, replacement r ≤ b r)
    (hpos : ∀ r, target r = true → replacement r = b r)
    (heval : ∀ r, (normRun gs (ws r ++ [b r])).getD out false = target r) :
    ∀ r, (normRun gs (ws r ++ [replacement r])).getD out false = target r := by
  intro r
  cases ht : target r with
  | true => simpa [ht, hpos r ht] using heval r
  | false =>
    have hm := (normRun_mono gs
      (normStateLE_append (normStateLE_refl (ws r)) (hle r))).2 out
    rw [heval r, ht] at hm
    have eqFalse : ∀ a : Bool, a ≤ false → a = false := by decide
    exact eqFalse _ hm

lemma normForceFalse_preserves_samples {R : Type} (gs : List (Bool × ℕ × ℕ))
    (ws : R → List Bool) (b target : R → Bool) (out : ℕ)
    (hzero : ∀ r, target r = true → b r = false)
    (heval : ∀ r, (normRun gs (ws r ++ [b r])).getD out false = target r) :
    ∀ r, (normRun gs (ws r ++ [false])).getD out false = target r := by
  intro r
  cases ht : target r with
  | true => simpa [ht, hzero r ht] using heval r
  | false =>
    have hle := normRun_force_false_le gs (ws r) (b r) out
    rw [heval r, ht] at hle
    have eqFalse : ∀ a : Bool, a ≤ false → a = false := by decide
    exact eqFalse _ hle

lemma normForceTrue_preserves_samples {R : Type} (gs : List (Bool × ℕ × ℕ))
    (ws : R → List Bool) (b target : R → Bool) (out : ℕ)
    (hone : ∀ r, target r = false → b r = true)
    (heval : ∀ r, (normRun gs (ws r ++ [b r])).getD out false = target r) :
    ∀ r, (normRun gs (ws r ++ [true])).getD out false = target r := by
  intro r
  cases ht : target r with
  | false => simpa [ht, hone r ht] using heval r
  | true =>
    have hle := normRun_le_force_true gs (ws r) (b r) out
    rw [heval r, ht] at hle
    have eqTrue : ∀ a : Bool, true ≤ a → a = true := by decide
    exact eqTrue _ hle

def normInputs : List (BitVec 58) :=
  [95229015649943559, 63038587666488, 256462815680, 4292497062759936,
   8521481482240, 14003410187812864, 55389823207997440, 189297016294081033,
   155696362464477250, 218994303132270608, 183565875465490436,
   229736628138025984, 270286071508633728, 288160007407550752]

set_option maxRecDepth 16000 in
lemma normSingleEdge_realizable : ∀ j : Fin 21, ∃ a b : Fin 14,
    a.val < b.val ∧ normInputs.getD a.val 0 &&& normInputs.getD b.val 0 =
      (1 : BitVec 58) <<< j.val := by
  decide

end PEqualNP.Outside.L_meta_4930
