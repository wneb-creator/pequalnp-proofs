import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2590.Boundary

abbrev Input := Fin 10 → Bool

def below (x y : Input) : Prop := ∀ i, x i = true → y i = true

def increasing (f : Input → Bool) : Prop :=
  ∀ x y, below x y → f x = true → f y = true

def edges : List (Fin 10 × Fin 10) :=
  [(0, 1), (1, 2), (2, 3), (3, 4), (4, 0), (0, 5), (1, 6), (2, 7),
   (3, 8), (4, 9), (5, 7), (7, 9), (9, 6), (6, 8), (8, 5)]

def pet (x : Input) : Bool := edges.any fun e => x e.1 && x e.2

def row (k : Nat) (i : Fin 10) : Bool := k.testBit i.val

def positives : List Nat :=
  [3, 6, 12, 17, 24, 33, 66, 132, 160, 264, 288, 320, 528, 576, 640]

def negatives : List Nat :=
  [50, 69, 104, 116, 138, 201, 208, 276, 385, 402, 521, 548, 554, 770, 773]

lemma positive_values : ∀ k ∈ positives, pet (row k) = true := by decide

lemma negative_values : ∀ k ∈ negatives, pet (row k) = false := by decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 20000000 in
lemma positive_cover : ∀ x : Input, pet x = true →
    ∃ k ∈ positives, below (row k) x := by
  unfold below
  decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 20000000 in
lemma negative_cover : ∀ x : Input, pet x = false →
    ∃ k ∈ negatives, below x (row k) := by
  unfold below
  decide

lemma exact_of_boundary (g : Input → Bool) (mono : increasing g)
    (pos : ∀ k ∈ positives, g (row k) = true)
    (neg : ∀ k ∈ negatives, g (row k) = false) :
    ∀ x, g x = pet x := by
  intro x
  cases hp : pet x
  · obtain ⟨k, hk, hle⟩ := negative_cover x hp
    cases hg : g x
    · rfl
    · have bad := mono x (row k) hle hg
      rw [neg k hk] at bad
      cases bad
  · obtain ⟨k, hk, hle⟩ := positive_cover x hp
    exact mono (row k) x hle (pos k hk)

lemma replacement_from_dominance
    (H D : Input → Bool) (K : Input → Bool → Bool)
    (context : ∀ x b c, (b = true → c = true) →
      K x b = true → K x c = true)
    (old : ∀ x, K x (H x) = pet x)
    (newMono : increasing (fun x => K x (D x)))
    (pos : ∀ k ∈ positives, H (row k) = true → D (row k) = true)
    (neg : ∀ k ∈ negatives, D (row k) = true → H (row k) = true) :
    ∀ x, K x (D x) = pet x := by
  apply exact_of_boundary _ newMono
  · intro k hk
    apply context (row k) (H (row k)) (D (row k)) (pos k hk)
    rw [old, positive_values k hk]
  · intro k hk
    cases hnew : K (row k) (D (row k))
    · rfl
    · have bad := context (row k) (D (row k)) (H (row k)) (neg k hk) hnew
      rw [old, negative_values k hk] at bad
      cases bad

end PEqualNP.Outside.L_meta_2590.Boundary
