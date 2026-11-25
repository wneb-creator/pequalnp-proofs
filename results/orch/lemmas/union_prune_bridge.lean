import Mathlib.Data.Bool.Basic

namespace PEqualNP.Outside.L_meta_2592

def starMasks : List Nat := [22, 37, 25, 42]

def singletonMasks : List Nat := [1, 2, 4, 8, 16, 32]

def helperMasks : List Nat :=
  [3, 5, 6, 7, 9, 10, 11, 12, 13, 14, 15, 17, 18, 19, 20, 21, 23, 24, 26, 27, 28, 29, 30, 31, 33, 34, 35, 36, 38, 39, 40, 41, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63]

lemma helperMasks_spec : helperMasks =
    (List.range 64).filter (fun x =>
      x != 0 && Nat.land x (x - 1) != 0 && !(starMasks.contains x)) := by
  decide +kernel

def setStepAllowed (known : List Nat) (target : Nat) : Bool :=
  known.any fun a => Nat.land target a == target ||
    known.any fun b => Nat.lor a b == target

def closeStarStep (known : List Nat) (target : Nat) : List Nat :=
  if known.contains target then known
  else if setStepAllowed known target then target :: known else known

def closeStarSets : Nat → List Nat → List Nat → List Nat
  | 0, _, known => known
  | fuel + 1, allowed, known =>
    let next := allowed.foldl closeStarStep known
    if next.length == known.length then known
    else closeStarSets fuel allowed next

def starTripleSucceeds (a b c : Nat) : Bool :=
  let known := closeStarSets 7 (starMasks ++ [a, b, c]) singletonMasks
  starMasks.all known.contains

def starHelperPair (a b : Nat) : Bool :=
  helperMasks.any fun c => if b < c then starTripleSucceeds a b c else false

def starHelperRow (a : Nat) : Bool :=
  helperMasks.any fun b => if a < b then starHelperPair a b else false

def starHelperSearch : Bool := helperMasks.any starHelperRow

lemma setStepAllowed_mono {known larger : List Nat} {target : Nat}
    (hsub : known ⊆ larger) (h : setStepAllowed known target = true) :
    setStepAllowed larger target = true := by
  simp only [setStepAllowed, List.any_eq_true, Bool.or_eq_true, beq_iff_eq] at h ⊢
  obtain ⟨a, ha, ht⟩ := h
  refine ⟨a, hsub ha, ?_⟩
  rcases ht with ht | ⟨b, hb, ht⟩
  · exact Or.inl ht
  · exact Or.inr ⟨b, hsub hb, ht⟩

lemma closeStarStep_prefix (known : List Nat) (target : Nat) :
    ∃ added, closeStarStep known target = added ++ known := by
  unfold closeStarStep
  split
  · exact ⟨[], rfl⟩
  · split
    · exact ⟨[target], rfl⟩
    · exact ⟨[], rfl⟩

lemma closeStarPass_prefix (known allowed : List Nat) :
    ∃ added, allowed.foldl closeStarStep known = added ++ known := by
  induction allowed generalizing known with
  | nil => exact ⟨[], rfl⟩
  | cons target rest ih =>
    obtain ⟨added, ha⟩ := closeStarStep_prefix known target
    obtain ⟨later, hl⟩ := ih (closeStarStep known target)
    refine ⟨later ++ added, ?_⟩
    simp only [List.foldl_cons, hl, ha, List.append_assoc]

lemma closeStarPass_extends (known allowed : List Nat) :
    known ⊆ allowed.foldl closeStarStep known := by
  obtain ⟨added, ha⟩ := closeStarPass_prefix known allowed
  rw [ha]
  intro a ha
  exact List.mem_append.mpr (Or.inr ha)

lemma closeStarPass_same_of_length (known allowed : List Nat)
    (h : (allowed.foldl closeStarStep known).length = known.length) :
    allowed.foldl closeStarStep known = known := by
  obtain ⟨added, ha⟩ := closeStarPass_prefix known allowed
  rw [ha, List.length_append] at h
  have hz : added.length = 0 := Nat.add_right_cancel (by simpa using h)
  have he : added = [] := List.length_eq_zero_iff.mp hz
  simpa [he] using ha

lemma closeStarPass_adds {known allowed : List Nat} {target : Nat}
    (hm : target ∈ allowed) (ha : setStepAllowed known target = true) :
    target ∈ allowed.foldl closeStarStep known := by
  induction allowed generalizing known with
  | nil => simp at hm
  | cons head rest ih =>
    simp only [List.mem_cons] at hm
    rcases hm with rfl | hm
    · have hs : head ∈ closeStarStep known head := by
        unfold closeStarStep
        split
        · simpa using ‹known.contains head = true›
        · rw [ha]
          simp
      exact closeStarPass_extends _ _ hs
    · apply ih hm
      apply setStepAllowed_mono _ ha
      obtain ⟨added, he⟩ := closeStarStep_prefix known head
      rw [he]
      intro a ha
      exact List.mem_append.mpr (Or.inr ha)

lemma starTriple_false_of_search_false {a b c : Nat}
    (hsearch : starHelperSearch = false)
    (ha : a ∈ helperMasks) (hb : b ∈ helperMasks) (hc : c ∈ helperMasks)
    (hab : a < b) (hbc : b < c) : starTripleSucceeds a b c = false := by
  have hsearch' : ¬ starHelperSearch = true := by simp [hsearch]
  cases h : starTripleSucceeds a b c
  · rfl
  · exfalso
    apply hsearch'
    unfold starHelperSearch
    apply List.any_eq_true.mpr
    refine ⟨a, ha, ?_⟩
    unfold starHelperRow
    apply List.any_eq_true.mpr
    refine ⟨b, hb, ?_⟩
    rw [if_pos hab]
    unfold starHelperPair
    apply List.any_eq_true.mpr
    exact ⟨c, hc, by simp only [if_pos hbc, h]⟩

end PEqualNP.Outside.L_meta_2592
