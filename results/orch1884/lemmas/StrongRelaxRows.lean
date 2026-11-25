import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1884.StrongRelaxRows

def target (x : Fin 9 → Bool) : Bool :=
  x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 0 && x 5 ||
    x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 4 && x 6 ||
    x 6 && x 8 || x 8 && x 5 || x 5 && x 7 || x 7 && x 4

def row (m : Nat) : Fin 9 → Bool := fun i => m.testBit i.val

abbrev below (x y : Fin 9 → Bool) : Prop := ∀ i, x i = true → y i = true

def negatives : List Nat := [25,52,58,69,100,104,138,201,274,385,386,21,273]

def positives : List Nat := [3,6,12,33,66,132,264,80,320,288,160,144]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
lemma cover_cofactor : ∀ t : Fin 9, t = 2 ∨ t = 8 → ∀ x : Fin 9 → Bool,
    x t = false → target x = false →
    negatives.any (fun m => decide (below x (row m))) = true := by decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
lemma cover_negative : ∀ x : Fin 9 → Bool, target x = false →
    (277 :: negatives).any (fun m => decide (below x (row m))) = true := by decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
lemma cover_positive : ∀ x : Fin 9 → Bool, target x = true →
    positives.any (fun m => decide (below (row m) x)) = true := by decide

lemma positive_rows (G : (Fin 9 → Bool) → Bool)
    (hm : ∀ x y, below x y → G x = true → G y = true)
    (hp : ∀ m ∈ positives, G (row m) = true) :
    ∀ x, target x = true → G x = true := by
  intro x hx
  obtain ⟨m, hm', hle⟩ := List.any_eq_true.mp (cover_positive x hx)
  exact hm (row m) x (of_decide_eq_true hle) (hp m hm')

lemma negative_below (G : (Fin 9 → Bool) → Bool)
    (hm : ∀ x y, below x y → G x = true → G y = true)
    (hn : ∀ m ∈ negatives, G (row m) = false)
    (x : Fin 9 → Bool)
    (hc : negatives.any (fun m => decide (below x (row m))) = true) :
    G x = false := by
  obtain ⟨m, hm', hle⟩ := List.any_eq_true.mp hc
  cases hx : G x
  · rfl
  · have hbad := hm x (row m) (of_decide_eq_true hle) hx
    rw [hn m hm'] at hbad
    cases hbad

theorem exact_cofactor (G : (Fin 9 → Bool) → Bool)
    (hm : ∀ x y, below x y → G x = true → G y = true)
    (hp : ∀ m ∈ positives, G (row m) = true)
    (hn : ∀ m ∈ negatives, G (row m) = false)
    (t : Fin 9) (ht : t = 2 ∨ t = 8) :
    ∀ x, x t = false → G x = target x := by
  intro x hxt
  cases hx : target x
  · exact negative_below G hm hn x (cover_cofactor t ht x hxt hx)
  · exact positive_rows G hm hp x hx

theorem exact_if_exception_rejected (G : (Fin 9 → Bool) → Bool)
    (hm : ∀ x y, below x y → G x = true → G y = true)
    (hp : ∀ m ∈ positives, G (row m) = true)
    (hn : ∀ m ∈ negatives, G (row m) = false)
    (he : G (row 277) = false) : ∀ x, G x = target x := by
  intro x
  cases hx : target x
  · obtain ⟨m, hm', hle⟩ := List.any_eq_true.mp (cover_negative x hx)
    have hrejected : G (row m) = false := by
      rcases List.mem_cons.mp hm' with rfl | hm'
      · exact he
      · exact hn m hm'
    cases hg : G x
    · rfl
    · have hbad := hm x (row m) (of_decide_eq_true hle) hg
      rw [hrejected] at hbad
      cases hbad
  · exact positive_rows G hm hp x hx

end PEqualNP.Outside.L_meta_1884.StrongRelaxRows
