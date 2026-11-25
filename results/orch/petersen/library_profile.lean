import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2590_aux.Profile

def edge (i : Fin 15) : Fin 10 × Fin 10 :=
  ![(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(4,9),
    (5,7),(7,9),(9,6),(6,8),(8,5)] i

def missing (T : Finset (Fin 10)) : Finset (Fin 15) :=
  Finset.univ.filter fun i => (edge i).1 ∉ T ∧ (edge i).2 ∉ T

def loss (k : ℕ) : ℕ :=
  if k = 0 then 15 else if k = 1 then 12 else if k = 2 then 9 else
  if k = 3 then 6 else if k = 4 then 3 else if k = 5 then 2 else 0

set_option maxRecDepth 24000 in
set_option maxHeartbeats 12000000 in
lemma missing_bound : ∀ T : Finset (Fin 10), loss T.card ≤ (missing T).card := by
  decide +kernel

lemma removed_bound (T : Finset (Fin 10)) (U : Finset (Fin 15))
    (hcover : ∀ i : Fin 15, i ∉ U → (edge i).1 ∈ T ∨ (edge i).2 ∈ T) :
    loss T.card ≤ U.card := by
  apply (missing_bound T).trans
  apply Finset.card_le_card
  intro i hi
  have hm := (Finset.mem_filter.mp hi).2
  by_contra hn
  rcases hcover i hn with ha | hb
  · exact hm.1 ha
  · exact hm.2 hb

lemma cover_six (T : Finset (Fin 10)) (U : Finset (Fin 15))
    (hcover : ∀ i : Fin 15, i ∉ U → (edge i).1 ∈ T ∨ (edge i).2 ∈ T)
    (hsmall : U.card ≤ 1) : 6 ≤ T.card := by
  have h := removed_bound T U hcover
  unfold loss at h
  split_ifs at h <;> omega

lemma cover_five (T : Finset (Fin 10)) (U : Finset (Fin 15))
    (hcover : ∀ i : Fin 15, i ∉ U → (edge i).1 ∈ T ∨ (edge i).2 ∈ T)
    (hsmall : U.card ≤ 2) : 5 ≤ T.card := by
  have h := removed_bound T U hcover
  unfold loss at h
  split_ifs at h <;> omega

lemma cover_four (T : Finset (Fin 10)) (U : Finset (Fin 15))
    (hcover : ∀ i : Fin 15, i ∉ U → (edge i).1 ∈ T ∨ (edge i).2 ∈ T)
    (hsmall : U.card ≤ 5) : 4 ≤ T.card := by
  have h := removed_bound T U hcover
  unfold loss at h
  split_ifs at h <;> omega

end PEqualNP.Outside.L_meta_2590_aux.Profile
