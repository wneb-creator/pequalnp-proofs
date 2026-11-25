import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_650

def incidenceEdges : List (ℕ × ℕ) :=
  [(0, 13), (0, 14), (0, 16), (0, 22), (1, 13), (1, 15), (1, 21), (1, 25), (2, 14), (2, 20), (2, 24), (2, 25), (3, 13), (3, 19), (3, 23), (3, 24), (4, 18), (4, 22), (4, 23), (4, 25), (5, 17), (5, 21), (5, 22), (5, 24), (6, 16), (6, 20), (6, 21), (6, 23), (7, 15), (7, 19), (7, 20), (7, 22), (8, 14), (8, 18), (8, 19), (8, 21), (9, 13), (9, 17), (9, 18), (9, 20), (10, 16), (10, 17), (10, 19), (10, 25), (11, 15), (11, 16), (11, 18), (11, 24), (12, 14), (12, 15), (12, 17), (12, 23)]

def incidenceRow (p : Fin 13) : Finset (Fin 13) :=
  Finset.univ.filter fun l => (p.val, 13 + l.val) ∈ incidenceEdges

lemma incidenceEdges_length : incidenceEdges.length = 52 := by decide

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
lemma incidenceRow_card : ∀ p : Fin 13, (incidenceRow p).card = 4 := by decide

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
lemma incidenceColumn_card : ∀ l : Fin 13,
    (Finset.univ.filter fun p : Fin 13 => (p.val, 13 + l.val) ∈ incidenceEdges).card = 4 := by
  decide

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
lemma incidenceRows_intersection : ∀ p q : Fin 13, p ≠ q →
    (incidenceRow p ∩ incidenceRow q).card = 1 := by decide

def matchingColumn (p : Fin 13) : Fin 13 :=
  ![0, 2, 11, 6, 10, 8, 7, 9, 5, 4, 12, 3, 1] p

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
lemma matchingColumn_injective : Function.Injective matchingColumn := by decide

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
lemma matchingColumn_edge : ∀ p : Fin 13,
    (p.val, 13 + (matchingColumn p).val) ∈ incidenceEdges := by decide

def leftVertex (p : Fin 13) : Fin 26 := ⟨p.val, by omega⟩

def rightVertex (l : Fin 13) : Fin 26 := ⟨13 + l.val, by omega⟩

lemma matching_cover_card (T : Finset (Fin 26))
    (hT : ∀ p : Fin 13, leftVertex p ∈ T ∨ rightVertex (matchingColumn p) ∈ T) :
    13 ≤ T.card := by
  let choose : Fin 13 → Fin 26 := fun p =>
    if leftVertex p ∈ T then leftVertex p else rightVertex (matchingColumn p)
  have hc : ∀ p, choose p ∈ T := by
    intro p
    dsimp [choose]
    split_ifs with hp
    · exact hp
    · exact (hT p).resolve_left hp
  have hi : Function.Injective choose := by
    intro p q h
    dsimp [choose] at h
    split_ifs at h with hp hq hq
    · apply Fin.ext
      exact congrArg (fun v : Fin 26 => v.val) h
    · have hv := congrArg Fin.val h
      dsimp [leftVertex, rightVertex] at hv
      have := p.isLt
      omega
    · have hv := congrArg Fin.val h
      dsimp [leftVertex, rightVertex] at hv
      have := q.isLt
      omega
    · apply matchingColumn_injective
      apply Fin.ext
      have hv := congrArg Fin.val h
      dsimp [rightVertex] at hv
      omega
  have hs : Finset.univ.image choose ⊆ T := by
    intro v hv
    obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp hv
    exact hc p
  have hb := Finset.card_le_card hs
  simpa [Finset.card_image_of_injective, hi] using hb

lemma incidence_cover_card (T : Finset (Fin 26))
    (hT : ∀ u v : Fin 26, (u.val, v.val) ∈ incidenceEdges → u ∈ T ∨ v ∈ T) :
    13 ≤ T.card := by
  apply matching_cover_card T
  intro p
  apply hT
  exact matchingColumn_edge p

end PEqualNP.Outside.L_meta_650
