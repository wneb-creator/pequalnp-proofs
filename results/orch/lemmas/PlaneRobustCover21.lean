import Mathlib

namespace PEqualNP.Outside.L_meta_1477.PlaneRobustCover

def planeEdges : List (ℕ × ℕ) :=
  [(0, 21), (0, 26), (0, 28), (0, 38), (0, 41), (1, 21), (1, 22), (1, 27), (1, 29), (1, 39), (2, 22), (2, 23), (2, 28), (2, 30), (2, 40), (3, 23), (3, 24), (3, 29), (3, 31), (3, 41), (4, 21), (4, 24), (4, 25), (4, 30), (4, 32), (5, 22), (5, 25), (5, 26), (5, 31), (5, 33), (6, 23), (6, 26), (6, 27), (6, 32), (6, 34), (7, 24), (7, 27), (7, 28), (7, 33), (7, 35), (8, 25), (8, 28), (8, 29), (8, 34), (8, 36), (9, 26), (9, 29), (9, 30), (9, 35), (9, 37), (10, 27), (10, 30), (10, 31), (10, 36), (10, 38), (11, 28), (11, 31), (11, 32), (11, 37), (11, 39), (12, 29), (12, 32), (12, 33), (12, 38), (12, 40), (13, 30), (13, 33), (13, 34), (13, 39), (13, 41), (14, 21), (14, 31), (14, 34), (14, 35), (14, 40), (15, 22), (15, 32), (15, 35), (15, 36), (15, 41), (16, 21), (16, 23), (16, 33), (16, 36), (16, 37), (17, 22), (17, 24), (17, 34), (17, 37), (17, 38), (18, 23), (18, 25), (18, 35), (18, 38), (18, 39), (19, 24), (19, 26), (19, 36), (19, 39), (19, 40), (20, 25), (20, 27), (20, 37), (20, 40), (20, 41)]

def shifts : Finset (Fin 21) := {0, 5, 7, 17, 20}

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma shift_edge : ∀ d ∈ shifts, ∀ i : Fin 21,
    (i.val, (i + d).val + 21) ∈ planeEdges := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma edge_has_shift : ∀ a b : Fin 21, (a.val, b.val + 21) ∈ planeEdges →
    ∃ d ∈ shifts, a + d = b := by
  decide

lemma shift_injective (d : Fin 21) : Function.Injective (fun i : Fin 21 => i + d) := by
  intro i j hij
  exact add_right_cancel hij

lemma residual_cover_lower (a b : Fin 21) (hab : (a.val, b.val + 21) ∈ planeEdges)
    (s : Finset ℕ)
    (hcover : ∀ i j : Fin 21, i ≠ a → j ≠ b →
      (i.val, j.val + 21) ∈ planeEdges → i.val ∈ s ∨ j.val + 21 ∈ s) :
    20 ≤ s.card := by
  obtain ⟨d, hd, had⟩ := edge_has_shift a b hab
  let f : Fin 21 → ℕ := fun i => if i.val ∈ s then i.val else (i + d).val + 21
  have hf : Function.Injective f := by
    intro i j hij
    by_cases hi : i.val ∈ s <;> by_cases hj : j.val ∈ s
    · apply Fin.ext
      simpa [f, hi, hj] using hij
    · have he : i.val = (j + d).val + 21 := by simpa [f, hi, hj] using hij
      have := i.isLt
      omega
    · have he : (i + d).val + 21 = j.val := by simpa [f, hi, hj] using hij
      have := j.isLt
      omega
    · have he : (i + d).val + 21 = (j + d).val + 21 := by simpa [f, hi, hj] using hij
      exact shift_injective d (Fin.ext (Nat.add_right_cancel he))
  have hsub : ((Finset.univ.erase a).image f) ⊆ s := by
    intro v hv
    rcases Finset.mem_image.mp hv with ⟨i, hi, rfl⟩
    have hia : i ≠ a := (Finset.mem_erase.mp hi).1
    have hid : i + d ≠ b := by
      intro h
      exact hia (shift_injective d (h.trans had.symm))
    have hc := hcover i (i + d) hia hid (shift_edge d hd i)
    dsimp [f]
    split_ifs with his
    · exact his
    · exact hc.resolve_left his
  have hcard : (Finset.univ.erase a : Finset (Fin 21)).card = 20 := by simp
  calc
    20 = (Finset.univ.erase a : Finset (Fin 21)).card := hcard.symm
    _ = ((Finset.univ.erase a).image f).card := (Finset.card_image_of_injective _ hf).symm
    _ ≤ s.card := Finset.card_le_card hsub


def residualMatch (d a : Fin 21) : Finset (Fin 21 × Fin 21) :=
  (Finset.univ.erase a).image (fun i => (i, i + d))

lemma residualMatch_card (d a : Fin 21) : (residualMatch d a).card = 20 := by
  rw [residualMatch, Finset.card_image_of_injective _ (fun _ _ h => congrArg Prod.fst h)]
  simp

lemma residualMatch_no_shared_endpoint (d a : Fin 21) (e f : Fin 21 × Fin 21)
    (he : e ∈ residualMatch d a) (hf : f ∈ residualMatch d a) (hef : e ≠ f) :
    e.1 ≠ f.1 ∧ e.2 ≠ f.2 := by
  rcases Finset.mem_image.mp he with ⟨i, _, rfl⟩
  rcases Finset.mem_image.mp hf with ⟨j, _, rfl⟩
  have hij : i ≠ j := fun h => hef (by simp [h])
  exact ⟨hij, fun h => hij (shift_injective d h)⟩

lemma residual_matching (a b : Fin 21) (hab : (a.val, b.val + 21) ∈ planeEdges) :
    ∃ M : Finset (Fin 21 × Fin 21), M.card = 20 ∧
      (∀ e ∈ M, (e.1.val, e.2.val + 21) ∈ planeEdges ∧ e.1 ≠ a ∧ e.2 ≠ b) ∧
      (∀ e ∈ M, ∀ f ∈ M, e ≠ f → e.1 ≠ f.1 ∧ e.2 ≠ f.2) := by
  obtain ⟨d, hd, had⟩ := edge_has_shift a b hab
  refine ⟨residualMatch d a, residualMatch_card d a, ?_, ?_⟩
  · intro e he
    rcases Finset.mem_image.mp he with ⟨i, hi, rfl⟩
    have hia : i ≠ a := (Finset.mem_erase.mp hi).1
    refine ⟨shift_edge d hd i, hia, ?_⟩
    intro h
    exact hia (shift_injective d (h.trans had.symm))
  · intro e he f hf hef
    exact residualMatch_no_shared_endpoint d a e f he hf hef

lemma planeEdges_bounds : ∀ e ∈ planeEdges, e.1 < 21 ∧ 21 ≤ e.2 ∧ e.2 < 42 := by
  decide

lemma residual_nat_cover_lower (a b : ℕ) (hab : (a, b) ∈ planeEdges) (s : Finset ℕ)
    (hcover : ∀ u v : ℕ, (u, v) ∈ planeEdges → u ≠ a → v ≠ b →
      u ∈ s ∨ v ∈ s) : 20 ≤ s.card := by
  have hb := planeEdges_bounds (a, b) hab
  let aa : Fin 21 := ⟨a, hb.1⟩
  let bb : Fin 21 := ⟨b - 21, by omega⟩
  have hab' : (aa.val, bb.val + 21) ∈ planeEdges := by
    change (a, b - 21 + 21) ∈ planeEdges
    simpa only [Nat.sub_add_cancel hb.2.1] using hab
  apply residual_cover_lower aa bb hab' s
  intro i j hia hjb hij
  apply hcover i.val (j.val + 21) hij
  · intro h
    exact hia (Fin.ext h)
  · intro h
    apply hjb
    apply Fin.ext
    change j.val = b - 21
    omega

def leftVertex (i : Fin 21) : Fin 42 := ⟨i.val, by omega⟩

def rightVertex (j : Fin 21) : Fin 42 := ⟨j.val + 21, by omega⟩

lemma residual_graph_cover_lower (G : SimpleGraph (Fin 42)) (a b : Fin 21)
    (hab : (a.val, b.val + 21) ∈ planeEdges)
    (hkeep : ∀ i j : Fin 21, i ≠ a → j ≠ b →
      (i.val, j.val + 21) ∈ planeEdges → G.Adj (leftVertex i) (rightVertex j))
    (T : Finset (Fin 42)) (hcover : ∀ u v, G.Adj u v → u ∈ T ∨ v ∈ T) :
    20 ≤ T.card := by
  let S : Finset ℕ := T.image Fin.val
  have hs : 20 ≤ S.card := by
    apply residual_cover_lower a b hab S
    intro i j hia hjb hij
    rcases hcover (leftVertex i) (rightVertex j) (hkeep i j hia hjb hij) with hi | hj
    · exact Or.inl (Finset.mem_image.mpr ⟨leftVertex i, hi, rfl⟩)
    · exact Or.inr (Finset.mem_image.mpr ⟨rightVertex j, hj, rfl⟩)
  exact hs.trans Finset.card_image_le


lemma residual_cover_lower_with_center (a b : Fin 21)
    (hab : (a.val, b.val + 21) ∈ planeEdges) (s : Finset ℕ)
    (hcenter : a.val ∈ s ∨ b.val + 21 ∈ s)
    (hcover : ∀ i j : Fin 21, i ≠ a → j ≠ b →
      (i.val, j.val + 21) ∈ planeEdges → i.val ∈ s ∨ j.val + 21 ∈ s) :
    21 ≤ s.card := by
  obtain ⟨d, hd, had⟩ := edge_has_shift a b hab
  let f : Fin 21 → ℕ := fun i => if i.val ∈ s then i.val else (i + d).val + 21
  have hf : Function.Injective f := by
    intro i j hij
    by_cases hi : i.val ∈ s <;> by_cases hj : j.val ∈ s
    · apply Fin.ext
      simpa [f, hi, hj] using hij
    · have he : i.val = (j + d).val + 21 := by simpa [f, hi, hj] using hij
      have := i.isLt
      omega
    · have he : (i + d).val + 21 = j.val := by simpa [f, hi, hj] using hij
      have := j.isLt
      omega
    · have he : (i + d).val + 21 = (j + d).val + 21 := by simpa [f, hi, hj] using hij
      exact shift_injective d (Fin.ext (Nat.add_right_cancel he))
  have hsub : Finset.univ.image f ⊆ s := by
    intro v hv
    rcases Finset.mem_image.mp hv with ⟨i, _, rfl⟩
    have hc : i.val ∈ s ∨ (i + d).val + 21 ∈ s := by
      by_cases hia : i = a
      · subst i
        simpa only [had] using hcenter
      · have hid : i + d ≠ b := by
          intro h
          exact hia (shift_injective d (h.trans had.symm))
        exact hcover i (i + d) hia hid (shift_edge d hd i)
    dsimp [f]
    split_ifs with his
    · exact his
    · exact hc.resolve_left his
  calc
    21 = (Finset.univ : Finset (Fin 21)).card := by simp
    _ = (Finset.univ.image f).card := (Finset.card_image_of_injective _ hf).symm
    _ ≤ s.card := Finset.card_le_card hsub

lemma residual_nat_cover_lower_with_center (a b : ℕ) (hab : (a, b) ∈ planeEdges)
    (s : Finset ℕ) (hcenter : a ∈ s ∨ b ∈ s)
    (hcover : ∀ u v : ℕ, (u, v) ∈ planeEdges → u ≠ a → v ≠ b →
      u ∈ s ∨ v ∈ s) : 21 ≤ s.card := by
  have hb := planeEdges_bounds (a, b) hab
  let aa : Fin 21 := ⟨a, hb.1⟩
  let bb : Fin 21 := ⟨b - 21, by omega⟩
  have hab' : (aa.val, bb.val + 21) ∈ planeEdges := by
    change (a, b - 21 + 21) ∈ planeEdges
    simpa only [Nat.sub_add_cancel hb.2.1] using hab
  apply residual_cover_lower_with_center aa bb hab' s
  · change a ∈ s ∨ b - 21 + 21 ∈ s
    simpa only [Nat.sub_add_cancel hb.2.1] using hcenter
  · intro i j hia hjb hij
    apply hcover i.val (j.val + 21) hij
    · intro h
      exact hia (Fin.ext h)
    · intro h
      apply hjb
      apply Fin.ext
      change j.val = b - 21
      omega

lemma residual_graph_cover_lower_with_center (G : SimpleGraph (Fin 42)) (a b : Fin 21)
    (hab : (a.val, b.val + 21) ∈ planeEdges)
    (hcenter : G.Adj (leftVertex a) (rightVertex b))
    (hkeep : ∀ i j : Fin 21, i ≠ a → j ≠ b →
      (i.val, j.val + 21) ∈ planeEdges → G.Adj (leftVertex i) (rightVertex j))
    (T : Finset (Fin 42)) (hcover : ∀ u v, G.Adj u v → u ∈ T ∨ v ∈ T) :
    21 ≤ T.card := by
  let S : Finset ℕ := T.image Fin.val
  have hs : 21 ≤ S.card := by
    apply residual_cover_lower_with_center a b hab S
    · rcases hcover (leftVertex a) (rightVertex b) hcenter with ha | hb
      · exact Or.inl (Finset.mem_image.mpr ⟨leftVertex a, ha, rfl⟩)
      · exact Or.inr (Finset.mem_image.mpr ⟨rightVertex b, hb, rfl⟩)
    · intro i j hia hjb hij
      rcases hcover (leftVertex i) (rightVertex j) (hkeep i j hia hjb hij) with hi | hj
      · exact Or.inl (Finset.mem_image.mpr ⟨leftVertex i, hi, rfl⟩)
      · exact Or.inr (Finset.mem_image.mpr ⟨rightVertex j, hj, rfl⟩)
  exact hs.trans Finset.card_image_le

end PEqualNP.Outside.L_meta_1477.PlaneRobustCover
