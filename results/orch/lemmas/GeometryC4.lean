import Mathlib

namespace PEqualNP.Outside.L_meta_1477

def planeEdges : List (ℕ × ℕ) :=
  [(0, 21), (0, 26), (0, 28), (0, 38), (0, 41), (1, 21), (1, 22), (1, 27), (1, 29), (1, 39), (2, 22), (2, 23), (2, 28), (2, 30), (2, 40), (3, 23), (3, 24), (3, 29), (3, 31), (3, 41), (4, 21), (4, 24), (4, 25), (4, 30), (4, 32), (5, 22), (5, 25), (5, 26), (5, 31), (5, 33), (6, 23), (6, 26), (6, 27), (6, 32), (6, 34), (7, 24), (7, 27), (7, 28), (7, 33), (7, 35), (8, 25), (8, 28), (8, 29), (8, 34), (8, 36), (9, 26), (9, 29), (9, 30), (9, 35), (9, 37), (10, 27), (10, 30), (10, 31), (10, 36), (10, 38), (11, 28), (11, 31), (11, 32), (11, 37), (11, 39), (12, 29), (12, 32), (12, 33), (12, 38), (12, 40), (13, 30), (13, 33), (13, 34), (13, 39), (13, 41), (14, 21), (14, 31), (14, 34), (14, 35), (14, 40), (15, 22), (15, 32), (15, 35), (15, 36), (15, 41), (16, 21), (16, 23), (16, 33), (16, 36), (16, 37), (17, 22), (17, 24), (17, 34), (17, 37), (17, 38), (18, 23), (18, 25), (18, 35), (18, 38), (18, 39), (19, 24), (19, 26), (19, 36), (19, 39), (19, 40), (20, 25), (20, 27), (20, 37), (20, 40), (20, 41)]

lemma planeEdges_length : planeEdges.length = 105 := by decide

lemma planeEdges_nodup : planeEdges.Nodup := by decide


lemma planeEdges_bounds : ∀ e ∈ planeEdges, e.1 < 21 ∧ 21 ≤ e.2 ∧ e.2 < 42 := by
  decide

lemma planeEdges_card : planeEdges.toFinset.card = 105 := by
  rw [List.toFinset_card_of_nodup planeEdges_nodup, planeEdges_length]

def planeNeighbors (i : Fin 21) : Finset (Fin 21) :=
  Finset.univ.filter (fun j => (i.val, j.val + 21) ∈ planeEdges)

def planeRightNeighbors (j : Fin 21) : Finset (Fin 21) :=
  Finset.univ.filter (fun i => (i.val, j.val + 21) ∈ planeEdges)

lemma planeNeighbors_card (i : Fin 21) : (planeNeighbors i).card = 5 := by
  fin_cases i <;> decide

lemma planeRightNeighbors_card (j : Fin 21) : (planeRightNeighbors j).card = 5 := by
  fin_cases j <;> decide

lemma planeEdges_diagonal (i : Fin 21) : (i.val, i.val + 21) ∈ planeEdges := by
  fin_cases i <;> decide

lemma planeEdges_vertexCover_lower (s : Finset ℕ)
    (hcover : ∀ u v, (u, v) ∈ planeEdges → u ∈ s ∨ v ∈ s) :
    21 ≤ s.card := by
  let f : Fin 21 → ℕ := fun i => if i.val ∈ s then i.val else i.val + 21
  have hf : Function.Injective f := by
    intro i j hij
    apply Fin.ext
    dsimp [f] at hij
    split_ifs at hij <;> omega
  have hsub : Finset.univ.image f ⊆ s := by
    intro v hv
    rcases Finset.mem_image.mp hv with ⟨i, _, rfl⟩
    dsimp [f]
    split_ifs with hi
    · exact hi
    · exact (hcover i.val (i.val + 21) (planeEdges_diagonal i)).resolve_left hi
  calc
    21 = (Finset.univ : Finset (Fin 21)).card := by simp
    _ = (Finset.univ.image f).card := (Finset.card_image_of_injective _ hf).symm
    _ ≤ s.card := Finset.card_le_card hsub

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma planeNeighbors_inter_card (i j : Fin 21) (h : i ≠ j) :
    (planeNeighbors i ∩ planeNeighbors j).card = 1 := by
  revert j
  fin_cases i <;> decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma planeRightNeighbors_inter_card (i j : Fin 21) (h : i ≠ j) :
    (planeRightNeighbors i ∩ planeRightNeighbors j).card = 1 := by
  revert j
  fin_cases i <;> decide


lemma mem_planeNeighbors {i j : Fin 21} :
    j ∈ planeNeighbors i ↔ (i.val, j.val + 21) ∈ planeEdges := by
  simp [planeNeighbors]

lemma planeNeighbors_common_unique {i j a b : Fin 21} (hij : i ≠ j)
    (hai : a ∈ planeNeighbors i) (haj : a ∈ planeNeighbors j)
    (hbi : b ∈ planeNeighbors i) (hbj : b ∈ planeNeighbors j) : a = b := by
  have hc : (planeNeighbors i ∩ planeNeighbors j).card ≤ 1 := by
    rw [planeNeighbors_inter_card i j hij]
  exact Finset.card_le_one.mp hc a (Finset.mem_inter.mpr ⟨hai, haj⟩)
    b (Finset.mem_inter.mpr ⟨hbi, hbj⟩)

lemma planeEdges_no_rectangle {a b c d : ℕ} (hab : a ≠ b) (hcd : c ≠ d)
    (hac : (a, c) ∈ planeEdges) (had : (a, d) ∈ planeEdges)
    (hbc : (b, c) ∈ planeEdges) (hbd : (b, d) ∈ planeEdges) : False := by
  have hacb := planeEdges_bounds (a, c) hac
  have hadb := planeEdges_bounds (a, d) had
  have hbcb := planeEdges_bounds (b, c) hbc
  let aa : Fin 21 := ⟨a, hacb.1⟩
  let bb : Fin 21 := ⟨b, hbcb.1⟩
  let cc : Fin 21 := ⟨c - 21, by omega⟩
  let dd : Fin 21 := ⟨d - 21, by omega⟩
  have haab : aa ≠ bb := by
    intro h
    exact hab (congrArg Fin.val h)
  have hcc : cc ∈ planeNeighbors aa ∧ cc ∈ planeNeighbors bb := by
    constructor
    · apply mem_planeNeighbors.mpr
      change (a, c - 21 + 21) ∈ planeEdges
      simpa only [Nat.sub_add_cancel hacb.2.1] using hac
    · apply mem_planeNeighbors.mpr
      change (b, c - 21 + 21) ∈ planeEdges
      simpa only [Nat.sub_add_cancel hacb.2.1] using hbc
  have hdd : dd ∈ planeNeighbors aa ∧ dd ∈ planeNeighbors bb := by
    constructor
    · apply mem_planeNeighbors.mpr
      change (a, d - 21 + 21) ∈ planeEdges
      simpa only [Nat.sub_add_cancel hadb.2.1] using had
    · apply mem_planeNeighbors.mpr
      change (b, d - 21 + 21) ∈ planeEdges
      simpa only [Nat.sub_add_cancel hadb.2.1] using hbd
  have heq := planeNeighbors_common_unique haab hcc.1 hcc.2 hdd.1 hdd.2
  have heqv := congrArg Fin.val heq
  dsimp [cc, dd] at heqv
  exact hcd (by omega)

end PEqualNP.Outside.L_meta_1477
