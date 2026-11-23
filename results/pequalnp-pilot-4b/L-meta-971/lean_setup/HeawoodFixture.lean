import PEqualNP.Defs

namespace HeawoodFixtureAudit

def edges : Finset (Fin 14 × Fin 14) :=
  {(0, 7), (0, 8), (0, 10), (1, 7), (1, 9), (1, 13), (2, 8), (2, 12), (2, 13),
   (3, 7), (3, 11), (3, 12), (4, 10), (4, 11), (4, 13), (5, 9), (5, 10), (5, 12),
   (6, 8), (6, 9), (6, 11)}

def neighbors (u : Fin 14) : Finset (Fin 14) :=
  Finset.univ.filter (fun v => (u, v) ∈ edges ∨ (v, u) ∈ edges)

def left : Finset (Fin 14) := Finset.univ.filter (fun u => u.val < 7)

theorem edge_count : edges.card = 21 := by decide

theorem bipartite : ∀ u v : Fin 14, (u, v) ∈ edges → u.val < 7 ∧ 7 ≤ v.val := by decide

theorem three_regular : ∀ u : Fin 14, (neighbors u).card = 3 := by decide

set_option maxHeartbeats 1000000 in
theorem no_four_cycle : ∀ u v : Fin 14, u ≠ v →
    (neighbors u ∩ neighbors v).card ≤ 1 := by decide

theorem left_cover_size : left.card = 7 := by decide

theorem left_covers : ∀ u v : Fin 14, (u, v) ∈ edges → u ∈ left := by decide

def matchLeft (i : Fin 7) : Fin 14 :=
  ⟨i.val, Nat.lt_trans i.isLt (by decide)⟩

def matchRight : Fin 7 → Fin 14 := ![7, 9, 8, 12, 13, 10, 11]

theorem matching_edges : ∀ i : Fin 7, (matchLeft i, matchRight i) ∈ edges := by decide

theorem matching_left_injective : Function.Injective matchLeft := by decide

theorem matching_right_injective : Function.Injective matchRight := by decide

theorem matching_disjoint : Disjoint (Finset.univ.image matchLeft)
    (Finset.univ.image matchRight) := by decide

theorem matching_right_ge_seven : ∀ i : Fin 7, 7 ≤ (matchRight i).val := by decide

theorem every_cover_at_least_seven (A : Finset (Fin 14))
    (hA : ∀ u v : Fin 14, (u, v) ∈ edges → u ∈ A ∨ v ∈ A) : 7 ≤ A.card := by
  let pick : Fin 7 → Fin 14 := fun i => if matchLeft i ∈ A then matchLeft i else matchRight i
  have hmem (i : Fin 7) : pick i ∈ A := by
    dsimp [pick]
    split_ifs with hi
    · exact hi
    · exact (hA _ _ (matching_edges i)).resolve_left hi
  have hinj : Function.Injective pick := by
    intro i j hij
    dsimp [pick] at hij
    by_cases hi : matchLeft i ∈ A <;> by_cases hj : matchLeft j ∈ A
    · simp only [ite_eq_left hi, ite_eq_left hj] at hij
      exact matching_left_injective hij
    · simp only [ite_eq_left hi, ite_eq_right hj] at hij
      have hval := congrArg Fin.val hij
      have hlo : (matchLeft i).val < 7 := i.isLt
      have hhi := matching_right_ge_seven j
      omega
    · simp only [ite_eq_right hi, ite_eq_left hj] at hij
      have hval := congrArg Fin.val hij
      have hlo : (matchLeft j).val < 7 := j.isLt
      have hhi := matching_right_ge_seven i
      omega
    · simp only [ite_eq_right hi, ite_eq_right hj] at hij
      exact matching_right_injective hij
  have hsub : Finset.univ.image pick ⊆ A := by
    intro a ha
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp ha
    exact hmem i
  have hcard : (Finset.univ.image pick).card = 7 := by
    rw [Finset.card_image_of_injective _ hinj]
    simp
  rw [← hcard]
  exact Finset.card_le_card hsub


def right : Finset (Fin 14) := Finset.univ.filter (fun u => 7 ≤ u.val)

def opposite (u v : Fin 14) : Prop :=
  (u.val < 7 ∧ 7 ≤ v.val) ∨ (7 ≤ u.val ∧ v.val < 7)

instance (u v : Fin 14) : Decidable (opposite u v) := inferInstanceAs (Decidable
  ((u.val < 7 ∧ 7 ≤ v.val) ∨ (7 ≤ u.val ∧ v.val < 7)))

def nonNeighbors (u : Fin 14) : Finset (Fin 14) :=
  Finset.univ.filter (fun v => opposite u v ∧ (u, v) ∉ edges ∧ (v, u) ∉ edges)

def singleCover (u : Fin 14) : Finset (Fin 14) := insert u (nonNeighbors u)
def pairCover (u v : Fin 14) : Finset (Fin 14) := {u, v} ∪ (nonNeighbors u ∩ nonNeighbors v)

def leftPairs : Finset (Fin 14 × Fin 14) :=
  (Finset.univ ×ˢ Finset.univ).filter (fun e => e.1.val < 7 ∧ e.2.val < 7 ∧ e.1 ≠ e.2)

def independentCovers : Finset (Finset (Fin 14)) :=
  {left, right} ∪ ((Finset.univ.image singleCover) ∪
    (leftPairs.image (fun e => pairCover e.1 e.2)))

def Independent (A : Finset (Fin 14)) : Prop :=
  ∀ u ∈ A, ∀ v ∈ A, (u, v) ∉ edges

set_option maxHeartbeats 1000000 in
theorem common_nonNeighbors_right : ∀ r s : Fin 14, r ≠ s →
    7 ≤ r.val → 7 ≤ s.val → (nonNeighbors r ∩ nonNeighbors s).card = 2 := by decide

private theorem singleCover_mem (u : Fin 14) : singleCover u ∈ independentCovers := by
  apply Finset.mem_union_right
  apply Finset.mem_union_left
  exact Finset.mem_image.mpr ⟨u, Finset.mem_univ _, rfl⟩

private theorem pairCover_mem (u v : Fin 14) (hu : u.val < 7) (hv : v.val < 7)
    (huv : u ≠ v) : pairCover u v ∈ independentCovers := by
  apply Finset.mem_union_right
  apply Finset.mem_union_right
  refine Finset.mem_image.mpr ⟨(u, v), ?_, rfl⟩
  simp [leftPairs, hu, hv, huv]

private theorem mem_nonNeighbors {A : Finset (Fin 14)} (hA : Independent A)
    {u v : Fin 14} (hu : u ∈ A) (hv : v ∈ A) (hop : opposite u v) :
    v ∈ nonNeighbors u := by
  simp only [nonNeighbors, Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨hop, hA u hu v hv, hA v hv u hu⟩

theorem every_independent_covered (A : Finset (Fin 14)) (hA : Independent A) :
    ∃ I ∈ independentCovers, A ⊆ I := by
  classical
  by_cases hL : A ⊆ left
  · exact ⟨left, Finset.mem_union_left _ (by simp), hL⟩
  by_cases hR : A ⊆ right
  · exact ⟨right, Finset.mem_union_left _ (by simp), hR⟩
  obtain ⟨u, hu, hun⟩ := Finset.not_subset.mp hR
  have hul : u.val < 7 := by simpa [right] using hun
  obtain ⟨r, hr, hrn⟩ := Finset.not_subset.mp hL
  have hrr : 7 ≤ r.val := by simpa [left] using hrn
  by_cases hsingleL : ∀ v ∈ A, v.val < 7 → v = u
  · refine ⟨singleCover u, singleCover_mem u, ?_⟩
    intro a ha
    by_cases hal : a.val < 7
    · rw [hsingleL a ha hal]
      exact Finset.mem_insert_self _ _
    · apply Finset.mem_insert_of_mem
      exact mem_nonNeighbors hA hu ha (Or.inl ⟨hul, by omega⟩)
  push Not at hsingleL
  obtain ⟨v, hv, hvl, hvu⟩ := hsingleL
  have huv : u ≠ v := Ne.symm hvu
  by_cases hsingleR : ∀ s ∈ A, 7 ≤ s.val → s = r
  · refine ⟨singleCover r, singleCover_mem r, ?_⟩
    intro a ha
    by_cases har : 7 ≤ a.val
    · rw [hsingleR a ha har]
      exact Finset.mem_insert_self _ _
    · apply Finset.mem_insert_of_mem
      exact mem_nonNeighbors hA hr ha (Or.inr ⟨hrr, by omega⟩)
  push Not at hsingleR
  obtain ⟨s, hs, hsr, hsrne⟩ := hsingleR
  have hrs : r ≠ s := Ne.symm hsrne
  have hcard := common_nonNeighbors_right r s hrs hrr hsr
  have huN : u ∈ nonNeighbors r ∩ nonNeighbors s := by
    exact Finset.mem_inter.mpr ⟨mem_nonNeighbors hA hr hu (Or.inr ⟨hrr, hul⟩),
      mem_nonNeighbors hA hs hu (Or.inr ⟨hsr, hul⟩)⟩
  have hvN : v ∈ nonNeighbors r ∩ nonNeighbors s := by
    exact Finset.mem_inter.mpr ⟨mem_nonNeighbors hA hr hv (Or.inr ⟨hrr, hvl⟩),
      mem_nonNeighbors hA hs hv (Or.inr ⟨hsr, hvl⟩)⟩
  have hpairSub : ({u, v} : Finset (Fin 14)) ⊆ nonNeighbors r ∩ nonNeighbors s := by
    simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]
    exact ⟨huN, hvN⟩
  have hpair : ({u, v} : Finset (Fin 14)) = nonNeighbors r ∩ nonNeighbors s := by
    apply Finset.eq_of_subset_of_card_le hpairSub
    rw [hcard]
    simp [huv]
  refine ⟨pairCover u v, pairCover_mem u v hul hvl huv, ?_⟩
  intro a ha
  by_cases hal : a.val < 7
  · apply Finset.mem_union_left
    rw [hpair]
    exact Finset.mem_inter.mpr ⟨mem_nonNeighbors hA hr ha (Or.inr ⟨hrr, hal⟩),
      mem_nonNeighbors hA hs ha (Or.inr ⟨hsr, hal⟩)⟩
  · apply Finset.mem_union_right
    exact Finset.mem_inter.mpr ⟨mem_nonNeighbors hA hu ha (Or.inl ⟨hul, by omega⟩),
      mem_nonNeighbors hA hv ha (Or.inl ⟨hvl, by omega⟩)⟩

def listedNegatives : Finset (Finset (Fin 14)) :=
  {{0, 1, 2, 3, 4, 5, 6},
   {2, 4, 5, 6, 7},
   {1, 3, 4, 5, 8},
   {4, 5, 7, 8},
   {0, 2, 3, 4, 9},
   {2, 4, 7, 9},
   {3, 4, 8, 9},
   {1, 2, 3, 6, 10},
   {2, 6, 7, 10},
   {1, 3, 8, 10},
   {2, 3, 9, 10},
   {0, 1, 2, 5, 11},
   {2, 5, 7, 11},
   {1, 5, 8, 11},
   {0, 2, 9, 11},
   {1, 2, 10, 11},
   {2, 7, 9, 10, 11},
   {0, 1, 4, 6, 12},
   {4, 6, 7, 12},
   {1, 4, 8, 12},
   {0, 4, 9, 12},
   {4, 7, 8, 9, 12},
   {1, 6, 10, 12},
   {0, 1, 11, 12},
   {1, 8, 10, 11, 12},
   {0, 3, 5, 6, 13},
   {5, 6, 7, 13},
   {3, 5, 8, 13},
   {0, 3, 9, 13},
   {3, 6, 10, 13},
   {3, 8, 9, 10, 13},
   {0, 5, 11, 13},
   {5, 7, 8, 11, 13},
   {0, 6, 12, 13},
   {6, 7, 10, 12, 13},
   {0, 9, 11, 12, 13},
   {7, 8, 9, 10, 11, 12, 13}}

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
theorem covers_eq_listed : independentCovers = listedNegatives := by decide

theorem listed_count : listedNegatives.card = 37 := by decide

theorem every_independent_covered_by_list (A : Finset (Fin 14)) (hA : Independent A) :
    ∃ I ∈ listedNegatives, A ⊆ I := by
  simpa [covers_eq_listed] using every_independent_covered A hA


private theorem nn_props {u v : Fin 14} (hv : v ∈ nonNeighbors u) :
    opposite u v ∧ (u, v) ∉ edges ∧ (v, u) ∉ edges := by
  simpa only [nonNeighbors, Finset.mem_filter, Finset.mem_univ, true_and] using hv

private theorem opposite_pair_nonedge {u a b : Fin 14}
    (ha : opposite u a) (hb : opposite u b) : (a, b) ∉ edges := by
  intro he
  have hab := bipartite a b he
  rcases ha with ha | ha <;> rcases hb with hb | hb <;> omega

private theorem left_independent : Independent left := by
  intro a ha b hb he
  have hbl : b.val < 7 := by simpa [left] using hb
  have hab := bipartite a b he
  omega

private theorem right_independent : Independent right := by
  intro a ha b hb he
  have har : 7 ≤ a.val := by simpa [right] using ha
  have hab := bipartite a b he
  omega

private theorem singleCover_independent (u : Fin 14) : Independent (singleCover u) := by
  intro a ha b hb he
  rcases Finset.mem_insert.mp ha with rfl | ha
  · rcases Finset.mem_insert.mp hb with rfl | hb
    · have hbad := bipartite _ _ he
      omega
    · exact (nn_props hb).2.1 he
  · rcases Finset.mem_insert.mp hb with rfl | hb
    · exact (nn_props ha).2.2 he
    · exact opposite_pair_nonedge (nn_props ha).1 (nn_props hb).1 he

private theorem pairCover_independent (u v : Fin 14) (hu : u.val < 7) (hv : v.val < 7) :
    Independent (pairCover u v) := by
  intro a ha b hb he
  rcases Finset.mem_union.mp ha with ha | ha
  · rcases Finset.mem_union.mp hb with hb | hb
    · have hal : a.val < 7 := by
        simp only [Finset.mem_insert, Finset.mem_singleton] at ha
        rcases ha with rfl | rfl <;> assumption
      have hbl : b.val < 7 := by
        simp only [Finset.mem_insert, Finset.mem_singleton] at hb
        rcases hb with rfl | rfl <;> assumption
      have hab := bipartite a b he
      omega
    · obtain ⟨hbu, hbv⟩ := Finset.mem_inter.mp hb
      simp only [Finset.mem_insert, Finset.mem_singleton] at ha
      rcases ha with rfl | rfl
      · exact (nn_props hbu).2.1 he
      · exact (nn_props hbv).2.1 he
  · obtain ⟨hau, hav⟩ := Finset.mem_inter.mp ha
    rcases Finset.mem_union.mp hb with hb | hb
    · simp only [Finset.mem_insert, Finset.mem_singleton] at hb
      rcases hb with rfl | rfl
      · exact (nn_props hau).2.2 he
      · exact (nn_props hav).2.2 he
    · have hbu := (Finset.mem_inter.mp hb).1
      exact opposite_pair_nonedge (nn_props hau).1 (nn_props hbu).1 he

theorem covers_independent : ∀ I ∈ independentCovers, Independent I := by
  intro I hI
  rcases Finset.mem_union.mp hI with hI | hI
  · simp only [Finset.mem_insert, Finset.mem_singleton] at hI
    rcases hI with rfl | rfl
    · exact left_independent
    · exact right_independent
  · rcases Finset.mem_union.mp hI with hI | hI
    · obtain ⟨u, _, rfl⟩ := Finset.mem_image.mp hI
      exact singleCover_independent u
    · obtain ⟨⟨u, v⟩, huv, rfl⟩ := Finset.mem_image.mp hI
      have h := (Finset.mem_filter.mp huv).2
      exact pairCover_independent u v h.1 h.2.1

theorem listed_independent : ∀ I ∈ listedNegatives, Independent I := by
  rw [← covers_eq_listed]
  exact covers_independent


theorem critical_rows_complete (F : Finset (Fin 14) → Prop) (hmono : Monotone F)
    (hpos : ∀ e ∈ edges, F {e.1, e.2})
    (hneg : ∀ I ∈ listedNegatives, ¬ F I) :
    ∀ A : Finset (Fin 14), F A ↔ ∃ u v : Fin 14, (u, v) ∈ edges ∧ u ∈ A ∧ v ∈ A := by
  intro A
  constructor
  · intro hFA
    by_contra hn
    have hA : Independent A := by
      intro u hu v hv he
      exact hn ⟨u, v, he, hu, hv⟩
    obtain ⟨I, hI, hAI⟩ := every_independent_covered_by_list A hA
    exact hneg I hI (hmono hAI hFA)
  · rintro ⟨u, v, he, hu, hv⟩
    apply hmono (show ({u, v} : Finset (Fin 14)) ⊆ A from ?_) (hpos (u, v) he)
    intro a ha
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl
    · exact hu
    · exact hv

theorem critical_rows_iff (F : Finset (Fin 14) → Prop) (hmono : Monotone F) :
    (∀ A : Finset (Fin 14), F A ↔ ∃ u v : Fin 14, (u, v) ∈ edges ∧ u ∈ A ∧ v ∈ A) ↔
      ((∀ e ∈ edges, F {e.1, e.2}) ∧ ∀ I ∈ listedNegatives, ¬ F I) := by
  constructor
  · intro h
    constructor
    · intro e he
      apply (h _).mpr
      exact ⟨e.1, e.2, he, by simp, by simp⟩
    · intro I hI hFI
      obtain ⟨u, v, he, hu, hv⟩ := (h I).mp hFI
      exact listed_independent I hI u hu v hv he
  · rintro ⟨hpos, hneg⟩
    exact critical_rows_complete F hmono hpos hneg

end HeawoodFixtureAudit
