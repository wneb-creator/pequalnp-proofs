import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2732_aux.RobustMatching

def point (i : Fin 7) : Fin 14 :=
  ([0, 1, 2, 3, 4, 5, 6] : List (Fin 14)).getD i.val 0

def line (r : Fin 3) (i : Fin 7) : Fin 14 :=
  (([[7, 9, 8, 12, 13, 10, 11], [8, 7, 13, 11, 10, 12, 9], [10, 13, 12, 7, 11, 9, 8]] : List (List (Fin 14))).getD r.val []).getD i.val 0

def index (r : Fin 3) (v : Fin 14) : Fin 7 :=
  (([[0, 1, 2, 3, 4, 5, 6, 0, 2, 1, 5, 6, 3, 4], [0, 1, 2, 3, 4, 5, 6, 1, 0, 6, 4, 3, 5, 2], [0, 1, 2, 3, 4, 5, 6, 3, 6, 5, 0, 4, 2, 1]] : List (List (Fin 7))).getD r.val []).getD v.val 0

lemma matching_indices : ∀ r : Fin 3, ∀ i : Fin 7,
    index r (point i) = i ∧ index r (line r i) = i := by decide +kernel

lemma matching_edges : ∀ r : Fin 3, ∀ i : Fin 7,
    ((point i).val, (line r i).val) ∈
      [(0,7),(0,8),(0,10),(1,7),(1,9),(1,13),(2,8),(2,12),(2,13),
       (3,7),(3,11),(3,12),(4,10),(4,11),(4,13),(5,9),(5,10),(5,12),
       (6,8),(6,9),(6,11)] := by decide +kernel

lemma indexed_edges_injective : Function.Injective
    (fun ri : Fin 3 × Fin 7 => (point ri.2, line ri.1 ri.2)) := by decide +kernel

lemma surviving_matching (bad : Finset (Fin 3 × Fin 7)) (hbad : bad.card ≤ 2) :
    ∃ r : Fin 3, ∀ i : Fin 7, (r, i) ∉ bad := by
  classical
  by_contra hn
  push Not at hn
  have cover : (Finset.univ : Finset (Fin 3)) ⊆ bad.image Prod.fst := by
    intro r _
    obtain ⟨i, hi⟩ := hn r
    exact Finset.mem_image.mpr ⟨(r, i), hi, rfl⟩
  have h1 := Finset.card_le_card cover
  have h2 := Finset.card_image_le (s := bad) (f := Prod.fst)
  simp only [Finset.card_univ, Fintype.card_fin] at h1
  omega

lemma cover_seven_after_two (T : Finset (Fin 14)) (bad : Finset (Fin 3 × Fin 7))
    (hbad : bad.card ≤ 2)
    (cover : ∀ r : Fin 3, ∀ i : Fin 7, (r, i) ∉ bad →
      point i ∈ T ∨ line r i ∈ T) :
    7 ≤ T.card := by
  classical
  obtain ⟨r, hr⟩ := surviving_matching bad hbad
  have sub : (Finset.univ : Finset (Fin 7)) ⊆ T.image (index r) := by
    intro i _
    obtain ⟨hp, hl⟩ := matching_indices r i
    rcases cover r i (hr i) with h | h
    · exact Finset.mem_image.mpr ⟨point i, h, hp⟩
    · exact Finset.mem_image.mpr ⟨line r i, h, hl⟩
  have h1 := Finset.card_le_card sub
  have h2 := Finset.card_image_le (s := T) (f := index r)
  simp only [Finset.card_univ, Fintype.card_fin] at h1
  omega

lemma cover_seven_of_nineteen (T : Finset (Fin 14)) (kept : Finset (Fin 3 × Fin 7))
    (hkept : 19 ≤ kept.card)
    (cover : ∀ ri ∈ kept, point ri.2 ∈ T ∨ line ri.1 ri.2 ∈ T) :
    7 ≤ T.card := by
  classical
  let bad := Finset.univ \ kept
  have count : bad.card + kept.card = 21 := by
    simpa [bad] using Finset.card_sdiff_add_card_eq_card (Finset.subset_univ kept)
  have hbad : bad.card ≤ 2 := by omega
  apply cover_seven_after_two T bad hbad
  intro r i hi
  have hri : (r, i) ∈ kept := by
    by_contra hnot
    exact hi (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hnot⟩)
  exact cover (r, i) hri

lemma indexed_sym_edges_injective : Function.Injective
    (fun ri : Fin 3 × Fin 7 => s(point ri.2, line ri.1 ri.2)) := by decide +kernel

lemma kept_edge_card (J : SimpleGraph (Fin 14)) [DecidableRel J.Adj]
    (kept : Finset (Fin 3 × Fin 7))
    (present : ∀ ri ∈ kept, J.Adj (point ri.2) (line ri.1 ri.2)) :
    kept.card ≤ J.edgeFinset.card := by
  classical
  have sub : kept.image (fun ri => s(point ri.2, line ri.1 ri.2)) ⊆ J.edgeFinset := by
    intro e he
    obtain ⟨ri, hri, rfl⟩ := Finset.mem_image.mp he
    exact J.mem_edgeFinset.mpr (present ri hri)
  have h := Finset.card_le_card sub
  rw [Finset.card_image_of_injective kept indexed_sym_edges_injective] at h
  exact h

lemma graph_bound_of_nineteen (J : SimpleGraph (Fin 14)) [DecidableRel J.Adj]
    (kept : Finset (Fin 3 × Fin 7)) (hkept : 19 ≤ kept.card)
    (present : ∀ ri ∈ kept, J.Adj (point ri.2) (line ri.1 ri.2))
    (T : Finset (Fin 14)) (cover : ∀ u v, J.Adj u v → u ∈ T ∨ v ∈ T) :
    26 ≤ J.edgeFinset.card + T.card := by
  have hc : 7 ≤ T.card := cover_seven_of_nineteen T kept hkept
    (fun ri hri => cover _ _ (present ri hri))
  have he := kept_edge_card J kept present
  omega

end PEqualNP.Outside.L_meta_2732_aux.RobustMatching
