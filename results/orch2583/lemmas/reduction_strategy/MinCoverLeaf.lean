import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2583_aux.MinCover

variable {V : Type} [Fintype V] [DecidableEq V]

def Cover (G : SimpleGraph V) (K : Finset V) : Prop :=
  ∀ u v, G.Adj u v → u ∈ K ∨ v ∈ K

def Minimal (G : SimpleGraph V) (K : Finset V) : Prop :=
  Cover G K ∧ ∀ u ∈ K, ∃ v, G.Adj u v ∧ v ∉ K

noncomputable def family (G : SimpleGraph V) : Finset (Finset V) := by
  classical
  exact Finset.univ.filter (Minimal G)

noncomputable def weight (G : SimpleGraph V) : ℕ :=
  ∑ K ∈ family G, K.card

noncomputable def neighbors (G : SimpleGraph V) (v : V) : Finset V := by
  classical
  exact Finset.univ.filter (G.Adj v)

def away (G : SimpleGraph V) (S : Finset V) : SimpleGraph V where
  Adj u v := G.Adj u v ∧ u ∉ S ∧ v ∉ S
  symm := ⟨by intro u v h; exact ⟨h.1.symm, h.2.2, h.2.1⟩⟩
  loopless := ⟨by intro v h; exact G.loopless v h.1⟩

lemma mem_family (G : SimpleGraph V) (K : Finset V) : K ∈ family G ↔ Minimal G K := by
  classical
  simp [family]

lemma mem_neighbors (G : SimpleGraph V) (u v : V) : u ∈ neighbors G v ↔ G.Adj v u := by
  classical
  simp [neighbors]

lemma exists_minimal (G : SimpleGraph V) : ∃ K : Finset V, Minimal G K := by
  classical
  let P (t : ℕ) := ∃ K : Finset V, Cover G K ∧ K.card = t
  have ex : ∃ t, P t := ⟨Fintype.card V, Finset.univ, by intro u v h; simp, by simp⟩
  obtain ⟨K, hc, hk⟩ := Nat.find_spec ex
  refine ⟨K, hc, ?_⟩
  intro u hu
  by_contra! hno
  have erased : Cover G (K.erase u) := by
    intro a b hab
    rcases hc a b hab with ha | hb
    · by_cases hau : a = u
      · subst a
        exact Or.inr (Finset.mem_erase.mpr ⟨hab.ne.symm, hno b hab⟩)
      · exact Or.inl (Finset.mem_erase.mpr ⟨hau, ha⟩)
    · by_cases hbu : b = u
      · subst b
        exact Or.inl (Finset.mem_erase.mpr ⟨hab.ne, hno a hab.symm⟩)
      · exact Or.inr (Finset.mem_erase.mpr ⟨hbu, hb⟩)
  have bound := Nat.find_min' ex (show P (K.erase u).card from ⟨_, erased, rfl⟩)
  have smaller := Finset.card_erase_lt_of_mem hu
  omega

lemma family_nonempty (G : SimpleGraph V) : (family G).Nonempty := by
  obtain ⟨K, hk⟩ := exists_minimal G
  exact ⟨K, (mem_family G K).mpr hk⟩

lemma minimal_away_disjoint (G : SimpleGraph V) (S K : Finset V)
    (hk : Minimal (away G S) K) : Disjoint K S := by
  apply Finset.disjoint_left.mpr
  intro u hu hs
  obtain ⟨v, hv, _⟩ := hk.2 u hu
  exact hv.2.1 hs

lemma leaf_lift (G : SimpleGraph V) (u v : V) (edge : G.Adj u v)
    (leaf : ∀ w, G.Adj u w → w = v) (K : Finset V)
    (hk : Minimal (away G {v}) K) : Minimal G (insert v K) := by
  have uv : u ≠ v := edge.ne
  have vk : v ∉ K := by
    intro h
    obtain ⟨w, hw, _⟩ := hk.2 v h
    exact hw.2.1 (by simp)
  have uk : u ∉ K := by
    intro h
    obtain ⟨w, hw, _⟩ := hk.2 u h
    exact hw.2.2 (by simp [leaf w hw.1])
  constructor
  · intro a b hab
    by_cases hav : a = v
    · exact Or.inl (by simp [hav])
    by_cases hbv : b = v
    · exact Or.inr (by simp [hbv])
    exact (hk.1 a b ⟨hab, by simpa, by simpa⟩).imp
      Finset.mem_insert_of_mem Finset.mem_insert_of_mem
  · intro a ha
    rcases Finset.mem_insert.mp ha with rfl | ha
    · exact ⟨u, edge.symm, by simpa [uv] using uk⟩
    · obtain ⟨b, hb, hbk⟩ := hk.2 a ha
      refine ⟨b, hb.1, ?_⟩
      simp only [Finset.mem_insert, not_or]
      exact ⟨by simpa using hb.2.2, hbk⟩

lemma neighbor_lift (G : SimpleGraph V) (v : V) (T : Finset V)
    (ht : Minimal (away G (insert v (neighbors G v))) T) :
    Minimal G (T ∪ neighbors G v) ∧ v ∉ T ∪ neighbors G v := by
  classical
  have awayT := minimal_away_disjoint G (insert v (neighbors G v)) T ht
  have vn : v ∉ neighbors G v := by simp [mem_neighbors]
  have vt : v ∉ T := by
    intro h; exact Finset.disjoint_left.mp awayT h (by simp)
  constructor
  · constructor
    · intro a b hab
      by_cases han : a ∈ neighbors G v
      · exact Or.inl (Finset.mem_union_right _ han)
      by_cases hbn : b ∈ neighbors G v
      · exact Or.inr (Finset.mem_union_right _ hbn)
      have hav : a ≠ v := by intro h; subst a; exact hbn ((mem_neighbors G b v).mpr hab)
      have hbv : b ≠ v := by intro h; subst b; exact han ((mem_neighbors G a v).mpr hab.symm)
      exact (ht.1 a b ⟨hab, by simp [hav, han], by simp [hbv, hbn]⟩).imp
        (Finset.mem_union_left _) (Finset.mem_union_left _)
    · intro a ha
      rcases Finset.mem_union.mp ha with hat | han
      · obtain ⟨b, hb, hbt⟩ := ht.2 a hat
        refine ⟨b, hb.1, ?_⟩
        simp only [Finset.mem_union, not_or]
        exact ⟨hbt, fun h => hb.2.2 (Finset.mem_insert_of_mem h)⟩
      · exact ⟨v, ((mem_neighbors G a v).mp han).symm, by simp [vt, vn]⟩
  · simp [vt, vn]

lemma leaf_weight (G : SimpleGraph V) (u v : V) (edge : G.Adj u v)
    (leaf : ∀ w, G.Adj u w → w = v) :
    weight (away G {v}) + (family (away G {v})).card + (neighbors G v).card ≤ weight G := by
  classical
  let H := away G {v}
  have absent : ∀ K ∈ family H, v ∉ K := by
    intro K hk hv
    obtain ⟨w, hw, _⟩ := ((mem_family H K).mp hk).2 v hv
    exact hw.2.1 (by simp)
  have inj : Set.InjOn (fun K : Finset V => insert v K) (family H) := by
    intro A ha B hb eq
    have e := congrArg (fun S : Finset V => S.erase v) eq
    simpa [absent A ha, absent B hb] using e
  let F := (family H).image (fun K : Finset V => insert v K)
  have sub : F ⊆ family G := by
    intro K hk
    obtain ⟨K, hk, rfl⟩ := Finset.mem_image.mp hk
    exact (mem_family G _).mpr (leaf_lift G u v edge leaf K ((mem_family H K).mp hk))
  have sumF : (∑ K ∈ F, K.card) = weight H + (family H).card := by
    rw [Finset.sum_image inj]
    calc
      ∑ K ∈ family H, (insert v K).card = ∑ K ∈ family H, (K.card + 1) := by
        apply Finset.sum_congr rfl
        intro K hk
        exact Finset.card_insert_of_notMem (absent K hk)
      _ = weight H + (family H).card := by simp [weight, Finset.sum_add_distrib]
  obtain ⟨T, ht⟩ := exists_minimal (away G (insert v (neighbors G v)))
  obtain ⟨hmin, hout⟩ := neighbor_lift G v T ht
  let Kout := T ∪ neighbors G v
  have notin : Kout ∉ F := by
    intro h
    obtain ⟨K, _, heq⟩ := Finset.mem_image.mp h
    apply hout
    rw [← heq]
    exact Finset.mem_insert_self _ _
  have allsub : insert Kout F ⊆ family G := by
    intro K hk
    rcases Finset.mem_insert.mp hk with rfl | hk
    · exact (mem_family G _).mpr hmin
    · exact sub hk
  have bound : (∑ K ∈ insert Kout F, K.card) ≤ weight G :=
    Finset.sum_le_sum_of_subset allsub
  rw [Finset.sum_insert notin, sumF] at bound
  have degree : (neighbors G v).card ≤ Kout.card :=
    Finset.card_le_card (Finset.subset_union_right : neighbors G v ⊆ T ∪ neighbors G v)
  change weight H + (family H).card + (neighbors G v).card ≤ weight G
  omega

lemma leaf_weight_succ (G : SimpleGraph V) (u v : V) (edge : G.Adj u v)
    (leaf : ∀ w, G.Adj u w → w = v) :
    weight (away G {v}) + 1 + (neighbors G v).card ≤ weight G := by
  have h := leaf_weight G u v edge leaf
  have hn := Finset.card_pos.mpr (family_nonempty (away G {v}))
  omega

end PEqualNP.Outside.L_meta_2583_aux.MinCover
