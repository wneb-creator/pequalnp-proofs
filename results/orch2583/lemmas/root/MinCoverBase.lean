import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2583_aux.MinCover

variable {V : Type*} [Fintype V] [DecidableEq V]

def Cover (G : SimpleGraph V) (K : Finset V) : Prop :=
  ∀ u v, G.Adj u v → u ∈ K ∨ v ∈ K

def Minimal (G : SimpleGraph V) (K : Finset V) : Prop :=
  Cover G K ∧ ∀ u ∈ K, ∃ v, G.Adj u v ∧ v ∉ K

noncomputable def neighbors (G : SimpleGraph V) (v : V) : Finset V := by
  classical
  exact Finset.univ.filter (G.Adj v)

noncomputable def family (G : SimpleGraph V) : Finset (Finset V) := by
  classical
  exact Finset.univ.filter (Minimal G)

noncomputable def weight (G : SimpleGraph V) : ℕ :=
  ∑ K ∈ family G, K.card

noncomputable def replacement (G : SimpleGraph V) (L : Finset V) (v : V) : Finset V :=
  L.erase v ∪ neighbors G v

lemma mem_neighbors (G : SimpleGraph V) (u v : V) : u ∈ neighbors G v ↔ G.Adj v u := by
  classical
  simp [neighbors]

lemma mem_family (G : SimpleGraph V) (K : Finset V) : K ∈ family G ↔ Minimal G K := by
  classical
  simp [family]

lemma replacement_minimal (G : SimpleGraph V) (L R : Finset V)
    (dis : Disjoint L R)
    (cross : ∀ u v, G.Adj u v → (u ∈ L ∧ v ∈ R) ∨ (u ∈ R ∧ v ∈ L))
    (degree : ∀ u ∈ L, 2 ≤ (neighbors G u).card)
    (common : ∀ u ∈ L, ∀ v ∈ L, u ≠ v →
      (neighbors G u ∩ neighbors G v).card ≤ 1)
    (v : V) (hv : v ∈ L) : Minimal G (replacement G L v) := by
  classical
  have outside (a b : V) (ha : a ∈ L) (hab : G.Adj a b) : b ∉ L := by
    rcases cross a b hab with h | h
    · exact fun hb => Finset.disjoint_left.mp dis hb h.2
    · exact False.elim (Finset.disjoint_left.mp dis ha h.1)
  constructor
  · intro a b hab
    rcases cross a b hab with h | h
    · by_cases hav : a = v
      · subst a
        exact Or.inr (Finset.mem_union_right _ ((mem_neighbors G b v).2 hab))
      · exact Or.inl (Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨hav, h.1⟩))
    · by_cases hbv : b = v
      · subst b
        exact Or.inl (Finset.mem_union_right _ ((mem_neighbors G a v).2 hab.symm))
      · exact Or.inr (Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨hbv, h.2⟩))
  · intro u hu
    rcases Finset.mem_union.mp hu with hu | hu
    · obtain ⟨huv, huL⟩ := Finset.mem_erase.mp hu
      have hnsub : ¬ neighbors G u ⊆ neighbors G v := by
        intro hsub
        have hh : neighbors G u ⊆ neighbors G u ∩ neighbors G v := fun w hw =>
          Finset.mem_inter.mpr ⟨hw, hsub hw⟩
        have hcard := Finset.card_le_card hh
        have hd := degree u huL
        have hc := common u huL v hv huv
        omega
      obtain ⟨w, hwu, hwv⟩ := Finset.not_subset.mp hnsub
      have huw := (mem_neighbors G w u).1 hwu
      refine ⟨w, huw, ?_⟩
      intro hw
      rcases Finset.mem_union.mp hw with hw | hw
      · exact outside u w huL huw (Finset.mem_of_mem_erase hw)
      · exact hwv hw
    · refine ⟨v, ((mem_neighbors G u v).1 hu).symm, ?_⟩
      intro hvm
      rcases Finset.mem_union.mp hvm with hvm | hvm
      · exact Finset.not_mem_erase v L hvm
      · exact G.loopless v ((mem_neighbors G v v).1 hvm)

lemma replacement_injective (G : SimpleGraph V) (L : Finset V) :
    Set.InjOn (replacement G L) L := by
  classical
  intro u hu v hv heq
  by_contra hne
  have huin : u ∈ replacement G L v :=
    Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨hne, hu⟩)
  rw [← heq] at huin
  rcases Finset.mem_union.mp huin with h | h
  · exact Finset.not_mem_erase u L h
  · exact G.loopless u ((mem_neighbors G u u).1 h)

end PEqualNP.Outside.L_meta_2583_aux.MinCover
