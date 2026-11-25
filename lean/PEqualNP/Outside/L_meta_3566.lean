import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3566

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm

def CutWitness {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (z : Fin n) (C : Circuit) : Prop :=
  ∃ D : Circuit, IsAO2 n D ∧
    circuitFun n D = (fun y : Fin n → Bool =>
      @decide (∃ a b : Fin n, (G.deleteEdges (G.incidenceSet z)).Adj a b ∧
        y a = true ∧ y b = true) (Classical.propDecidable _)) ∧
    D.size + G.degree z ≤ C.size ∧
    ((∃ S : Finset (Fin n),
      CoverPromise.IsVertexCover (G.deleteEdges (G.incidenceSet z)) S ∧
      ∀ T : Finset (Fin n), CoverPromise.IsVertexCover G T → S.card < T.card) →
      D.size + G.degree z + 1 ≤ C.size)

lemma cutWitness_mono {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (z : Fin n) (C C' : Circuit) (hsize : C.size ≤ C'.size)
    (h : CutWitness G z C) : CutWitness G z C' := by
  obtain ⟨D, hAO, hfun, hsizeD, hbonus⟩ := h
  exact ⟨D, hAO, hfun, hsizeD.trans hsize, fun hdrop => (hbonus hdrop).trans hsize⟩

lemma exists_least {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hAO : IsAO2 n C)
    (hfun : circuitFun n C = NestedCover.graphFun G ∅) :
    ∃ D : Circuit, IsLeastAO G D ∧ D.size ≤ C.size := by
  classical
  let P : ℕ → Prop := fun k => ∃ D : Circuit,
    IsAO2 n D ∧ circuitFun n D = NestedCover.graphFun G ∅ ∧ D.size = k
  have hex : ∃ k, P k := ⟨C.size, C, hAO, hfun, rfl⟩
  obtain ⟨D, hD, hfunD, hsizeD⟩ := Nat.find_spec hex
  have hmin : ∀ E : Circuit, IsAO2 n E →
      circuitFun n E = NestedCover.graphFun G ∅ → D.size ≤ E.size := by
    intro E hE hfunE
    rw [hsizeD]
    exact Nat.find_min' hex ⟨E, hE, hfunE, rfl⟩
  exact ⟨D, ⟨hD, hfunD, hmin⟩, hmin C hAO hfun⟩

lemma peel_of_least {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hpos : ∃ z : Fin n, 0 < G.degree z)
    (h : ∀ C : Circuit, IsLeastAO G C →
      ∃ z : Fin n, 0 < G.degree z ∧ CutWitness G z C) :
    ∃ z : Fin n, 0 < G.degree z ∧ ∀ C : Circuit, IsAO2 n C →
      circuitFun n C = NestedCover.graphFun G ∅ → CutWitness G z C := by
  classical
  by_cases hex : ∃ C : Circuit,
      IsAO2 n C ∧ circuitFun n C = NestedCover.graphFun G ∅
  · obtain ⟨C, hAO, hfun⟩ := hex
    obtain ⟨D, hD, _⟩ := exists_least G C hAO hfun
    obtain ⟨z, hz, hcut⟩ := h D hD
    exact ⟨z, hz, fun E hE hfunE =>
      cutWitness_mono G z D E (hD.2.2 E hE hfunE) hcut⟩
  · obtain ⟨z, hz⟩ := hpos
    exact ⟨z, hz, fun C hAO hfun => (hex ⟨C, hAO, hfun⟩).elim⟩

lemma cut_adj_iff {n : ℕ} (G : SimpleGraph (Fin n)) (z a b : Fin n) :
    (G.deleteEdges (G.incidenceSet z)).Adj a b ↔ G.Adj a b ∧ a ≠ z ∧ b ≠ z := by
  rw [SimpleGraph.deleteEdges_adj, SimpleGraph.mk'_mem_incidenceSet_iff]
  tauto

lemma twin_leaves_no_cover_drop {n : ℕ} (G : SimpleGraph (Fin n))
    (u v w : Fin n) (huv : u ≠ v) (huw : G.Adj u w) (hvw : G.Adj v w)
    (hu : ∀ t : Fin n, G.Adj u t → t = w)
    (hv : ∀ t : Fin n, G.Adj v t → t = w) :
    ¬ ∃ S : Finset (Fin n),
      CoverPromise.IsVertexCover (G.deleteEdges (G.incidenceSet u)) S ∧
      ∀ T : Finset (Fin n), CoverPromise.IsVertexCover G T → S.card < T.card := by
  rintro ⟨S, hS, hsmall⟩
  let T := insert w (S.erase v)
  have hT : CoverPromise.IsVertexCover G T := by
    intro a b hab
    by_cases hau : a = u
    · subst a
      have hbw := hu b hab
      right
      simp [T, hbw]
    by_cases hbu : b = u
    · subst b
      have haw := hu a hab.symm
      left
      simp [T, haw]
    by_cases hav : a = v
    · subst a
      have hbw := hv b hab
      right
      simp [T, hbw]
    by_cases hbv : b = v
    · subst b
      have haw := hv a hab.symm
      left
      simp [T, haw]
    obtain ha | hb := hS a b ((cut_adj_iff G u a b).mpr ⟨hab, hau, hbu⟩)
    · exact Or.inl (Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨hav, ha⟩))
    · exact Or.inr (Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨hbv, hb⟩))
  have hcard : T.card ≤ S.card := by
    obtain hvS | hwS := hS v w
      ((cut_adj_iff G u v w).mpr ⟨hvw, huv.symm, huw.ne.symm⟩)
    · have h1 := Finset.card_insert_le w (S.erase v)
      have h2 := Finset.card_erase_of_mem hvS
      have h3 : 0 < S.card := Finset.card_pos.mpr ⟨v, hvS⟩
      dsimp [T]
      omega
    · have hw : w ∈ S.erase v := Finset.mem_erase.mpr ⟨hvw.ne.symm, hwS⟩
      dsimp [T]
      rw [Finset.card_insert_of_mem hw]
      exact Finset.card_le_card (Finset.erase_subset _ _)
  exact (Nat.not_lt_of_ge hcard) (hsmall T hT)

lemma cutWitness_of_twin_leaves {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (u v w : Fin n) (huv : u ≠ v) (huw : G.Adj u w) (hvw : G.Adj v w)
    (hu : ∀ t : Fin n, G.Adj u t → t = w)
    (hv : ∀ t : Fin n, G.Adj v t → t = w)
    (C D : Circuit) (hAO : IsAO2 n D)
    (hfun : circuitFun n D = (fun y : Fin n → Bool =>
      @decide (∃ a b : Fin n, (G.deleteEdges (G.incidenceSet u)).Adj a b ∧
        y a = true ∧ y b = true) (Classical.propDecidable _)))
    (hsize : D.size + 1 ≤ C.size) : CutWitness G u C := by
  have hdeg : G.degree u = 1 :=
    SimpleGraph.degree_eq_one_iff_existsUnique_adj.mpr ⟨w, huw, hu⟩
  refine ⟨D, hAO, hfun, by simpa [hdeg] using hsize, ?_⟩
  intro hdrop
  exact (twin_leaves_no_cover_drop G u v w huv huw hvw hu hv hdrop).elim

end PEqualNP.Outside.L_meta_3566
