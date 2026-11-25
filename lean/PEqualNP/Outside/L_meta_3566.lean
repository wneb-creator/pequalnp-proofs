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

end PEqualNP.Outside.L_meta_3566
