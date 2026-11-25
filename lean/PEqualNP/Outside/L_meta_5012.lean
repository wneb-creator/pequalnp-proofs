import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_5012

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.MetaComplexity

lemma replacement_isLeastAO {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {C D : Circuit} (hC : IsLeastAO G C) (hD : IsAO2 n D)
    (hfun : circuitFun n D = NestedCover.graphFun G ∅) (hsize : D.size ≤ C.size) :
    IsLeastAO G D := by
  refine ⟨hD, hfun, ?_⟩
  intro E hE hEfun
  exact hsize.trans (hC.2.2 E hE hEfun)

lemma replacement_size_eq {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {C D : Circuit} (hC : IsLeastAO G C) (hD : IsAO2 n D)
    (hfun : circuitFun n D = NestedCover.graphFun G ∅) (hsize : D.size ≤ C.size) :
    D.size = C.size :=
  Nat.le_antisymm hsize (hC.2.2 D hD hfun)

lemma replacement_junk_ne_one
    (hfirst : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
      (C : Circuit) (s : Fin n → Bool),
      (∀ u v : Fin n, G.Adj u v → s u ≠ s v) → NoFourCycle G → IsLeastAO G C →
      (junk G C).card ≠ 1)
    {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C D : Circuit}
    (s : Fin n → Bool) (hs : ∀ u v : Fin n, G.Adj u v → s u ≠ s v)
    (hfour : NoFourCycle G) (hC : IsLeastAO G C) (hD : IsAO2 n D)
    (hfun : circuitFun n D = NestedCover.graphFun G ∅) (hsize : D.size ≤ C.size) :
    (junk G D).card ≠ 1 :=
  hfirst n G D s hs hfour (replacement_isLeastAO hC hD hfun hsize)

lemma junk_card_le_size {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) : (junk G C).card ≤ C.size := by
  simpa only [junk, gatesWhere, Circuit.size, Finset.card_range] using
    Finset.card_filter_le (Finset.range C.gates.length)
      (fun j => PEqualNP.CleanedNonEdge.IsDirtyAnd n G C j)

lemma edge_exists_of_nonempty_junk {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {C : Circuit} (hC : IsLeastAO G C) (hj : (junk G C).Nonempty) :
    ∃ u v : Fin n, G.Adj u v := by
  by_contra hnone
  have hn : ∀ u v : Fin n, ¬ G.Adj u v := by simpa only [not_exists] using hnone
  let D : Circuit := ⟨[], n⟩
  have hD : IsAO2 n D := by
    simp [D, IsAO2, PEqualNP.EdgeOwnership.AndOrOnly, NestedCover.ReadsBack]
  have hfun : circuitFun n D = NestedCover.graphFun G ∅ := by
    funext x
    simp [D, circuitFun, Circuit.eval, Circuit.wires, NestedCover.graphFun, hn]
  have hsize : C.size ≤ 0 := hC.2.2 D hD hfun
  have hjpos : 0 < (junk G C).card := Finset.card_pos.mpr hj
  exact (Nat.not_lt_zero _) (hjpos.trans_le ((junk_card_le_size G C).trans hsize))

end PEqualNP.Outside.L_meta_5012
