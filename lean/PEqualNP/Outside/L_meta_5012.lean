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

end PEqualNP.Outside.L_meta_5012
