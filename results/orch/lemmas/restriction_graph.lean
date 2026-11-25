import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_5012

lemma noFourCycle_of_injective {m n : ℕ}
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (H : SimpleGraph (Fin m)) [DecidableRel H.Adj]
    (f : Fin m → Fin n) (hf : Function.Injective f)
    (hedge : ∀ u v, H.Adj u v → G.Adj (f u) (f v))
    (hG : PEqualNP.TopForm.NoFourCycle G) :
    PEqualNP.TopForm.NoFourCycle H := by
  intro a b hab
  apply Finset.card_le_one.mpr
  intro x hx y hy
  apply hf
  have hab' : f a ≠ f b := fun h => hab (hf h)
  apply Finset.card_le_one.mp (hG (f a) (f b) hab')
  · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      hedge a x (Finset.mem_filter.mp hx).2.1,
      hedge b x (Finset.mem_filter.mp hx).2.2⟩
  · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      hedge a y (Finset.mem_filter.mp hy).2.1,
      hedge b y (Finset.mem_filter.mp hy).2.2⟩

lemma bipartite_of_embedding {m n : ℕ}
    (G : SimpleGraph (Fin n)) (H : SimpleGraph (Fin m))
    (f : Fin m → Fin n) (s : Fin n → Bool)
    (hedge : ∀ u v, H.Adj u v → G.Adj (f u) (f v))
    (hs : ∀ u v, G.Adj u v → s u ≠ s v) :
    ∀ u v, H.Adj u v → (s ∘ f) u ≠ (s ∘ f) v := by
  intro u v huv
  exact hs (f u) (f v) (hedge u v huv)

lemma graphFun_zero_extension {m n : ℕ}
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (H : SimpleGraph (Fin m)) [DecidableRel H.Adj]
    (f : Fin m → Fin n)
    (hedge : ∀ u v, H.Adj u v ↔ G.Adj (f u) (f v))
    (x : Fin m → Bool) (y : Fin n → Bool)
    (hy : ∀ i, y i = true ↔ ∃ u, f u = i ∧ x u = true) :
    PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ y =
      PEqualNP.MetaComplexity.NestedCover.graphFun H ∅ x := by
  simp only [PEqualNP.MetaComplexity.NestedCover.graphFun,
    Finset.notMem_empty, false_and, exists_false, decide_false, Bool.false_or]
  apply decide_eq_decide.mpr
  constructor
  · rintro ⟨a, b, hab, ha, hb⟩
    obtain ⟨u, hu, hxu⟩ := (hy a).mp ha
    obtain ⟨v, hv, hxv⟩ := (hy b).mp hb
    subst a
    subst b
    exact ⟨u, v, (hedge u v).mpr hab, hxu, hxv⟩
  · rintro ⟨u, v, huv, hu, hv⟩
    exact ⟨f u, f v, (hedge u v).mp huv,
      (hy (f u)).mpr ⟨u, rfl, hu⟩, (hy (f v)).mpr ⟨v, rfl, hv⟩⟩

lemma graphFun_eq_of_edge_tests {n : ℕ}
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (f : (Fin n → Bool) → Bool)
    (hbelow : ∀ x, f x = true →
      PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ x = true)
    (hmono : ∀ x y, (∀ i, x i = true → y i = true) → f x = true → f y = true)
    (htest : ∀ u v, G.Adj u v → f (PEqualNP.EdgeOwnership.pairInput u v) = true) :
    f = PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ := by
  funext x
  apply Bool.eq_iff_iff.mpr
  constructor
  · exact hbelow x
  · intro hx
    simp only [PEqualNP.MetaComplexity.NestedCover.graphFun,
      Finset.notMem_empty, false_and, exists_false, decide_false,
      Bool.false_or, decide_eq_true_eq] at hx
    obtain ⟨u, v, huv, hu, hv⟩ := hx
    apply hmono (PEqualNP.EdgeOwnership.pairInput u v) x _ (htest u v huv)
    intro i hi
    have hi' : i = u ∨ i = v := by
      simpa only [PEqualNP.EdgeOwnership.pairInput, decide_eq_true_eq] using hi
    rcases hi' with rfl | rfl
    · exact hu
    · exact hv

lemma leastAO_of_lifting {m n : ℕ}
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (H : SimpleGraph (Fin m)) [DecidableRel H.Adj]
    (C D : PEqualNP.CircuitLowerBounds.Circuit) (k : ℕ)
    (hC : PEqualNP.TopForm.IsLeastAO G C)
    (hD : PEqualNP.TopForm.IsAO2 m D)
    (hfun : PEqualNP.MetaComplexity.circuitFun m D =
      PEqualNP.MetaComplexity.NestedCover.graphFun H ∅)
    (hsize : D.size + k ≤ C.size)
    (hlift : ∀ E : PEqualNP.CircuitLowerBounds.Circuit,
      PEqualNP.TopForm.IsAO2 m E →
      PEqualNP.MetaComplexity.circuitFun m E =
        PEqualNP.MetaComplexity.NestedCover.graphFun H ∅ →
      ∃ L : PEqualNP.CircuitLowerBounds.Circuit,
        PEqualNP.TopForm.IsAO2 n L ∧
        PEqualNP.MetaComplexity.circuitFun n L =
          PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ ∧
        L.size ≤ E.size + k) :
    PEqualNP.TopForm.IsLeastAO H D := by
  refine ⟨hD, hfun, ?_⟩
  intro E hE hEfun
  obtain ⟨L, hL, hLfun, hLsize⟩ := hlift E hE hEfun
  have hCL : C.size ≤ L.size := hC.2.2 L hL hLfun
  omega

end PEqualNP.Outside.L_meta_5012
