namespace PEqualNP.Outside.L_meta_1477.SingletonIntegration

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm
  PEqualNP.EdgeOwnership OneJunk Structural StructuralMasks MaskGrouping TwoProductCentreless

lemma plane_singleton_other_size [DecidableRel planeGraph.Adj]
    (C : Circuit) (hL : IsLeastAO planeGraph C) (hTF : TopForm planeGraph C)
    (g h : ℕ) (hjunk : junk planeGraph C = {g,h}) (hgh : g≠h)
    (hpureg : ∀ b : Fin 2, ∀ k < C.gates.length, (gateAt C k).op=GateOp.and →
      ¬ P2.OrR 42 C (opnd C g b) (42+k))
    (hpureh : ∀ b : Fin 2, ∀ k < C.gates.length, (gateAt C k).op=GateOp.and →
      ¬ P2.OrR 42 C (opnd C h b) (42+k))
    (a : Fin 42) (hsingle : side (n := 42) C g 0 = {a})
    (hgdis : Disjoint (side (n := 42) C g 0) (side C g 1))
    (hhdis : Disjoint (side (n := 42) C h 0) (side C h 1))
    (hA : 2 ≤ (side (n := 42) C h 0).card) (hB : 2 ≤ (side (n := 42) C h 1).card)
    (htwo : (cleanCenters planeGraph (side (n := 42) C h 0) (side C h 1)).card=2)
    (hnojoint : ∀ u v : Fin 42, gateVal 42 C g (pairInput u v)=true →
      gateVal 42 C h (pairInput u v)=true → ¬ GeneralDirtyPairs.JointClean planeGraph C g h) :
    125 ≤ C.size := by
  have hE : planeGraph.edgeFinset.card = 105 := planeGraph_card
  have hne : planeGraph.edgeFinset.Nonempty := Finset.card_pos.mp (by omega)
  have hb := singleton_other_lower_bound planeGraph plane_no_four planeColor planeColor_proper
    C hL hTF hne 21 (fun K hK => planeGraph_cover_lower K (fun u v huv => hK huv))
    g h hjunk hgh hpureg hpureh a hsingle hgdis hhdis hA hB htwo hnojoint
  omega

lemma plane_minimum_junk_singleton_other_size [DecidableRel planeGraph.Adj]
    (C : Circuit) (hL : IsLeastAO planeGraph C) (hTF : TopForm planeGraph C)
    (hminjunk : ∀ D : Circuit, IsLeastAO planeGraph D → (junk planeGraph C).card ≤ (junk planeGraph D).card)
    (g h : ℕ) (hjunk : junk planeGraph C = {g,h}) (hgh : g≠h)
    (hpureg : ∀ b : Fin 2, ∀ k < C.gates.length, (gateAt C k).op=GateOp.and →
      ¬ P2.OrR 42 C (opnd C g b) (42+k))
    (hpureh : ∀ b : Fin 2, ∀ k < C.gates.length, (gateAt C k).op=GateOp.and →
      ¬ P2.OrR 42 C (opnd C h b) (42+k))
    (a : Fin 42) (hsingle : side (n := 42) C g 0 = {a})
    (hgdis : Disjoint (side (n := 42) C g 0) (side C g 1))
    (hhdis : Disjoint (side (n := 42) C h 0) (side C h 1))
    (hA : 2 ≤ (side (n := 42) C h 0).card) (hB : 2 ≤ (side (n := 42) C h 1).card)
    (hnojoint : ∀ u v : Fin 42, gateVal 42 C g (pairInput u v)=true →
      gateVal 42 C h (pairInput u v)=true → ¬ GeneralDirtyPairs.JointClean planeGraph C g h) :
    125 ≤ C.size := by
  have hhj : h ∈ junk planeGraph C := by rw [hjunk]; simp
  have hpureAll : ∀ j ∈ junk planeGraph C, ∀ b : Fin 2, ∀ k < C.gates.length,
      (gateAt C k).op=GateOp.and → ¬ P2.OrR 42 C (opnd C j b) (42+k) := by
    intro j hj
    rw [hjunk] at hj
    rcases Finset.mem_insert.mp hj with rfl | hj
    · exact hpureg
    · rw [Finset.mem_singleton.mp hj]
      exact hpureh
  have hn : ∀ j ∈ junk planeGraph C, h ≠ j → ∀ u v : Fin 42,
      gateVal 42 C h (pairInput u v)=true → gateVal 42 C j (pairInput u v)=true →
      ¬ GeneralDirtyPairs.JointClean planeGraph C h j := by
    intro j hj hne u v hhf hjf hclean
    rw [hjunk] at hj
    rcases Finset.mem_insert.mp hj with rfl | hj
    · exact hnojoint u v hjf hhf (fun x hxg hxh => hclean x hxh hxg)
    · exact hne (Finset.mem_singleton.mp hj).symm
  have heff := FirstLayerEffective.minimum_junk_two_effective_centers planeGraph C hL hTF hminjunk
    h hhj hpureAll hn hhdis
  have hdata := (P1.junk_iff planeGraph C h).mp hhj
  have htwo := ActualCleanCenters.two_clean_centers_of_effective planeGraph plane_no_four C
    (P2.ao_of 42 C hL.1) h hdata.1 hdata.2.1 hpureh hhdis hA hB heff
  exact plane_singleton_other_size C hL hTF g h hjunk hgh hpureg hpureh a hsingle
    hgdis hhdis hA hB htwo hnojoint

end PEqualNP.Outside.L_meta_1477.SingletonIntegration
