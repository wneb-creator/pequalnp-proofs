namespace PEqualNP.Outside.L_meta_2962.Structural
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.TopForm PEqualNP.Core PEqualNP.ReadTwo
open PEqualNP.Outside.L_meta_2962.Semantic
variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}

lemma essential_gate_input_occurrence (ao : IsAO2 n C) (v : Fin n)
    (x y : Fin n → Bool) (heq : ∀ t, t ≠ v → x t = y t)
    (j : ℕ) (hj : j < C.gates.length)
    (hdiff : gateVal n C j x ≠ gateVal n C j y) :
    ∃ i ∈ coneSet n C j, ∃ b : Fin 2, opnd C i b = v.val := by
  classical
  induction j using Nat.strong_induction_on with
  | ind j ih =>
    have hex : ∃ w ∈ (gateAt C j).inputs, wval C x w ≠ wval C y w := by
      by_contra hn
      apply hdiff
      change wval C x (n+j) = wval C y (n+j)
      rw [wire_gate C ao x j hj, wire_gate C ao y j hj]
      congr 1
      apply List.map_congr_left
      intro w hw
      by_contra hd
      exact hn ⟨w,hw,hd⟩
    obtain ⟨w,hw,hd⟩ := hex
    have hback := ao.2.1 j hj w hw
    by_cases hinput : w < n
    · let t : Fin n := ⟨w,hinput⟩
      have tv : t = v := by
        by_contra htv
        apply hd
        change wval C x t.val = wval C y t.val
        rw [wire_input, wire_input]
        exact heq t htv
      obtain ⟨b,hb,hbval⟩ := List.getElem_of_mem hw
      have hbl : b < 2 := by rw [ao.2.2 _ (by rw [gateAt_eq_getElem C j hj]; exact List.getElem_mem hj)] at hb; exact hb
      refine ⟨j, by simp [coneSet], ⟨b,hbl⟩, ?_⟩
      have hv : w = v.val := congrArg Fin.val tv
      simpa [opnd, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hb, hv] using hbval
    · have hn : n ≤ w := by omega
      have hk : w-n < j := by omega
      have hkl : w-n < C.gates.length := by omega
      have he : n + (w-n) = w := by omega
      have hd' : gateVal n C (w-n) x ≠ gateVal n C (w-n) y := by
        change wval C x (n+(w-n)) ≠ wval C y (n+(w-n))
        simpa only [he] using hd
      obtain ⟨i,hi,b,hb⟩ := ih (w-n) hk hkl hd'
      have hcone : InCone n C (w-n) j :=
        (InCone_iff n C (w-n) j hj).mpr ⟨w,hw,hn,hback,Or.inl rfl⟩
      exact ⟨i,coneSet_mono hkl hj (Or.inr hcone) hi,b,hb⟩

lemma accepted_edge_endpoint_port (ao : IsAO2 n C) {j : ℕ}
    (hj : j ∈ maximalCores G C) (u v : Fin n)
    (hv : gateVal n C j (pairInput u v) = true) :
    ∃ i ∈ (maximalCores G C).biUnion (coneSet n C), ∃ b : Fin 2,
      opnd C i b = u.val := by
  have hc := (mem_maximal.mp hj).1
  have hs : gateVal n C j (fun t => decide (t=v)) = false := by
    cases he : gateVal n C j (fun t => decide (t=v)) with
    | false => rfl
    | true => have hf := hc.2.1.1 _ he; rw [graph_unit_false] at hf; contradiction
  have hd : gateVal n C j (pairInput u v) ≠ gateVal n C j (fun t => decide (t=v)) := by
    rw [hv,hs]; decide
  obtain ⟨i,hi,b,hb⟩ := essential_gate_input_occurrence ao u (pairInput u v)
    (fun t => decide (t=v)) (by intro t ht; simp [pairInput,ht]) j hc.1 hd
  exact ⟨i,Finset.mem_biUnion.mpr ⟨j,hj,hi⟩,b,hb⟩

end PEqualNP.Outside.L_meta_2962.Structural
