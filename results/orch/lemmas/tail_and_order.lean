import PEqualNP.Outside.L_meta_3451

namespace PEqualNP.Outside.L_meta_3451

open CircuitLowerBounds MetaComplexity NestedCover

lemma frAndAfterLatest (n : ℕ) (C : Circuit)
    (hm : Monotone2 C) (hr : ReadsBack n C)
    (hmin : ∀ D : Circuit, Monotone2 D → ReadsBack n D →
      circuitFun n D = circuitFun n C → C.size ≤ D.size)
    (j : ℕ) (hd : frDirty n (fun z => circuitFun n C z = false) C j)
    (hlast : ∀ k < C.gates.length,
      frDirty n (fun z => circuitFun n C z = false) C k → k ≤ j)
    (k : ℕ) (hjk : j < k) (hk : k < C.gates.length)
    (hop : (gateAt C k).op = GateOp.and) :
    ∃ a b : ℕ, (gateAt C k).inputs = [a, b] ∧ a ≠ b ∧
      a ≤ n + j ∧ b ≤ n + j := by
  have hclean : ¬ frDirty n (fun z => circuitFun n C z = false) C k := by
    intro hd'
    have h := hlast k hk hd'
    omega
  have hbefore (w : ℕ) (hw : w ∈ (gateAt C k).inputs) : w ≤ n + j := by
    by_contra hn
    have hwn : n ≤ w := by omega
    have hwr := hr k hk w hw
    obtain ⟨z, hz, hf⟩ := saMinimumAndOperandUnsafe n C hm hr hmin k hk hop w hw
    have hwd : frDirty n (fun z => circuitFun n C z = false) C (w - n) := by
      refine ⟨z, hf, ?_⟩
      simpa only [Nat.add_sub_of_le hwn] using hz
    have hx := hlast (w - n) (by omega) hwd
    omega
  have hkmem : gateAt C k ∈ C.gates := by
    rw [gateAt, List.getD_eq_getElem _ _ hk]
    exact List.getElem_mem hk
  have hlen := (hm (gateAt C k) hkmem).2
  cases hin : (gateAt C k).inputs with
  | nil =>
    obtain ⟨z, hz, _⟩ := hd
    exact (hclean ⟨z, hz, by rw [frGateEval n C hr k hk z, hop, hin]; rfl⟩).elim
  | cons a rest =>
    have ha : a ∈ (gateAt C k).inputs := by simp [hin]
    cases rest with
    | nil =>
      obtain ⟨z, hz, hf⟩ := saMinimumAndOperandUnsafe n C hm hr hmin k hk hop a ha
      exact (hclean ⟨z, hf, by
        rw [frGateEval n C hr k hk z, hop, hin]
        simpa [GateOp.eval] using hz⟩).elim
    | cons b tail =>
      have ht : tail = [] := by simpa [hin] using hlen
      subst tail
      have hb : b ∈ (gateAt C k).inputs := by simp [hin]
      refine ⟨a, b, rfl, ?_, hbefore a ha, hbefore b hb⟩
      intro hab
      subst b
      obtain ⟨z, hz, hf⟩ := saMinimumAndOperandUnsafe n C hm hr hmin k hk hop a ha
      apply hclean
      refine ⟨z, hf, ?_⟩
      rw [frGateEval n C hr k hk z, hop, hin]
      simpa [GateOp.eval] using hz

end PEqualNP.Outside.L_meta_3451
