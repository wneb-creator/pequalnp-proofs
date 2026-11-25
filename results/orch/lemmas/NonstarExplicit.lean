namespace PEqualNP.Outside.L_meta_4675.NonstarExplicit

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm PEqualNP.TwoColour
open PEqualNP.Outside.L_meta_4675.Pruning
open PEqualNP.Outside.L_meta_4675.ReaderPartition
open PEqualNP.Outside.L_meta_4675.RestoreStar

def edgeValue {p l : ℕ} (E : Finset (Fin p × Fin l)) (x : Fin (p+l) → Bool) : Bool :=
  decide (∃ a b, (a,b) ∈ E ∧ x (Fin.castAdd l a) = true ∧ x (Fin.natAdd p b) = true)

lemma bool_eq_of_true_iff (a b : Bool) (h : a = true ↔ b = true) : a = b := by
  cases a <;> cases b <;> simp_all

lemma edgeValue_singleton {p l : ℕ} (E : Finset (Fin p × Fin l)) (i : Fin (p+l)) :
    edgeValue E (fun k => decide (k=i)) = false := by
  apply Bool.eq_false_iff.mpr
  intro h
  simp only [edgeValue, decide_eq_true_eq] at h
  obtain ⟨a,b,_,ha,hb⟩ := h
  have he := congrArg Fin.val (ha.trans hb.symm)
  have hlt := a.isLt
  simp only [Fin.val_castAdd, Fin.val_natAdd] at he
  omega

lemma semLE_ofFn {n : ℕ} (x y : Fin n → Bool)
    (h : ∀ i, x i = true → y i = true) : SemLE (List.ofFn x) (List.ofFn y) := by
  refine ⟨by simp, ?_⟩
  intro i hi
  by_cases hin : i < n
  · have hx : (List.ofFn x).getD i false = x ⟨i,hin⟩ := by
      simp [List.getD_eq_getElem?_getD, hin]
    have hy : (List.ofFn y).getD i false = y ⟨i,hin⟩ := by
      simp [List.getD_eq_getElem?_getD, hin]
    rw [hx] at hi
    rw [hy]
    exact h _ hi
  · simp [List.getD_eq_getElem?_getD, hin] at hi

lemma nonstar_prune_restore (p l q r aWire : ℕ) (C : Circuit)
    (E : Finset (Fin p × Fin l)) (A Q : Finset (Fin p)) (B P : Finset (Fin l))
    (hC4 : ∀ (a a' : Fin p) (b b' : Fin l), a ≠ a' → b ≠ b' →
      ¬ ((a,b) ∈ E ∧ (a,b') ∈ E ∧ (a',b) ∈ E ∧ (a',b') ∈ E))
    (hAO : IsAO2 (p+l) C) (colour : ℕ → Bool) (hz : tCount (p+l) C colour = 0)
    (hcompute : ∀ x, circuitFun (p+l) C x = edgeValue E x)
    (hqr : q < r) (hr : r < C.gates.length) (hread : p+l+q ∈ C.gates[r].inputs)
    (haWire : aWire < p+l+q)
    (hfactor : ∀ x : Fin (p+l) → Bool,
      (C.wires (List.ofFn x)).getD aWire false =
        decide (∃ a ∈ A, x (Fin.castAdd l a) = true))
    (hrectangle : ∀ x : Fin (p+l) → Bool,
      (C.wires (List.ofFn x)).getD (p+l+q) false = true ↔
        (∃ a ∈ A, x (Fin.castAdd l a) = true) ∧ (∃ b ∈ B, x (Fin.natAdd p b) = true))
    (hQ : 1 < Q.card) (hB : 1 < B.card) (hAQ : (A∩Q).Nonempty) (hP : P.Nonempty)
    (hbase : ∀ a ∈ Q, ∀ b ∈ P, (a,b) ∈ E)
    (hprod : ∀ a ∈ A, ∀ b ∈ B, ∀ a' ∈ Q, (a,b) ∈ E ∨ (a',b) ∈ E)
    (hdirty : ∃ a ∈ A, ∃ b ∈ B, (a,b) ∉ E)
    (hbasePreserved : ∀ a ∈ Q, ∀ b ∈ P,
      (forcedValues (p+l) q C (List.ofFn (splitInput (pairVal a b)))).getD C.output false = true) :
    ∃ b1 : Fin l, (∀ a ∈ A, (a,b1) ∈ E) ∧
      let D := PEqualNP.Outside.L_meta_4675.StarAppendOptional.restoreStar (p+l)
        (pruned (p+l) q C) aWire (Fin.natAdd p b1).val
      IsAO2 (p+l) D ∧ tCount (p+l) D colour = 0 ∧ D.size ≤ C.size ∧
        circuitFun (p+l) D = circuitFun (p+l) C := by
  let F0 : (Fin p ⊕ Fin l → Bool) → Bool := fun y =>
    (forcedValues (p+l) q C (List.ofFn (splitInput y))).getD C.output false
  have hmono : ∀ x y, (∀ v, x v = true → y v = true) → F0 x = true → F0 y = true := by
    intro x y hxy hx
    exact (forcedValues_mono (p+l) q C hAO _ _
      (semLE_ofFn (splitInput x) (splitInput y) (fun i => hxy _))).2 C.output hx
  have hbelow : ∀ y, F0 y = true → graphValue E y := by
    intro y hy
    have hc := forcedValues_below (p+l) q C hAO (List.ofFn (splitInput y)) C.output hy
    change circuitFun (p+l) C (splitInput y) = true at hc
    rw [hcompute] at hc
    simpa [edgeValue, graphValue, splitInput] using hc
  have houtside : ∀ a b, (a,b) ∈ E → (a ∉ A ∨ b ∉ B) → F0 (pairVal a b) = true := by
    intro a b hab hoff
    have hg : (C.wires (List.ofFn (splitInput (pairVal a b)))).getD (p+l+q) false = false := by
      apply Bool.eq_false_iff.mpr
      intro ht
      have hh := (hrectangle (splitInput (pairVal a b))).mp ht
      have hmem : a ∈ A ∧ b ∈ B := by simpa [splitInput, pairVal] using hh
      rcases hoff with ha | hb
      · exact ha hmem.1
      · exact hb hmem.2
    change (forcedValues (p+l) q C (List.ofFn (splitInput (pairVal a b)))).getD C.output false = true
    rw [forcedValues_agrees (p+l) q C _ hg]
    change circuitFun (p+l) C (splitInput (pairVal a b)) = true
    rw [hcompute]
    simp [edgeValue, splitInput, pairVal, hab]
  obtain ⟨b1,hcol,hrepair⟩ :=
    PEqualNP.Outside.L_meta_4675.NonstarRepair.nonstar_rectangle_repair E hC4 A Q B P
      hQ hB hAQ hP hbase hprod hdirty F0 hmono hbelow houtside hbasePreserved
  refine ⟨b1,hcol,?_⟩
  apply PEqualNP.Outside.L_meta_4675.PruneRestoreExplicit.restore_explicit
    (p+l) q r aWire (Fin.natAdd p b1).val C (circuitFun (p+l) C) colour hAO hz hqr hr hread
    haWire (by have := (Fin.natAdd p b1).isLt; omega)
  · intro i
    rw [hcompute]
    exact edgeValue_singleton E i
  · intro x
    let y : Fin p ⊕ Fin l → Bool := fun v => x (finSumFinEquiv v)
    have hy : splitInput y = x := by funext i; simp [splitInput, y]
    apply bool_eq_of_true_iff
    rw [hcompute]
    have hE : edgeValue E x = true ↔ graphValue E y := by simp [edgeValue, graphValue, y]
    rw [hE, hrepair y, Bool.or_eq_true, Bool.and_eq_true, hfactor]
    have hbval : (C.wires (List.ofFn x)).getD (Fin.natAdd p b1).val false = x (Fin.natAdd p b1) :=
      PEqualNP.Outside.L_meta_4675.MaskingNext.wireValue_input (p+l) C x _ (Fin.natAdd p b1).isLt
    rw [hbval]
    simp only [decide_eq_true_eq]
    simp [F0, hy, y]

end PEqualNP.Outside.L_meta_4675.NonstarExplicit
