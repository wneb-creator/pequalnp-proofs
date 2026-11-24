import PEqualNP.Outside.L_meta_3451

namespace PEqualNP.Outside.L_meta_3451

open CircuitLowerBounds MetaComplexity NestedCover

lemma saStrictSafeOperand (n : ℕ) (C : Circuit) (pre post : List Gate) (g : Gate)
    (hsplit : C.gates = pre ++ g :: post)
    (hmono : Monotone2 C) (hreads : ReadsBack n C)
    (hop : g.op = GateOp.and) (w : ℕ) (hmem : w ∈ g.inputs)
    (hsafe : ∀ z : Fin n → Bool,
      (C.wires (List.ofFn z)).getD w false = true → circuitFun n C z = true) :
    ∃ D : Circuit, Monotone2 D ∧ ReadsBack n D ∧ D.size + 1 = C.size ∧
      circuitFun n D = circuitFun n C := by
  let E : Circuit := ⟨pre ++ ⟨GateOp.or, [w]⟩ :: post, C.output⟩
  obtain ⟨hm, hr, hs, _, hf⟩ :=
    saSafeOperand n C pre post g hsplit hmono hreads hop w hmem hsafe
  have hj : pre.length < E.gates.length := by simp [E]
  have hins : (gateAt E pre.length).inputs = [w] := by simp [gateAt, E]
  obtain ⟨hdm, hdr, hds, hdf⟩ := edUnary_delete E pre.length w hm hr hj hins
  exact ⟨_, hdm, hdr, hds.trans hs, hdf.trans (funext hf)⟩

lemma saMinimumAndOperandUnsafe (n : ℕ) (C : Circuit)
    (hm : Monotone2 C) (hr : ReadsBack n C)
    (hmin : ∀ D : Circuit, Monotone2 D → ReadsBack n D →
      circuitFun n D = circuitFun n C → C.size ≤ D.size)
    (j : ℕ) (hj : j < C.gates.length) (hop : (gateAt C j).op = GateOp.and)
    (w : ℕ) (hmem : w ∈ (gateAt C j).inputs) :
    ∃ z : Fin n → Bool, (C.wires (List.ofFn z)).getD w false = true ∧
      circuitFun n C z = false := by
  by_contra hnone
  have hsafe : ∀ z : Fin n → Bool,
      (C.wires (List.ofFn z)).getD w false = true → circuitFun n C z = true := by
    intro z hz
    cases hf : circuitFun n C z with
    | true => rfl
    | false => exact (hnone ⟨z, hz, hf⟩).elim
  let pre := C.gates.take j
  let post := C.gates.drop (j + 1)
  have hs : C.gates = pre ++ gateAt C j :: post := by
    dsimp [pre, post, gateAt]
    rw [List.getD_eq_getElem _ _ hj]
    simp
  obtain ⟨D, hdm, hdr, hds, hdf⟩ :=
    saStrictSafeOperand n C pre post (gateAt C j) hs hm hr hop w hmem hsafe
  have hle := hmin D hdm hdr hdf
  omega

lemma saMinimumSafeReaders (n : ℕ) (C : Circuit)
    (hm : Monotone2 C) (hr : ReadsBack n C)
    (hmin : ∀ D : Circuit, Monotone2 D → ReadsBack n D →
      circuitFun n D = circuitFun n C → C.size ≤ D.size)
    (w : ℕ) (hsafe : ∀ z : Fin n → Bool,
      (C.wires (List.ofFn z)).getD w false = true → circuitFun n C z = true) :
    ∀ j < C.gates.length, w ∈ (gateAt C j).inputs →
      (gateAt C j).op = GateOp.or := by
  intro j hj hmem
  have hjmem : gateAt C j ∈ C.gates := by
    rw [gateAt, List.getD_eq_getElem _ _ hj]
    exact List.getElem_mem hj
  have hop := (hm (gateAt C j) hjmem).1
  change (gateAt C j).op = GateOp.and ∨ (gateAt C j).op = GateOp.or at hop
  rcases hop with hop | hop
  · obtain ⟨z, hz, hf⟩ := saMinimumAndOperandUnsafe n C hm hr hmin j hj hop w hmem
    have ht := hsafe z hz
    rw [hf] at ht
    contradiction
  · exact hop

lemma frMinimumLatestReaders (n : ℕ) (C : Circuit)
    (hm : Monotone2 C) (hr : ReadsBack n C)
    (hmin : ∀ D : Circuit, Monotone2 D → ReadsBack n D →
      circuitFun n D = circuitFun n C → C.size ≤ D.size)
    (j : ℕ) (hd : frDirty n (fun z => circuitFun n C z = false) C j)
    (hlast : ∀ k < C.gates.length,
      frDirty n (fun z => circuitFun n C z = false) C k → k ≤ j) :
    ∀ k < C.gates.length, n + j ∈ (gateAt C k).inputs →
      ∃ w < n + j, (gateAt C k).op = GateOp.and ∧
        ((gateAt C k).inputs = [n + j, w] ∨ (gateAt C k).inputs = [w, n + j]) := by
  intro k hk hread
  obtain ⟨hop, hclean⟩ := frLatestReaders n (fun z => circuitFun n C z = false)
    C hm hr j hd hlast k hk hread
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
  have hother : ∃ w ∈ (gateAt C k).inputs, w ≠ n + j := by
    by_contra hn
    have hall : ∀ w ∈ (gateAt C k).inputs, w = n + j := by
      intro w hw
      by_contra hne
      exact hn ⟨w, hw, hne⟩
    obtain ⟨z, hz, hwire⟩ := hd
    apply hclean
    refine ⟨z, hz, ?_⟩
    rw [frGateEval n C hr k hk z, hop]
    simp only [GateOp.eval, List.all_map, List.all_eq_true]
    intro w hw
    rw [hall w hw]
    exact hwire
  have hkmem : gateAt C k ∈ C.gates := by
    rw [gateAt, List.getD_eq_getElem _ _ hk]
    exact List.getElem_mem hk
  have hlen := (hm (gateAt C k) hkmem).2
  obtain ⟨w, hw, hne⟩ := hother
  have hwlt : w < n + j := lt_of_le_of_ne (hbefore w hw) hne
  refine ⟨w, hwlt, hop, ?_⟩
  cases hin : (gateAt C k).inputs with
  | nil => simp [hin] at hread
  | cons a rest =>
    cases rest with
    | nil =>
      have ha : n + j = a := by simpa [hin] using hread
      have hw' : w = a := by simpa [hin] using hw
      exact (hne (hw'.trans ha.symm)).elim
    | cons b tail =>
      have ht : tail = [] := by simpa [hin] using hlen
      subst tail
      simp only [hin, List.mem_cons, List.not_mem_nil, or_false] at hread hw
      rcases hread with ha | hb
      · subst a
        rcases hw with hw | hw
        · exact (hne hw).elim
        · subst b; exact Or.inl rfl
      · subst b
        rcases hw with hw | hw
        · subst a; exact Or.inr rfl
        · exact (hne hw).elim

end PEqualNP.Outside.L_meta_3451
