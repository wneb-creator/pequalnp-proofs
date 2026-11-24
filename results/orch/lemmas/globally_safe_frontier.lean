import PEqualNP.Outside.L_meta_3451

namespace PEqualNP.Outside.L_meta_3451

open CircuitLowerBounds MetaComplexity NestedCover

def frDirty (n : ℕ) (bad : (Fin n → Bool) → Prop) (C : Circuit) (j : ℕ) : Prop :=
  ∃ z : Fin n → Bool, bad z ∧ (C.wires (List.ofFn z)).getD (n + j) false = true

lemma frGateEval (n : ℕ) (C : Circuit) (hr : ReadsBack n C) (j : ℕ)
    (hj : j < C.gates.length) (z : Fin n → Bool) :
    (C.wires (List.ofFn z)).getD (n + j) false =
      (gateAt C j).op.eval
        ((gateAt C j).inputs.map fun i => (C.wires (List.ofFn z)).getD i false) := by
  let pre := C.gates.take j
  let post := C.gates.drop (j + 1)
  have hpre : pre.length = j := List.length_take_of_le hj.le
  have hs : C.gates = pre ++ gateAt C j :: post := by
    dsimp [pre, post, gateAt]
    rw [List.getD_eq_getElem _ _ hj]
    simp
  have hg := lcCircuitGate n C pre post (gateAt C j) hs z
  rw [hpre] at hg
  rw [hg]
  congr 1
  apply List.map_congr_left
  intro i hi
  symm
  change (C.gates.foldl decStep (List.ofFn z)).getD i false = _
  rw [hs, List.foldl_append]
  apply lcRead
  rw [lcLength, List.length_ofFn, hpre]
  exact hr j hj i hi

lemma frOrReader (n : ℕ) (bad : (Fin n → Bool) → Prop) (C : Circuit)
    (hr : ReadsBack n C) (j k : ℕ) (hk : k < C.gates.length)
    (hop : (gateAt C k).op = GateOp.or) (hread : n + j ∈ (gateAt C k).inputs)
    (hd : frDirty n bad C j) : frDirty n bad C k := by
  obtain ⟨z, hz, hw⟩ := hd
  refine ⟨z, hz, ?_⟩
  rw [frGateEval n C hr k hk z, hop]
  simp only [GateOp.eval, List.any_eq_true, List.mem_map]
  exact ⟨true, ⟨n + j, hread, hw⟩, rfl⟩

lemma frLatestReaders (n : ℕ) (bad : (Fin n → Bool) → Prop) (C : Circuit)
    (hm : Monotone2 C) (hr : ReadsBack n C) (j : ℕ)
    (hd : frDirty n bad C j)
    (hlast : ∀ k < C.gates.length, frDirty n bad C k → k ≤ j) :
    ∀ k < C.gates.length, n + j ∈ (gateAt C k).inputs →
      (gateAt C k).op = GateOp.and ∧ ¬ frDirty n bad C k := by
  intro k hk hread
  have hjk : j < k := by have h := hr k hk (n + j) hread; omega
  have hclean : ¬ frDirty n bad C k := by
    intro hd'
    have h := hlast k hk hd'
    omega
  refine ⟨?_, hclean⟩
  have hmem : gateAt C k ∈ C.gates := by
    unfold gateAt
    rw [List.getD_eq_getElem _ _ hk]
    exact List.getElem_mem hk
  have hop := (hm (gateAt C k) hmem).1
  change (gateAt C k).op = GateOp.and ∨ (gateAt C k).op = GateOp.or at hop
  rcases hop with hop | hop
  · exact hop
  · exact (hclean (frOrReader n bad C hr j k hk hop hread hd)).elim

lemma frLatestExists (n : ℕ) (bad : (Fin n → Bool) → Prop) (C : Circuit)
    (hm : Monotone2 C) (hr : ReadsBack n C)
    (hex : ∃ j < C.gates.length, frDirty n bad C j) :
    ∃ j < C.gates.length, frDirty n bad C j ∧
      (∀ k < C.gates.length, n + j ∈ (gateAt C k).inputs →
        (gateAt C k).op = GateOp.and ∧ ¬ frDirty n bad C k) := by
  classical
  let S := (Finset.range C.gates.length).filter (frDirty n bad C)
  have hS : S.Nonempty := by
    obtain ⟨j, hj, hd⟩ := hex
    exact ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hj, hd⟩⟩
  let j := S.max' hS
  have hjS : j ∈ S := Finset.max'_mem S hS
  obtain ⟨hj, hd⟩ := Finset.mem_filter.mp hjS
  have hj' := Finset.mem_range.mp hj
  refine ⟨j, hj', hd, frLatestReaders n bad C hm hr j hd ?_⟩
  intro k hk hdk
  exact Finset.le_max' S k (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hk, hdk⟩)

lemma frGloballySafeReaders (n : ℕ) (C : Circuit)
    (hm : Monotone2 C) (hr : ReadsBack n C)
    (hex : ∃ j < C.gates.length, ∃ z : Fin n → Bool,
      circuitFun n C z = false ∧ (C.wires (List.ofFn z)).getD (n + j) false = true) :
    ∃ j < C.gates.length,
      (∃ z : Fin n → Bool, circuitFun n C z = false ∧
        (C.wires (List.ofFn z)).getD (n + j) false = true) ∧
      C.output ≠ n + j ∧
      (∀ k < C.gates.length, n + j ∈ (gateAt C k).inputs →
        (gateAt C k).op = GateOp.and ∧
        ∀ z : Fin n → Bool, (C.wires (List.ofFn z)).getD (n + k) false = true →
          circuitFun n C z = true) := by
  obtain ⟨j, hj, hd, hreaders⟩ :=
    frLatestExists n (fun z => circuitFun n C z = false) C hm hr hex
  refine ⟨j, hj, hd, ?_, ?_⟩
  · intro hout
    obtain ⟨z, hz, hwire⟩ := hd
    change (C.wires (List.ofFn z)).getD C.output false = false at hz
    rw [hout, hwire] at hz
    contradiction
  · intro k hk hread
    obtain ⟨hop, hsafe⟩ := hreaders k hk hread
    refine ⟨hop, ?_⟩
    intro z hz
    cases hout : circuitFun n C z with
    | true => rfl
    | false => exact (hsafe ⟨z, hout, hz⟩).elim

end PEqualNP.Outside.L_meta_3451
