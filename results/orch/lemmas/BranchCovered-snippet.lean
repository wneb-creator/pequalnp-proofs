theorem petersen_label_cover_count (gs : List Gate) (out : Nat)
    (least : Least 10 petersenF gs out) (valid : out < 10 + gs.length)
    (live : ∀ v : Fin (10 + gs.length), v ≠ (⟨out, valid⟩ : Fin (10 + gs.length)) →
      ∃ w, readEdge gs v w)
    (B : Finset (Fin (10 + gs.length))) (sub : B ⊆ circuitBranchWires gs)
    (cover : ∀ v : Fin 10,
      firstInputBoundary least.hcl ⟨out, valid⟩ live v = ⟨out, valid⟩ ∨
      firstInputBoundary least.hcl ⟨out, valid⟩ live v ∈ B) : 6 ≤ B.card := by
  classical
  letI : DecidableRel petersenGraph.Adj := petersenAdjDecidable
  let outWire : Fin (10 + gs.length) := ⟨out, valid⟩
  let label : Fin 10 → Fin (10 + gs.length) := firstInputBoundary least.hcl outWire live
  have computes (x : Fin 10 → Bool) : vl gs x outWire.val = PetersenScratch.edgeValue petersenGraph x := by
    change vl gs x out = _
    rw [least.hev, Bool.eq_iff_iff, petersenF_graph_edges]
    simp only [PetersenScratch.edgeValue, decide_eq_true_eq]
  have marked (S : Finset (Fin 10)) : vl gs (setInput S) outWire.val = true ↔
      BranchGraph.containsEdge petersenGraph S := by
    change vl gs (setInput S) out = true ↔ _
    rw [least.hev]
    exact petersen_graph_marked_edges S
  have independent (r) : BranchGraph.Independent petersenGraph (BranchGroupsLean.bucket label r) :=
    firstInputGroup_independent least.hcl outWire live (predecessors_nodup least petersen_nonconstant)
      petersenGraph computes petersen_graph_alternate_neighbors r
  have before (r) (member : r ∈ B) : r < outWire := by
    obtain ⟨a, _, path, _, _⟩ := in_circuit_branches.mp (sub member)
    exact lt_of_lt_of_le (read_order least.hcl path) (wire_le_output least.hcl outWire live a)
  have twins (r) (member : r ∈ B) : BranchGraph.TwinGroup petersenGraph
      (BranchGroupsLean.below label r) (BranchGroupsLean.bucket label r) :=
    circuit_branch_class_twins least.hcl outWire live petersenGraph marked r
      (le_of_lt (before r member)) (Or.inr (in_circuit_branches.mp (sub member))) (independent r)
  exact BranchGroupsLean.roots_required petersenGraph label outWire B 6 cover before twins
    (independent outWire) (PetersenMaskBridge.petersen_ten_groups_need_six petersenGraph petersen_graph_matches_mask)

theorem least_fifteen_binary_branch_covered (gs : List Gate) (out : Nat)
    (least : Least 10 petersenF gs out) (budget : nonNotCount gs ≤ 15)
    (valid : out < 10 + gs.length)
    (live : ∀ v : Fin (10 + gs.length), v ≠ (⟨out, valid⟩ : Fin (10 + gs.length)) →
      ∃ w, readEdge gs v w) :
    ∀ w ∈ circuitBranchWires gs,
      ∃ v : Fin 10, firstInputBoundary least.hcl ⟨out, valid⟩ live v = w := by
  classical
  let branches := circuitBranchWires (n := 10) gs
  have branchBudget := branching_budget least.hcl valid (fun w hw hne => by
      let wire : Fin (10 + gs.length) := ⟨w, hw⟩
      obtain ⟨v, p, g, hg, _, hw'⟩ := live wire (fun h => hne (congrArg Fin.val h))
      exact ⟨p, g, hg, hw'⟩)
    (branches.image Fin.val) (fun w hw => by
      obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hw
      exact branch_slots_of_read_edges (in_circuit_branches.mp hv))
  rw [Finset.card_image_of_injective _ Fin.val_injective] at branchBudget
  have countTotal := nonNotCount_add_notCount gs
  change nonNotCount gs + notGateCount gs = gs.length at countTotal
  have bound : branches.card ≤ 6 := by omega
  intro w member
  by_contra absent
  have cover : ∀ v : Fin 10,
      firstInputBoundary least.hcl ⟨out, valid⟩ live v = ⟨out, valid⟩ ∨
      firstInputBoundary least.hcl ⟨out, valid⟩ live v ∈ branches.erase w := by
    intro v
    have stopped := FirstBranchRoute.first_stops (readEdge gs) ⟨out, valid⟩ (read_order least.hcl) live (inputWire gs v)
    rcases stopped with outLabel | fork
    · exact Or.inl outLabel
    · apply Or.inr
      apply Finset.mem_erase.mpr
      exact ⟨fun eq => absent ⟨v, eq⟩, in_circuit_branches.mpr fork⟩
  have lower := petersen_label_cover_count gs out least valid live (branches.erase w)
    (fun v hv => (Finset.mem_erase.mp hv).2) cover
  have erased : (branches.erase w).card = branches.card - 1 := Finset.card_erase_of_mem member
  omega
