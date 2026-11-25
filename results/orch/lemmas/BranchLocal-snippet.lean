theorem least_fifteen_internal_branch_reads_nonbranch (gs : List Gate) (out : Nat)
    (least : Least 10 petersenF gs out) (budget : nonNotCount gs ≤ 15)
    (v : Fin (10 + gs.length)) (internal : 10 ≤ v.val)
    (vBranch : v ∈ circuitBranchWires gs) :
    ∃ u : Fin (10 + gs.length), readEdge gs u v ∧ u ∉ circuitBranchWires gs := by
  classical
  have valid := least_petersen_output_valid least
  let outWire : Fin (10 + gs.length) := ⟨out, valid⟩
  have live := least_read_edge_live least petersen_nonconstant petersen_depends
    petersen_restrict_nonconstant valid
  obtain ⟨i, first⟩ := least_fifteen_binary_branch_covered gs out least budget valid live v vBranch
  have path := FirstBranchRoute.first_path (readEdge gs) outWire (read_order least.hcl) live (inputWire gs i)
  change FirstBranchRoute.first (readEdge gs) outWire (read_order least.hcl) live (inputWire gs i) = v at first
  rw [first] at path
  rcases path.cases_tail with same | ⟨u, _, last⟩
  · have values := congrArg Fin.val same
    change v.val = i.val at values
    have bound := i.isLt
    omega
  · exact ⟨u, last.1, fun member => last.2 (Or.inr (in_circuit_branches.mp member))⟩

theorem least_fifteen_no_adjacent_unary_branches (gs : List Gate) (out : Nat)
    (least : Least 10 petersenF gs out) (budget : nonNotCount gs ≤ 15)
    (u v : Fin (10 + gs.length)) (j : Nat) (op : GateOp)
    (atGate : gs[j]? = some ⟨op, [u.val]⟩) (atWire : v.val = 10 + j) :
    ¬ (u ∈ circuitBranchWires gs ∧ v ∈ circuitBranchWires gs) := by
  classical
  rintro ⟨uBranch, vBranch⟩
  obtain ⟨r, edge, nonbranch⟩ := least_fifteen_internal_branch_reads_nonbranch gs out least budget v
    (by omega) vBranch
  obtain ⟨k, g, readAt, value, mem⟩ := edge
  have index : k = j := by omega
  subst k
  have gateEq : g = ⟨op, [u.val]⟩ := Option.some.inj (readAt.symm.trans atGate)
  rw [gateEq] at mem
  have same : r = u := Fin.ext (by simpa only [List.mem_singleton] using mem)
  exact nonbranch (same.symm ▸ uBranch)
