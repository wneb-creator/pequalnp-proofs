import Existence

namespace PEqualNP.Outside.L_meta_2448_aux.StarExistence

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership
open PEqualNP.Outside.L_meta_2448_aux.Existence

lemma and_reads_input (n : ℕ) (C : Circuit) (j : ℕ) (u : Fin n)
    (hj : j < C.gates.length) (hop : (gateAt C j).op = GateOp.and)
    (hu : u.val ∈ (gateAt C j).inputs) (x : Fin n → Bool)
    (hx : gateVal n C j x = true) : x u = true := by
  let pre := C.gates.take j
  let post := C.gates.drop (j + 1)
  let g := C.gates[j]'hj
  have hpre : pre.length = j := by
    simp [pre, Nat.min_eq_left (Nat.le_of_lt hj)]
  have hga : gateAt C j = g := by
    simp [gateAt, g, List.getD_eq_getElem?_getD, hj]
  have hgs : C.gates = (pre ++ [g]) ++ post := by
    dsimp [pre, post, g]
    rw [List.append_assoc]
    change C.gates = C.gates.take j ++ C.gates[j] :: C.gates.drop (j + 1)
    rw [List.cons_getElem_drop_succ, List.take_append_drop]
  let W := wf pre (List.ofFn x)
  have hW : W.length = n + j := by
    dsimp [W]
    rw [wf_len, List.length_ofFn, hpre]
  have hval : gateVal n C j x =
      g.op.eval (g.inputs.map fun i => W.getD i false) := by
    change (wf C.gates (List.ofFn x)).getD (n + j) false = _
    rw [hgs, wf_prefix (pre ++ [g]) post (List.ofFn x) (n + j)
      (by simp [hpre]), wf_snoc]
    change (W ++ [g.op.eval (g.inputs.map fun i => W.getD i false)]).getD
      (n + j) false = _
    rw [← hW, getD_snoc_eq]
  rw [hga] at hop hu
  rw [hval, hop] at hx
  change (g.inputs.map fun i => W.getD i false).all id = true at hx
  have hraw := List.all_eq_true.mp hx _ (List.mem_map.mpr ⟨u.val, hu, rfl⟩)
  have hinput : W.getD u.val false = x u := by
    dsimp [W]
    rw [wf_keep _ _ _ (by simp)]
    simp
  rw [hinput] at hraw
  exact hraw

lemma raw_ands_star (n : ℕ) (G : SimpleGraph (Fin n)) (C : Circuit)
    (hraw : ∀ g ∈ C.gates, g.op = GateOp.and →
      ∃ u : Fin n, u.val ∈ g.inputs) : HasStarProfile n G C := by
  intro j hj hop
  have hmem : gateAt C j ∈ C.gates := by
    have he : gateAt C j = C.gates[j]'hj := by
      simp [gateAt, List.getD_eq_getElem?_getD, hj]
    rw [he]
    exact List.getElem_mem hj
  obtain ⟨u, hu⟩ := hraw (gateAt C j) hmem hop
  right
  refine ⟨u, ?_⟩
  intro a b _hab hown
  have h := and_reads_input n C j u hj hop hu (pairInput a b) hown.2.2.1
  have he : u = a ∨ u = b := of_decide_eq_true h
  exact he.imp Eq.symm Eq.symm

lemma build_and_raw (n : ℕ) : ∀ E : List (Fin n × Fin n),
    ∀ g ∈ build n E, g.op = GateOp.and → ∃ u : Fin n, u.val ∈ g.inputs := by
  intro E
  induction E with
  | nil =>
    intro g hg hop
    simp only [build, List.mem_cons, List.not_mem_nil, or_false] at hg
    subst g
    cases hop
  | cons e es ih =>
    intro g hg hop
    simp only [build, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with hg | rfl | rfl
    · exact ih g hg hop
    · exact ⟨e.1, by simp⟩
    · cases hop

lemma build_profile (n : ℕ) (G : SimpleGraph (Fin n)) (E : List (Fin n × Fin n)) :
    HasStarProfile n G ⟨build n E, n + 2 * E.length⟩ := by
  apply raw_ands_star
  exact build_and_raw n E

lemma graph_star_exists (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    ∃ C : Circuit, Monotone2 C ∧ circuitFun n C = graphFun G ∅ ∧ HasStarProfile n G C := by
  classical
  let E : List (Fin n × Fin n) :=
    ((List.finRange n).product (List.finRange n)).filter (fun e => decide (G.Adj e.1 e.2))
  refine ⟨⟨build n E, n + 2 * E.length⟩, build_mono n E, ?_, build_profile n G E⟩
  funext x
  show (wf (build n E) (List.ofFn x)).getD (n + 2 * E.length) false = _
  rw [build_val, Bool.eq_iff_iff]
  simp only [graphFun, List.any_eq_true, Bool.and_eq_true,
    Bool.or_eq_true, decide_eq_true_eq, Finset.notMem_empty, false_and, exists_false, false_or]
  constructor
  · rintro ⟨e, he, h1, h2⟩
    have := (List.mem_filter.mp he).2
    exact ⟨e.1, e.2, by simpa using this, h1, h2⟩
  · rintro ⟨u, v, huv, h1, h2⟩
    exact ⟨(u, v), List.mem_filter.mpr ⟨by simp [List.pair_mem_product], by simpa using huv⟩, h1, h2⟩

lemma star_minimal_exists (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    ∃ C : Circuit, Monotone2 C ∧ circuitFun n C = graphFun G ∅ ∧ HasStarProfile n G C ∧
      ∀ D : Circuit, Monotone2 D → circuitFun n D = graphFun G ∅ →
        HasStarProfile n G D → C.size ≤ D.size := by
  classical
  obtain ⟨C, hC, hCf, hCs⟩ := graph_star_exists n G
  have hex : ∃ s : ℕ, ∃ D : Circuit, Monotone2 D ∧ circuitFun n D = graphFun G ∅ ∧
      HasStarProfile n G D ∧ D.size = s := ⟨C.size, C, hC, hCf, hCs, rfl⟩
  obtain ⟨D, hD, hDf, hDs, hs⟩ := Nat.find_spec hex
  refine ⟨D, hD, hDf, hDs, ?_⟩
  intro E hE hEf hEs
  rw [hs]
  exact Nat.find_min' hex ⟨E, hE, hEf, hEs, rfl⟩

end PEqualNP.Outside.L_meta_2448_aux.StarExistence
