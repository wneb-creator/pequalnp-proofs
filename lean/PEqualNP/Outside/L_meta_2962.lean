import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2962_aux

lemma cover_extension {n : ℕ} (G : SimpleGraph (Fin n))
    (D : Finset (Sym2 (Fin n))) (S T' : Finset (Fin n))
    (coverD : ∀ u v : Fin n, G.Adj u v → s(u, v) ∈ D → u ∈ S ∨ v ∈ S)
    (coverRest : (G.deleteEdges (D : Set (Sym2 (Fin n)))).IsVertexCover
      (T' : Set (Fin n))) :
    G.IsVertexCover ((S ∪ T' : Finset (Fin n)) : Set (Fin n)) := by
  intro u v edge
  by_cases deleted : s(u, v) ∈ D
  · rcases coverD u v edge deleted with h | h
    · exact Or.inl (Finset.mem_union.mpr (Or.inl h))
    · exact Or.inr (Finset.mem_union.mpr (Or.inl h))
  · have rest : (G.deleteEdges (D : Set (Sym2 (Fin n)))).Adj u v :=
      SimpleGraph.deleteEdges_adj.mpr ⟨edge, deleted⟩
    rcases coverRest rest with h | h
    · exact Or.inl (Finset.mem_union.mpr (Or.inr h))
    · exact Or.inr (Finset.mem_union.mpr (Or.inr h))

lemma minimum_cover_delete_bound {n : ℕ} (G : SimpleGraph (Fin n))
    (D : Finset (Sym2 (Fin n))) (S T T' : Finset (Fin n))
    (minimal : ∀ V : Finset (Fin n), G.IsVertexCover (V : Set (Fin n)) → T.card ≤ V.card)
    (coverD : ∀ u v : Fin n, G.Adj u v → s(u, v) ∈ D → u ∈ S ∨ v ∈ S)
    (coverRest : (G.deleteEdges (D : Set (Sym2 (Fin n)))).IsVertexCover
      (T' : Set (Fin n))) :
    T.card ≤ S.card + T'.card := by
  exact (minimal (S ∪ T') (cover_extension G D S T' coverD coverRest)).trans
    (Finset.card_union_le S T')

lemma core_cover_of_certificate {n : ℕ} (G : SimpleGraph (Fin n))
    (D : Finset (Sym2 (Fin n))) (U : Finset ℕ) (mc : ℕ)
    (S T T' : Finset (Fin n))
    (minimal : ∀ V : Finset (Fin n), G.IsVertexCover (V : Set (Fin n)) → T.card ≤ V.card)
    (coverD : ∀ u v : Fin n, G.Adj u v → s(u, v) ∈ D → u ∈ S ∨ v ∈ S)
    (coverRest : (G.deleteEdges (D : Set (Sym2 (Fin n)))).IsVertexCover
      (T' : Set (Fin n)))
    (cost : D.card + S.card ≤ U.card + mc) :
    D.card + T.card ≤ U.card + mc + T'.card := by
  calc
    D.card + T.card ≤ D.card + (S.card + T'.card) :=
      Nat.add_le_add_left (minimum_cover_delete_bound G D S T T' minimal coverD coverRest) _
    _ = D.card + S.card + T'.card := (Nat.add_assoc _ _ _).symm
    _ ≤ U.card + mc + T'.card := Nat.add_le_add_right cost _

lemma exists_edge_cover_card_le {α : Type*} [DecidableEq α]
    (D : Finset (Sym2 α)) :
    ∃ S : Finset α, S.card ≤ D.card ∧
      ∀ u v : α, s(u, v) ∈ D → u ∈ S ∨ v ∈ S := by
  classical
  induction D using Finset.induction_on with
  | empty => exact ⟨∅, by simp, by simp⟩
  | @insert e D he ih =>
    obtain ⟨S, hcard, hcover⟩ := ih
    induction e using Sym2.inductionOn with
    | _ a b =>
      refine ⟨insert a S, ?_, ?_⟩
      · have h := Finset.card_insert_le a S
        rw [Finset.card_insert_of_notMem he]
        omega
      · intro u v huv
        rcases Finset.mem_insert.mp huv with huv | huv
        · rcases Sym2.eq_iff.mp huv with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · exact Or.inl (Finset.mem_insert_self _ _)
          · exact Or.inr (Finset.mem_insert_self _ _)
        · rcases hcover u v huv with h | h
          · exact Or.inl (Finset.mem_insert_of_mem h)
          · exact Or.inr (Finset.mem_insert_of_mem h)

lemma core_cover_singleton_incidence {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : PEqualNP.CircuitLowerBounds.Circuit)
    (T T' : Finset (Fin n))
    (small : ∀ j ∈ PEqualNP.Core.maximalCores G C,
      (PEqualNP.TopForm.gammaE G C j).card ≤ 1)
    (hT : PEqualNP.MetaComplexity.NestedCover.IsMinCover G T)
    (hT' : PEqualNP.MetaComplexity.NestedCover.IsMinCover
      (G.deleteEdges (((PEqualNP.Core.maximalCores G C).biUnion
        (PEqualNP.TopForm.gammaE G C) : Finset (Sym2 (Fin n))) : Set (Sym2 (Fin n)))) T') :
    ((PEqualNP.Core.maximalCores G C).biUnion (PEqualNP.TopForm.gammaE G C)).card + T.card ≤
      ((PEqualNP.Core.maximalCores G C).biUnion (PEqualNP.Core.coneSet n C)).card +
        (PEqualNP.Core.maximalCores G C).card + T'.card := by
  classical
  let M := PEqualNP.Core.maximalCores G C
  let D := M.biUnion (PEqualNP.TopForm.gammaE G C)
  let U := M.biUnion (PEqualNP.Core.coneSet n C)
  have hD : D.card ≤ M.card := by
    calc
      D.card ≤ ∑ j ∈ M, (PEqualNP.TopForm.gammaE G C j).card := Finset.card_biUnion_le
      _ ≤ ∑ j ∈ M, 1 := Finset.sum_le_sum fun j hj => small j hj
      _ = M.card := by simp
  have hM : M.card ≤ U.card := by
    apply Finset.card_le_card
    intro j hj
    exact Finset.mem_biUnion.mpr ⟨j, hj, Finset.mem_insert_self _ _⟩
  obtain ⟨S, hS, coverS⟩ := exists_edge_cover_card_le D
  apply core_cover_of_certificate G D U M.card S T T' hT.2
  · exact fun u v _ huv => coverS u v huv
  · exact hT'.1
  · omega


open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.TopForm PEqualNP.Core PEqualNP.SplitCount PEqualNP.ReadTwo

lemma foldl_wires_len (gs : List Gate) (acc : List Bool) :
    (gs.foldl (fun w gt => w ++ [gt.op.eval (gt.inputs.map fun i => w.getD i false)]) acc).length =
      acc.length + gs.length := by
  induction gs generalizing acc with
  | nil => simp
  | cons gt rest ih =>
    simp only [List.foldl_cons, ih, List.length_append, List.length_cons, List.length_nil]
    omega

lemma foldl_wires_getD_lt (gs : List Gate) (acc : List Bool) (i : ℕ) (hi : i < acc.length) :
    (gs.foldl (fun w gt => w ++ [gt.op.eval (gt.inputs.map fun idx => w.getD idx false)]) acc).getD i false =
      acc.getD i false := by
  induction gs generalizing acc with
  | nil => rfl
  | cons gt rest ih =>
    simp only [List.foldl_cons]
    have hlt : i < (acc ++ [gt.op.eval (gt.inputs.map fun idx => acc.getD idx false)]).length := by
      simp only [List.length_append, List.length_singleton]
      omega
    rw [ih _ hlt]
    simp [List.getD, List.getElem?_append_left hi]

lemma wires_length (C : Circuit) (x : List Bool) :
    (C.wires x).length = x.length + C.gates.length := by
  unfold Circuit.wires
  exact foldl_wires_len C.gates x

lemma wval_input {n : ℕ} (C : Circuit) (x : Fin n → Bool) (i : ℕ) (hi : i < n) :
    wval C x i = x ⟨i, hi⟩ := by
  unfold wval Circuit.wires
  have hlen : i < (List.ofFn x).length := by simpa using hi
  rw [foldl_wires_getD_lt C.gates (List.ofFn x) i hlen]
  simp [List.getD, hi]

lemma gateAt_mem {C : Circuit} {j : ℕ} (hj : j < C.gates.length) :
    gateAt C j ∈ C.gates := by
  unfold gateAt
  rw [List.getD_eq_getElem _ _ hj]
  exact List.getElem_mem hj

lemma gate_inputs_eq {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) {j : ℕ} (hj : j < C.gates.length) :
    (gateAt C j).inputs = [opnd C j 0, opnd C j 1] := by
  have hlen : (gateAt C j).inputs.length = 2 := hAO.2.2 (gateAt C j) (gateAt_mem hj)
  unfold opnd
  cases hl : (gateAt C j).inputs with
  | nil => simp [hl] at hlen
  | cons a l =>
    cases l with
    | nil => simp [hl] at hlen
    | cons b l' =>
      cases l' with
      | nil => simp [hl]
      | cons c l'' => simp [hl] at hlen

lemma opnd_mem {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) {j : ℕ} (hj : j < C.gates.length) (b : Fin 2) :
    opnd C j b ∈ (gateAt C j).inputs := by
  rw [gate_inputs_eq hAO hj]
  fin_cases b <;> simp

lemma opnd_lt {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) {j : ℕ} (hj : j < C.gates.length) (b : Fin 2) :
    opnd C j b < n + j :=
  hAO.2.1 j hj (opnd C j b) (opnd_mem hAO hj b)

lemma wval_gate_eval {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) (x : Fin n → Bool)
    {j : ℕ} (hj : j < C.gates.length) :
    wval C x (n + j) = (gateAt C j).op.eval [wval C x (opnd C j 0), wval C x (opnd C j 1)] := by
  unfold wval Circuit.wires
  have hsplit : C.gates = C.gates.take j ++ gateAt C j :: C.gates.drop (j + 1) := by
    have hg : gateAt C j = C.gates[j] := by
      unfold gateAt
      exact List.getD_eq_getElem _ _ hj
    rw [hg]
    simpa using (List.take_append_drop j C.gates).symm.trans (by
      congr 1
      exact (List.cons_getElem_drop_succ (h := hj)).symm)
  set step : List Bool → Gate → List Bool :=
    fun w gt => w ++ [gt.op.eval (gt.inputs.map fun i => w.getD i false)]
  set pre := (C.gates.take j).foldl step (List.ofFn x)
  have hpre_len : pre.length = n + j := by
    have h1 := foldl_wires_len (C.gates.take j) (List.ofFn x)
    simp only [List.length_ofFn, List.length_take, Nat.min_eq_left (Nat.le_of_lt hj)] at h1
    exact h1
  have h_eq : C.gates.foldl step (List.ofFn x) =
      (C.gates.drop (j + 1)).foldl step (step pre (gateAt C j)) := by
    conv_lhs => rw [hsplit]
    rw [List.foldl_append, List.foldl_cons]
  have h_pre_get : ∀ i < n + j, (C.gates.foldl step (List.ofFn x)).getD i false = pre.getD i false := by
    intro i hi
    rw [h_eq]
    have hi1 : i < (step pre (gateAt C j)).length := by
      simp only [step, List.length_append, List.length_singleton, hpre_len]
      omega
    rw [foldl_wires_getD_lt _ _ i hi1]
    simp only [step]
    have hi2 : i < pre.length := by omega
    simp [List.getD, List.getElem?_append_left hi2]
  have h_nj : (C.gates.foldl step (List.ofFn x)).getD (n + j) false =
      (gateAt C j).op.eval ((gateAt C j).inputs.map fun i => pre.getD i false) := by
    rw [h_eq]
    have hlt : n + j < (step pre (gateAt C j)).length := by
      simp only [step, List.length_append, List.length_singleton, hpre_len]
      omega
    rw [foldl_wires_getD_lt _ _ (n + j) hlt]
    simp only [step]
    have hle : pre.length ≤ n + j := by omega
    simp [List.getD, List.getElem?_append_right hle, hpre_len]
  rw [h_nj, gate_inputs_eq hAO hj]
  have h0 := h_pre_get (opnd C j 0) (opnd_lt hAO hj 0)
  have h1 := h_pre_get (opnd C j 1) (opnd_lt hAO hj 1)
  simp only [List.map_cons, List.map_nil, ← h0, ← h1]

lemma wval_gate_and {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) (x : Fin n → Bool)
    {j : ℕ} (hj : j < C.gates.length) (hop : (gateAt C j).op = GateOp.and) :
    wval C x (n + j) = (wval C x (opnd C j 0) && wval C x (opnd C j 1)) := by
  rw [wval_gate_eval hAO x hj, hop]
  simp [GateOp.eval]

lemma wval_gate_or {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) (x : Fin n → Bool)
    {j : ℕ} (hj : j < C.gates.length) (hop : (gateAt C j).op = GateOp.or) :
    wval C x (n + j) = (wval C x (opnd C j 0) || wval C x (opnd C j 1)) := by
  rw [wval_gate_eval hAO x hj, hop]
  simp [GateOp.eval]

lemma wval_ge_len {n : ℕ} (C : Circuit) (x : Fin n → Bool) {w : ℕ} (hw : n + C.gates.length ≤ w) :
    wval C x w = false := by
  unfold wval
  have hlen : (C.wires (List.ofFn x)).length ≤ w := by
    rw [wires_length, List.length_ofFn]
    exact hw
  exact List.getD_eq_default _ _ hlen

lemma wval_allTrue {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) :
    ∀ w < n + C.gates.length, wval C (fun _ : Fin n => true) w = true := by
  intro w
  induction w using Nat.strongRecOn with
  | ind w ih =>
    intro hw
    by_cases hlt : w < n
    · rw [wval_input C _ w hlt]
    · have hj : w - n < C.gates.length := by omega
      have hwn : w = n + (w - n) := by omega
      rw [hwn]
      have h0 : opnd C (w - n) 0 < w := by
        have := opnd_lt hAO hj 0
        omega
      have h1 : opnd C (w - n) 1 < w := by
        have := opnd_lt hAO hj 1
        omega
      have hv0 := ih (opnd C (w - n) 0) h0 (by omega)
      have hv1 := ih (opnd C (w - n) 1) h1 (by omega)
      rcases hAO.1 (gateAt C (w - n)) (gateAt_mem hj) with hop | hop
      · rw [wval_gate_and hAO _ hj hop, hv0, hv1]; rfl
      · rw [wval_gate_or hAO _ hj hop, hv0, hv1]; rfl

lemma graphFun_iff {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] (x : Fin n → Bool) :
    graphFun G ∅ x = true ↔ ∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true := by
  simp [graphFun]

lemma graphFun_unitInput_false {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (v : Fin n) :
    graphFun G ∅ (unitInput v) = false := by
  cases hf : graphFun G ∅ (unitInput v) with
  | false => rfl
  | true =>
    rw [graphFun_iff] at hf
    rcases hf with ⟨u, w, hadj, hu, hw⟩
    simp only [unitInput, decide_eq_true_eq] at hu hw
    subst hu; subst hw
    exact (G.ne_of_adj hadj rfl).elim

def WireBelowF {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) (w : ℕ) : Prop :=
  ∀ x : Fin n → Bool, wval C x w = true → graphFun G ∅ x = true

lemma not_wireBelowF_input {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    {w : ℕ} (hw : w < n) : ¬ WireBelowF G C w := by
  intro h
  have h1 : wval C (unitInput ⟨w, hw⟩) w = true := by
    rw [wval_input C _ w hw]
    simp [unitInput]
  have h2 := h (unitInput ⟨w, hw⟩) h1
  rw [graphFun_unitInput_false] at h2
  cases h2

lemma wireBelowF_gate_iff {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) (k : ℕ) :
    WireBelowF G C (n + k) ↔ BelowF G C k := Iff.rfl

lemma core_op_and {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {C : Circuit} (hAO : IsAO2 n C) {j : ℕ} (hc : PEqualNP.Core.IsCore G C j) :
    (gateAt C j).op = GateOp.and := by
  rcases hAO.1 _ (gateAt_mem hc.1) with h | h
  · exact h
  · exfalso
    apply hc.2.2.1
    have hj := hc.1
    have hop (b : Fin 2) : PEqualNP.Core.IsImpOperand G C (opnd C j b) := by
      have hb := opnd_lt hAO hc.1 b
      have below : WireBelowF G C (opnd C j b) := by
        intro x hx
        apply hc.2.1.1 x
        change wval C x (n + j) = true
        rw [wval_gate_or hAO x hc.1 h]
        apply Bool.or_eq_true_iff.mpr
        fin_cases b
        · exact Or.inl hx
        · exact Or.inr hx
      have hbn : n ≤ opnd C j b := by
        by_contra hh
        exact not_wireBelowF_input G C (by omega) below
      refine ⟨hbn, ?_, ?_⟩
      · change BelowF G C (opnd C j b - n)
        rw [← wireBelowF_gate_iff, Nat.add_sub_of_le hbn]
        exact below
      · refine ⟨fun _ => true, ?_⟩
        change wval C (fun _ => true) (n + (opnd C j b - n)) = true
        rw [Nat.add_sub_of_le hbn]
        exact wval_allTrue hAO _ (by omega)
    exact ⟨hop 0, hop 1⟩

lemma maximal_core_op_and {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {C : Circuit} (hAO : IsAO2 n C) {j : ℕ}
    (hj : j ∈ PEqualNP.Core.maximalCores G C) :
    (gateAt C j).op = GateOp.and := by
  exact core_op_and hAO ((Finset.mem_filter.mp hj).2.1)



open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.Core PEqualNP.TopForm

abbrev eqGraph : SimpleGraph (Fin 4) := SimpleGraph.fromRel fun a b =>
  (a = 0 ∧ b = 1) ∨ (a = 0 ∧ b = 2) ∨ (a = 3 ∧ b = 1)

def eqCircuit : Circuit :=
  ⟨[⟨.and, [3, 1]⟩, ⟨.or, [1, 2]⟩, ⟨.or, [0, 4]⟩,
    ⟨.and, [6, 5]⟩, ⟨.and, [0, 5]⟩, ⟨.or, [8, 4]⟩], 9⟩

lemma eq_ao : IsAO2 4 eqCircuit := by decide +kernel
lemma eq_fixed : IsLiftFixedPoint eqGraph eqCircuit := by decide +kernel
lemma eq_correct : circuitFun 4 eqCircuit = graphFun eqGraph ∅ := by
  funext x
  revert x
  decide +kernel
lemma eq_mc : maximalCores eqGraph eqCircuit = {3} := by decide +kernel
lemma eq_D : (maximalCores eqGraph eqCircuit).biUnion (gammaE eqGraph eqCircuit) =
  {s(0, 1), s(0, 2), s(1, 3)} := by decide +kernel
lemma eq_U : (maximalCores eqGraph eqCircuit).biUnion (coneSet 4 eqCircuit) =
  {0, 1, 2, 3} := by decide +kernel

lemma eq_bipartite : ∀ u v : Fin 4, eqGraph.Adj u v →
    decide (u = 0 ∨ u = 3) ≠ decide (v = 0 ∨ v = 3) := by decide +kernel
lemma eq_no4 : NoFourCycle eqGraph := by decide +kernel
lemma eq_cover : IsMinCover eqGraph ({0, 1} : Finset (Fin 4)) := by
  unfold IsMinCover SimpleGraph.IsVertexCover
  decide +kernel
lemma eq_deleted_cover : IsMinCover (eqGraph.deleteEdges
    (((maximalCores eqGraph eqCircuit).biUnion (gammaE eqGraph eqCircuit) : Finset (Sym2 (Fin 4))) :
      Set (Sym2 (Fin 4)))) ∅ := by
  rw [eq_D]
  refine ⟨?_, fun S _ => by simp⟩
  intro u v huv
  simp only [SimpleGraph.deleteEdges_adj, Finset.mem_coe] at huv
  have noEdge : ∀ u v : Fin 4,
      ¬ (eqGraph.Adj u v ∧ s(u, v) ∉ ({s(0, 1), s(0, 2), s(1, 3)} : Finset (Sym2 (Fin 4)))) := by
    decide +kernel
  exact (noEdge u v huv).elim


namespace Leaf

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.TopForm

lemma foldl_snoc_prefix {α β : Type _} (F : List α → β → α) (gs : List β) (init : List α) :
    init <+: gs.foldl (fun R g => R ++ [F R g]) init := by
  induction gs generalizing init with
  | nil => exact List.prefix_refl _
  | cons g gs ih => exact (List.prefix_append init [F init g]).trans (ih _)

lemma foldl_snoc_length {α β : Type _} (F : List α → β → α) (gs : List β) (init : List α) :
    (gs.foldl (fun R g => R ++ [F R g]) init).length = init.length + gs.length := by
  induction gs generalizing init with
  | nil => simp
  | cons g gs ih => simp [ih]; omega

lemma getD_of_prefix {α : Type _} {P L : List α} (h : P <+: L) {i : ℕ} (hi : i < P.length)
    (d : α) : L.getD i d = P.getD i d := by
  obtain ⟨t, rfl⟩ := h
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma foldl_snoc_init {α : Type _} (G : List α → Gate → α) (d : α) (init : List α)
    (gs : List Gate) (i : ℕ) (hi : i < init.length) :
    (gs.foldl (fun R g => R ++ [G (g.inputs.map fun i => R.getD i d) g]) init).getD i d
      = init.getD i d :=
  getD_of_prefix (foldl_snoc_prefix (fun R g => G (g.inputs.map fun i => R.getD i d) g) _ _) hi d

lemma foldl_snoc_beyond {α : Type _} (G : List α → Gate → α) (d : α) (init : List α)
    (gs : List Gate) (i : ℕ) (hi : init.length + gs.length ≤ i) :
    (gs.foldl (fun R g => R ++ [G (g.inputs.map fun i => R.getD i d) g]) init).getD i d = d := by
  apply List.getD_eq_default
  rw [foldl_snoc_length (fun R g => G (g.inputs.map fun i => R.getD i d) g)]
  exact hi

lemma foldl_snoc_gate {α : Type _} (G : List α → Gate → α) (d : α) (init : List α)
    (gs : List Gate) (j : ℕ) (hj : j < gs.length)
    (hrb : ∀ i ∈ gs[j].inputs, i < init.length + j) :
    (gs.foldl (fun R g => R ++ [G (g.inputs.map fun i => R.getD i d) g]) init).getD
        (init.length + j) d
      = G (gs[j].inputs.map fun i =>
          (gs.foldl (fun R g => R ++ [G (g.inputs.map fun i => R.getD i d) g]) init).getD i d)
          gs[j] := by
  have hsplit : gs = gs.take j ++ gs[j] :: gs.drop (j + 1) := by simp
  set P := (gs.take j).foldl (fun R g => R ++ [G (g.inputs.map fun i => R.getD i d) g]) init
    with hP
  have hPl : P.length = init.length + j := by
    rw [hP, foldl_snoc_length (fun R g => G (g.inputs.map fun i => R.getD i d) g)]
    simp; omega
  have hpre : (P ++ [G (gs[j].inputs.map fun i => P.getD i d) gs[j]]) <+:
      gs.foldl (fun R g => R ++ [G (g.inputs.map fun i => R.getD i d) g]) init := by
    conv_rhs => rw [hsplit]
    rw [List.foldl_append, List.foldl_cons]
    exact foldl_snoc_prefix (fun R g => G (g.inputs.map fun i => R.getD i d) g) _ _
  have hpre2 := (List.prefix_append P _).trans hpre
  rw [getD_of_prefix hpre (by simp; omega)]
  have e1 : (P ++ [G (gs[j].inputs.map fun i => P.getD i d) gs[j]]).getD (init.length + j) d
      = G (gs[j].inputs.map fun i => P.getD i d) gs[j] := by
    rw [← hPl]; simp
  rw [e1]
  congr 1
  apply List.map_congr_left
  intro i hi
  rw [getD_of_prefix hpre2 (by rw [hPl]; exact hrb i hi)]


lemma wires_eq (C : Circuit) (x : List Bool) :
    C.wires x = C.gates.foldl
      (fun R g => R ++ [(fun ins (g : Gate) => g.op.eval ins) (g.inputs.map fun i => R.getD i false) g])
      x := rfl

lemma gateAt_eq (C : Circuit) (j : ℕ) (hj : j < C.gates.length) :
    gateAt C j = C.gates[j] := by
  simp [gateAt, List.getD_eq_getElem?_getD, hj]


section Wires
variable (C : Circuit) (n : ℕ)
abbrev W (x : Fin n → Bool) (i : ℕ) : Bool := (C.wires (List.ofFn x)).getD i false

lemma W_input (x : Fin n → Bool) (i : ℕ) (hi : i < n) : W C n x i = x ⟨i, hi⟩ := by
  unfold W
  rw [wires_eq, foldl_snoc_init (fun ins (g : Gate) => g.op.eval ins) false _ _ _ (by simpa using hi)]
  simp [List.getD_eq_getElem?_getD, hi]

lemma W_gate (x : Fin n → Bool) (j : ℕ) (hj : j < C.gates.length)
    (hrb : ∀ i ∈ (gateAt C j).inputs, i < n + j) :
    W C n x (n + j) = (gateAt C j).op.eval ((gateAt C j).inputs.map (W C n x)) := by
  unfold W
  rw [gateAt_eq C j hj] at hrb ⊢
  have := foldl_snoc_gate (fun ins (g : Gate) => g.op.eval ins) false (List.ofFn x) C.gates j hj
    (by simpa using hrb)
  simp only [List.length_ofFn] at this
  rw [wires_eq, this]

end Wires

section Basic

variable (n : ℕ) (C : Circuit)


def Step (a b : ℕ) : Prop := ∃ g < C.gates.length, a = n + g ∧ b ∈ (gateAt C g).inputs


abbrev Reach : ℕ → ℕ → Prop := Relation.ReflTransGen (Step n C)

lemma foldl_snoc_split {α β : Type _} (F : List α → β → α) (gs : List β) (init : List α)
    (j : ℕ) (hj : j < gs.length) (d : α) :
    (gs.foldl (fun R g => R ++ [F R g]) init).getD (init.length + j) d
      = F ((gs.take j).foldl (fun R g => R ++ [F R g]) init) gs[j] ∧
    ((gs.take j).foldl (fun R g => R ++ [F R g]) init) <+:
      gs.foldl (fun R g => R ++ [F R g]) init ∧
    ((gs.take j).foldl (fun R g => R ++ [F R g]) init).length = init.length + j := by
  have hsplit : gs = gs.take j ++ gs[j] :: gs.drop (j + 1) := by simp
  set P := (gs.take j).foldl (fun R g => R ++ [F R g]) init with hP
  have hPl : P.length = init.length + j := by
    rw [hP, foldl_snoc_length F]; simp; omega
  have hpre : (P ++ [F P gs[j]]) <+: gs.foldl (fun R g => R ++ [F R g]) init := by
    conv_rhs => rw [hsplit]
    rw [List.foldl_append, List.foldl_cons]
    exact foldl_snoc_prefix F _ _
  refine ⟨?_, (List.prefix_append P _).trans hpre, hPl⟩
  rw [getD_of_prefix hpre (by simp; omega), ← hPl]
  simp


def coneF (cs : List (List ℕ)) (g : Gate) : List ℕ :=
  (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + cs.length))).flatMap
    (fun w => (w - n) :: cs.getD (w - n) [])

lemma cones_eq : cones n C = C.gates.foldl (fun R g => R ++ [coneF n R g]) [] := rfl

lemma flatMap_congr' {α β : Type _} {l : List α} {f g : α → List β}
    (h : ∀ a ∈ l, f a = g a) : l.flatMap f = l.flatMap g := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.flatMap_cons]
    rw [h a (by simp), ih (fun b hb => h b (by simp [hb]))]

lemma cone_getD {j : ℕ} (hj : j < C.gates.length) :
    (cones n C).getD j [] = ((gateAt C j).inputs.filter
      (fun w => decide (n ≤ w ∧ w < n + j))).flatMap (fun w => (w - n) :: (cones n C).getD (w - n) []) := by
  obtain ⟨h1, h2, h3⟩ := foldl_snoc_split (coneF n) C.gates [] j hj []
  simp only [List.length_nil, zero_add] at h1 h3
  rw [← cones_eq] at h1 h2
  generalize (C.gates.take j).foldl (fun R g => R ++ [coneF n R g]) [] = P at h1 h2 h3
  rw [h1, gateAt_eq C j hj]
  unfold coneF
  rw [h3]
  apply flatMap_congr'
  intro w hw
  rw [List.mem_filter] at hw
  have : w - n < j := by simp at hw; omega
  rw [getD_of_prefix h2 (by rw [h3]; exact this)]

lemma inCone_iff (hrb : ReadsBack n C) {i j : ℕ} (hj : j < C.gates.length) :
    InCone n C i j ↔ ∃ w ∈ (gateAt C j).inputs, n ≤ w ∧ (w - n = i ∨ InCone n C i (w - n)) := by
  unfold InCone
  rw [cone_getD n C hj]
  constructor
  · intro h
    obtain ⟨w, hw, hi⟩ := List.mem_flatMap.1 h
    rw [List.mem_filter] at hw
    simp only [decide_eq_true_eq] at hw
    rcases List.mem_cons.1 hi with h' | h'
    · exact ⟨w, hw.1, hw.2.1, Or.inl h'.symm⟩
    · exact ⟨w, hw.1, hw.2.1, Or.inr h'⟩
  · rintro ⟨w, hw, hnw, h⟩
    refine List.mem_flatMap.2 ⟨w, List.mem_filter.2 ⟨hw, ?_⟩, ?_⟩
    · simp only [decide_eq_true_eq]; exact ⟨hnw, hrb j hj w hw⟩
    · rcases h with h | h
      · exact List.mem_cons.2 (Or.inl h.symm)
      · exact List.mem_cons.2 (Or.inr h)

lemma inCone_iff_trans (hrb : ReadsBack n C) (i : ℕ) :
    ∀ j, j < C.gates.length → (InCone n C i j ↔ Relation.TransGen (Step n C) (n + j) (n + i)) := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
  intro hj
  rw [inCone_iff n C hrb hj]
  constructor
  · rintro ⟨w, hw, hnw, h⟩
    have hwl : w < n + j := hrb j hj w hw
    have hst : Step n C (n + j) w := ⟨j, hj, rfl, hw⟩
    rcases h with h | h
    · have : w = n + i := by omega
      subst this
      exact Relation.TransGen.single hst
    · have hlt : w - n < j := by omega
      have := (ih (w - n) hlt (by omega)).1 h
      have hw' : n + (w - n) = w := by omega
      rw [hw'] at this
      exact Relation.TransGen.head hst this
  · intro h
    obtain ⟨c, ⟨g, hg, hjg, hc⟩, hr⟩ := Relation.TransGen.head'_iff.1 h
    have hgj : g = j := by omega
    subst hgj
    have hcl : c < n + g := hrb g hg c hc
    rcases Relation.ReflTransGen.cases_head hr with hci | ⟨d, ⟨g', hg', hcg', _⟩, hr'⟩
    · exact ⟨c, hc, by omega, Or.inl (by omega)⟩
    · refine ⟨c, hc, by omega, Or.inr ?_⟩
      have hlt : c - n < g := by omega
      refine (ih (c - n) hlt (by omega)).2 ?_
      have hcn : n + (c - n) = c := by omega
      rw [hcn]
      exact Relation.TransGen.head' ⟨g', hg', hcg', by assumption⟩ hr'

lemma mem_coneSet (hrb : ReadsBack n C) {j : ℕ} (hj : j < C.gates.length) (g : ℕ) :
    g ∈ PEqualNP.Core.coneSet n C j ↔ g < C.gates.length ∧ Reach n C (n + j) (n + g) := by
  unfold PEqualNP.Core.coneSet
  rw [Finset.mem_insert, Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro (rfl | ⟨hg, hc⟩)
    · exact ⟨hj, Relation.ReflTransGen.refl⟩
    · exact ⟨hg, ((inCone_iff_trans n C hrb g j hj).1 hc).to_reflTransGen⟩
  · rintro ⟨hg, hr⟩
    rcases Relation.reflTransGen_iff_eq_or_transGen.1 hr with h | h
    · left; omega
    · right; exact ⟨hg, (inCone_iff_trans n C hrb g j hj).2 h⟩

lemma reach_le (hrb : ReadsBack n C) {a b : ℕ} (h : Reach n C a b) : b ≤ a := by
  induction h with
  | refl => exact le_refl _
  | tail _ hst ih =>
    obtain ⟨g, hg, rfl, hc⟩ := hst
    have := hrb g hg _ hc
    omega

end Basic


section AO

variable {n : ℕ} {C : Circuit}

lemma list_two {l : List ℕ} (h : l.length = 2) : l = [l.getD 0 0, l.getD 1 0] := by
  match l, h with
  | [a, b], _ => rfl

lemma ao_inputs (hC : IsAO2 n C) {g : ℕ} (hg : g < C.gates.length) :
    (gateAt C g).inputs = [opnd C g 0, opnd C g 1] := by
  have hl : (gateAt C g).inputs.length = 2 := by
    rw [gateAt_eq C g hg]; exact hC.2.2 _ (List.getElem_mem hg)
  exact list_two hl

lemma ao_op (hC : IsAO2 n C) {g : ℕ} (hg : g < C.gates.length) :
    (gateAt C g).op = GateOp.and ∨ (gateAt C g).op = GateOp.or := by
  rw [gateAt_eq C g hg]; exact hC.1 _ (List.getElem_mem hg)

lemma opnd_mem (hC : IsAO2 n C) {g : ℕ} (hg : g < C.gates.length) (b : Fin 2) :
    opnd C g b ∈ (gateAt C g).inputs := by
  rw [ao_inputs hC hg]; fin_cases b <;> simp

lemma opnd_lt (hC : IsAO2 n C) {g : ℕ} (hg : g < C.gates.length) (b : Fin 2) :
    opnd C g b < n + g := hC.2.1 g hg _ (opnd_mem hC hg b)

lemma step_opnd (hC : IsAO2 n C) {g : ℕ} (hg : g < C.gates.length) (b : Fin 2) :
    Step n C (n + g) (opnd C g b) := ⟨g, hg, rfl, opnd_mem hC hg b⟩

lemma step_inv (hC : IsAO2 n C) {a c : ℕ} (h : Step n C a c) :
    ∃ g < C.gates.length, a = n + g ∧ ∃ b : Fin 2, c = opnd C g b := by
  obtain ⟨g, hg, rfl, hc⟩ := h
  rw [ao_inputs hC hg] at hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with hc | hc
  · exact ⟨g, hg, rfl, 0, hc⟩
  · exact ⟨g, hg, rfl, 1, hc⟩

variable {j : ℕ}

lemma K_lt (hC : IsAO2 n C) (hj : j < C.gates.length) {g : ℕ}
    (hK : g ∈ PEqualNP.Core.coneSet n C j) : g < C.gates.length :=
  ((mem_coneSet n C hC.2.1 hj g).1 hK).1

lemma K_reach (hC : IsAO2 n C) (hj : j < C.gates.length) {g g' : ℕ}
    (hK : g ∈ PEqualNP.Core.coneSet n C j) (hr : Reach n C (n + g) (n + g'))
    (hg' : g' < C.gates.length) : g' ∈ PEqualNP.Core.coneSet n C j := by
  rw [mem_coneSet n C hC.2.1 hj] at hK ⊢
  exact ⟨hg', hK.2.trans hr⟩

lemma K_opnd (hC : IsAO2 n C) (hj : j < C.gates.length) {g : ℕ}
    (hK : g ∈ PEqualNP.Core.coneSet n C j) (b : Fin 2) (hge : n ≤ opnd C g b) :
    opnd C g b - n ∈ PEqualNP.Core.coneSet n C j ∧ opnd C g b - n < g := by
  have hg := K_lt hC hj hK
  have hlt := opnd_lt hC hg b
  refine ⟨K_reach hC hj hK ?_ (by omega), by omega⟩
  have : n + (opnd C g b - n) = opnd C g b := by omega
  rw [this]
  exact Relation.ReflTransGen.single (step_opnd hC hg b)

lemma K_cover (hC : IsAO2 n C) (hj : j < C.gates.length) {g : ℕ}
    (hK : g ∈ PEqualNP.Core.coneSet n C j) (hne : g ≠ j) :
    ∃ h ∈ PEqualNP.Core.coneSet n C j, ∃ b : Fin 2, opnd C h b = n + g := by
  have hr := ((mem_coneSet n C hC.2.1 hj g).1 hK).2
  rcases Relation.reflTransGen_iff_eq_or_transGen.1 hr with h | h
  · exact absurd (by omega) hne
  · obtain ⟨c, hrc, hst⟩ := Relation.TransGen.tail'_iff.1 h
    obtain ⟨h', hh', rfl, b, hb⟩ := step_inv hC hst
    refine ⟨h', ?_, b, hb.symm⟩
    rw [mem_coneSet n C hC.2.1 hj]
    exact ⟨hh', hrc⟩


def slots (n : ℕ) (C : Circuit) (j : ℕ) : Finset (ℕ × Fin 2) :=
  PEqualNP.Core.coneSet n C j ×ˢ (Finset.univ : Finset (Fin 2))


def slotW (C : Circuit) (p : ℕ × Fin 2) : ℕ := opnd C p.1 p.2

end AO

section Main

variable {n : ℕ} {C : Circuit}


lemma agree (hC : IsAO2 n C) {j : ℕ} (hj : j < C.gates.length) (x y : Fin n → Bool)
    (hxy : ∀ i (hi : i < n), i ∈ (slots n C j).image (slotW C) → x ⟨i, hi⟩ = y ⟨i, hi⟩) :
    ∀ g ∈ PEqualNP.Core.coneSet n C j, W C n x (n + g) = W C n y (n + g) := by
  intro g
  induction g using Nat.strong_induction_on with
  | _ g ih =>
  intro hK
  have hg := K_lt hC hj hK
  have hop : ∀ b : Fin 2, W C n x (opnd C g b) = W C n y (opnd C g b) := by
    intro b
    by_cases hn : opnd C g b < n
    · rw [W_input C n x _ hn, W_input C n y _ hn]
      apply hxy
      exact Finset.mem_image.2 ⟨(g, b), Finset.mem_product.2 ⟨hK, Finset.mem_univ _⟩, rfl⟩
    · obtain ⟨hK', hlt⟩ := K_opnd hC hj hK b (by omega)
      have he : n + (opnd C g b - n) = opnd C g b := by omega
      rw [← he]
      exact ih _ hlt hK'
  rw [W_gate C n x g hg (hC.2.1 g hg), W_gate C n y g hg (hC.2.1 g hg), ao_inputs hC hg]
  simp only [List.map_cons, List.map_nil, hop 0, hop 1]

lemma pairInput_comm (u v : Fin n) : pairInput u v = pairInput v u := by
  funext w; unfold pairInput; simp [or_comm]


lemma end_mem (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hC : IsAO2 n C) {j : ℕ}
    (hj : j < C.gates.length) (hbelow : BelowF G C j) {u v : Fin n} (huv : G.Adj u v)
    (hacc : gateVal n C j (pairInput u v) = true) :
    u.val ∈ (slots n C j).image (slotW C) := by
  by_contra hu
  have hjK : j ∈ PEqualNP.Core.coneSet n C j := Finset.mem_insert_self _ _
  have hag := agree hC hj (pairInput u v) (fun w => decide (w = v)) (by
    intro i hi hI
    have hne : (⟨i, hi⟩ : Fin n) ≠ u := by
      rintro rfl; exact hu hI
    unfold pairInput
    simp [hne]) j hjK
  have hy : gateVal n C j (fun w => decide (w = v)) = true := by
    have e1 : gateVal n C j (fun w => decide (w = v)) = W C n (fun w => decide (w = v)) (n + j) := rfl
    have e2 : gateVal n C j (pairInput u v) = W C n (pairInput u v) (n + j) := rfl
    rw [e1, ← hag, ← e2]; exact hacc
  have := hbelow _ hy
  unfold graphFun at this
  simp at this

end Main

def unionSlots (U : Finset ℕ) : Finset (ℕ × Fin 2) := U ×ˢ Finset.univ

def unionInputs (n : ℕ) (C : Circuit) (U : Finset ℕ) : Finset (Fin n) :=
  Finset.univ.filter fun v => v.val ∈ (unionSlots U).image (slotW C)

lemma union_leaf_count {n : ℕ} {C : Circuit} (hC : IsAO2 n C)
    (M : Finset ℕ) (hM : ∀ j ∈ M, j < C.gates.length) :
    (unionInputs n C (M.biUnion (PEqualNP.Core.coneSet n C))).card ≤
      (M.biUnion (PEqualNP.Core.coneSet n C)).card + M.card := by
  classical
  let U := M.biUnion (PEqualNP.Core.coneSet n C)
  let I := (unionSlots U).image (slotW C)
  have hMsub : M ⊆ U := by
    intro j hj
    exact Finset.mem_biUnion.mpr ⟨j, hj, Finset.mem_insert_self _ _⟩
  have hS : (unionInputs n C U).card ≤ (I.filter fun w => w < n).card := by
    apply Finset.card_le_card_of_injOn (fun w : Fin n => w.val)
    · intro w hw
      simp only [unionInputs, Finset.coe_filter, Finset.mem_univ, true_and,
        Set.mem_ofPred_eq] at hw
      simp only [Finset.coe_filter, Set.mem_ofPred_eq]
      exact ⟨hw, w.isLt⟩
    · intro a _ b _ h
      exact Fin.ext h
  have hG : (U \ M).card ≤ (I.filter fun w => ¬ w < n).card := by
    apply Finset.card_le_card_of_injOn (fun g => n + g)
    · intro g hg
      simp only [Finset.coe_sdiff, Set.mem_sdiff, Finset.mem_coe] at hg
      obtain ⟨j, hj, hgj⟩ := Finset.mem_biUnion.mp hg.1
      have hne : g ≠ j := fun h => hg.2 (h ▸ hj)
      obtain ⟨h, hh, b, hb⟩ := K_cover hC (hM j hj) hgj hne
      have hhU : h ∈ U := Finset.mem_biUnion.mpr ⟨j, hj, hh⟩
      simp only [Finset.coe_filter, Set.mem_ofPred_eq]
      refine ⟨Finset.mem_image.mpr ⟨(h, b),
        Finset.mem_product.mpr ⟨hhU, Finset.mem_univ _⟩, hb⟩, ?_⟩
      omega
    · intro a _ b _ h
      simp only at h
      omega
  have hsplit := Finset.card_filter_add_card_filter_not (s := I) (fun w => w < n)
  have hslots : (unionSlots U).card = U.card * 2 := by
    simp [unionSlots]
  have himage : I.card ≤ (unionSlots U).card := Finset.card_image_le
  have hdiff := Finset.card_sdiff_of_subset hMsub
  change (unionInputs n C U).card ≤ U.card + M.card
  omega

lemma core_endpoints_leaf_bound {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit) (hC : IsAO2 n C) :
    (((PEqualNP.Core.maximalCores G C).biUnion (gammaE G C)).biUnion Sym2.toFinset).card ≤
      ((PEqualNP.Core.maximalCores G C).biUnion (PEqualNP.Core.coneSet n C)).card +
        (PEqualNP.Core.maximalCores G C).card := by
  classical
  let M := PEqualNP.Core.maximalCores G C
  let U := M.biUnion (PEqualNP.Core.coneSet n C)
  have hM : ∀ j ∈ M, j < C.gates.length := by
    intro j hj
    exact Finset.mem_range.mp (Finset.mem_filter.mp hj).1
  apply le_trans ?_ (union_leaf_count hC M hM)
  apply Finset.card_le_card
  intro v hv
  obtain ⟨e, he, hv⟩ := Finset.mem_biUnion.mp hv
  obtain ⟨j, hj, hej⟩ := Finset.mem_biUnion.mp he
  have hcore : PEqualNP.Core.IsCore G C j := (Finset.mem_filter.mp hj).2.1
  obtain ⟨heG, a, b, rfl, hab⟩ := Finset.mem_filter.mp hej
  have hadj : G.Adj a b := by simpa using heG
  have slot : v.val ∈ (slots n C j).image (slotW C) := by
    rcases Sym2.mem_iff.mp (Sym2.mem_toFinset.mp hv) with rfl | rfl
    · exact end_mem G hC (hM j hj) hcore.2.1.1 hadj hab
    · exact end_mem G hC (hM j hj) hcore.2.1.1 hadj.symm
        (by rw [pairInput_comm]; exact hab)
  obtain ⟨⟨g, b⟩, hgb, heq⟩ := Finset.mem_image.mp slot
  have hg : g ∈ U := Finset.mem_biUnion.mpr ⟨j, hj, (Finset.mem_product.mp hgb).1⟩
  apply Finset.mem_filter.mpr
  exact ⟨Finset.mem_univ _, Finset.mem_image.mpr ⟨(g, b),
    Finset.mem_product.mpr ⟨hg, Finset.mem_univ _⟩, heq⟩⟩


end Leaf

lemma core_cover_matching_incidence {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : PEqualNP.CircuitLowerBounds.Circuit)
    (T T' : Finset (Fin n)) (hC : PEqualNP.TopForm.IsAO2 n C)
    (matching : (((PEqualNP.Core.maximalCores G C).biUnion
      (PEqualNP.TopForm.gammaE G C)) : Set (Sym2 (Fin n))).PairwiseDisjoint Sym2.toFinset)
    (hT : PEqualNP.MetaComplexity.NestedCover.IsMinCover G T)
    (hT' : PEqualNP.MetaComplexity.NestedCover.IsMinCover
      (G.deleteEdges (((PEqualNP.Core.maximalCores G C).biUnion
        (PEqualNP.TopForm.gammaE G C) : Finset (Sym2 (Fin n))) : Set (Sym2 (Fin n)))) T') :
    ((PEqualNP.Core.maximalCores G C).biUnion (PEqualNP.TopForm.gammaE G C)).card + T.card ≤
      ((PEqualNP.Core.maximalCores G C).biUnion (PEqualNP.Core.coneSet n C)).card +
        (PEqualNP.Core.maximalCores G C).card + T'.card := by
  classical
  let M := PEqualNP.Core.maximalCores G C
  let D := M.biUnion (PEqualNP.TopForm.gammaE G C)
  let U := M.biUnion (PEqualNP.Core.coneSet n C)
  have hDsub : D ⊆ G.edgeFinset := by
    intro e he
    obtain ⟨j, _, hej⟩ := Finset.mem_biUnion.mp he
    exact (Finset.mem_filter.mp hej).1
  have vertices : (D.biUnion Sym2.toFinset).card = 2 * D.card := by
    rw [Finset.card_biUnion matching]
    calc
      ∑ e ∈ D, e.toFinset.card = ∑ e ∈ D, 2 := by
        apply Finset.sum_congr rfl
        intro e he
        exact Sym2.card_toFinset_of_not_isDiag e (G.not_isDiag_of_mem_edgeFinset (hDsub he))
      _ = 2 * D.card := by simp [Nat.mul_comm]
  have bound := Leaf.core_endpoints_leaf_bound G C hC
  change (D.biUnion Sym2.toFinset).card ≤ U.card + M.card at bound
  rw [vertices] at bound
  obtain ⟨S, hS, coverS⟩ := exists_edge_cover_card_le D
  apply core_cover_of_certificate G D U M.card S T T' hT.2
  · exact fun u v _ huv => coverS u v huv
  · exact hT'.1
  · omega

end PEqualNP.Outside.L_meta_2962_aux
