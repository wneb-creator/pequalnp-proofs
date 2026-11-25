import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Basic
import PEqualNP.Defs.TopForm

namespace PEqualNP.Outside.L_meta_3566.DoubleLift

def baseEdges : List (Fin 8 × Fin 8) :=
  [(0, 4), (0, 6), (1, 5), (1, 6), (1, 7), (2, 6), (3, 7), (4, 7)]

def lower (v : Fin 8) : Fin 16 :=
  ⟨v.val, Nat.lt_trans v.isLt (by decide)⟩

def upper (v : Fin 8) : Fin 16 :=
  ⟨v.val + 8, Nat.add_lt_add_right v.isLt 8⟩

def doubleEdges : List (Fin 16 × Fin 16) :=
  baseEdges.flatMap fun uv => [(lower uv.1, upper uv.2), (lower uv.2, upper uv.1)]

def adjacencyBool (u v : Fin 16) : Bool :=
  doubleEdges.contains (u, v) || doubleEdges.contains (v, u)

def adjacencyBits (u v : Fin 16) : Bool :=
  (45938212404688224660688823459344804183317390199943558577277627156041584640 : Nat).testBit
    (16 * u.val + v.val)

lemma adjacency_bits : ∀ u v : Fin 16, adjacencyBool u v = adjacencyBits u v := by
  decide +kernel

lemma adjacency_symmetric : ∀ u v : Fin 16, adjacencyBool u v = adjacencyBool v u := by
  decide +kernel

lemma adjacency_irreflexive : ∀ u : Fin 16, adjacencyBool u u = false := by
  decide +kernel

lemma bipartite_sides : ∀ u v : Fin 16, adjacencyBool u v = true →
    (u.val < 8 ∧ 8 ≤ v.val) ∨ (v.val < 8 ∧ 8 ≤ u.val) := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 4000000 in
lemma no_four_cycle : ∀ a b : Fin 16, a ≠ b →
    (Finset.univ.filter fun w => adjacencyBool a w = true ∧ adjacencyBool b w = true).card ≤ 1 := by
  have fast : ∀ a b : Fin 16, a ≠ b →
      (Finset.univ.filter fun w => adjacencyBits a w = true ∧ adjacencyBits b w = true).card ≤ 1 := by
    decide +kernel
  simpa only [adjacency_bits] using fast

def graphFunction (x : Fin 16 → Bool) : Bool :=
  doubleEdges.any fun uv => x uv.1 && x uv.2

def naiveTerm (x : Fin 16 → Bool) : Bool :=
  x 2 && (x 14 || x 15) && (x 12 || x 14)

def badAssignment (v : Fin 16) : Bool :=
  [2, 12, 15].contains v

lemma bad_assignment_no_edge : graphFunction badAssignment = false := by
  decide +kernel

lemma bad_assignment_naive_term : naiveTerm badAssignment = true := by
  decide +kernel

lemma naive_term_does_not_imply_graph :
    ¬ (∀ x : Fin 16 → Bool, naiveTerm x = true → graphFunction x = true) := by
  intro h
  have bad := h badAssignment bad_assignment_naive_term
  rw [bad_assignment_no_edge] at bad
  cases bad

def withEdgeAdjacency (s t u v : Fin 16) : Bool :=
  adjacencyBool u v || (u == s && v == t) || (u == t && v == s)

lemma add_two_fifteen_cycle :
    ([2, 14, 1, 15] : List (Fin 16)).Nodup ∧
    withEdgeAdjacency 2 15 2 14 = true ∧
    withEdgeAdjacency 2 15 14 1 = true ∧
    withEdgeAdjacency 2 15 1 15 = true ∧
    withEdgeAdjacency 2 15 15 2 = true := by
  decide +kernel

lemma add_two_fifteen_common_neighbors :
    (Finset.univ.filter fun w =>
      withEdgeAdjacency 2 15 2 w = true ∧ withEdgeAdjacency 2 15 1 w = true).card = 2 := by
  decide +kernel

lemma add_two_twelve_cycle :
    ([2, 14, 0, 12] : List (Fin 16)).Nodup ∧
    withEdgeAdjacency 2 12 2 14 = true ∧
    withEdgeAdjacency 2 12 14 0 = true ∧
    withEdgeAdjacency 2 12 0 12 = true ∧
    withEdgeAdjacency 2 12 12 2 = true := by
  decide +kernel

lemma add_two_twelve_common_neighbors :
    (Finset.univ.filter fun w =>
      withEdgeAdjacency 2 12 2 w = true ∧ withEdgeAdjacency 2 12 0 w = true).card = 2 := by
  decide +kernel

end PEqualNP.Outside.L_meta_3566.DoubleLift

namespace PEqualNP.Outside.L_meta_3566.ReaderCut

open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge
  PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma fold_length (gs : List Gate) (w : List Bool) :
    (gs.foldl step w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp only [step, List.length_append, List.length_cons, List.length_nil]
    omega

lemma fold_old (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl step w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [List.foldl_cons, ih (step w g) (by simpa [step] using Nat.lt_succ_of_lt hi)]
    simp [step, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma op_mono (g : Gate) (a b : ℕ → Bool)
    (hop : g.op = GateOp.and ∨ g.op = GateOp.or)
    (h : ∀ i ∈ g.inputs, a i = true → b i = true) :
    g.op.eval (g.inputs.map a) = true → g.op.eval (g.inputs.map b) = true := by
  rcases hop with hop | hop
  · rw [hop]
    simp only [GateOp.eval, List.all_map, Function.comp_def, List.all_eq_true]
    intro ha i hi
    exact h i hi (ha i hi)
  · rw [hop]
    simp only [GateOp.eval, List.any_map, Function.comp_def, List.any_eq_true]
    rintro ⟨i, hi, ha⟩
    exact ⟨i, hi, h i hi ha⟩

lemma fold_cut (gs : List Gate) (a b : List Bool) (v : ℕ)
    (hlen : a.length = b.length)
    (hop : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
    (hinput : ∀ i, i ≠ v → a.getD i false = true → b.getD i false = true)
    (hcut : ∀ j (hj : j < gs.length), v ∈ gs[j].inputs →
      (gs.foldl step a).getD (a.length + j) false = true →
      (gs.foldl step b).getD (b.length + j) false = true) :
    ∀ i, i ≠ v → (gs.foldl step a).getD i false = true →
      (gs.foldl step b).getD i false = true := by
  induction gs generalizing a b with
  | nil => simpa using hinput
  | cons g gs ih =>
    have hfirst : g.op.eval (g.inputs.map fun i => a.getD i false) = true →
        g.op.eval (g.inputs.map fun i => b.getD i false) = true := by
      by_cases hv : v ∈ g.inputs
      · have hc := hcut 0 (by simp) (by simpa using hv)
        simp only [List.foldl_cons, Nat.add_zero] at hc
        rw [fold_old gs (step a g) a.length (by simp [step]),
          fold_old gs (step b g) b.length (by simp [step])] at hc
        simpa [step, List.getD_eq_getElem?_getD] using hc
      · apply op_mono g _ _ (hop g (by simp))
        intro i hi
        exact hinput i (fun he => hv (he ▸ hi))
    apply ih (step a g) (step b g)
    · simp [step, hlen]
    · intro h hh
      exact hop h (by simp [hh])
    · intro i hiv ha
      by_cases hi : i < a.length
      · have hib : i < b.length := by simpa [hlen] using hi
        simpa [step, List.getD_eq_getElem?_getD,
          List.getElem?_append_left hi, List.getElem?_append_left hib] using
          hinput i hiv (by simpa [step, List.getD_eq_getElem?_getD,
            List.getElem?_append_left hi] using ha)
      · by_cases hei : i = a.length
        · subst i
          simpa [step, hlen, List.getD_eq_getElem?_getD] using
            hfirst (by simpa [step, List.getD_eq_getElem?_getD] using ha)
        · have hlarge : (step a g).length ≤ i := by simp [step]; omega
          rw [List.getD_eq_default _ _ hlarge] at ha
          cases ha
    · intro j hj hv
      have hc := hcut (j + 1) (by simp; omega) (by simpa using hv)
      simpa [List.foldl_cons, step, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hc

lemma reader_cut (n : ℕ) (C : Circuit) (v : Fin n) (x y : Fin n → Bool)
    (hops : AndOrOnly C)
    (hinput : ∀ i : Fin n, i ≠ v → x i = true → y i = true)
    (houtput : C.output ≠ v.val)
    (hx : C.eval (List.ofFn x) = true)
    (hy : C.eval (List.ofFn y) = false) :
    ∃ j : Fin C.gates.length, v.val ∈ C.gates[j].inputs ∧
      gateVal n C j.val x = true ∧ gateVal n C j.val y = false := by
  classical
  by_contra hnone
  have hcut : ∀ j (hj : j < C.gates.length), v.val ∈ C.gates[j].inputs →
      gateVal n C j x = true → gateVal n C j y = true := by
    intro j hj hv hxj
    cases hyj : gateVal n C j y with
    | false => exact False.elim (hnone ⟨⟨j, hj⟩, hv, hxj, hyj⟩)
    | true => rfl
  have hle := fold_cut C.gates (List.ofFn x) (List.ofFn y) v.val
    (by simp) hops ?_ ?_ C.output houtput hx
  · change C.eval (List.ofFn y) = true at hle
    rw [hy] at hle
    cases hle
  · intro i hiv hxi
    by_cases hi : i < n
    · simpa [List.getD_eq_getElem?_getD, hi] using
        hinput ⟨i, hi⟩ (fun he => hiv (congrArg Fin.val he))
          (by simpa [List.getD_eq_getElem?_getD, hi] using hxi)
    · rw [List.getD_eq_default _ _ (by simpa using Nat.le_of_not_gt hi)] at hxi
      cases hxi
  · simp only [List.length_ofFn]
    exact hcut

lemma fold_raw_gate (gs : List Gate) (a : List Bool) (j : ℕ) (hj : j < gs.length)
    (u v : ℕ) (hu : u < a.length) (hv : v < a.length)
    (hinputs : gs[j].inputs = [u, v]) :
    (gs.foldl step a).getD (a.length + j) false =
      gs[j].op.eval [a.getD u false, a.getD v false] := by
  induction gs generalizing a j with
  | nil => simp at hj
  | cons g gs ih =>
    cases j with
    | zero =>
      simp only [List.getElem_cons_zero] at hinputs ⊢
      rw [List.foldl_cons, Nat.add_zero,
        fold_old gs (step a g) a.length (by simp [step])]
      simp [step, hinputs, List.getD_eq_getElem?_getD]
    | succ j =>
      have h := ih (step a g) j (by simpa using hj)
        (by simpa [step] using Nat.lt_succ_of_lt hu)
        (by simpa [step] using Nat.lt_succ_of_lt hv) (by simpa using hinputs)
      simpa [List.foldl_cons, step, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm,
        List.getD_eq_getElem?_getD, List.getElem?_append_left hu,
        List.getElem?_append_left hv] using h

lemma raw_gate_value {n : ℕ} (C : Circuit) (j : Fin C.gates.length)
    (u v : Fin n) (hinputs : C.gates[j].inputs = [u.val, v.val])
    (x : Fin n → Bool) :
    gateVal n C j.val x = C.gates[j].op.eval [x u, x v] := by
  have h := fold_raw_gate C.gates (List.ofFn x) j.val j.isLt u.val v.val
    (by simp) (by simp) hinputs
  change (C.gates.foldl step (List.ofFn x)).getD (n + j.val) false = _
  simpa [List.getD_eq_getElem?_getD] using h

lemma raw_gate_value_oriented {n : ℕ} (C : Circuit) (j : Fin C.gates.length)
    (u v : Fin n)
    (hinputs : C.gates[j].inputs = [u.val, v.val] ∨ C.gates[j].inputs = [v.val, u.val])
    (hop : C.gates[j].op = GateOp.and ∨ C.gates[j].op = GateOp.or)
    (x : Fin n → Bool) :
    gateVal n C j.val x = C.gates[j].op.eval [x u, x v] := by
  rcases hinputs with hinputs | hinputs
  · exact raw_gate_value C j u v hinputs x
  · rw [raw_gate_value C j v u hinputs]
    rcases hop with hop | hop <;> rw [hop] <;>
      simp [GateOp.eval, Bool.and_comm, Bool.or_comm]

lemma graph_eval_iff {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hC : circuitFun n C = graphFun G ∅) (x : Fin n → Bool) :
    C.eval (List.ofFn x) = true ↔ ∃ a b, G.Adj a b ∧ x a = true ∧ x b = true := by
  have h := congrFun hC x
  change C.eval (List.ofFn x) = graphFun G ∅ x at h
  rw [h]
  simp [graphFun]

lemma pair_graph_eval {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hC : circuitFun n C = graphFun G ∅) (u v : Fin n) :
    C.eval (List.ofFn (pairInput u v)) = true ↔ G.Adj u v := by
  rw [graph_eval_iff G C hC]
  simp only [pairInput, decide_eq_true_eq]
  constructor
  · rintro ⟨a, b, hab, ha, hb⟩
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · exact False.elim (G.irrefl hab)
    · exact hab
    · exact G.adj_symm hab
    · exact False.elim (G.irrefl hab)
  · intro huv
    exact ⟨u, v, huv, Or.inl rfl, Or.inr rfl⟩

lemma output_ne_primary {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hC : circuitFun n C = graphFun G ∅) (v : Fin n) :
    C.output ≠ v.val := by
  intro he
  have hfalse : C.eval (List.ofFn (pairInput v v)) ≠ true := by
    intro h
    exact G.irrefl ((pair_graph_eval G C hC v v).mp h)
  apply hfalse
  change (C.gates.foldl step (List.ofFn (pairInput v v))).getD C.output false = true
  rw [he, fold_old C.gates _ v.val (by simp)]
  simp [List.getD_eq_getElem?_getD, pairInput]

lemma pair_graph_false {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hC : circuitFun n C = graphFun G ∅) (u v : Fin n)
    (hnot : ¬ G.Adj u v) : C.eval (List.ofFn (pairInput u v)) = false := by
  cases he : C.eval (List.ofFn (pairInput u v)) with
  | false => rfl
  | true => exact False.elim (hnot ((pair_graph_eval G C hC u v).mp he))

lemma raw_sole_and_neighbor {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hAO : IsAO2 n C) (hC : circuitFun n C = graphFun G ∅)
    (j : Fin C.gates.length) (v u : Fin n) (hne : u ≠ v)
    (hinputs : C.gates[j].inputs = [v.val, u.val] ∨ C.gates[j].inputs = [u.val, v.val])
    (hop : C.gates[j].op = GateOp.and)
    (hsole : ∀ k : Fin C.gates.length, v.val ∈ C.gates[k].inputs → k = j)
    (w : Fin n) (hvw : G.Adj v w) : w = u := by
  by_contra hwu
  obtain ⟨k, hk, hkt, hkf⟩ := reader_cut n C v (pairInput v w) (pairInput w w) hAO.1
    (by
      intro i hiv hi
      simp only [pairInput, decide_eq_true_eq] at hi ⊢
      rcases hi with hi | hi
      · exact False.elim (hiv hi)
      · exact Or.inl hi)
    (output_ne_primary G C hC v) ((pair_graph_eval G C hC v w).mpr hvw)
    (pair_graph_false G C hC w w (fun h => G.irrefl h))
  have he := hsole k hk
  subst k
  rw [raw_gate_value_oriented C j v u hinputs (Or.inl hop), hop] at hkt
  simp [GateOp.eval, pairInput, hne, Ne.symm hwu] at hkt

lemma raw_sole_or_neighbor {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hAO : IsAO2 n C) (hC : circuitFun n C = graphFun G ∅)
    (j : Fin C.gates.length) (v u : Fin n)
    (hinputs : C.gates[j].inputs = [v.val, u.val] ∨ C.gates[j].inputs = [u.val, v.val])
    (hop : C.gates[j].op = GateOp.or)
    (hsole : ∀ k : Fin C.gates.length, v.val ∈ C.gates[k].inputs → k = j)
    (w : Fin n) (hvw : G.Adj v w) : G.Adj u w := by
  by_contra huw
  obtain ⟨k, hk, hkt, hkf⟩ := reader_cut n C v (pairInput v w) (pairInput u w) hAO.1
    (by
      intro i hiv hi
      simp only [pairInput, decide_eq_true_eq] at hi ⊢
      rcases hi with hi | hi
      · exact False.elim (hiv hi)
      · exact Or.inr hi)
    (output_ne_primary G C hC v) ((pair_graph_eval G C hC v w).mpr hvw)
    (pair_graph_false G C hC u w huw)
  have he := hsole k hk
  subst k
  rw [raw_gate_value_oriented C j v u hinputs (Or.inr hop), hop] at hkf
  simp [GateOp.eval, pairInput] at hkf

lemma raw_vertex_repeated {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hAO : IsAO2 n C) (hC : circuitFun n C = graphFun G ∅)
    (hfour : NoFourCycle G) (j : Fin C.gates.length) (v u : Fin n)
    (hinputs : C.gates[j].inputs = [v.val, u.val] ∨ C.gates[j].inputs = [u.val, v.val])
    (hdeg : ∃ a b : Fin n, a ≠ b ∧ G.Adj v a ∧ G.Adj v b) :
    v = u ∨ ∃ k : Fin C.gates.length, k ≠ j ∧ v.val ∈ C.gates[k].inputs := by
  classical
  by_cases hvu : v = u
  · exact Or.inl hvu
  right
  by_contra hnone
  have hsole : ∀ k : Fin C.gates.length, v.val ∈ C.gates[k].inputs → k = j := by
    intro k hk
    by_contra hkj
    exact hnone ⟨k, hkj, hk⟩
  obtain ⟨a, b, hab, hva, hvb⟩ := hdeg
  rcases hAO.1 C.gates[j] (List.getElem_mem _) with hand | hor
  · have hau := raw_sole_and_neighbor G C hAO hC j v u (Ne.symm hvu) hinputs hand hsole a hva
    have hbu := raw_sole_and_neighbor G C hAO hC j v u (Ne.symm hvu) hinputs hand hsole b hvb
    exact hab (hau.trans hbu.symm)
  · have hua := raw_sole_or_neighbor G C hAO hC j v u hinputs hor hsole a hva
    have hub := raw_sole_or_neighbor G C hAO hC j v u hinputs hor hsole b hvb
    have hsub : ({a, b} : Finset (Fin n)) ⊆
        Finset.univ.filter (fun w => G.Adj v w ∧ G.Adj u w) := by
      intro w hw
      simp only [Finset.mem_insert, Finset.mem_singleton] at hw
      rcases hw with rfl | rfl <;> simp [hva, hvb, hua, hub]
    have hcard := Finset.card_le_card hsub
    have hbound := hfour v u hvu
    have htwo : ({a, b} : Finset (Fin n)).card = 2 := by simp [hab]
    omega

lemma count_inputs_le (gs : List Gate) (j : ℕ) (hj : j < gs.length) (v : ℕ) :
    gs[j].inputs.count v ≤ (gs.flatMap Gate.inputs).count v := by
  induction gs generalizing j with
  | nil => simp at hj
  | cons g gs ih =>
    cases j with
    | zero => simp
    | succ j =>
      have h := ih j (by simpa using hj)
      simp only [List.getElem_cons_succ, List.flatMap_cons, List.count_append]
      omega

lemma two_reader_count (gs : List Gate) (j k : ℕ)
    (hj : j < gs.length) (hk : k < gs.length) (hjk : j ≠ k) (v : ℕ)
    (hjv : v ∈ gs[j].inputs) (hkv : v ∈ gs[k].inputs) :
    2 ≤ (gs.flatMap Gate.inputs).count v := by
  induction gs generalizing j k with
  | nil => simp at hj
  | cons g gs ih =>
    cases j with
    | zero =>
      cases k with
      | zero => exact False.elim (hjk rfl)
      | succ k =>
        have hkb : k < gs.length := by simpa using hk
        have hp : 0 < g.inputs.count v := List.count_pos_iff.mpr hjv
        have hq : 0 < gs[k].inputs.count v := List.count_pos_iff.mpr hkv
        have hle := count_inputs_le gs k hkb v
        simp only [List.flatMap_cons, List.count_append]
        omega
    | succ j =>
      cases k with
      | zero =>
        have hjb : j < gs.length := by simpa using hj
        have hp : 0 < g.inputs.count v := List.count_pos_iff.mpr hkv
        have hq : 0 < gs[j].inputs.count v := List.count_pos_iff.mpr hjv
        have hle := count_inputs_le gs j hjb v
        simp only [List.flatMap_cons, List.count_append]
        omega
      | succ k =>
        have h := ih j k (by simpa using hj) (by simpa using hk)
          (fun he => hjk (congrArg Nat.succ he)) hjv hkv
        simp only [List.flatMap_cons, List.count_append]
        omega

lemma raw_vertex_occurrences {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hAO : IsAO2 n C) (hC : circuitFun n C = graphFun G ∅)
    (hfour : NoFourCycle G) (j : Fin C.gates.length) (v u : Fin n)
    (hinputs : C.gates[j].inputs = [v.val, u.val] ∨ C.gates[j].inputs = [u.val, v.val])
    (hdeg : ∃ a b : Fin n, a ≠ b ∧ G.Adj v a ∧ G.Adj v b) :
    2 ≤ (C.gates.flatMap Gate.inputs).count v.val := by
  rcases raw_vertex_repeated G C hAO hC hfour j v u hinputs hdeg with he | ⟨k, hkj, hk⟩
  · subst u
    have hi : C.gates[j].inputs = [v.val, v.val] := hinputs.elim id id
    have hi' : C.gates[j.val].inputs = [v.val, v.val] := hi
    have h := count_inputs_le C.gates j.val j.isLt v.val
    rw [hi'] at h
    simpa using h
  · apply two_reader_count C.gates j.val k.val j.isLt k.isLt
      (fun he => hkj (Fin.ext he.symm)) v.val
    · have hm : v.val ∈ C.gates[j].inputs := by
        rcases hinputs with hi | hi <;> rw [hi] <;> simp
      exact hm
    · exact hk

lemma raw_gate_inputs_repeated {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hAO : IsAO2 n C) (hC : circuitFun n C = graphFun G ∅)
    (hfour : NoFourCycle G)
    (hdeg : ∀ v : Fin n, ∃ a b : Fin n, a ≠ b ∧ G.Adj v a ∧ G.Adj v b)
    (j : Fin C.gates.length) (u v : Fin n)
    (hinputs : C.gates[j].inputs = [u.val, v.val]) :
    2 ≤ (C.gates.flatMap Gate.inputs).count u.val ∧
      2 ≤ (C.gates.flatMap Gate.inputs).count v.val := by
  exact ⟨raw_vertex_occurrences G C hAO hC hfour j u v (Or.inl hinputs) (hdeg u),
    raw_vertex_occurrences G C hAO hC hfour j v u (Or.inr hinputs) (hdeg v)⟩

end PEqualNP.Outside.L_meta_3566.ReaderCut

namespace PEqualNP.Outside.L_meta_3566.ReaderCut

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.TopForm

lemma raw_gate_inputs_repeated_of_degree {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit) (hAO : IsAO2 n C)
    (hC : circuitFun n C = graphFun G ∅) (hfour : NoFourCycle G)
    (hdeg : ∀ v : Fin n, 2 ≤ G.degree v)
    (j : Fin C.gates.length) (u v : Fin n)
    (hinputs : C.gates[j].inputs = [u.val, v.val]) :
    2 ≤ (C.gates.flatMap Gate.inputs).count u.val ∧
      2 ≤ (C.gates.flatMap Gate.inputs).count v.val := by
  apply raw_gate_inputs_repeated G C hAO hC hfour ?_ j u v hinputs
  intro w
  have hc : 1 < (G.neighborFinset w).card := by
    rw [G.card_neighborFinset_eq_degree]
    exact Nat.lt_of_lt_of_le (by decide) (hdeg w)
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp hc
  exact ⟨a, b, hab, (G.mem_neighborFinset w a).mp ha, (G.mem_neighborFinset w b).mp hb⟩

end PEqualNP.Outside.L_meta_3566.ReaderCut

namespace PEqualNP.Outside.L_meta_3566.ReaderCut

open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge
  PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm

open scoped BigOperators

lemma input_occurs_of_neighbor {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hAO : IsAO2 n C) (hC : circuitFun n C = graphFun G ∅)
    (v w : Fin n) (hvw : G.Adj v w) :
    1 ≤ (C.gates.flatMap Gate.inputs).count v.val := by
  obtain ⟨j, hj, _, _⟩ := reader_cut n C v (pairInput v w) (pairInput w w) hAO.1
    (by
      intro i hiv hi
      simp only [pairInput, decide_eq_true_eq] at hi ⊢
      rcases hi with hi | hi
      · exact False.elim (hiv hi)
      · exact Or.inl hi)
    (output_ne_primary G C hC v) ((pair_graph_eval G C hC v w).mpr hvw)
    (pair_graph_false G C hC w w (fun h => G.irrefl h))
  have hpos : 0 < C.gates[j].inputs.count v.val := List.count_pos_iff.mpr hj
  have hpos' : 0 < C.gates[j.val].inputs.count v.val := hpos
  have hle := count_inputs_le C.gates j.val j.isLt v.val
  omega

def occurrenceWeight (n : ℕ) (C : Circuit) (i : ℕ) : ℕ :=
  if i < n then if (C.gates.flatMap Gate.inputs).count i = 1 then 2 else 1 else 0

lemma finite_weight_delta (n a : ℕ) (f : ℕ → ℕ) (hz : ∀ i, n ≤ i → f i = 0) :
    (∑ v : Fin n, if a = v.val then f v.val else 0) = f a := by
  classical
  by_cases ha : a < n
  · have heq : ∀ v : Fin n, a = v.val ↔ v = ⟨a, ha⟩ := by
      intro v
      constructor
      · intro he
        exact Fin.ext he.symm
      · intro he
        exact (congrArg Fin.val he).symm
    simp_rw [heq]
    simp
  · rw [hz a (Nat.le_of_not_gt ha)]
    apply Finset.sum_eq_zero
    intro v hv
    have hne : a ≠ v.val := by intro he; exact ha (he ▸ v.isLt)
    simp [hne]

lemma list_weight_count (n : ℕ) (xs : List ℕ) (f : ℕ → ℕ)
    (hz : ∀ i, n ≤ i → f i = 0) :
    (xs.map f).sum = ∑ v : Fin n, xs.count v.val * f v.val := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
    simp only [List.map_cons, List.sum_cons, List.count_cons, Nat.add_mul,
      Finset.sum_add_distrib, beq_iff_eq, ite_mul, one_mul, zero_mul]
    rw [finite_weight_delta n a f hz, ih]
    omega

lemma weighted_gate_sum_bound (gs : List Gate) (f : ℕ → ℕ) (p : Gate → Bool)
    (hg : ∀ g ∈ gs, (g.inputs.map f).sum ≤ if p g then 2 else 0) :
    ((gs.flatMap Gate.inputs).map f).sum ≤ 2 * (gs.filter p).length := by
  induction gs with
  | nil => simp
  | cons g gs ih =>
    have hhead := hg g (by simp)
    have htail := ih (by intro h hh; exact hg h (by simp [hh]))
    simp only [List.flatMap_cons, List.map_append, List.sum_append]
    cases hp : p g <;> simp [hp] at hhead ⊢ <;> omega

def hasPrimaryInput (n : ℕ) (g : Gate) : Bool :=
  g.inputs.any fun i => decide (i < n)

lemma occurrenceWeight_gate {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hAO : IsAO2 n C) (hC : circuitFun n C = graphFun G ∅)
    (hfour : NoFourCycle G)
    (hdeg : ∀ v : Fin n, ∃ a b : Fin n, a ≠ b ∧ G.Adj v a ∧ G.Adj v b)
    (g : Gate) (hg : g ∈ C.gates) :
    (g.inputs.map (occurrenceWeight n C)).sum ≤ if hasPrimaryInput n g then 2 else 0 := by
  obtain ⟨a, b, he⟩ := List.length_eq_two.mp (hAO.2.2 g hg)
  by_cases ha : a < n
  · by_cases hb : b < n
    · obtain ⟨j, hj, hjg⟩ := List.mem_iff_getElem.mp hg
      let ji : Fin C.gates.length := ⟨j, hj⟩
      have hjg' : C.gates[ji] = g := hjg
      have hrep := raw_gate_inputs_repeated G C hAO hC hfour hdeg ji ⟨a, ha⟩ ⟨b, hb⟩
        (by rw [hjg']; exact he)
      have hca : 2 ≤ (C.gates.flatMap Gate.inputs).count a := hrep.1
      have hcb : 2 ≤ (C.gates.flatMap Gate.inputs).count b := hrep.2
      have hna : (C.gates.flatMap Gate.inputs).count a ≠ 1 := by omega
      have hnb : (C.gates.flatMap Gate.inputs).count b ≠ 1 := by omega
      simp [he, occurrenceWeight, hasPrimaryInput, ha, hb, hna, hnb]
    · simp [he, occurrenceWeight, hasPrimaryInput, ha, hb]
      split <;> omega
  · by_cases hb : b < n
    · simp [he, occurrenceWeight, hasPrimaryInput, ha, hb]
      split <;> omega
    · simp [he, occurrenceWeight, hasPrimaryInput, ha, hb]

lemma count_primary_input_gates {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hAO : IsAO2 n C) (hC : circuitFun n C = graphFun G ∅)
    (hfour : NoFourCycle G)
    (hdeg : ∀ v : Fin n, ∃ a b : Fin n, a ≠ b ∧ G.Adj v a ∧ G.Adj v b) :
    n ≤ (C.gates.filter (hasPrimaryInput n)).length := by
  have hz : ∀ i, n ≤ i → occurrenceWeight n C i = 0 := by
    intro i hi
    simp [occurrenceWeight, Nat.not_lt.mpr hi]
  have hweight := list_weight_count n (C.gates.flatMap Gate.inputs) (occurrenceWeight n C) hz
  have hlower : 2 * n ≤ ((C.gates.flatMap Gate.inputs).map (occurrenceWeight n C)).sum := by
    rw [hweight]
    calc
      2 * n = ∑ v : Fin n, 2 := by simp [Nat.mul_comm]
      _ ≤ ∑ v : Fin n, (C.gates.flatMap Gate.inputs).count v.val * occurrenceWeight n C v.val := by
        apply Finset.sum_le_sum
        intro v hv
        obtain ⟨a, b, hab, hva, hvb⟩ := hdeg v
        have hpos := input_occurs_of_neighbor G C hAO hC v a hva
        simp only [occurrenceWeight, v.isLt, ite_true]
        split <;> omega
  have hupper := weighted_gate_sum_bound C.gates (occurrenceWeight n C) (hasPrimaryInput n)
    (fun g hg => occurrenceWeight_gate G C hAO hC hfour hdeg g hg)
  omega

lemma count_primary_input_gates_of_degree {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit) (hAO : IsAO2 n C)
    (hC : circuitFun n C = graphFun G ∅) (hfour : NoFourCycle G)
    (hdeg : ∀ v : Fin n, 2 ≤ G.degree v) :
    n ≤ (C.gates.filter (hasPrimaryInput n)).length := by
  apply count_primary_input_gates G C hAO hC hfour
  intro w
  have hc : 1 < (G.neighborFinset w).card := by
    rw [G.card_neighborFinset_eq_degree]
    exact Nat.lt_of_lt_of_le (by decide) (hdeg w)
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp hc
  exact ⟨a, b, hab, (G.mem_neighborFinset w a).mp ha, (G.mem_neighborFinset w b).mp hb⟩

lemma filter_complement_length {α : Type} (xs : List α) (p : α → Bool) :
    (xs.filter (fun x => !(p x))).length + (xs.filter p).length = xs.length := by
  induction xs with
  | nil => simp
  | cons a xs ih => cases hp : p a <;> simp [hp] at ⊢ <;> omega

lemma count_gate_only_bound {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hAO : IsAO2 n C) (hC : circuitFun n C = graphFun G ∅)
    (hfour : NoFourCycle G) (hdeg : ∀ v : Fin n, 2 ≤ G.degree v) :
    (C.gates.filter (fun g => !(hasPrimaryInput n g))).length ≤ C.size - n := by
  have hbound := count_primary_input_gates_of_degree G C hAO hC hfour hdeg
  have hpartition := filter_complement_length C.gates (hasPrimaryInput n)
  change (C.gates.filter (fun g => !(hasPrimaryInput n g))).length ≤ C.gates.length - n
  omega

end PEqualNP.Outside.L_meta_3566.ReaderCut

namespace PEqualNP.Outside.L_meta_3566.ReaderCut

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.TopForm

open scoped BigOperators

def selectedOccurrenceWeight {n : ℕ} (S : Finset (Fin n)) (C : Circuit) (i : ℕ) : ℕ :=
  if i ∈ S.image Fin.val then if (C.gates.flatMap Gate.inputs).count i = 1 then 2 else 1 else 0

def hasSelectedInput {n : ℕ} (S : Finset (Fin n)) (g : Gate) : Bool :=
  g.inputs.any fun i => decide (i ∈ S.image Fin.val)

lemma selectedOccurrenceWeight_gate {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hAO : IsAO2 n C) (hC : circuitFun n C = graphFun G ∅)
    (hfour : NoFourCycle G) (S : Finset (Fin n))
    (hdeg : ∀ v ∈ S, ∃ a b : Fin n, a ≠ b ∧ G.Adj v a ∧ G.Adj v b)
    (g : Gate) (hg : g ∈ C.gates) :
    (g.inputs.map (selectedOccurrenceWeight S C)).sum ≤
      if hasSelectedInput S g then 2 else 0 := by
  obtain ⟨a, b, he⟩ := List.length_eq_two.mp (hAO.2.2 g hg)
  by_cases ha : a ∈ S.image Fin.val
  · have hs : hasSelectedInput S g = true := by
      simp only [hasSelectedInput, List.any_eq_true, decide_eq_true_eq]
      exact ⟨a, by simp [he], ha⟩
    rw [hs]
    by_cases hb : b ∈ S.image Fin.val
    · obtain ⟨u, hu, hua⟩ := Finset.mem_image.mp ha
      obtain ⟨v, hv, hvb⟩ := Finset.mem_image.mp hb
      subst a
      subst b
      obtain ⟨j, hj, hjg⟩ := List.mem_iff_getElem.mp hg
      let ji : Fin C.gates.length := ⟨j, hj⟩
      have hjg' : C.gates[ji] = g := hjg
      have hi : C.gates[ji].inputs = [u.val, v.val] := by rw [hjg']; exact he
      have hcu := raw_vertex_occurrences G C hAO hC hfour ji u v (Or.inl hi) (hdeg u hu)
      have hcv := raw_vertex_occurrences G C hAO hC hfour ji v u (Or.inr hi) (hdeg v hv)
      have hnu : (C.gates.flatMap Gate.inputs).count u.val ≠ 1 := by omega
      have hnv : (C.gates.flatMap Gate.inputs).count v.val ≠ 1 := by omega
      simp [he, selectedOccurrenceWeight, ha, hb, hnu, hnv]
    · simp [he, selectedOccurrenceWeight, ha, hb]
      split <;> omega
  · by_cases hb : b ∈ S.image Fin.val
    · have hs : hasSelectedInput S g = true := by
        simp only [hasSelectedInput, List.any_eq_true, decide_eq_true_eq]
        exact ⟨b, by simp [he], hb⟩
      rw [hs]
      simp [he, selectedOccurrenceWeight, ha, hb]
      split <;> omega
    · simp [he, selectedOccurrenceWeight, hasSelectedInput, ha, hb]

lemma count_selected_input_gates {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hAO : IsAO2 n C) (hC : circuitFun n C = graphFun G ∅)
    (hfour : NoFourCycle G) (S : Finset (Fin n))
    (hdeg : ∀ v ∈ S, ∃ a b : Fin n, a ≠ b ∧ G.Adj v a ∧ G.Adj v b) :
    S.card ≤ (C.gates.filter (hasSelectedInput S)).length := by
  classical
  have hz : ∀ i, n ≤ i → selectedOccurrenceWeight S C i = 0 := by
    intro i hi
    have hn : i ∉ S.image Fin.val := by
      intro him
      obtain ⟨v, hv, hvi⟩ := Finset.mem_image.mp him
      have hvlt := v.isLt
      omega
    simp [selectedOccurrenceWeight, hn]
  have hweight := list_weight_count n (C.gates.flatMap Gate.inputs)
    (selectedOccurrenceWeight S C) hz
  have hlower : 2 * S.card ≤
      ((C.gates.flatMap Gate.inputs).map (selectedOccurrenceWeight S C)).sum := by
    rw [hweight]
    calc
      2 * S.card = ∑ v ∈ S, 2 := by simp [Nat.mul_comm]
      _ ≤ ∑ v ∈ S, (C.gates.flatMap Gate.inputs).count v.val *
          selectedOccurrenceWeight S C v.val := by
        apply Finset.sum_le_sum
        intro v hv
        obtain ⟨a, b, hab, hva, hvb⟩ := hdeg v hv
        have hpos := input_occurs_of_neighbor G C hAO hC v a hva
        have hvImage : v.val ∈ S.image Fin.val := Finset.mem_image.mpr ⟨v, hv, rfl⟩
        simp only [selectedOccurrenceWeight, hvImage, ite_true]
        split <;> omega
      _ ≤ ∑ v : Fin n, (C.gates.flatMap Gate.inputs).count v.val *
          selectedOccurrenceWeight S C v.val := by
        apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S)
        intro v hv hvS
        exact Nat.zero_le _
  have hupper := weighted_gate_sum_bound C.gates (selectedOccurrenceWeight S C)
    (hasSelectedInput S) (fun g hg => selectedOccurrenceWeight_gate G C hAO hC hfour S hdeg g hg)
  omega

lemma count_selected_input_gates_of_degree {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit) (hAO : IsAO2 n C)
    (hC : circuitFun n C = graphFun G ∅) (hfour : NoFourCycle G) (S : Finset (Fin n))
    (hdeg : ∀ v ∈ S, 2 ≤ G.degree v) :
    S.card ≤ (C.gates.filter (hasSelectedInput S)).length := by
  apply count_selected_input_gates G C hAO hC hfour S
  intro w hw
  have hc : 1 < (G.neighborFinset w).card := by
    rw [G.card_neighborFinset_eq_degree]
    exact Nat.lt_of_lt_of_le (by decide) (hdeg w hw)
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp hc
  exact ⟨a, b, hab, (G.mem_neighborFinset w a).mp ha, (G.mem_neighborFinset w b).mp hb⟩

lemma count_no_selected_input_bound {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit) (hAO : IsAO2 n C)
    (hC : circuitFun n C = graphFun G ∅) (hfour : NoFourCycle G) (S : Finset (Fin n))
    (hdeg : ∀ v ∈ S, 2 ≤ G.degree v) :
    (C.gates.filter (fun g => !(hasSelectedInput S g))).length ≤ C.size - S.card := by
  have hbound := count_selected_input_gates_of_degree G C hAO hC hfour S hdeg
  have hpartition := filter_complement_length C.gates (hasSelectedInput S)
  change (C.gates.filter (fun g => !(hasSelectedInput S g))).length ≤ C.gates.length - S.card
  omega

end PEqualNP.Outside.L_meta_3566.ReaderCut

namespace PEqualNP.Outside.L_meta_3566.ReaderCut

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.TopForm

open scoped BigOperators

lemma count_selected_input_gates_strict_of_three_reads {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit) (hAO : IsAO2 n C)
    (hC : circuitFun n C = graphFun G ∅) (hfour : NoFourCycle G) (S : Finset (Fin n))
    (hdeg : ∀ w ∈ S, 2 ≤ G.degree w) (v : Fin n) (hv : v ∈ S)
    (hthree : 3 ≤ (C.gates.flatMap Gate.inputs).count v.val) :
    S.card + 1 ≤ (C.gates.filter (hasSelectedInput S)).length := by
  classical
  have hneighbors : ∀ w ∈ S, ∃ a b : Fin n, a ≠ b ∧ G.Adj w a ∧ G.Adj w b := by
    intro w hw
    have hc : 1 < (G.neighborFinset w).card := by
      rw [G.card_neighborFinset_eq_degree]
      exact Nat.lt_of_lt_of_le (by decide) (hdeg w hw)
    obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp hc
    exact ⟨a, b, hab, (G.mem_neighborFinset w a).mp ha, (G.mem_neighborFinset w b).mp hb⟩
  have hz : ∀ i, n ≤ i → selectedOccurrenceWeight S C i = 0 := by
    intro i hi
    have hn : i ∉ S.image Fin.val := by
      intro him
      obtain ⟨w, hw, hwi⟩ := Finset.mem_image.mp him
      have hwlt := w.isLt
      omega
    simp [selectedOccurrenceWeight, hn]
  have hweight := list_weight_count n (C.gates.flatMap Gate.inputs)
    (selectedOccurrenceWeight S C) hz
  have hlower : 2 * S.card <
      ((C.gates.flatMap Gate.inputs).map (selectedOccurrenceWeight S C)).sum := by
    rw [hweight]
    calc
      2 * S.card = ∑ w ∈ S, 2 := by simp [Nat.mul_comm]
      _ < ∑ w ∈ S, (C.gates.flatMap Gate.inputs).count w.val *
          selectedOccurrenceWeight S C w.val := by
        apply Finset.sum_lt_sum
        · intro w hw
          obtain ⟨a, b, hab, hwa, hwb⟩ := hneighbors w hw
          have hpos := input_occurs_of_neighbor G C hAO hC w a hwa
          have hwImage : w.val ∈ S.image Fin.val := Finset.mem_image.mpr ⟨w, hw, rfl⟩
          simp only [selectedOccurrenceWeight, hwImage, ite_true]
          split <;> omega
        · refine ⟨v, hv, ?_⟩
          have hvImage : v.val ∈ S.image Fin.val := Finset.mem_image.mpr ⟨v, hv, rfl⟩
          have hne : (C.gates.flatMap Gate.inputs).count v.val ≠ 1 := by omega
          simp only [selectedOccurrenceWeight, hvImage, ite_true, hne, ite_false, mul_one]
          omega
      _ ≤ ∑ w : Fin n, (C.gates.flatMap Gate.inputs).count w.val *
          selectedOccurrenceWeight S C w.val := by
        apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S)
        intro w hw hwS
        exact Nat.zero_le _
  have hupper := weighted_gate_sum_bound C.gates (selectedOccurrenceWeight S C)
    (hasSelectedInput S) (fun g hg =>
      selectedOccurrenceWeight_gate G C hAO hC hfour S hneighbors g hg)
  omega

lemma selected_occurrences_le_two_of_count_eq {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit) (hAO : IsAO2 n C)
    (hC : circuitFun n C = graphFun G ∅) (hfour : NoFourCycle G) (S : Finset (Fin n))
    (hdeg : ∀ w ∈ S, 2 ≤ G.degree w)
    (heq : (C.gates.filter (hasSelectedInput S)).length = S.card) :
    ∀ v ∈ S, (C.gates.flatMap Gate.inputs).count v.val ≤ 2 := by
  intro v hv
  by_contra h
  have hthree : 3 ≤ (C.gates.flatMap Gate.inputs).count v.val := by omega
  have hstrict := count_selected_input_gates_strict_of_three_reads
    G C hAO hC hfour S hdeg v hv hthree
  omega

end PEqualNP.Outside.L_meta_3566.ReaderCut

namespace PEqualNP.Outside.L_meta_3566.ReaderCut

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.TopForm

open scoped BigOperators

lemma weighted_gate_sum_strict_bound (gs : List Gate) (f : ℕ → ℕ) (p : Gate → Bool)
    (hg : ∀ g ∈ gs, (g.inputs.map f).sum ≤ if p g then 2 else 0)
    (g : Gate) (hmem : g ∈ gs)
    (hstrict : (g.inputs.map f).sum < if p g then 2 else 0) :
    ((gs.flatMap Gate.inputs).map f).sum < 2 * (gs.filter p).length := by
  induction gs with
  | nil => simp at hmem
  | cons a gs ih =>
    have hhead := hg a (by simp)
    have htail : ∀ b ∈ gs, (b.inputs.map f).sum ≤ if p b then 2 else 0 := by
      intro b hb
      exact hg b (by simp [hb])
    simp only [List.flatMap_cons, List.map_append, List.sum_append]
    rcases List.mem_cons.mp hmem with he | hmem
    · subst a
      have hbound := weighted_gate_sum_bound gs f p htail
      cases hp : p g <;> simp [hp] at hstrict ⊢
      omega
    · have hbound := ih htail hmem
      cases hp : p a <;> simp [hp] at hhead ⊢ <;> omega

lemma selected_weight_sum_lower {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hAO : IsAO2 n C) (hC : circuitFun n C = graphFun G ∅)
    (S : Finset (Fin n)) (hdeg : ∀ v ∈ S, 2 ≤ G.degree v) :
    2 * S.card ≤
      ((C.gates.flatMap Gate.inputs).map (selectedOccurrenceWeight S C)).sum := by
  classical
  have hz : ∀ i, n ≤ i → selectedOccurrenceWeight S C i = 0 := by
    intro i hi
    have hn : i ∉ S.image Fin.val := by
      intro him
      obtain ⟨v, hv, hvi⟩ := Finset.mem_image.mp him
      have hvlt := v.isLt
      omega
    simp [selectedOccurrenceWeight, hn]
  rw [list_weight_count n (C.gates.flatMap Gate.inputs) (selectedOccurrenceWeight S C) hz]
  calc
    2 * S.card = ∑ v ∈ S, 2 := by simp [Nat.mul_comm]
    _ ≤ ∑ v ∈ S, (C.gates.flatMap Gate.inputs).count v.val *
        selectedOccurrenceWeight S C v.val := by
      apply Finset.sum_le_sum
      intro v hv
      have hc : 1 < (G.neighborFinset v).card := by
        rw [G.card_neighborFinset_eq_degree]
        exact Nat.lt_of_lt_of_le (by decide) (hdeg v hv)
      obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp hc
      have hpos := input_occurs_of_neighbor G C hAO hC v a ((G.mem_neighborFinset v a).mp ha)
      have hvImage : v.val ∈ S.image Fin.val := Finset.mem_image.mpr ⟨v, hv, rfl⟩
      simp only [selectedOccurrenceWeight, hvImage, ite_true]
      split <;> omega
    _ ≤ ∑ v : Fin n, (C.gates.flatMap Gate.inputs).count v.val *
        selectedOccurrenceWeight S C v.val := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S)
      intro v hv hvS
      exact Nat.zero_le _

lemma selected_single_operand_sole_of_count_eq {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit) (hAO : IsAO2 n C)
    (hC : circuitFun n C = graphFun G ∅) (hfour : NoFourCycle G) (S : Finset (Fin n))
    (hdeg : ∀ w ∈ S, 2 ≤ G.degree w)
    (heq : (C.gates.filter (hasSelectedInput S)).length = S.card)
    (g : Gate) (hg : g ∈ C.gates) (v : Fin n) (hv : v ∈ S) (u : ℕ)
    (hu : u ∉ S.image Fin.val)
    (hinputs : g.inputs = [v.val, u] ∨ g.inputs = [u, v.val]) :
    (C.gates.flatMap Gate.inputs).count v.val = 1 := by
  classical
  by_contra hn
  have hneighbors : ∀ w ∈ S, ∃ a b : Fin n, a ≠ b ∧ G.Adj w a ∧ G.Adj w b := by
    intro w hw
    have hc : 1 < (G.neighborFinset w).card := by
      rw [G.card_neighborFinset_eq_degree]
      exact Nat.lt_of_lt_of_le (by decide) (hdeg w hw)
    obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp hc
    exact ⟨a, b, hab, (G.mem_neighborFinset w a).mp ha, (G.mem_neighborFinset w b).mp hb⟩
  have hvImage : v.val ∈ S.image Fin.val := Finset.mem_image.mpr ⟨v, hv, rfl⟩
  have hs : hasSelectedInput S g = true := by
    simp only [hasSelectedInput, List.any_eq_true, decide_eq_true_eq]
    refine ⟨v.val, ?_, hvImage⟩
    rcases hinputs with hi | hi <;> simp [hi]
  have hstrict : (g.inputs.map (selectedOccurrenceWeight S C)).sum <
      if hasSelectedInput S g then 2 else 0 := by
    rw [hs]
    rcases hinputs with hi | hi <;> simp [hi, selectedOccurrenceWeight, hvImage, hu, hn]
  have hupper := weighted_gate_sum_strict_bound C.gates (selectedOccurrenceWeight S C)
    (hasSelectedInput S)
    (fun a ha => selectedOccurrenceWeight_gate G C hAO hC hfour S hneighbors a ha)
    g hg hstrict
  have hlower := selected_weight_sum_lower G C hAO hC S hdeg
  omega

end PEqualNP.Outside.L_meta_3566.ReaderCut

namespace PEqualNP.Outside.L_meta_3566.ReaderCut

open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge
  PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm

lemma fold_mono_values (gs : List Gate) (a b : List Bool)
    (hop : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
    (hlen : a.length = b.length)
    (hinput : ∀ i, a.getD i false = true → b.getD i false = true) :
    ∀ i, (gs.foldl step a).getD i false = true →
      (gs.foldl step b).getD i false = true := by
  induction gs generalizing a b with
  | nil => exact hinput
  | cons g gs ih =>
    apply ih (step a g) (step b g)
    · intro g' hg'
      exact hop g' (by simp [hg'])
    · simp [step, hlen]
    · intro i hi
      by_cases hia : i < a.length
      · have hib : i < b.length := by omega
        simpa [step, List.getD_eq_getElem?_getD,
          List.getElem?_append_left hia, List.getElem?_append_left hib] using
          hinput i (by simpa [step, List.getD_eq_getElem?_getD,
            List.getElem?_append_left hia] using hi)
      · by_cases hei : i = a.length
        · subst i
          have hm := op_mono g (fun i => a.getD i false) (fun i => b.getD i false)
            (hop g (by simp)) (by intro i _; exact hinput i)
          simpa [step, hlen, List.getD_eq_getElem?_getD] using
            hm (by simpa [step, List.getD_eq_getElem?_getD] using hi)
        · have hlarge : (step a g).length ≤ i := by simp [step]; omega
          rw [List.getD_eq_default _ _ hlarge] at hi
          cases hi

lemma wire_mono_values (n : ℕ) (C : Circuit) (hAO : IsAO2 n C)
    (x y : Fin n → Bool) (hxy : ∀ v, x v = true → y v = true) (w : ℕ) :
    wireVal n C w x = true → wireVal n C w y = true := by
  apply fold_mono_values C.gates (List.ofFn x) (List.ofFn y) hAO.1 (by simp)
  intro i hi
  by_cases hin : i < n
  · simpa [List.getD_eq_getElem?_getD, hin] using
      hxy ⟨i, hin⟩ (by simpa [List.getD_eq_getElem?_getD, hin] using hi)
  · rw [List.getD_eq_default _ _ (by simpa using Nat.le_of_not_gt hin)] at hi
    cases hi

lemma fold_all_false (gs : List Gate) (a : List Bool)
    (hop : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
    (hsize : ∀ g ∈ gs, g.inputs.length = 2)
    (ha : ∀ i, a.getD i false = false) :
    ∀ i, (gs.foldl step a).getD i false = false := by
  induction gs generalizing a with
  | nil => exact ha
  | cons g gs ih =>
    apply ih (step a g)
    · intro g' hg'
      exact hop g' (by simp [hg'])
    · intro g' hg'
      exact hsize g' (by simp [hg'])
    · intro i
      obtain ⟨u, v, huv⟩ := List.length_eq_two.mp (hsize g (by simp))
      have hv : g.op.eval (g.inputs.map fun i => a.getD i false) = false := by
        rw [huv]
        simp only [List.map_cons, List.map_nil, ha]
        rcases hop g (by simp) with hh | hh <;> simp [hh, GateOp.eval]
      by_cases hia : i < a.length
      · simpa [step, List.getD_eq_getElem?_getD,
          List.getElem?_append_left hia] using ha i
      · by_cases hei : i = a.length
        · subst i
          simpa [step, List.getD_eq_getElem?_getD] using hv
        · exact List.getD_eq_default _ _ (by simp [step]; omega)

lemma fold_prefix_value (gs : List Gate) (a : List Bool) (j i : ℕ)
    (hi : i < a.length + (gs.take j).length) :
    (gs.foldl step a).getD i false = ((gs.take j).foldl step a).getD i false := by
  conv_lhs => rw [← List.take_append_drop j gs, List.foldl_append]
  exact fold_old (gs.drop j) ((gs.take j).foldl step a) i (by rwa [fold_length])

lemma fold_gate_values (gs : List Gate) (a : List Bool) (j : ℕ) (hj : j < gs.length)
    (hback : ∀ w ∈ gs[j].inputs, w < a.length + j) :
    (gs.foldl step a).getD (a.length + j) false =
      gs[j].op.eval (gs[j].inputs.map fun w => (gs.foldl step a).getD w false) := by
  induction gs generalizing a j with
  | nil => simp at hj
  | cons g gs ih =>
    cases j with
    | zero =>
      simp only [List.getElem_cons_zero, Nat.add_zero] at hback ⊢
      have hmap : g.inputs.map (fun w => ((g :: gs).foldl step a).getD w false) =
          g.inputs.map (fun w => a.getD w false) := by
        apply List.map_congr_left
        intro w hw
        exact fold_old (g :: gs) a w (hback w hw)
      rw [hmap, List.foldl_cons, fold_old gs (step a g) a.length (by simp [step])]
      simp [step, List.getD_eq_getElem?_getD]
    | succ j =>
      have h := ih (step a g) j (by simpa using hj) (by
        intro w hw
        have hh := hback w (by simpa using hw)
        simpa [step, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hh)
      simpa [List.foldl_cons, step, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h

lemma gate_values (n : ℕ) (C : Circuit) (hAO : IsAO2 n C)
    (j : Fin C.gates.length) (x : Fin n → Bool) :
    gateVal n C j.val x = C.gates[j].op.eval
      (C.gates[j].inputs.map fun w => wireVal n C w x) := by
  have hback : ∀ w ∈ C.gates[j.val].inputs, w < (List.ofFn x).length + j.val := by
    intro w hw
    have hh := hAO.2.1 j.val j.isLt w
    simpa [gateAt, List.getD_eq_getElem?_getD, j.isLt] using hh (by
      simpa [gateAt, List.getD_eq_getElem?_getD, j.isLt] using hw)
  change (C.gates.foldl step (List.ofFn x)).getD (n + j.val) false =
    C.gates[j].op.eval (C.gates[j].inputs.map fun w =>
      (C.gates.foldl step (List.ofFn x)).getD w false)
  simpa using
    fold_gate_values C.gates (List.ofFn x) j.val j.isLt hback

lemma wire_primary_value (n : ℕ) (C : Circuit) (v : Fin n) (x : Fin n → Bool) :
    wireVal n C v.val x = x v := by
  change (C.gates.foldl step (List.ofFn x)).getD v.val false = x v
  rw [fold_old C.gates _ v.val (by simp)]
  simp [List.getD_eq_getElem?_getD]

lemma or_gate_wire_value (n : ℕ) (C : Circuit) (hAO : IsAO2 n C)
    (j : Fin C.gates.length) (v : Fin n) (w : ℕ)
    (hop : C.gates[j].op = GateOp.or)
    (hinputs : C.gates[j].inputs = [v.val, w] ∨ C.gates[j].inputs = [w, v.val])
    (x : Fin n → Bool) :
    gateVal n C j.val x = (x v || wireVal n C w x) := by
  rw [gate_values n C hAO j x, hop]
  rcases hinputs with hh | hh <;> rw [hh] <;>
    simp [GateOp.eval, wire_primary_value, Bool.or_comm]

lemma earlier_wire_singleton_of_sole_reader (n : ℕ) (C : Circuit) (hAO : IsAO2 n C)
    (j : Fin C.gates.length) (v : Fin n) (w : ℕ) (hbefore : w < n + j.val)
    (hne : w ≠ v.val)
    (hsole : ∀ k : Fin C.gates.length, v.val ∈ C.gates[k].inputs → k = j) :
    wireVal n C w (pairInput v v) = false := by
  let gs := C.gates.take j.val
  have hlen : gs.length = j.val := by simp [gs]
  have hops : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or := by
    intro g hg
    exact hAO.1 g (List.mem_of_mem_take hg)
  have hzero : ∀ i, (gs.foldl step (List.ofFn (fun _ : Fin n => false))).getD i false = false := by
    apply fold_all_false gs _ hops
    · intro g hg
      exact hAO.2.2 g (List.mem_of_mem_take hg)
    · intro i
      by_cases hi : i < n <;> simp [List.getD_eq_getElem?_getD, hi]
  cases hw : wireVal n C w (pairInput v v) with
  | false => rfl
  | true =>
    have hprefix : (gs.foldl step (List.ofFn (pairInput v v))).getD w false = true := by
      change (C.gates.foldl step (List.ofFn (pairInput v v))).getD w false = true at hw
      rw [fold_prefix_value C.gates _ j.val w (by simpa [hlen] using hbefore)] at hw
      exact hw
    have hh := fold_cut gs (List.ofFn (pairInput v v)) (List.ofFn (fun _ : Fin n => false))
      v.val (by simp) hops ?_ ?_ w hne hprefix
    · rw [hzero] at hh
      cases hh
    · intro i hiv hi
      by_cases hin : i < n
      · have he : (⟨i, hin⟩ : Fin n) = v := by
          simpa [List.getD_eq_getElem?_getD, hin, pairInput] using hi
        exact False.elim (hiv (congrArg Fin.val he))
      · rw [List.getD_eq_default _ _ (by simpa using Nat.le_of_not_gt hin)] at hi
        cases hi
    · intro k hk hv
      have hkj : k < j.val := by simpa [hlen] using hk
      have hkC : k < C.gates.length := Nat.lt_trans hkj j.isLt
      have hmem : v.val ∈ C.gates[k].inputs := by simpa [gs] using hv
      have he := congrArg Fin.val (hsole ⟨k, hkC⟩ hmem)
      change k = j.val at he
      omega

lemma sole_or_sibling_neighbor {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hAO : IsAO2 n C) (hC : circuitFun n C = graphFun G ∅)
    (j : Fin C.gates.length) (v u : Fin n) (sibling : ℕ)
    (hinputs : C.gates[j].inputs = [v.val, sibling] ∨
      C.gates[j].inputs = [sibling, v.val])
    (hop : C.gates[j].op = GateOp.or)
    (hsole : ∀ k : Fin C.gates.length, v.val ∈ C.gates[k].inputs → k = j)
    (hu : wireVal n C sibling (pairInput u u) = true)
    (w : Fin n) (hvw : G.Adj v w) : G.Adj u w := by
  by_contra huw
  obtain ⟨k, hk, hkt, hkf⟩ := reader_cut n C v (pairInput v w) (pairInput u w) hAO.1
    (by
      intro i hiv hi
      simp only [pairInput, decide_eq_true_eq] at hi ⊢
      rcases hi with hi | hi
      · exact False.elim (hiv hi)
      · exact Or.inr hi)
    (output_ne_primary G C hC v) ((pair_graph_eval G C hC v w).mpr hvw)
    (pair_graph_false G C hC u w huw)
  have he := hsole k hk
  subst k
  have hmono := wire_mono_values n C hAO (pairInput u u) (pairInput u w)
    (by intro i hi; simp only [pairInput, decide_eq_true_eq] at hi ⊢; exact Or.inl (hi.elim id id))
    sibling hu
  rw [or_gate_wire_value n C hAO j v sibling hop hinputs] at hkf
  simp [hmono] at hkf

lemma sole_or_sibling_singletons_false {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit) (hAO : IsAO2 n C)
    (hC : circuitFun n C = graphFun G ∅) (hfour : NoFourCycle G)
    (j : Fin C.gates.length) (v : Fin n) (sibling : ℕ) (hne : sibling ≠ v.val)
    (hinputs : C.gates[j].inputs = [v.val, sibling] ∨
      C.gates[j].inputs = [sibling, v.val])
    (hop : C.gates[j].op = GateOp.or)
    (hsole : ∀ k : Fin C.gates.length, v.val ∈ C.gates[k].inputs → k = j)
    (hdeg : ∃ a b : Fin n, a ≠ b ∧ G.Adj v a ∧ G.Adj v b) :
    ∀ u : Fin n, wireVal n C sibling (pairInput u u) = false := by
  intro u
  cases hu : wireVal n C sibling (pairInput u u) with
  | false => rfl
  | true =>
    by_cases huv : u = v
    · subst u
      have hbefore : sibling < n + j.val := by
        apply hAO.2.1 j.val j.isLt sibling
        have hh : sibling ∈ C.gates[j].inputs := by
          rcases hinputs with hh | hh <;> rw [hh] <;> simp
        simpa [gateAt, List.getD_eq_getElem?_getD, j.isLt] using hh
      have hh := earlier_wire_singleton_of_sole_reader n C hAO j v sibling hbefore hne hsole
      rw [hh] at hu
      cases hu
    · obtain ⟨a, b, hab, hva, hvb⟩ := hdeg
      have hua := sole_or_sibling_neighbor G C hAO hC j v u sibling hinputs hop hsole hu a hva
      have hub := sole_or_sibling_neighbor G C hAO hC j v u sibling hinputs hop hsole hu b hvb
      have hsub : ({a, b} : Finset (Fin n)) ⊆
          Finset.univ.filter (fun w => G.Adj v w ∧ G.Adj u w) := by
        intro w hw
        simp only [Finset.mem_insert, Finset.mem_singleton] at hw
        rcases hw with rfl | rfl <;> simp [hva, hvb, hua, hub]
      have hcard := Finset.card_le_card hsub
      have hbound := hfour v u (Ne.symm huv)
      have htwo : ({a, b} : Finset (Fin n)).card = 2 := by simp [hab]
      omega

end PEqualNP.Outside.L_meta_3566.ReaderCut

namespace PEqualNP.Outside.L_meta_3566.ReaderCut

open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge
  PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm

open scoped BigOperators

lemma sole_or_sibling_support_dominates {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit) (hAO : IsAO2 n C)
    (hC : circuitFun n C = graphFun G ∅)
    (j : Fin C.gates.length) (v : Fin n) (sibling : ℕ)
    (hinputs : C.gates[j].inputs = [v.val, sibling] ∨
      C.gates[j].inputs = [sibling, v.val])
    (hop : C.gates[j].op = GateOp.or)
    (hsole : ∀ k : Fin C.gates.length, v.val ∈ C.gates[k].inputs → k = j)
    (S : Finset (Fin n)) (hInd : ∀ a ∈ S, ∀ b ∈ S, ¬ G.Adj a b)
    (hS : wireVal n C sibling (fun u => decide (u ∈ S)) = true)
    (w : Fin n) (hvw : G.Adj v w) : ∃ u ∈ S, G.Adj u w := by
  classical
  by_contra hnone
  let y : Fin n → Bool := fun u => decide (u ∈ S ∨ u = w)
  have hy : C.eval (List.ofFn y) = false := by
    cases hh : C.eval (List.ofFn y) with
    | false => rfl
    | true =>
      obtain ⟨a, b, hab, ha, hb⟩ := (graph_eval_iff G C hC y).mp hh
      simp only [y, decide_eq_true_eq] at ha hb
      rcases ha with ha | rfl <;> rcases hb with hb | rfl
      · exact False.elim (hInd a ha b hb hab)
      · exact False.elim (hnone ⟨a, ha, hab⟩)
      · exact False.elim (hnone ⟨b, hb, G.adj_symm hab⟩)
      · exact False.elim (G.irrefl hab)
  obtain ⟨k, hk, hkt, hkf⟩ := reader_cut n C v (pairInput v w) y hAO.1
    (by
      intro u huv hu
      simp only [pairInput, decide_eq_true_eq] at hu
      simp only [y, decide_eq_true_eq]
      rcases hu with hu | hu
      · exact False.elim (huv hu)
      · exact Or.inr hu)
    (output_ne_primary G C hC v) ((pair_graph_eval G C hC v w).mpr hvw) hy
  have he := hsole k hk
  subst k
  have hmono := wire_mono_values n C hAO (fun u => decide (u ∈ S)) y
    (by intro u hu; simp only [decide_eq_true_eq] at hu; exact decide_eq_true (Or.inl hu))
    sibling hS
  rw [or_gate_wire_value n C hAO j v sibling hop hinputs] at hkf
  simp [hmono] at hkf

lemma sole_or_sibling_independent_support_bound {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit) (hAO : IsAO2 n C)
    (hC : circuitFun n C = graphFun G ∅) (hfour : NoFourCycle G)
    (j : Fin C.gates.length) (v : Fin n) (sibling : ℕ)
    (hinputs : C.gates[j].inputs = [v.val, sibling] ∨
      C.gates[j].inputs = [sibling, v.val])
    (hop : C.gates[j].op = GateOp.or)
    (hsole : ∀ k : Fin C.gates.length, v.val ∈ C.gates[k].inputs → k = j)
    (S : Finset (Fin n)) (hInd : ∀ a ∈ S, ∀ b ∈ S, ¬ G.Adj a b)
    (hvS : v ∉ S) (hS : wireVal n C sibling (fun u => decide (u ∈ S)) = true) :
    G.degree v ≤ S.card := by
  classical
  let common : Fin n → Finset (Fin n) := fun u =>
    Finset.univ.filter (fun w => G.Adj v w ∧ G.Adj u w)
  have hsub : G.neighborFinset v ⊆ S.biUnion common := by
    intro w hw
    have hvw := (G.mem_neighborFinset v w).mp hw
    obtain ⟨u, hu, huw⟩ := sole_or_sibling_support_dominates G C hAO hC
      j v sibling hinputs hop hsole S hInd hS w hvw
    exact Finset.mem_biUnion.mpr ⟨u, hu, by simp [common, hvw, huw]⟩
  calc
    G.degree v = (G.neighborFinset v).card := (G.card_neighborFinset_eq_degree v).symm
    _ ≤ (S.biUnion common).card := Finset.card_le_card hsub
    _ ≤ ∑ u ∈ S, (common u).card := Finset.card_biUnion_le
    _ ≤ ∑ _u ∈ S, 1 := by
      apply Finset.sum_le_sum
      intro u hu
      exact hfour v u (fun he => hvS (he ▸ hu))
    _ = S.card := by simp

end PEqualNP.Outside.L_meta_3566.ReaderCut

namespace PEqualNP.Outside.L_meta_3566.ReaderCut

open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge
  PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm

lemma earlier_wire_mono_of_sole_reader (n : ℕ) (C : Circuit) (hAO : IsAO2 n C)
    (j : Fin C.gates.length) (v : Fin n) (w : ℕ) (hbefore : w < n + j.val)
    (hne : w ≠ v.val)
    (hsole : ∀ k : Fin C.gates.length, v.val ∈ C.gates[k].inputs → k = j)
    (x y : Fin n → Bool) (hxy : ∀ u, u ≠ v → x u = true → y u = true) :
    wireVal n C w x = true → wireVal n C w y = true := by
  let gs := C.gates.take j.val
  have hlen : gs.length = j.val := by simp [gs]
  intro hx
  change (C.gates.foldl step (List.ofFn x)).getD w false = true at hx
  change (C.gates.foldl step (List.ofFn y)).getD w false = true
  rw [fold_prefix_value C.gates _ j.val w (by simpa [hlen] using hbefore)] at hx ⊢
  apply fold_cut gs (List.ofFn x) (List.ofFn y) v.val (by simp) ?_ ?_ ?_ w hne hx
  · intro g hg
    exact hAO.1 g (List.mem_of_mem_take hg)
  · intro i hiv hi
    by_cases hin : i < n
    · simpa [List.getD_eq_getElem?_getD, hin] using hxy ⟨i, hin⟩
        (fun hh => hiv (congrArg Fin.val hh))
        (by simpa [List.getD_eq_getElem?_getD, hin] using hi)
    · rw [List.getD_eq_default _ _ (by simpa using Nat.le_of_not_gt hin)] at hi
      cases hi
  · intro k hk hv
    have hkj : k < j.val := by simpa [hlen] using hk
    have hkC : k < C.gates.length := Nat.lt_trans hkj j.isLt
    have hmem : v.val ∈ C.gates[k].inputs := by simpa [gs] using hv
    have he := congrArg Fin.val (hsole ⟨k, hkC⟩ hmem)
    change k = j.val at he
    omega

lemma sibling_reads_back (n : ℕ) (C : Circuit) (hAO : IsAO2 n C)
    (j : Fin C.gates.length) (v : Fin n) (sibling : ℕ)
    (hinputs : C.gates[j].inputs = [v.val, sibling] ∨
      C.gates[j].inputs = [sibling, v.val]) : sibling < n + j.val := by
  apply hAO.2.1 j.val j.isLt sibling
  have hh : sibling ∈ C.gates[j].inputs := by
    rcases hinputs with hh | hh <;> rw [hh] <;> simp
  simpa [gateAt, List.getD_eq_getElem?_getD, j.isLt] using hh

lemma and_gate_wire_value (n : ℕ) (C : Circuit) (hAO : IsAO2 n C)
    (j : Fin C.gates.length) (v : Fin n) (w : ℕ)
    (hop : C.gates[j].op = GateOp.and)
    (hinputs : C.gates[j].inputs = [v.val, w] ∨ C.gates[j].inputs = [w, v.val])
    (x : Fin n → Bool) :
    gateVal n C j.val x = (x v && wireVal n C w x) := by
  rw [gate_values n C hAO j x, hop]
  rcases hinputs with hh | hh <;> rw [hh] <;>
    simp [GateOp.eval, wire_primary_value, Bool.and_comm]

lemma sole_and_sibling_neighbor_singleton {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit) (hAO : IsAO2 n C)
    (hC : circuitFun n C = graphFun G ∅)
    (j : Fin C.gates.length) (v : Fin n) (sibling : ℕ) (hne : sibling ≠ v.val)
    (hinputs : C.gates[j].inputs = [v.val, sibling] ∨
      C.gates[j].inputs = [sibling, v.val])
    (hop : C.gates[j].op = GateOp.and)
    (hsole : ∀ k : Fin C.gates.length, v.val ∈ C.gates[k].inputs → k = j)
    (w : Fin n) (hvw : G.Adj v w) :
    wireVal n C sibling (pairInput w w) = true := by
  obtain ⟨k, hk, hkt, hkf⟩ := reader_cut n C v (pairInput v w) (pairInput w w) hAO.1
    (by
      intro u huv hu
      simp only [pairInput, decide_eq_true_eq] at hu ⊢
      rcases hu with hu | hu
      · exact False.elim (huv hu)
      · exact Or.inl hu)
    (output_ne_primary G C hC v) ((pair_graph_eval G C hC v w).mpr hvw)
    (pair_graph_false G C hC w w (fun hh => G.irrefl hh))
  have he := hsole k hk
  subst k
  have hpair : wireVal n C sibling (pairInput v w) = true := by
    rw [and_gate_wire_value n C hAO j v sibling hop hinputs] at hkt
    exact (Bool.and_eq_true_iff.mp hkt).2
  apply earlier_wire_mono_of_sole_reader n C hAO j v sibling
    (sibling_reads_back n C hAO j v sibling hinputs) hne hsole
    (pairInput v w) (pairInput w w) ?_ hpair
  intro u huv hu
  simp only [pairInput, decide_eq_true_eq] at hu ⊢
  rcases hu with hu | hu
  · exact False.elim (huv hu)
  · exact Or.inl hu

lemma sole_or_sibling_erased_support_bound {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit) (hAO : IsAO2 n C)
    (hC : circuitFun n C = graphFun G ∅) (hfour : NoFourCycle G)
    (j : Fin C.gates.length) (v : Fin n) (sibling : ℕ) (hne : sibling ≠ v.val)
    (hinputs : C.gates[j].inputs = [v.val, sibling] ∨
      C.gates[j].inputs = [sibling, v.val])
    (hop : C.gates[j].op = GateOp.or)
    (hsole : ∀ k : Fin C.gates.length, v.val ∈ C.gates[k].inputs → k = j)
    (S : Finset (Fin n)) (hInd : ∀ a ∈ S, ∀ b ∈ S, ¬ G.Adj a b)
    (hS : wireVal n C sibling (fun u => decide (u ∈ S)) = true) :
    G.degree v ≤ (S.erase v).card := by
  have hErase : wireVal n C sibling (fun u => decide (u ∈ S.erase v)) = true := by
    apply earlier_wire_mono_of_sole_reader n C hAO j v sibling
      (sibling_reads_back n C hAO j v sibling hinputs) hne hsole
      (fun u => decide (u ∈ S)) (fun u => decide (u ∈ S.erase v)) ?_ hS
    intro u huv hu
    simpa [Finset.mem_erase, huv] using hu
  apply sole_or_sibling_independent_support_bound G C hAO hC hfour
    j v sibling hinputs hop hsole (S.erase v) ?_ (by simp) hErase
  intro a ha b hb
  exact hInd a (Finset.mem_of_mem_erase ha) b (Finset.mem_of_mem_erase hb)

end PEqualNP.Outside.L_meta_3566.ReaderCut

namespace PEqualNP.Outside.L_meta_3566.ReaderCut

open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge
  PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm

lemma sole_or_sibling_nonedge_pairs_false {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit) (hAO : IsAO2 n C)
    (hC : circuitFun n C = graphFun G ∅) (hfour : NoFourCycle G)
    (j : Fin C.gates.length) (v : Fin n) (sibling : ℕ) (hne : sibling ≠ v.val)
    (hinputs : C.gates[j].inputs = [v.val, sibling] ∨
      C.gates[j].inputs = [sibling, v.val])
    (hop : C.gates[j].op = GateOp.or)
    (hsole : ∀ k : Fin C.gates.length, v.val ∈ C.gates[k].inputs → k = j)
    (hdeg : 3 ≤ G.degree v) (a b : Fin n) (hab : ¬ G.Adj a b) :
    wireVal n C sibling (pairInput a b) = false := by
  cases hh : wireVal n C sibling (pairInput a b) with
  | false => rfl
  | true =>
    have hInd : ∀ u ∈ ({a, b} : Finset (Fin n)),
        ∀ w ∈ ({a, b} : Finset (Fin n)), ¬ G.Adj u w := by
      intro u hu w hw huw
      simp only [Finset.mem_insert, Finset.mem_singleton] at hu hw
      rcases hu with rfl | rfl <;> rcases hw with rfl | rfl
      · exact G.irrefl huw
      · exact hab huw
      · exact hab (G.adj_symm huw)
      · exact G.irrefl huw
    have hS : wireVal n C sibling
        (fun u => decide (u ∈ ({a, b} : Finset (Fin n)))) = true := by
      simp only [Finset.mem_insert, Finset.mem_singleton]
      exact hh
    have hbound := sole_or_sibling_erased_support_bound G C hAO hC hfour
      j v sibling hne hinputs hop hsole {a, b} hInd hS
    have herase := Finset.card_le_card (Finset.erase_subset v ({a, b} : Finset (Fin n)))
    have htwo : ({a, b} : Finset (Fin n)).card ≤ 2 := by
      by_cases he : a = b
      · subst b
        simp
      · simp [he]
    omega

end PEqualNP.Outside.L_meta_3566.ReaderCut
