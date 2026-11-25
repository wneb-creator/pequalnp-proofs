import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_5012

namespace Lift

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm PEqualNP.Core PEqualNP.ReadTwo

lemma foldl_wires_len (gs : List Gate) (acc : List Bool) :
    (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) acc).length =
      acc.length + gs.length := by
  induction gs generalizing acc with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, ih, List.length_append, List.length_cons, List.length_nil]
    omega

lemma foldl_wires_getD_lt (gs : List Gate) (acc : List Bool) (i : ℕ) (hi : i < acc.length) :
    (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun k => w.getD k false)]) acc).getD i false =
      acc.getD i false := by
  induction gs generalizing acc with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hlt : i < (acc ++ [g.op.eval (g.inputs.map fun k => acc.getD k false)]).length := by
      simp only [List.length_append, List.length_singleton]; omega
    rw [ih _ hlt]
    simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma foldl_wires_getD_gate (gs : List Gate) (acc : List Bool) (j : ℕ) (hj : j < gs.length)
    (hback : ∀ k ∈ gs[j].inputs, k < acc.length + j) :
    (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun k => w.getD k false)]) acc).getD
        (acc.length + j) false =
      gs[j].op.eval (gs[j].inputs.map fun k =>
        (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun m => w.getD m false)]) acc).getD
          k false) := by
  induction gs generalizing acc j with
  | nil => cases hj
  | cons g gs ih =>
    cases j with
    | zero =>
      simp only [Nat.add_zero, List.foldl_cons, List.getElem_cons_zero] at hback ⊢
      set acc' := acc ++ [g.op.eval (g.inputs.map fun k => acc.getD k false)]
      have hlen : acc.length < acc'.length := by
        simp only [acc', List.length_append, List.length_singleton]; omega
      rw [foldl_wires_getD_lt gs acc' acc.length hlen]
      have hlhs : acc'.getD acc.length false = g.op.eval (g.inputs.map fun k => acc.getD k false) := by
        simp only [acc', List.getD_eq_getElem?_getD, List.getElem?_append_right (le_refl _),
          Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]
      rw [hlhs]
      congr 1
      apply List.map_congr_left
      intro k hk
      have hka : k < acc.length := hback k hk
      have hka' : k < acc'.length := by omega
      rw [foldl_wires_getD_lt gs acc' k hka']
      simp only [acc', List.getD_eq_getElem?_getD, List.getElem?_append_left hka]
    | succ j' =>
      simp only [List.foldl_cons, List.getElem_cons_succ]
      set acc' := acc ++ [g.op.eval (g.inputs.map fun k => acc.getD k false)]
      have hlen' : acc'.length = acc.length + 1 := by
        simp only [acc', List.length_append, List.length_singleton]
      have hj' : j' < gs.length := by simp only [List.length_cons] at hj; omega
      have hidx : acc.length + (j' + 1) = acc'.length + j' := by omega
      rw [hidx]
      apply ih acc' j' hj'
      intro k hk
      have hbk := hback k (by simpa using hk)
      omega

lemma wires_length (C : Circuit) (x : List Bool) :
    (C.wires x).length = x.length + C.gates.length :=
  foldl_wires_len C.gates x

lemma wval_input {n : ℕ} (C : Circuit) (x : Fin n → Bool) (i : ℕ) (hi : i < n) :
    wval C x i = x ⟨i, hi⟩ := by
  unfold wval Circuit.wires
  have hlt : i < (List.ofFn x).length := by simp [hi]
  rw [foldl_wires_getD_lt C.gates (List.ofFn x) i hlt]
  simp [List.getD_eq_getElem?_getD, hi]

lemma gateVal_eq_wval {n : ℕ} (C : Circuit) (j : ℕ) (x : Fin n → Bool) :
    gateVal n C j x = wval C x (n + j) := rfl

lemma wval_ge_len {n : ℕ} (C : Circuit) (x : Fin n → Bool) {w : ℕ} (hw : n + C.gates.length ≤ w) :
    wval C x w = false := by
  unfold wval
  rw [List.getD_eq_getElem?_getD]
  have hlen : (C.wires (List.ofFn x)).length = n + C.gates.length := by
    rw [wires_length, List.length_ofFn]
  rw [List.getElem?_eq_none (by omega)]
  rfl

lemma gateAt_eq {C : Circuit} {j : ℕ} (hj : j < C.gates.length) :
    gateAt C j = C.gates[j] := by
  unfold gateAt
  simp [List.getD_eq_getElem?_getD, hj]

lemma gateAt_mem {C : Circuit} {j : ℕ} (hj : j < C.gates.length) :
    gateAt C j ∈ C.gates := by
  rw [gateAt_eq hj]; exact List.getElem_mem hj

lemma gate_inputs_eq {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) {j : ℕ} (hj : j < C.gates.length) :
    (gateAt C j).inputs = [opnd C j 0, opnd C j 1] := by
  have hlen : (gateAt C j).inputs.length = 2 := hAO.2.2 _ (gateAt_mem hj)
  unfold opnd
  match h : (gateAt C j).inputs with
  | [a, b] => simp
  | [] => rw [h] at hlen; simp at hlen
  | [_] => rw [h] at hlen; simp at hlen
  | _ :: _ :: _ :: _ => rw [h] at hlen; simp at hlen

lemma opnd_mem {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) {j : ℕ} (hj : j < C.gates.length) (b : Fin 2) :
    opnd C j b ∈ (gateAt C j).inputs := by
  rw [gate_inputs_eq hAO hj]
  fin_cases b <;> simp

lemma opnd_lt {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) {j : ℕ} (hj : j < C.gates.length) (b : Fin 2) :
    opnd C j b < n + j :=
  hAO.2.1 j hj _ (opnd_mem hAO hj b)

lemma wval_gate_eval {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) (x : Fin n → Bool)
    {j : ℕ} (hj : j < C.gates.length) :
    wval C x (n + j) = (gateAt C j).op.eval [wval C x (opnd C j 0), wval C x (opnd C j 1)] := by
  unfold wval Circuit.wires
  have hlen : (List.ofFn x).length = n := List.length_ofFn
  have hback : ∀ k ∈ C.gates[j].inputs, k < (List.ofFn x).length + j := by
    intro k hk; rw [hlen, ← gateAt_eq hj] at *; exact hAO.2.1 j hj k hk
  have h := foldl_wires_getD_gate C.gates (List.ofFn x) j hj hback
  rw [hlen] at h
  rw [h, ← gateAt_eq hj, gate_inputs_eq hAO hj]
  simp

lemma wval_gate_and {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) (x : Fin n → Bool)
    {j : ℕ} (hj : j < C.gates.length) (hop : (gateAt C j).op = GateOp.and) :
    wval C x (n + j) = (wval C x (opnd C j 0) && wval C x (opnd C j 1)) := by
  rw [wval_gate_eval hAO x hj, hop]; simp [GateOp.eval]

lemma wval_gate_or {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) (x : Fin n → Bool)
    {j : ℕ} (hj : j < C.gates.length) (hop : (gateAt C j).op = GateOp.or) :
    wval C x (n + j) = (wval C x (opnd C j 0) || wval C x (opnd C j 1)) := by
  rw [wval_gate_eval hAO x hj, hop]; simp [GateOp.eval]

lemma foldl_cones_len (n : ℕ) (gs : List Gate) (acc : List (List ℕ)) :
    (gs.foldl (coneStep n) acc).length = acc.length + gs.length := by
  induction gs generalizing acc with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, ih, coneStep, List.length_append, List.length_cons, List.length_nil]
    omega

lemma foldl_cones_getD_lt (n : ℕ) (gs : List Gate) (acc : List (List ℕ)) (i : ℕ) (hi : i < acc.length) :
    (gs.foldl (coneStep n) acc).getD i [] = acc.getD i [] := by
  induction gs generalizing acc with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hlt : i < (coneStep n acc g).length := by
      simp only [coneStep, List.length_append, List.length_singleton]; omega
    rw [ih _ hlt]
    simp only [coneStep, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma cones_length (n : ℕ) (C : Circuit) : (cones n C).length = C.gates.length := by
  unfold cones; rw [foldl_cones_len]; simp

lemma foldl_cones_getD_gate (n : ℕ) (gs : List Gate) (acc : List (List ℕ)) (j : ℕ) (hj : j < gs.length) :
    (gs.foldl (coneStep n) acc).getD (acc.length + j) [] =
      (gs[j].inputs.filter (fun w => decide (n ≤ w ∧ w < n + (acc.length + j)))).flatMap
        (fun w => (w - n) :: (gs.foldl (coneStep n) acc).getD (w - n) []) := by
  induction gs generalizing acc j with
  | nil => cases hj
  | cons g gs ih =>
    cases j with
    | zero =>
      simp only [Nat.add_zero, List.foldl_cons, List.getElem_cons_zero]
      set acc' := coneStep n acc g
      have hlen : acc.length < acc'.length := by
        simp only [acc', coneStep, List.length_append, List.length_singleton]; omega
      rw [foldl_cones_getD_lt n gs acc' acc.length hlen]
      have hlhs : acc'.getD acc.length [] =
          (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + acc.length))).flatMap
            (fun w => (w - n) :: acc.getD (w - n) []) := by
        simp only [acc', coneStep, List.getD_eq_getElem?_getD, List.getElem?_append_right (le_refl _),
          Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]
      rw [hlhs]
      apply List.flatMap_congr
      intro w hw
      simp only [List.mem_filter, decide_eq_true_eq] at hw
      have hwn : w - n < acc.length := by omega
      have hwn' : w - n < acc'.length := by omega
      rw [foldl_cones_getD_lt n gs acc' (w - n) hwn']
      simp only [acc', coneStep, List.getD_eq_getElem?_getD, List.getElem?_append_left hwn]
    | succ j' =>
      simp only [List.foldl_cons, List.getElem_cons_succ]
      set acc' := coneStep n acc g
      have hlen' : acc'.length = acc.length + 1 := by
        simp only [acc', coneStep, List.length_append, List.length_singleton]
      have hj' : j' < gs.length := by simp only [List.length_cons] at hj; omega
      have hidx : acc.length + (j' + 1) = acc'.length + j' := by omega
      rw [hidx]
      exact ih acc' j' hj'

lemma inCone_lt_len {n : ℕ} {C : Circuit} {i j : ℕ} (h : InCone n C i j) : j < C.gates.length := by
  by_contra hge
  unfold InCone at h
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by rw [cones_length]; omega)] at h
  simp at h

lemma inCone_iff {n : ℕ} {C : Circuit} {i j : ℕ} (hj : j < C.gates.length) :
    InCone n C i j ↔
      ∃ w ∈ (gateAt C j).inputs, n ≤ w ∧ w < n + j ∧ (i = w - n ∨ InCone n C i (w - n)) := by
  unfold InCone cones
  have h := foldl_cones_getD_gate n C.gates [] j hj
  simp only [List.length_nil, Nat.zero_add] at h
  rw [h, ← gateAt_eq hj]
  simp only [List.mem_flatMap, List.mem_filter, decide_eq_true_eq, List.mem_cons]
  constructor
  · rintro ⟨w, ⟨hw1, hw2, hw3⟩, hw4⟩; exact ⟨w, hw1, hw2, hw3, hw4⟩
  · rintro ⟨w, hw1, hw2, hw3, hw4⟩; exact ⟨w, ⟨hw1, hw2, hw3⟩, hw4⟩

lemma inCone_lt {n : ℕ} {C : Circuit} {i j : ℕ} : InCone n C i j → i < j := by
  induction j using Nat.strong_induction_on with
  | ind j ih =>
    intro h
    have hj := inCone_lt_len h
    rw [inCone_iff hj] at h
    rcases h with ⟨w, _, hnw, hwnj, rfl | hsub⟩
    · omega
    · have := ih (w - n) (by omega) hsub; omega

lemma inCone_trans {n : ℕ} {C : Circuit} {i j k : ℕ} (h1 : InCone n C i j) (h2 : InCone n C j k) :
    InCone n C i k := by
  induction k using Nat.strong_induction_on with
  | ind k ih =>
    have hk := inCone_lt_len h2
    rw [inCone_iff hk] at h2 ⊢
    rcases h2 with ⟨w, hw, hnw, hwnk, rfl | hsub⟩
    · exact ⟨w, hw, hnw, hwnk, Or.inr h1⟩
    · exact ⟨w, hw, hnw, hwnk, Or.inr (ih (w - n) (by omega) hsub)⟩

lemma graphFun_iff {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] (x : Fin n → Bool) :
    graphFun G ∅ x = true ↔ ∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true := by
  unfold graphFun; simp

lemma graphFun_unit_false {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (v : Fin n) :
    graphFun G ∅ (fun w => decide (w = v)) = false := by
  rw [Bool.eq_false_iff, ne_eq, graphFun_iff]
  rintro ⟨a, b, hab, ha, hb⟩
  simp only [decide_eq_true_eq] at ha hb
  subst ha; subst hb
  exact G.loopless.irrefl _ hab

lemma input_not_belowF {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}
    {w : ℕ} (hw : w < n) :
    ¬ ∀ x : Fin n → Bool, wval C x w = true → graphFun G ∅ x = true := by
  intro h
  have := h (fun i => decide (i = ⟨w, hw⟩)) (by rw [wval_input C _ w hw]; simp)
  rw [graphFun_unit_false] at this
  cases this

lemma below_wire_contains_top {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {C : Circuit} (hAO : IsAO2 n C) (w : ℕ) (hw : w < n + C.gates.length)
    (hb : ∀ x : Fin n → Bool, wval C x w = true → graphFun G ∅ x = true) :
    ∃ r, r < C.gates.length ∧ (gateAt C r).op = GateOp.and ∧ BelowF G C r ∧
      (r = w - n ∨ InCone n C r (w - n)) := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    have hn : n ≤ w := by
      by_contra h
      exact input_not_belowF (by omega : w < n) hb
    obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hn
    have hj : j < C.gates.length := by omega
    have hjb : BelowF G C j := hb
    rcases hAO.1 _ (gateAt_mem hj) with hand | hor
    · exact ⟨j, hj, hand, hjb, Or.inl (by omega)⟩
    · have hwb : ∀ x : Fin n → Bool, wval C x (opnd C j 0) = true → graphFun G ∅ x = true := by
        intro x hx
        apply hjb x
        rw [gateVal_eq_wval, wval_gate_or hAO x hj hor, Bool.or_eq_true]
        exact Or.inl hx
      have hlt := opnd_lt hAO hj 0
      have hn0 : n ≤ opnd C j 0 := by
        by_contra h
        exact input_not_belowF (by omega : opnd C j 0 < n) hwb
      obtain ⟨r, hr, hro, hrb, hrc⟩ := ih (opnd C j 0) hlt (by omega) hwb
      refine ⟨r, hr, hro, hrb, Or.inr ?_⟩
      simp only [Nat.add_sub_cancel_left]
      exact (inCone_iff hj).mpr ⟨opnd C j 0, opnd_mem hAO hj 0, hn0, hlt, hrc⟩

lemma cone_propagates_through_or {n : ℕ} {C : Circuit} (hAO : IsAO2 n C)
    {i j : ℕ} (hcone : InCone n C i j)
    (hor : ∀ k, InCone n C i k → (gateAt C k).op = GateOp.or)
    (x : Fin n → Bool) (hi : gateVal n C i x = true) : gateVal n C j x = true := by
  induction j using Nat.strong_induction_on with
  | ind j ih =>
    have hj := inCone_lt_len hcone
    have hop := hor j hcone
    obtain ⟨w, hw, hnw, hwj, hsub⟩ := (inCone_iff hj).mp hcone
    have hwv : wval C x w = true := by
      rcases hsub with he | hsub
      · rw [he, gateVal_eq_wval, Nat.add_sub_of_le hnw] at hi
        exact hi
      · have hg := ih (w - n) (by omega) hsub
        rw [gateVal_eq_wval, Nat.add_sub_of_le hnw] at hg
        exact hg
    rw [gateVal_eq_wval, wval_gate_or hAO x hj hop, Bool.or_eq_true]
    rw [gate_inputs_eq hAO hj] at hw
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl
    · exact Or.inl hwv
    · exact Or.inr hwv

lemma topForm_isLiftFixedPoint {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {C : Circuit} (hAO : IsAO2 n C) (hF : circuitFun n C = graphFun G ∅)
    (hT : TopForm G C) : IsLiftFixedPoint G C := by
  rintro ⟨h, hh, b, hLive, _, hNot, hImp⟩
  have hwlt := opnd_lt hAO hh b
  obtain ⟨r, hr, hro, hrb, hrc⟩ :=
    below_wire_contains_top hAO (opnd C h b) (by omega) hImp.1
  have hwn : n ≤ opnd C h b := by
    by_contra hlt
    exact input_not_belowF (by omega : opnd C h b < n) hImp.1
  have hrh : InCone n C r h :=
    (inCone_iff hh).mpr ⟨opnd C h b, opnd_mem hAO hh b, hwn, hwlt, hrc⟩
  have hor : ∀ k, InCone n C h k → (gateAt C k).op = GateOp.or := by
    intro k hk
    have hkl := inCone_lt_len hk
    rcases hAO.1 _ (gateAt_mem hkl) with hand | hkor
    · exact False.elim (hT r hr k hkl hro hrb hand (inCone_trans hrh hk))
    · exact hkor
  apply hNot
  intro x hx
  have hout : wval C x C.output = true := by
    rcases hLive.2 with hout | ⟨houtn, hcone⟩
    · rw [hout]
      exact hx
    · have hc := cone_propagates_through_or hAO hcone hor x hx
      rw [gateVal_eq_wval, Nat.add_sub_of_le houtn] at hc
      exact hc
  change circuitFun n C x = true at hout
  rwa [hF] at hout

end Lift


def CrossStar {n : ℕ} (G : SimpleGraph (Fin n)) (A B : Finset (Fin n)) : Prop :=
  ∃ x ∈ A, ∃ y ∈ B, G.Adj x y ∧
    (∀ a ∈ A, G.Adj a y) ∧ (∀ b ∈ B, G.Adj x b)

lemma no_four {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (h : PEqualNP.TopForm.NoFourCycle G) {a b u v : Fin n}
    (hab : a ≠ b) (huv : u ≠ v) (hau : G.Adj a u) (hav : G.Adj a v)
    (hbu : G.Adj b u) (hbv : G.Adj b v) : False := by
  have hh := h a b hab
  have hsub : ({u, v} : Finset (Fin n)) ⊆
      Finset.univ.filter (fun w => G.Adj a w ∧ G.Adj b w) := by
    intro w hw
    rcases Finset.mem_insert.mp hw with rfl | hw
    · simp [hau, hbu]
    · have he := Finset.mem_singleton.mp hw
      subst w
      simp [hav, hbv]
  have hc := Finset.card_le_card hsub
  rw [Finset.card_pair huv] at hc
  omega

lemma two_shared_right_crossStar {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (h4 : PEqualNP.TopForm.NoFourCycle G)
    (A B C D : Finset (Fin n)) (ha : 2 ≤ A.card) (hc : 2 ≤ C.card)
    (x y z : Fin n) (hxa : x ∈ A) (hxc : x ∈ C)
    (hyb : y ∈ B) (hyd : y ∈ D) (hzb : z ∈ B) (hzd : z ∈ D) (hyz : y ≠ z)
    (h : ∀ a ∈ A, ∀ b ∈ B, ∀ c ∈ C, ∀ d ∈ D,
      G.Adj a b ∨ G.Adj a d ∨ G.Adj c b ∨ G.Adj c d) :
    CrossStar G A B ∨ CrossStar G C D := by
  classical
  have row : (∀ b ∈ B, G.Adj x b) ∨ (∀ d ∈ D, G.Adj x d) := by
    by_cases hh : ∀ b ∈ B, G.Adj x b
    · exact Or.inl hh
    · right
      push Not at hh
      obtain ⟨b, hb, hxb⟩ := hh
      intro d hd
      have := h x hxa b hb x hxc d hd
      tauto
  have col : ∀ t ∈ B ∩ D,
      (∀ a ∈ A, G.Adj a t) ∨ (∀ c ∈ C, G.Adj c t) := by
    intro t ht
    obtain ⟨htb, htd⟩ := Finset.mem_inter.mp ht
    by_cases hh : ∀ a ∈ A, G.Adj a t
    · exact Or.inl hh
    · right
      push Not at hh
      obtain ⟨a, ha', hat⟩ := hh
      intro c hc'
      have := h a ha' t htb c hc' t htd
      tauto
  have notAA : ¬ ((∀ a ∈ A, G.Adj a y) ∧ (∀ a ∈ A, G.Adj a z)) := by
    rintro ⟨hy, hz⟩
    obtain ⟨a, ha', b, hb', hab⟩ := Finset.one_lt_card.mp (by omega : 1 < A.card)
    exact no_four G h4 hab hyz (hy a ha') (hz a ha') (hy b hb') (hz b hb')
  have notCC : ¬ ((∀ c ∈ C, G.Adj c y) ∧ (∀ c ∈ C, G.Adj c z)) := by
    rintro ⟨hy, hz⟩
    obtain ⟨a, ha', b, hb', hab⟩ := Finset.one_lt_card.mp (by omega : 1 < C.card)
    exact no_four G h4 hab hyz (hy a ha') (hz a ha') (hy b hb') (hz b hb')
  have cy := col y (Finset.mem_inter.mpr ⟨hyb, hyd⟩)
  have cz := col z (Finset.mem_inter.mpr ⟨hzb, hzd⟩)
  have split : ((∀ a ∈ A, G.Adj a y) ∧ (∀ c ∈ C, G.Adj c z)) ∨
      ((∀ a ∈ A, G.Adj a z) ∧ (∀ c ∈ C, G.Adj c y)) := by
    tauto
  rcases row with rB | rD
  · left
    rcases split with hs | hs
    · exact ⟨x, hxa, y, hyb, rB y hyb, hs.1, rB⟩
    · exact ⟨x, hxa, z, hzb, rB z hzb, hs.1, rB⟩
  · right
    rcases split with hs | hs
    · exact ⟨x, hxc, z, hzd, rD z hzd, hs.2, rD⟩
    · exact ⟨x, hxc, y, hyd, rD y hyd, hs.2, rD⟩

lemma clean_products_quad {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (s : Fin n → Bool) (hbip : ∀ u v, G.Adj u v → s u ≠ s v)
    (A B C D : Finset (Fin n)) (color : Bool)
    (hA : ∀ a ∈ A, s a = color) (hB : ∀ b ∈ B, s b = !color)
    (hC : ∀ c ∈ C, s c = color) (hD : ∀ d ∈ D, s d = !color)
    (hclean : ∀ x : Fin n → Bool,
      (∃ a ∈ A, x a = true) → (∃ b ∈ B, x b = true) →
      (∃ c ∈ C, x c = true) → (∃ d ∈ D, x d = true) →
      PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ x = true) :
    ∀ a ∈ A, ∀ b ∈ B, ∀ c ∈ C, ∀ d ∈ D,
      G.Adj a b ∨ G.Adj a d ∨ G.Adj c b ∨ G.Adj c d := by
  intro a ha b hb c hc d hd
  let x : Fin n → Bool := fun w => decide (w = a ∨ w = b ∨ w = c ∨ w = d)
  have hx := hclean x ⟨a, ha, by simp [x]⟩ ⟨b, hb, by simp [x]⟩
    ⟨c, hc, by simp [x]⟩ ⟨d, hd, by simp [x]⟩
  have he : ∃ u v, G.Adj u v ∧ (u = a ∨ u = b ∨ u = c ∨ u = d) ∧
      (v = a ∨ v = b ∨ v = c ∨ v = d) := by
    simpa [PEqualNP.MetaComplexity.NestedCover.graphFun, x] using hx
  have hAC : ¬ G.Adj a c := fun hac => (hbip a c hac) ((hA a ha).trans (hC c hc).symm)
  have hBD : ¬ G.Adj b d := fun hbd => (hbip b d hbd) ((hB b hb).trans (hD d hd).symm)
  obtain ⟨u, v, huv, hu, hv⟩ := he
  rcases hu with rfl | rfl | rfl | rfl <;> rcases hv with rfl | rfl | rfl | rfl
  all_goals first
    | exact False.elim (hAC huv)
    | exact False.elim (hAC (huv.symm))
    | exact False.elim (hBD huv)
    | exact False.elim (hBD (huv.symm))
    | (have hsym := huv.symm; tauto)

namespace TightSupport
namespace Semantics
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
def d58 (w:List Bool) (g:Gate):List Bool:=
 w ++ [g.op.eval (g.inputs.map fun i=>w.getD i false)]
lemma d60 (C:Circuit) (x:List Bool):
  C.wires x = C.gates.foldl d58 x:=rfl
lemma d20 (gs:List Gate) (w:List Bool):
  (gs.foldl d58 w).length = w.length + gs.length:=by
 induction gs generalizing w with
 | nil=>simp
 | cons g gs ih=>
  rw [List.foldl_cons,ih]
  simp [d58]
  omega
lemma d1z (gs:List Gate) (w:List Bool) (i:ℕ) (hi:i < w.length):
  (gs.foldl d58 w).getD i false = w.getD i false:=by
 induction gs generalizing w with
 | nil=>rfl
 | cons g gs ih=>
  simp only [List.foldl_cons]
  have hlt:i < (d58 w g).length:=by simp [d58];omega
  rw [ih (d58 w g) hlt]
  simp [d58,List.getD_eq_getElem?_getD,List.getElem?_append_left hi]
lemma d2g (w:List Bool) (i:ℕ) (hi:w.length ≤ i):
  w.getD i false = false:=by
 simp [List.getD_eq_getElem?_getD,List.getElem?_eq_none hi]
lemma d57 (gs:List Gate) (j:ℕ) (hj:j < gs.length):
  ∃ (pre post:List Gate) (gj:Gate),
   gs = pre ++ gj::post∧ pre.length = j∧ gs[j]'hj = gj:=by
 refine ⟨gs.take j,gs.drop (j + 1),gs[j]'hj,?_,by simp;omega,rfl⟩
 rw [List.cons_getElem_drop_succ,List.take_append_drop]
def W (n:ℕ) (C:Circuit) (x:Fin n→ Bool) (u:ℕ):Bool:=
 (C.wires (List.ofFn x)).getD u false
lemma d22 (C:Circuit) (k:ℕ) (hk:k < C.gates.length):gateAt C k = C.gates[k]:=by
 simp [gateAt,List.getD_eq_getElem?_getD,hk]
lemma d05 (n:ℕ) (C:Circuit) (x:Fin n→ Bool) (k:ℕ) (hk:k < C.gates.length):
  W n C x (n + k) = (gateAt C k).op.eval ((gateAt C k).inputs.map fun i=>
   if i < n + k then W n C x i else false):=by
 obtain ⟨pre,post,gj,hgs,q0a,hgj⟩:=d57 C.gates k hk
 have hga:gateAt C k = gj:=by rw [d22 C k hk];exact hgj
 rw [hga]
 let w0:=pre.foldl d58 (List.ofFn x)
 have q16:w0.length = n + k:=by
  simp [w0,d20,q0a]
 have hCj:W n C x (n + k) = gj.op.eval (gj.inputs.map fun i=>w0.getD i false):=by
  simp only [W]
  rw [d60,hgs,List.foldl_append,List.foldl_cons]
  rw [d1z post (d58 w0 gj) (n + k) (by simp [d58];omega)]
  simp [d58,List.getD_eq_getElem?_getD,q16]
 rw [hCj]
 congr 1
 refine List.map_congr_left fun i _=>?_
 by_cases hi:i < n + k
 ·simp only [hi,↓reduceIte]
  simp only [W]
  rw [d60,hgs,List.foldl_append]
  exact (d1z (gj::post) w0 i (by omega)).symm
 ·simp only [hi,↓reduceIte]
  exact d2g w0 i (by omega)
lemma d06 (n:ℕ) (C:Circuit) (x:Fin n→ Bool) (u:ℕ) (hu:u < n):
  W n C x u = x ⟨u,hu⟩:=by
 simp only [W]
 rw [d60,d1z C.gates (List.ofFn x) u (by simpa using hu)]
 simp [List.getD_eq_getElem?_getD,hu]
open PEqualNP.CleanedNonEdge in
lemma d3o (n:ℕ) (gs:List Gate) (cs:List (List ℕ)):
  (gs.foldl (orStep n) cs).length = cs.length + gs.length:=by
 induction gs generalizing cs with
 | nil=>simp
 | cons g gs ih=>
  rw [List.foldl_cons,ih]
  simp [orStep]
  omega
open PEqualNP.CleanedNonEdge in
lemma d3z (n:ℕ) (cs:List (List ℕ)) (g:Gate) (x:ℕ):
  x ∈ (orStep n cs g).getD cs.length []↔ x = cs.length∨ (g.op = GateOp.or∧ 
   ∃ w ∈ g.inputs,n ≤ w∧ w < n + cs.length∧ x ∈ cs.getD (w - n) []):=by
 by_cases h:g.op = GateOp.or
 ·simp only [orStep,List.getD_eq_getElem?_getD,List.getElem?_append_right le_rfl,h,
   ↓reduceIte,true_and,Nat.sub_self,List.getElem?_cons_zero,Option.getD_some,
   List.mem_cons,List.mem_flatMap,List.mem_filter,decide_eq_true_eq]
  constructor
  ·rintro (h1 | ⟨w,⟨hw,hn,hlt⟩,hx⟩)
   ·exact Or.inl h1
   ·exact Or.inr ⟨w,hw,hn,hlt,hx⟩
  ·rintro (h1 | ⟨w,hw,hn,hlt,hx⟩)
   ·exact Or.inl h1
   ·exact Or.inr ⟨w,⟨hw,hn,hlt⟩,hx⟩
 ·simp [orStep,List.getD_eq_getElem?_getD,h]
open PEqualNP.CleanedNonEdge in
lemma d3x (n:ℕ) (cs:List (List ℕ)) (g:Gate) (m:ℕ) (hm:m < cs.length):
  (orStep n cs g).getD m [] = cs.getD m []:=by
 simp [orStep,List.getD_eq_getElem?_getD,List.getElem?_append_left hm]
open PEqualNP.CleanedNonEdge in
lemma d3n (n:ℕ) (gs:List Gate) (cs:List (List ℕ)) (k:ℕ)
  (hk:k < cs.length):
  (gs.foldl (orStep n) cs).getD k [] = cs.getD k []:=by
 induction gs generalizing cs with
 | nil=>rfl
 | cons g gs ih=>
  simp only [List.foldl_cons]
  rw [ih (orStep n cs g) (by simp [orStep];omega)]
  exact d3x n cs g k hk
open PEqualNP.CleanedNonEdge in
lemma d3v (n:ℕ) (C:Circuit) (k x:ℕ) (hk:k < C.gates.length):
  x ∈ (orSets n C).getD k []↔ x = k∨ ((gateAt C k).op = GateOp.or∧ 
   ∃ w ∈ (gateAt C k).inputs,n ≤ w∧ w < n + k∧ x ∈ (orSets n C).getD (w - n) []):=by
 obtain ⟨pre,post,gk,hgs,q0a,hgk⟩:=d57 C.gates k hk
 have hga:gateAt C k = gk:=by rw [d22 C k hk];exact hgk
 rw [hga]
 have hc:orSets n C = post.foldl (orStep n) (orStep n (pre.foldl (orStep n) []) gk):=by
  simp only [orSets]
  rw [hgs,List.foldl_append,List.foldl_cons]
 have hl0:(pre.foldl (orStep n) []).length = k:=by
  rw [d3o];simp [q0a]
 have hl1:(orStep n (pre.foldl (orStep n) []) gk).length = k + 1:=by
  simp [orStep,hl0]
 have h1:(orSets n C).getD k [] = (orStep n (pre.foldl (orStep n) []) gk).getD k []:=by
  rw [hc,d3n n post _ k (by omega)]
 have h2:∀ m,m < k→ (orSets n C).getD m [] = (pre.foldl (orStep n) []).getD m []:=by
  intro m hm
  rw [hc,d3n n post _ m (by omega)]
  exact d3x n _ gk m (by omega)
 have h3:=d3z n (pre.foldl (orStep n) []) gk x
 rw [hl0] at h3
 rw [h1,h3]
 constructor
 ·rintro (h | ⟨hop,w,hw,hn,hlt,hx⟩)
  ·exact Or.inl h
  ·exact Or.inr ⟨hop,w,hw,hn,hlt,by rw [h2 (w - n) (by omega)];exact hx⟩
 ·rintro (h | ⟨hop,w,hw,hn,hlt,hx⟩)
  ·exact Or.inl h
  ·exact Or.inr ⟨hop,w,hw,hn,hlt,by rw [← h2 (w - n) (by omega)];exact hx⟩
lemma d07 (n:ℕ) (C:Circuit) (x:Fin n→ Bool) (r:ℕ) (hr:r < C.gates.length)
  (hop:(gateAt C r).op = GateOp.or) (i:ℕ) (hi:i ∈ (gateAt C r).inputs)
  (hlt:i < n + r) (hv:W n C x i = true):W n C x (n + r) = true:=by
 rw [d05 n C x r hr,hop]
 simp only [GateOp.eval,List.any_map,List.any_eq_true,Function.comp_apply,id_eq]
 exact ⟨i,hi,by rw [if_pos hlt];exact hv⟩
open PEqualNP.CleanedNonEdge in
lemma d4h (n:ℕ) (C:Circuit) (x:Fin n→ Bool) (g:ℕ)
  (hv:W n C x (n + g) = true):
  ∀ k,k < C.gates.length→ g ∈ (orSets n C).getD k []→ W n C x (n + k) = true:=by
 intro k
 induction k using Nat.strong_induction_on with
 | _ k ih=>
  intro hk q10
  rcases (d3v n C k g hk).mp q10 with h | ⟨hop,w,hw,hn,hlt,hx⟩
  ·rw [← h];exact hv
  ·have h3:=ih (w - n) (by omega) (by omega) hx
   have e:n + (w - n) = w:=by omega
   rw [e] at h3
   exact d07 n C x k hk hop w hw hlt h3
open PEqualNP.CleanedNonEdge in
lemma d4g (n:ℕ) (C:Circuit) (x:Fin n→ Bool) (w g:ℕ)
  (h:OrReaches n C w g) (hv:W n C x (n + g) = true):W n C x w = true:=by
 obtain ⟨hn,q10⟩:=h
 by_cases hk:w - n < C.gates.length
 ·have h3:=d4h n C x g hv (w - n) hk q10
  have e:n + (w - n) = w:=by omega
  rw [e] at h3
  exact h3
 ·exfalso
  have q06:(orSets n C).length = C.gates.length:=by
   unfold orSets;rw [d3o];simp
  have hge:(orSets n C).length ≤ w - n:=by omega
  rw [List.getD_eq_getElem?_getD,List.getElem?_eq_none hge] at q10
  simp at q10
lemma d31 {α:Type} (p:α→ Prop) (d:DecidablePred p) (s:Finset α) (a:α)
  (h:a ∈ @Finset.filter α p d s):p a:=
 ((@Finset.mem_filter α p d s a).mp h).2
lemma d55 (n:ℕ) (C:Circuit) (x:Fin n→ Bool) (j:ℕ) (b:Fin 2) (i:Fin n)
  (hi:i ∈ PEqualNP.TopForm.side (n:=n) C j b) (hx:x i = true):
  W n C x (PEqualNP.TopForm.opnd C j b) = true:=by
 unfold PEqualNP.TopForm.side PEqualNP.TopForm.orIn at hi
 have hi2:=d31 _ _ _ _ hi
 rcases hi2 with h | ⟨k,hk,q02,hop,hin⟩
 ·rw [← h,d06 n C x i.val i.isLt];exact hx
 ·have hk1:W n C x (n + k) = true:=by
   apply d07 n C x k hk hop i.val hin (by have:=i.isLt;omega)
   rw [d06 n C x i.val i.isLt];exact hx
  exact d4g n C x _ k q02 hk1
lemma d24 (C:Circuit) (j:ℕ) (hj:j < C.gates.length):gateAt C j ∈ C.gates:=by
 rw [d22 C j hj];exact List.getElem_mem hj
lemma d3p (n:ℕ) (C:Circuit) (w:ℕ) (i:Fin n):
  i ∈ PEqualNP.TopForm.orIn n C w↔ ((i:ℕ) = w∨ ∃ k < C.gates.length,
   PEqualNP.CleanedNonEdge.OrReaches n C w k∧ (gateAt C k).op = GateOp.or∧ 
    (i:ℕ) ∈ (gateAt C k).inputs):=by
 unfold PEqualNP.TopForm.orIn
 simp only [Finset.mem_filter,Finset.mem_univ,true_and]
end Semantics
namespace Boundary
open PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership
end Boundary
namespace Color
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
 PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm
 PEqualNP.Outside.L_meta_5012.TightSupport.Semantics
lemma d3q {n:ℕ} (C:Circuit) (x:Fin n→ Bool) (w:ℕ) (i:Fin n)
  (hi:i ∈ orIn n C w) (hx:x i = true):W n C x w = true:=by
 rcases (d3p n C w i).mp hi with h | ⟨k,hk,q02,hop,hin⟩
 ·rw [← h,d06 n C x i.val i.isLt]
  exact hx
 ·apply d4g n C x w k q02
  apply d07 n C x k hk hop i.val hin (by have:=i.isLt;omega)
  rw [d06 n C x i.val i.isLt]
  exact hx
lemma d2j {n:ℕ} (G:SimpleGraph (Fin n)) [DecidableRel G.Adj]
  (u v:Fin n) (h:graphFun G ∅ (pairInput u v) = true):G.Adj u v:=by
 simp only [graphFun,Finset.notMem_empty,false_and,exists_false,decide_false,
  Bool.false_or,decide_eq_true_eq] at h
 obtain ⟨a,b,hab,ha,hb⟩:=h
 have ha':a = u∨ a = v:=by simpa [pairInput] using ha
 have hb':b = u∨ b = v:=by simpa [pairInput] using hb
 rcases ha' with rfl | rfl <;> rcases hb' with rfl | rfl
 ·exact (G.irrefl hab).elim
 ·exact hab
 ·exact hab.symm
 ·exact (G.irrefl hab).elim
lemma d0e {n:ℕ} (C:Circuit) (hAO:IsAO2 n C)
  (a:ℕ) (ha:a < C.gates.length) (hop:(gateAt C a).op = GateOp.and)
  (x:Fin n→ Bool) (h0:W n C x (opnd C a 0) = true)
  (h1:W n C x (opnd C a 1) = true):W n C x (n + a) = true:=by
 obtain ⟨p,q,hin⟩:=List.length_eq_two.mp (hAO.2.2 _ (d24 C a ha))
 have hp:p < n + a:=hAO.2.1 a ha p (by rw [hin];simp)
 have hq:q < n + a:=hAO.2.1 a ha q (by rw [hin];simp)
 have e0:opnd C a 0 = p:=by simp [opnd,hin]
 have e1:opnd C a 1 = q:=by simp [opnd,hin]
 rw [e0] at h0
 rw [e1] at h1
 rw [d05 n C x a ha,hop,hin]
 simp [GateOp.eval,hp,hq,h0,h1]
lemma d2s {n:ℕ} (G:SimpleGraph (Fin n))
  [DecidableRel G.Adj] (C:Circuit) (hAO:IsAO2 n C)
  (k:ℕ) (hk:k ∈ lam G C):
  ∃ c:Fin n,∀ u ∈ orIn n C (n + k),G.Adj u c:=by
 classical
 obtain ⟨_,_,_,a,ha,b,hc,hr⟩:=Finset.mem_filter.mp hk
 obtain ⟨c,hc⟩:=Finset.card_eq_one.mp hc
 refine ⟨c,?_⟩
 intro u hu
 have q29:W n C (pairInput u c) (n + k) = true:=
  d3q C _ _ u hu (by simp [pairInput])
 have q1j:W n C (pairInput u c) (opnd C a b) = true:=
  d4g n C _ _ k hr q29
 have q1k:c ∈ side (n:=n) C a (1 - b):=by rw [hc];simp
 have q1l:W n C (pairInput u c) (opnd C a (1 - b)) = true:=
  d55 n C _ a (1 - b) c q1k (by simp [pairInput])
 have q30:=ha
 simp only [tops,gatesWhere,Finset.mem_filter,Finset.mem_range] at q30
 obtain ⟨q31,hop,q03⟩:=q30
 apply d2j G u c
 apply q03
 change W n C (pairInput u c) (n + a) = true
 have hb:b = 0∨ b = 1:=by omega
 rcases hb with rfl | rfl
 ·exact d0e C hAO a q31 hop _ q1j q1l
 ·exact d0e C hAO a q31 hop _ q1l q1j
lemma d2t {n:ℕ} (G:SimpleGraph (Fin n))
  [DecidableRel G.Adj] (C:Circuit) (hAO:IsAO2 n C) (s:Fin n→ Bool)
  (hs:∀ u v,G.Adj u v→ s u ≠ s v) (k:ℕ) (hk:k ∈ lam G C):
  ∀ u ∈ orIn n C (n + k),∀ v ∈ orIn n C (n + k),s u = s v:=by
 obtain ⟨c,hc⟩:=d2s G C hAO k hk
 intro u hu v hv
 have huc:=hs u c (hc u hu)
 have hvc:=hs v c (hc v hv)
 cases hsu:s u <;> cases hsv:s v <;> cases hsc:s c <;> simp_all
lemma d5b {n:ℕ} (G:SimpleGraph (Fin n))
  [DecidableRel G.Adj] (C:Circuit) (hAO:IsAO2 n C) (s:Fin n→ Bool)
  (hs:∀ u v,G.Adj u v→ s u ≠ s v) (m:ℕ)
  (q09:orN G C \ lam G C = {m}) (k:ℕ) (hkm:k < m)
  (hk:k ∈ orN G C):
  ∀ u ∈ orIn n C (n + k),∀ v ∈ orIn n C (n + k),s u = s v:=by
 apply d2t G C hAO s hs k
 by_contra hn
 have hm:k ∈ orN G C \ lam G C:=Finset.mem_sdiff.mpr ⟨hk,hn⟩
 rw [q09,Finset.mem_singleton] at hm
 omega
end Color
namespace SharedOrAccounting
open PEqualNP.TopForm PEqualNP.MetaComplexity.NestedCover
end SharedOrAccounting
namespace SharedProduct
open PEqualNP.TopForm PEqualNP.MetaComplexity.NestedCover
 PEqualNP.Outside.L_meta_5012.TightSupport.SharedOrAccounting
end SharedProduct
end TightSupport
namespace TightSupport.Budget
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
 PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm
def d58 (w:List Bool) (g:Gate):List Bool:=
 w ++ [g.op.eval (g.inputs.map fun i=>w.getD i false)]
lemma d60 (C:Circuit) (x:List Bool):
  C.wires x = C.gates.foldl d58 x:=rfl
lemma d1y (gs:List Gate) (w:List Bool):
  (gs.foldl d58 w).length = w.length + gs.length:=by
 induction gs generalizing w with
 | nil=>simp
 | cons g gs ih=>
  rw [List.foldl_cons,ih]
  simp [d58]
  omega
lemma d1x (gs:List Gate) (w:List Bool) (i:ℕ) (hi:i < w.length):
  (gs.foldl d58 w).getD i false = w.getD i false:=by
 induction gs generalizing w with
 | nil=>rfl
 | cons g gs ih=>
  simp only [List.foldl_cons]
  have hlt:i < (d58 w g).length:=by simp [d58];omega
  rw [ih (d58 w g) hlt]
  simp [d58,List.getD_eq_getElem?_getD,List.getElem?_append_left hi]
lemma d2f (w:List Bool) (i:ℕ) (hi:w.length ≤ i):w.getD i false = false:=by
 simp [List.getD_eq_getElem?_getD,List.getElem?_eq_none hi]
lemma d1w (gs:List Gate) (w:List Bool) (j:ℕ) (hj:j < gs.length):
  (gs.foldl d58 w).getD (w.length + j) false =
   (gs[j]).op.eval ((gs[j]).inputs.map fun i=>
    if i < w.length + j then (gs.foldl d58 w).getD i false else false):=by
 induction gs generalizing w j with
 | nil=>simp at hj
 | cons g gs ih=>
  rw [List.foldl_cons]
  cases j with
  | zero=>
   have h1:w.length < (d58 w g).length:=by simp [d58]
   rw [Nat.add_zero,d1x gs (d58 w g) w.length h1]
   simp only [List.getElem_cons_zero]
   have h2:(d58 w g).getD w.length false =
     g.op.eval (g.inputs.map fun i=>w.getD i false):=by
    simp [d58,List.getD_eq_getElem?_getD]
   rw [h2]
   congr 1
   apply List.map_congr_left
   intro i _
   by_cases hi:i < w.length
   ·rw [ite_eq_left hi,d1x gs (d58 w g) i (by simp [d58];omega)]
    simp [d58,List.getD_eq_getElem?_getD,List.getElem?_append_left hi]
   ·rw [ite_eq_right hi];exact d2f w i (by omega)
  | succ j=>
   have hj':j < gs.length:=by simpa using hj
   have key:=ih (d58 w g) j hj'
   have hl:(d58 w g).length = w.length + 1:=by simp [d58]
   rw [hl] at key
   have e:w.length + (j + 1) = w.length + 1 + j:=by omega
   simp only [List.getElem_cons_succ]
   rw [e]
   exact key
def val (C:Circuit) (x:List Bool) (u:ℕ):Bool:=(C.wires x).getD u false
lemma d22 {C:Circuit} {j:ℕ} (hj:j < C.gates.length):gateAt C j = C.gates[j]:=by
 simp [gateAt,List.getD_eq_getElem?_getD,hj]
lemma d23 {C:Circuit} {j:ℕ} (hj:j < C.gates.length):gateAt C j ∈ C.gates:=by
 rw [d22 hj];exact List.getElem_mem hj
lemma d5v {n:ℕ} {C:Circuit} {x:List Bool} (hx:x.length = n) {u:ℕ} (hu:u < n):
  val C x u = x.getD u false:=by
 unfold val;rw [d60];exact d1x _ _ _ (by omega)
lemma d5t {n:ℕ} {C:Circuit} {x:List Bool} (hx:x.length = n) {u:ℕ}
  (hu:n + C.gates.length ≤ u):val C x u = false:=by
 unfold val;apply d2f;rw [d60,d1y];omega
lemma d5s {n:ℕ} {C:Circuit} {x:List Bool} (hx:x.length = n) {j:ℕ}
  (hj:j < C.gates.length):
  val C x (n + j) = (gateAt C j).op.eval ((gateAt C j).inputs.map fun i=>
   if i < n + j then val C x i else false):=by
 subst hx
 rw [d22 hj]
 exact d1w C.gates x j hj
lemma d5x {n:ℕ} {C:Circuit} {x:List Bool} (hx:x.length = n) {r:ℕ}
  (hr:r < C.gates.length) (hop:(gateAt C r).op = GateOp.or):
  val C x (n + r) = true↔ ∃ i ∈ (gateAt C r).inputs,i < n + r∧ val C x i = true:=by
 rw [d5s hx hr,hop]
 simp only [GateOp.eval,List.any_map,List.any_eq_true,Function.comp_apply,id_eq]
 constructor
 ·rintro ⟨i,hi,h⟩
  by_cases hlt:i < n + r
  ·rw [ite_eq_left hlt] at h;exact ⟨i,hi,hlt,h⟩
  ·rw [ite_eq_right hlt] at h;cases h
 ·rintro ⟨i,hi,hlt,h⟩
  exact ⟨i,hi,by rw [ite_eq_left hlt];exact h⟩
lemma d5r {n:ℕ} {C:Circuit} {x:List Bool} (hx:x.length = n) {r:ℕ}
  (hr:r < C.gates.length) (hop:(gateAt C r).op = GateOp.and):
  val C x (n + r) = true↔ ∀ i ∈ (gateAt C r).inputs,i < n + r∧ val C x i = true:=by
 rw [d5s hx hr,hop]
 simp only [GateOp.eval,List.all_map,List.all_eq_true,Function.comp_apply,id_eq]
 constructor
 ·intro h i hi
  have h':=h i hi
  by_cases hlt:i < n + r
  ·rw [ite_eq_left hlt] at h';exact ⟨hlt,h'⟩
  ·rw [ite_eq_right hlt] at h';cases h'
 ·intro h i hi
  rw [ite_eq_left (h i hi).1];exact (h i hi).2
lemma d5w {n:ℕ} (C:Circuit) (x:Fin n→ Bool) (u:Fin n):
  val C (List.ofFn x) u.val = x u:=by
 rw [d5v (n:=n) (by simp) u.isLt]
 simp [List.getD_eq_getElem?_getD]
lemma d2c (n:ℕ) (C:Circuit) (j:ℕ) (x:Fin n→ Bool):
  PEqualNP.EdgeOwnership.gateVal n C j x = val C (List.ofFn x) (n + j):=rfl
def d53 (n k w:ℕ):ℕ:=
 if w < n + k then w else w - 1
def d5p (n k w:ℕ):ℕ:=
 if w < n + k then w else w + 1
def d5o (k j:ℕ):ℕ:=
 if j < k then j else j + 1
def d52 (n k:ℕ) (g:Gate):Gate:=
 ⟨g.op,g.inputs.map (d53 n k)⟩
def d19 (n k:ℕ) (C:Circuit):Circuit:=
 ⟨(C.gates.eraseIdx k).map (d52 n k),d53 n k C.output⟩
lemma d5q (n k w:ℕ) (hne:w ≠ n + k):
  d5p n k (d53 n k w) = w:=by
 unfold d5p d53
 split_ifs <;> omega
lemma d1f (n k:ℕ) (C:Circuit) (hk:k < C.size):
  (d19 n k C).size + 1 = C.size:=by
 unfold Circuit.size at hk ⊢
 unfold d19
 simp only [List.length_map,List.length_eraseIdx_of_lt hk]
 omega
lemma d1d (n k:ℕ) (C:Circuit) (hk:k < C.gates.length):
  (d19 n k C).gates.length = C.gates.length - 1:=by
 simp [d19,List.length_eraseIdx_of_lt hk]
lemma d1c (n k:ℕ) (C:Circuit) (hk:k < C.gates.length)
  (j:ℕ) (hj:j < (d19 n k C).gates.length):
  gateAt (d19 n k C) j = d52 n k (gateAt C (d5o k j)):=by
 have q0m:j < C.gates.length - 1:=by
  rw [← d1d n k C hk];exact hj
 have q32:j < (C.gates.eraseIdx k).length:=by
  rw [List.length_eraseIdx_of_lt hk];exact q0m
 rw [d22 hj]
 simp only [d19,List.getElem_map,d5o]
 split_ifs with hjk
 ·rw [List.getElem_eraseIdx_of_lt q32 hjk,d22 (C:=C) (j:=j) (by omega)]
 ·rw [List.getElem_eraseIdx_of_ge q32 (by omega),d22 (C:=C) (j:=j + 1) (by omega)]
lemma d1e (n k:ℕ) (C:Circuit) (hRB:ReadsBack n C)
  (hk:k < C.gates.length) (hno:∀ j < C.gates.length,n + k ∉ (gateAt C j).inputs):
  ReadsBack n (d19 n k C):=by
 intro j hj w' hw'
 rw [d1c n k C hk j hj] at hw'
 simp only [d52,List.mem_map] at hw'
 obtain ⟨w,hw,rfl⟩:=hw'
 have q33:j < C.gates.length - 1:=by
  rw [← d1d n k C hk];exact hj
 have q0c:d5o k j < C.gates.length:=by
  unfold d5o;split_ifs <;> omega
 have q1m:w < n + d5o k j:=hRB (d5o k j) q0c w hw
 have q39:w ≠ n + k:=fun heq=>hno (d5o k j) q0c (heq ▸ hw)
 unfold d53
 unfold d5o at q1m
 split_ifs at q1m ⊢ <;> omega
def d1p {α:Type} (d0:α) (evalG:GateOp→ List α→ α) (acc:List α) (g:Gate):
  List α:=
 acc ++ [evalG g.op (g.inputs.map fun i=>acc.getD i d0)]
lemma d1u {α:Type} (d0:α) (evalG:GateOp→ List α→ α)
  (gs:List Gate) (acc:List α):
  (gs.foldl (d1p d0 evalG) acc).length = acc.length + gs.length:=by
 induction gs generalizing acc with
 | nil=>simp
 | cons g gs ih=>
  simp only [List.foldl_cons,ih,d1p,List.length_append,List.length_cons,List.length_nil]
  omega
lemma d1v {α:Type} (d0:α) (evalG:GateOp→ List α→ α)
  (gs:List Gate) (acc:List α) (w:ℕ) (hw:w < acc.length):
  (gs.foldl (d1p d0 evalG) acc).getD w d0 = acc.getD w d0:=by
 induction gs generalizing acc with
 | nil=>rfl
 | cons g gs ih=>
  have hw':w < (d1p d0 evalG acc g).length:=by
   simp only [d1p,List.length_append,List.length_singleton]
   omega
  rw [List.foldl_cons,ih (d1p d0 evalG acc g) hw']
  rw [List.getD_eq_getElem?_getD,List.getD_eq_getElem?_getD]
  simp only [d1p,List.getElem?_append_left hw]
lemma d1t {α:Type} (d0:α) (evalG:GateOp→ List α→ α)
  (n:ℕ) (C:Circuit) (init:List α) (q0n:init.length = n)
  (hRB:ReadsBack n C) (j:ℕ) (hj:j < C.gates.length):
  (C.gates.foldl (d1p d0 evalG) init).getD (n + j) d0 =
   evalG (gateAt C j).op
    ((gateAt C j).inputs.map fun u=>(C.gates.foldl (d1p d0 evalG) init).getD u d0):=by
 have q1n:C.gates = C.gates.take j ++ [C.gates[j]] ++ C.gates.drop (j + 1):=by
  have h1:=List.take_append_drop j C.gates
  have h2:C.gates.drop j = C.gates[j]::C.gates.drop (j + 1):=List.drop_eq_getElem_cons hj
  rw [h2] at h1
  simp only [List.append_assoc,List.singleton_append,h1]
 set acc:=(C.gates.take j).foldl (d1p d0 evalG) init with q2a
 have q11:acc.length = n + j:=by
  rw [q2a,d1u,q0n,List.length_take]
  omega
 have q2b:∀ u < n + j,
   (C.gates.foldl (d1p d0 evalG) init).getD u d0 = acc.getD u d0:=by
  intro u hu
  conv_lhs=>rw [← List.take_append_drop j C.gates]
  rw [List.foldl_append,← q2a]
  exact d1v d0 evalG (C.gates.drop j) acc u (by omega)
 have q17:(C.gates.foldl (d1p d0 evalG) init).getD (n + j) d0 =
   evalG C.gates[j].op (C.gates[j].inputs.map fun u=>acc.getD u d0):=by
  conv_lhs=>rw [q1n]
  rw [List.foldl_append,List.foldl_append,← q2a,List.foldl_cons,List.foldl_nil]
  have q06:n + j < (d1p d0 evalG acc C.gates[j]).length:=by
   simp only [d1p,List.length_append,List.length_singleton]
   omega
  rw [d1v d0 evalG (C.gates.drop (j + 1)) (d1p d0 evalG acc C.gates[j])
   (n + j) q06]
  rw [List.getD_eq_getElem?_getD]
  simp only [d1p,List.getElem?_append_right (by omega:acc.length ≤ n + j),
   q11,Nat.sub_self,List.getElem?_cons_zero,Option.getD_some]
 rw [q17,d22 hj]
 congr 1
 apply List.map_congr_left
 intro u hu
 rw [← d22 hj] at hu
 exact (q2b u (hRB j hj u hu)).symm
lemma d1b {α:Type} (d0:α) (evalG:GateOp→ List α→ α)
  (n k:ℕ) (C:Circuit) (init:List α) (q0n:init.length = n)
  (hRB:ReadsBack n C) (hk:k < C.gates.length)
  (hno:∀ j < C.gates.length,n + k ∉ (gateAt C j).inputs):
  ∀ w:ℕ,
   ((d19 n k C).gates.foldl (d1p d0 evalG) init).getD w d0 =
    (C.gates.foldl (d1p d0 evalG) init).getD (d5p n k w) d0:=by
 have q34:ReadsBack n (d19 n k C):=d1e n k C hRB hk hno
 intro w
 induction w using Nat.strong_induction_on with
 | ind w ih=>
  by_cases q1o:n + (d19 n k C).gates.length ≤ w
  ·have q3a:((d19 n k C).gates.foldl (d1p d0 evalG) init).length =
     n + (d19 n k C).gates.length:=by
    rw [d1u,q0n]
   have q06:(C.gates.foldl (d1p d0 evalG) init).length = n + C.gates.length:=by
    rw [d1u,q0n]
   have hdl:=d1d n k C hk
   have huw:n + C.gates.length ≤ d5p n k w:=by
    unfold d5p;split_ifs <;> omega
   rw [List.getD_eq_getElem?_getD,List.getD_eq_getElem?_getD]
   rw [List.getElem?_eq_none (by omega),List.getElem?_eq_none (by omega)]
  ·push Not at q1o
   by_cases hwn:w < n
   ·have huw:d5p n k w = w:=by unfold d5p;split_ifs <;> omega
    rw [huw]
    rw [d1v d0 evalG (d19 n k C).gates init w (by omega)]
    rw [d1v d0 evalG C.gates init w (by omega)]
   ·set j:=w - n with q35
    have q2c:w = n + j:=by omega
    have q0m:j < (d19 n k C).gates.length:=by omega
    have hdl:=d1d n k C hk
    have q0c:d5o k j < C.gates.length:=by
     unfold d5o;split_ifs <;> omega
    have huw:d5p n k (n + j) = n + d5o k j:=by
     unfold d5p d5o;split_ifs <;> omega
    rw [q2c,huw]
    rw [d1t d0 evalG n (d19 n k C) init q0n q34 j q0m]
    rw [d1t d0 evalG n C init q0n hRB (d5o k j) q0c]
    rw [d1c n k C hk j q0m]
    simp only [d52,List.map_map]
    congr 1
    apply List.map_congr_left
    intro u hu
    have q3b:d53 n k u < n + j:=by
     have q10:d53 n k u ∈ (gateAt (d19 n k C) j).inputs:=by
      rw [d1c n k C hk j q0m]
      simp only [d52,List.mem_map]
      exact ⟨u,hu,rfl⟩
     exact q34 j q0m (d53 n k u) q10
    have q2d:u ≠ n + k:=fun heq=>hno (d5o k j) q0c (heq ▸ hu)
    simp only [Function.comp_apply]
    rw [ih (d53 n k u) (by omega),d5q n k u q2d]
lemma d1g (n k:ℕ) (C:Circuit) (l:List Bool) (hl:l.length = n)
  (hRB:ReadsBack n C) (hk:k < C.gates.length)
  (hno:∀ j < C.gates.length,n + k ∉ (gateAt C j).inputs) (w:ℕ):
  ((d19 n k C).wires l).getD w false = (C.wires l).getD (d5p n k w) false:=
 d1b false GateOp.eval n k C l hl hRB hk hno w
private lemma d1a {n k:ℕ} {C:Circuit} (h:IsAO2 n C)
  (hk:k < C.gates.length)
  (hno:∀ j < C.gates.length,n + k ∉ (gateAt C j).inputs):
  IsAO2 n (d19 n k C):=by
 have mapped:∀ g ∈ (d19 n k C).gates,
   (g.op = GateOp.and∨ g.op = GateOp.or)∧ g.inputs.length = 2:=by
  intro g hg
  obtain ⟨g',hg',rfl⟩:=List.mem_map.mp hg
  have hm:=List.mem_of_mem_eraseIdx hg'
  exact ⟨h.1 g' hm,by simp [d52,h.2.2 g' hm]⟩
 exact ⟨fun g hg=>(mapped g hg).1,d1e n k C h.2.1 hk hno,
  fun g hg=>(mapped g hg).2⟩
private def d03 (n:ℕ) (C:Circuit):Prop:=
 ∀ D:Circuit,IsAO2 n D→ circuitFun n D = circuitFun n C→ C.size ≤ D.size
private lemma d4l {n k:ℕ} {C:Circuit} (h:IsAO2 n C) (q36:d03 n C)
  (hk:k < C.gates.length) (q08:C.output ≠ n + k):
  ∃ j < C.gates.length,n + k ∈ (gateAt C j).inputs:=by
 by_contra q27
 have hno:∀ j < C.gates.length,n + k ∉ (gateAt C j).inputs:=
  fun j hj hj'=>q27 ⟨j,hj,hj'⟩
 have heq:circuitFun n (d19 n k C) = circuitFun n C:=by
  funext x
  unfold circuitFun Circuit.eval
  rw [d1g n k C _ List.length_ofFn h.2.1 hk hno]
  change (C.wires (List.ofFn x)).getD (d5p n k (d53 n k C.output)) false = _
  rw [d5q n k C.output q08]
 have hle:=q36 _ (d1a h hk hno) heq
 have q0r:=d1f n k C hk
 omega
def d04 (n:ℕ) (C:Circuit) (w w':ℕ):Prop:=
 ∃ k,k < C.gates.length∧ w = n + k∧ (gateAt C k).op = GateOp.or∧ 
  w' ∈ (gateAt C k).inputs∧ w' < n + k
lemma d40 {n:ℕ} {C:Circuit} {x:List Bool} (hx:x.length = n) {w w':ℕ}
  (h:Relation.ReflTransGen (d04 n C) w w') (hv:val C x w' = true):
  val C x w = true:=by
 induction h using Relation.ReflTransGen.head_induction_on with
 | refl=>exact hv
 | head q05 _ ih=>
  obtain ⟨k,hk,rfl,hop,hin,hlt⟩:=q05
  exact (d5x hx hk hop).mpr ⟨_,hin,hlt,ih⟩
lemma d41 {n:ℕ} {C:Circuit} {x:List Bool} (hx:x.length = n):
  ∀ w:ℕ,val C x w = true→ 
   ∃ w',Relation.ReflTransGen (d04 n C) w w'∧ val C x w' = true∧ 
    (w' < n∨ ∃ h,h < C.gates.length∧ w' = n + h∧ (gateAt C h).op ≠ GateOp.or):=by
 intro w
 induction w using Nat.strong_induction_on with
 | _ w ih=>
  intro hv
  by_cases hw:w < n
  ·exact ⟨w,Relation.ReflTransGen.refl,hv,Or.inl hw⟩
  ·by_cases q06:n + C.gates.length ≤ w
   ·rw [d5t hx q06] at hv;cases hv
   ·obtain ⟨k,rfl⟩:∃ k,w = n + k:=⟨w - n,by omega⟩
    have hk:k < C.gates.length:=by omega
    by_cases hop:(gateAt C k).op = GateOp.or
    ·obtain ⟨i,hin,hlt,hi⟩:=(d5x hx hk hop).mp hv
     obtain ⟨w',hr,hv',hw'⟩:=ih i hlt hi
     exact ⟨w',Relation.ReflTransGen.head ⟨k,hk,rfl,hop,hin,hlt⟩ hr,hv',hw'⟩
    ·exact ⟨n + k,Relation.ReflTransGen.refl,hv,Or.inr ⟨k,hk,rfl,hop⟩⟩
lemma d46 {n:ℕ} (u v:Fin n):pairInput u v u = true:=by
 simp [pairInput]
lemma d47 {n:ℕ} (u v:Fin n):pairInput u v v = true:=by
 simp [pairInput]
lemma d48 {n:ℕ} (u v w:Fin n):pairInput u v w = true↔ w = u∨ w = v:=by
 simp [pairInput]
lemma d2i {n:ℕ} (G:SimpleGraph (Fin n)) [DecidableRel G.Adj] (u v:Fin n):
  graphFun G ∅ (pairInput u v) = true↔ G.Adj u v:=by
 simp only [graphFun,Finset.notMem_empty,false_and,exists_false,decide_false,
  Bool.false_or,decide_eq_true_eq,d48]
 constructor
 ·rintro ⟨a,b,hab,ha,hb⟩
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
  ·exact (G.irrefl hab).elim
  ·exact hab
  ·exact hab.symm
  ·exact (G.irrefl hab).elim
 ·intro h
  exact ⟨u,v,h,Or.inl rfl,Or.inr rfl⟩
lemma d3j {n:ℕ} {C:Circuit} (u v:Fin n) (p:ℕ)
  (hv:val C (List.ofFn (pairInput u v)) p = true):
  (∃ t:Fin n,(t = u∨ t = v)∧ Relation.ReflTransGen (d04 n C) p t.val)∨ 
  (∃ h,h < C.gates.length∧ (gateAt C h).op ≠ GateOp.or∧ 
   Relation.ReflTransGen (d04 n C) p (n + h)∧ 
   val C (List.ofFn (pairInput u v)) (n + h) = true):=by
 obtain ⟨w',hr,hv',hw'⟩:=d41 (n:=n) (C:=C) (x:=List.ofFn (pairInput u v))
  (by simp) p hv
 rcases hw' with hlt | ⟨h,hh,rfl,hop⟩
 ·left
  refine ⟨⟨w',hlt⟩,?_,hr⟩
  have h1:=d5w C (pairInput u v) ⟨w',hlt⟩
  rw [show (⟨w',hlt⟩:Fin n).val = w' from rfl,hv'] at h1
  exact (d48 u v _).mp h1.symm
 ·right
  exact ⟨h,hh,hop,hr,hv'⟩
lemma d4i {n:ℕ} {C:Circuit} (x:Fin n→ Bool) (p:ℕ) (t:Fin n)
  (hr:Relation.ReflTransGen (d04 n C) p t.val) (ht:x t = true):
  val C (List.ofFn x) p = true:=
 d40 (n:=n) (by simp) hr (by rw [d5w];exact ht)
lemma d1n {n:ℕ} (G:SimpleGraph (Fin n)) {C:Circuit} (F:(Fin n→ Bool)→ Bool)
  (hF:∀ u v:Fin n,F (pairInput u v) = true→ G.Adj u v)
  (q08:∀ x:Fin n→ Bool,val C (List.ofFn x) C.output = F x)
  (u v:Fin n) (huv:F (pairInput u v) = true):
  ∃ a,a < C.gates.length∧ (gateAt C a).op ≠ GateOp.or∧ 
   Relation.ReflTransGen (d04 n C) C.output (n + a)∧ 
   val C (List.ofFn (pairInput u v)) (n + a) = true:=by
 rcases d3j (C:=C) u v C.output (by rw [q08];exact huv) with
  ⟨t,_,hr⟩ | h
 ·exfalso
  have h1:=d4i (pairInput t t) _ t hr (d46 t t)
  rw [q08] at h1
  exact G.irrefl (hF t t h1)
 ·exact h
lemma d0g {n:ℕ} {C:Circuit} (F:(Fin n→ Bool)→ Bool)
  (q08:∀ x:Fin n→ Bool,val C (List.ofFn x) C.output = F x) (a:ℕ)
  (hr:Relation.ReflTransGen (d04 n C) C.output (n + a)) (x:Fin n→ Bool)
  (hv:val C (List.ofFn x) (n + a) = true):F x = true:=by
 rw [← q08]
 exact d40 (n:=n) (by simp) hr hv
lemma d0x (n:ℕ) (gs:List Gate) (cs:List (List ℕ)):
  (gs.foldl (coneStep n) cs).length = cs.length + gs.length:=by
 induction gs generalizing cs with
 | nil=>simp
 | cons g gs ih=>
  rw [List.foldl_cons,ih]
  simp [coneStep]
  omega
lemma d0w (n:ℕ) (gs:List Gate):
  ∀ i j,i ∈ (gs.foldl (coneStep n) []).getD j []↔ 
   j < gs.length∧ ∃ w ∈ (gs.getD j ⟨GateOp.or,[]⟩).inputs,n ≤ w∧ w < n + j∧ 
    (i = w - n∨ i ∈ (gs.foldl (coneStep n) []).getD (w - n) []):=by
 induction gs using List.reverseRecOn with
 | nil=>intro i j;simp
 | append_singleton gs g ih=>
  intro i j
  rw [List.foldl_append,List.foldl_cons,List.foldl_nil]
  have q06:(gs.foldl (coneStep n) []).length = gs.length:=by
   rw [d0x];simp
  have key:∀ k,k < gs.length→ 
    (coneStep n (gs.foldl (coneStep n) []) g).getD k [] =
     (gs.foldl (coneStep n) []).getD k []:=by
   intro k hk
   simp only [coneStep,List.getD_eq_getElem?_getD]
   rw [List.getElem?_append_left (by omega)]
  rcases Nat.lt_trichotomy j gs.length with h | h | h
  ·have e1:(gs ++ [g]).getD j ⟨GateOp.or,[]⟩ = gs.getD j ⟨GateOp.or,[]⟩:=by
    simp only [List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_left h]
   rw [key j h,ih i j,e1]
   constructor
   ·rintro ⟨_,w,hw,h1,h2,h3⟩
    refine ⟨by simp;omega,w,hw,h1,h2,?_⟩
    rw [key (w - n) (by omega)]
    exact h3
   ·rintro ⟨_,w,hw,h1,h2,h3⟩
    refine ⟨h,w,hw,h1,h2,?_⟩
    rw [key (w - n) (by omega)] at h3
    exact h3
  ·subst h
   have e1:(gs ++ [g]).getD gs.length ⟨GateOp.or,[]⟩ = g:=by
    simp [List.getD_eq_getElem?_getD]
   have e2:(coneStep n (gs.foldl (coneStep n) []) g).getD gs.length [] =
     (g.inputs.filter (fun w=>decide (n ≤ w∧ w < n + gs.length))).flatMap
      (fun w=>(w - n)::(gs.foldl (coneStep n) []).getD (w - n) []):=by
    simp only [coneStep,List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_right (by omega)]
    simp [q06]
   rw [e2,e1]
   simp only [List.mem_flatMap,List.mem_filter,List.mem_cons,decide_eq_true_eq]
   constructor
   ·rintro ⟨w,⟨hw,h1,h2⟩,h3⟩
    refine ⟨by simp,w,hw,h1,h2,?_⟩
    rw [key (w - n) (by omega)]
    exact h3
   ·rintro ⟨_,w,hw,h1,h2,h3⟩
    rw [key (w - n) (by omega)] at h3
    exact ⟨w,⟨hw,h1,h2⟩,h3⟩
  ·have e0:(coneStep n (gs.foldl (coneStep n) []) g).getD j [] = []:=by
    simp only [coneStep,List.getD_eq_getElem?_getD]
    rw [List.getElem?_eq_none (by simp;omega)]
    rfl
   rw [e0]
   constructor
   ·intro h0;simp at h0
   ·rintro ⟨h0,_⟩
    simp at h0
    omega
lemma d2n (n:ℕ) (C:Circuit) (i j:ℕ):
  InCone n C i j↔ j < C.gates.length∧ ∃ k,k < j∧ n + k ∈ (gateAt C j).inputs∧ 
   (i = k∨ InCone n C i k):=by
 have h:=d0w n C.gates i j
 unfold InCone cones gateAt
 rw [h]
 constructor
 ·rintro ⟨h0,w,hw,h1,h2,h3⟩
  refine ⟨h0,w - n,by omega,?_,h3⟩
  have:n + (w - n) = w:=by omega
  rw [this]
  exact hw
 ·rintro ⟨h0,k,hk,hw,h3⟩
  refine ⟨h0,n + k,hw,by omega,by omega,?_⟩
  have:n + k - n = k:=by omega
  rw [this]
  exact h3
lemma d3y {n:ℕ} {C:Circuit} {w w':ℕ}
  (h:Relation.ReflTransGen (d04 n C) w w'):w' ≤ w:=by
 induction h using Relation.ReflTransGen.head_induction_on with
 | refl=>exact le_rfl
 | head q05 _ ih=>
  obtain ⟨k,_,rfl,_,_,hlt⟩:=q05
  omega
lemma d3w {n:ℕ} {C:Circuit} {w w':ℕ}
  (h:Relation.ReflTransGen (d04 n C) w w'):
  ∀ k h',w = n + k→ w' = n + h'→ h' = k∨ InCone n C h' k:=by
 induction h using Relation.ReflTransGen.head_induction_on with
 | refl=>intro k h' h1 h2;left;omega
 | @head a c q05 q1p ih=>
  intro k h' h1 h2
  obtain ⟨k0,hk0,e,_,hin,hlt⟩:=q05
  have hk:k0 = k:=by omega
  subst hk
  have hle:=d3y q1p
  obtain ⟨k1,hk1⟩:∃ k1,c = n + k1:=⟨c - n,by omega⟩
  subst hk1
  right
  rw [d2n]
  exact ⟨hk0,k1,by omega,hin,ih k1 h' rfl h2⟩
lemma d3i {n:ℕ} {C:Circuit} {a p h:ℕ} (ha:a < C.gates.length)
  (hin:p ∈ (gateAt C a).inputs) (hp:p < n + a)
  (hr:Relation.ReflTransGen (d04 n C) p (n + h)):InCone n C h a:=by
 have hle:=d3y hr
 obtain ⟨k1,rfl⟩:∃ k1,p = n + k1:=⟨p - n,by omega⟩
 rw [d2n]
 exact ⟨ha,k1,by omega,hin,d3w hr k1 h rfl rfl⟩
lemma d3u (n:ℕ) (gs:List Gate) (cs:List (List ℕ)):
  (gs.foldl (orStep n) cs).length = cs.length + gs.length:=by
 induction gs generalizing cs with
 | nil=>simp
 | cons g gs ih=>
  rw [List.foldl_cons,ih]
  simp [orStep]
  omega
lemma d3t (n:ℕ) (gs:List Gate):
  ∀ i j,i ∈ (gs.foldl (orStep n) []).getD j []↔ 
   j < gs.length∧ (i = j∨ ((gs.getD j ⟨GateOp.or,[]⟩).op = GateOp.or∧ 
    ∃ w ∈ (gs.getD j ⟨GateOp.or,[]⟩).inputs,n ≤ w∧ w < n + j∧ 
     i ∈ (gs.foldl (orStep n) []).getD (w - n) [])):=by
 induction gs using List.reverseRecOn with
 | nil=>intro i j;simp
 | append_singleton gs g ih=>
  intro i j
  rw [List.foldl_append,List.foldl_cons,List.foldl_nil]
  have q06:(gs.foldl (orStep n) []).length = gs.length:=by
   rw [d3u];simp
  have key:∀ k,k < gs.length→ 
    (orStep n (gs.foldl (orStep n) []) g).getD k [] =
     (gs.foldl (orStep n) []).getD k []:=by
   intro k hk
   simp only [orStep,List.getD_eq_getElem?_getD]
   rw [List.getElem?_append_left (by omega)]
  rcases Nat.lt_trichotomy j gs.length with h | h | h
  ·have e1:(gs ++ [g]).getD j ⟨GateOp.or,[]⟩ = gs.getD j ⟨GateOp.or,[]⟩:=by
    simp only [List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_left h]
   rw [key j h,ih i j,e1]
   constructor
   ·rintro ⟨_,h3⟩
    refine ⟨by simp;omega,?_⟩
    rcases h3 with h3 | ⟨hop,w,hw,h1,h2,h3⟩
    ·exact Or.inl h3
    ·refine Or.inr ⟨hop,w,hw,h1,h2,?_⟩
     rw [key (w - n) (by omega)]
     exact h3
   ·rintro ⟨_,h3⟩
    refine ⟨h,?_⟩
    rcases h3 with h3 | ⟨hop,w,hw,h1,h2,h3⟩
    ·exact Or.inl h3
    ·rw [key (w - n) (by omega)] at h3
     exact Or.inr ⟨hop,w,hw,h1,h2,h3⟩
  ·subst h
   have e1:(gs ++ [g]).getD gs.length ⟨GateOp.or,[]⟩ = g:=by
    simp [List.getD_eq_getElem?_getD]
   rw [e1]
   by_cases hop:g.op = GateOp.or
   ·have e2:(orStep n (gs.foldl (orStep n) []) g).getD gs.length [] =
      gs.length::(g.inputs.filter (fun w=>decide (n ≤ w∧ w < n + gs.length))).flatMap
       (fun w=>(gs.foldl (orStep n) []).getD (w - n) []):=by
     simp only [orStep,List.getD_eq_getElem?_getD]
     rw [List.getElem?_append_right (by omega)]
     simp [q06,hop]
    rw [e2]
    simp only [List.mem_cons,List.mem_flatMap,List.mem_filter,decide_eq_true_eq]
    constructor
    ·rintro (h3 | ⟨w,⟨hw,h1,h2⟩,h3⟩)
     ·exact ⟨by simp,Or.inl h3⟩
     ·refine ⟨by simp,Or.inr ⟨hop,w,hw,h1,h2,?_⟩⟩
      rw [key (w - n) (by omega)]
      exact h3
    ·rintro ⟨_,h3 | ⟨_,w,hw,h1,h2,h3⟩⟩
     ·exact Or.inl h3
     ·rw [key (w - n) (by omega)] at h3
      exact Or.inr ⟨w,⟨hw,h1,h2⟩,h3⟩
   ·have e2:(orStep n (gs.foldl (orStep n) []) g).getD gs.length [] = [gs.length]:=by
     simp only [orStep,List.getD_eq_getElem?_getD]
     rw [List.getElem?_append_right (by omega)]
     simp [q06,hop]
    rw [e2]
    simp only [List.mem_singleton]
    constructor
    ·intro h3
     exact ⟨by simp,Or.inl h3⟩
    ·rintro ⟨_,h3 | ⟨q3c,_⟩⟩
     ·exact h3
     ·exact (hop q3c).elim
  ·have e0:(orStep n (gs.foldl (orStep n) []) g).getD j [] = []:=by
    simp only [orStep,List.getD_eq_getElem?_getD]
    rw [List.getElem?_eq_none (by simp;omega)]
    rfl
   rw [e0]
   constructor
   ·intro h0;simp at h0
   ·rintro ⟨h0,_⟩
    simp at h0
    omega
lemma d3r (n:ℕ) (C:Circuit) (k g:ℕ):
  OrReaches n C (n + k) g↔ k < C.gates.length∧ (g = k∨ ((gateAt C k).op = GateOp.or∧ 
   ∃ i ∈ (gateAt C k).inputs,i < n + k∧ OrReaches n C i g)):=by
 have h:=d3t n C.gates g k
 unfold OrReaches orSets gateAt
 have e:n + k - n = k:=by omega
 rw [e,h]
 constructor
 ·rintro ⟨_,hk,h3⟩
  refine ⟨hk,?_⟩
  rcases h3 with h3 | ⟨hop,w,hw,h1,h2,h3⟩
  ·exact Or.inl h3
  ·exact Or.inr ⟨hop,w,hw,h2,h1,h3⟩
 ·rintro ⟨hk,h3⟩
  refine ⟨by omega,hk,?_⟩
  rcases h3 with h3 | ⟨hop,w,hw,h2,h1,h3⟩
  ·exact Or.inl h3
  ·exact Or.inr ⟨hop,w,hw,h1,h2,h3⟩
lemma d4f {n:ℕ} {C:Circuit} {w w2:ℕ}
  (h:Relation.ReflTransGen (d04 n C) w w2):
  ∀ g,w2 = n + g→ g < C.gates.length→ OrReaches n C w g:=by
 induction h using Relation.ReflTransGen.head_induction_on with
 | refl=>
  intro g h1 hg
  subst h1
  exact (d3r n C g g).mpr ⟨hg,Or.inl rfl⟩
 | @head a c q05 q1p ih=>
  intro g h1 hg
  obtain ⟨k,hk,rfl,hop,hin,hlt⟩:=q05
  exact (d3r n C k g).mpr ⟨hk,Or.inr ⟨hop,c,hin,hlt,ih g h1 hg⟩⟩
lemma d3s {n:ℕ} {C:Circuit} (g:ℕ):
  ∀ w,OrReaches n C w g→ 
   Relation.ReflTransGen (d04 n C) w (n + g)∧ g < C.gates.length:=by
 intro w
 induction w using Nat.strong_induction_on with
 | _ w ih=>
  intro h
  have hnw:n ≤ w:=h.1
  obtain ⟨k,rfl⟩:∃ k,w = n + k:=⟨w - n,by omega⟩
  obtain ⟨hk,h3⟩:=(d3r n C k g).mp h
  rcases h3 with rfl | ⟨hop,i,hi,hlt,hr⟩
  ·exact ⟨Relation.ReflTransGen.refl,hk⟩
  ·obtain ⟨hr2,hg⟩:=ih i hlt hr
   exact ⟨Relation.ReflTransGen.head ⟨k,hk,rfl,hop,hi,hlt⟩ hr2,hg⟩
lemma d32 {n:ℕ} {C:Circuit} {p:ℕ} (u:Fin n)
  (hu:u ∈ PEqualNP.TopForm.orIn n C p):
  Relation.ReflTransGen (d04 n C) p u.val:=by
 simp only [PEqualNP.TopForm.orIn,Finset.mem_filter,Finset.mem_univ,true_and] at hu
 rcases hu with h | ⟨k,hk,hr,hop,hin⟩
 ·rw [h]
 ·exact (d3s k p hr).1.tail ⟨k,hk,rfl,hop,hin,by omega⟩
lemma d4e {n:ℕ} {C:Circuit} {p:ℕ} (u:Fin n)
  (hr:Relation.ReflTransGen (d04 n C) p u.val):
  u ∈ PEqualNP.TopForm.orIn n C p:=by
 simp only [PEqualNP.TopForm.orIn,Finset.mem_filter,Finset.mem_univ,true_and]
 rcases Relation.ReflTransGen.cases_tail hr with h | ⟨c,hpc,q05⟩
 ·exact Or.inl h
 ·obtain ⟨k,hk,rfl,hop,hin,_⟩:=q05
  exact Or.inr ⟨k,hk,d4f hpc k rfl hk,hop,hin⟩
variable {n:ℕ} {G:SimpleGraph (Fin n)} [DecidableRel G.Adj] {C:Circuit}
lemma d5e {a:ℕ} (ha:a ∈ tops G C):
  a < C.gates.length∧ (gateAt C a).op = GateOp.and∧ BelowF G C a:=by
 simpa only [tops,gatesWhere,Finset.mem_filter,Finset.mem_range] using ha
lemma d2q {a:ℕ} (ha:a ∈ junk G C):
  a < C.gates.length∧ (gateAt C a).op = GateOp.and∧ 
   ∃ x:Fin n→ Bool,gateVal n C a x = true∧ graphFun G ∅ x = false:=by
 rcases Finset.mem_filter.mp ha with ⟨hr,hop,hal,hd⟩
 exact ⟨hal,hop,hd⟩
lemma d0h (hAO:IsAO2 n C) {a:ℕ} (ha:a < C.gates.length):
  ∃ p q,(gateAt C a).inputs = [p,q]:=
 List.length_eq_two.mp (hAO.2.2 _ (d23 ha))
lemma d3l (hAO:IsAO2 n C) {a:ℕ} (ha:a < C.gates.length) (b:Fin 2):
  opnd C a b ∈ (gateAt C a).inputs:=by
 obtain ⟨p,q,hpq⟩:=d0h hAO ha
 fin_cases b <;> simp [opnd,hpq]
lemma d3k (hAO:IsAO2 n C) {a:ℕ} (ha:a < C.gates.length) (b:Fin 2):
  opnd C a b < n + a:=
 hAO.2.1 a ha _ (d3l hAO ha b)
lemma d0c (hAO:IsAO2 n C) {a:ℕ} (ha:a < C.gates.length)
  (hop:(gateAt C a).op = GateOp.and) (x:Fin n→ Bool):
  gateVal n C a x = true↔ 
   val C (List.ofFn x) (opnd C a 0) = true∧ 
   val C (List.ofFn x) (opnd C a 1) = true:=by
 rw [d2c,d5r (n:=n) (by simp) ha hop]
 constructor
 ·intro h
  exact ⟨(h _ (d3l hAO ha 0)).2,(h _ (d3l hAO ha 1)).2⟩
 ·intro h i hi
  refine ⟨hAO.2.1 a ha i hi,?_⟩
  obtain ⟨p,q,hpq⟩:=d0h hAO ha
  rcases List.mem_cons.mp (hpq ▸ hi) with rfl | hq
  ·simpa [opnd,hpq] using h.1
  ·have e:i = q:=List.mem_singleton.mp hq
   subst i
   simpa [opnd,hpq] using h.2
lemma d0d (hAO:IsAO2 n C) {a:ℕ} (ha:a < C.gates.length)
  (hop:(gateAt C a).op = GateOp.and) (x:Fin n→ Bool):
  gateVal n C a x = true↔ ∀ b:Fin 2,val C (List.ofFn x) (opnd C a b) = true:=by
 rw [d0c hAO ha hop]
 constructor
 ·intro h b
  fin_cases b
  ·exact h.1
  ·exact h.2
 ·intro h
  exact ⟨h 0,h 1⟩
lemma d3g (hAO:IsAO2 n C) {a h:ℕ} (ha:a < C.gates.length)
  {b:Fin 2} (hr:OrReaches n C (opnd C a b) h):
  InCone n C h a:=
 d3i ha (d3l hAO ha b) (d3k hAO ha b)
  (d3s h _ hr).1
lemma d3f (hAO:IsAO2 n C) (hT:TopForm G C) {a h:ℕ}
  (ha:a < C.gates.length) (hop:(gateAt C a).op = GateOp.and)
  {b:Fin 2} (hr:OrReaches n C (opnd C a b) h)
  (hh:(gateAt C h).op = GateOp.and):h ∈ junk G C:=by
 have q06:=(d3s h _ hr).2
 have hnb:¬ BelowF G C h:=
  fun hb=>hT h q06 a ha hh hb hop (d3g hAO ha hr)
 have q1q:∃ x:Fin n→ Bool,gateVal n C h x = true∧ graphFun G ∅ x = false:=by
  by_contra hne
  apply hnb
  intro x hx
  by_contra hf
  exact hne ⟨x,hx,Bool.eq_false_iff.mpr hf⟩
 exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr q06,hh,q06,q1q⟩
lemma d2o (hAO:IsAO2 n C) {m z:ℕ} (hm:m < C.gates.length)
  (hz:z ∈ (gateAt C m).inputs):∃ b:Fin 2,z = opnd C m b:=by
 obtain ⟨p,q,hpq⟩:=d0h hAO hm
 rcases List.mem_cons.mp (hpq ▸ hz) with rfl | hq
 ·exact ⟨0,by simp [opnd,hpq]⟩
 ·have e:z = q:=List.mem_singleton.mp hq
  exact ⟨1,by simpa [opnd,hpq] using e⟩
lemma d54 {a:ℕ} {b:Fin 2} {x:Fin n→ Bool} {t:Fin n}
  (ht:t ∈ side (n:=n) C a b) (hx:x t = true):
  val C (List.ofFn x) (opnd C a b) = true:=
 d4i x _ t (d32 t ht) hx
lemma d0a (hAO:IsAO2 n C) {a:ℕ} (ha:a < C.gates.length)
  (hop:(gateAt C a).op = GateOp.and) {x:Fin n→ Bool}
  {u v:Fin n} (hu:u ∈ side (n:=n) C a 0) (hv:v ∈ side (n:=n) C a 1)
  (xu:x u = true) (xv:x v = true):gateVal n C a x = true:=
 (d0c hAO ha hop x).mpr ⟨d54 hu xu,d54 hv xv⟩
lemma d5d (hAO:IsAO2 n C) {a:ℕ} (ha:a ∈ tops G C)
  {u v:Fin n} (hu:u ∈ side (n:=n) C a 0) (hv:v ∈ side (n:=n) C a 1):
  G.Adj u v:=by
 obtain ⟨hl,ho,hb⟩:=d5e ha
 exact (d2i G u v).mp
  (hb _ (d0a hAO hl ho hu hv (d46 u v) (d47 u v)))
lemma d09 (hL:IsLeastAO G C) {u v:Fin n} (q0q:G.Adj u v):
  ∃ a ∈ tops G C,gateVal n C a (pairInput u v) = true:=by
 have q08 (x:Fin n→ Bool):val C (List.ofFn x) C.output = graphFun G ∅ x:=
  congrFun hL.2.1 x
 obtain ⟨a,hl,ho,hr,hv⟩:=
  d1n G (graphFun G ∅) (fun k l=>(d2i G k l).mp)
   q08 u v ((d2i G u v).mpr q0q)
 have q0j:=(hL.1.1 _ (d23 hl)).resolve_right ho
 have hb:BelowF G C a:=fun x hx=>
  d0g (graphFun G ∅) q08 a hr x (d2c n C a x ▸ hx)
 refine ⟨a,?_,hv⟩
 simpa only [tops,gatesWhere,Finset.mem_filter,Finset.mem_range] using
  And.intro hl (And.intro q0j hb)
lemma d3h (hAO:IsAO2 n C) (hT:TopForm G C) {a:ℕ}
  (ha:a < C.gates.length) (ho:(gateAt C a).op = GateOp.and) {b:Fin 2}
  {u v:Fin n} (h:val C (List.ofFn (pairInput u v)) (opnd C a b) = true):
  (∃ t ∈ side (n:=n) C a b,t = u∨ t = v)∨ 
   ∃ j ∈ junk G C,OrReaches n C (opnd C a b) j∧ 
    gateVal n C j (pairInput u v) = true:=by
 rcases d3j (C:=C) u v _ h with ⟨t,ht,hr⟩ | ⟨j,hj,hn,hr,hv⟩
 ·exact .inl ⟨t,d4e t hr,ht⟩
 ·have hr':=d4f hr j rfl hj
  exact .inr ⟨j,d3f hAO hT ha ho hr'
   ((hAO.1 _ (d23 hj)).resolve_right hn),hr',hv⟩
lemma d0b {j:ℕ} (hj:(gateAt C j).op = GateOp.and):
  orIn n C (n + j) = ∅:=by
 apply Finset.eq_empty_iff_forall_notMem.mpr
 intro v hv
 simp only [orIn,Finset.mem_filter,Finset.mem_univ,true_and] at hv
 rcases hv with he | ⟨k,_,hr,ho,_⟩
 ·have:=v.isLt
  omega
 ·rcases (d3r n C j k).mp hr with ⟨_,he | ⟨hof,_⟩⟩
  ·subst k
   rw [hj] at ho
   cases ho
  ·rw [hj] at hof
   cases hof
lemma d2u {j w:ℕ} (hr:Relation.ReflTransGen (d04 n C) w (n + j)):
  w = n + j∨ ∃ m,m < C.gates.length∧ (gateAt C m).op = GateOp.or∧ 
   n + j ∈ (gateAt C m).inputs∧ n + j < n + m∧ 
   Relation.ReflTransGen (d04 n C) w (n + m):=by
 rcases Relation.ReflTransGen.cases_tail hr with eq | ⟨z,hz,q05⟩
 ·exact .inl eq.symm
 ·obtain ⟨m,hm,rfl,ho,hi,hb⟩:=q05
  exact .inr ⟨m,hm,ho,hi,hb,hz⟩
lemma d4q (hL:IsLeastAO G C) (hT:TopForm G C) {u v:Fin n}
  (he:s(u,v) ∈ Ustar G C):
  ∃ a ∈ tops G C,∃ b:Fin 2,∃ j ∈ junk G C,
   OrReaches n C (opnd C a b) j∧ gateVal n C j (pairInput u v) = true:=by
 obtain ⟨adj,miss⟩:=Finset.mem_sdiff.mp he
 have adj':G.Adj u v:=SimpleGraph.mem_edgeFinset.mp adj
 obtain ⟨a,ha,hv⟩:=d09 hL adj'
 obtain ⟨hl,ho,_⟩:=d5e ha
 have h:=(d0d hL.1 hl ho _).mp hv
 rcases d3h hL.1 hT hl ho (b:=0) (h 0) with ⟨x,hx,hex⟩ | ⟨j,hj,hr,hjv⟩
 ·rcases d3h hL.1 hT hl ho (b:=1) (h 1) with ⟨y,hy,hey⟩ | ⟨j,hj,hr,hjv⟩
  ·have hxy:x ≠ y:=(d5d hL.1 ha hx hy).ne
   apply (miss ?_).elim
   unfold starEdges
   refine Finset.mem_biUnion.mpr ⟨a,ha,Finset.mem_image.mpr
    ⟨(x,y),Finset.mem_product.mpr ⟨hx,hy⟩,?_⟩⟩
   rcases hex with rfl | rfl <;> rcases hey with rfl | rfl
   ·exact (hxy rfl).elim
   ·rfl
   ·exact Sym2.eq_swap
   ·exact (hxy rfl).elim
  ·exact ⟨a,ha,1,j,hj,hr,hjv⟩
 ·exact ⟨a,ha,0,j,hj,hr,hjv⟩
lemma d4j {j k:ℕ} (h:k ∈ readers n C j):
  k < C.gates.length∧ n + j ∈ (gateAt C k).inputs:=by
 simpa only [readers,Finset.mem_filter,Finset.mem_range] using h
lemma d4k (hAO:IsAO2 n C) {j k:ℕ} (h:k ∈ readers n C j):j < k:=by
 have hlt:=hAO.2.1 k (d4j h).1 _ (d4j h).2
 omega
lemma d2r {j:ℕ} (hj:j ∈ junk G C):¬ BelowF G C j:=by
 obtain ⟨_,_,x,hx,hf⟩:=d2q hj
 intro h
 exact Bool.false_ne_true (hf.symm.trans (h x hx))
lemma d2v (hL:IsLeastAO G C) {j:ℕ} (hj:j < C.gates.length)
  (hd:¬ BelowF G C j):(readers n C j).Nonempty:=by
 have q08:C.output ≠ n + j:=by
  intro heq
  apply hd
  intro x hx
  have h:val C (List.ofFn x) C.output = graphFun G ∅ x:=congrFun hL.2.1 x
  rw [heq] at h
  exact h.symm.trans hx
 obtain ⟨k,hk,hin⟩:=d4l hL.1
  (fun D hD heq=>hL.2.2 D hD (heq.trans hL.2.1)) hj q08
 exact ⟨k,Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hk,hin⟩⟩
lemma d1o {a:ℕ} (ha:a ∈ tops G C) {b:Fin 2}
  (h:side (n:=n) C a b = ∅):a ∈ centreless G C:=by
 apply Finset.mem_filter.mpr
 refine ⟨ha,?_⟩
 fin_cases b
 ·exact Or.inl h
 ·exact Or.inr h
lemma d0m (hAO:IsAO2 n C) (hE:centreless G C = ∅) {j k:ℕ}
  (hd:¬ BelowF G C j) (hz:orIn n C (n + j) = ∅) (hr:k ∈ readers n C j):
  k ∈ junk G C∨ k ∈ orN G C \ lam G C:=by
 obtain ⟨hk,hin⟩:=d4j hr
 obtain ⟨b,hb⟩:=d2o hAO hk hin
 have hs:side (n:=n) C k b = ∅:=by
  change orIn n C (opnd C k b) = ∅
  rwa [← hb]
 rcases hAO.1 _ (d23 hk) with q0j | hor
 ·left
  have hnb:¬ BelowF G C k:=by
   intro q03
   have ht:k ∈ tops G C:=by
    simpa only [tops,gatesWhere,Finset.mem_filter,Finset.mem_range] using
     And.intro hk (And.intro q0j q03)
   have q37:=d1o ht hs
   rw [hE] at q37
   exact Finset.notMem_empty _ q37
  have hw:∃ x:Fin n→ Bool,gateVal n C k x = true∧ graphFun G ∅ x = false:=by
   by_contra q18
   apply hnb
   intro x hx
   by_contra hf
   exact q18 ⟨x,hx,Bool.eq_false_iff.mpr hf⟩
  exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hk,q0j,hk,hw⟩
 ·right
  have hnb:¬ BelowF G C k:=by
   intro q03
   apply hd
   intro x hx
   exact q03 x ((d5x (n:=n) (by simp) hk hor).mpr
    ⟨_,hin,hAO.2.1 k hk _ hin,hx⟩)
  refine Finset.mem_sdiff.mpr ⟨?_,?_⟩
  ·simpa only [orN,gatesWhere,Finset.mem_filter,Finset.mem_range] using
    And.intro hk (And.intro hor hnb)
  ·intro q3d
   obtain ⟨_,h0,h1,_⟩:=Finset.mem_filter.mp q3d
   have hn:(orIn n C (opnd C k b)).Nonempty:=by
    fin_cases b
    ·exact h0
    ·exact h1
   rw [← hb,hz] at hn
   exact Finset.not_nonempty_empty hn
lemma d3m {m:ℕ} (h:∀ w ∈ (gateAt C m).inputs,orIn n C w = ∅):
  orIn n C (n + m) = ∅:=by
 apply Finset.eq_empty_iff_forall_notMem.mpr
 intro u hu
 rcases Relation.ReflTransGen.cases_head (d32 u hu) with he | ⟨w,hw,tail⟩
 ·have:=u.isLt
  omega
 ·obtain ⟨k,_,he,_,hi,_⟩:=hw
  have e:k = m:=by omega
  subst k
  have hu':=d4e u tail
  rw [h w hi] at hu'
  exact Finset.notMem_empty _ hu'
lemma d5i (hAO:IsAO2 n C) {m p q:ℕ} (hm:m < C.gates.length)
  (hpq:p ≠ q) (hp:p ∈ (gateAt C m).inputs) (hq:q ∈ (gateAt C m).inputs)
  {w:ℕ} (hw:w ∈ (gateAt C m).inputs):w = p∨ w = q:=by
 obtain ⟨r,s,hrs⟩:=d0h hAO hm
 simp only [hrs,List.mem_cons,List.not_mem_nil,or_false] at hp hq hw
 omega
lemma d1h (hL:IsLeastAO G C) (hT:TopForm G C) (hJ:(junk G C).card = 2):
  2 ≤ 2 * (centreless G C).card + (orN G C \ lam G C).card∨ 
   ∃ a b m:ℕ,junk G C = {a,b}∧ InCone n C a b∧ centreless G C = ∅∧ 
    readers n C a = {b}∧ readers n C b = {m}∧ orN G C \ lam G C = {m}∧ 
    ∀ u v:Fin n,s(u,v) ∈ Ustar G C→ 
     gateVal n C a (pairInput u v) = true∧ gateVal n C b (pairInput u v) = true:=by
 by_cases h:2 ≤ 2 * (centreless G C).card + (orN G C \ lam G C).card
 ·exact Or.inl h
 right
 have hE:centreless G C = ∅:=Finset.card_eq_zero.mp (by omega)
 have q1r:(orN G C \ lam G C).card ≤ 1:=by omega
 obtain ⟨a,b,hab,q0o⟩:∃ a b:ℕ,a < b∧ junk G C = {a,b}:=by
  obtain ⟨i,j,hij,he⟩:=Finset.card_eq_two.mp hJ
  rcases lt_or_gt_of_ne hij with hlt | hlt
  ·exact ⟨i,j,hlt,he⟩
  ·exact ⟨j,i,hlt,he.trans (Finset.pair_comm _ _)⟩
 have ha:a ∈ junk G C:=by simp [q0o]
 have hb:b ∈ junk G C:=by simp [q0o]
 have noLaterJunk {k:ℕ} (hk:k ∈ junk G C) (hlt:b < k):False:=by
  simp only [q0o,Finset.mem_insert,Finset.mem_singleton] at hk
  omega
 have junkReader {j k:ℕ} (hj:j ∈ junk G C) (hr:k ∈ readers n C j):
   k ∈ junk G C∨ k ∈ orN G C \ lam G C:=
  d0m hL.1 hE (d2r hj) (d0b (d2q hj).2.1) hr
 obtain ⟨m,hbm⟩:=d2v hL (d2q hb).1 (d2r hb)
 have q1s:=d4k hL.1 hbm
 have hm:=(junkReader hb hbm).resolve_left (fun hk=>noLaterJunk hk q1s)
 have mUnique {k:ℕ} (hk:k ∈ orN G C \ lam G C):k = m:=
  Finset.card_le_one.mp q1r k hk m hm
 have hM:orN G C \ lam G C = {m}:=by
  ext k
  exact ⟨fun hk=>Finset.mem_singleton.mpr (mUnique hk),
   fun hk=>Finset.mem_singleton.mp hk ▸ hm⟩
 have hB:readers n C b = {m}:=by
  ext k
  refine ⟨fun hk=>Finset.mem_singleton.mpr (mUnique ?_),
   fun hk=>Finset.mem_singleton.mp hk ▸ hbm⟩
  exact (junkReader hb hk).resolve_left (fun hj=>noLaterJunk hj (d4k hL.1 hk))
 have noAM (ham:m ∈ readers n C a):False:=by
  have q0k:m < C.gates.length∧ (gateAt C m).op = GateOp.or∧ ¬ BelowF G C m:=by
   simpa only [orN,gatesWhere,Finset.mem_filter,Finset.mem_range] using (Finset.mem_sdiff.mp hm).1
  have q19:orIn n C (n + m) = ∅:=by
   apply d3m
   intro w hw
   rcases d5i hL.1 q0k.1 (show n + a ≠ n + b by omega)
     (d4j ham).2 (d4j hbm).2 hw with rfl | rfl
   ·exact d0b (d2q ha).2.1
   ·exact d0b (d2q hb).2.1
  obtain ⟨k,hmk⟩:=d2v hL q0k.1 q0k.2.2
  have q2e:=d4k hL.1 hmk
  rcases d0m hL.1 hE q0k.2.2 q19 hmk with hk | hk
  ·exact noLaterJunk hk (q1s.trans q2e)
  ·have:=mUnique hk
   omega
 have aRead {k:ℕ} (hk:k ∈ readers n C a):k = b:=by
  rcases junkReader ha hk with hj | hj
  ·have hlt:=d4k hL.1 hk
   simp only [q0o,Finset.mem_insert,Finset.mem_singleton] at hj
   omega
  ·exact (noAM (mUnique hj ▸ hk)).elim
 obtain ⟨k,hak⟩:=d2v hL (d2q ha).1 (d2r ha)
 have q0b:b ∈ readers n C a:=aRead hak ▸ hak
 have hA:readers n C a = {b}:=by
  ext i
  exact ⟨fun hi=>Finset.mem_singleton.mpr (aRead hi),
   fun hi=>Finset.mem_singleton.mp hi ▸ q0b⟩
 have q1a:InCone n C a b:=(d2n n C a b).mpr
  ⟨(d4j q0b).1,a,hab,(d4j q0b).2,Or.inl rfl⟩
 refine ⟨a,b,m,q0o,q1a,hE,hA,hB,hM,?_⟩
 intro u v he
 obtain ⟨t,ht,d,j,hj,path,hv⟩:=d4q hL hT he
 have hjb:j = b:=by
  simp only [q0o,Finset.mem_insert,Finset.mem_singleton] at hj
  rcases hj with h | h
  ·exfalso
   subst j
   rcases d2u (d3s a _ path).1 with heq | ⟨r,hr,hop,hin,_,_⟩
   ·have hs:side (n:=n) C t d = ∅:=by
     change orIn n C (opnd C t d) = ∅
     rw [heq]
     exact d0b (d2q ha).2.1
    have q1t:=d1o ht hs
    rw [hE] at q1t
    exact Finset.notMem_empty _ q1t
   ·have hr':r ∈ readers n C a:=Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hr,hin⟩
    rw [aRead hr',(d2q hb).2.1] at hop
    cases hop
  ·exact h
 subst j
 have q2f:=(d5r (n:=n) (by simp) (d2q hb).1 (d2q hb).2.1).mp hv
  (n + a) (d4j q0b).2
 exact ⟨q2f.2,hv⟩
end TightSupport.Budget
namespace TightSupport
open PEqualNP.EdgeOwnership
def d4z {n:ℕ} (A:Finset (Fin n)) (x:Fin n→ Bool):Bool:=
 decide (∃ a ∈ A,x a = true)
lemma d50 {n:ℕ} (A:Finset (Fin n)) (u v:Fin n):
  d4z A (pairInput u v) = decide (u ∈ A∨ v ∈ A):=by
 simp [d4z,pairInput,and_or_left,exists_or]
def d01 {n:ℕ} (f:(Fin n→ Bool)→ Bool):Prop:=
 ∀ x y,(∀ v,x v = true→ y v = true)→ f x = true→ f y = true
lemma d2k {n:ℕ} (G:SimpleGraph (Fin n)) [DecidableRel G.Adj]
  (f:(Fin n→ Bool)→ Bool) (hf:d01 f)
  (q03:∀ x,f x = true→ PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ x = true)
  (q1u:∀ u v,G.Adj u v→ f (pairInput u v) = true):
  f = PEqualNP.MetaComplexity.NestedCover.graphFun G ∅:=by
 funext x
 apply Bool.eq_iff_iff.mpr
 refine ⟨q03 x,?_⟩
 intro h
 simp only [PEqualNP.MetaComplexity.NestedCover.graphFun,Finset.notMem_empty,
  false_and,exists_false,decide_false,Bool.false_or,decide_eq_true_eq] at h
 obtain ⟨u,v,huv,hu,hv⟩:=h
 apply hf (pairInput u v) x ?_ (q1u u v huv)
 intro w hw
 simp only [pairInput,decide_eq_true_eq] at hw
 rcases hw with rfl | rfl
 ·exact hu
 ·exact hv
lemma d0p {α:Type*} (F H K:α→ Bool) (context:α→ Bool→ Bool)
  (q00:∀ x b c,(b = true→ c = true)→ 
   context x b = true→ context x c = true)
  (hK:∀ x,K x = true→ F x = true)
  (q2g:∀ x,context x (H x) = true→ F x = true):
  ∀ x,context x (K x) = true→ F x = true:=by
 intro x hx
 by_cases hk:K x = true
 ·exact hK x hk
 ·apply q2g x
  exact q00 x (K x) (H x) (fun h=>(hk h).elim) hx
lemma d0q {n:ℕ} (G:SimpleGraph (Fin n)) [DecidableRel G.Adj]
  (context:(Fin n→ Bool)→ Bool→ Bool) (H K:(Fin n→ Bool)→ Bool)
  (q00:∀ x y b c,(∀ v,x v = true→ y v = true)→ 
   (b = true→ c = true)→ context x b = true→ context y c = true)
  (q1v:d01 K)
  (q1b:∀ x,K x = true→ PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ x = true)
  (q0s:∀ u v,G.Adj u v→ context (pairInput u v) false = false→ 
   K (pairInput u v) = true)
  (hF:∀ x,context x (H x) = PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ x):
  (fun x=>context x (K x)) = PEqualNP.MetaComplexity.NestedCover.graphFun G ∅:=by
 apply d2k G
 ·intro x y hxy hx
  exact q00 x y (K x) (K y) hxy (q1v x y hxy) hx
 ·exact d0p _ H K context
   (fun x b c=>q00 x x b c (fun _=>id)) q1b
   (fun x hx=>(hF x).symm ▸ hx)
 ·intro u v huv
  have q2h:PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ (pairInput u v) = true:=by
   simp only [PEqualNP.MetaComplexity.NestedCover.graphFun,Bool.or_eq_true,
    decide_eq_true_eq]
   right
   exact ⟨u,v,huv,by simp [pairInput],by simp [pairInput]⟩
  by_cases hz:context (pairInput u v) false = true
  ·exact q00 _ _ false (K (pairInput u v)) (fun _=>id)
    (fun h=>Bool.false_ne_true h |>.elim) hz
  ·have hk:=q0s u v huv (Bool.eq_false_iff.mpr hz)
   have q2g:context (pairInput u v) (H (pairInput u v)) = true:=
    (hF (pairInput u v)).trans q2h
   exact q00 _ _ (H (pairInput u v)) (K (pairInput u v))
    (fun _=>id) (fun _=>hk) q2g
lemma d2l {n:ℕ} (G:SimpleGraph (Fin n)) [DecidableRel G.Adj]
  (u v:Fin n):
  PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ (pairInput u v) = true↔ G.Adj u v:=by
 simp only [PEqualNP.MetaComplexity.NestedCover.graphFun,Finset.notMem_empty,
  false_and,exists_false,decide_false,Bool.false_or,decide_eq_true_eq,pairInput]
 constructor
 ·rintro ⟨a,b,hab,ha,hb⟩
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
  ·exact (G.irrefl hab).elim
  ·exact hab
  ·exact hab.symm
  ·exact (G.irrefl hab).elim
 ·intro h
  exact ⟨u,v,h,Or.inl rfl,Or.inr rfl⟩
lemma d51 {n:ℕ} (G:SimpleGraph (Fin n)) [DecidableRel G.Adj]
  (H:(Fin n→ Bool)→ Bool) (R S:Finset (Fin n)) (r u v:Fin n)
  (hr:r ∈ R)
  (q01:∀ x,((d4z R x || H x) && d4z S x) = true→ 
   PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ x = true)
  (hR:d4z R (pairInput u v) = false)
  (hS:d4z S (pairInput u v) = true):
  r ≠ u∧ r ≠ v∧ ∃ w:Fin n,(w = u∨ w = v)∧ G.Adj r w∧ 
   ∀ x,H x = true→ x w = true→ 
    PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ x = true:=by
 have hRu:u ∉ R:=by
  intro h
  have ht:d4z R (pairInput u v) = true:=by simp [d50,h]
  exact Bool.false_ne_true (hR.symm.trans ht)
 have hRv:v ∉ R:=by
  intro h
  have ht:d4z R (pairInput u v) = true:=by simp [d50,h]
  exact Bool.false_ne_true (hR.symm.trans ht)
 have hs:u ∈ S∨ v ∈ S:=by simpa only [d50,decide_eq_true_eq] using hS
 obtain ⟨w,hw,hwS⟩:∃ w,(w = u∨ w = v)∧ w ∈ S:=by
  rcases hs with hs | hs
  ·exact ⟨u,Or.inl rfl,hs⟩
  ·exact ⟨v,Or.inr rfl,hs⟩
 refine ⟨fun h=>hRu (h ▸ hr),fun h=>hRv (h ▸ hr),w,hw,?_,?_⟩
 ·apply (d2l G r w).mp
  apply q01 (pairInput r w)
  have h1:d4z R (pairInput r w) = true:=by simp [d50,hr]
  have h2:d4z S (pairInput r w) = true:=by simp [d50,hwS]
  simp [h1,h2]
 ·intro x hx hxw
  apply q01 x
  have hs:d4z S x = true:=by
   simpa only [d4z,decide_eq_true_eq] using (show ∃ w ∈ S,x w = true from ⟨w,hwS,hxw⟩)
  simp [hx,hs]
end TightSupport
namespace TightSupport.Geometry
open PEqualNP.TopForm PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership
lemma d2m {n:ℕ} (G:SimpleGraph (Fin n)) [DecidableRel G.Adj]
  (x:Fin n→ Bool):
  graphFun G ∅ x = true↔ ∃ u v,G.Adj u v∧ x u = true∧ x v = true:=by
 simp [graphFun]
lemma d0s {n:ℕ} (G:SimpleGraph (Fin n)) [DecidableRel G.Adj]
  (h4:NoFourCycle G) (a b u v:Fin n) (hab:a ≠ b)
  (hau:G.Adj a u) (hbu:G.Adj b u) (hav:G.Adj a v) (hbv:G.Adj b v):u = v:=by
 exact Finset.card_le_one.mp (h4 a b hab) u
  (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hau,hbu⟩) v
  (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hav,hbv⟩)
lemma d0r {n:ℕ} (G:SimpleGraph (Fin n))
  (s:Fin n→ Bool) (hbip:∀ u v,G.Adj u v→ s u ≠ s v)
  (r u v:Fin n) (hru:G.Adj r u) (hrv:G.Adj r v):s u = s v:=by
 have h1:=hbip r u hru
 have h2:=hbip r v hrv
 cases hr:s r <;> cases hu:s u <;> cases hv:s v <;> simp_all
def d0n {n k:ℕ} (G:SimpleGraph (Fin n)) [DecidableRel G.Adj]
  (S:Fin k→ Finset (Fin n)) (w:Fin n):Prop:=
 ∀ x:Fin n→ Bool,x w = true→ 
  (∀ i,∃ a ∈ S i,x a = true)→ graphFun G ∅ x = true
lemma d0j (u v w:Bool) (hu:u ≠ w) (hv:v ≠ w):u = v:=by
 cases u <;> cases v <;> cases w <;> simp_all
lemma d35 {n k:ℕ}
  (G:SimpleGraph (Fin n)) [DecidableRel G.Adj]
  (s:Fin n→ Bool) (hbip:∀ u v,G.Adj u v→ s u ≠ s v)
  (S:Fin k→ Finset (Fin n)) (t:Fin k→ Bool)
  (hmono:∀ i,∀ a ∈ S i,s a = t i)
  (d w:Fin n) (hdw:s d ≠ s w)
  (hpair:∀ i,d ∈ S i∨ w ∈ S i)
  (q01:d0n G S w):
  ∃ i,t i ≠ s w∧ ∀ a ∈ S i,G.Adj w a:=by
 classical
 by_contra q18
 let x:Fin n→ Bool:=fun a=>decide (a = w∨ (s a ≠ s w∧ ¬ G.Adj w a))
 have hw:x w = true:=by simp [x]
 have q3e:∀ i,∃ a ∈ S i,x a = true:=by
  intro i
  by_cases hi:t i = s w
  ·have hwi:w ∈ S i:=by
    rcases hpair i with hd | hw
    ·exact False.elim (hdw ((hmono i d hd).trans hi))
    ·exact hw
   exact ⟨w,hwi,hw⟩
  ·by_contra q2i
   have q3f:∀ a ∈ S i,G.Adj w a:=by
    intro a ha
    by_contra hwa
    have hax:x a = true:=by
     apply decide_eq_true
     exact Or.inr ⟨by rw [hmono i a ha];exact hi,hwa⟩
    exact q2i ⟨a,ha,hax⟩
   exact q18 ⟨i,hi,q3f⟩
 obtain ⟨u,v,huv,hu,hv⟩:=(d2m G x).mp (q01 x hw q3e)
 simp only [x,decide_eq_true_eq] at hu hv
 rcases hu with hu | ⟨huc,hun⟩
 ·subst u
  rcases hv with hv | ⟨hvc,hvn⟩
  ·subst v
   exact G.loopless.irrefl w huv
  ·exact hvn huv
 ·rcases hv with hv | ⟨hvc,hvn⟩
  ·subst v
   exact hun huv.symm
  ·exact hbip u v huv (d0j (s u) (s v) (s w) huc hvc)
lemma d34 {n k:ℕ}
  (G:SimpleGraph (Fin n)) [DecidableRel G.Adj]
  (s:Fin n→ Bool) (hbip:∀ u v,G.Adj u v→ s u ≠ s v)
  (h4:NoFourCycle G)
  (S:Fin k→ Finset (Fin n)) (t:Fin k→ Bool)
  (hmono:∀ i,∀ a ∈ S i,s a = t i)
  (R:Fin n→ Fin n→ Prop) (hRn:∃ d w,R d w)
  (q13:∀ d w,R d w→ s d ≠ s w)
  (hpair:∀ d w,R d w→ ∀ i,d ∈ S i∨ w ∈ S i)
  (q01:∀ d w,R d w→ d0n G S w)
  (r:Fin n) (q0f:∀ d w,R d w→ G.Adj r w)
  (hne:∀ d w,R d w→ r ≠ d):
  ∃ (v:Fin n) (i:Fin k),(∀ a ∈ S i,G.Adj v a)∧ 
   ∀ d w,R d w→ w = v∧ d ∈ S i:=by
 obtain ⟨d0,w0,h0⟩:=hRn
 obtain ⟨i0,hi0,q14⟩:=d35 G s hbip S t hmono
  d0 w0 (q13 d0 w0 h0) (hpair d0 w0 h0) (q01 d0 w0 h0)
 have hd0:d0 ∈ S i0:=by
  rcases hpair d0 w0 h0 i0 with h | h
  ·exact h
  ·exact False.elim (hi0 (hmono i0 w0 h).symm)
 refine ⟨w0,i0,q14,?_⟩
 intro d w h
 have q1w:=d0r G s hbip r w w0 (q0f d w h) (q0f d0 w0 h0)
 obtain ⟨i,hi,q2j⟩:=d35 G s hbip S t hmono
  d w (q13 d w h) (hpair d w h) (q01 d w h)
 have q3g:d0 ∈ S i:=by
  rcases hpair d0 w0 h0 i with hh | hh
  ·exact hh
  ·exact False.elim (hi ((hmono i w0 hh).symm.trans q1w.symm))
 have q3h:=d0s G h4 r d0 w w0 (hne d0 w0 h0)
  (q0f d w h) (q2j d0 q3g).symm (q0f d0 w0 h0) (q14 d0 hd0).symm
 refine ⟨q3h,?_⟩
 rcases hpair d w h i0 with hh | hh
 ·exact hh
 ·exact False.elim (hi0 ((hmono i0 w hh).symm.trans q1w))
lemma d36 {n k:ℕ}
  (G:SimpleGraph (Fin n)) [DecidableRel G.Adj]
  (s:Fin n→ Bool) (hbip:∀ u v,G.Adj u v→ s u ≠ s v)
  (h4:NoFourCycle G)
  (S:Fin k→ Finset (Fin n)) (t:Fin k→ Bool)
  (hmono:∀ i,∀ a ∈ S i,s a = t i)
  (E:Finset (Fin n × Fin n)) (hEn:E.Nonempty)
  (q0q:∀ p ∈ E,G.Adj p.1 p.2)
  (hpair:∀ p ∈ E,∀ i,p.1 ∈ S i∨ p.2 ∈ S i)
  (r:Fin n) (hne:∀ p ∈ E,r ≠ p.1∧ r ≠ p.2)
  (q0t:∀ p ∈ E,
   (d0n G S p.1∧ G.Adj r p.1)∨ 
   (d0n G S p.2∧ G.Adj r p.2)):
  ∃ (v:Fin n) (i:Fin k),(∀ a ∈ S i,G.Adj v a)∧ 
   ∀ p ∈ E,(p.1 = v∧ p.2 ∈ S i)∨ (p.2 = v∧ p.1 ∈ S i):=by
 let R:Fin n→ Fin n→ Prop:=fun d w=>
  ((d,w) ∈ E∨ (w,d) ∈ E)∧ d0n G S w∧ G.Adj r w
 have hRn:∃ d w,R d w:=by
  obtain ⟨⟨d,w⟩,h⟩:=hEn
  rcases q0t (d,w) h with ⟨hc,hr⟩ | ⟨hc,hr⟩
  ·exact ⟨w,d,Or.inr h,hc,hr⟩
  ·exact ⟨d,w,Or.inl h,hc,hr⟩
 have q2k:∀ d w,R d w→ s d ≠ s w:=by
  intro d w h
  rcases h.1 with h | h
  ·exact hbip d w (q0q (d,w) h)
  ·exact hbip d w (q0q (w,d) h).symm
 have hpR:∀ d w,R d w→ ∀ i,d ∈ S i∨ w ∈ S i:=by
  intro d w h i
  rcases h.1 with h | h
  ·exact hpair (d,w) h i
  ·exact (hpair (w,d) h i).symm
 have hnR:∀ d w,R d w→ r ≠ d:=by
  intro d w h
  rcases h.1 with h | h
  ·exact (hne (d,w) h).1
  ·exact (hne (w,d) h).2
 obtain ⟨v,i,hu,hv⟩:=d34 G s hbip h4 S t hmono R hRn
  q2k hpR (fun _ _ h=>h.2.1) r (fun _ _ h=>h.2.2) hnR
 refine ⟨v,i,hu,?_⟩
 intro p hp
 rcases q0t p hp with ⟨hc,hr⟩ | ⟨hc,hr⟩
 ·exact Or.inl (hv p.2 p.1 ⟨Or.inr hp,hc,hr⟩)
 ·exact Or.inr (hv p.1 p.2 ⟨Or.inl hp,hc,hr⟩)
end TightSupport.Geometry
namespace TightSupport
open PEqualNP.EdgeOwnership PEqualNP.MetaComplexity.NestedCover
def d0o {n k:ℕ} (S:Fin k→ Finset (Fin n)) (x:Fin n→ Bool):Bool:=
 decide (∀ i,∃ a ∈ S i,x a = true)
lemma d0t {n k:ℕ}
  (G:SimpleGraph (Fin n)) [DecidableRel G.Adj]
  (s:Fin n→ Bool) (hbip:∀ u v,G.Adj u v→ s u ≠ s v)
  (h4:PEqualNP.TopForm.NoFourCycle G)
  (S:Fin k→ Finset (Fin n)) (t:Fin k→ Bool)
  (hmono:∀ i,∀ a ∈ S i,s a = t i)
  (context:(Fin n→ Bool)→ Bool→ Bool)
  (q00:∀ x y b c,(∀ v,x v = true→ y v = true)→ 
   (b = true→ c = true)→ context x b = true→ context y c = true)
  (hF:∀ x,context x (d0o S x) = graphFun G ∅ x)
  (E:Finset (Fin n × Fin n)) (hEn:E.Nonempty)
  (q0q:∀ p ∈ E,G.Adj p.1 p.2)
  (q0p:∀ p ∈ E,context (pairInput p.1 p.2) false = false)
  (q0u:∀ u v,G.Adj u v→ context (pairInput u v) false = false→ (u,v) ∈ E)
  (r:Fin n)
  (q0g:∀ p ∈ E,∃ R T:Finset (Fin n),r ∈ R∧ 
   (∀ x,((d4z R x || d0o S x) && d4z T x) = true→ graphFun G ∅ x = true)∧ 
   d4z R (pairInput p.1 p.2) = false∧ d4z T (pairInput p.1 p.2) = true):
  ∃ (v:Fin n) (i:Fin k),(∀ a ∈ S i,G.Adj v a)∧ 
   (fun x=>context x (x v && d4z (S i) x)) = graphFun G ∅:=by
 have hH:∀ p ∈ E,d0o S (pairInput p.1 p.2) = true:=by
  intro p hp
  have he:=(hF (pairInput p.1 p.2)).trans ((d2l G p.1 p.2).mpr (q0q p hp))
  cases h:d0o S (pairInput p.1 p.2)
  ·rw [h,q0p p hp] at he
   cases he
  ·rfl
 have hpair:∀ p ∈ E,∀ i,p.1 ∈ S i∨ p.2 ∈ S i:=by
  intro p hp i
  have hh:=(decide_eq_true_eq.mp (hH p hp)) i
  obtain ⟨a,ha,hx⟩:=hh
  simp only [pairInput,decide_eq_true_eq] at hx
  rcases hx with rfl | rfl
  ·exact Or.inl ha
  ·exact Or.inr ha
 have q0h:∀ p ∈ E,r ≠ p.1∧ r ≠ p.2∧ 
   ((Geometry.d0n G S p.1∧ G.Adj r p.1)∨ 
    (Geometry.d0n G S p.2∧ G.Adj r p.2)):=by
  intro p hp
  obtain ⟨R,T,hr,q01,hR,hT⟩:=q0g p hp
  obtain ⟨h1,h2,w,hw,q1x,hcw⟩:=
   d51 G (d0o S) R T r p.1 p.2 hr q01 hR hT
  have hc:Geometry.d0n G S w:=by
   intro x hx hh
   exact hcw x (decide_eq_true hh) hx
  refine ⟨h1,h2,?_⟩
  rcases hw with rfl | rfl
  ·exact Or.inl ⟨hc,q1x⟩
  ·exact Or.inr ⟨hc,q1x⟩
 obtain ⟨v,i,hu,hc⟩:=Geometry.d36 G s hbip h4 S t hmono
  E hEn q0q hpair r (fun p hp=>⟨(q0h p hp).1,(q0h p hp).2.1⟩)
  (fun p hp=>(q0h p hp).2.2)
 refine ⟨v,i,hu,?_⟩
 apply d0q G context (d0o S) (fun x=>x v && d4z (S i) x)
  q00 ?_ ?_ ?_ hF
 ·intro x y hxy hx
  simp only [Bool.and_eq_true,d4z,decide_eq_true_eq] at hx ⊢
  obtain ⟨hv,a,ha,hax⟩:=hx
  exact ⟨hxy v hv,a,ha,hxy a hax⟩
 ·intro x hx
  simp only [Bool.and_eq_true,d4z,decide_eq_true_eq] at hx
  obtain ⟨hv,a,ha,hax⟩:=hx
  exact (Geometry.d2m G x).mpr ⟨v,a,hu a ha,hv,hax⟩
 ·intro u w huw q1c
  rcases hc (u,w) (q0u u w huw q1c) with ⟨h,hm⟩ | ⟨h,hm⟩
  ·dsimp at h hm
   subst u
   simp [pairInput,d50,hm]
  ·dsimp at h hm
   subst w
   simp [pairInput,d50,hm]
end TightSupport
namespace TightSupport.CriticalEdge
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
def run (gs:List Gate) (x:List Bool):List Bool:=
 gs.foldl (fun w g=>w ++ [g.op.eval (g.inputs.map fun i=>w.getD i false)]) x
lemma d4v (gs:List Gate) (g:Gate) (x:List Bool):
  run (gs ++ [g]) x = run gs x ++ [g.op.eval (g.inputs.map fun i=>(run gs x).getD i false)]:=by
 simp [run,List.foldl_append]
lemma d4t (gs:List Gate) (x:List Bool):(run gs x).length = x.length + gs.length:=by
 induction gs using List.reverseRecOn with
 | nil=>simp [run]
 | append_singleton gs g ih=>rw [d4v];simp [ih];omega
lemma d2d (l:List Bool) (b:Bool):(l ++ [b]).getD l.length false = b:=by
 simp [List.getD_eq_getElem?_getD]
lemma d2h {α:Type} (z:α) (l:List α) (b:α) (t:ℕ) (h:t < l.length):
  (l ++ [b]).getD t z = l.getD t z:=by
 simp [List.getD_eq_getElem?_getD,List.getElem?_append_left h]
lemma d2e {α:Type} (z:α) (l:List α) (b:α):(l ++ [b]).getD l.length z = b:=by
 simp [List.getD_eq_getElem?_getD]
lemma d4u (gs hs:List Gate) (x:List Bool) (i:ℕ) (hi:i < x.length + gs.length):
  (run (gs ++ hs) x).getD i false = (run gs x).getD i false:=by
 induction hs using List.reverseRecOn with
 | nil=>simp
 | append_singleton hs g ih=>
  rw [← List.append_assoc,d4v,d2h false _ _ _ (by
   rw [d4t,List.length_append];omega),ih]
lemma d4s (gs:List Gate) (x:List Bool) (i:ℕ) (hi:i < x.length):
  (run gs x).getD i false = x.getD i false:=by
 have:=d4u [] gs x i (by simpa using hi)
 simpa [run] using this
lemma d4r (gs:List Gate) (x:List Bool):∀ (j:ℕ) (hj:j < gs.length),
  (run gs x).getD (x.length + j) false = gs[j].op.eval (gs[j].inputs.map fun i=>
   if i < x.length + j then (run gs x).getD i false else false):=by
 induction gs using List.reverseRecOn with
 | nil=>intro j hj;simp at hj
 | append_singleton gs g ih=>
  intro j hj
  have q06:(run gs x).length = x.length + gs.length:=d4t gs x
  have same:∀ (k:ℕ),k ≤ gs.length→ ∀ l:List ℕ,
    (l.map fun i=>if i < x.length + k then (run (gs ++ [g]) x).getD i false else false) =
    l.map fun i=>if i < x.length + k then (run gs x).getD i false else false:=by
   intro k hk l
   refine List.map_congr_left fun i _=>?_
   split_ifs with h
   ·exact d4u gs [g] x i (by omega)
   ·rfl
  rcases Nat.lt_or_ge j gs.length with h | h
  ·rw [List.getElem_append_left h,same j (by omega),d4u gs [g] x _ (by omega)]
   exact ih j h
  ·have hjj:j = gs.length:=by simp at hj;omega
   subst hjj
   have hg:(gs ++ [g])[gs.length] = g:=by simp
   rw [hg,same _ le_rfl,d4v,← q06,d2e]
   congr 1
   refine List.map_congr_left fun i _=>?_
   split_ifs with h
   ·rfl
   ·exact List.getD_eq_default _ _ (by omega)
def u (n:ℕ) (A:ℕ→ Bool) (a b:ℕ→ ℕ) (Del:Finset ℕ) (L:ℕ→ List ℕ) (x:List Bool)
  (w:ℕ):Bool:=
 if w < n then x.getD w false
 else if w - n ∈ Del then false
 else if A (w - n) = true then
  ((if _h:a (w - n) < w then u n A a b Del L x (a (w - n)) else false) ||
   (L (w - n)).any (fun t=>x.getD t false)) &&
  (if _h:b (w - n) < w then u n A a b Del L x (b (w - n)) else false)
 else
  (if _h:a (w - n) < w then u n A a b Del L x (a (w - n)) else false) ||
  (if _h:b (w - n) < w then u n A a b Del L x (b (w - n)) else false)
termination_by w
section RecursiveValues
variable {n:ℕ} {A:ℕ→ Bool} {a b:ℕ→ ℕ} {Del:Finset ℕ} {L:ℕ→ List ℕ} {x:List Bool}
lemma d5l {w:ℕ} (h:w < n):u n A a b Del L x w = x.getD w false:=by
 rw [u,if_pos h]
lemma d5k {j:ℕ} (h:j ∈ Del):u n A a b Del L x (n + j) = false:=by
 rw [u,if_neg (by omega),Nat.add_sub_cancel_left,if_pos h]
lemma d5j {j:ℕ} (h:j ∉ Del) (hA:A j = true) (ha:a j < n + j) (hb:b j < n + j):
  u n A a b Del L x (n + j) = ((u n A a b Del L x (a j) ||
   (L j).any (fun t=>x.getD t false)) && u n A a b Del L x (b j)):=by
 rw [u,if_neg (by omega),Nat.add_sub_cancel_left,if_neg h,if_pos hA,dif_pos ha,dif_pos hb]
lemma d5n {j:ℕ} (h:j ∉ Del) (hA:A j = false) (ha:a j < n + j) (hb:b j < n + j):
  u n A a b Del L x (n + j) = (u n A a b Del L x (a j) || u n A a b Del L x (b j)):=by
 rw [u,if_neg (by omega),Nat.add_sub_cancel_left,if_neg h,if_neg (by simp [hA]),dif_pos ha,
  dif_pos hb]
end RecursiveValues
def Ok (n:ℕ) (gs:List Gate):Prop:=
 ∀ j (hj:j < gs.length),∃ o s t,gs[j] = ⟨o,[s,t]⟩∧ (o = GateOp.and∨ o = GateOp.or)∧ 
  s < n + j∧ t < n + j
lemma d3e {n:ℕ} {gs:List Gate} (h:Ok n gs) {o:GateOp} {s t:ℕ}
  (ho:o = GateOp.and∨ o = GateOp.or) (hs:s < n + gs.length) (ht:t < n + gs.length):
  Ok n (gs ++ [⟨o,[s,t]⟩]):=by
 intro j hj
 by_cases hlt:j < gs.length
 ·rw [List.getElem_append_left hlt];exact h j hlt
 ·have:j = gs.length:=by simp at hj;omega
  subst this
  exact ⟨o,s,t,by simp,ho,hs,ht⟩
open Classical in
noncomputable def dc (n:ℕ) (F:(Fin n→ Bool)→ Bool) (gs:List Gate):ℕ:=
 ((Finset.range gs.length).filter fun i=>(gs.getD i ⟨GateOp.or,[]⟩).op = GateOp.and∧ 
  ∃ x:Fin n→ Bool,(run gs (List.ofFn x)).getD (n + i) false = true∧ F x = false).card
open Classical in
lemma d18 (n:ℕ) (F:(Fin n→ Bool)→ Bool) (gs:List Gate) (g:Gate):
  dc n F (gs ++ [g]) ≤ dc n F gs + if g.op = GateOp.and∧ 
   ∃ x:Fin n→ Bool,(run (gs ++ [g]) (List.ofFn x)).getD (n + gs.length) false = true∧ 
    F x = false then 1 else 0:=by
 unfold dc
 rw [List.length_append,List.length_singleton,Finset.range_add_one,Finset.filter_insert]
 have e:(gs ++ [g]).getD gs.length ⟨GateOp.or,[]⟩ = g:=by
  simp [List.getD_eq_getElem?_getD]
 rw [e]
 have h1:((Finset.range gs.length).filter fun i=>
   ((gs ++ [g]).getD i ⟨GateOp.or,[]⟩).op = GateOp.and∧ ∃ x:Fin n→ Bool,
    (run (gs ++ [g]) (List.ofFn x)).getD (n + i) false = true∧ F x = false) =
   (Finset.range gs.length).filter fun i=>
   (gs.getD i ⟨GateOp.or,[]⟩).op = GateOp.and∧ ∃ x:Fin n→ Bool,
    (run gs (List.ofFn x)).getD (n + i) false = true∧ F x = false:=by
  refine Finset.filter_congr fun i hi=>?_
  have hi':=Finset.mem_range.1 hi
  rw [d2h _ _ _ _ hi']
  refine and_congr_right fun _=>exists_congr fun x=>?_
  rw [d4u gs [g] _ _ (by simp;omega)]
 rw [h1]
 split_ifs with h
 ·exact (Finset.card_insert_le _ _)
 ·simp
def ov (gs:List Gate) (x:List Bool) (o:Option ℕ):Bool:=
 match o with
 | none=>false
 | some w=>(run gs x).getD w false
lemma d44 (gs hs:List Gate) (x:List Bool) (o:Option ℕ)
  (h:∀ w,o = some w→ w < x.length + gs.length):ov (gs ++ hs) x o = ov gs x o:=by
 cases o with
 | none=>rfl
 | some w=>exact d4u gs hs x w (h w rfl)
lemma d45 (gs:List Gate) (n:ℕ) (x:List Bool) (hx:x.length = n) (o:GateOp) (s t:ℕ)
  (hs:s < n + gs.length) (ht:t < n + gs.length):
  ov (gs ++ [⟨o,[s,t]⟩]) x (some (n + gs.length)) =
   o.eval [(run gs x).getD s false,(run gs x).getD t false]:=by
 unfold ov
 simp only
 rw [d4v]
 have:n + gs.length = (run gs x).length:=by rw [d4t,hx]
 rw [this,d2d]
 rfl
lemma d0l (n:ℕ) (F:(Fin n→ Bool)→ Bool):∀ (l:List ℕ),(∀ t ∈ l,t < n)→ 
  ∀ (gs:List Gate),Ok n gs→ ∀ o:Option ℕ,(∀ w,o = some w→ w < n + gs.length)→ 
  ∃ (hs:List Gate) (o':Option ℕ),Ok n (gs ++ hs)∧ hs.length ≤ l.length∧ 
   dc n F (gs ++ hs) ≤ dc n F gs∧ (∀ w,o' = some w→ w < n + (gs ++ hs).length)∧ 
   ∀ x:Fin n→ Bool,ov (gs ++ hs) (List.ofFn x) o' =
    (ov gs (List.ofFn x) o || l.any (fun t=>(List.ofFn x).getD t false)):=by
 intro l
 induction l with
 | nil=>
  intro _ gs hgs o ho
  exact ⟨[],o,by simpa using hgs,by simp,by simp,by simpa using ho,by simp⟩
 | cons t l ih=>
  intro hl gs hgs o ho
  have ht:t < n:=hl t (by simp)
  have hl':∀ t ∈ l,t < n:=fun s hs=>hl s (by simp [hs])
  cases o with
  | none=>
   obtain ⟨hs,o',h1,h2,h3,h4,h5⟩:=ih hl' gs hgs (some t) (by
    intro w hw;cases hw;omega)
   refine ⟨hs,o',h1,by simp;omega,h3,h4,fun x=>?_⟩
   rw [h5 x]
   have:ov gs (List.ofFn x) (some t) = (List.ofFn x).getD t false:=
    d4s _ _ _ (by simpa using ht)
   rw [this];simp [ov]
  | some w=>
   have hw:=ho w rfl
   obtain ⟨hs,o',h1,h2,h3,h4,h5⟩:=ih hl' (gs ++ [⟨GateOp.or,[w,t]⟩])
    (d3e hgs (Or.inr rfl) hw (by omega)) (some (n + gs.length)) (by
     intro w hw;cases hw;simp)
   refine ⟨⟨GateOp.or,[w,t]⟩::hs,o',by simpa using h1,by simp;omega,?_,
    by simpa using h4,fun x=>?_⟩
   ·have:=d18 n F gs ⟨GateOp.or,[w,t]⟩
    rw [if_neg (by simp)] at this
    have e:gs ++ ⟨GateOp.or,[w,t]⟩::hs = gs ++ [⟨GateOp.or,[w,t]⟩] ++ hs:=by simp
    rw [e];omega
   ·have e:gs ++ ⟨GateOp.or,[w,t]⟩::hs = gs ++ [⟨GateOp.or,[w,t]⟩] ++ hs:=by simp
    rw [e,h5 x,d45 gs n _ (by simp) _ _ _ hw (by omega)]
    rw [d4s gs (List.ofFn x) t (by simpa using ht)]
    simp [ov,GateOp.eval,Bool.or_assoc]
open Classical in
lemma d0k (n:ℕ) (A:ℕ→ Bool) (a b:ℕ→ ℕ) (Del R:Finset ℕ) (L:ℕ→ List ℕ)
  (F:(Fin n→ Bool)→ Bool) (hL:∀ j,∀ t ∈ L j,t < n)
  (hR:∀ j ∈ R,A j = false∧ j ∉ Del∧ ∃ d ∈ Del,d < j∧ (a j = n + d∨ b j = n + d)):
  ∀ p,(∀ j < p,a j < n + j∧ b j < n + j)→ 
  ∃ (gs:List Gate) (m:ℕ→ Option ℕ),Ok n gs∧ 
   (∀ w < n + p,(∀ w',m w = some w'→ w' < n + gs.length)∧ 
    ∀ x:Fin n→ Bool,ov gs (List.ofFn x) (m w) = u n A a b Del L (List.ofFn x) w)∧ 
   (∀ d ∈ Del,d < p→ m (n + d) = none)∧ 
   gs.length + ((Finset.range p).filter (· ∈ Del)).card +
    ((Finset.range p).filter (· ∈ R)).card ≤ p + ∑ j ∈ Finset.range p,(L j).length∧ 
   dc n F gs ≤ ((Finset.range p).filter fun j=>A j = true∧ j ∉ Del∧ 
    ∃ x:Fin n→ Bool,u n A a b Del L (List.ofFn x) (n + j) = true∧ F x = false).card:=by
 intro p
 induction p with
 | zero=>
  intro _
  refine ⟨[],fun w=>some w,by intro j hj;simp at hj,?_,by simp,by simp,by simp [dc]⟩
  intro w hw
  refine ⟨by intro w' h;cases h;simpa using hw,fun x=>?_⟩
  rw [d5l (by omega)];rfl
 | succ p ih=>
  intro hab
  obtain ⟨gs,m,hok,hm,hd,hc,hj⟩:=ih fun j hj=>hab j (by omega)
  obtain ⟨hap,hbp⟩:=hab p (by omega)
  suffices hh:∃ (hs:List Gate) (o:Option ℕ),Ok n (gs ++ hs)∧ 
    (∀ w,o = some w→ w < n + (gs ++ hs).length)∧ (p ∈ Del→ o = none)∧ 
    (∀ x:Fin n→ Bool,ov (gs ++ hs) (List.ofFn x) o =
     u n A a b Del L (List.ofFn x) (n + p))∧ 
    hs.length + (if p ∈ Del then 1 else 0) + (if p ∈ R then 1 else 0) ≤ 1 + (L p).length∧ 
    dc n F (gs ++ hs) ≤ dc n F gs + if A p = true∧ p ∉ Del∧ ∃ x:Fin n→ Bool,
     u n A a b Del L (List.ofFn x) (n + p) = true∧ F x = false then 1 else 0 by
   obtain ⟨hs,o,h1,h2,h3,h4,h5,h6⟩:=hh
   refine ⟨gs ++ hs,Function.update m (n + p) o,h1,?_,?_,?_,?_⟩
   ·intro w hw
    by_cases hwp:w = n + p
    ·subst hwp;rw [Function.update_self];exact ⟨h2,h4⟩
    ·rw [Function.update_of_ne hwp]
     obtain ⟨q1,q2⟩:=hm w (by omega)
     refine ⟨fun w' hw'=>by have:=q1 w' hw';simp;omega,fun x=>?_⟩
     rw [d44 gs hs _ _ (by simpa using q1),q2]
   ·intro d hdd hdp
    by_cases q3i:d = p
    ·subst q3i;rw [Function.update_self];exact h3 hdd
    ·rw [Function.update_of_ne (by omega)];exact hd d hdd (by omega)
   ·rw [Finset.range_add_one,Finset.filter_insert,Finset.filter_insert,
     Finset.sum_insert (by simp),List.length_append]
    split_ifs at h5 ⊢ with q1 q2 q2 <;>
     (try rw [Finset.card_insert_of_notMem (by simp)]) <;>
     (try rw [Finset.card_insert_of_notMem (by simp)]) <;> omega
   ·rw [Finset.range_add_one,Finset.filter_insert]
    split_ifs at h6 ⊢ with q1
    ·rw [Finset.card_insert_of_notMem (by simp)];omega
    ·omega
  by_cases hpd:p ∈ Del
  ·have hpR:p ∉ R:=fun h=>(hR p h).2.1 hpd
   refine ⟨[],none,by simpa using hok,by simp,fun _=>rfl,fun x=>?_,?_,by simp⟩
   ·rw [d5k hpd];rfl
   ·rw [if_pos hpd,if_neg hpR];simp
  obtain ⟨a1,a2⟩:=hm (a p) hap
  obtain ⟨b1,b2⟩:=hm (b p) hbp
  cases hA:A p with
  | false=>
   have hu:=fun x:Fin n→ Bool=>d5n (L:=L) (x:=List.ofFn x) hpd hA hap hbp
   rcases ha0:m (a p) with _ | s
   ·refine ⟨[],m (b p),by simpa using hok,by simpa using b1,fun h=>absurd h hpd,
     fun x=>?_,?_,by simp⟩
    ·rw [hu x,← a2 x,← b2 x,ha0];simp [ov]
    ·rw [if_neg hpd];split_ifs <;> simp
   rcases hb0:m (b p) with _ | t
   ·refine ⟨[],m (a p),by simpa using hok,by simpa using a1,fun h=>absurd h hpd,
     fun x=>?_,?_,by simp⟩
    ·rw [hu x,← a2 x,← b2 x,hb0];simp [ov]
    ·rw [if_neg hpd];split_ifs <;> simp
   have hpR:p ∉ R:=by
    intro h
    obtain ⟨_,_,d,hd1,hd2,hd3⟩:=hR p h
    have:=hd d hd1 hd2
    rcases hd3 with h | h
    ·rw [h,this] at ha0;cases ha0
    ·rw [h,this] at hb0;cases hb0
   have hs:=a1 s ha0
   have ht:=b1 t hb0
   refine ⟨[⟨GateOp.or,[s,t]⟩],some (n + gs.length),d3e hok (Or.inr rfl) hs ht,
    by intro w hw;cases hw;simp,fun h=>absurd h hpd,fun x=>?_,?_,?_⟩
   ·rw [d45 gs n _ (by simp) _ _ _ hs ht,hu x,← a2 x,← b2 x,ha0,hb0]
    simp [ov,GateOp.eval]
   ·rw [if_neg hpd,if_neg hpR];simp
   ·have:=d18 n F gs ⟨GateOp.or,[s,t]⟩
    rw [if_neg (by simp)] at this
    omega
  | true=>
   have hu:=fun x:Fin n→ Bool=>d5j (L:=L) (x:=List.ofFn x) hpd hA hap hbp
   have hpR:p ∉ R:=fun h=>by rw [(hR p h).1] at hA;cases hA
   obtain ⟨hs,o',c1,c2,c3,c4,c5⟩:=d0l n F (L p) (hL p) gs hok (m (a p)) a1
   rcases ho:o' with _ | s
   ·refine ⟨hs,none,c1,by simp,fun _=>rfl,fun x=>?_,?_,by omega⟩
    ·have:=c5 x
     rw [ho,a2 x] at this
     rw [hu x,← this];simp [ov]
    ·rw [if_neg hpd,if_neg hpR];omega
   rcases hb0:m (b p) with _ | t
   ·refine ⟨hs,none,c1,by simp,fun _=>rfl,fun x=>?_,?_,by omega⟩
    ·have:=b2 x
     rw [hb0] at this
     rw [hu x,← this];simp [ov]
    ·rw [if_neg hpd,if_neg hpR];omega
   have hs':=c4 s ho
   have ht:t < n + (gs ++ hs).length:=by have:=b1 t hb0;simp;omega
   have q17:∀ x:Fin n→ Bool,ov (gs ++ hs ++ [⟨GateOp.and,[s,t]⟩]) (List.ofFn x)
     (some (n + (gs ++ hs).length)) = u n A a b Del L (List.ofFn x) (n + p):=by
    intro x
    rw [d45 (gs ++ hs) n _ (by simp) _ _ _ hs' ht,hu x,← a2 x,← b2 x,← c5 x,ho,hb0,
     ← d44 gs hs (List.ofFn x) (some t) (by intro w hw;cases hw;simpa using b1 t hb0)]
    simp [ov,GateOp.eval]
   refine ⟨hs ++ [⟨GateOp.and,[s,t]⟩],some (n + (gs ++ hs).length),?_,?_,
    fun h=>absurd h hpd,fun x=>?_,?_,?_⟩
   ·rw [← List.append_assoc];exact d3e c1 (Or.inl rfl) hs' ht
   ·intro w hw;cases hw;simp
   ·rw [← List.append_assoc];exact q17 x
   ·rw [if_neg hpd,if_neg hpR];simp;omega
   ·rw [← List.append_assoc]
    have:=d18 n F (gs ++ hs) ⟨GateOp.and,[s,t]⟩
    have e:((⟨GateOp.and,[s,t]⟩:Gate).op = GateOp.and∧ ∃ x:Fin n→ Bool,
      (run (gs ++ hs ++ [⟨GateOp.and,[s,t]⟩]) (List.ofFn x)).getD
       (n + (gs ++ hs).length) false = true∧ F x = false)↔ 
      (true = true∧ p ∉ Del∧ ∃ x:Fin n→ Bool,
       u n A a b Del L (List.ofFn x) (n + p) = true∧ F x = false):=by
     refine ⟨fun h=>⟨rfl,hpd,?_⟩,fun h=>⟨rfl,?_⟩⟩
     ·obtain ⟨x,h1,h2⟩:=h.2
      exact ⟨x,by rw [← q17 x];exact h1,h2⟩
     ·obtain ⟨x,h1,h2⟩:=h.2.2
      exact ⟨x,by rw [← q17 x] at h1;exact h1,h2⟩
    rw [if_congr e rfl rfl] at this
    omega
lemma gf {n:ℕ} (G:SimpleGraph (Fin n)) [DecidableRel G.Adj] (x:Fin n→ Bool):
  graphFun G ∅ x = true↔ ∃ p q,G.Adj p q∧ x p = true∧ x q = true:=by
 simp [graphFun]
lemma gD {n:ℕ} (x:Fin n→ Bool) (p:Fin n):(List.ofFn x).getD p.val false = x p:=by
 simp [List.getD_eq_getElem?_getD]
lemma d5m {n N:ℕ} {A:ℕ→ Bool} {a b:ℕ→ ℕ} {Del:Finset ℕ} {L:ℕ→ List ℕ}
  (hab:∀ j < N,a j < n + j∧ b j < n + j) (x y:List Bool)
  (h:∀ t,x.getD t false = true→ y.getD t false = true):
  ∀ w < n + N,u n A a b Del L x w = true→ u n A a b Del L y w = true:=by
 intro w
 induction w using Nat.strong_induction_on with
 | _ w ih=>
  intro hw hx
  by_cases h9:w < n
  ·rw [d5l h9] at hx ⊢;exact h _ hx
  obtain ⟨j,rfl⟩:∃ j,w = n + j:=⟨w - n,by omega⟩
  obtain ⟨ha,hb⟩:=hab j (by omega)
  by_cases hd:j ∈ Del
  ·rw [d5k hd] at hx;cases hx
  have ia:=ih (a j) ha (by omega)
  have ib:=ih (b j) hb (by omega)
  cases hA:A j with
  | true=>
   rw [d5j hd hA ha hb,Bool.and_eq_true,Bool.or_eq_true] at hx ⊢
   refine ⟨?_,ib hx.2⟩
   rcases hx.1 with h1 | h1
   ·exact Or.inl (ia h1)
   ·right
    rw [List.any_eq_true] at h1 ⊢
    obtain ⟨t,h2,h3⟩:=h1
    exact ⟨t,h2,h t h3⟩
  | false=>
   rw [d5n hd hA ha hb,Bool.or_eq_true] at hx ⊢
   rcases hx with h1 | h1
   ·exact Or.inl (ia h1)
   ·exact Or.inr (ib h1)
lemma d21 {n:ℕ} {C:Circuit} (h:TopForm.IsAO2 n C) {j:ℕ} (hj:j < C.gates.length):
  C.gates[j] = gateAt C j∧ (gateAt C j).inputs = [TopForm.opnd C j 0,TopForm.opnd C j 1]∧ 
  TopForm.opnd C j 0 < n + j∧ TopForm.opnd C j 1 < n + j∧ 
  ((gateAt C j).op = GateOp.and∨ (gateAt C j).op = GateOp.or):=by
 have e:gateAt C j = C.gates[j]:=List.getD_eq_getElem _ _ hj
 have hm:gateAt C j ∈ C.gates:=by rw [e];exact List.getElem_mem hj
 have hl:=h.2.2 _ hm
 obtain ⟨s,t,hst⟩:=List.length_eq_two.1 hl
 have hb:=h.2.1 j hj
 rw [hst] at hb
 have e0:TopForm.opnd C j 0 = s:=by unfold TopForm.opnd;rw [hst];rfl
 have e1:TopForm.opnd C j 1 = t:=by unfold TopForm.opnd;rw [hst];rfl
 refine ⟨e.symm,by rw [hst,e0,e1],by rw [e0];exact hb s (by simp),
  by rw [e1];exact hb t (by simp),h.1 _ hm⟩
lemma gDv {n:ℕ} (x:Fin n→ Bool) (w:ℕ) (hw:w < n):
  (List.ofFn x).getD w false = x ⟨w,hw⟩:=gD x ⟨w,hw⟩
lemma d3d {n:ℕ} {gs:List Gate} {w:ℕ} (hok:Ok n gs):TopForm.IsAO2 n ⟨gs,w⟩:=by
 refine ⟨?_,?_,?_⟩
 ·intro q hq
  obtain ⟨i,hi,rfl⟩:=List.getElem_of_mem hq
  obtain ⟨o',s',t',h1,h2,_⟩:=hok i hi
  rw [h1];exact h2
 ·intro j hj i hi
  obtain ⟨o',s',t',h1,h2,h3,h4⟩:=hok j hj
  have e1:gateAt ⟨gs,w⟩ j = gs[j]:=List.getD_eq_getElem _ _ hj
  rw [e1,h1] at hi
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
  rcases hi with rfl | rfl <;> assumption
 ·intro q hq
  obtain ⟨i,hi,rfl⟩:=List.getElem_of_mem hq
  obtain ⟨o',s',t',h1,h2,_⟩:=hok i hi
  rw [h1];rfl
open PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm
def d2p (C:Circuit) (j:ℕ):Bool:=
 match (gateAt C j).op with
 | .and=>true
 | _=>false
def val (n:ℕ) (C:Circuit) (x:Fin n→ Bool) (w:ℕ):Bool:=
 (run C.gates (List.ofFn x)).getD w false
def d13 (n:ℕ) (C:Circuit) (Del:Finset ℕ) (x:Fin n→ Bool) (w:ℕ):Bool:=
 u n (d2p C) (fun j=>opnd C j 0) (fun j=>opnd C j 1) Del (fun _=>[]) (List.ofFn x) w
lemma d5u {n:ℕ} (C:Circuit) (x:Fin n→ Bool) (w:ℕ) (hw:w < n):
  val n C x w = (List.ofFn x).getD w false:=by
 exact d4s C.gates (List.ofFn x) w (by simpa using hw)
lemma d5z {n:ℕ} (C:Circuit) (hC:IsAO2 n C) (x:Fin n→ Bool) (j:ℕ)
  (hj:j < C.gates.length):
  val n C x (n + j) = if d2p C j = true then
   val n C x (opnd C j 0) && val n C x (opnd C j 1)
  else val n C x (opnd C j 0) || val n C x (opnd C j 1):=by
 obtain ⟨heq,hin,ha,hb,hop⟩:=d21 hC hj
 have hr:=d4r C.gates (List.ofFn x) j hj
 rw [List.length_ofFn,heq,hin] at hr
 rcases hop with hop | hop
 ·simp only [val,hr,hop,List.map_cons,List.map_nil,if_pos ha,if_pos hb]
  simp [d2p,hop,GateOp.eval]
 ·simp only [val,hr,hop,List.map_cons,List.map_nil,if_pos ha,if_pos hb]
  simp [d2p,hop,GateOp.eval]
lemma d16 {n:ℕ} (C:Circuit) (hC:IsAO2 n C) (Del:Finset ℕ)
  (x:Fin n→ Bool):
  ∀ w < n + C.gates.length,d13 n C Del x w = true→ val n C x w = true:=by
 intro w
 induction w using Nat.strong_induction_on with
 | _ w ih=>
  intro hw h
  by_cases hin:w < n
  ·simpa only [d13,d5l hin,d5u C x w hin] using h
  obtain ⟨j,rfl⟩:∃ j,w = n + j:=⟨w - n,by omega⟩
  have hj:j < C.gates.length:=by omega
  obtain ⟨_,_,ha,hb,_⟩:=d21 hC hj
  by_cases hd:j ∈ Del
  ·simp only [d13,d5k hd] at h
   cases h
  rw [d5z C hC x j hj]
  cases hA:d2p C j with
  | false=>
   simp only [hA,Bool.false_eq_true,↓reduceIte]
   rw [d13,d5n hd hA ha hb,Bool.or_eq_true] at h
   rcases h with h | h
   ·rw [Bool.or_eq_true];exact Or.inl (ih _ ha (by omega) h)
   ·rw [Bool.or_eq_true];exact Or.inr (ih _ hb (by omega) h)
  | true=>
   simp only [hA,↓reduceIte]
   rw [d13,d5j hd hA ha hb] at h
   simp only [List.any_nil,Bool.or_false,Bool.and_eq_true] at h
   rw [Bool.and_eq_true];exact ⟨ih _ ha (by omega) h.1,ih _ hb (by omega) h.2⟩
lemma d14 {n:ℕ} (C:Circuit) (hC:IsAO2 n C) (j:ℕ)
  (x:Fin n→ Bool) (hz:val n C x (n + j) = false):
  ∀ w < n + C.gates.length,d13 n C {j} x w = val n C x w:=by
 intro w
 induction w using Nat.strong_induction_on with
 | _ w ih=>
  intro hw
  by_cases hin:w < n
  ·simp only [d13,d5l hin,d5u C x w hin]
  obtain ⟨k,rfl⟩:∃ k,w = n + k:=⟨w - n,by omega⟩
  have hk:k < C.gates.length:=by omega
  obtain ⟨_,_,ha,hb,_⟩:=d21 hC hk
  by_cases hd:k ∈ ({j}:Finset ℕ)
  ·have hkj:k = j:=Finset.mem_singleton.mp hd
   subst k
   rw [d13,d5k (Finset.mem_singleton_self j),hz]
  rw [d5z C hC x k hk]
  have ia:=ih (opnd C k 0) ha (by omega)
  have ib:=ih (opnd C k 1) hb (by omega)
  cases hA:d2p C k with
  | false=>
   simp only [hA,Bool.false_eq_true,↓reduceIte]
   rw [d13,d5n hd hA ha hb]
   exact congrArg₂ Bool.or ia ib
  | true=>
   simp only [hA,↓reduceIte]
   rw [d13,d5j hd hA ha hb]
   simp only [List.any_nil,Bool.or_false]
   exact congrArg₂ Bool.and ia ib
lemma d17 {n:ℕ} (C:Circuit) (hC:IsAO2 n C) (Del:Finset ℕ)
  (x y:Fin n→ Bool) (hxy:∀ i,x i = true→ y i = true)
  (w:ℕ) (hw:w < n + C.gates.length):
  d13 n C Del x w = true→ d13 n C Del y w = true:=by
 have hab:∀ j < C.gates.length,opnd C j 0 < n + j∧ opnd C j 1 < n + j:=by
  intro j hj
  exact ⟨(d21 hC hj).2.2.1,(d21 hC hj).2.2.2.1⟩
 have q3j:∀ t,(List.ofFn x).getD t false = true→ (List.ofFn y).getD t false = true:=by
  intro t ht
  by_cases ht':t < n
  ·rw [gDv y t ht']
   exact hxy ⟨t,ht'⟩ (by simpa only [gDv x t ht'] using ht)
  ·have:(List.ofFn x).getD t false = false:=
    List.getD_eq_default _ _ (by simp;omega)
   rw [this] at ht
   cases ht
 exact d5m hab (List.ofFn x) (List.ofFn y) q3j w hw
lemma d5y {n:ℕ} (C:Circuit) (x:Fin n→ Bool):
  val n C x C.output = circuitFun n C x:=rfl
lemma d43 {n:ℕ} (G:SimpleGraph (Fin n)) [DecidableRel G.Adj]
  (C:Circuit) (hF:circuitFun n C = graphFun G ∅) (hE:G.edgeFinset.Nonempty):
  C.output < n + C.gates.length:=by
 have hE':∃ p q,G.Adj p q:=by
  obtain ⟨e,he⟩:=hE
  induction e using Sym2.ind with
  | _ p q=>exact ⟨p,q,by simpa using he⟩
 obtain ⟨p,q,hpq⟩:=hE'
 have q0v:val n C (fun _=>true) C.output = true:=by
  rw [d5y,hF]
  exact (gf G _).mpr ⟨p,q,hpq,rfl,rfl⟩
 by_contra h
 have q0d:val n C (fun _=>true) C.output = false:=
  List.getD_eq_default _ _ (by rw [d4t,List.length_ofFn];omega)
 rw [q0d] at q0v
 cases q0v
lemma d0v {n:ℕ} (C:Circuit) (hC:IsAO2 n C) (j:ℕ)
  (hj:j < C.gates.length) (q08:C.output < n + C.gates.length):
  ∃ D:Circuit,IsAO2 n D∧ D.size < C.size∧ 
   ∀ x:Fin n→ Bool,circuitFun n D x = d13 n C {j} x C.output:=by
 obtain ⟨gs,m,hok,hm,_,q0r,_⟩:=d0k n (d2p C)
  (fun k=>opnd C k 0) (fun k=>opnd C k 1) {j} ∅ (fun _=>[])
  (fun _=>false) (by simp) (by simp) C.gates.length
  (fun k hk=>⟨(d21 hC hk).2.2.1,(d21 hC hk).2.2.2.1⟩)
 have q2l:((Finset.range C.gates.length).filter (· ∈ ({j}:Finset ℕ))).card = 1:=by
  have:(Finset.range C.gates.length).filter (· ∈ ({j}:Finset ℕ)) = {j}:=by
   ext k
   simp only [Finset.mem_filter,Finset.mem_range,Finset.mem_singleton]
   omega
  rw [this]
  simp
 simp only [q2l,Finset.notMem_empty,Finset.filter_false,Finset.card_empty,
  Nat.add_zero,List.length_nil,Finset.sum_const_zero] at q0r
 rcases hm C.output q08 with ⟨hbound,heq⟩
 cases ho:m C.output with
 | none=>
  refine ⟨⟨gs,n + gs.length⟩,d3d hok,by simp only [Circuit.size];omega,?_⟩
  intro x
  have q0d:(run gs (List.ofFn x)).getD (n + gs.length) false = false:=
   List.getD_eq_default _ _ (by rw [d4t,List.length_ofFn])
  change (run gs (List.ofFn x)).getD (n + gs.length) false = _
  rw [q0d]
  have hh:=heq x
  simpa only [ho,ov,d13] using hh
 | some w=>
  refine ⟨⟨gs,w⟩,d3d hok,by simp only [Circuit.size];omega,?_⟩
  intro x
  change (run gs (List.ofFn x)).getD w false = _
  have hh:=heq x
  simpa only [ho,ov,d13] using hh
lemma d2w {n:ℕ} (G:SimpleGraph (Fin n)) [DecidableRel G.Adj]
  (C:Circuit) (hL:IsLeastAO G C) (hE:G.edgeFinset.Nonempty) (j:ℕ)
  (hj:j < C.gates.length):
  ∃ p q:Fin n,G.Adj p q∧ d13 n C {j} (pairInput p q) C.output = false:=by
 have q08:=d43 G C hL.2.1 hE
 by_contra h
 push Not at h
 have hF:∀ x:Fin n→ Bool,d13 n C {j} x C.output = graphFun G ∅ x:=by
  intro x
  apply Bool.eq_iff_iff.mpr
  constructor
  ·intro hx
   have q17:=d16 C hL.1 {j} x C.output q08 hx
   rwa [d5y,hL.2.1] at q17
  ·intro hx
   obtain ⟨p,q,hpq,hp,hq⟩:=(gf G x).mp hx
   have q2m:d13 n C {j} (pairInput p q) C.output = true:=by
    cases ht:d13 n C {j} (pairInput p q) C.output
    ·exact (h p q hpq ht).elim
    ·rfl
   apply d17 C hL.1 {j} (pairInput p q) x ?_ C.output q08 q2m
   intro i hi
   have:i = p∨ i = q:=by simpa [pairInput] using hi
   rcases this with rfl | rfl <;> assumption
 obtain ⟨D,hAO,q0r,heq⟩:=d0v C hL.1 j hj q08
 have hDF:circuitFun n D = graphFun G ∅:=funext fun x=>(heq x).trans (hF x)
 have q36:=hL.2.2 D hAO hDF
 omega
lemma d15 {n:ℕ} (C:Circuit) (hC:IsAO2 n C) (j:ℕ)
  (x:Fin n→ Bool):
  ∀ w < n + C.gates.length,
   d13 n C {j} x w =
    (run (C.gates.set j ⟨GateOp.or,[]⟩) (List.ofFn x)).getD w false:=by
 intro w
 induction w using Nat.strong_induction_on with
 | _ w ih=>
  intro hw
  by_cases hin:w < n
  ·rw [d13,d5l hin,d4s _ _ w (by simpa using hin)]
  obtain ⟨k,rfl⟩:∃ k,w = n + k:=⟨w - n,by omega⟩
  have hk:k < C.gates.length:=by omega
  have hk':k < (C.gates.set j ⟨GateOp.or,[]⟩).length:=by simpa using hk
  have q1i:=d4r (C.gates.set j ⟨GateOp.or,[]⟩) (List.ofFn x) k hk'
  rw [List.length_ofFn] at q1i
  by_cases hkj:k = j
  ·subst k
   rw [d13,d5k (Finset.mem_singleton_self j),q1i]
   simp [GateOp.eval]
  have q27:k ∉ ({j}:Finset ℕ):=by simpa using hkj
  have hgt:(C.gates.set j ⟨GateOp.or,[]⟩)[k] = C.gates[k]:=by
   simp [List.getElem_set,hkj,Ne.symm hkj]
  obtain ⟨heq,q3k,ha,hb,hop⟩:=d21 hC hk
  rw [hgt,heq,q3k] at q1i
  simp only [List.map_cons,List.map_nil,if_pos ha,if_pos hb] at q1i
  have ia:=ih (opnd C k 0) ha (by omega)
  have ib:=ih (opnd C k 1) hb (by omega)
  rcases hop with hop | hop
  ·have hA:d2p C k = true:=by simp [d2p,hop]
   rw [d13,d5j q27 hA ha hb,q1i,hop]
   simp only [List.any_nil,Bool.or_false,GateOp.eval,List.all_cons,List.all_nil,
    Bool.and_true,id_eq]
   exact congrArg₂ Bool.and ia ib
  ·have hA:d2p C k = false:=by simp [d2p,hop]
   rw [d13,d5n q27 hA ha hb,q1i,hop]
   simp only [GateOp.eval,List.any_cons,List.any_nil,Bool.or_false,id_eq]
   exact congrArg₂ Bool.or ia ib
lemma d2x {n:ℕ} (G:SimpleGraph (Fin n)) [DecidableRel G.Adj]
  (C:Circuit) (hL:IsLeastAO G C) (hE:G.edgeFinset.Nonempty) (j:ℕ)
  (hj:j < C.gates.length):
  ∃ p q:Fin n,G.Adj p q∧ gateVal n C j (pairInput p q) = true∧ 
   circuitFun n ⟨C.gates.set j ⟨GateOp.or,[]⟩,C.output⟩ (pairInput p q) = false:=by
 obtain ⟨p,q,hpq,q0p⟩:=d2w G C hL hE j hj
 have q2n:circuitFun n ⟨C.gates.set j ⟨GateOp.or,[]⟩,C.output⟩ (pairInput p q) = false:=by
  change (run (C.gates.set j ⟨GateOp.or,[]⟩) (List.ofFn (pairInput p q))).getD C.output false = false
  rw [← d15 C hL.1 j (pairInput p q) C.output (d43 G C hL.2.1 hE)]
  exact q0p
 refine ⟨p,q,hpq,?_,q2n⟩
 cases hz:gateVal n C j (pairInput p q) with
 | true=>rfl
 | false=>
  have heq:=d14 C hL.1 j (pairInput p q) hz C.output
   (d43 G C hL.2.1 hE)
  rw [q0p,d5y,hL.2.1] at heq
  have hf:graphFun G ∅ (pairInput p q) = true:=
   (gf G _).mpr ⟨p,q,hpq,by simp [pairInput],by simp [pairInput]⟩
  rw [hf] at heq
  cases heq
lemma d2z {n:ℕ} (G:SimpleGraph (Fin n)) [DecidableRel G.Adj]
  (C:Circuit) (hL:IsLeastAO G C) (j:ℕ) (hj:j < C.gates.length):
  G.edgeFinset.Nonempty:=by
 by_contra q0e
 have q0e:G.edgeFinset = ∅:=Finset.not_nonempty_iff_eq_empty.mp q0e
 have q0q:∀ p q:Fin n,¬ G.Adj p q:=by
  intro p q hpq
  have he:s(p,q) ∈ G.edgeFinset:=by simpa using hpq
  rw [q0e] at he
  exact Finset.notMem_empty _ he
 let D:Circuit:=⟨[],n⟩
 have hAO:IsAO2 n D:=by
  simp [IsAO2,AndOrOnly,ReadsBack,D]
 have hF:circuitFun n D = graphFun G ∅:=by
  funext x
  have q0d:graphFun G ∅ x = false:=by
   cases hx:graphFun G ∅ x with
   | false=>rfl
   | true=>
    obtain ⟨p,q,hpq,_,_⟩:=(gf G x).mp hx
    exact (q0q p q hpq).elim
  rw [q0d]
  simp [circuitFun,D,Circuit.eval,Circuit.wires,List.getD_eq_getElem?_getD]
 have q0r:=hL.2.2 D hAO hF
 simp only [Circuit.size,D,List.length_nil] at q0r
 omega
lemma d2y {n:ℕ} (G:SimpleGraph (Fin n))
  [DecidableRel G.Adj] (C:Circuit) (hL:IsLeastAO G C) (j:ℕ)
  (hj:j < C.gates.length):
  ∃ p q:Fin n,G.Adj p q∧ gateVal n C j (pairInput p q) = true∧ 
   circuitFun n ⟨C.gates.set j ⟨GateOp.or,[]⟩,C.output⟩ (pairInput p q) = false:=by
 exact d2x G C hL (d2z G C hL j hj) j hj
end TightSupport.CriticalEdge
namespace TightSupport.Context
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
 PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership
 PEqualNP.CleanedNonEdge PEqualNP.TopForm
def d25 (w:List Bool) (g:Gate):Bool:=
 g.op.eval (g.inputs.map fun i=>w.getD i false)
def d58 (w:List Bool) (g:Gate):List Bool:=w ++ [d25 w g]
def d08 (w z:List Bool):Prop:=
 w.length = z.length∧ ∀ i,w.getD i false = true→ z.getD i false = true
def d02 (g:Gate):Prop:=g.op = GateOp.and∨ g.op = GateOp.or
lemma d33 {C:Circuit} (hC:Monotone2 C) {g:Gate} (hg:g ∈ C.gates):
  d02 g:=by
 simpa [d02] using (hC g hg).1
lemma d0i {w z:List Bool} (h:d08 w z) {g:Gate} (hg:d02 g)
  (hw:d25 w g = true):d25 z g = true:=by
 rcases hg with hop | hop
 ·simp only [d25,hop,GateOp.eval,List.all_map,List.all_eq_true,
   Function.comp_apply,id_eq] at hw ⊢
  exact fun i hi=>h.2 i (hw i hi)
 ·simp only [d25,hop,GateOp.eval,List.any_map,List.any_eq_true,
   Function.comp_apply,id_eq] at hw ⊢
  obtain ⟨i,hi,hv⟩:=hw
  exact ⟨i,hi,h.2 i hv⟩
lemma d0f {w z:List Bool} {a b:Bool} (h:d08 w z)
  (hab:a = true→ b = true):d08 (w ++ [a]) (z ++ [b]):=by
 refine ⟨by simp [h.1],?_⟩
 intro i hi
 rw [List.getD_eq_getElem?_getD] at hi ⊢
 by_cases hlt:i < w.length
 ·rw [List.getElem?_append_left hlt] at hi
  rw [List.getElem?_append_left (by rwa [← h.1])]
  simpa only [List.getD_eq_getElem?_getD] using h.2 i
   (by simpa only [List.getD_eq_getElem?_getD] using hi)
 ·rw [List.getElem?_append_right (Nat.le_of_not_gt hlt)] at hi
  rw [List.getElem?_append_right (by rw [← h.1];omega),← h.1]
  cases hd:i - w.length with
  | zero=>
   simp only [hd,List.getElem?_cons_zero,Option.getD_some] at hi ⊢
   exact hab hi
  | succ k=>simp [hd] at hi
lemma d1s (gs:List Gate) (hg:∀ g ∈ gs,d02 g)
  {w z:List Bool} (h:d08 w z):
  d08 (gs.foldl d58 w) (gs.foldl d58 z):=by
 induction gs generalizing w z with
 | nil=>exact h
 | cons g gs ih=>
  exact ih (fun k hk=>hg k (List.mem_cons_of_mem _ hk))
   (d0f h (d0i h (hg g (by simp))))
lemma d1r (gs:List Gate) (w:List Bool):
  (gs.foldl d58 w).length = w.length + gs.length:=by
 induction gs generalizing w with
 | nil=>simp
 | cons g gs ih=>
  rw [List.foldl_cons,ih]
  simp [d58]
  omega
lemma d1q (gs:List Gate) (w:List Bool) (i:ℕ) (hi:i < w.length):
  (gs.foldl d58 w).getD i false = w.getD i false:=by
 induction gs generalizing w with
 | nil=>rfl
 | cons g gs ih=>
  simp only [List.foldl_cons]
  rw [ih (d58 w g) (by simp [d58];omega)]
  simp [d58,List.getD_eq_getElem?_getD,List.getElem?_append_left hi]
lemma d38 {n:ℕ} (x:Fin n→ Bool) (u:Fin n):
  (List.ofFn x).getD u.val false = x u:=by
 simp [List.getD_eq_getElem?_getD]
lemma d39 {n:ℕ} {x y:Fin n→ Bool} (h:∀ u,x u = true→ y u = true):
  d08 (List.ofFn x) (List.ofFn y):=by
 refine ⟨by simp,?_⟩
 intro i hi
 by_cases hlt:i < n
 ·rw [d38 y ⟨i,hlt⟩]
  exact h ⟨i,hlt⟩ (by simpa only [d38 x ⟨i,hlt⟩] using hi)
 ·rw [List.getD_eq_getElem?_getD,List.getElem?_eq_none (by simpa using Nat.le_of_not_gt hlt)] at hi
  cases hi
def d49 (C:Circuit) (j:ℕ) (g:Gate):Circuit:=⟨C.gates.set j g,C.output⟩
def d1i (C:Circuit) (j:ℕ) (w:List Bool):List Bool:=
 (C.gates.take j).foldl d58 w
def off:Gate:=⟨GateOp.or,[]⟩
lemma d61 {C:Circuit} {j:ℕ} (hj:j < C.gates.length) (g:Gate) (w:List Bool):
  (d49 C j g).wires w = (C.gates.drop (j + 1)).foldl d58 (d58 (d1i C j w) g):=by
 change (C.gates.set j g).foldl d58 w = _
 rw [List.set_eq_take_append_cons_drop,ite_eq_left hj,List.foldl_append,List.foldl_cons]
 rfl
lemma d42 {C:Circuit} {j:ℕ} (hj:j < C.gates.length):
  d49 C j C.gates[j] = C:=by
 cases C with
 | mk gates output=>
  change Circuit.mk (gates.set j gates[j]) output = Circuit.mk gates output
  congr 1
  exact List.set_getElem_self hj
lemma d4a {n:ℕ} {C:Circuit} {j:ℕ} (hj:j < C.gates.length)
  (g:Gate) (x:Fin n→ Bool):
  gateVal n (d49 C j g) j x = d25 (d1i C j (List.ofFn x)) g:=by
 have q06:(d1i C j (List.ofFn x)).length = n + j:=by
  unfold d1i
  rw [d1r]
  simp [Nat.min_eq_left (Nat.le_of_lt hj)]
 unfold gateVal
 rw [d61 hj,d1q _ _ _ (by simp [d58,q06]),← q06]
 simp [d58,List.getD_eq_getElem?_getD]
lemma d00 {n:ℕ} {C:Circuit} (hAO:IsAO2 n C):Monotone2 C:=by
 intro g hg
 exact ⟨hAO.1 g hg,by rw [hAO.2.2 g hg]⟩
def d0y (b:Bool):Gate:=if b then ⟨GateOp.and,[]⟩ else off
lemma d0z (w:List Bool) (b:Bool):d25 w (d0y b) = b:=by
 cases b <;> rfl
def d26 {n:ℕ} (C:Circuit) (j:ℕ) (x:Fin n→ Bool) (b:Bool):Bool:=
 circuitFun n (d49 C j (d0y b)) x
lemma d4w {C:Circuit} {j:ℕ} (hj:j < C.gates.length)
  (g h:Gate) (w:List Bool)
  (q3l:d25 (d1i C j w) g = d25 (d1i C j w) h):
  (d49 C j g).wires w = (d49 C j h).wires w:=by
 rw [d61 hj,d61 hj]
 simp only [d58,q3l]
lemma d27 {n:ℕ} {C:Circuit} (hAO:IsAO2 n C)
  {j:ℕ} (hj:j < C.gates.length)
  (x y:Fin n→ Bool) (b c:Bool)
  (hxy:∀ v,x v = true→ y v = true) (hbc:b = true→ c = true):
  d26 C j x b = true→ d26 C j y c = true:=by
 have hC:Monotone2 C:=d00 hAO
 have hp:d08 (d1i C j (List.ofFn x)) (d1i C j (List.ofFn y)):=
  d1s _ (fun g hg=>d33 hC (List.mem_of_mem_take hg)) (d39 hxy)
 have ha:d08
   (d58 (d1i C j (List.ofFn x)) (d0y b))
   (d58 (d1i C j (List.ofFn y)) (d0y c)):=by
  apply d0f hp
  simpa only [d0z] using hbc
 have hw:d08
   ((d49 C j (d0y b)).wires (List.ofFn x))
   ((d49 C j (d0y c)).wires (List.ofFn y)):=by
  rw [d61 hj,d61 hj]
  exact d1s _ (fun g hg=>d33 hC (List.mem_of_mem_drop hg)) ha
 exact hw.2 C.output
lemma d29 {n:ℕ} {C:Circuit} {j:ℕ}
  (hj:j < C.gates.length) (g:Gate) (x:Fin n→ Bool):
  d26 C j x (d25 (d1i C j (List.ofFn x)) g) =
   circuitFun n (d49 C j g) x:=by
 have hw:=d4w hj
  (d0y (d25 (d1i C j (List.ofFn x)) g)) g (List.ofFn x)
  (d0z _ _)
 exact congrArg (fun w:List Bool=>w.getD C.output false) hw
lemma d2a {n:ℕ} {C:Circuit} {j:ℕ}
  (hj:j < C.gates.length) (g:Gate) (x:Fin n→ Bool):
  d26 C j x (gateVal n (d49 C j g) j x) = circuitFun n (d49 C j g) x:=by
 rw [d4a hj]
 exact d29 hj g x
lemma d28 {n:ℕ} {C:Circuit} {j:ℕ}
  (hj:j < C.gates.length) (x:Fin n→ Bool):
  d26 C j x (gateVal n C j x) = circuitFun n C x:=by
 have h:=d2a hj C.gates[j] x
 rwa [d42 hj] at h
lemma d1j {n:ℕ} (C:Circuit) {j:ℕ}
  (hj:j < C.gates.length) (x:Fin n→ Bool):
  (d1i C j (List.ofFn x)).length = n + j:=by
 unfold d1i
 rw [d1r]
 simp [Nat.min_eq_left (Nat.le_of_lt hj)]
lemma d1k {n:ℕ} (C:Circuit) {j:ℕ}
  (hj:j < C.gates.length) (x:Fin n→ Bool) (w:ℕ) (hw:w < n + j):
  (d1i C j (List.ofFn x)).getD w false = wireVal n C w x:=by
 have q06:=d1j C hj x
 have heq:=d61 hj C.gates[j] (List.ofFn x)
 rw [d42 hj] at heq
 change _ = (C.wires (List.ofFn x)).getD w false
 rw [heq,d1q _ _ _ (by simp [d58,q06];omega)]
 simp [d58,List.getD_eq_getElem?_getD,
  List.getElem?_append_left (show w < (d1i C j (List.ofFn x)).length by omega)]
lemma d4b {n:ℕ} (C:Circuit) {j:ℕ}
  (hj:j < C.gates.length) (x:Fin n→ Bool) (v:Fin n)
  (w:ℕ) (hw:w < n + j):
  d25 (d1i C j (List.ofFn x)) ⟨GateOp.and,[v.val,w]⟩ =
   (x v && wireVal n C w x):=by
 simp only [d25,GateOp.eval,List.map_cons,List.map_nil,List.all_cons,
  List.all_nil,id_eq,Bool.and_true]
 rw [d1k C hj x w hw]
 unfold d1i
 rw [d1q _ _ _ (by simp),d38]
lemma d2b {n:ℕ} {C:Circuit} {j:ℕ}
  (hj:j < C.gates.length) (v:Fin n) (w:ℕ) (hw:w < n + j)
  (x:Fin n→ Bool):
  d26 C j x (x v && wireVal n C w x) =
   circuitFun n (d49 C j ⟨GateOp.and,[v.val,w]⟩) x:=by
 rw [← d4b C hj x v w hw]
 exact d29 hj _ x
end TightSupport.Context
namespace TightSupport.Tight
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
 PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm
 PEqualNP.Outside.L_meta_5012.TightSupport.Budget
variable {n:ℕ} {G:SimpleGraph (Fin n)} [DecidableRel G.Adj] {C:Circuit}
lemma d30 {g h w:ℕ}
  (q04:readers n C g = {h}) (q2o:(gateAt C h).op = GateOp.and)
  (hr:OrReaches n C w g):w = n + g:=by
 rcases d2u (d3s g w hr).1 with he | ⟨k,hk,hop,hin,_,_⟩
 ·exact he
 ·have hkr:k ∈ readers n C g:=
   Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hk,hin⟩
  rw [q04,Finset.mem_singleton] at hkr
  rw [hkr,q2o] at hop
  cases hop
lemma d5c {g h:ℕ} (hAO:IsAO2 n C)
  (hT:TopForm G C) (hpair:junk G C = {g,h})
  (q04:readers n C g = {h}) (b:Fin 2)
  (hne:opnd C h b ≠ n + g) (x:Fin n→ Bool):
  val C (List.ofFn x) (opnd C h b) = true↔ 
   ∃ u ∈ side (n:=n) C h b,x u = true:=by
 have hh:h ∈ junk G C:=by simp [hpair]
 obtain ⟨q06,q0j,_⟩:=d2q hh
 constructor
 ·intro hv
  obtain ⟨w,hr,hw,q0w⟩:=d41 (n:=n) (C:=C)
   (x:=List.ofFn x) (by simp) (opnd C h b) hv
  rcases q0w with q15 | ⟨k,hk,rfl,q1d⟩
  ·refine ⟨⟨w,q15⟩,d4e _ hr,?_⟩
   exact (d5w C x ⟨w,q15⟩).symm.trans hw
  ·exfalso
   have q0x:=(hAO.1 _ (d23 hk)).resolve_right q1d
   have q02:OrReaches n C (opnd C h b) k:=d4f hr k rfl hk
   have hkj:=d3f hAO hT q06 q0j q02 q0x
   simp only [hpair,Finset.mem_insert,Finset.mem_singleton] at hkj
   rcases hkj with rfl | rfl
   ·exact hne (d30 q04 q0j q02)
   ·have hle:=d3y hr
    have hlt:=d3k hAO q06 b
    omega
 ·rintro ⟨u,hu,hux⟩
  exact d54 hu hux
lemma d0u {h m w:ℕ} (q04:readers n C h = {m})
  (q3m:w ≠ n + h) (hr:OrReaches n C w h)
  {r:Fin n} (hrm:r ∈ orIn n C (n + m)):r ∈ orIn n C w:=by
 rcases d2u (d3s h w hr).1 with he | ⟨k,hk,_,hin,_,q2p⟩
 ·exact (q3m he).elim
 ·have hkr:k ∈ readers n C h:=
   Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hk,hin⟩
  rw [q04,Finset.mem_singleton] at hkr
  subst k
  exact d4e r (q2p.trans (d32 r hrm))
lemma d5f {a h:ℕ} (hE:centreless G C = ∅)
  (ha:a ∈ tops G C) (hh:h ∈ junk G C) (b:Fin 2):
  opnd C a b ≠ n + h:=by
 intro heq
 have q0e:side (n:=n) C a b = ∅:=by
  change orIn n C (opnd C a b) = ∅
  rw [heq]
  exact d0b (d2q hh).2.1
 have q1t:=d1o ha q0e
 rw [hE] at q1t
 exact Finset.notMem_empty _ q1t
lemma d5g {g h a:ℕ} (hAO:IsAO2 n C)
  (hT:TopForm G C) (hpair:junk G C = {g,h})
  (q04:readers n C g = {h}) (hE:centreless G C = ∅)
  (ha:a ∈ tops G C) (b:Fin 2) (x:Fin n→ Bool):
  val C (List.ofFn x) (opnd C a b) = true↔ 
   (∃ u ∈ side (n:=n) C a b,x u = true)∨ 
   (OrReaches n C (opnd C a b) h∧ gateVal n C h x = true):=by
 obtain ⟨q2q,q2r,_⟩:=d5e ha
 have hh:h ∈ junk G C:=by simp [hpair]
 constructor
 ·intro hv
  obtain ⟨w,hr,hw,q0w⟩:=d41 (n:=n) (C:=C)
   (x:=List.ofFn x) (by simp) (opnd C a b) hv
  rcases q0w with q15 | ⟨k,hk,rfl,q1d⟩
  ·exact Or.inl ⟨⟨w,q15⟩,d4e _ hr,
    (d5w C x ⟨w,q15⟩).symm.trans hw⟩
  ·have q0x:=(hAO.1 _ (d23 hk)).resolve_right q1d
   have q02:OrReaches n C (opnd C a b) k:=d4f hr k rfl hk
   have hkj:=d3f hAO hT q2q q2r q02 q0x
   simp only [hpair,Finset.mem_insert,Finset.mem_singleton] at hkj
   rcases hkj with rfl | rfl
   ·exact (d5f hE ha (show k ∈ junk G C by simp [hpair]) b
     (d30 q04 (d2q hh).2.1 q02)).elim
   ·exact Or.inr ⟨q02,hw⟩
 ·rintro (⟨u,hu,hux⟩ | ⟨hr,hv⟩)
  ·exact d54 hu hux
  ·exact d40 (n:=n) (by simp) (d3s h _ hr).1 hv
lemma d5h {h a:ℕ} (hAO:IsAO2 n C)
  (ha:a ∈ tops G C) (hh:h ∈ junk G C) (b:Fin 2)
  (hb:OrReaches n C (opnd C a b) h):
  ¬ OrReaches n C (opnd C a (1 - b)) h:=by
 intro hb'
 apply d2r hh
 intro x hx
 apply (d5e ha).2.2 x
 apply (d0d hAO (d5e ha).1 (d5e ha).2.1 x).mpr
 intro d
 have hd:d = b∨ d = 1 - b:=by omega
 rcases hd with rfl | rfl
 ·exact d40 (n:=n) (by simp) (d3s h _ hb).1 hx
 ·exact d40 (n:=n) (by simp) (d3s h _ hb').1 hx
lemma d4y {g h m a:ℕ} (hAO:IsAO2 n C)
  (hT:TopForm G C) (hpair:junk G C = {g,h})
  (hreadg:readers n C g = {h}) (hreadh:readers n C h = {m})
  (hE:centreless G C = ∅) (ha:a ∈ tops G C) (b:Fin 2)
  (u v r:Fin n) (hr:r ∈ orIn n C (n + m))
  (q0y:gateVal n C a (pairInput u v) = true)
  (q0f:¬ ∃ z ∈ side (n:=n) C a b,pairInput u v z = true):
  r ∈ side (n:=n) C a b∧ 
  (∀ x:Fin n→ Bool,
   ((∃ z ∈ side (n:=n) C a b,x z = true)∨ gateVal n C h x = true)→ 
   (∃ z ∈ side (n:=n) C a (1 - b),x z = true)→ graphFun G ∅ x = true)∧ 
  (∃ z ∈ side (n:=n) C a (1 - b),pairInput u v z = true):=by
 have hh:h ∈ junk G C:=by simp [hpair]
 have q1y:=(d0d hAO (d5e ha).1 (d5e ha).2.1 _).mp q0y
 obtain ⟨hb,_⟩:=((d5g hAO hT hpair hreadg hE ha b _).mp
  (q1y b)).resolve_left q0f
 have q1z:=((d5g hAO hT hpair hreadg hE ha (1 - b) _).mp
  (q1y (1 - b))).resolve_right (fun hz=>d5h hAO ha hh b hb hz.1)
 refine ⟨d0u hreadh (d5f hE ha hh b) hb hr,?_,q1z⟩
 intro x hxb hxo
 apply (d5e ha).2.2 x
 apply (d0d hAO (d5e ha).1 (d5e ha).2.1 x).mpr
 have hvb:val C (List.ofFn x) (opnd C a b) = true:=
  (d5g hAO hT hpair hreadg hE ha b x).mpr (hxb.imp_right (fun hx=>⟨hb,hx⟩))
 have hvo:val C (List.ofFn x) (opnd C a (1 - b)) = true:=by
  obtain ⟨z,hz,hzx⟩:=hxo
  exact d54 hz hzx
 intro d
 have hd:d = b∨ d = 1 - b:=by omega
 rcases hd with rfl | rfl
 ·exact hvb
 ·exact hvo
lemma d4x {g h m a:ℕ} (hAO:IsAO2 n C)
  (hT:TopForm G C) (hpair:junk G C = {g,h})
  (hreadg:readers n C g = {h}) (hreadh:readers n C h = {m})
  (hE:centreless G C = ∅) (ha:a ∈ tops G C) (b:Fin 2)
  (u v r:Fin n) (hr:r ∈ orIn n C (n + m))
  (q0y:gateVal n C a (pairInput u v) = true)
  (q0f:¬ ∃ z ∈ side (n:=n) C a b,pairInput u v z = true):
  ∃ R T:Finset (Fin n),r ∈ R∧ 
   (∀ x:Fin n→ Bool,
    ((decide (∃ z ∈ R,x z = true) || gateVal n C h x) &&
     decide (∃ z ∈ T,x z = true)) = true→ graphFun G ∅ x = true)∧ 
   (decide (∃ z ∈ R,pairInput u v z = true):Bool) = false∧ 
   (decide (∃ z ∈ T,pairInput u v z = true):Bool) = true:=by
 obtain ⟨hrr,q01,ht⟩:=d4y hAO hT hpair hreadg hreadh hE
  ha b u v r hr q0y q0f
 refine ⟨side (n:=n) C a b,side (n:=n) C a (1 - b),hrr,?_,by simp [q0f],by simp [ht]⟩
 intro x hx
 simp only [Bool.and_eq_true,Bool.or_eq_true,decide_eq_true_eq] at hx
 exact q01 x hx.1 hx.2
end TightSupport.Tight
namespace TightSupport.CutTrace
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
 PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm
 PEqualNP.Outside.L_meta_5012.TightSupport.Budget
def off (C:Circuit) (h:ℕ):Circuit:=⟨C.gates.set h ⟨GateOp.or,[]⟩,C.output⟩
lemma d3a {C:Circuit} {h j:ℕ} (hj:j < C.gates.length) (q38:j ≠ h):
  gateAt (off C h) j = gateAt C j:=by
 rw [d22 (show j < (off C h).gates.length by simpa [off] using hj),d22 hj]
 simp [off,List.getElem_set,q38,Ne.symm q38]
lemma d3b {n:ℕ} {C:Circuit} {h:ℕ}
  (hh:(gateAt C h).op = GateOp.and) (x:Fin n→ Bool) {w z:ℕ}
  (hr:Relation.ReflTransGen (d04 n C) w z)
  (hv:val (off C h) (List.ofFn x) z = true):
  val (off C h) (List.ofFn x) w = true:=by
 induction hr using Relation.ReflTransGen.head_induction_on with
 | refl=>exact hv
 | head q05 _ ih=>
  obtain ⟨k,hk,rfl,hop,hin,hlt⟩:=q05
  have hkh:k ≠ h:=by intro heq;subst k;rw [hh] at hop;cases hop
  have heq:=d3a hk hkh
  apply (d5x (n:=n) (by simp) (show k < (off C h).gates.length by simpa [off] using hk)
   (show (gateAt (off C h) k).op = GateOp.or by rw [heq];exact hop)).mpr
  exact ⟨_,by rw [heq];exact hin,hlt,ih⟩
lemma d3c {n:ℕ} {C:Circuit} {h:ℕ}
  (hh:(gateAt C h).op = GateOp.and) (x:Fin n→ Bool)
  {a:ℕ} {b:Fin 2} {u:Fin n}
  (hu:u ∈ side (n:=n) C a b) (hxu:x u = true):
  val (off C h) (List.ofFn x) (opnd C a b) = true:=by
 apply d3b hh x (d32 u hu)
 rw [d5w]
 exact hxu
lemma d12 {n:ℕ} (G:SimpleGraph (Fin n)) [DecidableRel G.Adj]
  (C:Circuit) (hAO:IsAO2 n C) (hF:circuitFun n C = graphFun G ∅)
  (h:ℕ) (q0i:h ∈ junk G C) (u v:Fin n) (huv:G.Adj u v)
  (q0p:circuitFun n (off C h) (pairInput u v) = false):
  ∃ a ∈ tops G C,∃ b:Fin 2,
   gateVal n C a (pairInput u v) = true∧ 
   val (off C h) (List.ofFn (pairInput u v)) (opnd C a b) = false∧ 
   (∀ t ∈ side (n:=n) C a b,t ≠ u∧ t ≠ v):=by
 have q08:∀ x:Fin n→ Bool,val C (List.ofFn x) C.output = graphFun G ∅ x:=
  fun x=>congrFun hF x
 obtain ⟨a,ha,q20,hr,hav⟩:=d1n G (graphFun G ∅)
  (fun p q hpq=>(d2i G p q).mp hpq) q08 u v ((d2i G u v).mpr huv)
 have q0j:(gateAt C a).op = GateOp.and:=
  (hAO.1 _ (d23 ha)).resolve_right q20
 have q03:BelowF G C a:=fun x hx=>
  d0g (graphFun G ∅) q08 a hr x (d2c n C a x ▸ hx)
 have q2s:a ∈ tops G C:=by
  simpa only [tops,gatesWhere,Finset.mem_filter,Finset.mem_range] using
   And.intro ha (And.intro q0j q03)
 have hah:a ≠ h:=by
  intro heq
  subst a
  exact d2r q0i q03
 have q1e:=(d2q q0i).2.1
 have q1c:val (off C h) (List.ofFn (pairInput u v)) (n + a) = false:=by
  cases hv:val (off C h) (List.ofFn (pairInput u v)) (n + a) with
  | false=>rfl
  | true=>
   have ho:=d3b q1e (pairInput u v) hr hv
   change circuitFun n (off C h) (pairInput u v) = true at ho
   rw [q0p] at ho
   cases ho
 have hex:∃ b:Fin 2,val (off C h) (List.ofFn (pairInput u v)) (opnd C a b) = false:=by
  by_contra! q28
  have q0v:val (off C h) (List.ofFn (pairInput u v)) (n + a) = true:=by
   apply (d5r (n:=n) (by simp)
    (show a < (off C h).gates.length by simpa [off] using ha)
    (show (gateAt (off C h) a).op = GateOp.and by rw [d3a ha hah];exact q0j)).mpr
   intro w hw
   rw [d3a ha hah] at hw
   obtain ⟨b,rfl⟩:=d2o hAO ha hw
   refine ⟨d3k hAO ha b,?_⟩
   cases hv:val (off C h) (List.ofFn (pairInput u v)) (opnd C a b) with
   | false=>exact ((q28 b) hv).elim
   | true=>rfl
  rw [q1c] at q0v
  cases q0v
 obtain ⟨b,hb⟩:=hex
 refine ⟨a,q2s,b,?_,hb,?_⟩
 ·rwa [d2c]
 ·intro t ht
  constructor <;> intro heq
  ·subst t
   have:=d3c q1e (pairInput u v) ht (d46 u v)
   rw [hb] at this
   cases this
  ·subst t
   have:=d3c q1e (pairInput u v) ht (d47 u v)
   rw [hb] at this
   cases this
end TightSupport.CutTrace
namespace TightSupport.TightCut
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
 PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm
 PEqualNP.Outside.L_meta_5012.TightSupport.Budget PEqualNP.Outside.L_meta_5012.TightSupport.CutTrace
 PEqualNP.Outside.L_meta_5012.TightSupport.Tight
lemma d11 {n:ℕ} (G:SimpleGraph (Fin n)) [DecidableRel G.Adj]
  (C:Circuit) (hAO:IsAO2 n C) (hF:circuitFun n C = graphFun G ∅)
  (hT:TopForm G C) (g h m:ℕ) (hpair:junk G C = {g,h})
  (hreadg:readers n C g = {h}) (hreadh:readers n C h = {m})
  (hE:centreless G C = ∅) (r:Fin n) (hr:r ∈ orIn n C (n + m))
  (u v:Fin n) (huv:G.Adj u v)
  (q0p:circuitFun n (off C h) (pairInput u v) = false):
  ∃ R T:Finset (Fin n),r ∈ R∧ 
   (∀ x:Fin n→ Bool,
    ((decide (∃ z ∈ R,x z = true) || gateVal n C h x) &&
     decide (∃ z ∈ T,x z = true)) = true→ graphFun G ∅ x = true)∧ 
   (decide (∃ z ∈ R,pairInput u v z = true):Bool) = false∧ 
   (decide (∃ z ∈ T,pairInput u v z = true):Bool) = true:=by
 have q0i:h ∈ junk G C:=by rw [hpair];simp
 obtain ⟨a,ha,b,q0y,_,q0f⟩:=
  d12 G C hAO hF h q0i u v huv q0p
 apply d4x hAO hT hpair hreadg hreadh hE ha b u v r hr q0y
 rintro ⟨z,hz,hzp⟩
 have q3n:z = u∨ z = v:=by simpa [pairInput] using hzp
 exact q3n.elim (q0f z hz).1 (q0f z hz).2
end TightSupport.TightCut
namespace TightSupport.SerialReplacement
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
 PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm
 PEqualNP.Outside.L_meta_5012.TightSupport.Budget
def d4m (C:Circuit) (h:ℕ) (q:Gate):Circuit:=⟨C.gates.set h q,C.output⟩
lemma d4o {C:Circuit} {h k:ℕ} (q:Gate) (hkh:k ≠ h):
  gateAt (d4m C h q) k = gateAt C k:=by
 simp [d4m,gateAt,List.getD_eq_getElem?_getD,List.getElem?_set_ne (Ne.symm hkh)]
lemma d4p {C:Circuit} {h:ℕ} (q:Gate) (hh:h < C.gates.length):
  gateAt (d4m C h q) h = q:=by
 rw [d22 (show h < (d4m C h q).gates.length by simpa [d4m] using hh)]
 simp [d4m,List.getElem_set]
lemma d4n {n:ℕ} {C:Circuit} (hAO:IsAO2 n C) (h:ℕ) (q:Gate)
  (q2t:q.op = GateOp.and∨ q.op = GateOp.or) (q1f:q.inputs.length = 2)
  (q0z:∀ w ∈ q.inputs,w < n + h):IsAO2 n (d4m C h q):=by
 refine ⟨?_,?_,?_⟩
 ·intro a ha
  rcases List.mem_or_eq_of_mem_set ha with ha | rfl
  ·exact hAO.1 a ha
  ·exact q2t
 ·intro k hk w hw
  have hk':k < C.gates.length:=by simpa [d4m] using hk
  by_cases hkh:k = h
  ·subst k
   rw [d4p q hk'] at hw
   exact q0z w hw
  ·rw [d4o q hkh] at hw
   exact hAO.2.1 k hk' w hw
 ·intro a ha
  rcases List.mem_or_eq_of_mem_set ha with ha | rfl
  ·exact hAO.2.2 a ha
  ·exact q1f
lemma d56 {n:ℕ} (G:SimpleGraph (Fin n))
  [DecidableRel G.Adj] (C:Circuit) (hL:IsLeastAO G C)
  (g h:ℕ) (hg:g ∈ junk G C) (q04:readers n C g = {h})
  (q:Gate) (q2t:q.op = GateOp.and∨ q.op = GateOp.or)
  (q1f:q.inputs.length = 2) (q0z:∀ w ∈ q.inputs,w < n + h)
  (q1g:n + g ∉ q.inputs)
  (q3o:circuitFun n (d4m C h q) = graphFun G ∅):False:=by
 have q10:h ∈ readers n C g:=by rw [q04];simp
 have hh:=(d4j q10).1
 have hgN:=(d2q hg).1
 have q08:C.output ≠ n + g:=by
  intro heq
  apply d2r hg
  intro x hx
  have hf:val C (List.ofFn x) C.output = graphFun G ∅ x:=congrFun hL.2.1 x
  rw [heq] at hf
  exact hf.symm.trans hx
 let D:=d4m C h q
 have hD:IsAO2 n D:=d4n hL.1 h q q2t q1f q0z
 have q21:∀ E:Circuit,IsAO2 n E→ circuitFun n E = circuitFun n D→ D.size ≤ E.size:=by
  intro E hE hEF
  have hs:=hL.2.2 E hE (hEF.trans q3o)
  simpa [D,d4m,Circuit.size] using hs
 obtain ⟨k,hk,hkg⟩:=PEqualNP.Outside.L_meta_5012.TightSupport.Budget.d4l hD q21
  (show g < D.gates.length by simpa [D,d4m] using hgN) q08
 have hk':k < C.gates.length:=by simpa [D,d4m] using hk
 by_cases hkh:k = h
 ·subst k
  have q1h:gateAt D h = q:=d4p q hh
  rw [q1h] at hkg
  exact q1g hkg
 ·have q1h:gateAt D k = gateAt C k:=d4o q hkh
  rw [q1h] at hkg
  have hkr:k ∈ readers n C g:=Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hk',hkg⟩
  rw [q04,Finset.mem_singleton] at hkr
  exact hkh hkr
end TightSupport.SerialReplacement
namespace TightSupport.Factor
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
 PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm
 PEqualNP.Outside.L_meta_5012.TightSupport.Budget PEqualNP.Outside.L_meta_5012.TightSupport.Tight
variable {n:ℕ} {G:SimpleGraph (Fin n)} [DecidableRel G.Adj] {C:Circuit}
lemma d1l {g h:ℕ} (hAO:IsAO2 n C)
  (hT:TopForm G C) (hpair:junk G C = {g,h}) (hgh:g < h)
  (b:Fin 2) (x:Fin n→ Bool):
  val C (List.ofFn x) (opnd C g b) = true↔ 
   ∃ u ∈ side (n:=n) C g b,x u = true:=by
 have hg:g ∈ junk G C:=by simp [hpair]
 obtain ⟨glen,gand,_⟩:=d2q hg
 constructor
 ·intro hv
  obtain ⟨w,hr,hw,q0w⟩:=d41 (n:=n) (C:=C)
   (x:=List.ofFn x) (by simp) (opnd C g b) hv
  rcases q0w with q15 | ⟨k,hk,rfl,q1d⟩
  ·exact ⟨⟨w,q15⟩,d4e _ hr,(d5w C x ⟨w,q15⟩).symm.trans hw⟩
  ·exfalso
   have q0x:=(hAO.1 _ (d23 hk)).resolve_right q1d
   have q02:OrReaches n C (opnd C g b) k:=d4f hr k rfl hk
   have hkj:=d3f hAO hT glen gand q02 q0x
   simp only [hpair,Finset.mem_insert,Finset.mem_singleton] at hkj
   have hle:=d3y hr
   have hlt:=d3k hAO glen b
   omega
 ·rintro ⟨u,hu,hux⟩
  exact d54 hu hux
lemma d1m {g h:ℕ} (hAO:IsAO2 n C)
  (hT:TopForm G C) (hpair:junk G C = {g,h}) (hgh:g < h) (b:Fin 2):
  (side (n:=n) C g b).Nonempty:=by
 have hg:g ∈ junk G C:=by simp [hpair]
 obtain ⟨glen,gand,x,hx,_⟩:=d2q hg
 have hv:=(d0d hAO glen gand x).mp hx b
 obtain ⟨u,hu,_⟩:=(d1l hAO hT hpair hgh b x).mp hv
 exact ⟨u,hu⟩
lemma d4d {k:ℕ} (q0f:(orIn n C (n + k)).Nonempty):
  ¬ BelowF G C k:=by
 obtain ⟨u,hu⟩:=q0f
 intro q03
 have hv:gateVal n C k (pairInput u u) = true:=
  d4i (pairInput u u) _ u (d32 u hu) (d46 u u)
 exact G.irrefl ((d2i G u u).mp (q03 _ hv))
lemma d4c {m:ℕ} (hAO:IsAO2 n C)
  (q09:orN G C \ lam G C = {m})
  (s:Fin n→ Bool) (hs:∀ u v,G.Adj u v→ s u ≠ s v)
  (w:ℕ) (hwm:w < n + m) (q0f:(orIn n C w).Nonempty):
  ∃ t:Bool,∀ u ∈ orIn n C w,s u = t:=by
 classical
 obtain ⟨u,hu⟩:=q0f
 refine ⟨s u,?_⟩
 by_cases hwn:w < n
 ·intro v hv
  have raw_eq (a:Fin n) (ha:a ∈ orIn n C w):a.val = w:=by
   simp only [orIn,Finset.mem_filter,Finset.mem_univ,true_and] at ha
   obtain he | ⟨k,_,hr,_,_⟩:=ha
   ·exact he
   ·exact (Nat.not_le_of_lt hwn hr.1).elim
  have huv:v = u:=Fin.ext ((raw_eq v hv).trans (raw_eq u hu).symm)
  rw [huv]
 ·have hm:m ∈ orN G C:=(Finset.mem_sdiff.mp (show m ∈ orN G C \ lam G C by simp [q09])).1
  have q22:m < C.gates.length∧ (gateAt C m).op = GateOp.or∧ ¬ BelowF G C m:=by
   simpa only [orN,gatesWhere,Finset.mem_filter,Finset.mem_range] using hm
  have q3p:=q22.1
  have q2u:w = n + (w - n):=by omega
  have q23:w - n < C.gates.length:=by omega
  have q1d:(gateAt C (w - n)).op = GateOp.or:=by
   rcases hAO.1 _ (d23 q23) with q0j | hor
   ·have hz:=d0b (n:=n) q0j
    rw [← q2u] at hz
    exact (Finset.notMem_empty u (hz ▸ hu)).elim
   ·exact hor
  have hnb:¬ BelowF G C (w - n):=d4d (G:=G)
   (q2u ▸ (show (orIn n C w).Nonempty from ⟨u,hu⟩))
  have q3q:w - n ∈ orN G C:=by
   simpa only [orN,gatesWhere,Finset.mem_filter,Finset.mem_range] using
    And.intro q23 (And.intro q1d hnb)
  intro v hv
  have hmono:=PEqualNP.Outside.L_meta_5012.TightSupport.Color.d5b
   G C hAO s hs m q09 (w - n) (by omega) q3q
  rw [← q2u] at hmono
  exact hmono v hv u hu
lemma d37 {g h:ℕ} (hAO:IsAO2 n C)
  (hh:h ∈ junk G C) (b:Fin 2) (hb:opnd C h b = n + g) (x:Fin n→ Bool):
  gateVal n C h x = true↔ gateVal n C g x = true∧ 
   val C (List.ofFn x) (opnd C h (1 - b)) = true:=by
 have hv:=d0d hAO (d2q hh).1 (d2q hh).2.1 x
 constructor
 ·intro hx
  have q28:=hv.mp hx
  refine ⟨?_,q28 (1 - b)⟩
  have hgb:=q28 b
  rw [hb] at hgb
  exact hgb
 ·intro hx
  apply hv.mpr
  intro d
  have hd:d = b∨ d = 1 - b:=by omega
  rcases hd with rfl | rfl
  ·rw [hb]
   exact hx.1
  ·exact hx.2
lemma d59 {g h:ℕ} (hAO:IsAO2 n C)
  (hT:TopForm G C) (hpair:junk G C = {g,h}) (hgh:g < h)
  (q04:readers n C g = {h}):
  ∃ p:ℕ,p < n + h∧ p ≠ n + g∧ (orIn n C p).Nonempty∧ 
   (∀ x:Fin n→ Bool,val C (List.ofFn x) p = true↔ ∃ u ∈ orIn n C p,x u = true)∧ 
   (∀ x:Fin n→ Bool,gateVal n C h x = true↔ 
    gateVal n C g x = true∧ val C (List.ofFn x) p = true):=by
 have hg:g ∈ junk G C:=by simp [hpair]
 have hh:h ∈ junk G C:=by simp [hpair]
 have hgr:h ∈ readers n C g:=by simp [q04]
 obtain ⟨b,hb⟩:=d2o hAO (d2q hh).1 (d4j hgr).2
 have hb':=hb.symm
 by_cases q2v:opnd C h (1 - b) = n + g
 ·refine ⟨opnd C g 0,?_,?_,d1m hAO hT hpair hgh 0,
   d1l hAO hT hpair hgh 0,?_⟩
  ·have:=d3k hAO (d2q hg).1 (0:Fin 2)
   omega
  ·exact ne_of_lt (d3k hAO (d2q hg).1 (0:Fin 2))
  ·intro x
   rw [d37 hAO hh b hb' x,q2v]
   constructor
   ·intro hx
    exact ⟨hx.1,(d0d hAO (d2q hg).1 (d2q hg).2.1 x).mp hx.1 0⟩
   ·intro hx
    exact ⟨hx.1,hx.1⟩
 ·have q12:=d5c hAO hT hpair q04 (1 - b) q2v
  have q2w:(orIn n C (opnd C h (1 - b))).Nonempty:=by
   obtain ⟨q06,q0j,x,hx,_⟩:=d2q hh
   obtain ⟨u,hu,_⟩:=(q12 x).mp ((d0d hAO q06 q0j x).mp hx (1 - b))
   exact ⟨u,hu⟩
  exact ⟨opnd C h (1 - b),d3k hAO (d2q hh).1 (1 - b),q2v,q2w,
   q12,d37 hAO hh b hb'⟩
lemma d5a {g h m:ℕ} (hAO:IsAO2 n C)
  (hT:TopForm G C) (hpair:junk G C = {g,h}) (hgh:g < h) (hhm:h < m)
  (q04:readers n C g = {h}) (q09:orN G C \ lam G C = {m})
  (s:Fin n→ Bool) (hs:∀ u v,G.Adj u v→ s u ≠ s v):
  ∃ (w:Fin 3→ ℕ) (t:Fin 3→ Bool),
   (∀ i,w i < n + h∧ w i ≠ n + g∧ (orIn n C (w i)).Nonempty)∧ 
   (∀ i (x:Fin n→ Bool),val C (List.ofFn x) (w i) = true↔ 
    ∃ u ∈ orIn n C (w i),x u = true)∧ 
   (∀ i,∀ u ∈ orIn n C (w i),s u = t i)∧ 
   (∀ x:Fin n→ Bool,gateVal n C h x = true↔ 
    ∀ i,∃ u ∈ orIn n C (w i),x u = true):=by
 classical
 have hg:g ∈ junk G C:=by simp [hpair]
 obtain ⟨p,q2x,q2y,q2w,q12,q3r⟩:=d59 hAO hT hpair hgh q04
 let w:Fin 3→ ℕ:=![opnd C g 0,opnd C g 1,p]
 have q0h:∀ i,w i < n + h∧ w i ≠ n + g∧ (orIn n C (w i)).Nonempty:=by
  intro i
  fin_cases i
  ·have:=d3k hAO (d2q hg).1 (0:Fin 2)
   exact ⟨by dsimp [w];omega,ne_of_lt this,d1m hAO hT hpair hgh 0⟩
  ·have:=d3k hAO (d2q hg).1 (1:Fin 2)
   exact ⟨by dsimp [w];omega,ne_of_lt this,d1m hAO hT hpair hgh 1⟩
  ·exact ⟨q2x,q2y,q2w⟩
 have q07:∀ i (x:Fin n→ Bool),val C (List.ofFn x) (w i) = true↔ 
   ∃ u ∈ orIn n C (w i),x u = true:=by
  intro i x
  fin_cases i
  ·exact d1l hAO hT hpair hgh 0 x
  ·exact d1l hAO hT hpair hgh 1 x
  ·exact q12 x
 have q3s:∀ i,∃ t:Bool,∀ u ∈ orIn n C (w i),s u = t:=by
  intro i
  exact d4c hAO q09 s hs (w i) (by have:=(q0h i).1;omega) (q0h i).2.2
 choose t ht using q3s
 refine ⟨w,t,q0h,q07,ht,?_⟩
 intro x
 rw [q3r x,d0c hAO (d2q hg).1 (d2q hg).2.1 x]
 constructor
 ·rintro ⟨⟨h0,h1⟩,hp⟩ i
  fin_cases i
  ·exact (q07 0 x).mp h0
  ·exact (q07 1 x).mp h1
  ·exact (q07 2 x).mp hp
 ·intro hx
  exact ⟨⟨(q07 0 x).mpr (hx 0),(q07 1 x).mpr (hx 1)⟩,
   (q07 2 x).mpr (hx 2)⟩
end TightSupport.Factor
namespace TightSupport.TightAssembly
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
 PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm
 PEqualNP.Outside.L_meta_5012.TightSupport PEqualNP.Outside.L_meta_5012.TightSupport.Budget
lemma d10 {n k:ℕ} (G:SimpleGraph (Fin n))
  [DecidableRel G.Adj] (C:Circuit) (s:Fin n→ Bool)
  (hbip:∀ u v,G.Adj u v→ s u ≠ s v) (h4:NoFourCycle G)
  (hL:IsLeastAO G C) (hT:TopForm G C) (g h m:ℕ)
  (hpair:junk G C = {g,h})
  (hreadg:readers n C g = {h}) (hreadh:readers n C h = {m})
  (hE:centreless G C = ∅) (hM:orN G C \ lam G C = {m})
  (S:Fin k→ Finset (Fin n)) (t:Fin k→ Bool) (w:Fin k→ ℕ)
  (hw:∀ i,w i < n + h∧ w i ≠ n + g)
  (q2z:∀ i x,wireVal n C (w i) x = d4z (S i) x)
  (hmono:∀ i,∀ a ∈ S i,s a = t i)
  (q0l:∀ x,gateVal n C h x = d0o S x):False:=by
 classical
 have hg:g ∈ junk G C:=by rw [hpair];simp
 have hh:h ∈ junk G C:=by rw [hpair];simp
 have q24:h ∈ readers n C g:=by rw [hreadg];simp
 have q25:m ∈ readers n C h:=by rw [hreadh];simp
 have hgh:=d4k hL.1 q24
 have hhm:=d4k hL.1 q25
 have hhN:=(d2q hh).1
 have q26:(orIn n C (n + m)).Nonempty:=by
  have hm:m ∈ orN G C \ lam G C:=by rw [hM];simp
  have hmd:m < C.gates.length∧ (gateAt C m).op = GateOp.or∧ ¬ BelowF G C m:=by
   simpa only [orN,gatesWhere,Finset.mem_filter,Finset.mem_range] using
    (Finset.mem_sdiff.mp hm).1
  by_contra hn
  have hz:=Finset.not_nonempty_iff_eq_empty.mp hn
  obtain ⟨j,hj⟩:=d2v hL hmd.1 hmd.2.2
  have hmj:=d4k hL.1 hj
  rcases d0m hL.1 hE hmd.2.2 hz hj with q0i | hjM
  ·rw [hpair,Finset.mem_insert,Finset.mem_singleton] at q0i
   rcases q0i with rfl | rfl <;> omega
  ·rw [hM,Finset.mem_singleton] at hjM
   omega
 obtain ⟨r,hr⟩:=q26
 let E:Finset (Fin n × Fin n):=Finset.univ.filter fun p=>
  G.Adj p.1 p.2∧ circuitFun n (CutTrace.off C h) (pairInput p.1 p.2) = false
 have hEn:E.Nonempty:=by
  obtain ⟨u,v,huv,_,q0p⟩:=CriticalEdge.d2y G C hL h hhN
  refine ⟨(u,v),Finset.mem_filter.mpr ⟨Finset.mem_univ _,huv,?_⟩⟩
  exact q0p
 have q0q:∀ p ∈ E,G.Adj p.1 p.2:=fun p hp=>(Finset.mem_filter.mp hp).2.1
 have q0p:∀ p ∈ E,Context.d26 C h (pairInput p.1 p.2) false = false:=
  fun p hp=>(Finset.mem_filter.mp hp).2.2
 have q0u:∀ u v,G.Adj u v→ Context.d26 C h (pairInput u v) false = false→ 
   (u,v) ∈ E:=by
  intro u v huv hz
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,huv,hz⟩
 have hF:∀ x,Context.d26 C h x (d0o S x) = graphFun G ∅ x:=by
  intro x
  rw [← q0l x,Context.d28 hhN]
  exact congrFun hL.2.1 x
 have q0g:∀ p ∈ E,∃ R T:Finset (Fin n),r ∈ R∧ 
   (∀ x,((d4z R x || d0o S x) && d4z T x) = true→ graphFun G ∅ x = true)∧ 
   d4z R (pairInput p.1 p.2) = false∧ d4z T (pairInput p.1 p.2) = true:=by
  intro p hp
  obtain ⟨R,T,hR,q01,hno,q3t⟩:=TightCut.d11 G C hL.1 hL.2.1
   hT g h m hpair hreadg hreadh hE r hr p.1 p.2 (q0q p hp) (q0p p hp)
  refine ⟨R,T,hR,?_,hno,q3t⟩
  intro x hx
  apply q01 x
  simpa only [d4z,q0l] using hx
 obtain ⟨v,i,_,heq⟩:=d0t G s hbip h4 S t hmono
  (Context.d26 C h) (Context.d27 hL.1 hhN) hF E hEn q0q q0p q0u r q0g
 let q:Gate:=⟨GateOp.and,[v.val,w i]⟩
 apply SerialReplacement.d56 G C hL g h hg hreadg q
  (Or.inl rfl) rfl
 ·intro z hz
  change z ∈ [v.val,w i] at hz
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
  rcases hz with rfl | rfl
  ·have:=v.isLt;omega
  ·exact (hw i).1
 ·change n + g ∉ [v.val,w i]
  simp only [List.mem_cons,List.not_mem_nil,or_false,not_or]
  exact ⟨by have:=v.isLt;omega,Ne.symm (hw i).2⟩
 ·funext x
  have hc:=congrFun heq x
  rw [← q2z i x] at hc
  have hs:=Context.d2b hhN v (w i) (hw i).1 x
  exact hs.symm.trans hc
end TightSupport.TightAssembly
namespace TightSupport.TightAssembly
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
 PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm
 PEqualNP.Outside.L_meta_5012.TightSupport PEqualNP.Outside.L_meta_5012.TightSupport.Budget
lemma tight_nested_impossible {n:ℕ} (G:SimpleGraph (Fin n))
  [DecidableRel G.Adj] (C:Circuit) (s:Fin n→ Bool)
  (hbip:∀ u v,G.Adj u v→ s u ≠ s v) (h4:NoFourCycle G)
  (hL:IsLeastAO G C) (hT:TopForm G C) (g h m:ℕ)
  (hpair:junk G C = {g,h})
  (hreadg:readers n C g = {h}) (hreadh:readers n C h = {m})
  (hE:centreless G C = ∅) (hM:orN G C \ lam G C = {m}):False:=by
 have hgm:h ∈ readers n C g:=by rw [hreadg];simp
 have hhm:m ∈ readers n C h:=by rw [hreadh];simp
 obtain ⟨w,t,hw,heval,hmono,hprod⟩:=Factor.d5a hL.1 hT hpair
  (d4k hL.1 hgm) (d4k hL.1 hhm) hreadg hM s hbip
 apply d10 G C s hbip h4 hL hT g h m hpair hreadg hreadh hE hM
  (fun i=>orIn n C (w i)) t w (fun i=>⟨(hw i).1,(hw i).2.1⟩)
 ·intro i x
  apply Bool.eq_iff_iff.mpr
  simpa only [d4z,decide_eq_true_eq,Budget.val,CleanedNonEdge.wireVal] using heval i x
 ·exact hmono
 ·intro x
  apply Bool.eq_iff_iff.mpr
  simpa only [d0o,d4z,decide_eq_true_eq] using hprod x
lemma two_junk_resource_bound {n:ℕ} (G:SimpleGraph (Fin n))
  [DecidableRel G.Adj] (C:Circuit) (s:Fin n→ Bool)
  (hbip:∀ u v,G.Adj u v→ s u ≠ s v) (h4:NoFourCycle G)
  (hL:IsLeastAO G C) (hT:TopForm G C) (hj:(junk G C).card = 2):
  2 ≤ 2 * (centreless G C).card + (orN G C \ lam G C).card:=by
 rcases d1h hL hT hj with hbound | ⟨g,h,m,hpair,_,hE,hreadg,hreadh,hM,_⟩
 ·exact hbound
 ·exact (tight_nested_impossible G C s hbip h4 hL hT g h m hpair hreadg hreadh hE hM).elim
end TightSupport.TightAssembly

namespace BoundaryGeometry

lemma safe_or_one_overlap {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (h4 : PEqualNP.TopForm.NoFourCycle G)
    (I T : Finset (Fin n)) (w v : Fin n)
    (hI : ∀ x ∈ I, G.Adj x w) (hT : ∀ x ∈ T, G.Adj x v) :
    (∀ x ∈ T, G.Adj x w) ∨ (T ∩ I).card ≤ 1 := by
  classical
  by_cases hwv : w = v
  · subst v
    exact Or.inl hT
  · right
    have hs : T ∩ I ⊆ Finset.univ.filter (fun x => G.Adj w x ∧ G.Adj v x) := by
      intro x hx
      obtain ⟨hxT, hxI⟩ := Finset.mem_inter.mp hx
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ x, (hI x hxI).symm, (hT x hxT).symm⟩
    exact (Finset.card_le_card hs).trans (h4 w v hwv)

lemma safe_boundary_replacement {n : ℕ} (G : SimpleGraph (Fin n))
    (I T : Finset (Fin n)) (w : Fin n)
    (hI : ∀ x ∈ I, G.Adj x w)
    (hT : (∀ x ∈ T, G.Adj x w) ∨ (T ∩ I).card ≤ 1) :
    ∃ P : Finset (Fin n), P ⊆ T ∧ T ∩ I ⊆ P ∧
      (∀ x ∈ P, G.Adj x w) ∧ (P = T ∨ P.card ≤ 1) := by
  classical
  rcases hT with hT | hT
  · exact ⟨T, Finset.Subset.refl T, Finset.inter_subset_left,
      hT, Or.inl rfl⟩
  · refine ⟨T ∩ I, Finset.inter_subset_left, Finset.Subset.refl _, ?_, Or.inr hT⟩
    intro x hx
    exact hI x (Finset.mem_inter.mp hx).2

lemma clean_raw_boundary {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (h4 : PEqualNP.TopForm.NoFourCycle G)
    (I T V : Finset (Fin n)) (w : Fin n) (hV : V.Nonempty)
    (hI : ∀ x ∈ I, G.Adj x w)
    (hclean : ∀ x : Fin n → Bool,
      (∃ t ∈ T, x t = true) → (∃ v ∈ V, x v = true) →
      PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ x = true) :
    (∀ x ∈ T, G.Adj x w) ∨ (T ∩ I).card ≤ 1 := by
  classical
  obtain ⟨v, hv⟩ := hV
  apply safe_or_one_overlap G h4 I T w v hI
  intro t ht
  let x : Fin n → Bool := fun a => decide (a = t ∨ a = v)
  have hx := hclean x ⟨t, ht, by simp [x]⟩ ⟨v, hv, by simp [x]⟩
  have he : ∃ a b, G.Adj a b ∧ (a = t ∨ a = v) ∧ (b = t ∨ b = v) := by
    simpa [PEqualNP.MetaComplexity.NestedCover.graphFun, x] using hx
  obtain ⟨a, b, hab, ha, hb⟩ := he
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
  · simp at hab
  · exact hab
  · exact hab.symm
  · simp at hab

end BoundaryGeometry

end PEqualNP.Outside.L_meta_5012
