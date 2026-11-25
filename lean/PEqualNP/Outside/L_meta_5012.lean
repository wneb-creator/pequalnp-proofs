import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_5012.Lift

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

end PEqualNP.Outside.L_meta_5012.Lift

namespace PEqualNP.Outside.L_meta_5012

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

end PEqualNP.Outside.L_meta_5012
