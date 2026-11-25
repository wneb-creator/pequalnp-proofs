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

namespace Patch

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm PEqualNP.Core PEqualNP.ReadTwo
open Lift

def patch (C : Circuit) (j : ℕ) (g : Gate) : Circuit := ⟨C.gates.set j g, C.output⟩

lemma patch_length (C : Circuit) (j : ℕ) (g : Gate) :
    (patch C j g).gates.length = C.gates.length := by
  simp [patch]

lemma gateAt_patch_ne (C : Circuit) (j k : ℕ) (g : Gate) (hne : j ≠ k) :
    gateAt (patch C j g) k = gateAt C k := by
  simp [patch, gateAt, List.getD_eq_getElem?_getD, List.getElem?_set_ne hne]

lemma gateAt_patch_eq {C : Circuit} {j : ℕ} (hj : j < C.gates.length) (g : Gate) :
    gateAt (patch C j g) j = g := by
  simp [patch, gateAt, List.getD_eq_getElem?_getD, hj]

lemma patch_isAO2 {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) (j : ℕ) (g : Gate)
    (hOp : g.op = GateOp.and ∨ g.op = GateOp.or) (hLen : g.inputs.length = 2)
    (hBack : ∀ w ∈ g.inputs, w < n + j) : IsAO2 n (patch C j g) := by
  refine ⟨?_, ?_, ?_⟩
  · intro k hk
    change k ∈ C.gates.set j g at hk
    rcases List.mem_or_eq_of_mem_set hk with hk | rfl
    · exact hAO.1 k hk
    · exact hOp
  · intro k hk w hw
    have hkC : k < C.gates.length := by simpa only [patch_length] using hk
    by_cases hkj : k = j
    · subst k
      rw [gateAt_patch_eq hkC] at hw
      exact hBack w hw
    · rw [gateAt_patch_ne C j k g (Ne.symm hkj)] at hw
      exact hAO.2.1 k hkC w hw
  · intro k hk
    change k ∈ C.gates.set j g at hk
    rcases List.mem_or_eq_of_mem_set hk with hk | rfl
    · exact hAO.2.2 k hk
    · exact hLen

lemma patch_gateVal_eq_of_not_inCone {n : ℕ} {C : Circuit} {j : ℕ} {g : Gate}
    (hAO : IsAO2 n C) (hAO' : IsAO2 n (patch C j g)) (k : ℕ)
    (hne : j ≠ k) (hCone : ¬ InCone n C j k) (x : Fin n → Bool) :
    gateVal n (patch C j g) k x = gateVal n C k x := by
  induction k using Nat.strong_induction_on with
  | ind k ih =>
    by_cases hk : k < C.gates.length
    · have hk' : k < (patch C j g).gates.length := by simpa only [patch_length] using hk
      have hgate := gateAt_patch_ne C j k g hne
      have hopnd (b : Fin 2) : opnd (patch C j g) k b = opnd C k b := by
        unfold opnd
        rw [hgate]
      have hval (b : Fin 2) : wval (patch C j g) x (opnd C k b) =
          wval C x (opnd C k b) := by
        by_cases hw : opnd C k b < n
        · rw [wval_input _ _ _ hw, wval_input _ _ _ hw]
        · have hw' : n ≤ opnd C k b := by omega
          have hlt := opnd_lt hAO hk b
          have hsub_ne : j ≠ opnd C k b - n := by
            intro he
            apply hCone
            exact (inCone_iff hk).mpr ⟨opnd C k b, opnd_mem hAO hk b, hw', hlt, Or.inl he⟩
          have hsub_cone : ¬ InCone n C j (opnd C k b - n) := by
            intro he
            apply hCone
            exact (inCone_iff hk).mpr ⟨opnd C k b, opnd_mem hAO hk b, hw', hlt, Or.inr he⟩
          have hv := ih (opnd C k b - n) (by omega) hsub_ne hsub_cone
          rw [gateVal_eq_wval, gateVal_eq_wval, Nat.add_sub_of_le hw'] at hv
          exact hv
      rw [gateVal_eq_wval, gateVal_eq_wval, wval_gate_eval hAO' x hk',
        wval_gate_eval hAO x hk, hgate, hopnd 0, hopnd 1, hval 0, hval 1]
    · rw [gateVal_eq_wval, gateVal_eq_wval, wval_ge_len _ _ (by rw [patch_length]; omega),
        wval_ge_len _ _ (by omega)]

lemma patch_wireVal_eq_of_not_inCone {n : ℕ} {C : Circuit} {j : ℕ} {g : Gate}
    (hAO : IsAO2 n C) (hAO' : IsAO2 n (patch C j g)) (w : ℕ)
    (h : n ≤ w → j ≠ w - n ∧ ¬ InCone n C j (w - n)) (x : Fin n → Bool) :
    wval (patch C j g) x w = wval C x w := by
  by_cases hw : w < n
  · rw [wval_input _ _ _ hw, wval_input _ _ _ hw]
  · have hwn : n ≤ w := by omega
    have hv := patch_gateVal_eq_of_not_inCone hAO hAO' (w - n) (h hwn).1 (h hwn).2 x
    rw [gateVal_eq_wval, gateVal_eq_wval, Nat.add_sub_of_le hwn] at hv
    exact hv

lemma patch_size (C : Circuit) (j : ℕ) (g : Gate) : (patch C j g).size = C.size := by
  simp [Circuit.size, patch_length]

lemma patch_isLeastAO {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {C : Circuit} {j : ℕ} {g : Gate} (hL : IsLeastAO G C)
    (hAO' : IsAO2 n (patch C j g)) (hF' : circuitFun n (patch C j g) = graphFun G ∅) :
    IsLeastAO G (patch C j g) := by
  refine ⟨hAO', hF', ?_⟩
  intro D hD hDF
  rw [patch_size]
  exact hL.2.2 D hD hDF

lemma patch_junk_mem_iff_of_not_inCone {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {C : Circuit} {j : ℕ} {g : Gate} (hAO : IsAO2 n C) (hAO' : IsAO2 n (patch C j g))
    {k : ℕ} (hne : j ≠ k) (hCone : ¬ InCone n C j k) :
    k ∈ junk G (patch C j g) ↔ k ∈ junk G C := by
  change (k ∈ (Finset.range (patch C j g).gates.length).filter (fun i => IsDirtyAnd n G (patch C j g) i)) ↔
    k ∈ (Finset.range C.gates.length).filter (fun i => IsDirtyAnd n G C i)
  rw [Finset.mem_filter, Finset.mem_filter]
  simp only [Finset.mem_range, IsDirtyAnd, IsDirty, patch_length,
    gateAt_patch_ne C j k g hne, patch_gateVal_eq_of_not_inCone hAO hAO' k hne hCone]


lemma patch_cone_subset_of_raw_inputs {n : ℕ} {C : Circuit} {r : ℕ} {g : Gate}
    (hraw : ∀ w ∈ g.inputs, w < n) {i j : ℕ} :
    InCone n (patch C r g) i j → InCone n C i j := by
  induction j using Nat.strong_induction_on with
  | ind j ih =>
    intro hc
    have hj' := inCone_lt_len hc
    have hj : j < C.gates.length := by simpa only [patch_length] using hj'
    obtain ⟨w,hw,hnw,hwj,hsub⟩ := (inCone_iff hj').mp hc
    by_cases hjr : j = r
    · subst j
      rw [gateAt_patch_eq hj] at hw
      have := hraw w hw
      omega
    · rw [gateAt_patch_ne C r j g (Ne.symm hjr)] at hw
      apply (inCone_iff hj).mpr
      refine ⟨w,hw,hnw,hwj,?_⟩
      rcases hsub with he | hc'
      · exact Or.inl he
      · exact Or.inr (ih (w-n) (by omega) hc')

lemma topForm_of_cone_subset {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {C D : Circuit} (hlen : D.gates.length = C.gates.length)
    (hop : ∀ i < C.gates.length, (gateAt D i).op = (gateAt C i).op)
    (hcone : ∀ i j, InCone n D i j → InCone n C i j)
    (hjunk : junk G C ⊆ junk G D) (hT : TopForm G C) : TopForm G D := by
  intro i hi j hj hiand hib hjand hc
  have hiC : i < C.gates.length := by omega
  have hjC : j < C.gates.length := by omega
  have hiop : (gateAt C i).op = GateOp.and := (hop i hiC).symm.trans hiand
  have hjop : (gateAt C j).op = GateOp.and := (hop j hjC).symm.trans hjand
  have hibC : BelowF G C i := by
    intro x hx
    by_contra hf
    have hm : i ∈ junk G C := by
      exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hiC,hiop,hiC,x,hx,
        Bool.eq_false_iff.mpr hf⟩
    obtain ⟨_,_,_,y,hy,hyF⟩ := Finset.mem_filter.mp (hjunk hm)
    have := hib y hy
    rw [hyF] at this
    cases this
  exact hT i hiC j hjC hiop hibC hjop (hcone i j hc)

end Patch


namespace SoleReader

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm PEqualNP.Core PEqualNP.ReadTwo
open Lift

lemma foldl_orSets_len (n : ℕ) (gs : List Gate) (acc : List (List ℕ)) :
    (gs.foldl (orStep n) acc).length = acc.length + gs.length := by
  induction gs generalizing acc with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, ih, orStep, List.length_append, List.length_cons, List.length_nil]
    omega

lemma foldl_orSets_getD_lt (n : ℕ) (gs : List Gate) (acc : List (List ℕ)) (i : ℕ) (hi : i < acc.length) :
    (gs.foldl (orStep n) acc).getD i [] = acc.getD i [] := by
  induction gs generalizing acc with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hlt : i < (orStep n acc g).length := by
      simp only [orStep, List.length_append, List.length_singleton]; omega
    rw [ih _ hlt]
    simp only [orStep, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma orSets_length (n : ℕ) (C : Circuit) : (orSets n C).length = C.gates.length := by
  unfold orSets; rw [foldl_orSets_len]; simp

lemma foldl_orSets_getD_gate (n : ℕ) (gs : List Gate) (acc : List (List ℕ)) (j : ℕ) (hj : j < gs.length) :
    (gs.foldl (orStep n) acc).getD (acc.length + j) [] =
      (acc.length + j) :: (match gs[j].op with
        | GateOp.or =>
          (gs[j].inputs.filter (fun w => decide (n ≤ w ∧ w < n + (acc.length + j)))).flatMap
            (fun w => (gs.foldl (orStep n) acc).getD (w - n) [])
        | _ => []) := by
  induction gs generalizing acc j with
  | nil => cases hj
  | cons g gs ih =>
    cases j with
    | zero =>
      simp only [Nat.add_zero, List.foldl_cons, List.getElem_cons_zero]
      set acc' := orStep n acc g
      have hlen : acc.length < acc'.length := by
        simp only [acc', orStep, List.length_append, List.length_singleton]; omega
      rw [foldl_orSets_getD_lt n gs acc' acc.length hlen]
      have hlhs : acc'.getD acc.length [] =
          acc.length :: (match g.op with
            | GateOp.or =>
              (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + acc.length))).flatMap
                (fun w => acc.getD (w - n) [])
            | _ => []) := by
        simp only [acc', orStep, List.getD_eq_getElem?_getD, List.getElem?_append_right (le_refl _),
          Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]
        cases g.op <;> rfl
      rw [hlhs]
      congr 1
      cases g.op
      · rfl
      · apply List.flatMap_congr
        intro w hw
        simp only [List.mem_filter, decide_eq_true_eq] at hw
        have hwn : w - n < acc.length := by omega
        have hwn' : w - n < acc'.length := by omega
        rw [foldl_orSets_getD_lt n gs acc' (w - n) hwn']
        simp only [acc', orStep, List.getD_eq_getElem?_getD, List.getElem?_append_left hwn]
      · rfl
      · rfl
      · rfl
    | succ j' =>
      simp only [List.foldl_cons, List.getElem_cons_succ]
      set acc' := orStep n acc g
      have hlen' : acc'.length = acc.length + 1 := by
        simp only [acc', orStep, List.length_append, List.length_singleton]
      have hj' : j' < gs.length := by simp only [List.length_cons] at hj; omega
      have hidx : acc.length + (j' + 1) = acc'.length + j' := by omega
      rw [hidx]
      exact ih acc' j' hj'

lemma orReaches_lt_len {n : ℕ} {C : Circuit} {w g : ℕ} (h : OrReaches n C w g) :
    w - n < C.gates.length := by
  by_contra hge
  unfold OrReaches at h
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by rw [orSets_length]; omega)] at h
  simp at h

lemma orReaches_gate_iff {n : ℕ} {C : Circuit} {j g : ℕ} (hj : j < C.gates.length) :
    OrReaches n C (n + j) g ↔
      g = j ∨ ((gateAt C j).op = GateOp.or ∧
        ∃ w ∈ (gateAt C j).inputs, n ≤ w ∧ w < n + j ∧ OrReaches n C w g) := by
  unfold OrReaches orSets
  have h := foldl_orSets_getD_gate n C.gates [] j hj
  simp only [List.length_nil, Nat.zero_add] at h
  rw [Nat.add_sub_cancel_left, h, ← gateAt_eq hj]
  constructor
  · rintro ⟨_, hmem⟩
    rw [List.mem_cons] at hmem
    rcases hmem with rfl | hmem
    · exact Or.inl rfl
    · cases hop : (gateAt C j).op
      · rw [hop] at hmem; simp at hmem
      · rw [hop] at hmem
        rw [List.mem_flatMap] at hmem
        rcases hmem with ⟨w, hw, hwg⟩
        rw [List.mem_filter] at hw
        simp only [decide_eq_true_eq] at hw
        exact Or.inr ⟨rfl, w, hw.1, hw.2.1, hw.2.2, ⟨hw.2.1, hwg⟩⟩
      · rw [hop] at hmem; simp at hmem
      · rw [hop] at hmem; simp at hmem
      · rw [hop] at hmem; simp at hmem
  · rintro (rfl | ⟨hop, w, hw, hnw, hwnj, hwg⟩)
    · exact ⟨Nat.le_add_right n _, List.mem_cons_self⟩
    · refine ⟨Nat.le_add_right n j, List.mem_cons_of_mem j ?_⟩
      rw [hop, List.mem_flatMap]
      exact ⟨w, List.mem_filter.mpr ⟨hw, by simp [hnw, hwnj]⟩, hwg.2⟩

lemma orReaches_input_false {n : ℕ} {C : Circuit} {w g : ℕ} (hw : w < n) : ¬ OrReaches n C w g :=
  fun h => by have := h.1; omega

lemma orReaches_le {n : ℕ} {C : Circuit} {w g : ℕ} (h : OrReaches n C w g) : g ≤ w - n := by
  have hnw : n ≤ w := h.1
  have hj : w - n < C.gates.length := orReaches_lt_len h
  obtain ⟨k, hk⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
  subst hk
  rw [Nat.add_sub_cancel_left] at hj ⊢
  clear hnw
  induction k using Nat.strong_induction_on with
  | ind k ih =>
    rw [orReaches_gate_iff hj] at h
    rcases h with rfl | ⟨_, u, _, hnu, hunk, hug⟩
    · exact le_refl _
    · have hlt : u - n < k := by omega
      have hu_eq : u = n + (u - n) := by omega
      rw [hu_eq] at hug
      have := ih (u - n) hlt hug (by omega)
      omega

lemma orReaches_self {n : ℕ} {C : Circuit} {j : ℕ} (hj : j < C.gates.length) :
    OrReaches n C (n + j) j :=
  (orReaches_gate_iff hj).mpr (Or.inl rfl)

lemma orReaches_trans {n : ℕ} {C : Circuit} {w j g : ℕ}
    (h1 : OrReaches n C w j) (h2 : OrReaches n C (n + j) g) : OrReaches n C w g := by
  have hnw : n ≤ w := h1.1
  have hwn : w - n < C.gates.length := orReaches_lt_len h1
  obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
  rw [Nat.add_sub_cancel_left] at hwn
  clear hnw
  induction k using Nat.strong_induction_on with
  | ind k ih =>
    rw [orReaches_gate_iff hwn] at h1
    rcases h1 with rfl | ⟨hop, u, hu, hnu, hunk, huj⟩
    · exact h2
    · rw [orReaches_gate_iff hwn]
      refine Or.inr ⟨hop, u, hu, hnu, hunk, ?_⟩
      have hu_eq : u = n + (u - n) := by omega
      rw [hu_eq] at huj ⊢
      exact ih (u - n) (by omega) huj (by omega)

lemma orReaches_inCone_or_eq {n : ℕ} {C : Circuit} {j g : ℕ} (h : OrReaches n C (n + j) g) :
    g = j ∨ InCone n C g j := by
  have hj := orReaches_lt_len h
  rw [Nat.add_sub_cancel_left] at hj
  induction j using Nat.strong_induction_on with
  | ind j ih =>
    rw [orReaches_gate_iff hj] at h
    rcases h with rfl | ⟨_, u, hu, hnu, hunj, hug⟩
    · exact Or.inl rfl
    · right
      rw [inCone_iff hj]
      refine ⟨u, hu, hnu, hunj, ?_⟩
      have hu_eq : u = n + (u - n) := by omega
      rw [hu_eq] at hug
      exact ih (u - n) (by omega) hug (by omega)

lemma exists_reader_of_inCone {n : ℕ} {C : Circuit} {k j : ℕ} (h : InCone n C k j) :
    ∃ m < C.gates.length, n + k ∈ (gateAt C m).inputs := by
  induction j using Nat.strong_induction_on with
  | ind j ih =>
    have hj := inCone_lt_len h
    rw [inCone_iff hj] at h
    rcases h with ⟨w, hw, hnw, hwnj, rfl | hsub⟩
    · exact ⟨j, hj, by rwa [show n + (w - n) = w by omega]⟩
    · exact ih (w - n) (by omega) hsub

lemma input_eq_opnd {n : ℕ} {C : Circuit} (hAO : IsAO2 n C)
    {a w : ℕ} (ha : a < C.gates.length) (hw : w ∈ (gateAt C a).inputs) :
    ∃ b : Fin 2, opnd C a b = w := by
  rw [gate_inputs_eq hAO ha] at hw
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with hw | hw
  · exact ⟨0, hw.symm⟩
  · exact ⟨1, hw.symm⟩

lemma orReaches_only_self_of_direct_boundary {n : ℕ} {C : Circuit}
    (hAO : IsAO2 n C) (hLive : ∀ k < C.gates.length, InOutputCone n C k)
    {r : ℕ} (hr : r < C.gates.length) (hOut : ¬ OrReaches n C C.output r)
    (hBoundary : ∀ a < C.gates.length, (gateAt C a).op = GateOp.and →
      ∀ b : Fin 2, OrReaches n C (opnd C a b) r → opnd C a b = n + r)
    {k : ℕ} (hk : OrReaches n C (n + k) r) : k = r := by
  let S := (Finset.range C.gates.length).filter fun a => OrReaches n C (n + a) r
  have hrS : r ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hr, orReaches_self hr⟩
  have hS : S.Nonempty := ⟨r, hrS⟩
  let m := S.max' hS
  have hmS : m ∈ S := Finset.max'_mem S hS
  obtain ⟨hml, hmr⟩ := Finset.mem_filter.mp hmS
  have hm : m < C.gates.length := Finset.mem_range.mp hml
  have hmr_le : r ≤ m := by simpa only [Nat.add_sub_cancel_left] using orReaches_le hmr
  have hLive_m := hLive m hm
  have hNoOut : C.output ≠ n + m := by
    intro he
    apply hOut
    rwa [he]
  obtain ⟨a, ha, hRead⟩ := exists_reader_of_inCone ((hLive_m.2.resolve_left hNoOut).2)
  have hma : m < a := by
    have := hAO.2.1 a ha (n + m) hRead
    omega
  have hMaxEq : m = r := by
    rcases hAO.1 _ (gateAt_mem ha) with hAnd | hOr
    · obtain ⟨b, hb⟩ := input_eq_opnd hAO ha hRead
      have hbr : OrReaches n C (opnd C a b) r := by rw [hb]; exact hmr
      have he := hBoundary a ha hAnd b hbr
      rw [hb] at he
      omega
    · have haR : OrReaches n C (n + a) r :=
        (orReaches_gate_iff ha).mpr (Or.inr ⟨hOr, n + m, hRead, by omega, by omega, hmr⟩)
      have haS : a ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ha, haR⟩
      have ham : a ≤ m := Finset.le_max' S a haS
      omega
  have hkl : k < C.gates.length := by simpa only [Nat.add_sub_cancel_left] using orReaches_lt_len hk
  have hkS : k ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hkl, hk⟩
  have hkm : k ≤ m := Finset.le_max' S k hkS
  have hrk : r ≤ k := by simpa only [Nat.add_sub_cancel_left] using orReaches_le hk
  omega

lemma readers_eq_singleton_of_direct_boundary {n : ℕ} {C : Circuit}
    (hAO : IsAO2 n C) (hLive : ∀ k < C.gates.length, InOutputCone n C k)
    {r g : ℕ} (hr : r < C.gates.length) (hg : g < C.gates.length)
    (hRead : n + r ∈ (gateAt C g).inputs) (hOut : ¬ OrReaches n C C.output r)
    (hBoundary : ∀ a < C.gates.length, (gateAt C a).op = GateOp.and →
      ∀ b : Fin 2, OrReaches n C (opnd C a b) r → a = g ∧ opnd C a b = n + r) :
    readers n C r = {g} := by
  apply Finset.ext
  intro k
  constructor
  · intro hk
    obtain ⟨hkl, hkr⟩ := Finset.mem_filter.mp hk
    have hkLen := Finset.mem_range.mp hkl
    apply Finset.mem_singleton.mpr
    rcases hAO.1 _ (gateAt_mem hkLen) with hAnd | hOr
    · obtain ⟨b, hb⟩ := input_eq_opnd hAO hkLen hkr
      have hbr : OrReaches n C (opnd C k b) r := by rw [hb]; exact orReaches_self hr
      exact (hBoundary k hkLen hAnd b hbr).1
    · have hrk : r < k := by have := hAO.2.1 k hkLen (n + r) hkr; omega
      have hkR : OrReaches n C (n + k) r :=
        (orReaches_gate_iff hkLen).mpr (Or.inr ⟨hOr, n + r, hkr, by omega, by omega, orReaches_self hr⟩)
      have he := orReaches_only_self_of_direct_boundary hAO hLive hr hOut
        (fun a ha hop b hb => (hBoundary a ha hop b hb).2) hkR
      omega
  · intro hk
    have he := Finset.mem_singleton.mp hk
    subst k
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hg, hRead⟩

lemma orReaches_val_mono {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) (x : Fin n → Bool)
    {w g : ℕ} (h : OrReaches n C w g) (hg : gateVal n C g x = true) : wval C x w = true := by
  have hnw : n ≤ w := h.1
  have hwn : w - n < C.gates.length := orReaches_lt_len h
  obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
  rw [Nat.add_sub_cancel_left] at hwn
  clear hnw
  induction k using Nat.strong_induction_on with
  | ind k ih =>
    rw [orReaches_gate_iff hwn] at h
    rcases h with rfl | ⟨hop, u, hu, hnu, hunk, hug⟩
    · exact hg
    · rw [wval_gate_or hAO x hwn hop, Bool.or_eq_true]
      rw [gate_inputs_eq hAO hwn] at hu
      have hu_eq : u = n + (u - n) := by omega
      rw [hu_eq] at hug
      have hvu := ih (u - n) (by omega) hug (by omega)
      rw [← hu_eq] at hvu
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
      rcases hu with rfl | rfl
      · exact Or.inl hvu
      · exact Or.inr hvu

lemma not_orReaches_output_of_not_belowF {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {C : Circuit} (hAO : IsAO2 n C) (hF : circuitFun n C = graphFun G ∅)
    {r : ℕ} (hr : ¬ BelowF G C r) : ¬ OrReaches n C C.output r := by
  intro hReach
  apply hr
  intro x hx
  have hout := orReaches_val_mono hAO x hReach hx
  change circuitFun n C x = true at hout
  rwa [hF] at hout


end SoleReader

namespace IndependentDescent

open PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership PEqualNP.TopForm

def product {n : ℕ} (P Q : Finset (Fin n)) (x : Fin n → Bool) : Bool :=
  decide (∃ p ∈ P, x p = true) && decide (∃ q ∈ Q, x q = true)

def Safe {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (P Q : Finset (Fin n)) (w : Fin n) : Prop :=
  ∀ x : Fin n → Bool, product P Q x = true → x w = true → graphFun G ∅ x = true

def leftCenters {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (P Q : Finset (Fin n)) : Finset (Fin n) :=
  P.filter fun p => ∀ q ∈ Q, G.Adj p q

def rightCenters {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (P Q : Finset (Fin n)) : Finset (Fin n) :=
  Q.filter fun q => ∀ p ∈ P, G.Adj p q

def Useful {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (P Q : Finset (Fin n)) (u v : Fin n) : Prop :=
  G.Adj u v ∧ product P Q (pairInput u v) = true ∧
    (Safe G P Q u ∨ Safe G P Q v)

lemma product_true {n : ℕ} (P Q : Finset (Fin n)) (x : Fin n → Bool) :
    product P Q x = true ↔ (∃ p ∈ P, x p = true) ∧ ∃ q ∈ Q, x q = true := by
  simp [product]

lemma wmax_iff {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : PEqualNP.CircuitLowerBounds.Circuit) (g : ℕ) (P Q : Finset (Fin n))
    (heval : ∀ x : Fin n → Bool, gateVal n C g x = product P Q x) (w : Fin n) :
    w ∈ wmax G C g ↔ Safe G P Q w := by
  simp only [wmax, Finset.mem_filter, Finset.mem_univ, true_and, Safe]
  simp_rw [heval]

lemma graph_pair {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (u v : Fin n) :
    graphFun G ∅ (pairInput u v) = true ↔ G.Adj u v := by
  simp only [graphFun, Finset.notMem_empty, false_and, exists_false, decide_false,
    Bool.false_or, decide_eq_true_eq, pairInput]
  constructor
  · rintro ⟨a, b, hab, ha, hb⟩
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · exact (G.irrefl hab).elim
    · exact hab
    · exact hab.symm
    · exact (G.irrefl hab).elim
  · intro h
    exact ⟨u, v, h, Or.inl rfl, Or.inr rfl⟩

lemma safe_left {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (P Q : Finset (Fin n)) {z : Fin n} (hz : z ∈ P) :
    Safe G P Q z ↔ ∀ q ∈ Q, G.Adj z q := by
  constructor
  · intro hs q hq
    apply (graph_pair G z q).mp
    apply hs
    · exact (product_true P Q _).mpr ⟨⟨z, hz, by simp [pairInput]⟩,
        q, hq, by simp [pairInput]⟩
    · simp [pairInput]
  · intro hadj x hp hxz
    obtain ⟨_, q, hq, hxq⟩ := (product_true P Q x).mp hp
    simp only [graphFun, Finset.notMem_empty, false_and, exists_false, decide_false,
      Bool.false_or, decide_eq_true_eq]
    exact ⟨z, q, hadj q hq, hxz, hxq⟩

lemma safe_right {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (P Q : Finset (Fin n)) {z : Fin n} (hz : z ∈ Q) :
    Safe G P Q z ↔ ∀ p ∈ P, G.Adj p z := by
  constructor
  · intro hs p hp
    apply (graph_pair G p z).mp
    apply hs
    · exact (product_true P Q _).mpr ⟨⟨p, hp, by simp [pairInput]⟩,
        z, hz, by simp [pairInput]⟩
    · simp [pairInput]
  · intro hadj x hp hxz
    obtain ⟨⟨p, hp, hxp⟩, _⟩ := (product_true P Q x).mp hp
    simp only [graphFun, Finset.notMem_empty, false_and, exists_false, decide_false,
      Bool.false_or, decide_eq_true_eq]
    exact ⟨p, z, hadj p hp, hxp, hxz⟩

lemma left_centers_card {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (P Q : Finset (Fin n)) (h4 : NoFourCycle G) (hQ : 2 ≤ Q.card) :
    (leftCenters G P Q).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro u hu v hv
  by_contra hne
  obtain ⟨_, huQ⟩ := Finset.mem_filter.mp hu
  obtain ⟨_, hvQ⟩ := Finset.mem_filter.mp hv
  have hsub : Q ⊆ Finset.univ.filter fun w => G.Adj u w ∧ G.Adj v w := by
    intro w hw
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, huQ w hw, hvQ w hw⟩
  have hc := (Finset.card_le_card hsub).trans (h4 u v hne)
  omega

lemma right_centers_card {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (P Q : Finset (Fin n)) (h4 : NoFourCycle G) (hP : 2 ≤ P.card) :
    (rightCenters G P Q).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro u hu v hv
  by_contra hne
  obtain ⟨_, huP⟩ := Finset.mem_filter.mp hu
  obtain ⟨_, hvP⟩ := Finset.mem_filter.mp hv
  have hsub : P ⊆ Finset.univ.filter fun w => G.Adj u w ∧ G.Adj v w := by
    intro w hw
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (huP w hw).symm, (hvP w hw).symm⟩
  have hc := (Finset.card_le_card hsub).trans (h4 u v hne)
  omega

lemma pair_cross {n : ℕ} (P Q : Finset (Fin n)) (hdis : Disjoint P Q)
    (u v : Fin n) (hprod : product P Q (pairInput u v) = true) :
    (u ∈ P ∧ v ∈ Q) ∨ (v ∈ P ∧ u ∈ Q) := by
  obtain ⟨⟨p, hp, hxp⟩, q, hq, hxq⟩ := (product_true P Q _).mp hprod
  simp only [pairInput, decide_eq_true_eq] at hxp hxq
  rcases hxp with rfl | rfl <;> rcases hxq with rfl | rfl
  · exact (Finset.disjoint_left.mp hdis hp hq).elim
  · exact Or.inl ⟨hp, hq⟩
  · exact Or.inr ⟨hp, hq⟩
  · exact (Finset.disjoint_left.mp hdis hp hq).elim

lemma useful_center {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (P Q : Finset (Fin n)) (hdis : Disjoint P Q) (u v : Fin n)
    (huv : Useful G P Q u v) :
    ∃ z, (z = u ∨ z = v) ∧
      (z ∈ leftCenters G P Q ∨ z ∈ rightCenters G P Q) := by
  obtain ⟨_, hp, hu | hv⟩ := huv
  · rcases pair_cross P Q hdis u v hp with ⟨hup, hvq⟩ | ⟨hvp, huq⟩
    · exact ⟨u, Or.inl rfl, Or.inl (Finset.mem_filter.mpr
        ⟨hup, (safe_left G P Q hup).mp hu⟩)⟩
    · exact ⟨u, Or.inl rfl, Or.inr (Finset.mem_filter.mpr
        ⟨huq, (safe_right G P Q huq).mp hu⟩)⟩
  · rcases pair_cross P Q hdis u v hp with ⟨hup, hvq⟩ | ⟨hvp, huq⟩
    · exact ⟨v, Or.inr rfl, Or.inr (Finset.mem_filter.mpr
        ⟨hvq, (safe_right G P Q hvq).mp hv⟩)⟩
    · exact ⟨v, Or.inr rfl, Or.inl (Finset.mem_filter.mpr
        ⟨hvp, (safe_left G P Q hvp).mp hv⟩)⟩

lemma decomposition {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (P Q : Finset (Fin n)) (h4 : NoFourCycle G) (hdis : Disjoint P Q)
    (hP : 2 ≤ P.card) (hQ : 2 ≤ Q.card) :
    (∃ z ∈ P, ∃ zp ∈ Q, G.Adj z zp ∧
      (∀ p ∈ P, G.Adj p zp) ∧ (∀ q ∈ Q, G.Adj z q)) ∨
    (∃ z ∈ P, (∀ q ∈ Q, G.Adj z q) ∧
      ∀ u v, Useful G P Q u v → pairInput u v z = true) ∨
    (∃ z ∈ Q, (∀ p ∈ P, G.Adj p z) ∧
      ∀ u v, Useful G P Q u v → pairInput u v z = true) ∨
    (∀ u v, ¬ Useful G P Q u v) := by
  classical
  by_cases hL : (leftCenters G P Q).Nonempty
  · obtain ⟨z, hz⟩ := hL
    obtain ⟨hzP, hzQ⟩ := Finset.mem_filter.mp hz
    by_cases hR : (rightCenters G P Q).Nonempty
    · obtain ⟨zp, hzp⟩ := hR
      obtain ⟨hzpQ, hzpP⟩ := Finset.mem_filter.mp hzp
      exact Or.inl ⟨z, hzP, zp, hzpQ, hzQ zp hzpQ, hzpP, hzQ⟩
    · refine Or.inr (Or.inl ⟨z, hzP, hzQ, ?_⟩)
      intro u v huv
      obtain ⟨w, hw, hwL | hwR⟩ := useful_center G P Q hdis u v huv
      · have heq : w = z := Finset.card_le_one.mp (left_centers_card G P Q h4 hQ) w hwL z hz
        subst w
        simpa [pairInput] using hw
      · exact (hR ⟨w, hwR⟩).elim
  · by_cases hR : (rightCenters G P Q).Nonempty
    · obtain ⟨z, hz⟩ := hR
      obtain ⟨hzQ, hzP⟩ := Finset.mem_filter.mp hz
      refine Or.inr (Or.inr (Or.inl ⟨z, hzQ, hzP, ?_⟩))
      intro u v huv
      obtain ⟨w, hw, hwL | hwR⟩ := useful_center G P Q hdis u v huv
      · exact (hL ⟨w, hwL⟩).elim
      · have heq : w = z := Finset.card_le_one.mp (right_centers_card G P Q h4 hP) w hwR z hz
        subst w
        simpa [pairInput] using hw
    · refine Or.inr (Or.inr (Or.inr ?_))
      intro u v huv
      obtain ⟨w, _, hwL | hwR⟩ := useful_center G P Q hdis u v huv
      · exact hL ⟨w, hwL⟩
      · exact hR ⟨w, hwR⟩

lemma clean_left {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (P Q : Finset (Fin n)) (z : Fin n) (hzP : z ∈ P)
    (hzQ : ∀ q ∈ Q, G.Adj z q) :
    (∀ x, product {z} Q x = true → product P Q x = true) ∧
    (∀ x, product {z} Q x = true → graphFun G ∅ x = true) ∧
    (∀ u v, product P Q (pairInput u v) = true → pairInput u v z = true →
      product {z} Q (pairInput u v) = true) := by
  have hf : ∀ x, product {z} Q x = true ↔ x z = true ∧ ∃ q ∈ Q, x q = true := by
    intro x
    simp [product_true]
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨hxz, hq⟩ := (hf x).mp hx
    exact (product_true P Q x).mpr ⟨⟨z, hzP, hxz⟩, hq⟩
  · intro x hx
    obtain ⟨hxz, q, hq, hxq⟩ := (hf x).mp hx
    simp only [graphFun, Finset.notMem_empty, false_and, exists_false, decide_false,
      Bool.false_or, decide_eq_true_eq]
    exact ⟨z, q, hzQ q hq, hxz, hxq⟩
  · intro u v hp hz
    exact (hf _).mpr ⟨hz, ((product_true P Q _).mp hp).2⟩

lemma clean_right {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (P Q : Finset (Fin n)) (z : Fin n) (hzQ : z ∈ Q)
    (hzP : ∀ p ∈ P, G.Adj p z) :
    (∀ x, product P {z} x = true → product P Q x = true) ∧
    (∀ x, product P {z} x = true → graphFun G ∅ x = true) ∧
    (∀ u v, product P Q (pairInput u v) = true → pairInput u v z = true →
      product P {z} (pairInput u v) = true) := by
  have hf : ∀ x, product P {z} x = true ↔ (∃ p ∈ P, x p = true) ∧ x z = true := by
    intro x
    simp [product_true]
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨hp, hxz⟩ := (hf x).mp hx
    exact (product_true P Q x).mpr ⟨hp, z, hzQ, hxz⟩
  · intro x hx
    obtain ⟨⟨p, hp, hxp⟩, hxz⟩ := (hf x).mp hx
    simp only [graphFun, Finset.notMem_empty, false_and, exists_false, decide_false,
      Bool.false_or, decide_eq_true_eq]
    exact ⟨p, z, hzP p hp, hxp, hxz⟩
  · intro u v hp hz
    exact (hf _).mpr ⟨((product_true P Q _).mp hp).1, hz⟩

lemma safe_outside {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (P Q : Finset (Fin n)) (hL : leftCenters G P Q = ∅)
    (hR : rightCenters G P Q = ∅) {w : Fin n} (hw : Safe G P Q w) :
    w ∉ P ∧ w ∉ Q := by
  constructor
  · intro hp
    have hm : w ∈ leftCenters G P Q :=
      Finset.mem_filter.mpr ⟨hp, (safe_left G P Q hp).mp hw⟩
    rw [hL] at hm
    exact Finset.notMem_empty w hm
  · intro hq
    have hm : w ∈ rightCenters G P Q :=
      Finset.mem_filter.mpr ⟨hq, (safe_right G P Q hq).mp hw⟩
    rw [hR] at hm
    exact Finset.notMem_empty w hm

lemma singleton_overlap_bypass {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (P Q : Finset (Fin n)) (z : Fin n) (hI : P ∩ Q = {z})
    (hL : leftCenters G P Q = ∅) (hR : rightCenters G P Q = ∅) :
    (∀ x : Fin n → Bool, x z = true → product P Q x = true) ∧
    (∀ u v, Useful G P Q u v → pairInput u v z = true) := by
  have hzI : z ∈ P ∩ Q := by rw [hI]; simp
  obtain ⟨hzP, hzQ⟩ := Finset.mem_inter.mp hzI
  refine ⟨?_, ?_⟩
  · intro x hx
    exact (product_true P Q x).mpr ⟨⟨z, hzP, hx⟩, z, hzQ, hx⟩
  · intro u v huv
    obtain ⟨_, hp, hu | hv⟩ := huv
    · obtain ⟨hup, huq⟩ := safe_outside G P Q hL hR hu
      obtain ⟨⟨p, hp, hpu⟩, q, hq, hqu⟩ := (product_true P Q _).mp hp
      simp only [pairInput, decide_eq_true_eq] at hpu hqu
      have hpv : p = v := hpu.resolve_left (fun heq => hup (heq ▸ hp))
      have hqv : q = v := hqu.resolve_left (fun heq => huq (heq ▸ hq))
      have hvI : v ∈ P ∩ Q := Finset.mem_inter.mpr ⟨hpv ▸ hp, hqv ▸ hq⟩
      rw [hI, Finset.mem_singleton] at hvI
      simp [pairInput, ← hvI]
    · obtain ⟨hvp, hvq⟩ := safe_outside G P Q hL hR hv
      obtain ⟨⟨p, hp, hpu⟩, q, hq, hqu⟩ := (product_true P Q _).mp hp
      simp only [pairInput, decide_eq_true_eq] at hpu hqu
      have hpu' : p = u := hpu.resolve_right (fun heq => hvp (heq ▸ hp))
      have hqu' : q = u := hqu.resolve_right (fun heq => hvq (heq ▸ hq))
      have huI : u ∈ P ∩ Q := Finset.mem_inter.mpr ⟨hpu' ▸ hp, hqu' ▸ hq⟩
      rw [hI, Finset.mem_singleton] at huI
      simp [pairInput, ← huI]

lemma bipartite_overlap_no_both_centers {n : ℕ}
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (s : Fin n → Bool) (hbip : ∀ u v, G.Adj u v → s u ≠ s v)
    (P Q : Finset (Fin n)) (hI : (P ∩ Q).Nonempty) :
    ¬ ((leftCenters G P Q).Nonempty ∧ (rightCenters G P Q).Nonempty) := by
  rintro ⟨⟨z, hz⟩, zp, hzp⟩
  obtain ⟨v, hv⟩ := hI
  obtain ⟨hzP, hzQ⟩ := Finset.mem_filter.mp hz
  obtain ⟨hzpQ, hzpP⟩ := Finset.mem_filter.mp hzp
  obtain ⟨hvP, hvQ⟩ := Finset.mem_inter.mp hv
  have hzzp := hbip z zp (hzQ zp hzpQ)
  have hzv := hbip z v (hzQ v hvQ)
  have hvzp := hbip v zp (hzpP v hvP)
  cases hs : s z <;> cases hsp : s zp <;> cases hsv : s v <;> simp_all

lemma safe_overlap_adjacent {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (P Q : Finset (Fin n)) {w v : Fin n} (hw : Safe G P Q w) (hv : v ∈ P ∩ Q) :
    G.Adj w v := by
  obtain ⟨hvP, hvQ⟩ := Finset.mem_inter.mp hv
  apply (graph_pair G w v).mp
  apply hw
  · exact (product_true P Q _).mpr ⟨⟨v, hvP, by simp [pairInput]⟩,
      v, hvQ, by simp [pairInput]⟩
  · simp [pairInput]

lemma safe_unique_of_large_overlap {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (P Q : Finset (Fin n)) (h4 : NoFourCycle G) (hI : 2 ≤ (P ∩ Q).card)
    {u v : Fin n} (hu : Safe G P Q u) (hv : Safe G P Q v) : u = v := by
  by_contra hne
  have hsub : P ∩ Q ⊆ Finset.univ.filter fun w => G.Adj u w ∧ G.Adj v w := by
    intro w hw
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      safe_overlap_adjacent G P Q hu hw, safe_overlap_adjacent G P Q hv hw⟩
  have hc := (Finset.card_le_card hsub).trans (h4 u v hne)
  omega

end IndependentDescent

namespace IndependentObstruction

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership
open PEqualNP.TopForm

abbrev G : SimpleGraph (Fin 4) := edgeGraph 4 [(0, 1), (2, 3)]

def C : Circuit :=
  { gates :=
      [ ⟨GateOp.or, [3, 0]⟩,
        ⟨GateOp.or, [3, 1]⟩,
        ⟨GateOp.and, [4, 5]⟩,
        ⟨GateOp.or, [0, 2]⟩,
        ⟨GateOp.and, [4, 7]⟩,
        ⟨GateOp.and, [2, 6]⟩,
        ⟨GateOp.and, [1, 8]⟩,
        ⟨GateOp.or, [9, 10]⟩ ],
    output := 11 }

def D : Circuit := { C with output := 9 }

def E : Circuit :=
  { gates := [⟨GateOp.and, [0, 1]⟩, ⟨GateOp.and, [2, 3]⟩,
      ⟨GateOp.or, [4, 5]⟩],
    output := 6 }

def color : Fin 4 → Bool := fun i => decide (i = 1 ∨ i = 3)

lemma bipartite : ∀ u v : Fin 4, G.Adj u v → color u ≠ color v := by
  decide

lemma no_four_cycle : NoFourCycle G := by
  decide

lemma ao2 : IsAO2 4 C := by
  decide

lemma computes : circuitFun 4 C = graphFun G ∅ := by
  funext x
  exact (show ∀ y : Fin 4 → Bool, circuitFun 4 C y = graphFun G ∅ y by decide) x

lemma top_form : TopForm G C := by
  decide

lemma junk_eq : junk G C = {2, 4} := by
  decide

lemma tops_eq : tops G C = {5, 6} := by
  decide

lemma independent : ¬ InCone 4 C 2 4 ∧ ¬ InCone 4 C 4 2 := by
  decide

lemma no_common_top : ∀ t ∈ tops G C, ¬ (InCone 4 C 2 t ∧ InCone 4 C 4 t) := by
  decide

lemma lower_output_formula : ∀ x : Fin 4 → Bool,
    circuitFun 4 D x = ((x 2 && x 3) || (x 0 && x 1 && x 2)) := by
  decide

def triple : Fin 4 → Bool := fun i => decide (i ≠ 3)

lemma lower_accepts_triple : circuitFun 4 D triple = true := by
  decide

lemma lower_rejects_subpairs : ∀ u v : Fin 4, triple u = true → triple v = true →
    circuitFun 4 D (pairInput u v) = false := by
  decide

lemma lower_not_graph : ∀ (H : SimpleGraph (Fin 4)) [DecidableRel H.Adj],
    circuitFun 4 D ≠ graphFun H ∅ := by
  intro H _ heq
  have htriple : graphFun H ∅ triple = true := by
    rw [← heq]
    exact lower_accepts_triple
  simp only [graphFun, Finset.notMem_empty, false_and, exists_false,
    decide_false, Bool.false_or, decide_eq_true_eq] at htriple
  obtain ⟨u, v, huv, hu, hv⟩ := htriple
  have hpair : graphFun H ∅ (pairInput u v) = true := by
    simp only [graphFun, Finset.notMem_empty, false_and, exists_false,
      decide_false, Bool.false_or, decide_eq_true_eq]
    exact ⟨u, v, huv, by simp [pairInput], by simp [pairInput]⟩
  rw [← heq, lower_rejects_subpairs u v hu hv] at hpair
  exact Bool.false_ne_true hpair

lemma cheaper_ao2 : IsAO2 4 E := by
  decide

lemma cheaper_computes : circuitFun 4 E = graphFun G ∅ := by
  funext x
  exact (show ∀ y : Fin 4 → Bool, circuitFun 4 E y = graphFun G ∅ y by decide) x

lemma not_least : ¬ IsLeastAO G C := by
  intro h
  have hs : C.size ≤ E.size := h.2.2 E cheaper_ao2 cheaper_computes
  exact (show ¬ C.size ≤ E.size by decide) hs

end IndependentObstruction

namespace Normalize

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm

def isAndOp : GateOp → Bool
  | GateOp.and => true
  | _ => false

lemma isAndOp_eq_true_iff (op : GateOp) : isAndOp op = true ↔ op = GateOp.and := by
  cases op <;> simp [isAndOp]

def andIndexSum (C : Circuit) : ℕ :=
  ∑ k ∈ (Finset.range C.gates.length).filter (fun k => isAndOp (gateAt C k).op = true), k

def wireStep (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma foldl_wireStep_length (gs : List Gate) (acc : List Bool) :
    (gs.foldl wireStep acc).length = acc.length + gs.length := by
  induction gs generalizing acc with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, ih, wireStep, List.length_append, List.length_cons, List.length_nil]
    omega

lemma foldl_wireStep_prefix (gs : List Gate) (acc : List Bool) (w : ℕ) (hw : w < acc.length) :
    (gs.foldl wireStep acc).getD w false = acc.getD w false := by
  induction gs generalizing acc with
  | nil => rfl
  | cons g gs ih =>
    have hw' : w < (wireStep acc g).length := by
      simp only [wireStep, List.length_append, List.length_singleton]
      omega
    rw [List.foldl_cons, ih (wireStep acc g) hw']
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD]
    simp only [wireStep, List.getElem?_append_left hw]

lemma wires_length (C : Circuit) (x : List Bool) :
    (C.wires x).length = x.length + C.gates.length := by
  exact foldl_wireStep_length C.gates x

lemma gateAt_eq_getElem (C : Circuit) (k : ℕ) (hk : k < C.gates.length) :
    gateAt C k = C.gates[k] := by
  unfold gateAt
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk]
  rfl

lemma wireVal_input (n : ℕ) (C : Circuit) (x : Fin n → Bool) (w : ℕ) (hw : w < n) :
    wireVal n C w x = x ⟨w, hw⟩ := by
  unfold wireVal Circuit.wires
  have hw' : w < (List.ofFn x).length := by simp [hw]
  have h1 := foldl_wireStep_prefix C.gates (List.ofFn x) w hw'
  change (C.gates.foldl wireStep (List.ofFn x)).getD w false = x ⟨w, hw⟩
  rw [h1, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hw']
  simp

lemma wireVal_gate (n : ℕ) (C : Circuit) (x : Fin n → Bool) (k : ℕ)
    (hk : k < C.gates.length) (hRB : ReadsBack n C) :
    wireVal n C (n + k) x =
      (gateAt C k).op.eval ((gateAt C k).inputs.map fun u => wireVal n C u x) := by
  have hsplit : C.gates = C.gates.take k ++ [C.gates[k]] ++ C.gates.drop (k + 1) := by
    have h1 := List.take_append_drop k C.gates
    have h2 : C.gates.drop k = C.gates[k] :: C.gates.drop (k + 1) := List.drop_eq_getElem_cons hk
    rw [h2] at h1
    simp only [List.append_assoc, List.singleton_append, h1]
  set acc := (C.gates.take k).foldl wireStep (List.ofFn x) with hacc
  have hacc_len : acc.length = n + k := by
    rw [hacc, foldl_wireStep_length, List.length_ofFn, List.length_take]
    omega
  have hpref : ∀ u < n + k, wireVal n C u x = acc.getD u false := by
    intro u hu
    unfold wireVal Circuit.wires
    change (C.gates.foldl wireStep (List.ofFn x)).getD u false = acc.getD u false
    conv_lhs => rw [← List.take_append_drop k C.gates]
    rw [List.foldl_append, ← hacc]
    exact foldl_wireStep_prefix (C.gates.drop k) acc u (by omega)
  have hval : wireVal n C (n + k) x =
      C.gates[k].op.eval (C.gates[k].inputs.map fun u => acc.getD u false) := by
    unfold wireVal Circuit.wires
    change (C.gates.foldl wireStep (List.ofFn x)).getD (n + k) false = _
    conv_lhs => rw [hsplit]
    rw [List.foldl_append, List.foldl_append, ← hacc, List.foldl_cons, List.foldl_nil]
    have hlen : n + k < (wireStep acc C.gates[k]).length := by
      simp only [wireStep, List.length_append, List.length_singleton]
      omega
    rw [foldl_wireStep_prefix (C.gates.drop (k + 1)) (wireStep acc C.gates[k]) (n + k) hlen]
    rw [List.getD_eq_getElem?_getD]
    simp only [wireStep, List.getElem?_append_right (by omega : acc.length ≤ n + k),
      hacc_len, Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]
  rw [hval, gateAt_eq_getElem C k hk]
  congr 1
  apply List.map_congr_left
  intro u hu
  rw [← gateAt_eq_getElem C k hk] at hu
  exact (hpref u (hRB k hk u hu)).symm

lemma wireVal_append_lt (n : ℕ) (C : Circuit) (g : Gate) (out : ℕ) (x : Fin n → Bool)
    (w : ℕ) (hw : w < n + C.gates.length) :
    wireVal n ⟨C.gates ++ [g], out⟩ w x = wireVal n C w x := by
  unfold wireVal Circuit.wires
  change ((C.gates ++ [g]).foldl wireStep (List.ofFn x)).getD w false =
    (C.gates.foldl wireStep (List.ofFn x)).getD w false
  rw [List.foldl_append]
  have hw' : w < (C.gates.foldl wireStep (List.ofFn x)).length := by
    rw [foldl_wireStep_length, List.length_ofFn]
    exact hw
  exact foldl_wireStep_prefix [g] (C.gates.foldl wireStep (List.ofFn x)) w hw'

lemma wireVal_append_last (n : ℕ) (C : Circuit) (g : Gate) (out : ℕ) (x : Fin n → Bool) :
    wireVal n ⟨C.gates ++ [g], out⟩ (n + C.gates.length) x =
      g.op.eval (g.inputs.map fun u => wireVal n C u x) := by
  unfold wireVal Circuit.wires
  change ((C.gates ++ [g]).foldl wireStep (List.ofFn x)).getD (n + C.gates.length) false = _
  rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
  set acc := C.gates.foldl wireStep (List.ofFn x) with hacc
  have hlen : acc.length = n + C.gates.length := by
    rw [hacc, foldl_wireStep_length, List.length_ofFn]
  rw [List.getD_eq_getElem?_getD]
  simp only [wireStep, List.getElem?_append_right (by omega : acc.length ≤ n + C.gates.length),
    hlen, Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]
  rfl

lemma output_lt_of_nonempty {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hE : G.edgeFinset.Nonempty) (hF : circuitFun n C = graphFun G ∅) :
    C.output < n + C.gates.length := by
  by_contra hge
  push Not at hge
  obtain ⟨e, he⟩ := hE
  induction e using Sym2.ind with
  | _ u v =>
    have hadj : G.Adj u v := SimpleGraph.mem_edgeFinset.mp he
    have htrue : graphFun G ∅ (fun _ => true) = true := by
      unfold graphFun
      rw [Bool.or_eq_true]
      right
      rw [decide_eq_true_eq]
      exact ⟨u, v, hadj, rfl, rfl⟩
    have hfalse : circuitFun n C (fun _ => true) = false := by
      unfold circuitFun Circuit.eval
      rw [List.getD_eq_getElem?_getD]
      have hlen : (C.wires (List.ofFn (fun _ : Fin n => true))).length = n + C.gates.length := by
        rw [wires_length, List.length_ofFn]
      rw [List.getElem?_eq_none (by omega)]
      rfl
    have hEq := congrFun hF (fun _ => true)
    rw [hfalse, htrue] at hEq
    cases hEq

lemma foldl_coneStep_length (n : ℕ) (gs : List Gate) (acc : List (List ℕ)) :
    (gs.foldl (coneStep n) acc).length = acc.length + gs.length := by
  induction gs generalizing acc with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, ih, coneStep, List.length_append, List.length_cons, List.length_nil]
    omega

lemma foldl_coneStep_prefix (n : ℕ) (gs : List Gate) (acc : List (List ℕ))
    (j : ℕ) (hj : j < acc.length) :
    (gs.foldl (coneStep n) acc).getD j [] = acc.getD j [] := by
  induction gs generalizing acc with
  | nil => rfl
  | cons g gs ih =>
    have hj' : j < (coneStep n acc g).length := by
      simp only [coneStep, List.length_append, List.length_singleton]
      omega
    rw [List.foldl_cons, ih (coneStep n acc g) hj']
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD]
    simp only [coneStep, List.getElem?_append_left hj]

lemma inCone_iff (n : ℕ) (C : Circuit) (i j : ℕ) (hj : j < C.gates.length) :
    InCone n C i j ↔
      ∃ w ∈ (gateAt C j).inputs, n ≤ w ∧ w < n + j ∧ (i = w - n ∨ InCone n C i (w - n)) := by
  have hsplit : C.gates = C.gates.take j ++ [C.gates[j]] ++ C.gates.drop (j + 1) := by
    have h1 := List.take_append_drop j C.gates
    have h2 : C.gates.drop j = C.gates[j] :: C.gates.drop (j + 1) := List.drop_eq_getElem_cons hj
    rw [h2] at h1
    simp only [List.append_assoc, List.singleton_append, h1]
  set acc := (C.gates.take j).foldl (coneStep n) [] with hacc
  have hacc_len : acc.length = j := by
    rw [hacc, foldl_coneStep_length, List.length_nil, List.length_take]
    omega
  have hpref : ∀ k < j, (cones n C).getD k [] = acc.getD k [] := by
    intro k hk
    unfold cones
    conv_lhs => rw [← List.take_append_drop j C.gates]
    rw [List.foldl_append, ← hacc]
    exact foldl_coneStep_prefix n (C.gates.drop j) acc k (by omega)
  have hstep : (cones n C).getD j [] =
      ((gateAt C j).inputs.filter (fun w => decide (n ≤ w ∧ w < n + j))).flatMap
        (fun w => (w - n) :: acc.getD (w - n) []) := by
    unfold cones
    conv_lhs => rw [hsplit]
    rw [List.foldl_append, List.foldl_append, ← hacc, List.foldl_cons, List.foldl_nil]
    have hlen : j < (coneStep n acc C.gates[j]).length := by
      simp only [coneStep, List.length_append, List.length_singleton]
      omega
    rw [foldl_coneStep_prefix n (C.gates.drop (j + 1)) (coneStep n acc C.gates[j]) j hlen]
    rw [List.getD_eq_getElem?_getD]
    simp only [coneStep, List.getElem?_append_right (by omega : acc.length ≤ j),
      hacc_len, Nat.sub_self, List.getElem?_cons_zero, Option.getD_some,
      gateAt_eq_getElem C j hj]
  unfold InCone
  rw [hstep, List.mem_flatMap]
  constructor
  · rintro ⟨w, hw, hi⟩
    rw [List.mem_filter] at hw
    have hbounds : n ≤ w ∧ w < n + j := by simpa using hw.2
    rw [List.mem_cons] at hi
    refine ⟨w, hw.1, hbounds.1, hbounds.2, ?_⟩
    rcases hi with rfl | hi
    · exact Or.inl rfl
    · right
      rw [hpref (w - n) (by omega)]
      exact hi
  · rintro ⟨w, hw, hnw, hlt, hi⟩
    refine ⟨w, ?_, ?_⟩
    · rw [List.mem_filter]
      exact ⟨hw, by simpa using And.intro hnw hlt⟩
    · rw [List.mem_cons]
      rcases hi with rfl | hi
      · exact Or.inl rfl
      · right
        rw [← hpref (w - n) (by omega)]
        exact hi

lemma exists_direct_reader (n : ℕ) (C : Circuit) (i j : ℕ)
    (hj : j < C.gates.length) (h : InCone n C i j) :
    ∃ g, i < g ∧ g ≤ j ∧ g < C.gates.length ∧ n + i ∈ (gateAt C g).inputs := by
  induction j using Nat.strong_induction_on with
  | ind j ih =>
    rw [inCone_iff n C i j hj] at h
    obtain ⟨w, hw, hnw, hlt, hcase⟩ := h
    rcases hcase with rfl | hcone
    · refine ⟨j, by omega, le_refl j, hj, ?_⟩
      have heq : n + (w - n) = w := by omega
      rw [heq]
      exact hw
    · have hklt : w - n < j := by omega
      obtain ⟨g, hig, hgk, hglen, hmem⟩ := ih (w - n) hklt (by omega) hcone
      exact ⟨g, hig, by omega, hglen, hmem⟩

def remap (n g r w : ℕ) : ℕ :=
  if w < n + g then w
  else if w = n + g then r
  else w - 1

def origWire (n g w : ℕ) : ℕ :=
  if w < n + g then w else w + 1

def mapGate (f : ℕ → ℕ) (gt : Gate) : Gate :=
  ⟨gt.op, gt.inputs.map f⟩

def delGate (n g r : ℕ) (C : Circuit) : Circuit :=
  ⟨(C.gates.eraseIdx g).map (mapGate (remap n g r)), remap n g r C.output⟩

lemma delGate_length (n g r : ℕ) (C : Circuit) (hg : g < C.gates.length) :
    (delGate n g r C).gates.length = C.gates.length - 1 := by
  simp [delGate, List.length_eraseIdx_of_lt hg]

lemma delGate_gateAt (n g r : ℕ) (C : Circuit) (hg : g < C.gates.length)
    (k : ℕ) (hk : k < C.gates.length - 1) :
    gateAt (delGate n g r C) k =
      mapGate (remap n g r) (gateAt C (if k < g then k else k + 1)) := by
  have hk' : k < (delGate n g r C).gates.length := by
    rw [delGate_length n g r C hg]; exact hk
  rw [gateAt_eq_getElem (delGate n g r C) k hk']
  have hk_e : k < (C.gates.eraseIdx g).length := by
    rw [List.length_eraseIdx_of_lt hg]; exact hk
  simp only [delGate, List.getElem_map]
  split_ifs with hkg
  · rw [List.getElem_eraseIdx_of_lt hk_e hkg, gateAt_eq_getElem C k (by omega)]
  · rw [List.getElem_eraseIdx_of_ge hk_e (by omega), gateAt_eq_getElem C (k + 1) (by omega)]

lemma delGate_isAO2 (n g r : ℕ) (C : Circuit) (hAO : IsAO2 n C)
    (hg : g < C.gates.length) (hr : r < n + g) :
    IsAO2 n (delGate n g r C) := by
  rcases hAO with ⟨hAOOnly, hRB, hLen2⟩
  refine ⟨?_, ?_, ?_⟩
  · intro gt hgt
    simp only [delGate, List.mem_map] at hgt
    obtain ⟨gt0, hgt0, rfl⟩ := hgt
    exact hAOOnly gt0 (List.mem_of_mem_eraseIdx hgt0)
  · intro k hk w' hw'
    rw [delGate_length n g r C hg] at hk
    rw [delGate_gateAt n g r C hg k hk] at hw'
    simp only [mapGate, List.mem_map] at hw'
    obtain ⟨w, hw, rfl⟩ := hw'
    split_ifs at hw with hkg
    · have hlt := hRB k (by omega) w hw
      unfold remap
      split_ifs <;> omega
    · have hlt := hRB (k + 1) (by omega) w hw
      unfold remap
      split_ifs <;> omega
  · intro gt hgt
    simp only [delGate, List.mem_map] at hgt
    obtain ⟨gt0, hgt0, rfl⟩ := hgt
    simp only [mapGate, List.length_map]
    exact hLen2 gt0 (List.mem_of_mem_eraseIdx hgt0)

lemma delGate_output_lt (n g r : ℕ) (C : Circuit) (hg : g < C.gates.length)
    (hr : r < n + g) (hout : C.output < n + C.gates.length) :
    (delGate n g r C).output < n + (delGate n g r C).gates.length := by
  rw [delGate_length n g r C hg]
  simp only [delGate, remap]
  split_ifs <;> omega

lemma origWire_remap_ne (n g r u : ℕ) (hne : u ≠ n + g) :
    origWire n g (remap n g r u) = u := by
  unfold origWire remap
  split_ifs <;> omega

lemma origWire_remap_eq (n g r : ℕ) (hr : r < n + g) :
    origWire n g (remap n g r (n + g)) = r := by
  unfold origWire remap
  split_ifs <;> omega

lemma delGate_wireVal_eq (n g r : ℕ) (C : Circuit) (x : Fin n → Bool)
    (hRB : ReadsBack n C) (hg : g < C.gates.length) (hr : r < n + g)
    (hmatch : wireVal n C (n + g) x = wireVal n C r x) :
    ∀ w < n + (delGate n g r C).gates.length,
      wireVal n (delGate n g r C) w x = wireVal n C (origWire n g w) x := by
  have hAO_rb : ReadsBack n (delGate n g r C) := by
    intro k hk w' hw'
    rw [delGate_length n g r C hg] at hk
    rw [delGate_gateAt n g r C hg k hk] at hw'
    simp only [mapGate, List.mem_map] at hw'
    obtain ⟨w, hw, rfl⟩ := hw'
    split_ifs at hw with hkg
    · have hlt := hRB k (by omega) w hw
      unfold remap; split_ifs <;> omega
    · have hlt := hRB (k + 1) (by omega) w hw
      unfold remap; split_ifs <;> omega
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw
    by_cases hwn : w < n
    · rw [wireVal_input n (delGate n g r C) x w hwn]
      have horig : origWire n g w = w := by unfold origWire; split_ifs <;> omega
      rw [horig, wireVal_input n C x w hwn]
    · set k := w - n with hk_def
      have hw_eq : w = n + k := by omega
      have hk_lt : k < (delGate n g r C).gates.length := by omega
      have hk_lt' : k < C.gates.length - 1 := by
        rw [← delGate_length n g r C hg]; exact hk_lt
      rw [hw_eq, wireVal_gate n (delGate n g r C) x k hk_lt hAO_rb]
      rw [delGate_gateAt n g r C hg k hk_lt']
      set k0 := if k < g then k else k + 1 with hk0_def
      have hk0_lt : k0 < C.gates.length := by
        rw [hk0_def]; split_ifs <;> omega
      have horig : origWire n g (n + k) = n + k0 := by
        unfold origWire; rw [hk0_def]; split_ifs <;> omega
      rw [horig, wireVal_gate n C x k0 hk0_lt hRB]
      simp only [mapGate, List.map_map]
      congr 1
      apply List.map_congr_left
      intro u hu
      have hru_lt : remap n g r u < n + k := by
        have h1 : remap n g r u ∈ (gateAt (delGate n g r C) k).inputs := by
          rw [delGate_gateAt n g r C hg k hk_lt']
          simp only [mapGate, List.mem_map]
          exact ⟨u, hu, rfl⟩
        exact hAO_rb k hk_lt (remap n g r u) h1
      have hih := ih (remap n g r u) (by omega) (by omega)
      simp only [Function.comp_apply, hih]
      by_cases hug : u = n + g
      · rw [hug, origWire_remap_eq n g r hr, hmatch]
      · rw [origWire_remap_ne n g r u hug]

lemma gateOp_eval_mono (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or)
    (l1 l2 : List Bool) (hlen : l1.length = l2.length)
    (hmono : ∀ p (hp1 : p < l1.length) (hp2 : p < l2.length), l1[p] = true → l2[p] = true) :
    op.eval l1 = true → op.eval l2 = true := by
  rcases hop with rfl | rfl
  · intro h1
    simp only [GateOp.eval, List.all_eq_true, id_eq] at h1 ⊢
    intro b hb
    rw [List.mem_iff_getElem] at hb
    obtain ⟨p, hp2, rfl⟩ := hb
    have hp1 : p < l1.length := by omega
    exact hmono p hp1 hp2 (h1 l1[p] (List.getElem_mem hp1))
  · intro h1
    simp only [GateOp.eval, List.any_eq_true, id_eq] at h1 ⊢
    obtain ⟨b, hb, rfl⟩ := h1
    rw [List.mem_iff_getElem] at hb
    obtain ⟨p, hp1, hbp⟩ := hb
    have hp2 : p < l2.length := by omega
    exact ⟨l2[p], List.getElem_mem hp2, hmono p hp1 hp2 hbp⟩

lemma delGate_wireVal_mono (n g r : ℕ) (C : Circuit) (x : Fin n → Bool)
    (hAOOnly : AndOrOnly C) (hRB : ReadsBack n C) (hg : g < C.gates.length) (hr : r < n + g)
    (hmono_g : wireVal n C (n + g) x = true → wireVal n C r x = true) :
    ∀ w < n + (delGate n g r C).gates.length,
      wireVal n C (origWire n g w) x = true → wireVal n (delGate n g r C) w x = true := by
  have hAO_rb : ReadsBack n (delGate n g r C) := by
    intro k hk w' hw'
    rw [delGate_length n g r C hg] at hk
    rw [delGate_gateAt n g r C hg k hk] at hw'
    simp only [mapGate, List.mem_map] at hw'
    obtain ⟨w, hw, rfl⟩ := hw'
    split_ifs at hw with hkg
    · have hlt := hRB k (by omega) w hw
      unfold remap; split_ifs <;> omega
    · have hlt := hRB (k + 1) (by omega) w hw
      unfold remap; split_ifs <;> omega
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw htrue
    by_cases hwn : w < n
    · rw [wireVal_input n (delGate n g r C) x w hwn]
      have horig : origWire n g w = w := by unfold origWire; split_ifs <;> omega
      rw [horig, wireVal_input n C x w hwn] at htrue
      exact htrue
    · set k := w - n with hk_def
      have hw_eq : w = n + k := by omega
      have hk_lt : k < (delGate n g r C).gates.length := by omega
      have hk_lt' : k < C.gates.length - 1 := by
        rw [← delGate_length n g r C hg]; exact hk_lt
      rw [hw_eq] at htrue ⊢
      rw [wireVal_gate n (delGate n g r C) x k hk_lt hAO_rb]
      rw [delGate_gateAt n g r C hg k hk_lt']
      set k0 := if k < g then k else k + 1 with hk0_def
      have hk0_lt : k0 < C.gates.length := by
        rw [hk0_def]; split_ifs <;> omega
      have horig : origWire n g (n + k) = n + k0 := by
        unfold origWire; rw [hk0_def]; split_ifs <;> omega
      rw [horig, wireVal_gate n C x k0 hk0_lt hRB] at htrue
      simp only [mapGate, List.map_map]
      have hop : (gateAt C k0).op = GateOp.and ∨ (gateAt C k0).op = GateOp.or := by
        rw [gateAt_eq_getElem C k0 hk0_lt]
        exact hAOOnly C.gates[k0] (List.getElem_mem hk0_lt)
      apply gateOp_eval_mono (gateAt C k0).op hop _ _ (by simp) _ htrue
      intro p hp1 hp2 hv
      simp only [List.getElem_map, Function.comp_apply] at hv ⊢
      set u := (gateAt C k0).inputs[p]'(by simpa using hp1) with hu_def
      have hu_mem : u ∈ (gateAt C k0).inputs := List.getElem_mem (by simpa using hp1)
      have hru_lt : remap n g r u < n + k := by
        have h1 : remap n g r u ∈ (gateAt (delGate n g r C) k).inputs := by
          rw [delGate_gateAt n g r C hg k hk_lt']
          simp only [mapGate, List.mem_map]
          exact ⟨u, hu_mem, rfl⟩
        exact hAO_rb k hk_lt (remap n g r u) h1
      apply ih (remap n g r u) (by omega) (by omega)
      by_cases hug : u = n + g
      · rw [hug, origWire_remap_eq n g r hr]
        rw [hug] at hv
        exact hmono_g hv
      · rw [origWire_remap_ne n g r u hug]
        exact hv

lemma delGate_wireVal_prefix_eq (n g r : ℕ) (C : Circuit) (x : Fin n → Bool)
    (hRB : ReadsBack n C) (hg : g < C.gates.length) (hr : r < n + g) :
    ∀ w < n + g, wireVal n (delGate n g r C) w x = wireVal n C w x := by
  have hAO_rb : ReadsBack n (delGate n g r C) := by
    intro k hk w' hw'
    rw [delGate_length n g r C hg] at hk
    rw [delGate_gateAt n g r C hg k hk] at hw'
    simp only [mapGate, List.mem_map] at hw'
    obtain ⟨w, hw, rfl⟩ := hw'
    split_ifs at hw with hkg
    · have hlt := hRB k (by omega) w hw
      unfold remap; split_ifs <;> omega
    · have hlt := hRB (k + 1) (by omega) w hw
      unfold remap; split_ifs <;> omega
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw
    by_cases hwn : w < n
    · rw [wireVal_input n (delGate n g r C) x w hwn, wireVal_input n C x w hwn]
    · set k := w - n with hk_def
      have hw_eq : w = n + k := by omega
      have hkg : k < g := by omega
      have hk_lt : k < (delGate n g r C).gates.length := by
        rw [delGate_length n g r C hg]; omega
      rw [hw_eq, wireVal_gate n (delGate n g r C) x k hk_lt hAO_rb]
      rw [delGate_gateAt n g r C hg k (by omega)]
      simp only [hkg, ↓reduceIte]
      rw [wireVal_gate n C x k (by omega) hRB]
      simp only [mapGate, List.map_map]
      congr 1
      apply List.map_congr_left
      intro u hu
      have hu_lt : u < n + k := hRB k (by omega) u hu
      have hrm : remap n g r u = u := by unfold remap; split_ifs <;> omega
      simp only [Function.comp_apply, hrm]
      exact ih u (by omega) (by omega)

lemma no_and_reader {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (i g : ℕ)
    (hE : G.edgeFinset.Nonempty) (hL : IsLeastAO G C)
    (hig : i < g) (hg : g < C.gates.length)
    (hBelow : BelowF G C i)
    (hgAnd : (gateAt C g).op = GateOp.and)
    (hmem : n + i ∈ (gateAt C g).inputs) : False := by
  rcases hL with ⟨hAO, hF, hMin⟩
  rcases hAO with ⟨hAOOnly, hRB, hLen2⟩
  have hout : C.output < n + C.gates.length := output_lt_of_nonempty G C hE hF
  set C' := delGate n g (n + i) C with hC'
  have hAO' : IsAO2 n C' := delGate_isAO2 n g (n + i) C ⟨hAOOnly, hRB, hLen2⟩ hg (by omega)
  have hout' : C'.output < n + C'.gates.length :=
    delGate_output_lt n g (n + i) C hg (by omega) hout
  have hF' : circuitFun n C' = graphFun G ∅ := by
    funext x
    have hmono_g : wireVal n C (n + g) x = true → wireVal n C (n + i) x = true := by
      intro hg_true
      rw [wireVal_gate n C x g hg hRB, hgAnd] at hg_true
      simp only [GateOp.eval, List.all_eq_true, List.mem_map, id_eq] at hg_true
      exact hg_true (wireVal n C (n + i) x) ⟨n + i, hmem, rfl⟩
    cases hgx : graphFun G ∅ x
    · have hi_false : wireVal n C (n + i) x = false := by
        cases hvi : wireVal n C (n + i) x with
        | false => rfl
        | true =>
          have := hBelow x hvi
          rw [hgx] at this
          cases this
      have hg_false : wireVal n C (n + g) x = false := by
        cases hvg : wireVal n C (n + g) x with
        | false => rfl
        | true =>
          have := hmono_g hvg
          rw [hi_false] at this
          cases this
      have hmatch : wireVal n C (n + g) x = wireVal n C (n + i) x := by
        rw [hg_false, hi_false]
      have hval := delGate_wireVal_eq n g (n + i) C x hRB hg (by omega) hmatch C'.output hout'
      have hcf : circuitFun n C' x = wireVal n C' C'.output x := rfl
      rw [hcf, hval]
      have hcfC : circuitFun n C x = false := by rw [hF, hgx]
      by_cases ho : C.output = n + g
      · simp only [hC', delGate]
        rw [ho, origWire_remap_eq n g (n + i) (by omega), ← hmatch]
        change wireVal n C (n + g) x = false
        rw [← ho]
        exact hcfC
      · simp only [hC', delGate]
        rw [origWire_remap_ne n g (n + i) C.output ho]
        exact hcfC
    · have hcfC : wireVal n C C.output x = true := by
        change circuitFun n C x = true
        rw [hF, hgx]
      have hval := delGate_wireVal_mono n g (n + i) C x hAOOnly hRB hg (by omega) hmono_g
        C'.output hout'
      change wireVal n C' C'.output x = true
      apply hval
      by_cases ho : C.output = n + g
      · simp only [hC', delGate]
        rw [ho, origWire_remap_eq n g (n + i) (by omega)]
        rw [ho] at hcfC
        exact hmono_g hcfC
      · simp only [hC', delGate]
        rw [origWire_remap_ne n g (n + i) C.output ho]
        exact hcfC
  have hle := hMin C' hAO' hF'
  have hsz : C'.size = C.size - 1 := delGate_length n g (n + i) C hg
  change C.gates.length ≤ C'.gates.length at hle
  rw [show C'.gates.length = C.gates.length - 1 from hsz] at hle
  omega

def pushOr (n g y i : ℕ) (C : Circuit) : Circuit :=
  let Cmid := delGate n g y C
  ⟨Cmid.gates ++ [⟨GateOp.or, [Cmid.output, n + i]⟩], n + Cmid.gates.length⟩

def shiftDown (g k : ℕ) : ℕ :=
  if k < g then k else k - 1

lemma pushOr_step {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (i g j : ℕ)
    (hE : G.edgeFinset.Nonempty) (hL : IsLeastAO G C)
    (hig : i < g) (hgj : g < j) (hj : j < C.gates.length)
    (hBelow : BelowF G C i)
    (hgOr : (gateAt C g).op = GateOp.or)
    (hjAnd : (gateAt C j).op = GateOp.and)
    (hmem : n + i ∈ (gateAt C g).inputs) :
    ∃ C' : Circuit, IsLeastAO G C' ∧ C'.size = C.size ∧
      (junk G C').card = (junk G C).card ∧ andIndexSum C' < andIndexSum C := by
  rcases hL with ⟨hAO, hF, hMin⟩
  rcases hAO with ⟨hAOOnly, hRB, hLen2⟩
  have hg : g < C.gates.length := by omega
  have hout : C.output < n + C.gates.length := output_lt_of_nonempty G C hE hF
  have hgin_len : (gateAt C g).inputs.length = 2 := by
    rw [gateAt_eq_getElem C g hg]
    exact hLen2 C.gates[g] (List.getElem_mem hg)
  rcases hgin : (gateAt C g).inputs with _ | ⟨a, _ | ⟨b, _ | _⟩⟩
  · simp [hgin] at hgin_len
  · simp [hgin] at hgin_len
  · have hmem' : n + i = a ∨ n + i = b := by
      simpa [hgin] using hmem
    set y := if a = n + i then b else a with hy_def
    have hy_mem : y ∈ (gateAt C g).inputs := by
      rw [hgin, hy_def]
      split_ifs <;> simp
    have hy_lt : y < n + g := hRB g hg y hy_mem
    have hg_eval : ∀ x : Fin n → Bool,
        wireVal n C (n + g) x = (wireVal n C (n + i) x || wireVal n C y x) := by
      intro x
      rw [wireVal_gate n C x g hg hRB, hgOr, hgin]
      simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil,
        id_eq, Bool.or_false]
      rw [hy_def]
      split_ifs with ha
      · rw [ha]
      · rcases hmem' with rfl | rfl
        · exact absurd rfl ha
        · exact Bool.or_comm _ _
    set Cmid := delGate n g y C with hCmid
    set C' := pushOr n g y i C with hC'
    have hCmid_len : Cmid.gates.length = C.gates.length - 1 := delGate_length n g y C hg
    have hC'_len : C'.gates.length = C.gates.length := by
      simp only [hC', pushOr, List.length_append, List.length_singleton, ← hCmid, hCmid_len]
      omega
    have hCmid_AO : IsAO2 n Cmid := delGate_isAO2 n g y C ⟨hAOOnly, hRB, hLen2⟩ hg hy_lt
    have hCmid_out : Cmid.output < n + Cmid.gates.length :=
      delGate_output_lt n g y C hg hy_lt hout
    have hC'_AO : IsAO2 n C' := by
      rcases hCmid_AO with ⟨h1, h2, h3⟩
      refine ⟨?_, ?_, ?_⟩
      · intro gt hgt
        simp only [hC', pushOr, ← hCmid, List.mem_append, List.mem_singleton] at hgt
        rcases hgt with hgt | rfl
        · exact h1 gt hgt
        · exact Or.inr rfl
      · intro k hk w hw
        have hk' : k < Cmid.gates.length + 1 := by
          simpa [hC', pushOr, ← hCmid] using hk
        by_cases hkm : k < Cmid.gates.length
        · have hgat : gateAt C' k = gateAt Cmid k := by
            rw [gateAt_eq_getElem C' k hk, gateAt_eq_getElem Cmid k hkm]
            simp [hC', pushOr, ← hCmid, List.getElem_append_left hkm]
          rw [hgat] at hw
          exact h2 k hkm w hw
        · have hkeq : k = Cmid.gates.length := by omega
          have hgat : gateAt C' k = ⟨GateOp.or, [Cmid.output, n + i]⟩ := by
            rw [gateAt_eq_getElem C' k hk]
            simp [hC', pushOr, ← hCmid, hkeq]
          rw [hgat] at hw
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
          rcases hw with rfl | rfl
          · omega
          · rw [hkeq, hCmid_len]; omega
      · intro gt hgt
        simp only [hC', pushOr, ← hCmid, List.mem_append, List.mem_singleton] at hgt
        rcases hgt with hgt | rfl
        · exact h3 gt hgt
        · rfl
    have hC'_F : circuitFun n C' = graphFun G ∅ := by
      funext x
      have hlast : circuitFun n C' x =
          (wireVal n Cmid Cmid.output x || wireVal n Cmid (n + i) x) := by
        change wireVal n C' (n + Cmid.gates.length) x = _
        have h := wireVal_append_last n Cmid ⟨GateOp.or, [Cmid.output, n + i]⟩
          (n + Cmid.gates.length) x
        simpa [hC', pushOr, ← hCmid, GateOp.eval] using h
      rw [hlast]
      have hni : wireVal n Cmid (n + i) x = wireVal n C (n + i) x :=
        delGate_wireVal_prefix_eq n g y C x hRB hg hy_lt (n + i) (by omega)
      rw [hni]
      cases hvi : wireVal n C (n + i) x
      · have hmatch : wireVal n C (n + g) x = wireVal n C y x := by
          rw [hg_eval x, hvi, Bool.false_or]
        have hval := delGate_wireVal_eq n g y C x hRB hg hy_lt hmatch Cmid.output hCmid_out
        rw [hval, Bool.or_false]
        have hcfC : wireVal n C C.output x = graphFun G ∅ x := congrFun hF x
        by_cases ho : C.output = n + g
        · simp only [hCmid, delGate]
          rw [ho, origWire_remap_eq n g y hy_lt, ← hmatch, ← ho]
          exact hcfC
        · simp only [hCmid, delGate]
          rw [origWire_remap_ne n g y C.output ho]
          exact hcfC
      · rw [Bool.or_true]
        exact (hBelow x hvi).symm
    have hC'_Least : IsLeastAO G C' := by
      refine ⟨hC'_AO, hC'_F, ?_⟩
      intro D hDAO hDF
      have hle := hMin D hDAO hDF
      change C'.gates.length ≤ D.gates.length
      rw [hC'_len]
      exact hle
    have hgateAt_lt : ∀ m < Cmid.gates.length,
        gateAt C' m = gateAt Cmid m := by
      intro m hm
      have hm' : m < C'.gates.length := by rw [hC'_len]; omega
      rw [gateAt_eq_getElem C' m hm', gateAt_eq_getElem Cmid m hm]
      simp [hC', pushOr, ← hCmid, List.getElem_append_left hm]
    have hgateAt_last : gateAt C' Cmid.gates.length = ⟨GateOp.or, [Cmid.output, n + i]⟩ := by
      have hm' : Cmid.gates.length < C'.gates.length := by rw [hC'_len]; omega
      rw [gateAt_eq_getElem C' Cmid.gates.length hm']
      simp [hC', pushOr, ← hCmid]
    have hop_shift : ∀ k < C.gates.length, k ≠ g →
        (gateAt C' (shiftDown g k)).op = (gateAt C k).op := by
      intro k hk hne
      have hsd : shiftDown g k < Cmid.gates.length := by
        unfold shiftDown; rw [hCmid_len]; split_ifs <;> omega
      rw [hgateAt_lt (shiftDown g k) hsd]
      rw [hCmid, delGate_gateAt n g y C hg (shiftDown g k) (by omega)]
      simp only [mapGate]
      have hidx : (if shiftDown g k < g then shiftDown g k else shiftDown g k + 1) = k := by
        unfold shiftDown; split_ifs <;> omega
      rw [hidx]
    have hval_false : ∀ k < C.gates.length, k ≠ g → ∀ x : Fin n → Bool,
        graphFun G ∅ x = false →
        gateVal n C' (shiftDown g k) x = gateVal n C k x := by
      intro k hk hne x hgx
      have hsd : shiftDown g k < Cmid.gates.length := by
        unfold shiftDown; rw [hCmid_len]; split_ifs <;> omega
      have hi_false : wireVal n C (n + i) x = false := by
        cases hvi : wireVal n C (n + i) x with
        | false => rfl
        | true =>
          have := hBelow x hvi
          rw [hgx] at this
          cases this
      have hmatch : wireVal n C (n + g) x = wireVal n C y x := by
        rw [hg_eval x, hi_false, Bool.false_or]
      have happ : wireVal n C' (n + shiftDown g k) x = wireVal n Cmid (n + shiftDown g k) x :=
        wireVal_append_lt n Cmid ⟨GateOp.or, [Cmid.output, n + i]⟩ (n + Cmid.gates.length) x
          (n + shiftDown g k) (by omega)
      have heq := delGate_wireVal_eq n g y C x hRB hg hy_lt hmatch
        (n + shiftDown g k) (by rw [← hCmid]; omega)
      have horig : origWire n g (n + shiftDown g k) = n + k := by
        unfold origWire shiftDown
        split_ifs <;> omega
      change wireVal n C' (n + shiftDown g k) x = wireVal n C (n + k) x
      rw [happ, hCmid, heq, horig]
    have hjunk : (junk G C').card = (junk G C).card := by
      symm
      apply Finset.card_bij (fun k _ => shiftDown g k)
      · intro k hk
        unfold junk gatesWhere at hk ⊢
        rw [Finset.mem_filter, Finset.mem_range] at hk ⊢
        rcases hk with ⟨hk_lt, hk_and, _, x, hkx, hgx⟩
        have hkne : k ≠ g := by
          intro hEq; rw [hEq, hgOr] at hk_and; cases hk_and
        have hsd_lt : shiftDown g k < C'.gates.length := by
          unfold shiftDown; rw [hC'_len]; split_ifs <;> omega
        refine ⟨hsd_lt, ?_, hsd_lt, x, ?_, hgx⟩
        · rw [hop_shift k hk_lt hkne]; exact hk_and
        · rw [hval_false k hk_lt hkne x hgx]; exact hkx
      · intro k1 hk1 k2 hk2 heq
        unfold junk gatesWhere at hk1 hk2
        rw [Finset.mem_filter, Finset.mem_range] at hk1 hk2
        have hne1 : k1 ≠ g := by
          intro hEq; have := hk1.2.1; rw [hEq, hgOr] at this; cases this
        have hne2 : k2 ≠ g := by
          intro hEq; have := hk2.2.1; rw [hEq, hgOr] at this; cases this
        unfold shiftDown at heq
        split_ifs at heq <;> omega
      · intro m hm
        unfold junk gatesWhere at hm
        rw [Finset.mem_filter, Finset.mem_range] at hm
        rcases hm with ⟨hm_lt, hm_and, _, x, hmx, hgx⟩
        have hm_ne : m ≠ Cmid.gates.length := by
          intro hEq; rw [hEq, hgateAt_last] at hm_and; cases hm_and
        have hm_mid : m < Cmid.gates.length := by
          rw [hC'_len] at hm_lt; omega
        set k := if m < g then m else m + 1 with hk_def
        have hk_lt : k < C.gates.length := by rw [hk_def]; split_ifs <;> omega
        have hkne : k ≠ g := by rw [hk_def]; split_ifs <;> omega
        have hsd : shiftDown g k = m := by unfold shiftDown; rw [hk_def]; split_ifs <;> omega
        refine ⟨k, ?_, hsd⟩
        unfold junk gatesWhere
        rw [Finset.mem_filter, Finset.mem_range]
        refine ⟨hk_lt, ?_, hk_lt, x, ?_, hgx⟩
        · rw [← hop_shift k hk_lt hkne, hsd]; exact hm_and
        · rw [← hval_false k hk_lt hkne x hgx, hsd]; exact hmx
    have hsum : andIndexSum C' < andIndexSum C := by
      unfold andIndexSum
      set A := (Finset.range C.gates.length).filter (fun k => isAndOp (gateAt C k).op = true)
      set A' := (Finset.range C'.gates.length).filter (fun k => isAndOp (gateAt C' k).op = true)
      have hsum_eq : ∑ k ∈ A, shiftDown g k = ∑ m ∈ A', m := by
        apply Finset.sum_bij (fun k _ => shiftDown g k)
        · intro k hk
          simp only [A, A', Finset.mem_filter, Finset.mem_range, isAndOp_eq_true_iff] at hk ⊢
          have hkne : k ≠ g := by
            intro hEq; rw [hEq, hgOr] at hk; cases hk.2
          have hsd_lt : shiftDown g k < C'.gates.length := by
            unfold shiftDown; rw [hC'_len]; split_ifs <;> omega
          exact ⟨hsd_lt, by rw [hop_shift k hk.1 hkne]; exact hk.2⟩
        · intro k1 hk1 k2 hk2 heq
          simp only [A, Finset.mem_filter, Finset.mem_range, isAndOp_eq_true_iff] at hk1 hk2
          have hne1 : k1 ≠ g := by intro hEq; rw [hEq, hgOr] at hk1; cases hk1.2
          have hne2 : k2 ≠ g := by intro hEq; rw [hEq, hgOr] at hk2; cases hk2.2
          unfold shiftDown at heq
          split_ifs at heq <;> omega
        · intro m hm
          simp only [A', Finset.mem_filter, Finset.mem_range, isAndOp_eq_true_iff] at hm
          have hm_ne : m ≠ Cmid.gates.length := by
            intro hEq; rw [hEq, hgateAt_last] at hm; cases hm.2
          have hm_mid : m < Cmid.gates.length := by rw [hC'_len] at hm; omega
          set k := if m < g then m else m + 1 with hk_def
          have hk_lt : k < C.gates.length := by rw [hk_def]; split_ifs <;> omega
          have hkne : k ≠ g := by rw [hk_def]; split_ifs <;> omega
          have hsd : shiftDown g k = m := by unfold shiftDown; rw [hk_def]; split_ifs <;> omega
          refine ⟨k, ?_, hsd⟩
          simp only [A, Finset.mem_filter, Finset.mem_range, isAndOp_eq_true_iff]
          exact ⟨hk_lt, by rw [← hop_shift k hk_lt hkne, hsd]; exact hm.2⟩
        · intro _ _; rfl
      rw [← hsum_eq]
      apply Finset.sum_lt_sum
      · intro k _
        unfold shiftDown; split_ifs <;> omega
      · refine ⟨j, ?_, ?_⟩
        · simp only [A, Finset.mem_filter, Finset.mem_range, isAndOp_eq_true_iff]
          exact ⟨hj, hjAnd⟩
        · unfold shiftDown; split_ifs <;> omega
    exact ⟨C', hC'_Least, hC'_len, hjunk, hsum⟩
  · simp [hgin] at hgin_len

lemma main_aux {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hE : G.edgeFinset.Nonempty) (m : ℕ) :
    ∀ C : Circuit, andIndexSum C = m → IsLeastAO G C →
      ∃ C' : Circuit, IsLeastAO G C' ∧ C'.size = C.size ∧
        (junk G C').card = (junk G C).card ∧ TopForm G C' := by
  induction m using Nat.strong_induction_on with
  | ind m ih =>
    intro C hm hL
    by_cases hTF : TopForm G C
    · exact ⟨C, hL, rfl, rfl, hTF⟩
    · unfold TopForm at hTF
      push Not at hTF
      obtain ⟨i, hi, j, hj, hiAnd, hiBelow, hjAnd, hCone⟩ := hTF
      obtain ⟨g, hig, hgj, hglen, hmem⟩ := exists_direct_reader n C i j hj hCone
      have hgAO : (gateAt C g).op = GateOp.and ∨ (gateAt C g).op = GateOp.or := by
        rw [gateAt_eq_getElem C g hglen]
        exact hL.1.1 C.gates[g] (List.getElem_mem hglen)
      rcases hgAO with hgAnd | hgOr
      · exfalso
        exact no_and_reader G C i g hE hL hig hglen hiBelow hgAnd hmem
      · have hgj_lt : g < j := by
          by_contra hge
          have hEq : g = j := by omega
          rw [hEq, hjAnd] at hgOr
          cases hgOr
        obtain ⟨C1, hL1, hsz1, hjunk1, hsum1⟩ :=
          pushOr_step G C i g j hE hL hig hgj_lt hj hiBelow hgOr hjAnd hmem
        obtain ⟨C2, hL2, hsz2, hjunk2, hTF2⟩ :=
          ih (andIndexSum C1) (by omega) C1 rfl hL1
        exact ⟨C2, hL2, hsz2.trans hsz1, hjunk2.trans hjunk1, hTF2⟩

end Normalize

namespace Cases

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm PEqualNP.Core

lemma edge_nonempty_of_junk_nonempty {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hL : IsLeastAO G C) (hJ : (junk G C).Nonempty) :
    G.edgeFinset.Nonempty := by
  by_contra hE
  have hnone : ∀ u v : Fin n, ¬ G.Adj u v := by
    intro u v huv
    exact hE ⟨s(u,v), by simpa using huv⟩
  let D : Circuit := ⟨[], n⟩
  have hD : IsAO2 n D := by simp [IsAO2, AndOrOnly, ReadsBack, D]
  have hDF : circuitFun n D = graphFun G ∅ := by
    funext x
    simp [circuitFun, Circuit.eval, Circuit.wires, D, graphFun, hnone]
  have hsize := hL.2.2 D hD hDF
  obtain ⟨j, hj⟩ := hJ
  have hjlt : j < C.gates.length := by
    exact Finset.mem_range.mp (Finset.mem_filter.mp hj).1
  simp only [Circuit.size, D, List.length_nil] at hsize
  omega

lemma ordered_junk_pair {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hJ : (junk G C).card = 2) :
    ∃ g h : ℕ, g < h ∧ junk G C = {g,h} := by
  obtain ⟨g,h,hne,hpair⟩ := Finset.card_eq_two.mp hJ
  rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
  · exact ⟨g,h,hlt,hpair⟩
  · exact ⟨h,g,hlt,by simpa [Finset.pair_comm] using hpair⟩

lemma normalized_two_junk {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hL : IsLeastAO G C) (hJ : (junk G C).card = 2) :
    ∃ D : Circuit, IsLeastAO G D ∧ D.size = C.size ∧ TopForm G D ∧
      IsLiftFixedPoint G D ∧ ∃ g h : ℕ, g < h ∧ junk G D = {g,h} ∧
        ¬ InCone n D h g ∧
        (InCone n D g h ∨
          (¬ InCone n D g h ∧ ∃ t ∈ tops G D, InCone n D g t ∧ InCone n D h t) ∨
          (¬ InCone n D g h ∧ ∀ t ∈ tops G D, ¬ (InCone n D g t ∧ InCone n D h t))) := by
  have hE := edge_nonempty_of_junk_nonempty G C hL
    (Finset.card_pos.mp (by omega : 0 < (junk G C).card))
  obtain ⟨D,hDL,hsize,hcount,hT⟩ :=
    Normalize.main_aux G hE (Normalize.andIndexSum C) C rfl hL
  have h2 : (junk G D).card = 2 := hcount.trans hJ
  obtain ⟨g,h,hgh,hpair⟩ := ordered_junk_pair G D h2
  refine ⟨D,hDL,hsize,hT,Lift.topForm_isLiftFixedPoint hDL.1 hDL.2.1 hT,
    g,h,hgh,hpair,?_,?_⟩
  · intro hc
    have := Lift.inCone_lt hc
    omega
  · by_cases hc : InCone n D g h
    · exact Or.inl hc
    · by_cases ht : ∃ t ∈ tops G D, InCone n D g t ∧ InCone n D h t
      · exact Or.inr (Or.inl ⟨hc,ht⟩)
      · exact Or.inr (Or.inr ⟨hc,fun t htm hboth => ht ⟨t,htm,hboth⟩⟩)

end Cases


namespace CleanReplacement

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
  PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership
  PEqualNP.CleanedNonEdge PEqualNP.TopForm

def gateBit (w : List Bool) (g : Gate) : Bool :=
  g.op.eval (g.inputs.map fun i => w.getD i false)

def stepWire (w : List Bool) (g : Gate) : List Bool := w ++ [gateBit w g]

def WiresLE (w z : List Bool) : Prop :=
  w.length = z.length ∧ ∀ i, w.getD i false = true → z.getD i false = true

def IsMonoGate (g : Gate) : Prop := g.op = GateOp.and ∨ g.op = GateOp.or

lemma monoGate_of_mem {C : Circuit} (hC : Monotone2 C) {g : Gate} (hg : g ∈ C.gates) :
    IsMonoGate g := by
  simpa [IsMonoGate] using (hC g hg).1

lemma bit_mono {w z : List Bool} (h : WiresLE w z) {g : Gate} (hg : IsMonoGate g)
    (hw : gateBit w g = true) : gateBit z g = true := by
  rcases hg with hop | hop
  · simp only [gateBit, hop, GateOp.eval, List.all_map, List.all_eq_true,
      Function.comp_apply, id_eq] at hw ⊢
    exact fun i hi => h.2 i (hw i hi)
  · simp only [gateBit, hop, GateOp.eval, List.any_map, List.any_eq_true,
      Function.comp_apply, id_eq] at hw ⊢
    obtain ⟨i, hi, hv⟩ := hw
    exact ⟨i, hi, h.2 i hv⟩

lemma append_mono {w z : List Bool} {a b : Bool} (h : WiresLE w z)
    (hab : a = true → b = true) : WiresLE (w ++ [a]) (z ++ [b]) := by
  refine ⟨by simp [h.1], ?_⟩
  intro i hi
  rw [List.getD_eq_getElem?_getD] at hi ⊢
  by_cases hlt : i < w.length
  · rw [List.getElem?_append_left hlt] at hi
    rw [List.getElem?_append_left (by rwa [← h.1])]
    simpa only [List.getD_eq_getElem?_getD] using h.2 i
      (by simpa only [List.getD_eq_getElem?_getD] using hi)
  · rw [List.getElem?_append_right (Nat.le_of_not_gt hlt)] at hi
    rw [List.getElem?_append_right (by rw [← h.1]; omega), ← h.1]
    cases hd : i - w.length with
    | zero =>
      simp only [hd, List.getElem?_cons_zero, Option.getD_some] at hi ⊢
      exact hab hi
    | succ k => simp [hd] at hi

lemma fold_mono (gs : List Gate) (hg : ∀ g ∈ gs, IsMonoGate g)
    {w z : List Bool} (h : WiresLE w z) :
    WiresLE (gs.foldl stepWire w) (gs.foldl stepWire z) := by
  induction gs generalizing w z with
  | nil => exact h
  | cons g gs ih =>
    exact ih (fun k hk => hg k (List.mem_cons_of_mem _ hk))
      (append_mono h (bit_mono h (hg g (by simp))))

lemma fold_length (gs : List Gate) (w : List Bool) :
    (gs.foldl stepWire w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [stepWire]
    omega

lemma fold_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl stepWire w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    rw [ih (stepWire w g) (by simp [stepWire]; omega)]
    simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma ofFn_getD {n : ℕ} (x : Fin n → Bool) (u : Fin n) :
    (List.ofFn x).getD u.val false = x u := by
  simp [List.getD_eq_getElem?_getD]

lemma ofFn_mono {n : ℕ} {x y : Fin n → Bool} (h : ∀ u, x u = true → y u = true) :
    WiresLE (List.ofFn x) (List.ofFn y) := by
  refine ⟨by simp, ?_⟩
  intro i hi
  by_cases hlt : i < n
  · rw [ofFn_getD y ⟨i, hlt⟩]
    exact h ⟨i, hlt⟩ (by simpa only [ofFn_getD x ⟨i, hlt⟩] using hi)
  · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simpa using Nat.le_of_not_gt hlt)] at hi
    cases hi

def patch (C : Circuit) (j : ℕ) (g : Gate) : Circuit := ⟨C.gates.set j g, C.output⟩

def earlierWires (C : Circuit) (j : ℕ) (w : List Bool) : List Bool :=
  (C.gates.take j).foldl stepWire w

def off : Gate := ⟨GateOp.or, []⟩

def edgeGate {n : ℕ} (u v : Fin n) : Gate := ⟨GateOp.and, [u.val, v.val]⟩

lemma off_bit (w : List Bool) : gateBit w off = false := rfl

lemma edge_bit {n : ℕ} (C : Circuit) (j : ℕ) (x : Fin n → Bool) (u v : Fin n) :
    gateBit (earlierWires C j (List.ofFn x)) (edgeGate u v) = (x u && x v) := by
  simp only [gateBit, edgeGate, GateOp.eval, List.map_cons, List.map_nil, List.all_cons,
    List.all_nil, id_eq, Bool.and_true]
  unfold earlierWires
  rw [fold_getD_lt _ _ _ (by simp), fold_getD_lt _ _ _ (by simp),
    ofFn_getD, ofFn_getD]

lemma wires_patch {C : Circuit} {j : ℕ} (hj : j < C.gates.length) (g : Gate) (w : List Bool) :
    (patch C j g).wires w = (C.gates.drop (j + 1)).foldl stepWire (stepWire (earlierWires C j w) g) := by
  change (C.gates.set j g).foldl stepWire w = _
  rw [List.set_eq_take_append_cons_drop, ite_eq_left hj, List.foldl_append, List.foldl_cons]
  rfl

lemma original_patch {C : Circuit} {j : ℕ} (hj : j < C.gates.length) :
    patch C j C.gates[j] = C := by
  cases C with
  | mk gates output =>
    change Circuit.mk (gates.set j gates[j]) output = Circuit.mk gates output
    congr 1
    exact List.set_getElem_self hj

lemma patch_mono {C : Circuit} (hC : Monotone2 C) {j : ℕ} (hj : j < C.gates.length)
    (g h : Gate) (w : List Bool)
    (hbit : gateBit (earlierWires C j w) g = true → gateBit (earlierWires C j w) h = true) :
    WiresLE ((patch C j g).wires w) ((patch C j h).wires w) := by
  rw [wires_patch hj, wires_patch hj]
  apply fold_mono _ (fun k hk => monoGate_of_mem hC (List.mem_of_mem_drop hk))
  exact append_mono ⟨rfl, fun _ h => h⟩ hbit

lemma patch_bit {n : ℕ} {C : Circuit} {j : ℕ} (hj : j < C.gates.length)
    (g : Gate) (x : Fin n → Bool) :
    gateVal n (patch C j g) j x = gateBit (earlierWires C j (List.ofFn x)) g := by
  have hlen : (earlierWires C j (List.ofFn x)).length = n + j := by
    unfold earlierWires
    rw [fold_length]
    simp [Nat.min_eq_left (Nat.le_of_lt hj)]
  unfold gateVal
  rw [wires_patch hj, fold_getD_lt _ _ _ (by simp [stepWire, hlen]), ← hlen]
  simp [stepWire, List.getD_eq_getElem?_getD]

lemma patch_isMono {C : Circuit} (hC : Monotone2 C) {j : ℕ} {g : Gate}
    (hg : IsMonoGate g) (hlen : g.inputs.length ≤ 2) : Monotone2 (patch C j g) := by
  intro k hk
  change k ∈ C.gates.set j g at hk
  rcases List.mem_or_eq_of_mem_set hk with hk | rfl
  · exact hC k hk
  · exact ⟨by simpa [IsMonoGate] using hg, hlen⟩

lemma gateAt_patch_ne (C : Circuit) (j k : ℕ) (g : Gate) (hne : j ≠ k) :
    gateAt (patch C j g) k = gateAt C k := by
  simp [patch, gateAt, List.getD_eq_getElem?_getD, List.getElem?_set_ne hne]

lemma graph_true {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (x : Fin n → Bool) :
    graphFun G ∅ x = true ↔ ∃ u v, G.Adj u v ∧ x u = true ∧ x v = true := by
  simp [graphFun]

lemma pair_le {n : ℕ} {x : Fin n → Bool} {u v : Fin n}
    (hu : x u = true) (hv : x v = true) (k : Fin n) :
    pairInput u v k = true → x k = true := by
  simp only [pairInput, decide_eq_true_eq]
  rintro (rfl | rfl)
  · exact hu
  · exact hv

lemma circuit_mono {n : ℕ} {C : Circuit} (hC : Monotone2 C) {x y : Fin n → Bool}
    (hxy : ∀ u, x u = true → y u = true) :
    circuitFun n C x = true → circuitFun n C y = true :=
  (fold_mono C.gates (fun _ hg => monoGate_of_mem hC hg) (ofFn_mono hxy)).2 C.output

lemma mem_junk {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit} {j : ℕ} :
    j ∈ junk G C ↔ j < C.gates.length ∧ IsDirtyAnd n G C j := by
  unfold junk gatesWhere
  rw [Finset.mem_filter, Finset.mem_range]


lemma ao2_mono {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) : Monotone2 C := by
  intro g hg
  exact ⟨by simpa using hAO.1 g hg, Nat.le_of_eq (hAO.2.2 g hg)⟩

lemma no_clean_independent_replacement {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit) (hL : IsLeastAO G C)
    (hOne : ∀ D : Circuit, IsLeastAO G D → (junk G D).card ≠ 1)
    {j k : ℕ} (hne : j ≠ k) (hJ : junk G C = {j,k})
    (hCone : ¬ InCone n C j k) (R : Gate)
    (hOp : R.op = GateOp.and ∨ R.op = GateOp.or)
    (hLen : R.inputs.length = 2) (hBack : ∀ w ∈ R.inputs, w < n + j)
    (hClean : ∀ x : Fin n → Bool, graphFun G ∅ x = false →
      gateBit (earlierWires C j (List.ofFn x)) R = false)
    (hCover : ∀ u v : Fin n, G.Adj u v →
      circuitFun n (patch C j off) (pairInput u v) = false →
      gateBit (earlierWires C j (List.ofFn (pairInput u v))) R = true) : False := by
  have hjmem : j ∈ junk G C := by rw [hJ]; simp
  have hkmem : k ∈ junk G C := by rw [hJ]; simp
  have hj : j < C.gates.length := (mem_junk.mp hjmem).1
  have hmono : Monotone2 C := ao2_mono hL.1
  let D := patch C j R
  have hDAO : IsAO2 n D := Patch.patch_isAO2 hL.1 j R hOp hLen hBack
  have hDM : Monotone2 D := ao2_mono hDAO
  have hnegative (x : Fin n → Bool) (hf : graphFun G ∅ x = false) :
      WiresLE (D.wires (List.ofFn x)) (C.wires (List.ofFn x)) := by
    have h := patch_mono hmono hj R C.gates[j] (List.ofFn x)
      (by intro hh; rw [hClean x hf] at hh; cases hh)
    rwa [original_patch hj] at h
  have hEdges (u v : Fin n) (huv : G.Adj u v) :
      circuitFun n D (pairInput u v) = true := by
    have hF : circuitFun n C (pairInput u v) = true := by
      rw [hL.2.1]
      exact (graph_true G _).mpr ⟨u,v,huv,by simp [pairInput],by simp [pairInput]⟩
    cases hCut : circuitFun n (patch C j off) (pairInput u v) with
    | false =>
      have h := patch_mono hmono hj C.gates[j] R (List.ofFn (pairInput u v))
        (fun _ => hCover u v huv hCut)
      rw [original_patch hj] at h
      exact h.2 C.output hF
    | true =>
      exact (patch_mono hmono hj off R (List.ofFn (pairInput u v))
        (by intro hh; simp [off_bit] at hh)).2 C.output hCut
  have hDF : circuitFun n D = graphFun G ∅ := by
    funext x
    cases hf : graphFun G ∅ x with
    | false =>
      cases hd : circuitFun n D x with
      | false => rfl
      | true =>
        have hh : circuitFun n C x = true := (hnegative x hf).2 C.output hd
        rw [hL.2.1,hf] at hh
        cases hh
    | true =>
      obtain ⟨u,v,huv,hu,hv⟩ := (graph_true G x).mp hf
      exact circuit_mono hDM (pair_le hu hv) (hEdges u v huv)
  have hNoJ : j ∉ junk G D := by
    intro hmem
    obtain ⟨_,_,_,x,hx,hf⟩ := mem_junk.mp hmem
    change gateVal n (patch C j R) j x = true at hx
    rw [patch_bit hj, hClean x hf] at hx
    cases hx
  have hSub : junk G D ⊆ junk G C := by
    intro a ha
    have hja : j ≠ a := by intro he; exact hNoJ (he.symm ▸ ha)
    obtain ⟨haLen,haAnd,_,x,hx,hf⟩ := mem_junk.mp ha
    have haC : a < C.gates.length := by simpa [D,patch] using haLen
    have haOp : (gateAt C a).op = GateOp.and := by
      change (gateAt (patch C j R) a).op = GateOp.and at haAnd
      rwa [gateAt_patch_ne C j a R hja] at haAnd
    exact mem_junk.mpr ⟨haC,haOp,haC,x,(hnegative x hf).2 (n+a) hx,hf⟩
  have hkD : k ∈ junk G D :=
    (Patch.patch_junk_mem_iff_of_not_inCone hL.1 hDAO hne hCone).mpr hkmem
  have hJD : junk G D = {k} := by
    apply Finset.ext
    intro a
    constructor
    · intro ha
      have hao := hSub ha
      rw [hJ] at hao
      simp only [Finset.mem_insert,Finset.mem_singleton] at hao ⊢
      rcases hao with rfl | he
      · exact (hNoJ ha).elim
      · exact he
    · intro ha
      have he := Finset.mem_singleton.mp ha
      exact he ▸ hkD
  have hDL : IsLeastAO G D := Patch.patch_isLeastAO hL hDAO hDF
  exact hOne D hDL (by rw [hJD]; simp)

end CleanReplacement

namespace FlagReduction

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm PEqualNP.ReadTwo
open CleanReplacement IndependentDescent

lemma earlier_wire_eq {n : ℕ} (C : Circuit) (j : ℕ) (hj : j ≤ C.gates.length)
    (x : Fin n → Bool) {w : ℕ} (hw : w < n + j) :
    (earlierWires C j (List.ofFn x)).getD w false = wval C x w := by
  have hlen : (earlierWires C j (List.ofFn x)).length = n + j := by
    unfold earlierWires
    rw [fold_length]
    simp [Nat.min_eq_left hj]
  have hsplit : C.wires (List.ofFn x) =
      (C.gates.drop j).foldl stepWire (earlierWires C j (List.ofFn x)) := by
    change C.gates.foldl stepWire _ = _
    conv_lhs => rw [← List.take_append_drop j C.gates, List.foldl_append]
    rfl
  unfold wval
  rw [hsplit, fold_getD_lt _ _ _ (by omega)]

lemma star_gate_bit {n : ℕ} (C : Circuit) (j : ℕ) (hj : j ≤ C.gates.length)
    (z : Fin n) (w : ℕ) (hw : w < n + j) (x : Fin n → Bool) :
    gateBit (earlierWires C j (List.ofFn x)) ⟨GateOp.and,[z.val,w]⟩ =
      (x z && wval C x w) := by
  simp only [gateBit, GateOp.eval, List.map_cons, List.map_nil, List.all_cons,
    List.all_nil, id_eq, Bool.and_true]
  rw [earlier_wire_eq C j hj x (by have := z.isLt; omega),
    earlier_wire_eq C j hj x hw, Lift.wval_input C x z.val z.isLt]

lemma filtered_independent_is_cross_star {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit) (hL : IsLeastAO G C)
    (hOne : ∀ D : Circuit, IsLeastAO G D → (junk G D).card ≠ 1)
    {j k : ℕ} (hne : j ≠ k) (hJ : junk G C = {j,k})
    (hCone : ¬ InCone n C j k) (P Q : Finset (Fin n))
    (h4 : NoFourCycle G) (hdis : Disjoint P Q) (hP : 2 ≤ P.card) (hQ : 2 ≤ Q.card)
    (hRawP : ∀ x : Fin n → Bool,
      wval C x (opnd C j 0) = decide (∃ p ∈ P, x p = true))
    (hRawQ : ∀ x : Fin n → Bool,
      wval C x (opnd C j 1) = decide (∃ q ∈ Q, x q = true))
    (hCritical : ∀ u v : Fin n, G.Adj u v →
      circuitFun n (patch C j off) (pairInput u v) = false → Useful G P Q u v) :
    ∃ z ∈ P, ∃ zp ∈ Q, G.Adj z zp ∧
      (∀ p ∈ P, G.Adj p zp) ∧ (∀ q ∈ Q, G.Adj z q) := by
  have hjmem : j ∈ junk G C := by rw [hJ]; simp
  have hj : j < C.gates.length := (mem_junk.mp hjmem).1
  have hOpnd (b : Fin 2) : opnd C j b < n + j := Lift.opnd_lt hL.1 hj b
  rcases decomposition G P Q h4 hdis hP hQ with
    hFlag | ⟨z,hzP,hzQ,hzCover⟩ | ⟨z,hzQ,hzP,hzCover⟩ | hNone
  · exact hFlag
  · exfalso
    apply no_clean_independent_replacement G C hL hOne hne hJ hCone
      ⟨GateOp.and,[z.val,opnd C j 1]⟩ (Or.inl rfl) rfl
    · intro w hw
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hw
      rcases hw with rfl | rfl
      · have := z.isLt; omega
      · exact hOpnd 1
    · intro x hf
      rw [star_gate_bit C j (Nat.le_of_lt hj) z _ (hOpnd 1) x, hRawQ x]
      apply Bool.eq_false_iff.mpr
      intro ht
      have hc := (clean_left G P Q z hzP hzQ).2.1 x
      have hp : product {z} Q x = true := by simpa [product] using ht
      have := hc hp
      rw [hf] at this
      cases this
    · intro u v huv hCut
      have hUse := hCritical u v huv hCut
      rw [star_gate_bit C j (Nat.le_of_lt hj) z _ (hOpnd 1) _, hRawQ]
      have hp := (clean_left G P Q z hzP hzQ).2.2 u v hUse.2.1 (hzCover u v hUse)
      simpa [product] using hp
  · exfalso
    apply no_clean_independent_replacement G C hL hOne hne hJ hCone
      ⟨GateOp.and,[z.val,opnd C j 0]⟩ (Or.inl rfl) rfl
    · intro w hw
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hw
      rcases hw with rfl | rfl
      · have := z.isLt; omega
      · exact hOpnd 0
    · intro x hf
      rw [star_gate_bit C j (Nat.le_of_lt hj) z _ (hOpnd 0) x, hRawP x]
      apply Bool.eq_false_iff.mpr
      intro ht
      have hc := (clean_right G P Q z hzQ hzP).2.1 x
      have hp : product P {z} x = true := by simpa [product,Bool.and_comm] using ht
      have := hc hp
      rw [hf] at this
      cases this
    · intro u v huv hCut
      have hUse := hCritical u v huv hCut
      rw [star_gate_bit C j (Nat.le_of_lt hj) z _ (hOpnd 0) _, hRawP]
      have hp := (clean_right G P Q z hzQ hzP).2.2 u v hUse.2.1 (hzCover u v hUse)
      simpa [product,Bool.and_comm] using hp
  · exfalso
    obtain ⟨e,he⟩ := Cases.edge_nonempty_of_junk_nonempty G C hL ⟨j,hjmem⟩
    obtain ⟨u,v,huv⟩ : ∃ u v : Fin n, G.Adj u v := by
      revert he
      refine Sym2.inductionOn e ?_
      intro u v he
      exact ⟨u,v,by simpa using he⟩
    apply no_clean_independent_replacement G C hL hOne hne hJ hCone
      (edgeGate u v) (Or.inl rfl) rfl
    · intro w hw
      simp only [edgeGate,List.mem_cons,List.not_mem_nil,or_false] at hw
      rcases hw with rfl | rfl <;> omega
    · intro x hf
      rw [edge_bit]
      apply Bool.eq_false_iff.mpr
      intro ht
      simp only [Bool.and_eq_true] at ht
      obtain ⟨hu,hv⟩ := ht
      have := (graph_true G x).mpr ⟨u,v,huv,hu,hv⟩
      rw [hf] at this
      cases this
    · intro a b hab hCut
      exact (hNone a b (hCritical a b hab hCut)).elim

end FlagReduction


namespace RawOperands


open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

def stepWire (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma wires_eq_foldl (C : Circuit) (x : List Bool) :
    C.wires x = C.gates.foldl stepWire x := rfl

lemma foldl_stepWire_length (gs : List Gate) (w : List Bool) :
    (gs.foldl stepWire w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [stepWire]
    omega

lemma foldl_stepWire_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl stepWire w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hlt : i < (stepWire w g).length := by simp [stepWire]; omega
    rw [ih (stepWire w g) hlt]
    simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma getD_ge_length (w : List Bool) (i : ℕ) (hi : w.length ≤ i) :
    w.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]

lemma wires_length (n : ℕ) (C : Circuit) (x : Fin n → Bool) :
    (C.wires (List.ofFn x)).length = n + C.gates.length := by
  rw [wires_eq_foldl, foldl_stepWire_length, List.length_ofFn]

lemma split_gates (gs : List Gate) (j : ℕ) (hj : j < gs.length) :
    ∃ (pre post : List Gate) (gj : Gate),
      gs = pre ++ gj :: post ∧ pre.length = j ∧ gs[j]'hj = gj := by
  refine ⟨gs.take j, gs.drop (j + 1), gs[j]'hj, ?_, by simp; omega, rfl⟩
  rw [List.cons_getElem_drop_succ, List.take_append_drop]


def W (n : ℕ) (C : Circuit) (x : Fin n → Bool) (u : ℕ) : Bool :=
  (C.wires (List.ofFn x)).getD u false

lemma gateAt_eq (C : Circuit) (k : ℕ) (hk : k < C.gates.length) : gateAt C k = C.gates[k] := by
  simp [gateAt, List.getD_eq_getElem?_getD, hk]

lemma W_gate (n : ℕ) (C : Circuit) (x : Fin n → Bool) (k : ℕ) (hk : k < C.gates.length) :
    W n C x (n + k) = (gateAt C k).op.eval ((gateAt C k).inputs.map fun i =>
      if i < n + k then W n C x i else false) := by
  obtain ⟨pre, post, gj, hgs, hpre_len, hgj⟩ := split_gates C.gates k hk
  have hga : gateAt C k = gj := by rw [gateAt_eq C k hk]; exact hgj
  rw [hga]
  let w0 := pre.foldl stepWire (List.ofFn x)
  have hw0_len : w0.length = n + k := by
    simp [w0, foldl_stepWire_length, hpre_len]
  have hCj : W n C x (n + k) = gj.op.eval (gj.inputs.map fun i => w0.getD i false) := by
    simp only [W]
    rw [wires_eq_foldl, hgs, List.foldl_append, List.foldl_cons]
    rw [foldl_stepWire_getD_lt post (stepWire w0 gj) (n + k) (by simp [stepWire]; omega)]
    simp [stepWire, List.getD_eq_getElem?_getD, hw0_len]
  rw [hCj]
  congr 1
  refine List.map_congr_left fun i _ => ?_
  by_cases hi : i < n + k
  · simp only [hi, ↓reduceIte]
    simp only [W]
    rw [wires_eq_foldl, hgs, List.foldl_append]
    exact (foldl_stepWire_getD_lt (gj :: post) w0 i (by omega)).symm
  · simp only [hi, ↓reduceIte]
    exact getD_ge_length w0 i (by omega)

lemma W_input (n : ℕ) (C : Circuit) (x : Fin n → Bool) (u : ℕ) (hu : u < n) :
    W n C x u = x ⟨u, hu⟩ := by
  simp only [W]
  rw [wires_eq_foldl, foldl_stepWire_getD_lt C.gates (List.ofFn x) u (by simpa using hu)]
  simp [List.getD_eq_getElem?_getD, hu]

open PEqualNP.CleanedNonEdge in
lemma orFold_length (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) :
    (gs.foldl (orStep n) cs).length = cs.length + gs.length := by
  induction gs generalizing cs with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [orStep]
    omega

open PEqualNP.CleanedNonEdge in
lemma orStep_mem_last (n : ℕ) (cs : List (List ℕ)) (g : Gate) (x : ℕ) :
    x ∈ (orStep n cs g).getD cs.length [] ↔ x = cs.length ∨ (g.op = GateOp.or ∧
      ∃ w ∈ g.inputs, n ≤ w ∧ w < n + cs.length ∧ x ∈ cs.getD (w - n) []) := by
  by_cases h : g.op = GateOp.or
  · simp only [orStep, List.getD_eq_getElem?_getD, List.getElem?_append_right le_rfl, h,
      ↓reduceIte, true_and, Nat.sub_self, List.getElem?_cons_zero, Option.getD_some,
      List.mem_cons, List.mem_flatMap, List.mem_filter, decide_eq_true_eq]
    constructor
    · rintro (h1 | ⟨w, ⟨hw, hn, hlt⟩, hx⟩)
      · exact Or.inl h1
      · exact Or.inr ⟨w, hw, hn, hlt, hx⟩
    · rintro (h1 | ⟨w, hw, hn, hlt, hx⟩)
      · exact Or.inl h1
      · exact Or.inr ⟨w, ⟨hw, hn, hlt⟩, hx⟩
  · simp [orStep, List.getD_eq_getElem?_getD, h]

open PEqualNP.CleanedNonEdge in
lemma orStep_getD_lt (n : ℕ) (cs : List (List ℕ)) (g : Gate) (m : ℕ) (hm : m < cs.length) :
    (orStep n cs g).getD m [] = cs.getD m [] := by
  simp [orStep, List.getD_eq_getElem?_getD, List.getElem?_append_left hm]

open PEqualNP.CleanedNonEdge in
lemma orFold_getD_lt (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) (k : ℕ)
    (hk : k < cs.length) :
    (gs.foldl (orStep n) cs).getD k [] = cs.getD k [] := by
  induction gs generalizing cs with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    rw [ih (orStep n cs g) (by simp [orStep]; omega)]
    exact orStep_getD_lt n cs g k hk

open PEqualNP.CleanedNonEdge in
lemma orSets_mem_iff (n : ℕ) (C : Circuit) (k x : ℕ) (hk : k < C.gates.length) :
    x ∈ (orSets n C).getD k [] ↔ x = k ∨ ((gateAt C k).op = GateOp.or ∧
      ∃ w ∈ (gateAt C k).inputs, n ≤ w ∧ w < n + k ∧ x ∈ (orSets n C).getD (w - n) []) := by
  obtain ⟨pre, post, gk, hgs, hpre_len, hgk⟩ := split_gates C.gates k hk
  have hga : gateAt C k = gk := by rw [gateAt_eq C k hk]; exact hgk
  rw [hga]
  have hc : orSets n C = post.foldl (orStep n) (orStep n (pre.foldl (orStep n) []) gk) := by
    simp only [orSets]
    rw [hgs, List.foldl_append, List.foldl_cons]
  have hl0 : (pre.foldl (orStep n) []).length = k := by
    rw [orFold_length]; simp [hpre_len]
  have hl1 : (orStep n (pre.foldl (orStep n) []) gk).length = k + 1 := by
    simp [orStep, hl0]
  have h1 : (orSets n C).getD k [] = (orStep n (pre.foldl (orStep n) []) gk).getD k [] := by
    rw [hc, orFold_getD_lt n post _ k (by omega)]
  have h2 : ∀ m, m < k → (orSets n C).getD m [] = (pre.foldl (orStep n) []).getD m [] := by
    intro m hm
    rw [hc, orFold_getD_lt n post _ m (by omega)]
    exact orStep_getD_lt n _ gk m (by omega)
  have h3 := orStep_mem_last n (pre.foldl (orStep n) []) gk x
  rw [hl0] at h3
  rw [h1, h3]
  constructor
  · rintro (h | ⟨hop, w, hw, hn, hlt, hx⟩)
    · exact Or.inl h
    · exact Or.inr ⟨hop, w, hw, hn, hlt, by rw [h2 (w - n) (by omega)]; exact hx⟩
  · rintro (h | ⟨hop, w, hw, hn, hlt, hx⟩)
    · exact Or.inl h
    · exact Or.inr ⟨hop, w, hw, hn, hlt, by rw [← h2 (w - n) (by omega)]; exact hx⟩


lemma W_or (n : ℕ) (C : Circuit) (x : Fin n → Bool) (r : ℕ) (hr : r < C.gates.length)
    (hop : (gateAt C r).op = GateOp.or) (i : ℕ) (hi : i ∈ (gateAt C r).inputs)
    (hlt : i < n + r) (hv : W n C x i = true) : W n C x (n + r) = true := by
  rw [W_gate n C x r hr, hop]
  simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id_eq]
  exact ⟨i, hi, by rw [ite_eq_left hlt]; exact hv⟩

lemma W_and (n : ℕ) (C : Circuit) (x : Fin n → Bool) (r : ℕ) (hr : r < C.gates.length)
    (hop : (gateAt C r).op = GateOp.and)
    (h : ∀ i ∈ (gateAt C r).inputs, i < n + r ∧ W n C x i = true) :
    W n C x (n + r) = true := by
  rw [W_gate n C x r hr, hop]
  simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id_eq]
  intro i hi
  rw [ite_eq_left (h i hi).1]; exact (h i hi).2

open PEqualNP.CleanedNonEdge in
lemma reach_val (n : ℕ) (C : Circuit) (x : Fin n → Bool) (g : ℕ)
    (hv : W n C x (n + g) = true) :
    ∀ k, k < C.gates.length → g ∈ (orSets n C).getD k [] → W n C x (n + k) = true := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk hmem
    rcases (orSets_mem_iff n C k g hk).mp hmem with h | ⟨hop, w, hw, hn, hlt, hx⟩
    · rw [← h]; exact hv
    · have h3 := ih (w - n) (by omega) (by omega) hx
      have e : n + (w - n) = w := by omega
      rw [e] at h3
      exact W_or n C x k hk hop w hw hlt h3

open PEqualNP.CleanedNonEdge in
lemma reach_up (n : ℕ) (C : Circuit) (x : Fin n → Bool) (w g : ℕ)
    (h : OrReaches n C w g) (hv : W n C x (n + g) = true) : W n C x w = true := by
  obtain ⟨hn, hmem⟩ := h
  by_cases hk : w - n < C.gates.length
  · have h3 := reach_val n C x g hv (w - n) hk hmem
    have e : n + (w - n) = w := by omega
    rw [e] at h3
    exact h3
  · exfalso
    have hlen : (orSets n C).length = C.gates.length := by
      unfold orSets; rw [orFold_length]; simp
    have hge : (orSets n C).length ≤ w - n := by omega
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hge] at hmem
    simp at hmem

lemma mem_filter_gen {α : Type} (p : α → Prop) (d : DecidablePred p) (s : Finset α) (a : α)
    (h : a ∈ @Finset.filter α p d s) : p a :=
  ((@Finset.mem_filter α p d s a).mp h).2

lemma side_val (n : ℕ) (C : Circuit) (x : Fin n → Bool) (j : ℕ) (b : Fin 2) (i : Fin n)
    (hi : i ∈ PEqualNP.TopForm.side (n := n) C j b) (hx : x i = true) :
    W n C x (PEqualNP.TopForm.opnd C j b) = true := by
  unfold PEqualNP.TopForm.side PEqualNP.TopForm.orIn at hi
  have hi2 := mem_filter_gen _ _ _ _ hi
  rcases hi2 with h | ⟨k, hk, hreach, hop, hin⟩
  · rw [← h, W_input n C x i.val i.isLt]; exact hx
  · have hk1 : W n C x (n + k) = true := by
      apply W_or n C x k hk hop i.val hin (by have := i.isLt; omega)
      rw [W_input n C x i.val i.isLt]; exact hx
    exact reach_up n C x _ k hreach hk1

open PEqualNP.EdgeOwnership in
lemma cones_len (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) :
    (gs.foldl (coneStep n) cs).length = cs.length + gs.length := by
  induction gs generalizing cs with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [coneStep]
    omega

open PEqualNP.EdgeOwnership in
lemma cones_char (n : ℕ) (gs : List Gate) :
    ∀ i j, i ∈ (gs.foldl (coneStep n) []).getD j [] ↔
      j < gs.length ∧ ∃ w ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, n ≤ w ∧ w < n + j ∧
        (i = w - n ∨ i ∈ (gs.foldl (coneStep n) []).getD (w - n) []) := by
  induction gs using List.reverseRecOn with
  | nil => intro i j; simp
  | append_singleton gs g ih =>
    intro i j
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
    have hlen : (gs.foldl (coneStep n) []).length = gs.length := by
      rw [cones_len]; simp
    have key : ∀ k, k < gs.length →
        (coneStep n (gs.foldl (coneStep n) []) g).getD k [] =
          (gs.foldl (coneStep n) []).getD k [] := by
      intro k hk
      simp only [coneStep, List.getD_eq_getElem?_getD]
      rw [List.getElem?_append_left (by omega)]
    rcases Nat.lt_trichotomy j gs.length with h | h | h
    · have e1 : (gs ++ [g]).getD j ⟨GateOp.or, []⟩ = gs.getD j ⟨GateOp.or, []⟩ := by
        simp only [List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_left h]
      rw [key j h, ih i j, e1]
      constructor
      · rintro ⟨_, w, hw, h1, h2, h3⟩
        refine ⟨by simp; omega, w, hw, h1, h2, ?_⟩
        rw [key (w - n) (by omega)]
        exact h3
      · rintro ⟨_, w, hw, h1, h2, h3⟩
        refine ⟨h, w, hw, h1, h2, ?_⟩
        rw [key (w - n) (by omega)] at h3
        exact h3
    · subst h
      have e1 : (gs ++ [g]).getD gs.length ⟨GateOp.or, []⟩ = g := by
        simp [List.getD_eq_getElem?_getD]
      have e2 : (coneStep n (gs.foldl (coneStep n) []) g).getD gs.length [] =
          (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + gs.length))).flatMap
            (fun w => (w - n) :: (gs.foldl (coneStep n) []).getD (w - n) []) := by
        simp only [coneStep, List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_right (by omega)]
        simp [hlen]
      rw [e2, e1]
      simp only [List.mem_flatMap, List.mem_filter, List.mem_cons, decide_eq_true_eq]
      constructor
      · rintro ⟨w, ⟨hw, h1, h2⟩, h3⟩
        refine ⟨by simp, w, hw, h1, h2, ?_⟩
        rw [key (w - n) (by omega)]
        exact h3
      · rintro ⟨_, w, hw, h1, h2, h3⟩
        rw [key (w - n) (by omega)] at h3
        exact ⟨w, ⟨hw, h1, h2⟩, h3⟩
    · have e0 : (coneStep n (gs.foldl (coneStep n) []) g).getD j [] = [] := by
        simp only [coneStep, List.getD_eq_getElem?_getD]
        rw [List.getElem?_eq_none (by simp; omega)]
        rfl
      rw [e0]
      constructor
      · intro h0; simp at h0
      · rintro ⟨h0, _⟩
        simp at h0
        omega

open PEqualNP.EdgeOwnership in
lemma inCone_iff (n : ℕ) (C : Circuit) (i j : ℕ) :
    InCone n C i j ↔ j < C.gates.length ∧ ∃ k, k < j ∧ n + k ∈ (gateAt C j).inputs ∧
      (i = k ∨ InCone n C i k) := by
  have h := cones_char n C.gates i j
  unfold InCone cones gateAt
  rw [h]
  constructor
  · rintro ⟨h0, w, hw, h1, h2, h3⟩
    refine ⟨h0, w - n, by omega, ?_, h3⟩
    have : n + (w - n) = w := by omega
    rw [this]
    exact hw
  · rintro ⟨h0, k, hk, hw, h3⟩
    refine ⟨h0, n + k, hw, by omega, by omega, ?_⟩
    have : n + k - n = k := by omega
    rw [this]
    exact h3


lemma gateAt_mem' (C : Circuit) (j : ℕ) (hj : j < C.gates.length) : gateAt C j ∈ C.gates := by
  rw [gateAt_eq C j hj]; exact List.getElem_mem hj

open PEqualNP.EdgeOwnership in
lemma inCone_lt (n : ℕ) (C : Circuit) : ∀ j i, InCone n C i j → i < j := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro i h
    obtain ⟨_, k, hk, _, h3⟩ := (inCone_iff n C i j).mp h
    rcases h3 with h3 | h3
    · omega
    · have := ih k hk i h3; omega

open PEqualNP.CleanedNonEdge in
lemma orReach_trans (n : ℕ) (C : Circuit) (k : ℕ) (hk : k < C.gates.length)
    (hop : (gateAt C k).op = GateOp.or) (w : ℕ) (hw : w ∈ (gateAt C k).inputs)
    (hlt : w < n + k) (g : ℕ) (h : OrReaches n C w g) : OrReaches n C (n + k) g := by
  obtain ⟨hn, hmem⟩ := h
  refine ⟨by omega, ?_⟩
  have e : n + k - n = k := by omega
  rw [e]
  exact (orSets_mem_iff n C k g hk).mpr (Or.inr ⟨hop, w, hw, hn, hlt, hmem⟩)

open PEqualNP.CleanedNonEdge in
lemma orReach_self (n : ℕ) (C : Circuit) (k : ℕ) (hk : k < C.gates.length) :
    OrReaches n C (n + k) k := by
  refine ⟨by omega, ?_⟩
  have e : n + k - n = k := by omega
  rw [e]
  exact (orSets_mem_iff n C k k hk).mpr (Or.inl rfl)

lemma orIn_mem (n : ℕ) (C : Circuit) (w : ℕ) (i : Fin n) :
    i ∈ PEqualNP.TopForm.orIn n C w ↔ ((i : ℕ) = w ∨ ∃ k < C.gates.length,
      PEqualNP.CleanedNonEdge.OrReaches n C w k ∧ (gateAt C k).op = GateOp.or ∧
        (i : ℕ) ∈ (gateAt C k).inputs) := by
  unfold PEqualNP.TopForm.orIn
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]

open PEqualNP.CleanedNonEdge in
lemma down (n : ℕ) (C : Circuit) (x : Fin n → Bool)
    (hAO : ∀ k < C.gates.length, (gateAt C k).op = GateOp.and ∨ (gateAt C k).op = GateOp.or) :
    ∀ w, W n C x w = true → (∃ i : Fin n, i ∈ PEqualNP.TopForm.orIn n C w ∧ x i = true) ∨
      ∃ k, k < C.gates.length ∧ OrReaches n C w k ∧ (gateAt C k).op = GateOp.and ∧
        W n C x (n + k) = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hv
    by_cases hwn : w < n
    · left
      refine ⟨⟨w, hwn⟩, (orIn_mem n C w _).mpr (Or.inl rfl), ?_⟩
      rw [← W_input n C x w hwn]; exact hv
    · by_cases hk : w - n < C.gates.length
      · have hw : w = n + (w - n) := by omega
        set k := w - n with hkdef
        rcases hAO k hk with hop | hop
        · right
          refine ⟨k, hk, ?_, hop, ?_⟩
          · rw [hw]; exact orReach_self n C k hk
          · rw [← hw]; exact hv
        · have hv2 := hv
          rw [hw, W_gate n C x k hk, hop] at hv2
          simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id_eq] at hv2
          obtain ⟨i, hi, hiv⟩ := hv2
          split_ifs at hiv with hlt
          rcases ih i (by omega) hiv with ⟨j, hj, hxj⟩ | ⟨k', hk', hr, hop', hv'⟩
          · left
            refine ⟨j, ?_, hxj⟩
            rw [orIn_mem] at hj ⊢
            right
            rcases hj with hj | ⟨k'', hk'', hr, hop'', hin⟩
            · refine ⟨k, hk, ?_, hop, ?_⟩
              · rw [hw]; exact orReach_self n C k hk
              · rw [hj]; exact hi
            · refine ⟨k'', hk'', ?_, hop'', hin⟩
              rw [hw]; exact orReach_trans n C k hk hop i hi hlt k'' hr
          · right
            refine ⟨k', hk', ?_, hop', hv'⟩
            rw [hw]; exact orReach_trans n C k hk hop i hi hlt k' hr
      · exfalso
        have hl := wires_length n C x
        have : W n C x w = false := getD_ge_length _ w (by omega)
        rw [this] at hv; exact Bool.false_ne_true hv

open PEqualNP.EdgeOwnership in
lemma orSets_cone (n : ℕ) (C : Circuit) : ∀ m, m < C.gates.length → ∀ k,
    k ∈ (PEqualNP.CleanedNonEdge.orSets n C).getD m [] → k = m ∨ InCone n C k m := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro hm k hk
    rcases (orSets_mem_iff n C m k hm).mp hk with h | ⟨_, w, hw, hn, hlt, hx⟩
    · exact Or.inl h
    · right
      have h2 := ih (w - n) (by omega) (by omega) k hx
      have e : n + (w - n) = w := by omega
      exact (inCone_iff n C k m).mpr ⟨hm, w - n, by omega, by rw [e]; exact hw, h2⟩

open PEqualNP.EdgeOwnership in
lemma reach_cone (n : ℕ) (C : Circuit) (j : ℕ) (hj : j < C.gates.length) (o : ℕ)
    (ho : o ∈ (gateAt C j).inputs) (hlt : o < n + j) (k : ℕ)
    (h : PEqualNP.CleanedNonEdge.OrReaches n C o k) : InCone n C k j := by
  obtain ⟨hn, hmem⟩ := h
  have h2 := orSets_cone n C (o - n) (by omega) k hmem
  have e : n + (o - n) = o := by omega
  exact (inCone_iff n C k j).mpr ⟨hj, o - n, by omega, by rw [e]; exact ho, h2⟩

open PEqualNP.TopForm PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge

lemma junk_data {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (j : ℕ) (hj : j ∈ junk G C) :
    j < C.gates.length ∧ (gateAt C j).op = GateOp.and := by
  obtain ⟨hjl, hja, _⟩ := Finset.mem_filter.mp hj
  exact ⟨Finset.mem_range.mp hjl, hja⟩

lemma operand_mem {n : ℕ} (C : Circuit) (hAO : IsAO2 n C)
    (j : ℕ) (hj : j < C.gates.length) (b : Fin 2) :
    opnd C j b ∈ (gateAt C j).inputs := by
  have hlen := hAO.2.2 _ (gateAt_mem' C j hj)
  unfold opnd
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]
  exact List.getElem_mem _

lemma raw_operand_of_no_junk_cone {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hAO : IsAO2 n C) (hTop : TopForm G C)
    (j : ℕ) (hj : j < C.gates.length) (hand : (gateAt C j).op = GateOp.and)
    (hno : ∀ k ∈ junk G C, ¬ InCone n C k j) (b : Fin 2) (x : Fin n → Bool) :
    PEqualNP.ReadTwo.wval C x (opnd C j b) =
      decide (∃ u ∈ side (n := n) C j b, x u = true) := by
  have hm := operand_mem C hAO j hj b
  have hlt := hAO.2.1 j hj _ hm
  have hi : W n C x (opnd C j b) = true ↔
      ∃ u ∈ side (n := n) C j b, x u = true := by
    constructor
    · intro hv
      have hops : ∀ k < C.gates.length,
          (gateAt C k).op = GateOp.and ∨ (gateAt C k).op = GateOp.or :=
        fun k hk => hAO.1 _ (gateAt_mem' C k hk)
      rcases down n C x hops _ hv with hraw | ⟨k, hk, hr, hop, _⟩
      · exact hraw
      · have hc := reach_cone n C j hj _ hm hlt k hr
        have hnb : ¬ BelowF G C k := fun hb => hTop k hk j hj hop hb hand hc
        have hd : ∃ y : Fin n → Bool, gateVal n C k y = true ∧ graphFun G ∅ y = false := by
          by_contra hn
          apply hnb
          intro y hy
          by_contra hf
          exact hn ⟨y, hy, Bool.eq_false_iff.mpr hf⟩
        have hkj : k ∈ junk G C :=
          Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hk, hop, hk, hd⟩
        exact (hno k hkj hc).elim
    · rintro ⟨u, hu, hxu⟩
      exact side_val n C x j b u hu hxu
  change W n C x (opnd C j b) = _
  by_cases hv : W n C x (opnd C j b) = true
  · simp [hv, hi.mp hv]
  · have hn : ¬ ∃ u ∈ side (n := n) C j b, x u = true := fun h => hv (hi.mpr h)
    simp [Bool.eq_false_iff.mpr hv, hn]

lemma independent_no_junk_ancestors {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (g h : ℕ) (hJ : junk G C = {g, h})
    (hgh : ¬ InCone n C g h) (hhg : ¬ InCone n C h g)
    (j : ℕ) (hj : j = g ∨ j = h) :
    ∀ k ∈ junk G C, ¬ InCone n C k j := by
  intro k hk hc
  have hkm : k = g ∨ k = h := by simpa [hJ] using hk
  rcases hj with rfl | rfl <;> rcases hkm with rfl | rfl
  · have := inCone_lt n C _ _ hc
    omega
  · exact hhg hc
  · exact hgh hc
  · have := inCone_lt n C _ _ hc
    omega

lemma independent_operand {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hAO : IsAO2 n C) (hTop : TopForm G C)
    (g h : ℕ) (hJ : junk G C = {g, h})
    (hgh : ¬ InCone n C g h) (hhg : ¬ InCone n C h g)
    (j : ℕ) (hj : j = g ∨ j = h) (b : Fin 2) (x : Fin n → Bool) :
    PEqualNP.ReadTwo.wval C x (opnd C j b) =
      decide (∃ u ∈ side (n := n) C j b, x u = true) := by
  have hjm : j ∈ junk G C := by simpa [hJ] using hj
  obtain ⟨hjl, hja⟩ := junk_data G C j hjm
  exact raw_operand_of_no_junk_cone G C hAO hTop j hjl hja
    (independent_no_junk_ancestors G C g h hJ hgh hhg j hj) b x

lemma and_gate_eq {n : ℕ} (C : Circuit) (hAO : IsAO2 n C)
    (j : ℕ) (hj : j < C.gates.length) (hand : (gateAt C j).op = GateOp.and)
    (x : Fin n → Bool) :
    gateVal n C j x =
      (PEqualNP.ReadTwo.wval C x (opnd C j 0) && PEqualNP.ReadTwo.wval C x (opnd C j 1)) := by
  obtain ⟨a, b, hab⟩ := List.length_eq_two.mp (hAO.2.2 _ (gateAt_mem' C j hj))
  have ham : a ∈ (gateAt C j).inputs := by simp [hab]
  have hbm : b ∈ (gateAt C j).inputs := by simp [hab]
  have hba := hAO.2.1 j hj a ham
  have hbb := hAO.2.1 j hj b hbm
  change W n C x (n + j) = _
  rw [W_gate n C x j hj, hand, hab]
  simp [GateOp.eval, opnd, hab, hba, hbb, W, PEqualNP.ReadTwo.wval]

lemma independent_product {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hAO : IsAO2 n C) (hTop : TopForm G C)
    (g h : ℕ) (hJ : junk G C = {g, h})
    (hgh : ¬ InCone n C g h) (hhg : ¬ InCone n C h g)
    (j : ℕ) (hj : j = g ∨ j = h) (x : Fin n → Bool) :
    gateVal n C j x =
      (decide (∃ u ∈ side (n := n) C j 0, x u = true) &&
        decide (∃ u ∈ side (n := n) C j 1, x u = true)) := by
  have hjm : j ∈ junk G C := by simpa [hJ] using hj
  obtain ⟨hjl, hja⟩ := junk_data G C j hjm
  rw [and_gate_eq C hAO j hjl hja x,
    independent_operand G C hAO hTop g h hJ hgh hhg j hj 0 x,
    independent_operand G C hAO hTop g h hJ hgh hhg j hj 1 x]


end RawOperands

namespace Critical.Base

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm

def stepWire (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma wires_eq_foldl (C : Circuit) (x : List Bool) :
    C.wires x = C.gates.foldl stepWire x := rfl

lemma foldl_length (gs : List Gate) (w : List Bool) :
    (gs.foldl stepWire w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [stepWire]
    omega

lemma foldl_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl stepWire w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hlt : i < (stepWire w g).length := by simp [stepWire]; omega
    rw [ih (stepWire w g) hlt]
    simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma getD_ge (w : List Bool) (i : ℕ) (hi : w.length ≤ i) : w.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]

lemma foldl_getD_gate (gs : List Gate) (w : List Bool) (j : ℕ) (hj : j < gs.length) :
    (gs.foldl stepWire w).getD (w.length + j) false =
      (gs[j]).op.eval ((gs[j]).inputs.map fun i =>
        if i < w.length + j then (gs.foldl stepWire w).getD i false else false) := by
  induction gs generalizing w j with
  | nil => simp at hj
  | cons g gs ih =>
    rw [List.foldl_cons]
    cases j with
    | zero =>
      have h1 : w.length < (stepWire w g).length := by simp [stepWire]
      rw [Nat.add_zero, foldl_getD_lt gs (stepWire w g) w.length h1]
      simp only [List.getElem_cons_zero]
      have h2 : (stepWire w g).getD w.length false =
          g.op.eval (g.inputs.map fun i => w.getD i false) := by
        simp [stepWire, List.getD_eq_getElem?_getD]
      rw [h2]
      congr 1
      apply List.map_congr_left
      intro i _
      by_cases hi : i < w.length
      · rw [ite_eq_left hi, foldl_getD_lt gs (stepWire w g) i (by simp [stepWire]; omega)]
        simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
      · rw [ite_eq_right hi]; exact getD_ge w i (by omega)
    | succ j =>
      have hj' : j < gs.length := by simpa using hj
      have key := ih (stepWire w g) j hj'
      have hl : (stepWire w g).length = w.length + 1 := by simp [stepWire]
      rw [hl] at key
      have e : w.length + (j + 1) = w.length + 1 + j := by omega
      simp only [List.getElem_cons_succ]
      rw [e]
      exact key

def val (C : Circuit) (x : List Bool) (u : ℕ) : Bool := (C.wires x).getD u false
lemma gateAt_eq {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j = C.gates[j] := by
  simp [gateAt, List.getD_eq_getElem?_getD, hj]

lemma gateAt_mem {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j ∈ C.gates := by
  rw [gateAt_eq hj]; exact List.getElem_mem hj

lemma val_input {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {u : ℕ} (hu : u < n) :
    val C x u = x.getD u false := by
  unfold val; rw [wires_eq_foldl]; exact foldl_getD_lt _ _ _ (by omega)

lemma val_ge {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {u : ℕ}
    (hu : n + C.gates.length ≤ u) : val C x u = false := by
  unfold val; apply getD_ge; rw [wires_eq_foldl, foldl_length]; omega

lemma val_gate {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {j : ℕ}
    (hj : j < C.gates.length) :
    val C x (n + j) = (gateAt C j).op.eval ((gateAt C j).inputs.map fun i =>
      if i < n + j then val C x i else false) := by
  subst hx
  rw [gateAt_eq hj]
  exact foldl_getD_gate C.gates x j hj
lemma val_or {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {r : ℕ}
    (hr : r < C.gates.length) (hop : (gateAt C r).op = GateOp.or) :
    val C x (n + r) = true ↔ ∃ i ∈ (gateAt C r).inputs, i < n + r ∧ val C x i = true := by
  rw [val_gate hx hr, hop]
  simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id_eq]
  constructor
  · rintro ⟨i, hi, h⟩
    by_cases hlt : i < n + r
    · rw [ite_eq_left hlt] at h; exact ⟨i, hi, hlt, h⟩
    · rw [ite_eq_right hlt] at h; cases h
  · rintro ⟨i, hi, hlt, h⟩
    exact ⟨i, hi, by rw [ite_eq_left hlt]; exact h⟩

lemma val_and {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {r : ℕ}
    (hr : r < C.gates.length) (hop : (gateAt C r).op = GateOp.and) :
    val C x (n + r) = true ↔ ∀ i ∈ (gateAt C r).inputs, i < n + r ∧ val C x i = true := by
  rw [val_gate hx hr, hop]
  simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id_eq]
  constructor
  · intro h i hi
    have h' := h i hi
    by_cases hlt : i < n + r
    · rw [ite_eq_left hlt] at h'; exact ⟨hlt, h'⟩
    · rw [ite_eq_right hlt] at h'; cases h'
  · intro h i hi
    rw [ite_eq_left (h i hi).1]; exact (h i hi).2
lemma val_ofFn {n : ℕ} (C : Circuit) (x : Fin n → Bool) (u : Fin n) :
    val C (List.ofFn x) u.val = x u := by
  rw [val_input (n := n) (by simp) u.isLt]
  simp [List.getD_eq_getElem?_getD]

lemma gateVal_eq_val (n : ℕ) (C : Circuit) (j : ℕ) (x : Fin n → Bool) :
    PEqualNP.EdgeOwnership.gateVal n C j x = val C (List.ofFn x) (n + j) := rfl

def OrStep (n : ℕ) (C : Circuit) (w w' : ℕ) : Prop :=
  ∃ k, k < C.gates.length ∧ w = n + k ∧ (gateAt C k).op = GateOp.or ∧
    w' ∈ (gateAt C k).inputs ∧ w' < n + k

lemma orStep_up {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {w w' : ℕ}
    (h : Relation.ReflTransGen (OrStep n C) w w') (hv : val C x w' = true) :
    val C x w = true := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact hv
  | head hstep _ ih =>
    obtain ⟨k, hk, rfl, hop, hin, hlt⟩ := hstep
    exact (val_or hx hk hop).mpr ⟨_, hin, hlt, ih⟩

lemma or_trace {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) :
    ∀ w : ℕ, val C x w = true →
      ∃ w', Relation.ReflTransGen (OrStep n C) w w' ∧ val C x w' = true ∧
        (w' < n ∨ ∃ h, h < C.gates.length ∧ w' = n + h ∧ (gateAt C h).op ≠ GateOp.or) := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hv
    by_cases hw : w < n
    · exact ⟨w, Relation.ReflTransGen.refl, hv, Or.inl hw⟩
    · by_cases hlen : n + C.gates.length ≤ w
      · rw [val_ge hx hlen] at hv; cases hv
      · obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
        have hk : k < C.gates.length := by omega
        by_cases hop : (gateAt C k).op = GateOp.or
        · obtain ⟨i, hin, hlt, hi⟩ := (val_or hx hk hop).mp hv
          obtain ⟨w', hr, hv', hw'⟩ := ih i hlt hi
          exact ⟨w', Relation.ReflTransGen.head ⟨k, hk, rfl, hop, hin, hlt⟩ hr, hv', hw'⟩
        · exact ⟨n + k, Relation.ReflTransGen.refl, hv, Or.inr ⟨k, hk, rfl, hop⟩⟩

lemma pairInput_left {n : ℕ} (u v : Fin n) : pairInput u v u = true := by
  simp [pairInput]

lemma pairInput_right {n : ℕ} (u v : Fin n) : pairInput u v v = true := by
  simp [pairInput]

lemma pairInput_true {n : ℕ} (u v w : Fin n) : pairInput u v w = true ↔ w = u ∨ w = v := by
  simp [pairInput]

lemma graphFun_pair {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (u v : Fin n) :
    graphFun G ∅ (pairInput u v) = true ↔ G.Adj u v := by
  simp only [graphFun, Finset.notMem_empty, false_and, exists_false, decide_false,
    Bool.false_or, decide_eq_true_eq, pairInput_true]
  constructor
  · rintro ⟨a, b, hab, ha, hb⟩
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · exact (G.irrefl hab).elim
    · exact hab
    · exact hab.symm
    · exact (G.irrefl hab).elim
  · intro h
    exact ⟨u, v, h, Or.inl rfl, Or.inr rfl⟩
lemma operand_trace {n : ℕ} {C : Circuit} (u v : Fin n) (p : ℕ)
    (hv : val C (List.ofFn (pairInput u v)) p = true) :
    (∃ t : Fin n, (t = u ∨ t = v) ∧ Relation.ReflTransGen (OrStep n C) p t.val) ∨
    (∃ h, h < C.gates.length ∧ (gateAt C h).op ≠ GateOp.or ∧
      Relation.ReflTransGen (OrStep n C) p (n + h) ∧
      val C (List.ofFn (pairInput u v)) (n + h) = true) := by
  obtain ⟨w', hr, hv', hw'⟩ := or_trace (n := n) (C := C) (x := List.ofFn (pairInput u v))
    (by simp) p hv
  rcases hw' with hlt | ⟨h, hh, rfl, hop⟩
  · left
    refine ⟨⟨w', hlt⟩, ?_, hr⟩
    have h1 := val_ofFn C (pairInput u v) ⟨w', hlt⟩
    rw [show (⟨w', hlt⟩ : Fin n).val = w' from rfl, hv'] at h1
    exact (pairInput_true u v _).mp h1.symm
  · right
    exact ⟨h, hh, hop, hr, hv'⟩

lemma reach_var_val {n : ℕ} {C : Circuit} (x : Fin n → Bool) (p : ℕ) (t : Fin n)
    (hr : Relation.ReflTransGen (OrStep n C) p t.val) (ht : x t = true) :
    val C (List.ofFn x) p = true :=
  orStep_up (n := n) (by simp) hr (by rw [val_ofFn]; exact ht)
lemma edge_trace {n : ℕ} (G : SimpleGraph (Fin n)) {C : Circuit} (F : (Fin n → Bool) → Bool)
    (hF : ∀ u v : Fin n, F (pairInput u v) = true → G.Adj u v)
    (hout : ∀ x : Fin n → Bool, val C (List.ofFn x) C.output = F x)
    (u v : Fin n) (huv : F (pairInput u v) = true) :
    ∃ a, a < C.gates.length ∧ (gateAt C a).op ≠ GateOp.or ∧
      Relation.ReflTransGen (OrStep n C) C.output (n + a) ∧
      val C (List.ofFn (pairInput u v)) (n + a) = true := by
  rcases operand_trace (C := C) u v C.output (by rw [hout]; exact huv) with
    ⟨t, _, hr⟩ | h
  · exfalso
    have h1 := reach_var_val (pairInput t t) _ t hr (pairInput_left t t)
    rw [hout] at h1
    exact G.irrefl (hF t t h1)
  · exact h

lemma below_of_reach {n : ℕ} {C : Circuit} (F : (Fin n → Bool) → Bool)
    (hout : ∀ x : Fin n → Bool, val C (List.ofFn x) C.output = F x) (a : ℕ)
    (hr : Relation.ReflTransGen (OrStep n C) C.output (n + a)) (x : Fin n → Bool)
    (hv : val C (List.ofFn x) (n + a) = true) : F x = true := by
  rw [← hout]
  exact orStep_up (n := n) (by simp) hr hv
lemma cones_len (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) :
    (gs.foldl (coneStep n) cs).length = cs.length + gs.length := by
  induction gs generalizing cs with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [coneStep]
    omega

lemma cones_char (n : ℕ) (gs : List Gate) :
    ∀ i j, i ∈ (gs.foldl (coneStep n) []).getD j [] ↔
      j < gs.length ∧ ∃ w ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, n ≤ w ∧ w < n + j ∧
        (i = w - n ∨ i ∈ (gs.foldl (coneStep n) []).getD (w - n) []) := by
  induction gs using List.reverseRecOn with
  | nil => intro i j; simp
  | append_singleton gs g ih =>
    intro i j
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
    have hlen : (gs.foldl (coneStep n) []).length = gs.length := by
      rw [cones_len]; simp
    have key : ∀ k, k < gs.length →
        (coneStep n (gs.foldl (coneStep n) []) g).getD k [] =
          (gs.foldl (coneStep n) []).getD k [] := by
      intro k hk
      simp only [coneStep, List.getD_eq_getElem?_getD]
      rw [List.getElem?_append_left (by omega)]
    rcases Nat.lt_trichotomy j gs.length with h | h | h
    · have e1 : (gs ++ [g]).getD j ⟨GateOp.or, []⟩ = gs.getD j ⟨GateOp.or, []⟩ := by
        simp only [List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_left h]
      rw [key j h, ih i j, e1]
      constructor
      · rintro ⟨_, w, hw, h1, h2, h3⟩
        refine ⟨by simp; omega, w, hw, h1, h2, ?_⟩
        rw [key (w - n) (by omega)]
        exact h3
      · rintro ⟨_, w, hw, h1, h2, h3⟩
        refine ⟨h, w, hw, h1, h2, ?_⟩
        rw [key (w - n) (by omega)] at h3
        exact h3
    · subst h
      have e1 : (gs ++ [g]).getD gs.length ⟨GateOp.or, []⟩ = g := by
        simp [List.getD_eq_getElem?_getD]
      have e2 : (coneStep n (gs.foldl (coneStep n) []) g).getD gs.length [] =
          (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + gs.length))).flatMap
            (fun w => (w - n) :: (gs.foldl (coneStep n) []).getD (w - n) []) := by
        simp only [coneStep, List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_right (by omega)]
        simp [hlen]
      rw [e2, e1]
      simp only [List.mem_flatMap, List.mem_filter, List.mem_cons, decide_eq_true_eq]
      constructor
      · rintro ⟨w, ⟨hw, h1, h2⟩, h3⟩
        refine ⟨by simp, w, hw, h1, h2, ?_⟩
        rw [key (w - n) (by omega)]
        exact h3
      · rintro ⟨_, w, hw, h1, h2, h3⟩
        rw [key (w - n) (by omega)] at h3
        exact ⟨w, ⟨hw, h1, h2⟩, h3⟩
    · have e0 : (coneStep n (gs.foldl (coneStep n) []) g).getD j [] = [] := by
        simp only [coneStep, List.getD_eq_getElem?_getD]
        rw [List.getElem?_eq_none (by simp; omega)]
        rfl
      rw [e0]
      constructor
      · intro h0; simp at h0
      · rintro ⟨h0, _⟩
        simp at h0
        omega

lemma inCone_iff (n : ℕ) (C : Circuit) (i j : ℕ) :
    InCone n C i j ↔ j < C.gates.length ∧ ∃ k, k < j ∧ n + k ∈ (gateAt C j).inputs ∧
      (i = k ∨ InCone n C i k) := by
  have h := cones_char n C.gates i j
  unfold InCone cones gateAt
  rw [h]
  constructor
  · rintro ⟨h0, w, hw, h1, h2, h3⟩
    refine ⟨h0, w - n, by omega, ?_, h3⟩
    have : n + (w - n) = w := by omega
    rw [this]
    exact hw
  · rintro ⟨h0, k, hk, hw, h3⟩
    refine ⟨h0, n + k, hw, by omega, by omega, ?_⟩
    have : n + k - n = k := by omega
    rw [this]
    exact h3

lemma orStep_le {n : ℕ} {C : Circuit} {w w' : ℕ}
    (h : Relation.ReflTransGen (OrStep n C) w w') : w' ≤ w := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact le_rfl
  | head hstep _ ih =>
    obtain ⟨k, _, rfl, _, _, hlt⟩ := hstep
    omega

lemma orStep_cone {n : ℕ} {C : Circuit} {w w' : ℕ}
    (h : Relation.ReflTransGen (OrStep n C) w w') :
    ∀ k h', w = n + k → w' = n + h' → h' = k ∨ InCone n C h' k := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => intro k h' h1 h2; left; omega
  | @head a c hstep hrest ih =>
    intro k h' h1 h2
    obtain ⟨k0, hk0, e, _, hin, hlt⟩ := hstep
    have hk : k0 = k := by omega
    subst hk
    have hle := orStep_le hrest
    obtain ⟨k1, hk1⟩ : ∃ k1, c = n + k1 := ⟨c - n, by omega⟩
    subst hk1
    right
    rw [inCone_iff]
    exact ⟨hk0, k1, by omega, hin, ih k1 h' rfl h2⟩

lemma operand_cone {n : ℕ} {C : Circuit} {a p h : ℕ} (ha : a < C.gates.length)
    (hin : p ∈ (gateAt C a).inputs) (hp : p < n + a)
    (hr : Relation.ReflTransGen (OrStep n C) p (n + h)) : InCone n C h a := by
  have hle := orStep_le hr
  obtain ⟨k1, rfl⟩ : ∃ k1, p = n + k1 := ⟨p - n, by omega⟩
  rw [inCone_iff]
  exact ⟨ha, k1, by omega, hin, orStep_cone hr k1 h rfl rfl⟩
lemma orSets_len (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) :
    (gs.foldl (orStep n) cs).length = cs.length + gs.length := by
  induction gs generalizing cs with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [orStep]
    omega

lemma orSets_char (n : ℕ) (gs : List Gate) :
    ∀ i j, i ∈ (gs.foldl (orStep n) []).getD j [] ↔
      j < gs.length ∧ (i = j ∨ ((gs.getD j ⟨GateOp.or, []⟩).op = GateOp.or ∧
        ∃ w ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, n ≤ w ∧ w < n + j ∧
          i ∈ (gs.foldl (orStep n) []).getD (w - n) [])) := by
  induction gs using List.reverseRecOn with
  | nil => intro i j; simp
  | append_singleton gs g ih =>
    intro i j
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
    have hlen : (gs.foldl (orStep n) []).length = gs.length := by
      rw [orSets_len]; simp
    have key : ∀ k, k < gs.length →
        (orStep n (gs.foldl (orStep n) []) g).getD k [] =
          (gs.foldl (orStep n) []).getD k [] := by
      intro k hk
      simp only [orStep, List.getD_eq_getElem?_getD]
      rw [List.getElem?_append_left (by omega)]
    rcases Nat.lt_trichotomy j gs.length with h | h | h
    · have e1 : (gs ++ [g]).getD j ⟨GateOp.or, []⟩ = gs.getD j ⟨GateOp.or, []⟩ := by
        simp only [List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_left h]
      rw [key j h, ih i j, e1]
      constructor
      · rintro ⟨_, h3⟩
        refine ⟨by simp; omega, ?_⟩
        rcases h3 with h3 | ⟨hop, w, hw, h1, h2, h3⟩
        · exact Or.inl h3
        · refine Or.inr ⟨hop, w, hw, h1, h2, ?_⟩
          rw [key (w - n) (by omega)]
          exact h3
      · rintro ⟨_, h3⟩
        refine ⟨h, ?_⟩
        rcases h3 with h3 | ⟨hop, w, hw, h1, h2, h3⟩
        · exact Or.inl h3
        · rw [key (w - n) (by omega)] at h3
          exact Or.inr ⟨hop, w, hw, h1, h2, h3⟩
    · subst h
      have e1 : (gs ++ [g]).getD gs.length ⟨GateOp.or, []⟩ = g := by
        simp [List.getD_eq_getElem?_getD]
      rw [e1]
      by_cases hop : g.op = GateOp.or
      · have e2 : (orStep n (gs.foldl (orStep n) []) g).getD gs.length [] =
            gs.length :: (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + gs.length))).flatMap
              (fun w => (gs.foldl (orStep n) []).getD (w - n) []) := by
          simp only [orStep, List.getD_eq_getElem?_getD]
          rw [List.getElem?_append_right (by omega)]
          simp [hlen, hop]
        rw [e2]
        simp only [List.mem_cons, List.mem_flatMap, List.mem_filter, decide_eq_true_eq]
        constructor
        · rintro (h3 | ⟨w, ⟨hw, h1, h2⟩, h3⟩)
          · exact ⟨by simp, Or.inl h3⟩
          · refine ⟨by simp, Or.inr ⟨hop, w, hw, h1, h2, ?_⟩⟩
            rw [key (w - n) (by omega)]
            exact h3
        · rintro ⟨_, h3 | ⟨_, w, hw, h1, h2, h3⟩⟩
          · exact Or.inl h3
          · rw [key (w - n) (by omega)] at h3
            exact Or.inr ⟨w, ⟨hw, h1, h2⟩, h3⟩
      · have e2 : (orStep n (gs.foldl (orStep n) []) g).getD gs.length [] = [gs.length] := by
          simp only [orStep, List.getD_eq_getElem?_getD]
          rw [List.getElem?_append_right (by omega)]
          simp [hlen, hop]
        rw [e2]
        simp only [List.mem_singleton]
        constructor
        · intro h3
          exact ⟨by simp, Or.inl h3⟩
        · rintro ⟨_, h3 | ⟨hop2, _⟩⟩
          · exact h3
          · exact (hop hop2).elim
    · have e0 : (orStep n (gs.foldl (orStep n) []) g).getD j [] = [] := by
        simp only [orStep, List.getD_eq_getElem?_getD]
        rw [List.getElem?_eq_none (by simp; omega)]
        rfl
      rw [e0]
      constructor
      · intro h0; simp at h0
      · rintro ⟨h0, _⟩
        simp at h0
        omega

lemma orReaches_iff (n : ℕ) (C : Circuit) (k g : ℕ) :
    OrReaches n C (n + k) g ↔ k < C.gates.length ∧ (g = k ∨ ((gateAt C k).op = GateOp.or ∧
      ∃ i ∈ (gateAt C k).inputs, i < n + k ∧ OrReaches n C i g)) := by
  have h := orSets_char n C.gates g k
  unfold OrReaches orSets gateAt
  have e : n + k - n = k := by omega
  rw [e, h]
  constructor
  · rintro ⟨_, hk, h3⟩
    refine ⟨hk, ?_⟩
    rcases h3 with h3 | ⟨hop, w, hw, h1, h2, h3⟩
    · exact Or.inl h3
    · exact Or.inr ⟨hop, w, hw, h2, h1, h3⟩
  · rintro ⟨hk, h3⟩
    refine ⟨by omega, hk, ?_⟩
    rcases h3 with h3 | ⟨hop, w, hw, h2, h1, h3⟩
    · exact Or.inl h3
    · exact Or.inr ⟨hop, w, hw, h1, h2, h3⟩

lemma reach_orReaches {n : ℕ} {C : Circuit} {w w2 : ℕ}
    (h : Relation.ReflTransGen (OrStep n C) w w2) :
    ∀ g, w2 = n + g → g < C.gates.length → OrReaches n C w g := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl =>
    intro g h1 hg
    subst h1
    exact (orReaches_iff n C g g).mpr ⟨hg, Or.inl rfl⟩
  | @head a c hstep hrest ih =>
    intro g h1 hg
    obtain ⟨k, hk, rfl, hop, hin, hlt⟩ := hstep
    exact (orReaches_iff n C k g).mpr ⟨hk, Or.inr ⟨hop, c, hin, hlt, ih g h1 hg⟩⟩

lemma orReaches_reach {n : ℕ} {C : Circuit} (g : ℕ) :
    ∀ w, OrReaches n C w g →
      Relation.ReflTransGen (OrStep n C) w (n + g) ∧ g < C.gates.length := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro h
    have hnw : n ≤ w := h.1
    obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
    obtain ⟨hk, h3⟩ := (orReaches_iff n C k g).mp h
    rcases h3 with rfl | ⟨hop, i, hi, hlt, hr⟩
    · exact ⟨Relation.ReflTransGen.refl, hk⟩
    · obtain ⟨hr2, hg⟩ := ih i hlt hr
      exact ⟨Relation.ReflTransGen.head ⟨k, hk, rfl, hop, hi, hlt⟩ hr2, hg⟩

lemma mem_orIn_reach {n : ℕ} {C : Circuit} {p : ℕ} (u : Fin n)
    (hu : u ∈ PEqualNP.TopForm.orIn n C p) :
    Relation.ReflTransGen (OrStep n C) p u.val := by
  simp only [PEqualNP.TopForm.orIn, Finset.mem_filter, Finset.mem_univ, true_and] at hu
  rcases hu with h | ⟨k, hk, hr, hop, hin⟩
  · rw [h]
  · exact (orReaches_reach k p hr).1.tail ⟨k, hk, rfl, hop, hin, by omega⟩

lemma reach_mem_orIn {n : ℕ} {C : Circuit} {p : ℕ} (u : Fin n)
    (hr : Relation.ReflTransGen (OrStep n C) p u.val) :
    u ∈ PEqualNP.TopForm.orIn n C p := by
  simp only [PEqualNP.TopForm.orIn, Finset.mem_filter, Finset.mem_univ, true_and]
  rcases Relation.ReflTransGen.cases_tail hr with h | ⟨c, hpc, hstep⟩
  · exact Or.inl h
  · obtain ⟨k, hk, rfl, hop, hin, _⟩ := hstep
    exact Or.inr ⟨k, hk, reach_orReaches hpc k rfl hk, hop, hin⟩

variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}

lemma topData {a : ℕ} (ha : a ∈ tops G C) :
    a < C.gates.length ∧ (gateAt C a).op = GateOp.and ∧ BelowF G C a := by
  simpa only [tops, gatesWhere, Finset.mem_filter, Finset.mem_range] using ha
lemma junkData {a : ℕ} (ha : a ∈ junk G C) :
    a < C.gates.length ∧ (gateAt C a).op = GateOp.and ∧
      ∃ x : Fin n → Bool, gateVal n C a x = true ∧ graphFun G ∅ x = false := by
  rcases Finset.mem_filter.mp ha with ⟨hr, hop, hal, hd⟩
  exact ⟨hal, hop, hd⟩
lemma binaryInputs (hAO : IsAO2 n C) {a : ℕ} (ha : a < C.gates.length) :
    ∃ p q, (gateAt C a).inputs = [p, q] :=
  List.length_eq_two.mp (hAO.2.2 _ (gateAt_mem ha))
lemma opndMem (hAO : IsAO2 n C) {a : ℕ} (ha : a < C.gates.length) (b : Fin 2) :
    opnd C a b ∈ (gateAt C a).inputs := by
  obtain ⟨p, q, hpq⟩ := binaryInputs hAO ha
  fin_cases b <;> simp [opnd, hpq]
lemma opndBound (hAO : IsAO2 n C) {a : ℕ} (ha : a < C.gates.length) (b : Fin 2) :
    opnd C a b < n + a :=
  hAO.2.1 a ha _ (opndMem hAO ha b)
lemma andValBoth (hAO : IsAO2 n C) {a : ℕ} (ha : a < C.gates.length)
    (hop : (gateAt C a).op = GateOp.and) (x : Fin n → Bool) :
    gateVal n C a x = true ↔
      val C (List.ofFn x) (opnd C a 0) = true ∧
      val C (List.ofFn x) (opnd C a 1) = true := by
  rw [gateVal_eq_val, val_and (n := n) (by simp) ha hop]
  constructor
  · intro h
    exact ⟨(h _ (opndMem hAO ha 0)).2, (h _ (opndMem hAO ha 1)).2⟩
  · intro h i hi
    refine ⟨hAO.2.1 a ha i hi, ?_⟩
    obtain ⟨p, q, hpq⟩ := binaryInputs hAO ha
    rcases List.mem_cons.mp (hpq ▸ hi) with rfl | hq
    · simpa [opnd, hpq] using h.1
    · have e : i = q := List.mem_singleton.mp hq
      subst i
      simpa [opnd, hpq] using h.2
lemma andValOperands (hAO : IsAO2 n C) {a : ℕ} (ha : a < C.gates.length)
    (hop : (gateAt C a).op = GateOp.and) (x : Fin n → Bool) :
    gateVal n C a x = true ↔ ∀ b : Fin 2, val C (List.ofFn x) (opnd C a b) = true := by
  rw [andValBoth hAO ha hop]
  constructor
  · intro h b
    fin_cases b
    · exact h.1
    · exact h.2
  · intro h
    exact ⟨h 0, h 1⟩
lemma operandReachCone (hAO : IsAO2 n C) {a h : ℕ} (ha : a < C.gates.length)
    {b : Fin 2} (hr : OrReaches n C (opnd C a b) h) :
    InCone n C h a :=
  operand_cone ha (opndMem hAO ha b) (opndBound hAO ha b)
    (orReaches_reach h _ hr).1
lemma operandReachLt (hAO : IsAO2 n C) {a h : ℕ} (ha : a < C.gates.length)
    {b : Fin 2} (hr : OrReaches n C (opnd C a b) h) : h < a := by
  have hle := orStep_le (orReaches_reach h _ hr).1
  have hb := opndBound hAO ha b
  omega
lemma operandOrAndJunk (hAO : IsAO2 n C) (hT : TopForm G C) {a h : ℕ}
    (ha : a < C.gates.length) (hop : (gateAt C a).op = GateOp.and)
    {b : Fin 2} (hr : OrReaches n C (opnd C a b) h)
    (hh : (gateAt C h).op = GateOp.and) : h ∈ junk G C := by
  have hlen := (orReaches_reach h _ hr).2
  have hnb : ¬ BelowF G C h :=
    fun hb => hT h hlen a ha hh hb hop (operandReachCone hAO ha hr)
  have hdirty : ∃ x : Fin n → Bool, gateVal n C h x = true ∧ graphFun G ∅ x = false := by
    by_contra hne
    apply hnb
    intro x hx
    by_contra hf
    exact hne ⟨x, hx, Bool.eq_false_iff.mpr hf⟩
  exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hlen, hh, hlen, hdirty⟩
lemma reachVal {w h : ℕ} {x : Fin n → Bool} (hr : OrReaches n C w h)
    (hh : gateVal n C h x = true) : val C (List.ofFn x) w = true :=
  orStep_up (n := n) (by simp) (orReaches_reach h _ hr).1 hh
lemma eitherOperand (b c : Fin 2) : c = b ∨ c = 1 - b := by
  fin_cases b <;> fin_cases c <;> decide
lemma oppositeSideWmax (hAO : IsAO2 n C) {a j : ℕ} (ha : a ∈ tops G C) {b : Fin 2}
    (hr : OrReaches n C (opnd C a b) j) :
    side (n := n) C a (1 - b) ⊆ wmax G C j := by
  intro t ht
  obtain ⟨hal, hao, hab⟩ := topData ha
  simp only [wmax, Finset.mem_filter, Finset.mem_univ, true_and]
  intro x hj hx
  apply hab x
  apply (andValOperands hAO hal hao x).mpr
  intro c
  rcases eitherOperand b c with rfl | rfl
  · exact reachVal hr hj
  · exact reach_var_val x _ t (mem_orIn_reach t ht) hx
lemma orInTrans {w z : ℕ} (hr : Relation.ReflTransGen (OrStep n C) w z) :
    orIn n C z ⊆ orIn n C w :=
  fun x hx => reach_mem_orIn x (hr.trans (mem_orIn_reach x hx))
lemma orStepOpnd (hAO : IsAO2 n C) {m : ℕ} (hm : m < C.gates.length)
    (hop : (gateAt C m).op = GateOp.or) (b : Fin 2) :
    OrStep n C (n + m) (opnd C m b) :=
  ⟨m, hm, rfl, hop, opndMem hAO hm b, opndBound hAO hm b⟩
lemma inputsAsOpnd (hAO : IsAO2 n C) {m z : ℕ} (hm : m < C.gates.length)
    (hz : z ∈ (gateAt C m).inputs) : ∃ b : Fin 2, z = opnd C m b := by
  obtain ⟨p, q, hpq⟩ := binaryInputs hAO hm
  rcases List.mem_cons.mp (hpq ▸ hz) with rfl | hq
  · exact ⟨0, by simp [opnd, hpq]⟩
  · have e : z = q := List.mem_singleton.mp hq
    exact ⟨1, by simpa [opnd, hpq] using e⟩
lemma orNOfRaw {m : ℕ} (hm : m < C.gates.length) (hop : (gateAt C m).op = GateOp.or)
    (hn : (orIn n C (n + m)).Nonempty) : m ∈ orN G C := by
  obtain ⟨t, ht⟩ := hn
  simp only [orN, gatesWhere, Finset.mem_filter, Finset.mem_range]
  refine ⟨hm, hop, ?_⟩
  intro hb
  have hv : gateVal n C m (pairInput t t) = true :=
    reach_var_val (pairInput t t) _ t (mem_orIn_reach t ht) (pairInput_left t t)
  exact G.irrefl ((graphFun_pair G t t).mp (hb _ hv))
lemma lamAvoidsUstar {m : ℕ} (hm : m ∈ lam G C)
    (hstar : ∀ a ∈ tops G C, ∀ x ∈ side (n := n) C a 0, ∀ y ∈ side C a 1, G.Adj x y) :
    ∃ t : Fin n, ∀ x ∈ orIn n C (n + m), G.Adj t x ∧ s(t, x) ∉ Ustar G C := by
  obtain ⟨_, _, _, a, ha, b, hcard, hr⟩ := Finset.mem_filter.mp hm
  have hsub : orIn n C (n + m) ⊆ side (n := n) C a b :=
    orInTrans (orReaches_reach m _ hr).1
  obtain ⟨t, ht⟩ := Finset.card_eq_one.mp hcard
  refine ⟨t, fun x hx => ?_⟩
  have hts : t ∈ side (n := n) C a (1 - b) := by simp [ht]
  have hstar' : s(t, x) ∈ starEdges G C := by
    unfold starEdges
    refine Finset.mem_biUnion.mpr ⟨a, ha, Finset.mem_image.mpr ?_⟩
    fin_cases b
    · exact ⟨(x, t), Finset.mem_product.mpr ⟨hsub hx, hts⟩, Sym2.eq_swap⟩
    · exact ⟨(t, x), Finset.mem_product.mpr ⟨hts, hsub hx⟩, rfl⟩
  refine ⟨?_, fun he => (Finset.mem_sdiff.mp he).2 hstar'⟩
  fin_cases b
  · exact (hstar a ha x (hsub hx) t hts).symm
  · exact hstar a ha t hts x (hsub hx)

lemma sideVal {a : ℕ} {b : Fin 2} {x : Fin n → Bool} {t : Fin n}
    (ht : t ∈ side (n := n) C a b) (hx : x t = true) :
    val C (List.ofFn x) (opnd C a b) = true :=
  reach_var_val x _ t (mem_orIn_reach t ht) hx

lemma andFromInputs (hAO : IsAO2 n C) {a : ℕ} (ha : a < C.gates.length)
    (hop : (gateAt C a).op = GateOp.and) {x : Fin n → Bool}
    {u v : Fin n} (hu : u ∈ side (n := n) C a 0) (hv : v ∈ side (n := n) C a 1)
    (xu : x u = true) (xv : x v = true) : gateVal n C a x = true :=
  (andValBoth hAO ha hop x).mpr ⟨sideVal hu xu, sideVal hv xv⟩

lemma topAdj (hAO : IsAO2 n C) {a : ℕ} (ha : a ∈ tops G C)
    {u v : Fin n} (hu : u ∈ side (n := n) C a 0) (hv : v ∈ side (n := n) C a 1) :
    G.Adj u v := by
  obtain ⟨hl, ho, hb⟩ := topData ha
  exact (graphFun_pair G u v).mp
    (hb _ (andFromInputs hAO hl ho hu hv (pairInput_left u v) (pairInput_right u v)))

lemma acceptedTop (hL : IsLeastAO G C) {u v : Fin n} (hadj : G.Adj u v) :
    ∃ a ∈ tops G C, gateVal n C a (pairInput u v) = true := by
  have hout (x : Fin n → Bool) : val C (List.ofFn x) C.output = graphFun G ∅ x :=
    congrFun hL.2.1 x
  obtain ⟨a, hl, ho, hr, hv⟩ :=
    edge_trace G (graphFun G ∅) (fun k l => (graphFun_pair G k l).mp)
      hout u v ((graphFun_pair G u v).mpr hadj)
  have hand := (hL.1.1 _ (gateAt_mem hl)).resolve_right ho
  have hb : BelowF G C a := fun x hx =>
    below_of_reach (graphFun G ∅) hout a hr x (gateVal_eq_val n C a x ▸ hx)
  refine ⟨a, ?_, hv⟩
  simpa only [tops, gatesWhere, Finset.mem_filter, Finset.mem_range] using
    And.intro hl (And.intro hand hb)

lemma operandSupport (hAO : IsAO2 n C) (hT : TopForm G C) {a : ℕ}
    (ha : a < C.gates.length) (ho : (gateAt C a).op = GateOp.and) {b : Fin 2}
    {u v : Fin n} (h : val C (List.ofFn (pairInput u v)) (opnd C a b) = true) :
    (∃ t ∈ side (n := n) C a b, t = u ∨ t = v) ∨
      ∃ j ∈ junk G C, OrReaches n C (opnd C a b) j ∧
        gateVal n C j (pairInput u v) = true := by
  rcases operand_trace (C := C) u v _ h with ⟨t, ht, hr⟩ | ⟨j, hj, hn, hr, hv⟩
  · exact .inl ⟨t, reach_mem_orIn t hr, ht⟩
  · have hr' := reach_orReaches hr j rfl hj
    exact .inr ⟨j, operandOrAndJunk hAO hT ha ho hr'
      ((hAO.1 _ (gateAt_mem hj)).resolve_right hn), hr', hv⟩

lemma memJunkPair {j k a : ℕ} (hs : junk G C = {j,k}) (ha : a ∈ junk G C) :
    a = j ∨ a = k := by
  simpa only [hs, Finset.mem_insert, Finset.mem_singleton] using ha

lemma mem_gammaE_of_pair {u v : Fin n} (he : s(u, v) ∈ G.edgeFinset) {j : ℕ}
    (hv : gateVal n C j (pairInput u v) = true) :
    s(u, v) ∈ gammaE G C j :=
  Finset.mem_filter.mpr ⟨he, u, v, rfl, hv⟩

end Critical.Base

namespace Critical.Patch

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm PEqualNP.Core PEqualNP.ReadTwo

lemma card_sdiff_eq {α : Type} [DecidableEq α] {A B : Finset α} (h : A ⊆ B) :
    (B \ A).card = B.card - A.card := by
  rw [Finset.card_sdiff, Finset.inter_eq_left.mpr h]


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

def patch (C : Circuit) (j : ℕ) (g : Gate) : Circuit := ⟨C.gates.set j g, C.output⟩

lemma patch_length (C : Circuit) (j : ℕ) (g : Gate) :
    (patch C j g).gates.length = C.gates.length := by
  simp [patch]

lemma gateAt_patch_ne (C : Circuit) (j k : ℕ) (g : Gate) (hne : j ≠ k) :
    gateAt (patch C j g) k = gateAt C k := by
  simp [patch, gateAt, List.getD_eq_getElem?_getD, List.getElem?_set_ne hne]

lemma gateAt_patch_eq {C : Circuit} {j : ℕ} (hj : j < C.gates.length) (g : Gate) :
    gateAt (patch C j g) j = g := by
  simp [patch, gateAt, List.getD_eq_getElem?_getD, hj]

lemma patch_wval_gate_eval {n : ℕ} {C : Circuit} {j : ℕ} {g : Gate}
    (hAO : IsAO2 n C) (x : Fin n → Bool) {k : ℕ} (hk : k < C.gates.length)
    (hne : j ≠ k) :
    wval (patch C j g) x (n + k) = (gateAt C k).op.eval
      [wval (patch C j g) x (opnd C k 0), wval (patch C j g) x (opnd C k 1)] := by
  have hk' : k < (patch C j g).gates.length := by simpa only [patch_length] using hk
  have hgate := gateAt_patch_ne C j k g hne
  have hlen : (List.ofFn x).length = n := List.length_ofFn
  have hback : ∀ w ∈ (patch C j g).gates[k].inputs, w < (List.ofFn x).length + k := by
    intro w hw
    rw [← gateAt_eq hk', hgate] at hw
    rw [hlen]
    exact hAO.2.1 k hk w hw
  have heval := foldl_wires_getD_gate (patch C j g).gates (List.ofFn x) k hk' hback
  rw [hlen, ← gateAt_eq hk', hgate, gate_inputs_eq hAO hk] at heval
  simpa only [wval, Circuit.wires, List.map_cons, List.map_nil] using heval

lemma patch_gateVal_eq_of_not_inCone {n : ℕ} {C : Circuit} {j : ℕ} {g : Gate}
    (hAO : IsAO2 n C) (k : ℕ) (hne : j ≠ k) (hCone : ¬ InCone n C j k)
    (x : Fin n → Bool) : gateVal n (patch C j g) k x = gateVal n C k x := by
  induction k using Nat.strong_induction_on with
  | ind k ih =>
    by_cases hk : k < C.gates.length
    · have hval (b : Fin 2) : wval (patch C j g) x (opnd C k b) =
          wval C x (opnd C k b) := by
        by_cases hw : opnd C k b < n
        · rw [wval_input _ _ _ hw, wval_input _ _ _ hw]
        · have hw' : n ≤ opnd C k b := by omega
          have hlt := opnd_lt hAO hk b
          have hsub_ne : j ≠ opnd C k b - n := by
            intro he
            apply hCone
            exact (inCone_iff hk).mpr ⟨opnd C k b, opnd_mem hAO hk b, hw', hlt, Or.inl he⟩
          have hsub_cone : ¬ InCone n C j (opnd C k b - n) := by
            intro he
            apply hCone
            exact (inCone_iff hk).mpr ⟨opnd C k b, opnd_mem hAO hk b, hw', hlt, Or.inr he⟩
          have hv := ih (opnd C k b - n) (by omega) hsub_ne hsub_cone
          rw [gateVal_eq_wval, gateVal_eq_wval, Nat.add_sub_of_le hw'] at hv
          exact hv
      rw [gateVal_eq_wval, gateVal_eq_wval, patch_wval_gate_eval hAO x hk hne,
        wval_gate_eval hAO x hk, hval 0, hval 1]
    · rw [gateVal_eq_wval, gateVal_eq_wval, wval_ge_len _ _ (by rw [patch_length]; omega),
        wval_ge_len _ _ (by omega)]

lemma patch_wireVal_eq_of_not_inCone {n : ℕ} {C : Circuit} {j : ℕ} {g : Gate}
    (hAO : IsAO2 n C) (w : ℕ)
    (h : n ≤ w → j ≠ w - n ∧ ¬ InCone n C j (w - n)) (x : Fin n → Bool) :
    wval (patch C j g) x w = wval C x w := by
  by_cases hw : w < n
  · rw [wval_input _ _ _ hw, wval_input _ _ _ hw]
  · have hwn : n ≤ w := by omega
    have hv := patch_gateVal_eq_of_not_inCone (g := g) hAO (w - n) (h hwn).1 (h hwn).2 x
    rw [gateVal_eq_wval, gateVal_eq_wval, Nat.add_sub_of_le hwn] at hv
    exact hv

end Critical.Patch

namespace Critical

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm

def offPatch (C : Circuit) (h : ℕ) : Circuit := ⟨C.gates.set h ⟨GateOp.or, []⟩, C.output⟩

lemma offPatch_length (C : Circuit) (h : ℕ) : (offPatch C h).gates.length = C.gates.length := by
  simp [offPatch]

lemma gateAt_offPatch_ne (C : Circuit) (h k : ℕ) (hne : h ≠ k) :
    gateAt (offPatch C h) k = gateAt C k := by
  simp [offPatch, gateAt, List.getD_eq_getElem?_getD, List.getElem?_set_ne hne]

lemma orStep_offPatch {n : ℕ} {C : Circuit} {h w w' : ℕ}
    (hAnd : (gateAt C h).op = GateOp.and) (hs : Base.OrStep n C w w') :
    Base.OrStep n (offPatch C h) w w' := by
  obtain ⟨k, hk, rfl, hOr, hi, hb⟩ := hs
  have hne : h ≠ k := by
    intro he
    rw [← he, hAnd] at hOr
    cases hOr
  refine ⟨k, by simpa only [offPatch_length] using hk, rfl, ?_, ?_, hb⟩
  · simpa only [gateAt_offPatch_ne C h k hne] using hOr
  · simpa only [gateAt_offPatch_ne C h k hne] using hi

lemma orPath_offPatch {n : ℕ} {C : Circuit} {h w w' : ℕ}
    (hAnd : (gateAt C h).op = GateOp.and)
    (hs : Relation.ReflTransGen (Base.OrStep n C) w w') :
    Relation.ReflTransGen (Base.OrStep n (offPatch C h)) w w' := by
  induction hs using Relation.ReflTransGen.head_induction_on with
  | refl => exact Relation.ReflTransGen.refl
  | head hs _ ih => exact Relation.ReflTransGen.head (orStep_offPatch hAnd hs) ih

lemma offPatch_difference_trace {n : ℕ} {C : Circuit} (hAO : IsAO2 n C)
    {h : ℕ} (hAnd : (gateAt C h).op = GateOp.and) (x : Fin n → Bool) :
    ∀ w, Base.val C (List.ofFn x) w = true → Base.val (offPatch C h) (List.ofFn x) w = false →
    ∃ j, j < C.gates.length ∧ (gateAt C j).op = GateOp.and ∧ OrReaches n C w j ∧
      gateVal n C j x = true ∧ gateVal n (offPatch C h) j x = false := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw hw'
    by_cases hwInput : w < n
    · rw [Base.val_input (n := n) (by simp) hwInput] at hw hw'
      rw [hw] at hw'
      cases hw'
    · by_cases hwLarge : n + C.gates.length ≤ w
      · rw [Base.val_ge (n := n) (by simp) hwLarge] at hw
        cases hw
      · obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
        have hk : k < C.gates.length := by omega
        by_cases hOr : (gateAt C k).op = GateOp.or
        · have hne : h ≠ k := by
            intro he
            rw [← he, hAnd] at hOr
            cases hOr
          obtain ⟨v, hvMem, hvLt, hv⟩ := (Base.val_or (n := n) (by simp) hk hOr).mp hw
          have hv' : Base.val (offPatch C h) (List.ofFn x) v = false := by
            cases hv' : Base.val (offPatch C h) (List.ofFn x) v
            · rfl
            · have hk' : k < (offPatch C h).gates.length := by simpa only [offPatch_length] using hk
              have hOr' : (gateAt (offPatch C h) k).op = GateOp.or := by
                simpa only [gateAt_offPatch_ne C h k hne] using hOr
              have hMem' : v ∈ (gateAt (offPatch C h) k).inputs := by
                simpa only [gateAt_offPatch_ne C h k hne] using hvMem
              have ht := (Base.val_or (n := n) (by simp) hk' hOr').mpr ⟨v, hMem', hvLt, hv'⟩
              rw [hw'] at ht
              cases ht
          obtain ⟨j, hj, hjAnd, hReach, hjv, hjv'⟩ := ih v hvLt hv hv'
          refine ⟨j, hj, hjAnd, ?_, hjv, hjv'⟩
          exact (Base.orReaches_iff n C k j).mpr ⟨hk, Or.inr ⟨hOr, v, hvMem, hvLt, hReach⟩⟩
        · have hAndK : (gateAt C k).op = GateOp.and := (hAO.1 _ (Base.gateAt_mem hk)).resolve_right hOr
          exact ⟨k, hk, hAndK, (Base.orReaches_iff n C k k).mpr ⟨hk, Or.inl rfl⟩, hw, hw'⟩


lemma critical_edge_useful {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {C : Circuit} (hAO : IsAO2 n C) (hF : circuitFun n C = graphFun G ∅)
    (hT : TopForm G C) {g h : ℕ} (hJ : junk G C = {g, h}) (hne : g ≠ h)
    (hIndependent : ¬ InCone n C h g)
    (hNoCommon : ∀ a ∈ tops G C, ∀ b : Fin 2,
      OrReaches n C (opnd C a b) h → ¬ OrReaches n C (opnd C a (1 - b)) g)
    (u v : Fin n) (hAdj : G.Adj u v)
    (hLost : circuitFun n (offPatch C h) (pairInput u v) = false) :
    gateVal n C h (pairInput u v) = true ∧ (u ∈ wmax G C h ∨ v ∈ wmax G C h) := by
  have hhJ : h ∈ junk G C := by rw [hJ]; simp
  obtain ⟨hhLen, hhAnd, hx, hhx, hFx⟩ := Base.junkData hhJ
  have hout (x : Fin n → Bool) : Base.val C (List.ofFn x) C.output = graphFun G ∅ x :=
    congrFun hF x
  obtain ⟨a, haLen, haNotOr, haPath, haVal⟩ :=
    Base.edge_trace G (graphFun G ∅) (fun x y hxy => (Base.graphFun_pair G x y).mp hxy)
      hout u v ((Base.graphFun_pair G u v).mpr hAdj)
  have haAnd : (gateAt C a).op = GateOp.and :=
    (hAO.1 _ (Base.gateAt_mem haLen)).resolve_right haNotOr
  have haBelow : BelowF G C a := fun x hv =>
    Base.below_of_reach (graphFun G ∅) hout a haPath x hv
  have haTop : a ∈ tops G C := by
    simpa only [tops, gatesWhere, Finset.mem_filter, Finset.mem_range] using
      And.intro haLen (And.intro haAnd haBelow)
  have hha : h ≠ a := by
    intro he
    subst a
    have ht := haBelow hx hhx
    rw [hFx] at ht
    cases ht
  have haOff : gateVal n (offPatch C h) a (pairInput u v) = false := by
    cases hc : gateVal n (offPatch C h) a (pairInput u v)
    · rfl
    · have ho := Base.orStep_up (n := n) (by simp) (orPath_offPatch hhAnd haPath) hc
      change circuitFun n (offPatch C h) (pairInput u v) = true at ho
      rw [hLost] at ho
      cases ho
  have hEval : gateVal n (offPatch C h) a (pairInput u v) =
      (Base.val (offPatch C h) (List.ofFn (pairInput u v)) (opnd C a 0) &&
       Base.val (offPatch C h) (List.ofFn (pairInput u v)) (opnd C a 1)) := by
    have he := Patch.patch_wval_gate_eval (j := h) (g := ⟨GateOp.or, []⟩) hAO (pairInput u v) haLen hha
    change gateVal n (offPatch C h) a (pairInput u v) = (gateAt C a).op.eval
      [Base.val (offPatch C h) (List.ofFn (pairInput u v)) (opnd C a 0),
       Base.val (offPatch C h) (List.ofFn (pairInput u v)) (opnd C a 1)] at he
    simpa only [haAnd, GateOp.eval, List.all_cons, List.all_nil, id_eq, Bool.and_true] using he
  obtain ⟨b, hbOff⟩ : ∃ b : Fin 2,
      Base.val (offPatch C h) (List.ofFn (pairInput u v)) (opnd C a b) = false := by
    by_cases h0 : Base.val (offPatch C h) (List.ofFn (pairInput u v)) (opnd C a 0) = false
    · exact ⟨0, h0⟩
    · have h0t := Bool.eq_true_of_not_eq_false h0
      refine ⟨1, ?_⟩
      rw [haOff, h0t, Bool.true_and] at hEval
      exact hEval.symm
  have hbVal := ((Base.andValOperands hAO haLen haAnd (pairInput u v)).mp haVal) b
  obtain ⟨j, hjLen, hjAnd, hjReach, hjVal, hjOff⟩ :=
    offPatch_difference_trace hAO hhAnd (pairInput u v) (opnd C a b) hbVal hbOff
  have hjJ := Base.operandOrAndJunk hAO hT haLen haAnd hjReach hjAnd
  have hjh : j = h := by
    rcases Base.memJunkPair hJ hjJ with hjg | hjh
    · subst j
      have he := Patch.patch_gateVal_eq_of_not_inCone (j := h) (g := ⟨GateOp.or, []⟩)
        hAO g (Ne.symm hne) hIndependent (pairInput u v)
      change gateVal n (offPatch C h) g (pairInput u v) = gateVal n C g (pairInput u v) at he
      rw [he, hjVal] at hjOff
      cases hjOff
    · exact hjh
  subst j
  refine ⟨hjVal, ?_⟩
  have hoVal := ((Base.andValOperands hAO haLen haAnd (pairInput u v)).mp haVal) (1 - b)
  rcases Base.operandSupport hAO hT haLen haAnd hoVal with ⟨t, ht, htu⟩ | ⟨k, hkJ, hkReach, _⟩
  · have htw := Base.oppositeSideWmax hAO haTop hjReach ht
    rcases htu with rfl | rfl
    · exact Or.inl htw
    · exact Or.inr htw
  · rcases Base.memJunkPair hJ hkJ with hkg | hkh
    · subst k
      exact False.elim (hNoCommon a haTop b hjReach hkReach)
    · subst k
      have ht : gateVal n C a hx = true := by
        apply (Base.andValOperands hAO haLen haAnd hx).mpr
        intro c
        rcases Base.eitherOperand b c with rfl | rfl
        · exact Base.reachVal hjReach hhx
        · exact Base.reachVal hkReach hhx
      have hf := haBelow hx ht
      rw [hFx] at hf
      cases hf

end Critical


namespace ApartFlags

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm PEqualNP.ReadTwo

lemma one_flag {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hL : IsLeastAO G C)
    (hOne : ∀ D : Circuit, IsLeastAO G D → (junk G D).card ≠ 1)
    (hT : TopForm G C) {j k : ℕ} (hne : j ≠ k) (hJ : junk G C = {j,k})
    (hjk : ¬ InCone n C j k) (hkj : ¬ InCone n C k j)
    (hNoCommon : ∀ a ∈ tops G C, ∀ b : Fin 2,
      OrReaches n C (opnd C a b) j → ¬ OrReaches n C (opnd C a (1-b)) k)
    (h4 : NoFourCycle G)
    (hdis : Disjoint (side (n := n) C j 0) (side (n := n) C j 1))
    (hP : 2 ≤ (side (n := n) C j 0).card) (hQ : 2 ≤ (side (n := n) C j 1).card) :
    ∃ z ∈ side (n := n) C j 0, ∃ zp ∈ side (n := n) C j 1,
      G.Adj z zp ∧ (∀ p ∈ side (n := n) C j 0, G.Adj p zp) ∧
        (∀ q ∈ side (n := n) C j 1, G.Adj z q) := by
  apply FlagReduction.filtered_independent_is_cross_star G C hL hOne hne hJ hjk
    (side (n := n) C j 0) (side (n := n) C j 1) h4 hdis hP hQ
  · exact RawOperands.independent_operand G C hL.1 hT j k hJ hjk hkj j (Or.inl rfl) 0
  · exact RawOperands.independent_operand G C hL.1 hT j k hJ hjk hkj j (Or.inl rfl) 1
  · intro u v huv hLost
    have hJ' : junk G C = {k,j} := by rw [hJ,Finset.pair_comm]
    obtain ⟨hjv,hFilter⟩ := Critical.critical_edge_useful hL.1 hL.2.1 hT hJ'
      (Ne.symm hne) hjk hNoCommon u v huv hLost
    have heval : ∀ x : Fin n → Bool, gateVal n C j x =
        IndependentDescent.product (side (n := n) C j 0) (side (n := n) C j 1) x :=
      RawOperands.independent_product G C hL.1 hT j k hJ hjk hkj j (Or.inl rfl)
    refine ⟨huv,(heval _).symm.trans hjv,?_⟩
    rcases hFilter with hu | hv
    · exact Or.inl ((IndependentDescent.wmax_iff G C j _ _ heval u).mp hu)
    · exact Or.inr ((IndependentDescent.wmax_iff G C j _ _ heval v).mp hv)

lemma reaches_operand_cone {n : ℕ} {C : Circuit} (hAO : IsAO2 n C)
    {a g : ℕ} (ha : a < C.gates.length) (b : Fin 2)
    (hr : OrReaches n C (opnd C a b) g) : InCone n C g a := by
  exact Critical.Base.operand_cone ha (Lift.opnd_mem hAO ha b) (Lift.opnd_lt hAO ha b)
    (Critical.Base.orReaches_reach g _ hr).1

lemma two_flags {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hL : IsLeastAO G C)
    (hOne : ∀ D : Circuit, IsLeastAO G D → (junk G D).card ≠ 1)
    (hT : TopForm G C) {g h : ℕ} (hne : g ≠ h) (hJ : junk G C = {g,h})
    (hgh : ¬ InCone n C g h) (hhg : ¬ InCone n C h g)
    (hApart : ∀ a ∈ tops G C, ¬ (InCone n C g a ∧ InCone n C h a))
    (h4 : NoFourCycle G)
    (hdis : ∀ j ∈ junk G C, Disjoint (side (n := n) C j 0) (side (n := n) C j 1))
    (hlarge : ∀ j ∈ junk G C, ∀ b : Fin 2, 2 ≤ (side (n := n) C j b).card) :
    ∀ j ∈ junk G C, ∃ (P Q : Finset (Fin n)) (z zp : Fin n),
      G.Adj z zp ∧ z ∈ P ∧ zp ∈ Q ∧ (∀ p ∈ P, G.Adj p zp) ∧
      (∀ q ∈ Q, G.Adj q z) ∧ 2 ≤ P.card ∧ 2 ≤ Q.card ∧
      ∀ x : Fin n → Bool, gateVal n C j x =
        (decide (∃ p ∈ P, x p = true) && decide (∃ q ∈ Q, x q = true)) := by
  classical
  have hFlag (j k : ℕ) (hne' : j ≠ k) (hJ' : junk G C = {j,k})
      (hjk : ¬ InCone n C j k) (hkj : ¬ InCone n C k j)
      (hApart' : ∀ a ∈ tops G C, ¬ (InCone n C j a ∧ InCone n C k a)) :
      ∃ z ∈ side (n := n) C j 0, ∃ zp ∈ side (n := n) C j 1,
        G.Adj z zp ∧ (∀ p ∈ side (n := n) C j 0, G.Adj p zp) ∧
          (∀ q ∈ side (n := n) C j 1, G.Adj z q) := by
    have hjmem : j ∈ junk G C := by rw [hJ']; simp
    apply one_flag G C hL hOne hT hne' hJ' hjk hkj ?_ h4
      (hdis j hjmem) (hlarge j hjmem 0) (hlarge j hjmem 1)
    intro a ha b hjr hkr
    have hal : a < C.gates.length := (Critical.Base.topData ha).1
    exact hApart' a ha ⟨reaches_operand_cone hL.1 hal b hjr,
      reaches_operand_cone hL.1 hal (1-b) hkr⟩
  intro j hj
  have hjcases : j = g ∨ j = h := by simpa [hJ] using hj
  have heval := RawOperands.independent_product G C hL.1 hT g h hJ hgh hhg j hjcases
  have hz : ∃ z ∈ side (n := n) C j 0, ∃ zp ∈ side (n := n) C j 1,
      G.Adj z zp ∧ (∀ p ∈ side (n := n) C j 0, G.Adj p zp) ∧
        (∀ q ∈ side (n := n) C j 1, G.Adj z q) := by
    rcases hjcases with hjg | hjh
    · rw [hjg]
      exact hFlag g h hne hJ hgh hhg hApart
    · rw [hjh]
      exact hFlag h g (Ne.symm hne) (by rw [hJ,Finset.pair_comm]) hhg hgh
        (fun a ha hh => hApart a ha hh.symm)
  obtain ⟨z,hz,zp,hzp,hzzp,hP,hQ⟩ := hz
  exact ⟨side (n := n) C j 0,side (n := n) C j 1,z,zp,hzzp,hz,hzp,hP,
    fun q hq => (hQ q hq).symm,hlarge j hj 0,hlarge j hj 1,heval⟩

end ApartFlags

end PEqualNP.Outside.L_meta_5012
