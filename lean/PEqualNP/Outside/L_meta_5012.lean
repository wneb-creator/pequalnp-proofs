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

end PEqualNP.Outside.L_meta_5012
