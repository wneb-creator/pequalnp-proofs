import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_18219

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.TopForm PEqualNP.BlindGate

private def stepWire (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i Bool.false)]

private lemma foldl_step_len (gs : List Gate) (init : List Bool) :
    (gs.foldl stepWire init).length = init.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp
  | append_singleton gs g ih =>
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil, stepWire]
    simp [ih]
    omega

private lemma foldl_step_getD_lt (gs : List Gate) (init : List Bool) (w : ℕ) (hw : w < init.length) :
    (gs.foldl stepWire init).getD w Bool.false = init.getD w Bool.false := by
  induction gs using List.reverseRecOn with
  | nil => rfl
  | append_singleton gs g ih =>
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil, stepWire]
    have hlen : w < (gs.foldl stepWire init).length := by rw [foldl_step_len]; omega
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_left hlen, ← List.getD_eq_getElem?_getD]
    exact ih

private lemma wires_eq_foldl (C : Circuit) (inp : List Bool) :
    C.wires inp = C.gates.foldl stepWire inp := rfl

private lemma wires_len (C : Circuit) (inp : List Bool) :
    (C.wires inp).length = inp.length + C.gates.length :=
  foldl_step_len C.gates inp

private lemma wires_getD_input (C : Circuit) (inp : List Bool) (w : ℕ) (hw : w < inp.length) :
    (C.wires inp).getD w Bool.false = inp.getD w Bool.false :=
  foldl_step_getD_lt C.gates inp w hw

private lemma wires_getD_gate (C : Circuit) (inp : List Bool) (j : ℕ) (hj : j < C.gates.length) :
    (C.wires inp).getD (inp.length + j) Bool.false =
      (C.gates[j]).op.eval ((C.gates[j]).inputs.map fun i =>
        ((C.gates.take j).foldl stepWire inp).getD i Bool.false) := by
  have hsplit : C.gates = C.gates.take j ++ [C.gates[j]] ++ C.gates.drop (j + 1) := by
    calc C.gates = C.gates.take j ++ C.gates.drop j := (List.take_append_drop j C.gates).symm
      _ = C.gates.take j ++ (C.gates[j] :: C.gates.drop (j + 1)) := by rw [List.drop_eq_getElem_cons hj]
      _ = C.gates.take j ++ [C.gates[j]] ++ C.gates.drop (j + 1) := by simp
  rw [wires_eq_foldl]
  conv_lhs => rw [hsplit]
  rw [List.foldl_append, List.foldl_append, List.foldl_cons, List.foldl_nil]
  set pref := (C.gates.take j).foldl stepWire inp
  have hplen : pref.length = inp.length + j := by
    simp only [pref, foldl_step_len, List.length_take]
    omega
  have hlt : inp.length + j < (stepWire pref C.gates[j]).length := by
    simp only [stepWire, List.length_append, List.length_singleton, hplen]; omega
  rw [foldl_step_getD_lt _ _ _ hlt]
  simp only [stepWire, List.getD_eq_getElem?_getD]
  rw [← hplen, List.getElem?_append_right (le_refl _)]
  simp

private lemma wires_getD_take_eq (C : Circuit) (inp : List Bool) (j i : ℕ)
    (hj : j ≤ C.gates.length) (hi : i < inp.length + j) :
    ((C.gates.take j).foldl stepWire inp).getD i Bool.false =
      (C.wires inp).getD i Bool.false := by
  have hsplit : C.gates = C.gates.take j ++ C.gates.drop j := (List.take_append_drop j C.gates).symm
  rw [wires_eq_foldl]
  conv_rhs => rw [hsplit]
  rw [List.foldl_append]
  have hplen : ((C.gates.take j).foldl stepWire inp).length = inp.length + j := by
    rw [foldl_step_len, List.length_take]; omega
  exact (foldl_step_getD_lt (C.gates.drop j) ((C.gates.take j).foldl stepWire inp) i (by omega)).symm

private lemma wires_getD_gate_full (C : Circuit) (inp : List Bool) (j : ℕ) (hj : j < C.gates.length)
    (hrb : ∀ i ∈ (C.gates[j]).inputs, i < inp.length + j) :
    (C.wires inp).getD (inp.length + j) Bool.false =
      (C.gates[j]).op.eval ((C.gates[j]).inputs.map fun i => (C.wires inp).getD i Bool.false) := by
  rw [wires_getD_gate C inp j hj]
  congr 1
  apply List.map_congr_left
  intro i hi
  exact wires_getD_take_eq C inp j i (le_of_lt hj) (hrb i hi)

private lemma wires_getD_ge (C : Circuit) (inp : List Bool) (w : ℕ)
    (hw : inp.length + C.gates.length ≤ w) :
    (C.wires inp).getD w Bool.false = Bool.false := by
  rw [List.getD_eq_getElem?_getD]
  have hlen : (C.wires inp).length ≤ w := by rw [wires_len]; exact hw
  rw [List.getElem?_eq_none hlen]
  rfl

private lemma getD_append_last (l : List Bool) (b : Bool) :
    (l ++ [b]).getD l.length Bool.false = b := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (le_refl _)]
  simp

private lemma isAO2_gate_props {n : ℕ} {C : Circuit} (hAO : IsAO2 n C)
    (j : ℕ) (hj : j < C.gates.length) :
    ((C.gates[j]).op = GateOp.and ∨ (C.gates[j]).op = GateOp.or) ∧
    (∃ a b : ℕ, (C.gates[j]).inputs = [a, b] ∧ a < n + j ∧ b < n + j) := by
  rcases hAO with ⟨hao, hrb, hlen⟩
  have hmem : C.gates[j] ∈ C.gates := List.getElem_mem hj
  have hop := hao C.gates[j] hmem
  have hl := hlen C.gates[j] hmem
  have hgat : gateAt C j = C.gates[j] := by simp [gateAt, List.getD_eq_getElem?_getD, hj]
  have hrbj := hrb j hj
  rw [hgat] at hrbj
  match hins : (C.gates[j]).inputs with
  | [a, b] =>
    exact ⟨hop, a, b, rfl, hrbj a (by simp [hins]), hrbj b (by simp [hins])⟩
  | [] => simp [hins] at hl
  | [_] => simp [hins] at hl
  | _ :: _ :: _ :: _ => simp [hins] at hl

private lemma build_prefix (n : ℕ) (v : Fin n) (C : Circuit) (S : Finset ℕ)
    (hAO : IsAO2 n C)
    (hS : ∀ j ∈ S, j < C.gates.length ∧ ∃ w < n + j,
      ∀ x : Fin n → Bool, x v = Bool.false →
        (C.wires (List.ofFn x)).getD (n + j) Bool.false =
        (C.wires (List.ofFn x)).getD w Bool.false) :
    ∀ k : ℕ, k ≤ C.gates.length →
      ∃ (gs : List Gate) (rep : ℕ → ℕ),
        (∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2) ∧
        (∀ (j : ℕ) (hj : j < gs.length), ∀ i ∈ (gs[j]'hj).inputs, i < n + j) ∧
        gs.length + (S.filter (· < k)).card ≤ k ∧
        (∀ w < n + k, rep w < n + gs.length ∧ ∀ x : Fin n → Bool, x v = Bool.false →
          (gs.foldl stepWire (List.ofFn x)).getD (rep w) Bool.false =
          (C.wires (List.ofFn x)).getD w Bool.false) := by
  intro k
  induction k with
  | zero =>
    intro _
    refine ⟨[], id, ?_, ?_, ?_, ?_⟩
    · intro g hg; cases hg
    · intro j hj; exact absurd hj (Nat.not_lt_zero _)
    · simp
    · intro w hw
      have hwn : w < n := by omega
      refine ⟨by simpa using hwn, fun x _ => ?_⟩
      rw [List.foldl_nil, id]
      exact (wires_getD_input C (List.ofFn x) w (by rw [List.length_ofFn]; exact hwn)).symm
  | succ k ih =>
    intro hk_le
    have hk_lt : k < C.gates.length := by omega
    obtain ⟨gs, rep, hgs_ao, hgs_rb, hgs_len, hrep⟩ := ih (Nat.le_of_lt hk_lt)
    have hfilt_eq : (S.filter (· < k + 1)).card =
        (S.filter (· < k)).card + (if k ∈ S then 1 else 0) := by
      by_cases hkS : k ∈ S
      · have hsub : S.filter (· < k + 1) = insert k (S.filter (· < k)) := by
          ext u; simp only [Finset.mem_filter, Finset.mem_insert]; constructor
          · rintro ⟨huS, hu⟩
            by_cases huk : u = k
            · left; exact huk
            · right; exact ⟨huS, by omega⟩
          · rintro (rfl | ⟨huS, hu⟩)
            · exact ⟨hkS, by omega⟩
            · exact ⟨huS, by omega⟩
        rw [hsub, Finset.card_insert_of_notMem (by simp), ite_eq_left hkS]
      · have hsub : S.filter (· < k + 1) = S.filter (· < k) := by
          ext u; simp only [Finset.mem_filter]; constructor
          · rintro ⟨huS, hu⟩
            have huk : u ≠ k := fun h => hkS (h ▸ huS)
            exact ⟨huS, by omega⟩
          · rintro ⟨huS, hu⟩; exact ⟨huS, by omega⟩
        rw [hsub, ite_eq_right hkS]; omega
    by_cases hkS : k ∈ S
    · obtain ⟨_, w0, hw0_lt, hw0_eq⟩ := hS k hkS
      let rep' : ℕ → ℕ := fun w => if w = n + k then rep w0 else rep w
      refine ⟨gs, rep', hgs_ao, hgs_rb, ?_, ?_⟩
      · rw [hfilt_eq, ite_eq_left hkS]; omega
      · intro w hw
        by_cases hwk : w = n + k
        · subst hwk
          simp only [rep', ↓reduceIte]
          have h0 := hrep w0 hw0_lt
          exact ⟨h0.1, fun x hxv => by rw [hw0_eq x hxv, h0.2 x hxv]⟩
        · simp only [rep', hwk, ↓reduceIte]
          exact hrep w (by omega)
    · obtain ⟨hop, a, b, hins, ha_lt, hb_lt⟩ := isAO2_gate_props hAO k hk_lt
      have ha_spec := hrep a ha_lt
      have hb_spec := hrep b hb_lt
      let gnew : Gate := ⟨(C.gates[k]).op, [rep a, rep b]⟩
      let gs' := gs ++ [gnew]
      let rep' : ℕ → ℕ := fun w => if w = n + k then n + gs.length else rep w
      refine ⟨gs', rep', ?_, ?_, ?_, ?_⟩
      · intro g hg
        simp only [gs', List.mem_append, List.mem_singleton] at hg
        rcases hg with hg | rfl
        · exact hgs_ao g hg
        · exact ⟨hop, rfl⟩
      · intro j hj i hi
        by_cases hjl : j < gs.length
        · have hget : gs'[j]'hj = gs[j]'hjl := List.getElem_append_left hjl
          rw [hget] at hi
          exact hgs_rb j hjl i hi
        · have hjeq : j = gs.length := by
            simp only [gs', List.length_append, List.length_singleton] at hj; omega
          subst hjeq
          have hget : gs'[gs.length]'hj = gnew := by simp [gs']
          rw [hget] at hi
          simp only [gnew, List.mem_cons, List.not_mem_nil, or_false] at hi
          rcases hi with rfl | rfl
          · exact ha_spec.1
          · exact hb_spec.1
      · simp only [gs', List.length_append, List.length_singleton]
        rw [hfilt_eq, ite_eq_right hkS]; omega
      · intro w hw
        by_cases hwk : w = n + k
        · subst hwk
          simp only [rep', ↓reduceIte]
          refine ⟨by simp [gs'], fun x hxv => ?_⟩
          have hlen_ofFn : (List.ofFn x).length = n := List.length_ofFn
          have hrbk : ∀ i ∈ (C.gates[k]).inputs, i < (List.ofFn x).length + k := by
            rw [hlen_ofFn, hins]
            intro i hi
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
            rcases hi with rfl | rfl <;> assumption
          have hgate := wires_getD_gate_full C (List.ofFn x) k hk_lt hrbk
          rw [hlen_ofFn, hins] at hgate
          rw [hgate]
          simp only [gs', List.foldl_append, List.foldl_cons, List.foldl_nil, stepWire]
          have hplen : (gs.foldl stepWire (List.ofFn x)).length = n + gs.length := by
            rw [foldl_step_len, List.length_ofFn]
          rw [← hplen, getD_append_last]
          simp only [gnew, List.map_cons, List.map_nil]
          rw [ha_spec.2 x hxv, hb_spec.2 x hxv]
        · simp only [rep', hwk, ↓reduceIte]
          have hw0 := hrep w (by omega)
          refine ⟨by simp only [gs', List.length_append, List.length_singleton]; omega, fun x hxv => ?_⟩
          simp only [gs', List.foldl_append, List.foldl_cons, List.foldl_nil, stepWire]
          have hplen : rep w < (gs.foldl stepWire (List.ofFn x)).length := by
            rw [foldl_step_len, List.length_ofFn]; exact hw0.1
          rw [List.getD_eq_getElem?_getD, List.getElem?_append_left hplen, ← List.getD_eq_getElem?_getD]
          exact hw0.2 x hxv

theorem main : ∀ (x1 : ℕ) (x2 : Fin x1) (x3 : PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.TopForm.IsAO2 x1 x3 →     have x5 : Finset (Fin x3.size) := {x5 : Fin x3.size | ∃ (x6 : Fin (x1 + ↑x5)), ∀ (x7 : Fin x1 → Bool), x7 x2 = Bool.false → PEqualNP.BlindGate.wireValue x3 x1 x7 (x1 + ↑x5) = PEqualNP.BlindGate.wireValue x3 x1 x7 ↑x6};     ∃ (x6 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 x1 x6 ∧ x6.size + x5.card ≤ x3.size ∧ ∀ (x7 : Fin x1 → Bool), x7 x2 = Bool.false → x6.eval (List.ofFn x7) = x3.eval (List.ofFn x7) := by
  intro n v C hAO
  dsimp only
  let x5set : Finset (Fin C.size) :=
    Finset.univ.filter fun j : Fin C.size =>
      ∃ w : Fin (n + j.val), ∀ x : Fin n → Bool, x v = Bool.false →
        wireValue C n x (n + j.val) = wireValue C n x w.val
  let S : Finset ℕ := x5set.image Fin.val
  have hS_card : S.card = x5set.card := Finset.card_image_of_injective x5set Fin.val_injective
  have hS : ∀ j ∈ S, j < C.gates.length ∧ ∃ w < n + j,
      ∀ x : Fin n → Bool, x v = Bool.false →
        (C.wires (List.ofFn x)).getD (n + j) Bool.false =
        (C.wires (List.ofFn x)).getD w Bool.false := by
    intro j hj
    rcases Finset.mem_image.mp hj with ⟨j', hj', rfl⟩
    have hj'f := (Finset.mem_filter.mp hj').2
    rcases hj'f with ⟨w, hw⟩
    exact ⟨j'.isLt, w.val, w.isLt, fun x hxv => hw x hxv⟩
  obtain ⟨gs, rep, hgs_ao, hgs_rb, hgs_len, hrep⟩ := build_prefix n v C S hAO hS C.gates.length (le_refl _)
  have hS_filt : S.filter (· < C.gates.length) = S := by
    ext j
    simp only [Finset.mem_filter, and_iff_left_iff_imp]
    intro hj
    exact (hS j hj).1
  rw [hS_filt, hS_card] at hgs_len
  let out' : ℕ := if C.output < n + C.gates.length then rep C.output else n + gs.length
  let D : Circuit := ⟨gs, out'⟩
  refine ⟨D, ?_, hgs_len, ?_⟩
  · refine ⟨?_, ?_, ?_⟩
    · intro g hg; exact (hgs_ao g hg).1
    · intro j hj i hi
      have hgat : gateAt D j = gs[j]'hj := by
        change gs.getD j ⟨GateOp.or, []⟩ = gs[j]'hj
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]
        rfl
      rw [hgat] at hi
      exact hgs_rb j hj i hi
    · intro g hg; exact (hgs_ao g hg).2
  · intro x hxv
    by_cases hout : C.output < n + C.gates.length
    · change (gs.foldl stepWire (List.ofFn x)).getD out' Bool.false =
        (C.wires (List.ofFn x)).getD C.output Bool.false
      simp only [out', ite_eq_left hout]
      exact (hrep C.output hout).2 x hxv
    · have hge : n + C.gates.length ≤ C.output := Nat.not_lt.mp hout
      change (D.wires (List.ofFn x)).getD out' Bool.false =
        (C.wires (List.ofFn x)).getD C.output Bool.false
      simp only [out', ite_eq_right hout]
      have hL : (D.wires (List.ofFn x)).getD (n + gs.length) Bool.false = Bool.false :=
        wires_getD_ge D (List.ofFn x) (n + gs.length) (by rw [List.length_ofFn])
      have hR : (C.wires (List.ofFn x)).getD C.output Bool.false = Bool.false :=
        wires_getD_ge C (List.ofFn x) C.output (by rw [List.length_ofFn]; exact hge)
      exact hL.trans hR.symm

end PEqualNP.Outside.L_meta_18219

theorem PEqualNP.Outside.L_meta_18219 : ∀ (x1 : ℕ) (x2 : Fin x1) (x3 : PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.TopForm.IsAO2 x1 x3 →     have x5 : Finset (Fin x3.size) := {x5 : Fin x3.size | ∃ (x6 : Fin (x1 + ↑x5)), ∀ (x7 : Fin x1 → Bool), x7 x2 = Bool.false → PEqualNP.BlindGate.wireValue x3 x1 x7 (x1 + ↑x5) = PEqualNP.BlindGate.wireValue x3 x1 x7 ↑x6};     ∃ (x6 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 x1 x6 ∧ x6.size + x5.card ≤ x3.size ∧ ∀ (x7 : Fin x1 → Bool), x7 x2 = Bool.false → x6.eval (List.ofFn x7) = x3.eval (List.ofFn x7) := PEqualNP.Outside.L_meta_18219.main
