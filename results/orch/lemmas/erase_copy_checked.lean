import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3451

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover

def edStepWire (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def edRunWires (gs : List Gate) (init : List Bool) : List Bool :=
  gs.foldl edStepWire init

lemma edGetD_append_singleton (w : List Bool) (b : Bool) (i : ℕ) :
    (w ++ [b]).getD i false =
      if i < w.length then w.getD i false
      else if i = w.length then b
      else false := by
  simp only [List.getD_eq_getElem?_getD]
  by_cases h1 : i < w.length
  · rw [ite_eq_left h1, List.getElem?_append_left h1]
  · rw [ite_eq_right h1]
    by_cases h2 : i = w.length
    · subst h2
      rw [ite_eq_left rfl, List.getElem?_append_right (le_refl _)]
      simp
    · rw [ite_eq_right h2, List.getElem?_eq_none]
      · rfl
      · simp only [List.length_append, List.length_singleton]
        omega

lemma edGetD_of_ge (w : List Bool) (i : ℕ) (h : w.length ≤ i) :
    w.getD i false = false := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]
  rfl

lemma edRunWires_len (gs : List Gate) (init : List Bool) :
    (edRunWires gs init).length = init.length + gs.length := by
  induction gs generalizing init with
  | nil => simp [edRunWires]
  | cons g gs ih =>
    change (edRunWires gs (edStepWire init g)).length = init.length + (gs.length + 1)
    rw [ih, edStepWire, List.length_append, List.length_singleton]
    omega

lemma edRunWires_getD_prefix (gs : List Gate) (init : List Bool) (i : ℕ)
    (hi : i < init.length) :
    (edRunWires gs init).getD i false = init.getD i false := by
  induction gs generalizing init with
  | nil => rfl
  | cons g gs ih =>
    change (edRunWires gs (edStepWire init g)).getD i false = init.getD i false
    have hlt : i < (edStepWire init g).length := by
      simp only [edStepWire, List.length_append, List.length_singleton]
      omega
    rw [ih (edStepWire init g) hlt, edStepWire, edGetD_append_singleton, ite_eq_left hi]

lemma edRunWires_getD_gate (gs : List Gate) (init : List Bool) (j : ℕ)
    (hj : j < gs.length) :
    (edRunWires gs init).getD (init.length + j) false =
      (gs[j]).op.eval
        ((gs[j]).inputs.map fun i =>
          if i < init.length + j then (edRunWires gs init).getD i false else false) := by
  induction gs generalizing init j with
  | nil => simp at hj
  | cons g gs ih =>
    cases j with
    | zero =>
      change (edRunWires gs (edStepWire init g)).getD (init.length + 0) false =
        g.op.eval (g.inputs.map fun i =>
          if i < init.length + 0 then (edRunWires gs (edStepWire init g)).getD i false else false)
      have hlen : init.length < (edStepWire init g).length := by
        simp only [edStepWire, List.length_append, List.length_singleton]
        omega
      rw [Nat.add_zero, edRunWires_getD_prefix gs (edStepWire init g) init.length hlen]
      have hhead : (edStepWire init g).getD init.length false =
          g.op.eval (g.inputs.map fun i => init.getD i false) := by
        rw [edStepWire, edGetD_append_singleton, ite_eq_right (lt_irrefl _), ite_eq_left rfl]
      rw [hhead]
      congr 1
      apply List.map_congr_left
      intro i _
      by_cases hi : i < init.length
      · rw [ite_eq_left hi]
        have hi' : i < (edStepWire init g).length := by
          simp only [edStepWire, List.length_append, List.length_singleton]
          omega
        rw [edRunWires_getD_prefix gs (edStepWire init g) i hi', edStepWire,
          edGetD_append_singleton, ite_eq_left hi]
      · rw [ite_eq_right hi, edGetD_of_ge init i (not_lt.mp hi)]
    | succ k =>
      have hk : k < gs.length := by simpa using hj
      have hidx : init.length + (k + 1) = (edStepWire init g).length + k := by
        simp only [edStepWire, List.length_append, List.length_singleton]
        omega
      change (edRunWires gs (edStepWire init g)).getD (init.length + (k + 1)) false =
        (gs[k]).op.eval ((gs[k]).inputs.map fun i =>
          if i < init.length + (k + 1) then (edRunWires gs (edStepWire init g)).getD i false else false)
      rw [hidx]
      exact ih (edStepWire init g) k hk

def edWireVal {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ) : Bool :=
  (C.wires (List.ofFn x)).getD w false

lemma edWireVal_input {n : ℕ} (C : Circuit) (x : Fin n → Bool) (i : ℕ) (hi : i < n) :
    edWireVal C x i = x ⟨i, hi⟩ := by
  unfold edWireVal
  change (edRunWires C.gates (List.ofFn x)).getD i false = x ⟨i, hi⟩
  rw [edRunWires_getD_prefix C.gates (List.ofFn x) i (by simp [hi])]
  rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
  simp [hi]

lemma edWireVal_gate {n : ℕ} (C : Circuit) (x : Fin n → Bool) (j : ℕ)
    (hj : j < C.gates.length) :
    edWireVal C x (n + j) =
      (C.gates[j]).op.eval ((C.gates[j]).inputs.map fun i =>
        if i < n + j then edWireVal C x i else false) := by
  unfold edWireVal
  have h := edRunWires_getD_gate C.gates (List.ofFn x) j hj
  have hlen : (List.ofFn x).length = n := List.length_ofFn
  rw [hlen] at h
  exact h

lemma edWireVal_ge {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ)
    (hw : n + C.gates.length ≤ w) : edWireVal C x w = false := by
  unfold edWireVal
  apply edGetD_of_ge
  change (edRunWires C.gates (List.ofFn x)).length ≤ w
  rw [edRunWires_len, List.length_ofFn]
  exact hw

def edShiftIdx (cut rep i : ℕ) : ℕ :=
  if i < cut then i else if i = cut then rep else i - 1

lemma edShiftIdx_lt (cut rep i : ℕ) (h : i < cut) : edShiftIdx cut rep i = i := by
  unfold edShiftIdx; exact ite_eq_left h

lemma edShiftIdx_eq (cut rep : ℕ) : edShiftIdx cut rep cut = rep := by
  unfold edShiftIdx; rw [ite_eq_right (lt_irrefl _), ite_eq_left rfl]

lemma edShiftIdx_gt (cut rep i : ℕ) (h : ¬i < cut) (hne : i ≠ cut) :
    edShiftIdx cut rep i = i - 1 := by
  unfold edShiftIdx; rw [ite_eq_right h, ite_eq_right hne]

def edDelete (n : ℕ) (C : Circuit) (j rep : ℕ) : Circuit :=
  ⟨C.gates.take j ++ (C.gates.drop (j + 1)).map
      (fun g => ⟨g.op, g.inputs.map (edShiftIdx (n + j) rep)⟩),
    edShiftIdx (n + j) rep C.output⟩

lemma edDelete_wires {n : ℕ} (C : Circuit)
    (j : ℕ) (hj : j < C.gates.length) (rep : ℕ)
    (hrep : rep < n + j ∨ rep = n + C.gates.length)
    (heq : ∀ x : Fin n → Bool, edWireVal C x (n + j) = edWireVal C x rep) :
    ∀ (x : Fin n → Bool) (w : ℕ),
      edWireVal (edDelete n C j rep) x (edShiftIdx (n + j) rep w) = edWireVal C x w := by
  let gs' : List Gate :=
    C.gates.take j ++ (C.gates.drop (j + 1)).map fun g =>
      ⟨g.op, g.inputs.map (edShiftIdx (n + j) rep)⟩
  let C' : Circuit := ⟨gs', edShiftIdx (n + j) rep C.output⟩
  have hlen_take : (C.gates.take j).length = j := List.length_take_of_le (le_of_lt hj)
  have hlen' : C'.gates.length = C.gates.length - 1 := by
    simp [C', gs', hlen_take]
    omega
  have hagree : ∀ (x : Fin n → Bool) (w : ℕ),
      (w < n + j → edWireVal C' x w = edWireVal C x w) ∧
      (∀ k < C.gates.length - (j + 1), w = n + j + k → edWireVal C' x w = edWireVal C x (n + j + 1 + k)) := by
    intro x w
    induction w using Nat.strong_induction_on with
    | ind w ih =>
      constructor
      · intro hlt
        by_cases hlt_n : w < n
        · rw [edWireVal_input C' x w hlt_n, edWireVal_input C x w hlt_n]
        · have hj1 : w - n < j := by omega
          have hj1' : w - n < C'.gates.length := by omega
          have hj1c : w - n < C.gates.length := by omega
          have hw_eq : n + (w - n) = w := by omega
          rw [← hw_eq, edWireVal_gate C' x (w - n) hj1', edWireVal_gate C x (w - n) hj1c]
          have hg_eq : C'.gates[w - n] = C.gates[w - n] := by
            simp only [C', gs']
            rw [List.getElem_append_left (by rw [hlen_take]; exact hj1)]
            simp
          rw [hg_eq]
          congr 1
          apply List.map_congr_left
          intro i _
          by_cases hil : i < n + (w - n)
          · rw [ite_eq_left hil, ite_eq_left hil]
            exact (ih i (by omega)).1 (by omega)
          · rw [ite_eq_right hil, ite_eq_right hil]
      · intro k hk hw
        subst hw
        have hk' : j + k < C'.gates.length := by omega
        have hkc : j + 1 + k < C.gates.length := by omega
        have hidx1 : n + (j + k) = n + j + k := by omega
        have hidx2 : n + (j + 1 + k) = n + j + 1 + k := by omega
        rw [← hidx1, ← hidx2, edWireVal_gate C' x (j + k) hk', edWireVal_gate C x (j + 1 + k) hkc]
        have hg_eq : C'.gates[j + k] =
            ⟨(C.gates[j + 1 + k]).op, (C.gates[j + 1 + k]).inputs.map (edShiftIdx (n + j) rep)⟩ := by
          simp only [C', gs']
          rw [List.getElem_append_right (by rw [hlen_take]; omega)]
          simp only [hlen_take, Nat.add_sub_cancel_left, List.getElem_map, List.getElem_drop]
        rw [hg_eq, List.map_map]
        congr 1
        apply List.map_congr_left
        intro i _
        simp only [Function.comp_apply]
        by_cases h1 : i < n + j
        · simp only [edShiftIdx_lt _ _ _ h1]
          rw [ite_eq_left (by omega), ite_eq_left (by omega)]
          exact (ih i (by omega)).1 h1
        · by_cases h2 : i = n + j
          · subst h2
            simp only [edShiftIdx_eq]
            rw [ite_eq_left (show n + j < n + (j + 1 + k) by omega), heq x]
            rcases hrep with hrl | hre
            · rw [ite_eq_left (by omega)]
              exact (ih rep (by omega)).1 hrl
            · rw [hre, ite_eq_right (by omega), edWireVal_ge C x (n + C.gates.length) (le_refl _)]
          · simp only [edShiftIdx_gt _ _ _ h1 h2]
            by_cases h3 : i < n + (j + 1 + k)
            · rw [ite_eq_left (by omega), ite_eq_left h3]
              have h4 := (ih (i - 1) (by omega)).2 (i - 1 - (n + j)) (by omega) (by omega)
              have h5 : n + j + 1 + (i - 1 - (n + j)) = i := by omega
              rw [h5] at h4
              exact h4
            · rw [ite_eq_right (by omega), ite_eq_right h3]
  intro x w
  change edWireVal C' x (edShiftIdx (n + j) rep w) = edWireVal C x w
  simp only [edShiftIdx]
  by_cases h1 : w < n + j
  · rw [ite_eq_left h1]
    exact (hagree x w).1 h1
  · rw [ite_eq_right h1]
    by_cases h2 : w = n + j
    · rw [ite_eq_left h2, h2, heq x]
      rcases hrep with hrl | hre
      · exact (hagree x rep).1 hrl
      · rw [hre, edWireVal_ge C' x (n + C.gates.length) (by omega),
            edWireVal_ge C x (n + C.gates.length) (le_refl _)]
    · rw [ite_eq_right h2]
      by_cases h3 : w < n + C.gates.length
      · have h4 := (hagree x (w - 1)).2 (w - 1 - (n + j)) (by omega) (by omega)
        have h5 : n + j + 1 + (w - 1 - (n + j)) = w := by omega
        rw [h5] at h4
        exact h4
      · rw [edWireVal_ge C' x (w - 1) (by omega), edWireVal_ge C x w (by omega)]

lemma edDelete_size (n : ℕ) (C : Circuit) (j rep : ℕ) (hj : j < C.gates.length) :
    (edDelete n C j rep).size + 1 = C.size := by
  simp only [edDelete, Circuit.size, List.length_append, List.length_take,
    List.length_map, List.length_drop]
  omega

lemma edDelete_monotone (n : ℕ) (C : Circuit) (j rep : ℕ) (hm : Monotone2 C) :
    Monotone2 (edDelete n C j rep) := by
  intro g hg
  simp only [edDelete, List.mem_append, List.mem_map] at hg
  rcases hg with h | ⟨g₀, h, rfl⟩
  · exact hm g (List.mem_of_mem_take h)
  · obtain ⟨hop, hlen⟩ := hm g₀ (List.mem_of_mem_drop h)
    exact ⟨hop, by simpa using hlen⟩

lemma edDelete_before (n : ℕ) (C : Circuit) (j rep k : ℕ)
    (hj : j < C.gates.length) (hk : k < j) :
    gateAt (edDelete n C j rep) k = gateAt C k := by
  have hlen := edDelete_size n C j rep hj
  have hd : k < (edDelete n C j rep).gates.length := by
    change (edDelete n C j rep).gates.length + 1 = C.gates.length at hlen
    omega
  unfold gateAt
  rw [List.getD_eq_getElem _ _ hd, List.getD_eq_getElem _ _ (by omega)]
  simp only [edDelete]
  rw [List.getElem_append_left (by simp; omega)]
  simp

lemma edDelete_after (n : ℕ) (C : Circuit) (j rep k : ℕ)
    (hj : j < C.gates.length) (hk : k < (edDelete n C j rep).gates.length)
    (hjk : j ≤ k) :
    gateAt (edDelete n C j rep) k =
      ⟨(gateAt C (k + 1)).op, (gateAt C (k + 1)).inputs.map (edShiftIdx (n + j) rep)⟩ := by
  have hlen := edDelete_size n C j rep hj
  change (edDelete n C j rep).gates.length + 1 = C.gates.length at hlen
  have hold : k + 1 < C.gates.length := by omega
  have ht : (C.gates.take j).length = j := List.length_take_of_le (by omega)
  unfold gateAt
  rw [List.getD_eq_getElem _ _ hk, List.getD_eq_getElem _ _ hold]
  simp only [edDelete]
  rw [List.getElem_append_right (by omega)]
  simp only [ht, List.getElem_map, List.getElem_drop]
  have hi : j + 1 + (k - j) = k + 1 := by omega
  simp only [hi]

lemma edDelete_readsBack (n : ℕ) (C : Circuit) (j rep : ℕ)
    (hj : j < C.gates.length) (hrep : rep < n + j) (hr : ReadsBack n C) :
    ReadsBack n (edDelete n C j rep) := by
  intro k hk i hi
  by_cases hkj : k < j
  · rw [edDelete_before n C j rep k hj hkj] at hi
    exact hr k (by omega) i hi
  · rw [edDelete_after n C j rep k hj hk (by omega)] at hi
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hi
    have hlen := edDelete_size n C j rep hj
    change (edDelete n C j rep).gates.length + 1 = C.gates.length at hlen
    have ha' := hr (k + 1) (by omega) a ha
    unfold edShiftIdx
    split_ifs <;> omega

lemma edDelete_eval {n : ℕ} (C : Circuit) (j rep : ℕ)
    (hj : j < C.gates.length) (hrep : rep < n + j)
    (heq : ∀ x : Fin n → Bool, edWireVal C x (n + j) = edWireVal C x rep) :
    circuitFun n (edDelete n C j rep) = circuitFun n C := by
  funext x
  exact edDelete_wires C j hj rep (Or.inl hrep) heq x C.output

lemma edUnary_equal {n : ℕ} (C : Circuit) (j rep : ℕ)
    (hj : j < C.gates.length) (hrep : rep < n + j)
    (hop : (gateAt C j).op = .and ∨ (gateAt C j).op = .or)
    (hins : (gateAt C j).inputs = [rep]) :
    ∀ x : Fin n → Bool, edWireVal C x (n + j) = edWireVal C x rep := by
  intro x
  rw [edWireVal_gate C x j hj]
  have hgate : C.gates[j] = gateAt C j := by
    exact (List.getD_eq_getElem _ _ hj).symm
  rw [hgate, hins]
  rcases hop with hop | hop <;> simp [hop, GateOp.eval, hrep]

lemma edDelete_and_source {n : ℕ} (C : Circuit) (j rep k : ℕ)
    (hj : j < C.gates.length) (hrep : rep < n + j)
    (heq : ∀ x : Fin n → Bool, edWireVal C x (n + j) = edWireVal C x rep)
    (hk : k < (edDelete n C j rep).gates.length)
    (hand : (gateAt (edDelete n C j rep) k).op = .and) :
    ∃ l < C.gates.length, l ≠ j ∧ (gateAt C l).op = .and ∧
      ∀ x : Fin n → Bool,
        edWireVal (edDelete n C j rep) x (n + k) = edWireVal C x (n + l) := by
  by_cases hkj : k < j
  · refine ⟨k, by omega, by omega, ?_, ?_⟩
    · simpa [edDelete_before n C j rep k hj hkj] using hand
    · intro x
      simpa [edShiftIdx, show n + k < n + j by omega] using
        edDelete_wires C j hj rep (Or.inl hrep) heq x (n + k)
  · have hlen := edDelete_size n C j rep hj
    change (edDelete n C j rep).gates.length + 1 = C.gates.length at hlen
    refine ⟨k + 1, by omega, by omega, ?_, ?_⟩
    · simpa [edDelete_after n C j rep k hj hk (by omega)] using hand
    · intro x
      have hidx : edShiftIdx (n + j) rep (n + (k + 1)) = n + k := by
        unfold edShiftIdx
        split_ifs <;> omega
      simpa [hidx] using edDelete_wires C j hj rep (Or.inl hrep) heq x (n + (k + 1))

lemma edUnary_delete {n : ℕ} (C : Circuit) (j rep : ℕ)
    (hm : Monotone2 C) (hr : ReadsBack n C) (hj : j < C.gates.length)
    (hins : (gateAt C j).inputs = [rep]) :
    Monotone2 (edDelete n C j rep) ∧ ReadsBack n (edDelete n C j rep) ∧
      (edDelete n C j rep).size + 1 = C.size ∧
      circuitFun n (edDelete n C j rep) = circuitFun n C := by
  have hrep : rep < n + j := hr j hj rep (by simp [hins])
  have hmem : gateAt C j ∈ C.gates := by
    rw [gateAt, List.getD_eq_getElem _ _ hj]
    exact List.getElem_mem hj
  exact ⟨edDelete_monotone n C j rep hm, edDelete_readsBack n C j rep hj hrep hr,
    edDelete_size n C j rep hj,
    edDelete_eval C j rep hj hrep (edUnary_equal C j rep hj hrep (hm _ hmem).1 hins)⟩

end PEqualNP.Outside.L_meta_3451
