import Mathlib
import PEqualNP.Defs
import PEqualNP.Outside.L_lib_435

namespace PEqualNP.Outside.L_meta_25740_aux

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity.NestedCover (ReadsBack gateAt)

def h5b2z (b : Bool) : ZMod 2 := if b then 1 else 0

lemma h5b2z_inj {a b : Bool} (h : h5b2z a = h5b2z b) : a = b := by
  cases a <;> cases b <;> simp [h5b2z] at h <;> rfl

lemma h5b2z_xor (a b : Bool) : h5b2z (xor a b) = h5b2z a + h5b2z b := by
  cases a <;> cases b <;> decide

lemma h5b2z_and (a b : Bool) : h5b2z (a && b) = h5b2z a * h5b2z b := by
  cases a <;> cases b <;> decide

lemma h5b2z_not (a : Bool) : h5b2z (!a) = 1 + h5b2z a := by
  cases a <;> decide

lemma h5zmod2_add_self (x : ZMod 2) : x + x = 0 := by
  fin_cases x <;> decide

lemma h5zmod2_two : (2 : ZMod 2) = 0 := rfl

lemma h5zmod2_ite_eq (x : ZMod 2) : (if x = 1 then (1 : ZMod 2) else 0) = x := by
  by_cases h : x = 1
  · simp [h]
  · simp only [h, ite_false]
    fin_cases x
    · rfl
    · exact absurd rfl h

def h5nlGate (g : Gate) : Bool :=
  (g.inputs.length == 2) &&
  xor (xor (g.op.eval [false, false]) (g.op.eval [false, true]))
      (xor (g.op.eval [true, false]) (g.op.eval [true, true]))

def h5wiresOf (x : List Bool) (gs : List Gate) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

lemma h5wiresOf_length (x : List Bool) (gs : List Gate) :
    (h5wiresOf x gs).length = x.length + gs.length := by
  unfold h5wiresOf
  induction gs generalizing x with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega

lemma h5wiresOf_append (x : List Bool) (gs1 gs2 : List Gate) :
    h5wiresOf x (gs1 ++ gs2) =
      gs2.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
        (h5wiresOf x gs1) := by
  unfold h5wiresOf
  rw [List.foldl_append]

lemma h5foldl_append_prefix {α β : Type*} (f : List α → β → α) (l : List β) (init : List α) :
    ∃ ext : List α, l.foldl (fun acc b => acc ++ [f acc b]) init = init ++ ext := by
  induction l generalizing init with
  | nil => exact ⟨[], by simp⟩
  | cons b l ih =>
    rw [List.foldl_cons]
    obtain ⟨ext, hext⟩ := ih (init ++ [f init b])
    exact ⟨f init b :: ext, by rw [hext]; simp⟩

lemma h5wiresOf_append_getD_lt (x : List Bool) (gs1 gs2 : List Gate) {k : ℕ}
    (hk : k < x.length + gs1.length) :
    (h5wiresOf x (gs1 ++ gs2)).getD k false = (h5wiresOf x gs1).getD k false := by
  rw [h5wiresOf_append]
  obtain ⟨ext, hext⟩ := h5foldl_append_prefix
    (fun (w : List Bool) (g : Gate) => g.op.eval (g.inputs.map fun i => w.getD i false))
    gs2 (h5wiresOf x gs1)
  rw [hext, List.getD_append _ _ _ _ (by rw [h5wiresOf_length]; exact hk)]

lemma h5wiresOf_getD_input (x : List Bool) (gs : List Gate) {k : ℕ} (hk : k < x.length) :
    (h5wiresOf x gs).getD k false = x.getD k false := by
  have h := h5wiresOf_append_getD_lt x [] gs (by simpa using hk)
  simpa [h5wiresOf] using h

lemma h5wiresOf_getD_gate (x : List Bool) (gs : List Gate) {idx : ℕ} (hidx : idx < gs.length)
    (hrb : ∀ a ∈ (gs[idx]).inputs, a < x.length + idx) :
    (h5wiresOf x gs).getD (x.length + idx) false =
      (gs[idx]).op.eval ((gs[idx]).inputs.map fun a => (h5wiresOf x gs).getD a false) := by
  have hsplit : gs = (gs.take idx ++ [gs[idx]]) ++ gs.drop (idx + 1) := by
    rw [List.take_append_getElem, List.take_append_drop]
  have hlen1 : (gs.take idx).length = idx := List.length_take_of_le (Nat.le_of_lt hidx)
  have hlen2 : (gs.take idx ++ [gs[idx]]).length = idx + 1 := by
    rw [List.length_append, hlen1]
    rfl
  conv_lhs => rw [hsplit]
  rw [h5wiresOf_append_getD_lt x (gs.take idx ++ [gs[idx]]) (gs.drop (idx + 1)) (by omega)]
  rw [h5wiresOf_append, List.foldl_cons, List.foldl_nil]
  have hlw : (h5wiresOf x (gs.take idx)).length = x.length + idx := by
    rw [h5wiresOf_length, hlen1]
  rw [List.getD_append_right _ _ _ _ (by omega)]
  simp only [hlw, Nat.sub_self, List.getD_cons_zero]
  congr 1
  apply List.map_congr_left
  intro a ha
  have halt : a < x.length + (gs.take idx).length := by rw [hlen1]; exact hrb a ha
  conv_rhs => rw [hsplit]
  rw [h5wiresOf_append_getD_lt x (gs.take idx ++ [gs[idx]]) (gs.drop (idx + 1)) (by omega)]
  rw [h5wiresOf_append_getD_lt x (gs.take idx) [gs[idx]] halt]

lemma h5anf_one (f : Bool → Bool) (x : Bool) :
    h5b2z (f x) = h5b2z (f false) + (h5b2z (f false) + h5b2z (f true)) * h5b2z x := by
  cases x <;> cases h0 : f false <;> cases h1 : f true <;> decide

lemma h5anf_two (f : Bool → Bool → Bool) (x y : Bool) :
    h5b2z (f x y) =
      h5b2z (f false false) +
      (h5b2z (f false false) + h5b2z (f true false)) * h5b2z x +
      (h5b2z (f false false) + h5b2z (f false true)) * h5b2z y +
      h5b2z (xor (xor (f false false) (f false true)) (xor (f true false) (f true true))) *
        (h5b2z x * h5b2z y) := by
  cases x <;> cases y <;>
    cases h00 : f false false <;> cases h01 : f false true <;>
    cases h10 : f true false <;> cases h11 : f true true <;> decide

def h5val (N : ℕ) (C : Circuit) (k : ℕ) (x : Fin N → Bool) : ZMod 2 :=
  h5b2z ((h5wiresOf (List.ofFn x) C.gates).getD k false)

def h5prod (N : ℕ) (C : Circuit) (j : Fin C.gates.length) (x : Fin N → Bool) : ZMod 2 :=
  h5val N C ((C.gates[j.val]).inputs.getD 0 0) x *
    h5val N C ((C.gates[j.val]).inputs.getD 1 0) x

set_option maxHeartbeats 800000 in
lemma h5wire_normal_form (N : ℕ) (C : Circuit)
    (hlen : ∀ g ∈ C.gates, g.inputs.length ≤ 2)
    (hrb : ReadsBack N C) (k : ℕ) :
    ∃ (c : ZMod 2) (a : Fin N → ZMod 2) (b : Fin C.gates.length → ZMod 2),
      (∀ x, h5val N C k x = c + (∑ i, a i * h5b2z (x i)) +
        ∑ j, b j * h5prod N C j x) ∧
      ∀ j, k < N + j.val ∨ h5nlGate (C.gates[j.val]) = false → b j = 0 := by
  classical
  have hrb' : ∀ (idx : ℕ) (hidx : idx < C.gates.length),
      ∀ a ∈ (C.gates[idx]).inputs, a < N + idx := by
    intro idx hidx a ha
    have h := hrb idx hidx a
    unfold gateAt at h
    rw [List.getD_eq_getElem _ _ hidx] at h
    exact h ha
  have hval_gate : ∀ (idx : ℕ) (hidx : idx < C.gates.length) (x : Fin N → Bool),
      h5val N C (N + idx) x =
        h5b2z ((C.gates[idx]).op.eval ((C.gates[idx]).inputs.map fun a =>
          (h5wiresOf (List.ofFn x) C.gates).getD a false)) := by
    intro idx hidx x
    unfold h5val
    have h := h5wiresOf_getD_gate (List.ofFn x) C.gates hidx (by
      intro a ha
      rw [List.length_ofFn]
      exact hrb' idx hidx a ha)
    rw [List.length_ofFn] at h
    rw [h]
  induction k using Nat.strong_induction_on with
  | ind k ih =>
    by_cases hk1 : k < N
    · refine ⟨0, fun i => if i.val = k then 1 else 0, fun _ => 0, ?_, by simp⟩
      intro x
      have hv : h5val N C k x = h5b2z (x ⟨k, hk1⟩) := by
        unfold h5val
        rw [h5wiresOf_getD_input _ _ (by simp [hk1])]
        rw [List.getD_eq_getElem _ _ (by simp [hk1]), List.getElem_ofFn]
      rw [hv]
      simp only [zero_mul, Finset.sum_const_zero, add_zero, zero_add]
      symm
      rw [Finset.sum_eq_single (⟨k, hk1⟩ : Fin N)]
      · simp
      · intro i _ hi
        have hne : i.val ≠ k := fun h => hi (Fin.ext h)
        simp [hne]
      · simp
    · by_cases hk2 : k < N + C.gates.length
      · let idx : Fin C.gates.length := ⟨k - N, by omega⟩
        have hkeq : k = N + idx.val := by simp [idx]; omega
        let g := C.gates[idx.val]
        have hgl : g.inputs.length ≤ 2 := hlen g (List.getElem_mem idx.isLt)
        match hg_in : g.inputs with
        | [] =>
          refine ⟨h5b2z (g.op.eval []), fun _ => 0, fun _ => 0, ?_, by simp⟩
          intro x
          rw [hkeq, hval_gate idx.val idx.isLt x]
          change h5b2z (g.op.eval (g.inputs.map _)) = _
          simp [hg_in]
        | [u] =>
          have hu_lt : u < k := by
            rw [hkeq]
            exact hrb' idx.val idx.isLt u (by rw [hg_in]; simp)
          obtain ⟨cu, au, bu, huf, hus⟩ := ih u hu_lt
          let c0 := h5b2z (g.op.eval [false])
          let c1 := h5b2z (g.op.eval [false]) + h5b2z (g.op.eval [true])
          refine ⟨c0 + c1 * cu, fun i => c1 * au i, fun j => c1 * bu j, ?_, ?_⟩
          · intro x
            rw [hkeq, hval_gate idx.val idx.isLt x]
            change h5b2z (g.op.eval (g.inputs.map _)) = _
            rw [hg_in, List.map_cons, List.map_nil]
            have hanf := h5anf_one (fun z => g.op.eval [z])
              ((h5wiresOf (List.ofFn x) C.gates).getD u false)
            change h5b2z (g.op.eval [_]) = c0 + c1 * h5val N C u x at hanf
            rw [hanf, huf x]
            simp_rw [mul_assoc]
            rw [← Finset.mul_sum, ← Finset.mul_sum]
            ring
          · intro j hj
            have hz : bu j = 0 := hus j (hj.imp (fun h => by omega) id)
            simp [hz]
        | [u, v] =>
          have hu_lt : u < k := by
            rw [hkeq]
            exact hrb' idx.val idx.isLt u (by rw [hg_in]; simp)
          have hv_lt : v < k := by
            rw [hkeq]
            exact hrb' idx.val idx.isLt v (by rw [hg_in]; simp)
          obtain ⟨cu, au, bu, huf, hus⟩ := ih u hu_lt
          obtain ⟨cv, av, bv, hvf, hvs⟩ := ih v hv_lt
          let c0 := h5b2z (g.op.eval [false, false])
          let c1 := h5b2z (g.op.eval [false, false]) + h5b2z (g.op.eval [true, false])
          let c2 := h5b2z (g.op.eval [false, false]) + h5b2z (g.op.eval [false, true])
          let c3 := h5b2z (h5nlGate g)
          have hp : ∀ x, h5prod N C idx x = h5val N C u x * h5val N C v x := by
            intro x
            change h5val N C (g.inputs.getD 0 0) x * h5val N C (g.inputs.getD 1 0) x = _
            simp [hg_in]
          refine ⟨c0 + c1 * cu + c2 * cv, fun i => c1 * au i + c2 * av i,
            fun j => c1 * bu j + c2 * bv j + if j = idx then c3 else 0, ?_, ?_⟩
          · intro x
            have hanf : h5val N C k x = c0 + c1 * h5val N C u x +
                c2 * h5val N C v x + c3 * h5prod N C idx x := by
              rw [hkeq, hval_gate idx.val idx.isLt x]
              change h5b2z (g.op.eval (g.inputs.map _)) = _
              rw [hg_in, List.map_cons, List.map_cons, List.map_nil, hp]
              have h := h5anf_two (fun a b => g.op.eval [a, b])
                ((h5wiresOf (List.ofFn x) C.gates).getD u false)
                ((h5wiresOf (List.ofFn x) C.gates).getD v false)
              simpa [c0, c1, c2, c3, h5val, h5nlGate, hg_in] using h
            rw [hanf, huf x, hvf x]
            simp_rw [add_mul, Finset.sum_add_distrib, mul_assoc]
            have hs : (∑ j : Fin C.gates.length,
                (if j = idx then c3 else 0) * h5prod N C j x) = c3 * h5prod N C idx x := by
              simp
            rw [hs]
            simp_rw [← Finset.mul_sum]
            ring
          · intro j hj
            have hzu : bu j = 0 := hus j (hj.imp (fun h => by omega) id)
            have hzv : bv j = 0 := hvs j (hj.imp (fun h => by omega) id)
            change c1 * bu j + c2 * bv j + (if j = idx then c3 else 0) = 0
            rw [hzu, hzv]
            by_cases heq : j = idx
            · subst j
              have hn : h5nlGate g = false := by
                rcases hj with hj | hj
                · omega
                · exact hj
              simp [c3, hn, h5b2z]
            · simp [heq]
        | _ :: _ :: _ :: _ =>
          rw [hg_in] at hgl
          simp at hgl
      · refine ⟨0, fun _ => 0, fun _ => 0, ?_, by simp⟩
        intro x
        unfold h5val
        have hge : (h5wiresOf (List.ofFn x) C.gates).length ≤ k := by
          rw [h5wiresOf_length, List.length_ofFn]
          omega
        rw [List.getD_eq_default _ _ hge]
        simp [h5b2z]

lemma h5card_filter_fin_eq_countP {α : Type*} (l : List α) (p : α → Bool) :
    (Finset.univ.filter (fun idx : Fin l.length => p l[idx.val] = true)).card = l.countP p := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.countP_cons]
    have hsplit : (Finset.univ.filter (fun idx : Fin (a :: l).length => p (a :: l)[idx.val] = true)).card =
        (if p a = true then 1 else 0) +
        (Finset.univ.filter (fun idx : Fin l.length => p l[idx.val] = true)).card := by
      have hsum : ∀ (S : Finset (Fin (l.length + 1))), S.card =
          (if (0 : Fin (l.length + 1)) ∈ S then 1 else 0) +
          (Finset.univ.filter (fun idx : Fin l.length => idx.succ ∈ S)).card := by
        intro S
        have h1 : S.card = ∑ x : Fin (l.length + 1), if x ∈ S then 1 else 0 := by
          simp
        rw [h1, Fin.sum_univ_succ]
        congr 1
        simp
      have h2 := hsum (Finset.univ.filter (fun idx : Fin (a :: l).length => p (a :: l)[idx.val] = true))
      simpa using h2
    rw [hsplit, ih]
    cases p a <;> simp [Nat.add_comm]

lemma h5compact_wire_normal_form (N : ℕ) (C : Circuit)
    (hlen : ∀ g ∈ C.gates, g.inputs.length ≤ 2) (hrb : ReadsBack N C) :
    ∃ e : Fin (C.gates.countP h5nlGate) ↪o Fin C.gates.length,
      (∀ i, h5nlGate (C.gates[(e i).val]) = true) ∧
      (∀ j, h5nlGate (C.gates[j.val]) = true → ∃ i, e i = j) ∧
      ∃ (c : ℕ → ZMod 2) (a : ℕ → Fin N → ZMod 2)
        (b : ℕ → Fin (C.gates.countP h5nlGate) → ZMod 2),
        (∀ k x, h5val N C k x = c k + (∑ i, a k i * h5b2z (x i)) +
          ∑ j, b k j * h5prod N C (e j) x) ∧
        (∀ k j, k < N + (e j).val → b k j = 0) := by
  classical
  let S := Finset.univ.filter (fun j : Fin C.gates.length => h5nlGate (C.gates[j.val]) = true)
  have hcard : S.card = C.gates.countP h5nlGate := h5card_filter_fin_eq_countP _ _
  let e : Fin (C.gates.countP h5nlGate) ↪o Fin C.gates.length := S.orderEmbOfFin hcard
  have he_mem : ∀ i, e i ∈ S := fun i => S.orderEmbOfFin_mem hcard i
  have he_nl : ∀ i, h5nlGate (C.gates[(e i).val]) = true := by
    intro i
    exact (Finset.mem_filter.mp (he_mem i)).2
  refine ⟨e, he_nl, ?_, ?_⟩
  · intro j hj
    have hmem : j ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩
    refine ⟨(S.orderIsoOfFin hcard).symm ⟨j, hmem⟩, ?_⟩
    have h := (S.orderIsoOfFin hcard).apply_symm_apply ⟨j, hmem⟩
    exact congrArg Subtype.val h
  · choose c a b hb hs using h5wire_normal_form N C hlen hrb
    refine ⟨c, a, fun k j => b k (e j), ?_, ?_⟩
    · intro k x
      rw [hb k x]
      congr 1
      calc
        (∑ j, b k j * h5prod N C j x) = ∑ j ∈ S, b k j * h5prod N C j x := by
          symm
          apply Finset.sum_subset (Finset.filter_subset _ _)
          intro j _ hj
          have hn : h5nlGate (C.gates[j.val]) = false := by
            cases h : h5nlGate (C.gates[j.val])
            · rfl
            · exact False.elim (hj (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩))
          rw [hs k j (Or.inr hn), zero_mul]
        _ = ∑ j : S, b k j.val * h5prod N C j.val x :=
          (Finset.sum_coe_sort S (fun j => b k j * h5prod N C j x)).symm
        _ = ∑ i, b k (e i) * h5prod N C (e i) x := by
          symm
          apply Fintype.sum_equiv (S.orderIsoOfFin hcard).toEquiv
          intro i
          rfl
    · intro k j hj
      exact hs k (e j) (Or.inl hj)

def h5input0 (C : Circuit) (j : Fin C.gates.length) : ℕ :=
  (C.gates[j.val]).inputs.getD 0 0

def h5input1 (C : Circuit) (j : Fin C.gates.length) : ℕ :=
  (C.gates[j.val]).inputs.getD 1 0

lemma h5operand_before (N : ℕ) (C : Circuit) (hrb : ReadsBack N C)
    (j : Fin C.gates.length) (hnl : h5nlGate (C.gates[j.val]) = true) :
    h5input0 C j < N + j.val ∧ h5input1 C j < N + j.val := by
  have hlen2 : (C.gates[j.val]).inputs.length = 2 := by
    unfold h5nlGate at hnl
    rw [Bool.and_eq_true] at hnl
    simpa using hnl.1
  obtain ⟨u, v, huv⟩ : ∃ u v, (C.gates[j.val]).inputs = [u, v] := by
    match h : (C.gates[j.val]).inputs with
    | [u, v] => exact ⟨u, v, rfl⟩
    | [] => rw [h] at hlen2; simp at hlen2
    | [_] => rw [h] at hlen2; simp at hlen2
    | _ :: _ :: _ :: _ => rw [h] at hlen2; simp at hlen2
  have hr := hrb j.val j.isLt
  unfold gateAt at hr
  rw [List.getD_eq_getElem _ _ j.isLt] at hr
  constructor
  · simpa [h5input0, huv] using hr u (by simp [huv])
  · simpa [h5input1, huv] using hr v (by simp [huv])

lemma h5compact_operand_lower (N : ℕ) (C : Circuit) (hrb : ReadsBack N C)
    {t : ℕ} (e : Fin t ↪o Fin C.gates.length)
    (hnl : ∀ i, h5nlGate (C.gates[(e i).val]) = true)
    (b : ℕ → Fin t → ZMod 2)
    (hs : ∀ k j, k < N + (e j).val → b k j = 0) :
    ∀ i j, i ≤ j → b (h5input0 C (e i)) j = 0 ∧ b (h5input1 C (e i)) j = 0 := by
  intro i j hij
  have hbnd := h5operand_before N C hrb (e i) (hnl i)
  have he : (e i).val ≤ (e j).val := e.monotone hij
  exact ⟨hs _ _ (by omega), hs _ _ (by omega)⟩

lemma h5compact_normal_system (N : ℕ) (C : Circuit)
    (hlen : ∀ g ∈ C.gates, g.inputs.length ≤ 2) (hrb : ReadsBack N C) :
    ∃ (e : Fin (C.gates.countP h5nlGate) ↪o Fin C.gates.length)
      (c : ℕ → ZMod 2) (a : ℕ → Fin N → ZMod 2)
      (b : ℕ → Fin (C.gates.countP h5nlGate) → ZMod 2),
      (∀ i, h5nlGate (C.gates[(e i).val]) = true) ∧
      (∀ j, h5nlGate (C.gates[j.val]) = true → ∃ i, e i = j) ∧
      (∀ k x, h5val N C k x = c k + (∑ i, a k i * h5b2z (x i)) +
        ∑ j, b k j * (h5val N C (h5input0 C (e j)) x * h5val N C (h5input1 C (e j)) x)) ∧
      (∀ i j, i ≤ j → b (h5input0 C (e i)) j = 0 ∧ b (h5input1 C (e i)) j = 0) := by
  obtain ⟨e, hnl, he, c, a, b, hb, hs⟩ := h5compact_wire_normal_form N C hlen hrb
  refine ⟨e, c, a, b, hnl, he, ?_, h5compact_operand_lower N C hrb e hnl b hs⟩
  intro k x
  exact hb k x

lemma h5operand_coverage (C : Circuit) {t : ℕ}
    (e : Fin t ↪o Fin C.gates.length)
    (he : ∀ j, h5nlGate (C.gates[j.val]) = true → ∃ i, e i = j)
    (g : Gate) (hg : g ∈ C.gates) (hnl : h5nlGate g = true)
    (w : ℕ) (hw : w ∈ g.inputs) :
    ∃ i, w = h5input0 C (e i) ∨ w = h5input1 C (e i) := by
  obtain ⟨j, hj, hjg⟩ := List.mem_iff_getElem.mp hg
  have hjnl : h5nlGate (C.gates[(⟨j, hj⟩ : Fin C.gates.length).val]) = true := by
    simpa [hjg] using hnl
  obtain ⟨i, hi⟩ := he ⟨j, hj⟩ hjnl
  refine ⟨i, ?_⟩
  rw [hi]
  simp only [h5input0, h5input1, hjg]
  have hlen2 : g.inputs.length = 2 := by
    unfold h5nlGate at hnl
    rw [Bool.and_eq_true] at hnl
    simpa using hnl.1
  match h : g.inputs with
  | [u, v] => simpa [h] using hw
  | [] => rw [h] at hlen2; simp at hlen2
  | [_] => rw [h] at hlen2; simp at hlen2
  | _ :: _ :: _ :: _ => rw [h] at hlen2; simp at hlen2

lemma h5AddSelf (x : ZMod 2) : x + x = 0 := by
  have htwo : (2 : ZMod 2) = 0 := by decide
  calc
    x + x = (2 : ZMod 2) * x := by ring
    _ = 0 := by rw [htwo, zero_mul]

def h5RawDefect {n : ℕ} (f : (Fin n → Bool) → ZMod 2)
    (v : (Fin n → Bool) × (Fin n → Bool)) : ZMod 2 :=
  f v.1 + f v.2 + f (fun i => xor (v.1 i) (v.2 i)) + f (fun _ => false)

def h5RawDefectLinear (n : ℕ) :
    ((Fin n → Bool) → ZMod 2) →ₗ[ZMod 2]
      (((Fin n → Bool) × (Fin n → Bool)) → ZMod 2) where
  toFun := h5RawDefect
  map_add' f g := by
    funext v
    simp only [h5RawDefect, Pi.add_apply]
    ring
  map_smul' c f := by
    funext v
    simp only [h5RawDefect, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

lemma h5RawDefectLinear_const (n : ℕ) (c : ZMod 2) :
    h5RawDefectLinear n (fun _ => c) = 0 := by
  funext v
  change c + c + c + c = 0
  calc
    c + c + c + c = (c + c) + (c + c) := by ring
    _ = 0 := h5AddSelf (c + c)

lemma h5RawDefectLinear_coord (n : ℕ) (i : Fin n) :
    h5RawDefectLinear n (fun x => if x i then 1 else 0) = 0 := by
  funext v
  change (if v.1 i then (1 : ZMod 2) else 0) + (if v.2 i then 1 else 0) +
    (if xor (v.1 i) (v.2 i) then 1 else 0) + (if false then 1 else 0) = 0
  cases v.1 i <;> cases v.2 i <;> decide

lemma h5RawDefectLinear_affine (n : ℕ) (c : ZMod 2) (a : Fin n → ZMod 2) :
    h5RawDefectLinear n
      (fun x => c + ∑ i : Fin n, a i * (if x i then 1 else 0)) = 0 := by
  have heq : (fun x : Fin n → Bool => c + ∑ i : Fin n, a i *
      (if x i then (1 : ZMod 2) else 0)) =
      (fun _ => c) + ∑ i : Fin n, a i • (fun x => if x i then 1 else 0) := by
    funext x
    simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [heq, map_add, map_sum, h5RawDefectLinear_const]
  simp only [map_smul, h5RawDefectLinear_coord, smul_zero,
    Finset.sum_const_zero, add_zero]

lemma h5RawDefect_factor {n : ℕ} {W J : Type*} [Fintype J]
    (F : W → (Fin n → Bool) → ZMod 2)
    (c : W → ZMod 2) (a : W → Fin n → ZMod 2)
    (B : Matrix W J (ZMod 2)) (P : J → (Fin n → Bool) → ZMod 2)
    (hF : ∀ w x, F w x = c w +
      (∑ i : Fin n, a w i * (if x i then 1 else 0)) + ∑ j : J, B w j * P j x) :
    (Matrix.of fun w v => h5RawDefect (F w) v) =
      B * (Matrix.of fun j v => h5RawDefect (P j) v) := by
  classical
  ext w v
  have heq : F w = (fun x => c w + ∑ i : Fin n, a w i *
      (if x i then (1 : ZMod 2) else 0)) + ∑ j : J, B w j • P j := by
    funext x
    simpa only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      using hF w x
  change (h5RawDefectLinear n (F w)) v = _
  rw [heq, map_add, h5RawDefectLinear_affine, zero_add, map_sum]
  simp only [map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    Matrix.mul_apply, h5RawDefectLinear]
  rfl

lemma h5RawDefect_factor_masked {n : ℕ} {W J : Type*} [Fintype J]
    (F : W → (Fin n → Bool) → ZMod 2)
    (c : W → ZMod 2) (a : W → Fin n → ZMod 2)
    (B : Matrix W J (ZMod 2)) (P : J → (Fin n → Bool) → ZMod 2)
    (mask : W → ZMod 2)
    (hF : ∀ w x, F w x = c w +
      (∑ i : Fin n, a w i * (if x i then 1 else 0)) + ∑ j : J, B w j * P j x) :
    (Matrix.of fun w v => mask w * h5RawDefect (F w) v) =
      (Matrix.of fun w j => mask w * B w j) *
        (Matrix.of fun j v => h5RawDefect (P j) v) := by
  have heq := h5RawDefect_factor F c a B P hF
  classical
  ext w v
  have he := congrFun (congrFun heq w) v
  change h5RawDefect (F w) v = ∑ j, B w j * h5RawDefect (P j) v at he
  change mask w * h5RawDefect (F w) v = ∑ j, (mask w * B w j) * h5RawDefect (P j) v
  rw [he]
  simp only [Finset.mul_sum, mul_assoc]

lemma h5RawDefect_bit {n : ℕ} (f : (Fin n → Bool) → Bool)
    (v : (Fin n → Bool) × (Fin n → Bool)) :
    h5RawDefect (fun x => if f x then 1 else 0) v =
      if xor (xor (f v.1) (f v.2))
          (xor (f (fun i => xor (v.1 i) (v.2 i))) (f (fun _ => false)))
      then 1 else 0 := by
  dsimp only [h5RawDefect]
  cases f v.1 <;> cases f v.2 <;>
    cases f (fun i => xor (v.1 i) (v.2 i)) <;> cases f (fun _ => false) <;> decide

abbrev h5OperandMask (C : PEqualNP.CircuitLowerBounds.Circuit) (w : ℕ) : Prop :=
  ∃ g ∈ C.gates, h5nlGate g = true ∧ w ∈ g.inputs

def h5PostedDefect (N : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) :
    Matrix (Fin (N + C.gates.length)) ((Fin N → Bool) × (Fin N → Bool)) (ZMod 2) :=
  let W := fun (w : ℕ) (x : Fin N → Bool) => (C.wires (List.ofFn x)).getD w false
  fun w v =>
    if (∃ g ∈ C.gates, h5nlGate g = true ∧ w.val ∈ g.inputs) ∧
        xor (xor (W w.val v.1) (W w.val v.2))
          (xor (W w.val (fun i => xor (v.1 i) (v.2 i))) (W w.val (fun _ => false))) = true
    then 1 else 0

lemma h5PostedDefect_masked (N : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) :
    h5PostedDefect N C = Matrix.of (fun w v =>
      (if h5OperandMask C w.val then (1 : ZMod 2) else 0) *
        h5RawDefect (h5val N C w.val) v) := by
  classical
  ext w v
  let W := fun (k : ℕ) (x : Fin N → Bool) => (C.wires (List.ofFn x)).getD k false
  let d := xor (xor (W w.val v.1) (W w.val v.2))
    (xor (W w.val (fun i => xor (v.1 i) (v.2 i))) (W w.val (fun _ => false)))
  have hb : h5RawDefect (h5val N C w.val) v = if d then 1 else 0 := by
    change h5RawDefect (fun x => if W w.val x then 1 else 0) v = if d then 1 else 0
    exact h5RawDefect_bit (W w.val) v
  change (if h5OperandMask C w.val ∧ d = true then (1 : ZMod 2) else 0) =
    (if h5OperandMask C w.val then 1 else 0) * h5RawDefect (h5val N C w.val) v
  rw [hb]
  by_cases hm : h5OperandMask C w.val <;> by_cases hd : d = true <;> simp [hm, hd]

lemma h5PostedDefect_factor (N : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit)
    {J : Type*} [Fintype J]
    (c : ℕ → ZMod 2) (a : ℕ → Fin N → ZMod 2) (b : ℕ → J → ZMod 2)
    (P : J → (Fin N → Bool) → ZMod 2)
    (hF : ∀ k x, h5val N C k x = c k + (∑ i : Fin N, a k i * h5b2z (x i)) +
      ∑ j : J, b k j * P j x) :
    h5PostedDefect N C =
      (Matrix.of fun (w : Fin (N + C.gates.length)) j =>
        (if h5OperandMask C w.val then (1 : ZMod 2) else 0) * b w.val j) *
      (Matrix.of fun j v => h5RawDefect (P j) v) := by
  rw [h5PostedDefect_masked]
  exact h5RawDefect_factor_masked
    (fun (w : Fin (N + C.gates.length)) => h5val N C w.val)
    (fun w => c w.val) (fun w => a w.val) (Matrix.of fun w j => b w.val j)
    P (fun w => if h5OperandMask C w.val then 1 else 0) (fun w x => hF w.val x)

lemma h5PostedDefect_rank_le (N : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit)
    {J : Type*} [Fintype J]
    (c : ℕ → ZMod 2) (a : ℕ → Fin N → ZMod 2) (b : ℕ → J → ZMod 2)
    (P : J → (Fin N → Bool) → ZMod 2)
    (hF : ∀ k x, h5val N C k x = c k + (∑ i : Fin N, a k i * h5b2z (x i)) +
      ∑ j : J, b k j * P j x) :
    (h5PostedDefect N C).rank ≤
      (Matrix.of fun (w : Fin (N + C.gates.length)) j =>
        (if h5OperandMask C w.val then (1 : ZMod 2) else 0) * b w.val j).rank := by
  rw [h5PostedDefect_factor N C c a b P hF]
  exact Matrix.rank_mul_le_left _ _

def h5SourceSet (C : PEqualNP.CircuitLowerBounds.Circuit) {t : ℕ}
    (e : Fin t ↪o Fin C.gates.length) (b : ℕ → Fin t → ZMod 2) : Finset (Fin t) :=
  Finset.univ.filter (fun j => ∃ i : Fin t,
    b (h5input0 C (e i)) j ≠ 0 ∨ b (h5input1 C (e i)) j ≠ 0)

lemma h5maskedCoefficient_off_sources (N : ℕ)
    (C : PEqualNP.CircuitLowerBounds.Circuit) {t : ℕ}
    (e : Fin t ↪o Fin C.gates.length)
    (he : ∀ j, h5nlGate (C.gates[j.val]) = true → ∃ i, e i = j)
    (b : ℕ → Fin t → ZMod 2) (w : Fin (N + C.gates.length)) (j : Fin t)
    (hj : j ∉ h5SourceSet C e b) :
    (if h5OperandMask C w.val then (1 : ZMod 2) else 0) * b w.val j = 0 := by
  classical
  by_cases hw : h5OperandMask C w.val
  · have hz : b w.val j = 0 := by
      by_contra hne
      apply hj
      obtain ⟨g, hg, hnl, hwg⟩ := hw
      obtain ⟨i, hi | hi⟩ := h5operand_coverage C e he g hg hnl w.val hwg
      · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, i,
          Or.inl (by simpa only [← hi] using hne)⟩
      · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, i,
          Or.inr (by simpa only [← hi] using hne)⟩
    simp only [hz, mul_zero]
  · simp only [hw, ite_false, zero_mul]

lemma h5MatrixFactor_restrict {I J K : Type*} [Fintype J]
    (A : Matrix I J (ZMod 2)) (B : Matrix J K (ZMod 2))
    (D : Finset J) (hzero : ∀ i j, j ∉ D → A i j = 0) :
    A * B =
      (Matrix.of fun i (j : D) => A i j.val) * (Matrix.of fun (j : D) k => B j.val k) := by
  classical
  ext i k
  change (∑ j : J, A i j * B j k) = ∑ j : D, A i j.val * B j.val k
  calc
    (∑ j : J, A i j * B j k) = ∑ j ∈ D, A i j * B j k := by
      symm
      apply Finset.sum_subset (Finset.subset_univ D)
      intro j _ hj
      rw [hzero i j hj, zero_mul]
    _ = ∑ j : D, A i j.val * B j.val k :=
      (Finset.sum_coe_sort D (fun j => A i j * B j k)).symm

lemma h5Matrix_rank_mul_le_support {I J K : Type*} [Fintype J] [Fintype K]
    (A : Matrix I J (ZMod 2)) (B : Matrix J K (ZMod 2))
    (D : Finset J) (hzero : ∀ i j, j ∉ D → A i j = 0) :
    (A * B).rank ≤ D.card := by
  classical
  rw [h5MatrixFactor_restrict A B D hzero]
  apply (Matrix.rank_mul_le_left _ _).trans
  simpa only [Fintype.card_coe] using
    (Matrix.rank_le_card_width (Matrix.of fun i (j : D) => A i j.val))

lemma h5PostedDefect_rank_le_sources (N : ℕ)
    (C : PEqualNP.CircuitLowerBounds.Circuit) {t : ℕ}
    (e : Fin t ↪o Fin C.gates.length)
    (he : ∀ j, h5nlGate (C.gates[j.val]) = true → ∃ i, e i = j)
    (c : ℕ → ZMod 2) (a : ℕ → Fin N → ZMod 2) (b : ℕ → Fin t → ZMod 2)
    (P : Fin t → (Fin N → Bool) → ZMod 2)
    (hF : ∀ k x, h5val N C k x = c k + (∑ i : Fin N, a k i * h5b2z (x i)) +
      ∑ j : Fin t, b k j * P j x) :
    (h5PostedDefect N C).rank ≤ (h5SourceSet C e b).card := by
  classical
  rw [h5PostedDefect_factor N C c a b P hF]
  apply h5Matrix_rank_mul_le_support _ _ (h5SourceSet C e b)
  intro w j hj
  exact h5maskedCoefficient_off_sources N C e he b w j hj

def h5oneEachRaw {n m : ℕ} (i : Fin n) (j : Fin m) : Fin (n+m) → Bool :=
  Fin.append (fun a => decide (a = i)) (fun b => decide (b = j))

lemma h5oneEachRaw_ofFn {n m : ℕ} (i : Fin n) (j : Fin m) :
    List.ofFn (h5oneEachRaw i j) =
      List.ofFn (fun a : Fin n => decide (a = i)) ++
      List.ofFn (fun b : Fin m => decide (b = j)) := by
  exact List.ofFn_fin_append _ _

lemma h5linear_oneEach {n m : ℕ} (a : Fin (n+m) → ZMod 2) (i : Fin n) (j : Fin m) :
    (∑ k, a k * h5b2z (h5oneEachRaw i j k)) =
      a (Fin.castAdd m i) + a (Fin.natAdd n j) := by
  rw [Fin.sum_univ_add]
  simp [h5oneEachRaw, h5b2z]

lemma h5affine_oneEach {n m : ℕ} (c : ZMod 2) (a : Fin (n+m) → ZMod 2)
    (i : Fin n) (j : Fin m) :
    c + (∑ k, a k * h5b2z (h5oneEachRaw i j k)) =
      (c + a (Fin.castAdd m i)) + a (Fin.natAdd n j) := by
  rw [h5linear_oneEach]
  ac_rfl

def h5affineTerm {N : ℕ} (c : ℕ → ZMod 2) (a : ℕ → Fin N → ZMod 2)
    (k : ℕ) (x : Fin N → Bool) : ZMod 2 :=
  c k + ∑ i, a k i * h5b2z (x i)

def h5affinePair {N t : ℕ} (u v : Fin t → ℕ)
    (c : ℕ → ZMod 2) (a : ℕ → Fin N → ZMod 2) (x : Fin N → Bool) :
    (Fin t → ZMod 2) × (Fin t → ZMod 2) :=
  (fun i => h5affineTerm c a (u i) x, fun i => h5affineTerm c a (v i) x)

lemma h5normal_decoder_eq {N t : ℕ} (C : Circuit) (u v : Fin t → ℕ)
    (c : ℕ → ZMod 2) (a : ℕ → Fin N → ZMod 2) (b : ℕ → Fin t → ZMod 2)
    (e : ((Fin t → ZMod 2) × (Fin t → ZMod 2)) ≃
      ((Fin t → ZMod 2) × (Fin t → ZMod 2)))
    (he : ∀ y, e y =
      ((fun i => y.1 i + ∑ j, b (u i) j * y.1 j * y.2 j),
       (fun i => y.2 i + ∑ j, b (v i) j * y.1 j * y.2 j)))
    (hf : ∀ k x, h5val N C k x = h5affineTerm c a k x +
      ∑ j, b k j * (h5val N C (u j) x * h5val N C (v j) x))
    (k : ℕ) (x : Fin N → Bool) :
    h5val N C k x = h5affineTerm c a k x +
      ∑ j, b k j * (e.symm (h5affinePair u v c a x)).1 j *
        (e.symm (h5affinePair u v c a x)).2 j := by
  let y : (Fin t → ZMod 2) × (Fin t → ZMod 2) :=
    (fun i => h5val N C (u i) x, fun i => h5val N C (v i) x)
  have hy : e y = h5affinePair u v c a x := by
    rw [he]
    apply Prod.ext
    · funext i
      change h5val N C (u i) x +
        (∑ j, b (u i) j * h5val N C (u j) x * h5val N C (v j) x) = _
      rw [hf]
      simp_rw [mul_assoc]
      rw [add_assoc, h5zmod2_add_self, add_zero]
      rfl
    · funext i
      change h5val N C (v i) x +
        (∑ j, b (v i) j * h5val N C (u j) x * h5val N C (v j) x) = _
      rw [hf]
      simp_rw [mul_assoc]
      rw [add_assoc, h5zmod2_add_self, add_zero]
      rfl
  have hsym : e.symm (h5affinePair u v c a x) = y := by
    rw [← hy, Equiv.symm_apply_apply]
  rw [hsym, hf]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  exact (mul_assoc _ _ _).symm

lemma h5affinePair_oneEach {n m t : ℕ} (u v : Fin t → ℕ)
    (c : ℕ → ZMod 2) (a : ℕ → Fin (n+m) → ZMod 2)
    (i : Fin n) (j : Fin m) :
    h5affinePair u v c a (h5oneEachRaw i j) =
      ((fun z => c (u z) + a (u z) (Fin.castAdd m i)),
       (fun z => c (v z) + a (v z) (Fin.castAdd m i))) +
      ((fun z => a (u z) (Fin.natAdd n j)),
       (fun z => a (v z) (Fin.natAdd n j))) := by
  apply Prod.ext
  · funext z
    exact h5affine_oneEach (c (u z)) (a (u z)) i j
  · funext z
    exact h5affine_oneEach (c (v z)) (a (v z)) i j

lemma bool_defect_split (a b c d : Bool)
    (h : xor (xor a b) (xor c d) = false) : c = xor (xor a b) d := by
  cases a <;> cases b <;> cases c <;> cases d <;> simp_all

lemma matrix_eq_zero_of_rank_zero {I J : Type*} [Fintype I] [Fintype J]
    (D : Matrix I J (ZMod 2)) (hr : D.rank = 0) : D = 0 := by
  classical
  rw [Matrix.rank_eq_finrank_span_cols] at hr
  have hs : Submodule.span (ZMod 2) (Set.range D.col) = ⊥ :=
    Submodule.finrank_eq_zero.mp hr
  ext i j
  have hc : D.col j ∈ Submodule.span (ZMod 2) (Set.range D.col) :=
    Submodule.subset_span ⟨j, rfl⟩
  rw [hs, Submodule.mem_bot] at hc
  exact congrFun hc i

noncomputable def defectMatrix {I X : Type*} (P : I → Prop)
    (F : I → X → Bool) (add : X → X → X) (zero : X) :
    Matrix I (X × X) (ZMod 2) := by
  classical
  exact fun w v => if P w ∧
    xor (xor (F w v.1) (F w v.2)) (xor (F w (add v.1 v.2)) (F w zero)) = true
    then 1 else 0

lemma rank_zero_operand_split {I X : Type*} [Fintype I] [Fintype X]
    (P : I → Prop) (F : I → X → Bool) (add : X → X → X) (zero : X)
    (hr : (defectMatrix P F add zero).rank = 0) (w : I) (hw : P w)
    (x y : X) : F w (add x y) = xor (xor (F w x) (F w y)) (F w zero) := by
  classical
  have he := matrix_eq_zero_of_rank_zero (defectMatrix P F add zero) hr
  have hv : defectMatrix P F add zero w (x, y) = 0 := congrFun (congrFun he w) (x, y)
  apply bool_defect_split
  cases hd : xor (xor (F w x) (F w y)) (xor (F w (add x y)) (F w zero)) with
  | false => rfl
  | true => simp [defectMatrix, hw, hd] at hv

lemma threshold_forces_zero (t r k : ℕ)
    (hbound : 2 * 4^r * k ≤ (4^r + 1) * 4^t)
    (hhigh : 5 * 4^t < 8 * k) : r = 0 := by
  by_contra hr
  have hpow : 4 ≤ 4^r := by
    have hp : 4^1 ≤ 4^r := Nat.pow_le_pow_right (by omega) (by omega)
    simpa using hp
  have hp : 0 < 4^t := by positivity
  nlinarith

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity.NestedCover (ReadsBack gateAt)

lemma operand_lt_total (n : ℕ) (C : Circuit) (hback : ReadsBack n C)
    (g : Gate) (hg : g ∈ C.gates) (w : ℕ) (hw : w ∈ g.inputs) :
    w < n + C.gates.length := by
  obtain ⟨i, hi, hgi⟩ := List.mem_iff_getElem.mp hg
  have hgate : gateAt C i = g := by
    simpa [gateAt, List.getD_eq_getElem, hi] using hgi
  have hw' : w < n + i := hback i hi w (by simpa [hgate] using hw)
  omega

noncomputable def circuitDefect (n : ℕ) (C : Circuit) (nonlinear : Gate → Bool) :
    Matrix (Fin (n + C.gates.length)) ((Fin n → Bool) × (Fin n → Bool)) (ZMod 2) := by
  classical
  let W := fun (w : ℕ) (x : Fin n → Bool) => (C.wires (List.ofFn x)).getD w false
  exact fun w v =>
    if (∃ g ∈ C.gates, nonlinear g = true ∧ w.val ∈ g.inputs) ∧
      xor (xor (W w.val v.1) (W w.val v.2))
        (xor (W w.val (fun i => xor (v.1 i) (v.2 i))) (W w.val (fun _ => false))) = true
    then 1 else 0

lemma circuit_rank_zero_operand_split (n : ℕ) (C : Circuit) (nonlinear : Gate → Bool)
    (hback : ReadsBack n C) (hr : (circuitDefect n C nonlinear).rank = 0)
    (g : Gate) (hg : g ∈ C.gates) (hnl : nonlinear g = true)
    (w : ℕ) (hw : w ∈ g.inputs) (x y : Fin n → Bool) :
    (C.wires (List.ofFn (fun i => xor (x i) (y i)))).getD w false =
      xor (xor ((C.wires (List.ofFn x)).getD w false)
        ((C.wires (List.ofFn y)).getD w false))
        ((C.wires (List.ofFn (fun _ : Fin n => false))).getD w false) := by
  classical
  let wi : Fin (n + C.gates.length) := ⟨w, operand_lt_total n C hback g hg w hw⟩
  let P := fun u : Fin (n + C.gates.length) =>
    ∃ g ∈ C.gates, nonlinear g = true ∧ u.val ∈ g.inputs
  let F := fun (u : Fin (n + C.gates.length)) (x : Fin n → Bool) =>
    (C.wires (List.ofFn x)).getD u.val false
  let add := fun (x y : Fin n → Bool) i => xor (x i) (y i)
  let zero := fun _ : Fin n => false
  have hD : circuitDefect n C nonlinear = defectMatrix P F add zero := by
    ext u v
    simp only [circuitDefect, defectMatrix, P, F, add, zero]
    split_ifs <;> rfl
  rw [hD] at hr
  exact rank_zero_operand_split P F add zero hr wi ⟨g, hg, hnl, hw⟩ x y


def rowRaw {n m : ℕ} (i : Fin n) : Fin (n + m) → Bool :=
  Fin.append (fun k => decide (k = i)) (fun _ => false)

def colRaw {n m : ℕ} (j : Fin m) : Fin (n + m) → Bool :=
  Fin.append (fun _ => false) (fun k => decide (k = j))

lemma rowRaw_xor_colRaw {n m : ℕ} (i : Fin n) (j : Fin m) :
    List.ofFn (fun k => xor (rowRaw i k) (colRaw j k)) =
      PEqualNP.Represents.oneEach i j := by
  have hfun : (fun k => xor (rowRaw i k) (colRaw j k)) =
      Fin.append (fun k => decide (k = i)) (fun k => decide (k = j)) := by
    funext k
    refine Fin.addCases (fun k => ?_) (fun k => ?_) k <;>
      simp [rowRaw, colRaw]
  rw [hfun, List.ofFn_fin_append]
  rfl

def b2z (b : Bool) : ZMod 2 := if b then 1 else 0

lemma b2z_xor (a b : Bool) : b2z (xor a b) = b2z a + b2z b := by
  cases a <;> cases b <;> decide

lemma circuit_rank_zero_operand_promise_split (n m : ℕ) (C : Circuit)
    (nonlinear : Gate → Bool) (hback : ReadsBack (n + m) C)
    (hr : (circuitDefect (n + m) C nonlinear).rank = 0)
    (g : Gate) (hg : g ∈ C.gates) (hnl : nonlinear g = true)
    (w : ℕ) (hw : w ∈ g.inputs) :
    ∃ (r : Fin n → ZMod 2) (s : Fin m → ZMod 2),
      ∀ i j, b2z ((C.wires (PEqualNP.Represents.oneEach i j)).getD w false) = r i + s j := by
  let W := fun x : Fin (n + m) → Bool => (C.wires (List.ofFn x)).getD w false
  refine ⟨fun i => b2z (W (rowRaw i)),
    fun j => b2z (W (colRaw j)) + b2z (W (fun _ => false)), ?_⟩
  intro i j
  have h := circuit_rank_zero_operand_split (n + m) C nonlinear hback hr
    g hg hnl w hw (rowRaw i) (colRaw j)
  rw [rowRaw_xor_colRaw i j] at h
  rw [h, b2z_xor, b2z_xor]
  simp only [W]
  exact add_assoc _ _ _

open PEqualNP.CircuitLowerBounds PEqualNP.Represents
open PEqualNP.MetaComplexity.NestedCover (ReadsBack gateAt)

lemma b2z_inj {a b : Bool} (h : b2z a = b2z b) : a = b := by
  cases a <;> cases b <;> simp [b2z] at h <;> rfl

lemma b2z_and (a b : Bool) : b2z (a && b) = b2z a * b2z b := by
  cases a <;> cases b <;> decide

lemma b2z_not (a : Bool) : b2z (!a) = 1 + b2z a := by
  cases a <;> decide

lemma zmod2_add_self (x : ZMod 2) : x + x = 0 := by
  fin_cases x <;> decide

lemma zmod2_two : (2 : ZMod 2) = 0 := rfl

lemma zmod2_ite_eq (x : ZMod 2) : (if x = 1 then (1 : ZMod 2) else 0) = x := by
  by_cases h : x = 1
  · simp [h]
  · simp only [h, ite_false]
    fin_cases x
    · rfl
    · exact absurd rfl h

def nlGate (g : Gate) : Bool :=
  (g.inputs.length == 2) &&
  xor (xor (g.op.eval [false, false]) (g.op.eval [false, true]))
      (xor (g.op.eval [true, false]) (g.op.eval [true, true]))

def wiresOf (x : List Bool) (gs : List Gate) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

lemma wiresOf_length (x : List Bool) (gs : List Gate) :
    (wiresOf x gs).length = x.length + gs.length := by
  unfold wiresOf
  induction gs generalizing x with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega


lemma wiresOf_append (x : List Bool) (gs1 gs2 : List Gate) :
    wiresOf x (gs1 ++ gs2) =
      gs2.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
        (wiresOf x gs1) := by
  unfold wiresOf
  rw [List.foldl_append]


lemma foldl_append_prefix {α β : Type*} (f : List α → β → α) (l : List β) (init : List α) :
    ∃ ext : List α, l.foldl (fun acc b => acc ++ [f acc b]) init = init ++ ext := by
  induction l generalizing init with
  | nil => exact ⟨[], by simp⟩
  | cons b l ih =>
    rw [List.foldl_cons]
    obtain ⟨ext, hext⟩ := ih (init ++ [f init b])
    exact ⟨f init b :: ext, by rw [hext]; simp⟩

lemma wiresOf_append_getD_lt (x : List Bool) (gs1 gs2 : List Gate) {k : ℕ}
    (hk : k < x.length + gs1.length) :
    (wiresOf x (gs1 ++ gs2)).getD k false = (wiresOf x gs1).getD k false := by
  rw [wiresOf_append]
  obtain ⟨ext, hext⟩ := foldl_append_prefix
    (fun (w : List Bool) (g : Gate) => g.op.eval (g.inputs.map fun i => w.getD i false))
    gs2 (wiresOf x gs1)
  rw [hext, List.getD_append _ _ _ _ (by rw [wiresOf_length]; exact hk)]


lemma wiresOf_getD_input (x : List Bool) (gs : List Gate) {k : ℕ} (hk : k < x.length) :
    (wiresOf x gs).getD k false = x.getD k false := by
  have h := wiresOf_append_getD_lt x [] gs (by simpa using hk)
  simpa [wiresOf] using h


lemma wiresOf_getD_gate (x : List Bool) (gs : List Gate) {idx : ℕ} (hidx : idx < gs.length)
    (hrb : ∀ a ∈ (gs[idx]).inputs, a < x.length + idx) :
    (wiresOf x gs).getD (x.length + idx) false =
      (gs[idx]).op.eval ((gs[idx]).inputs.map fun a => (wiresOf x gs).getD a false) := by
  have hsplit : gs = (gs.take idx ++ [gs[idx]]) ++ gs.drop (idx + 1) := by
    rw [List.take_append_getElem, List.take_append_drop]
  have hlen1 : (gs.take idx).length = idx := List.length_take_of_le (Nat.le_of_lt hidx)
  have hlen2 : (gs.take idx ++ [gs[idx]]).length = idx + 1 := by
    rw [List.length_append, hlen1]
    rfl
  conv_lhs => rw [hsplit]
  rw [wiresOf_append_getD_lt x (gs.take idx ++ [gs[idx]]) (gs.drop (idx + 1)) (by omega)]
  rw [wiresOf_append, List.foldl_cons, List.foldl_nil]
  have hlw : (wiresOf x (gs.take idx)).length = x.length + idx := by
    rw [wiresOf_length, hlen1]
  rw [List.getD_append_right _ _ _ _ (by omega)]
  simp only [hlw, Nat.sub_self, List.getD_cons_zero]
  congr 1
  apply List.map_congr_left
  intro a ha
  have halt : a < x.length + (gs.take idx).length := by rw [hlen1]; exact hrb a ha
  conv_rhs => rw [hsplit]
  rw [wiresOf_append_getD_lt x (gs.take idx ++ [gs[idx]]) (gs.drop (idx + 1)) (by omega)]
  rw [wiresOf_append_getD_lt x (gs.take idx) [gs[idx]] halt]


lemma oneEach_length {n m : ℕ} (i : Fin n) (j : Fin m) :
    (oneEach i j).length = n + m := by
  simp [oneEach]

lemma oneEach_getD_left {n m : ℕ} (i : Fin n) (j : Fin m) {k : ℕ} (hk : k < n) :
    (oneEach i j).getD k false = decide (k = i.val) := by
  unfold oneEach
  rw [List.getD_append _ _ _ _ (by simp [hk])]
  rw [List.getD_eq_getElem _ _ (by simp [hk]), List.getElem_ofFn]
  simp [Fin.ext_iff]

lemma oneEach_getD_right {n m : ℕ} (i : Fin n) (j : Fin m) {k : ℕ} (hk1 : n ≤ k)
    (hk2 : k < n + m) :
    (oneEach i j).getD k false = decide (k - n = j.val) := by
  unfold oneEach
  rw [List.getD_append_right _ _ _ _ (by simp [hk1])]
  simp only [List.length_ofFn]
  rw [List.getD_eq_getElem _ _ (by simp; omega), List.getElem_ofFn]
  simp [Fin.ext_iff]

lemma anf_one (f : Bool → Bool) (x : Bool) :
    b2z (f x) = b2z (f false) + (b2z (f false) + b2z (f true)) * b2z x := by
  cases x <;> cases h0 : f false <;> cases h1 : f true <;> decide

lemma anf_two (f : Bool → Bool → Bool) (x y : Bool) :
    b2z (f x y) =
      b2z (f false false) +
      (b2z (f false false) + b2z (f true false)) * b2z x +
      (b2z (f false false) + b2z (f false true)) * b2z y +
      b2z (xor (xor (f false false) (f false true)) (xor (f true false) (f true true))) *
        (b2z x * b2z y) := by
  cases x <;> cases y <;>
    cases h00 : f false false <;> cases h01 : f false true <;>
    cases h10 : f true false <;> cases h11 : f true true <;> decide

def anchor {n m : ℕ} (u : Fin n) (v : Fin m) (h : Fin n → Fin m → ZMod 2) :
    Matrix (Fin n) (Fin m) (ZMod 2) :=
  fun i j => h i j + h i v + h u j + h u v

lemma anchor_const {n m : ℕ} (u : Fin n) (v : Fin m) (c : ZMod 2) :
    anchor u v (fun _ _ => c) = 0 := by
  ext i j
  simp only [anchor, Matrix.zero_apply]
  simp [zmod2_add_self]

lemma anchor_split {n m : ℕ} (u : Fin n) (v : Fin m) (r : Fin n → ZMod 2) (s : Fin m → ZMod 2) :
    anchor u v (fun i j => r i + s j) = 0 := by
  ext i j
  simp only [anchor, Matrix.zero_apply]
  have h : (r i + s j) + (r i + s v) + (r u + s j) + (r u + s v) =
      (r i + r i) + (r u + r u) + (s j + s j) + (s v + s v) := by ring
  simp [h, zmod2_add_self]

lemma anchor_add {n m : ℕ} (u : Fin n) (v : Fin m) (h1 h2 : Fin n → Fin m → ZMod 2) :
    anchor u v (fun i j => h1 i j + h2 i j) = anchor u v h1 + anchor u v h2 := by
  ext i j
  simp only [anchor, Matrix.add_apply]

  ring

lemma anchor_smul {n m : ℕ} (u : Fin n) (v : Fin m) (c : ZMod 2) (h : Fin n → Fin m → ZMod 2) :
    anchor u v (fun i j => c * h i j) = c • anchor u v h := by
  ext i j
  simp only [anchor, Matrix.smul_apply, smul_eq_mul]
  ring

lemma anchor_prod_split {n m : ℕ} (u : Fin n) (v : Fin m)
    (r1 r2 : Fin n → ZMod 2) (s1 s2 : Fin m → ZMod 2) :
    anchor u v (fun i j => (r1 i + s1 j) * (r2 i + s2 j)) =
      Matrix.vecMulVec (fun i => r1 i + r1 u) (fun j => s2 j + s2 v) +
      Matrix.vecMulVec (fun i => r2 i + r2 u) (fun j => s1 j + s1 v) := by
  ext i j
  simp only [anchor, Matrix.add_apply, Matrix.vecMulVec_apply]
  have h : ((r1 i + s1 j) * (r2 i + s2 j) + (r1 i + s1 v) * (r2 i + s2 v) +
      (r1 u + s1 j) * (r2 u + s2 j) + (r1 u + s1 v) * (r2 u + s2 v)) +
      ((r1 i + r1 u) * (s2 j + s2 v) + (r2 i + r2 u) * (s1 j + s1 v)) =
      (2 : ZMod 2) * (r1 i * r2 i + r1 u * r2 u + s1 j * s2 j + s1 v * s2 v +
        r1 i * s2 j + r1 i * s2 v + r1 u * s2 j + r1 u * s2 v +
        r2 i * s1 j + r2 i * s1 v + r2 u * s1 j + r2 u * s1 v) := by ring
  rw [zmod2_two, zero_mul] at h
  have hsub : ∀ a b : ZMod 2, a + b = 0 → a = b := by
    intro a b hab
    calc a = a + 0 := (add_zero a).symm
      _ = a + (b + b) := by rw [zmod2_add_self]
      _ = (a + b) + b := by ring
      _ = 0 + b := by rw [hab]
      _ = b := zero_add b
  exact hsub _ _ h

lemma rank_of_factor {n m K : ℕ} (P : Matrix (Fin n) (Fin K) (ZMod 2))
    (Q : Matrix (Fin K) (Fin m) (ZMod 2)) : (P * Q).rank ≤ K := by
  calc (P * Q).rank ≤ P.rank := Matrix.rank_mul_le_left P Q
    _ = Module.finrank (ZMod 2) (LinearMap.range P.mulVecLin) := rfl
    _ ≤ Module.finrank (ZMod 2) (Fin K → ZMod 2) := LinearMap.finrank_range_le P.mulVecLin
    _ = K := Module.finrank_fin_fun (ZMod 2)

lemma factor_of_rank_le {n m K : ℕ} (A : Matrix (Fin n) (Fin m) (ZMod 2)) (h : A.rank ≤ K) :
    ∃ (rowVec : Fin K → Fin n → ZMod 2) (colVec : Fin K → Fin m → ZMod 2),
      ∀ i j, A i j = ∑ k : Fin K, rowVec k i * colVec k j := by
  let r := A.rank
  let b := Module.finBasisOfFinrankEq (ZMod 2) (LinearMap.range A.mulVecLin)
    (rfl : Module.finrank (ZMod 2) (LinearMap.range A.mulVecLin) = r)
  have hcol : ∀ j : Fin m, (fun i => A i j) ∈ LinearMap.range A.mulVecLin := by
    intro j
    refine ⟨Pi.single j 1, ?_⟩
    ext i
    simp [Matrix.mulVec_single]
  let rowVec : Fin K → Fin n → ZMod 2 := fun k i =>
    if hk : k.val < r then (b ⟨k.val, hk⟩).val i else 0
  let colVec : Fin K → Fin m → ZMod 2 := fun k j =>
    if hk : k.val < r then b.repr ⟨fun i => A i j, hcol j⟩ ⟨k.val, hk⟩ else 0
  refine ⟨rowVec, colVec, fun i j => ?_⟩
  have hrepr : ∑ t : Fin r, (b.repr ⟨fun i => A i j, hcol j⟩ t) • (b t) =
      ⟨fun i => A i j, hcol j⟩ := b.sum_repr ⟨fun i => A i j, hcol j⟩
  have heval : A i j = ∑ t : Fin r, (b t).val i * b.repr ⟨fun i => A i j, hcol j⟩ t := by
    have h1 := congrArg (fun (v : LinearMap.range A.mulVecLin) => v.val i) hrepr
    simp only [Submodule.coe_sum, Finset.sum_apply, Submodule.coe_smul_of_tower,
      Pi.smul_apply, smul_eq_mul] at h1
    rw [← h1]
    refine Finset.sum_congr rfl fun t _ => mul_comm _ _
  rw [heval]
  symm
  have hfilt : ∑ k : Fin K, rowVec k i * colVec k j =
      ∑ k ∈ Finset.univ.filter (fun k : Fin K => k.val < r), rowVec k i * colVec k j := by
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro k _ hnk
    rw [Finset.mem_filter] at hnk
    have hge : ¬ k.val < r := fun hk => hnk ⟨Finset.mem_univ k, hk⟩
    simp [rowVec, colVec, hge]
  rw [hfilt]
  refine Finset.sum_bij (fun k hk => ⟨k.val, (Finset.mem_filter.mp hk).2⟩) ?_ ?_ ?_ ?_
  · intro _ _
    exact Finset.mem_univ _
  · intro k1 _ k2 _ heq
    exact Fin.ext (Fin.mk.inj heq)
  · intro t _
    refine ⟨⟨t.val, Nat.lt_of_lt_of_le t.isLt h⟩,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, t.isLt⟩, Fin.ext rfl⟩
  · intro k hk
    have hlt : k.val < r := (Finset.mem_filter.mp hk).2
    simp only [rowVec, colVec, hlt, dite_true]
    rfl

lemma card_filter_fin_eq_countP {α : Type*} (l : List α) (p : α → Bool) :
    (Finset.univ.filter (fun idx : Fin l.length => p l[idx.val] = true)).card = l.countP p := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.countP_cons]
    have hsplit : (Finset.univ.filter (fun idx : Fin (a :: l).length => p (a :: l)[idx.val] = true)).card =
        (if p a = true then 1 else 0) +
        (Finset.univ.filter (fun idx : Fin l.length => p l[idx.val] = true)).card := by
      have hsum : ∀ (S : Finset (Fin (l.length + 1))), S.card =
          (if (0 : Fin (l.length + 1)) ∈ S then 1 else 0) +
          (Finset.univ.filter (fun idx : Fin l.length => idx.succ ∈ S)).card := by
        intro S
        have h1 : S.card = ∑ x : Fin (l.length + 1), if x ∈ S then 1 else 0 := by
          simp
        rw [h1, Fin.sum_univ_succ]
        congr 1
        simp
      have h2 := hsum (Finset.univ.filter (fun idx : Fin (a :: l).length => p (a :: l)[idx.val] = true))
      simpa using h2
    rw [hsplit, ih]
    cases p a <;> simp [Nat.add_comm]


lemma dir_split_le {n m : ℕ} (G : Fin n → Fin m → Bool) (u : Fin n) (v : Fin m) (t : ℕ)
    (C : Circuit)
    (hlen : ∀ g ∈ C.gates, g.inputs.length ≤ 2)
    (hrb : ReadsBack (n + m) C)
    (hrep : Represents G C)
    (hsplit : ∀ g ∈ C.gates, nlGate g = true → ∀ k ∈ g.inputs,
      ∃ (r : Fin n → ZMod 2) (s : Fin m → ZMod 2), ∀ i j,
        b2z ((C.wires (oneEach i j)).getD k false) = r i + s j)
    (hcnt : C.gates.countP nlGate ≤ t) :
    (anchor u v (fun i j => b2z (G i j))).rank ≤ 2 * t := by
  let val : ℕ → Fin n → Fin m → ZMod 2 :=
    fun k i j => b2z ((wiresOf (oneEach i j) C.gates).getD k false)
  have hrb' : ∀ (idx : ℕ) (hidx : idx < C.gates.length),
      ∀ a ∈ (C.gates[idx]).inputs, a < n + m + idx := by
    intro idx hidx a ha
    have h := hrb idx hidx a
    unfold gateAt at h
    rw [List.getD_eq_getElem _ _ hidx] at h
    exact h ha
  have hval_gate : ∀ (idx : ℕ) (hidx : idx < C.gates.length) (i : Fin n) (j : Fin m),
      val (n + m + idx) i j =
        b2z ((C.gates[idx]).op.eval ((C.gates[idx]).inputs.map fun a =>
          (wiresOf (oneEach i j) C.gates).getD a false)) := by
    intro idx hidx i j
    unfold val
    have h := wiresOf_getD_gate (oneEach i j) C.gates hidx (by
      intro a ha
      rw [oneEach_length]
      exact hrb' idx hidx a ha)
    rw [oneEach_length] at h
    rw [h]

  let NL : Finset (Fin C.gates.length) :=
    Finset.univ.filter (fun idx => nlGate (C.gates[idx.val]) = true)
  have hNL_card : NL.card ≤ t := by
    calc NL.card
        = C.gates.countP nlGate := card_filter_fin_eq_countP C.gates nlGate
      _ ≤ t := hcnt

  have hNL_outer : ∀ idx ∈ NL,
      ∃ (r1 r2 : Fin n → ZMod 2) (s1 s2 : Fin m → ZMod 2),
        anchor u v (val (n + m + idx.val)) =

          Matrix.vecMulVec r1 s1 + Matrix.vecMulVec r2 s2 := by
    intro idx hidx_mem
    have hnl : nlGate (C.gates[idx.val]) = true := (Finset.mem_filter.mp hidx_mem).2
    let g := C.gates[idx.val]
    have hlen2 : g.inputs.length = 2 := by
      unfold nlGate at hnl
      rw [Bool.and_eq_true] at hnl
      simpa using hnl.1
    obtain ⟨a, b, hab⟩ : ∃ a b, g.inputs = [a, b] := by
      match h : g.inputs with
      | [a, b] => exact ⟨a, b, rfl⟩
      | [] => rw [h] at hlen2; simp at hlen2
      | [_] => rw [h] at hlen2; simp at hlen2
      | _ :: _ :: _ :: _ => rw [h] at hlen2; simp at hlen2
    have hgm : g ∈ C.gates := List.getElem_mem idx.isLt
    obtain ⟨r1, s1, h1⟩ := hsplit g hgm hnl a (by rw [hab]; simp)
    obtain ⟨r2, s2, h2⟩ := hsplit g hgm hnl b (by rw [hab]; simp)
    change ∀ i j, val a i j = r1 i + s1 j at h1
    change ∀ i j, val b i j = r2 i + s2 j at h2
    have hxor : xor (xor (g.op.eval [false, false]) (g.op.eval [false, true]))
        (xor (g.op.eval [true, false]) (g.op.eval [true, true])) = true := by
      unfold nlGate at hnl
      rw [Bool.and_eq_true] at hnl
      exact hnl.2
    let c0 := b2z (g.op.eval [false, false])
    let c1 := b2z (g.op.eval [false, false]) + b2z (g.op.eval [true, false])
    let c2 := b2z (g.op.eval [false, false]) + b2z (g.op.eval [false, true])
    have hfun : val (n + m + idx.val) = fun i j =>
        (c0 + c1 * r1 i + c2 * r2 i + (c1 * s1 j + c2 * s2 j)) +
        (r1 i + s1 j) * (r2 i + s2 j) := by
      funext i j
      rw [hval_gate idx.val idx.isLt i j]
      change b2z (g.op.eval (g.inputs.map _)) = _
      rw [hab, List.map_cons, List.map_cons, List.map_nil]
      have hanf := anf_two (fun x y => g.op.eval [x, y])
        ((wiresOf (oneEach i j) C.gates).getD a false)
        ((wiresOf (oneEach i j) C.gates).getD b false)
      rw [hxor] at hanf
      have hbt : b2z true = 1 := rfl
      change b2z (g.op.eval [_, _]) = c0 + c1 * val a i j + c2 * val b i j + b2z true * (val a i j * val b i j) at hanf
      rw [hbt, one_mul] at hanf
      rw [hanf, h1 i j, h2 i j]
      ring
    refine ⟨fun i => r1 i + r1 u, fun i => r2 i + r2 u, fun j => s2 j + s2 v, fun j => s1 j + s1 v, ?_⟩
    rw [hfun, anchor_add, anchor_split, zero_add, anchor_prod_split]

  have hspan : ∀ k : ℕ,
      ∃ coeff : Fin C.gates.length → ZMod 2,
        anchor u v (val k) = ∑ idx ∈ NL, coeff idx • anchor u v (val (n + m + idx.val)) := by
    intro k
    induction k using Nat.strong_induction_on with
    | ind k ih =>
      by_cases hk1 : k < n + m
      · have hs : ∃ (r : Fin n → ZMod 2) (s : Fin m → ZMod 2),
            ∀ i j, val k i j = r i + s j := by
          by_cases hk0 : k < n
          · refine ⟨fun i => b2z (decide (k = i.val)), fun _ => 0, fun i j => ?_⟩
            unfold val
            rw [wiresOf_getD_input _ _ (by rw [oneEach_length]; exact hk1),
              oneEach_getD_left i j hk0, add_zero]
          · refine ⟨fun _ => 0, fun j => b2z (decide (k - n = j.val)), fun i j => ?_⟩
            unfold val
            rw [wiresOf_getD_input _ _ (by rw [oneEach_length]; exact hk1),
              oneEach_getD_right i j (by omega) hk1, zero_add]
        obtain ⟨r, s, hrs⟩ := hs
        refine ⟨fun _ => 0, ?_⟩
        have hfun : val k = fun i j => r i + s j := by funext i j; exact hrs i j
        rw [hfun, anchor_split]
        simp
      · by_cases hk2 : k < n + m + C.gates.length
        · let idx : Fin C.gates.length := ⟨k - (n + m), by omega⟩
          have hkeq : k = n + m + idx.val := by simp [idx]; omega
          rw [hkeq]
          let g := C.gates[idx.val]
          by_cases hnl : nlGate g = true
          · have hmem : idx ∈ NL := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hnl⟩
            refine ⟨fun idx' => if idx' = idx then 1 else 0, ?_⟩
            rw [Finset.sum_eq_single idx]
            · simp
            · intro idx' _ hne
              simp [hne]
            · intro h
              exact absurd hmem h
          · have hnlf : nlGate g = false := by cases h : nlGate g <;> simp_all
            have hgl : g.inputs.length ≤ 2 := hlen g (List.getElem_mem idx.isLt)

            match hg_in : g.inputs with
            | [] =>
              refine ⟨fun _ => 0, ?_⟩
              have hfun : val (n + m + idx.val) = fun _ _ => b2z (g.op.eval []) := by
                funext i j
                rw [hval_gate idx.val idx.isLt i j]
                change b2z (g.op.eval (g.inputs.map _)) = _
                rw [hg_in, List.map_nil]
              rw [hfun, anchor_const]
              simp
            | [a] =>
              have ha_lt : a < n + m + idx.val := hrb' idx.val idx.isLt a (by rw [hg_in]; simp)
              obtain ⟨ca, hca⟩ := ih a (by omega)
              let c0 := b2z (g.op.eval [false])
              let c1 := b2z (g.op.eval [false]) + b2z (g.op.eval [true])
              refine ⟨fun idx' => c1 * ca idx', ?_⟩
              have hfun : val (n + m + idx.val) = fun i j => c0 + c1 * val a i j := by
                funext i j
                rw [hval_gate idx.val idx.isLt i j]
                change b2z (g.op.eval (g.inputs.map _)) = _
                rw [hg_in, List.map_cons, List.map_nil]
                exact anf_one (fun x => g.op.eval [x]) ((wiresOf (oneEach i j) C.gates).getD a false)
              rw [hfun, anchor_add, anchor_const, zero_add, anchor_smul, hca, Finset.smul_sum]
              refine Finset.sum_congr rfl fun idx' _ => by rw [smul_smul]
            | [a, b] =>
              have ha_lt : a < n + m + idx.val := hrb' idx.val idx.isLt a (by rw [hg_in]; simp)
              have hb_lt : b < n + m + idx.val := hrb' idx.val idx.isLt b (by rw [hg_in]; simp)
              obtain ⟨ca, hca⟩ := ih a (by omega)
              obtain ⟨cb, hcb⟩ := ih b (by omega)
              have hxor : xor (xor (g.op.eval [false, false]) (g.op.eval [false, true]))
                  (xor (g.op.eval [true, false]) (g.op.eval [true, true])) = false := by
                unfold nlGate at hnlf
                rw [hg_in] at hnlf
                simpa using hnlf
              let c0 := b2z (g.op.eval [false, false])
              let c1 := b2z (g.op.eval [false, false]) + b2z (g.op.eval [true, false])
              let c2 := b2z (g.op.eval [false, false]) + b2z (g.op.eval [false, true])
              refine ⟨fun idx' => c1 * ca idx' + c2 * cb idx', ?_⟩
              have hfun : val (n + m + idx.val) = fun i j => (c0 + c1 * val a i j) + c2 * val b i j := by
                funext i j
                rw [hval_gate idx.val idx.isLt i j]
                change b2z (g.op.eval (g.inputs.map _)) = _
                rw [hg_in, List.map_cons, List.map_cons, List.map_nil]
                have hanf := anf_two (fun x y => g.op.eval [x, y])
                  ((wiresOf (oneEach i j) C.gates).getD a false)
                  ((wiresOf (oneEach i j) C.gates).getD b false)
                rw [hxor] at hanf

                have hbf : b2z false = 0 := rfl
                change b2z (g.op.eval [_, _]) = c0 + c1 * val a i j + c2 * val b i j + b2z false * _ at hanf
                rw [hbf, zero_mul, add_zero] at hanf
                exact hanf
              rw [hfun, anchor_add, anchor_add, anchor_const, zero_add, anchor_smul, anchor_smul,
                hca, hcb, Finset.smul_sum, Finset.smul_sum, ← Finset.sum_add_distrib]
              refine Finset.sum_congr rfl fun idx' _ => by
                rw [smul_smul, smul_smul, ← add_smul]
            | _ :: _ :: _ :: _ =>
              rw [hg_in] at hgl
              simp at hgl

        · refine ⟨fun _ => 0, ?_⟩
          have hfun : val k = fun _ _ => 0 := by
            funext i j
            unfold val
            have hge : (wiresOf (oneEach i j) C.gates).length ≤ k := by
              rw [wiresOf_length, oneEach_length]
              omega
            rw [List.getD_eq_default _ _ hge]
            rfl
          rw [hfun, anchor_const]
          simp

  obtain ⟨coeff, hcoeff⟩ := hspan C.output
  have hAeq : anchor u v (fun i j => b2z (G i j)) = anchor u v (val C.output) := by
    congr 1
    funext i j
    unfold val
    rw [← hrep i j]
    rfl
  rw [hAeq, hcoeff]
  choose r1 r2 s1 s2 houter using fun idx : NL => hNL_outer idx.val idx.property
  let P : Matrix (Fin n) (NL ⊕ NL) (ZMod 2) := fun i k =>
    match k with
    | Sum.inl idx => coeff idx.val * r1 idx i
    | Sum.inr idx => coeff idx.val * r2 idx i
  let Q : Matrix (NL ⊕ NL) (Fin m) (ZMod 2) := fun k j =>
    match k with
    | Sum.inl idx => s1 idx j
    | Sum.inr idx => s2 idx j
  have hPQ : ∑ idx ∈ NL, coeff idx • anchor u v (val (n + m + idx.val)) = P * Q := by
    ext i j
    rw [Matrix.mul_apply, Fintype.sum_sum_type, ← Finset.sum_add_distrib]
    simp only [Matrix.sum_apply]
    rw [← Finset.sum_attach NL]
    refine Finset.sum_congr rfl fun idx _ => ?_
    simp only [Matrix.smul_apply, smul_eq_mul, houter idx, Matrix.add_apply,
      Matrix.vecMulVec_apply, P, Q]
    ring
  rw [hPQ]
  calc (P * Q).rank ≤ P.rank := Matrix.rank_mul_le_left P Q
    _ = Module.finrank (ZMod 2) (LinearMap.range P.mulVecLin) := rfl
    _ ≤ Module.finrank (ZMod 2) (NL ⊕ NL → ZMod 2) := LinearMap.finrank_range_le P.mulVecLin
    _ = Fintype.card (NL ⊕ NL) := Module.finrank_pi (ZMod 2)
    _ = NL.card + NL.card := by simp
    _ ≤ 2 * t := by omega



lemma factor_bool_of_anchor_rank {n m t : ℕ} (G : Fin n → Fin m → Bool)
    (u : Fin n) (v : Fin m)
    (hr : (anchor u v (fun i j => b2z (G i j))).rank ≤ 2 * t) :
    ∃ (row : Fin n → Fin (2 * t) → ZMod 2)
      (col : Fin m → Fin (2 * t) → ZMod 2)
      (Q : Fin n → Bool) (R : Fin m → Bool),
      ∀ i j, G i j = xor (xor (Q i) (R j))
        (decide ((∑ b : Fin (2 * t), row i b * col j b) = 1)) := by
  obtain ⟨rowVec, colVec, hfac⟩ :=
    factor_of_rank_le (anchor u v (fun i j => b2z (G i j))) hr
  refine ⟨(fun i b => rowVec b i), (fun j b => colVec b j),
    (fun i => G i v), (fun j => xor (G u j) (G u v)), ?_⟩
  intro i j
  apply b2z_inj
  rw [b2z_xor, b2z_xor, b2z_xor]
  have hdec : b2z (decide ((∑ b : Fin (2 * t), rowVec b i * colVec b j) = 1)) =
      ∑ b : Fin (2 * t), rowVec b i * colVec b j := by
    simpa only [b2z, decide_eq_true_eq] using
      zmod2_ite_eq (∑ b : Fin (2 * t), rowVec b i * colVec b j)
  rw [hdec, ← hfac]
  simp only [anchor]
  have hsum : b2z (G i v) + (b2z (G u j) + b2z (G u v)) +
      (b2z (G i j) + b2z (G i v) + b2z (G u j) + b2z (G u v)) =
      b2z (G i j) + (2 : ZMod 2) * (b2z (G i v) + b2z (G u j) + b2z (G u v)) := by
    ring
  rw [hsum, zmod2_two, zero_mul, add_zero]


lemma factor_of_operand_split {n m : ℕ} (C : Circuit)
    (hlen : ∀ g ∈ C.gates, g.inputs.length ≤ 2)
    (hrb : ReadsBack (n + m) C)
    (hsplit : ∀ g ∈ C.gates, nlGate g = true → ∀ k ∈ g.inputs,
      ∃ (r : Fin n → ZMod 2) (s : Fin m → ZMod 2), ∀ i j,
        b2z ((C.wires (oneEach i j)).getD k false) = r i + s j) :
    let t := C.gates.countP nlGate
    ∃ (row : Fin n → Fin (2 * t) → ZMod 2)
      (col : Fin m → Fin (2 * t) → ZMod 2)
      (Q : Fin n → Bool) (R : Fin m → Bool),
      ∀ i j, C.eval (oneEach i j) = xor (xor (Q i) (R j))
        (decide ((∑ b : Fin (2 * t), row i b * col j b) = 1)) := by
  classical
  dsimp only
  by_cases hn : n = 0
  · subst n
    exact ⟨fun _ _ => 0, fun _ _ => 0, fun _ => false, fun _ => false,
      fun i => Fin.elim0 i⟩
  by_cases hm : m = 0
  · subst m
    exact ⟨fun _ _ => 0, fun _ _ => 0, fun _ => false, fun _ => false,
      fun _ j => Fin.elim0 j⟩
  let u : Fin n := ⟨0, Nat.pos_of_ne_zero hn⟩
  let v : Fin m := ⟨0, Nat.pos_of_ne_zero hm⟩
  have hrep : Represents (fun (i : Fin n) (j : Fin m) => C.eval (oneEach i j)) C := fun _ _ => rfl
  have hr := dir_split_le (fun i j => C.eval (oneEach i j)) u v
    (C.gates.countP nlGate) C hlen hrb hrep hsplit (le_refl _)
  exact factor_bool_of_anchor_rank (fun i j => C.eval (oneEach i j)) u v hr

lemma factor_of_zero_defect {n m : ℕ} (C : Circuit)
    (hlen : ∀ g ∈ C.gates, g.inputs.length ≤ 2)
    (hrb : ReadsBack (n + m) C)
    (hr : (circuitDefect (n + m) C nlGate).rank = 0) :
    let t := C.gates.countP nlGate
    ∃ (row : Fin n → Fin (2 * t) → ZMod 2)
      (col : Fin m → Fin (2 * t) → ZMod 2)
      (Q : Fin n → Bool) (R : Fin m → Bool),
      ∀ i j, C.eval (oneEach i j) = xor (xor (Q i) (R j))
        (decide ((∑ b : Fin (2 * t), row i b * col j b) = 1)) := by
  apply factor_of_operand_split C hlen hrb
  exact circuit_rank_zero_operand_promise_split n m C nlGate hrb hr

open scoped BigOperators


abbrev Cube (t : ℕ) := (Fin t → ZMod 2) × (Fin t → ZMod 2)

def triangular {t : ℕ} (A B : Fin t → Fin t → ZMod 2)
    (y : Cube t) :
    Cube t :=
  (fun i => y.1 i + ∑ j : Fin t, A i j * y.1 j * y.2 j,
   fun i => y.2 i + ∑ j : Fin t, B i j * y.1 j * y.2 j)

lemma triangular_injective {t : ℕ} (A B : Fin t → Fin t → ZMod 2)
    (hA : ∀ i j, ¬ j < i → A i j = 0)
    (hB : ∀ i j, ¬ j < i → B i j = 0) :
    Function.Injective (triangular A B) := by
  intro y z h
  have coord : ∀ k : ℕ, ∀ hk : k < t,
      y.1 ⟨k, hk⟩ = z.1 ⟨k, hk⟩ ∧ y.2 ⟨k, hk⟩ = z.2 ⟨k, hk⟩ := by
    intro k
    induction k using Nat.strong_induction_on with
    | ind k ih =>
      intro hk
      let i : Fin t := ⟨k, hk⟩
      have sumA : (∑ j : Fin t, A i j * y.1 j * y.2 j) =
          ∑ j : Fin t, A i j * z.1 j * z.2 j := by
        apply Finset.sum_congr rfl
        intro j _
        by_cases hj : j < i
        · have hjk : j.val < k := hj
          obtain ⟨hy, hz⟩ := ih j.val hjk j.isLt
          rw [hy, hz]
        · simp only [hA i j hj, zero_mul]
      have sumB : (∑ j : Fin t, B i j * y.1 j * y.2 j) =
          ∑ j : Fin t, B i j * z.1 j * z.2 j := by
        apply Finset.sum_congr rfl
        intro j _
        by_cases hj : j < i
        · have hjk : j.val < k := hj
          obtain ⟨hy, hz⟩ := ih j.val hjk j.isLt
          rw [hy, hz]
        · simp only [hB i j hj, zero_mul]
      have eqA := congrFun (congrArg Prod.fst h) i
      have eqB := congrFun (congrArg Prod.snd h) i
      change y.1 i + _ = z.1 i + _ at eqA
      change y.2 i + _ = z.2 i + _ at eqB
      rw [sumA] at eqA
      rw [sumB] at eqB
      exact ⟨add_right_cancel eqA, add_right_cancel eqB⟩
  apply Prod.ext
  · funext i
    exact (coord i.val i.isLt).1
  · funext i
    exact (coord i.val i.isLt).2

lemma triangular_bijective {t : ℕ} (A B : Fin t → Fin t → ZMod 2)
    (hA : ∀ i j, ¬ j < i → A i j = 0)
    (hB : ∀ i j, ¬ j < i → B i j = 0) :
    Function.Bijective (triangular A B) :=
  Finite.injective_iff_bijective.mp (triangular_injective A B hA hB)

noncomputable def triangularEquiv {t : ℕ} (A B : Fin t → Fin t → ZMod 2)
    (hA : ∀ i j, ¬ j < i → A i j = 0)
    (hB : ∀ i j, ¬ j < i → B i j = 0) :
    Cube t ≃ Cube t :=
  Equiv.ofBijective (triangular A B) (triangular_bijective A B hA hB)

lemma triangularEquiv_apply {t : ℕ} (A B : Fin t → Fin t → ZMod 2)
    (hA : ∀ i j, ¬ j < i → A i j = 0)
    (hB : ∀ i j, ¬ j < i → B i j = 0)
    (y : Cube t) :
    triangularEquiv A B hA hB y = triangular A B y := rfl

open scoped BigOperators

def sign2 (z : ZMod 2) : ℚ := if z = 0 then 1 else -1

lemma fpZmodCases (z : ZMod 2) : z = 0 ∨ z = 1 := by
  fin_cases z
  · exact Or.inl rfl
  · exact Or.inr rfl

lemma fpSumZmod (f : ZMod 2 → ℚ) : (∑ z, f z) = f 0 + f 1 := by
  exact Fin.sum_univ_two f

lemma sign2_add (a b : ZMod 2) :
    sign2 (a + b) = sign2 a * sign2 b := by
  have h11 : (1 : ZMod 2) + 1 = 0 := by decide
  have h2 : (2 : ZMod 2) = 0 := by decide
  have h3 : (3 : ZMod 2) = 1 := by decide
  rcases fpZmodCases a with rfl | rfl <;>
    rcases fpZmodCases b with rfl | rfl <;> simp [sign2, h11]

lemma sum_sign2 {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (f : ι → ZMod 2) :
    sign2 (∑ i ∈ s, f i) = ∏ i ∈ s, sign2 (f i) := by
  induction s using Finset.induction_on with
  | empty => simp [sign2]
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha, sign2_add, Finset.prod_insert ha, ih]

def localFourier (k a b : ZMod 2) : ℚ :=
  ∑ p : ZMod 2 × ZMod 2,
    sign2 (k * p.1 * p.2 + a * p.1 + b * p.2)

lemma localFourier_eq (k a b : ZMod 2) :
    localFourier k a b =
      if k = 1 then (if a * b = 0 then 2 else -2)
      else (if a = 0 ∧ b = 0 then 4 else 0) := by
  have h11 : (1 : ZMod 2) + 1 = 0 := by decide
  have h2 : (2 : ZMod 2) = 0 := by decide
  have h3 : (3 : ZMod 2) = 1 := by decide
  rcases fpZmodCases k with rfl | rfl <;>
    rcases fpZmodCases a with rfl | rfl <;>
    rcases fpZmodCases b with rfl | rfl <;>
    simp [localFourier, Fintype.sum_prod_type, fpSumZmod, sign2, h11] <;> norm_num

lemma localFourier_ne_zero_iff (k a b : ZMod 2) :
    localFourier k a b ≠ 0 ↔ k = 1 ∨ (a = 0 ∧ b = 0) := by
  rw [localFourier_eq]
  rcases fpZmodCases k with rfl | rfl <;>
    rcases fpZmodCases a with rfl | rfl <;>
    rcases fpZmodCases b with rfl | rfl <;> norm_num

def pairPiEquiv (t : ℕ) :
    ((Fin t → ZMod 2) × (Fin t → ZMod 2)) ≃ (Fin t → ZMod 2 × ZMod 2) where
  toFun y i := (y.1 i, y.2 i)
  invFun y := (fun i => (y i).1, fun i => (y i).2)
  left_inv := by
    rintro ⟨a, b⟩
    rfl
  right_inv := by
    intro y
    funext i
    rfl

lemma fourier_product (t : ℕ) (k : Fin t → ZMod 2)
    (s : (Fin t → ZMod 2) × (Fin t → ZMod 2)) :
    (∑ y : (Fin t → ZMod 2) × (Fin t → ZMod 2),
      sign2 (Finset.univ.sum (fun i : Fin t =>
        k i * y.1 i * y.2 i + s.1 i * y.1 i + s.2 i * y.2 i))) =
      ∏ i, localFourier (k i) (s.1 i) (s.2 i) := by
  classical
  calc
    (∑ y : (Fin t → ZMod 2) × (Fin t → ZMod 2),
      sign2 (Finset.univ.sum (fun i : Fin t =>
        k i * y.1 i * y.2 i + s.1 i * y.1 i + s.2 i * y.2 i))) =
        ∑ y : Fin t → ZMod 2 × ZMod 2,
          sign2 (Finset.univ.sum (fun i : Fin t =>
            k i * (y i).1 * (y i).2 + s.1 i * (y i).1 + s.2 i * (y i).2)) := by
              refine Fintype.sum_equiv (pairPiEquiv t) _ _ ?_
              intro y
              rfl
    _ = ∑ y : Fin t → ZMod 2 × ZMod 2,
        ∏ i, sign2
          (k i * (y i).1 * (y i).2 + s.1 i * (y i).1 + s.2 i * (y i).2) := by
            apply Finset.sum_congr rfl
            intro y _
            exact sum_sign2 Finset.univ _
    _ = ∏ i, localFourier (k i) (s.1 i) (s.2 i) := by
      exact (Fintype.prod_sum (fun (i : Fin t) (p : ZMod 2 × ZMod 2) =>
        sign2 (k i * p.1 * p.2 + s.1 i * p.1 + s.2 i * p.2))).symm

lemma fourier_product_ne_zero_iff (t : ℕ) (k : Fin t → ZMod 2)
    (s : (Fin t → ZMod 2) × (Fin t → ZMod 2)) :
    (∑ y : (Fin t → ZMod 2) × (Fin t → ZMod 2),
      sign2 (Finset.univ.sum (fun i : Fin t =>
        k i * y.1 i * y.2 i + s.1 i * y.1 i + s.2 i * y.2 i))) ≠ 0 ↔
      ∀ i, k i = 1 ∨ (s.1 i = 0 ∧ s.2 i = 0) := by
  rw [fourier_product]
  simp only [Finset.prod_ne_zero_iff, Finset.mem_univ, forall_const,
    localFourier_ne_zero_iff]

open scoped BigOperators


lemma decoder_phase {t : ℕ}
    (A B : Fin t → Fin t → ZMod 2) (c : Fin t → ZMod 2)
    (s y : (Fin t → ZMod 2) × (Fin t → ZMod 2)) :
    (∑ i : Fin t, c i * y.1 i * y.2 i) +
      (∑ i : Fin t, (s.1 i * (y.1 i + ∑ j : Fin t, A i j * y.1 j * y.2 j) +
        s.2 i * (y.2 i + ∑ j : Fin t, B i j * y.1 j * y.2 j))) =
      ∑ j : Fin t, ((c j + ∑ i : Fin t, (s.1 i * A i j + s.2 i * B i j)) * y.1 j * y.2 j +
        s.1 j * y.1 j + s.2 j * y.2 j) := by
  have hswapA :
      (∑ i : Fin t, s.1 i * ∑ j : Fin t, A i j * y.1 j * y.2 j) =
      ∑ j : Fin t, (∑ i : Fin t, s.1 i * A i j) * y.1 j * y.2 j := by
    simp_rw [Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hswapB :
      (∑ i : Fin t, s.2 i * ∑ j : Fin t, B i j * y.1 j * y.2 j) =
      ∑ j : Fin t, (∑ i : Fin t, s.2 i * B i j) * y.1 j * y.2 j := by
    simp_rw [Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro i _
    ring
  simp_rw [mul_add, Finset.sum_add_distrib]
  rw [hswapA, hswapB]
  simp_rw [add_mul, Finset.sum_add_distrib]
  ring

open scoped BigOperators

def dotPair {t : ℕ}
    (s z : (Fin t → ZMod 2) × (Fin t → ZMod 2)) : ZMod 2 :=
  ∑ i : Fin t, (s.1 i * z.1 i + s.2 i * z.2 i)

def walshPair {t : ℕ}
    (f : ((Fin t → ZMod 2) × (Fin t → ZMod 2)) → ℚ)
    (s : (Fin t → ZMod 2) × (Fin t → ZMod 2)) : ℚ :=
  ∑ z, if dotPair s z = 0 then f z else -f z

noncomputable def decoder {t : ℕ}
    (e : ((Fin t → ZMod 2) × (Fin t → ZMod 2)) ≃
      ((Fin t → ZMod 2) × (Fin t → ZMod 2)))
    (c : Fin t → ZMod 2)
    (z : (Fin t → ZMod 2) × (Fin t → ZMod 2)) : ℚ :=
  sign2 (∑ i : Fin t, c i * (e.symm z).1 i * (e.symm z).2 i)

lemma decoder_walsh_factorization {t : ℕ}
    (A B : Fin t → Fin t → ZMod 2) (c : Fin t → ZMod 2)
    (e : ((Fin t → ZMod 2) × (Fin t → ZMod 2)) ≃
      ((Fin t → ZMod 2) × (Fin t → ZMod 2)))
    (he : ∀ y, e y =
      (fun i => y.1 i + ∑ j : Fin t, A i j * y.1 j * y.2 j,
       fun i => y.2 i + ∑ j : Fin t, B i j * y.1 j * y.2 j))
    (s : (Fin t → ZMod 2) × (Fin t → ZMod 2)) :
    walshPair (decoder e c) s =
      ∏ j : Fin t, localFourier (c j + ∑ i : Fin t, (s.1 i * A i j + s.2 i * B i j))
        (s.1 j) (s.2 j) := by
  classical
  calc
    walshPair (decoder e c) s =
        ∑ z, sign2 ((∑ i : Fin t, c i * (e.symm z).1 i * (e.symm z).2 i) +
          dotPair s z) := by
      apply Finset.sum_congr rfl
      intro z _
      rw [sign2_add]
      simp only [decoder, sign2]
      split_ifs <;> ring
    _ = ∑ y : (Fin t → ZMod 2) × (Fin t → ZMod 2), sign2 ((∑ i : Fin t, c i * y.1 i * y.2 i) + dotPair s (e y)) := by
      symm
      simpa using e.sum_comp (fun z =>
        sign2 ((∑ i : Fin t, c i * (e.symm z).1 i * (e.symm z).2 i) + dotPair s z))
    _ = ∑ y : (Fin t → ZMod 2) × (Fin t → ZMod 2), sign2 (∑ j : Fin t,
        ((c j + ∑ i : Fin t, (s.1 i * A i j + s.2 i * B i j)) * y.1 j * y.2 j +
          s.1 j * y.1 j + s.2 j * y.2 j)) := by
      apply Finset.sum_congr rfl
      intro y _
      rw [he]
      congr 1
      exact decoder_phase A B c s y
    _ = ∏ j : Fin t, localFourier
        (c j + ∑ i : Fin t, (s.1 i * A i j + s.2 i * B i j)) (s.1 j) (s.2 j) :=
      fourier_product t _ s

lemma decoder_walsh_support {t : ℕ}
    (A B : Fin t → Fin t → ZMod 2) (c : Fin t → ZMod 2)
    (e : ((Fin t → ZMod 2) × (Fin t → ZMod 2)) ≃
      ((Fin t → ZMod 2) × (Fin t → ZMod 2)))
    (he : ∀ y, e y =
      (fun i => y.1 i + ∑ j : Fin t, A i j * y.1 j * y.2 j,
       fun i => y.2 i + ∑ j : Fin t, B i j * y.1 j * y.2 j))
    (s : (Fin t → ZMod 2) × (Fin t → ZMod 2)) :
    walshPair (decoder e c) s ≠ 0 ↔
      ∀ j, c j + (∑ i : Fin t, (s.1 i * A i j + s.2 i * B i j)) = 1 ∨
        (s.1 j = 0 ∧ s.2 j = 0) := by
  rw [decoder_walsh_factorization A B c e he]
  simp only [Finset.prod_ne_zero_iff, Finset.mem_univ, forall_const,
    localFourier_ne_zero_iff]

lemma partial_involution_card_bound {X : Type*} [Fintype X] [DecidableEq X]
    (S Z : Finset X) (T : X → X)
    (hT : Function.Involutive T)
    (hbad : ∀ x ∈ S \ Z, T x ∉ S) :
    2 * S.card ≤ Fintype.card X + Z.card := by
  have hcount : (S \ Z).card ≤ Sᶜ.card := by
    apply Finset.card_le_card_of_injOn T
    · intro x hx
      exact Finset.mem_compl.mpr (hbad x hx)
    · exact hT.injective.injOn
  have hsplit := Finset.card_le_card_sdiff_add_card (s := S) (t := Z)
  have hle := Finset.card_le_univ S
  rw [Finset.card_compl] at hcount
  omega

lemma source_zero_card_bound (t : ℕ) (D : Finset (Fin t)) :
    (Finset.univ.filter (fun s : (Fin t → ZMod 2) × (Fin t → ZMod 2) =>
      ∀ j ∈ D, s.1 j = 0 ∧ s.2 j = 0)).card ≤ 4 ^ (t - D.card) := by
  classical
  let Z := Finset.univ.filter (fun s : (Fin t → ZMod 2) × (Fin t → ZMod 2) =>
      ∀ j ∈ D, s.1 j = 0 ∧ s.2 j = 0)
  let f : Z → ({j : Fin t // j ∉ D} → (ZMod 2 × ZMod 2)) :=
    fun s j => (s.1.1 j, s.1.2 j)
  have hf : Function.Injective f := by
    intro x y h
    apply Subtype.ext
    apply Prod.ext
    · funext j
      by_cases hj : j ∈ D
      · exact ((Finset.mem_filter.mp x.property).2 j hj).1.trans
          ((Finset.mem_filter.mp y.property).2 j hj).1.symm
      · exact congrArg Prod.fst (congrFun h ⟨j, hj⟩)
    · funext j
      by_cases hj : j ∈ D
      · exact ((Finset.mem_filter.mp x.property).2 j hj).2.trans
          ((Finset.mem_filter.mp y.property).2 j hj).2.symm
      · exact congrArg Prod.snd (congrFun h ⟨j, hj⟩)
  have hcount := Fintype.card_le_of_injective f hf
  have hdc : Fintype.card {j : Fin t // j ∉ D} = t - D.card := by
    rw [Fintype.card_subtype_compl]
    simp
  simpa [Z, hdc, Fintype.card_subtype] using hcount

lemma source_count_from_flips (t : ℕ) (D : Finset (Fin t))
    (q : ((Fin t → ZMod 2) × (Fin t → ZMod 2)) → Fin t → ZMod 2)
    (F : Fin t → ((Fin t → ZMod 2) × (Fin t → ZMod 2)) →
      ((Fin t → ZMod 2) × (Fin t → ZMod 2)))
    (hFinv : ∀ j, Function.Involutive (F j))
    (hFpre : ∀ j s k, k ≤ j → (F j s).1 k = s.1 k ∧ (F j s).2 k = s.2 k)
    (hFq : ∀ j ∈ D, ∀ s, q (F j s) j = q s j + 1) :
    2 * (Finset.univ.filter (fun s => ∀ j, q s j = 0 → s.1 j = 0 ∧ s.2 j = 0)).card ≤
      4 ^ t + 4 ^ (t - D.card) := by
  classical
  let active := fun s : (Fin t → ZMod 2) × (Fin t → ZMod 2) =>
    D.filter (fun j => s.1 j ≠ 0 ∨ s.2 j ≠ 0)
  let T := fun s => if h : (active s).Nonempty then F ((active s).min' h) s else s
  have hstable : ∀ s (h : (active s).Nonempty),
      ∃ h' : (active (F ((active s).min' h) s)).Nonempty,
        (active (F ((active s).min' h) s)).min' h' = (active s).min' h := by
    intro s h
    let j := (active s).min' h
    have hmem : j ∈ active s := Finset.min'_mem _ _
    have hpres : ∀ k, k ≤ j →
        (k ∈ active (F j s) ↔ k ∈ active s) := by
      intro k hk
      simp only [active, Finset.mem_filter]
      rw [(hFpre j s k hk).1, (hFpre j s k hk).2]
    have hjnew : j ∈ active (F j s) := (hpres j le_rfl).mpr hmem
    refine ⟨⟨j, hjnew⟩, ?_⟩
    apply (Finset.min'_eq_iff _ _ _).mpr
    refine ⟨hjnew, ?_⟩
    intro k hk
    by_contra hle
    have hkj : k ≤ j := (lt_of_not_ge hle).le
    have hks : k ∈ active s := (hpres k hkj).mp hk
    exact hle (Finset.min'_le _ _ hks)
  have hT : Function.Involutive T := by
    intro s
    by_cases h : (active s).Nonempty
    · obtain ⟨h', hm⟩ := hstable s h
      simp only [T, dite_eq_left h]
      rw [dite_eq_left h', hm]
      exact hFinv _ s
    · simp [T, h]
  let S := Finset.univ.filter (fun s => ∀ j, q s j = 0 → s.1 j = 0 ∧ s.2 j = 0)
  let Z := Finset.univ.filter (fun s : (Fin t → ZMod 2) × (Fin t → ZMod 2) =>
    ∀ j ∈ D, s.1 j = 0 ∧ s.2 j = 0)
  have hbad : ∀ s ∈ S \ Z, T s ∉ S := by
    intro s hs
    have hsS := (Finset.mem_filter.mp (Finset.mem_sdiff.mp hs).1).2
    have hsZ : ¬∀ j ∈ D, s.1 j = 0 ∧ s.2 j = 0 := by
      simpa [Z] using (Finset.mem_sdiff.mp hs).2
    push Not at hsZ
    obtain ⟨j0, hj0D, hj0⟩ := hsZ
    have ha : (active s).Nonempty := by
      refine ⟨j0, Finset.mem_filter.mpr ⟨hj0D, ?_⟩⟩
      by_cases h0 : s.1 j0 = 0
      · exact Or.inr (hj0 h0)
      · exact Or.inl h0
    let j := (active s).min' ha
    have hj := Finset.mem_filter.mp (Finset.min'_mem (active s) ha)
    have hq : q s j = 1 := by
      have hvals : ∀ z : ZMod 2, z = 0 ∨ z = 1 := by decide
      rcases hvals (q s j) with h0 | h1
      · have hz := hsS j h0
        rcases hj.2 with hh | hh
        · exact False.elim (hh hz.1)
        · exact False.elim (hh hz.2)
      · exact h1
    have hqT : q (T s) j = 0 := by
      simp only [T, dite_eq_left ha]
      rw [hFq j hj.1 s, hq]
      decide
    intro hTs
    have hz := (Finset.mem_filter.mp hTs).2 j hqT
    have hp : (T s).1 j = s.1 j ∧ (T s).2 j = s.2 j := by
      simpa only [T, dite_eq_left ha] using hFpre j s j le_rfl
    rcases hj.2 with hh | hh
    · exact hh (hp.1.symm.trans hz.1)
    · exact hh (hp.2.symm.trans hz.2)
  have hbound := partial_involution_card_bound S Z T hT hbad
  have hzbound := source_zero_card_bound t D
  have htotal : Fintype.card ((Fin t → ZMod 2) × (Fin t → ZMod 2)) = 4 ^ t := by
    simp [← mul_pow]
  rw [htotal] at hbound
  exact hbound.trans (Nat.add_le_add_left hzbound _)

lemma direct_source_count_bound (t : ℕ) (A B : Fin t → Fin t → ZMod 2)
    (c : Fin t → ZMod 2)
    (hA : ∀ i j, i ≤ j → A i j = 0)
    (hB : ∀ i j, i ≤ j → B i j = 0) :
    let D := Finset.univ.filter (fun j => ∃ i, A i j ≠ 0 ∨ B i j ≠ 0)
    let q := fun s : (Fin t → ZMod 2) × (Fin t → ZMod 2) =>
      fun j => c j + ∑ i, (s.1 i * A i j + s.2 i * B i j)
    2 * (Finset.univ.filter (fun s => ∀ j, q s j = 0 → s.1 j = 0 ∧ s.2 j = 0)).card ≤
      4 ^ t + 4 ^ (t - D.card) := by
  classical
  intro D q
  have hdelta : ∀ j ∈ D, ∃ d : (Fin t → ZMod 2) × (Fin t → ZMod 2),
      (∀ k, k ≤ j → d.1 k = 0 ∧ d.2 k = 0) ∧
      ∑ i, (d.1 i * A i j + d.2 i * B i j) = 1 := by
    intro j hj
    obtain ⟨i, hi⟩ := (Finset.mem_filter.mp hj).2
    have hvals : ∀ z : ZMod 2, z = 0 ∨ z = 1 := by decide
    rcases hi with hi | hi
    · have hji : j < i := lt_of_not_ge (fun hij => hi (hA i j hij))
      have hi1 := (hvals (A i j)).resolve_left hi
      refine ⟨(Pi.single i 1, 0), ?_, ?_⟩
      · intro k hk
        have hki : k ≠ i := ne_of_lt (lt_of_le_of_lt hk hji)
        simp [hki]
      · simp [Pi.single_apply, hi1]
    · have hji : j < i := lt_of_not_ge (fun hij => hi (hB i j hij))
      have hi1 := (hvals (B i j)).resolve_left hi
      refine ⟨(0, Pi.single i 1), ?_, ?_⟩
      · intro k hk
        have hki : k ≠ i := ne_of_lt (lt_of_le_of_lt hk hji)
        simp [hki]
      · simp [Pi.single_apply, hi1]
  let d := fun j => if hj : j ∈ D then (hdelta j hj).choose else 0
  have hdpre : ∀ j k, k ≤ j → (d j).1 k = 0 ∧ (d j).2 k = 0 := by
    intro j k hk
    by_cases hj : j ∈ D
    · simpa only [d, dite_eq_left hj] using (hdelta j hj).choose_spec.1 k hk
    · simp [d, hj]
  have hdsum : ∀ j ∈ D, ∑ i, ((d j).1 i * A i j + (d j).2 i * B i j) = 1 := by
    intro j hj
    simpa only [d, dite_eq_left hj] using (hdelta j hj).choose_spec.2
  apply source_count_from_flips t D q (fun j s => s + d j)
  · intro j s
    have hdd : d j + d j = 0 := by
      ext k <;> exact CharTwo.add_self_eq_zero _
    simp [add_assoc, hdd]
  · intro j s k hk
    simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply]
    rw [(hdpre j k hk).1, (hdpre j k hk).2]
    simp
  · intro j hj s
    change c j + ∑ i, ((s.1 i + (d j).1 i) * A i j +
      (s.2 i + (d j).2 i) * B i j) = _
    have hterm : ∀ i, (s.1 i + (d j).1 i) * A i j +
        (s.2 i + (d j).2 i) * B i j =
        (s.1 i * A i j + s.2 i * B i j) +
        ((d j).1 i * A i j + (d j).2 i * B i j) := by intro i; ring
    simp_rw [hterm]
    rw [Finset.sum_add_distrib, hdsum j hj]
    simp [q, add_assoc]

lemma h8_signed_submatrix_rank_le
    {α β γ δ : Type*} [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]
    (A : Matrix γ δ ℚ) (row : α → γ) (col : β → δ)
    (left : α → ℚ) (right : β → ℚ) :
    Matrix.rank (fun i j => left i * A (row i) (col j) * right j : Matrix α β ℚ) ≤ A.rank := by
  classical
  have h : (fun i j => left i * A (row i) (col j) * right j : Matrix α β ℚ) =
      Matrix.diagonal left * A.submatrix row col * Matrix.diagonal right := by
    ext i j
    simp [Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.submatrix]
  rw [h]
  exact (Matrix.rank_mul_le_left _ _).trans
    ((Matrix.rank_mul_le_right _ _).trans (Matrix.rank_submatrix_le _ _ _))

lemma h8_decoder_rank_le_walsh
    {α β : Type*} [Fintype α] [Fintype β] (d : ℕ)
    (f : (Fin d → ZMod 2) → ℚ)
    (row : α → (Fin d → ZMod 2)) (col : β → (Fin d → ZMod 2))
    (left : α → ℚ) (right : β → ℚ) :
    Matrix.rank (fun i j => left i * f (row i + col j) * right j : Matrix α β ℚ) ≤
      ((Finset.univ : Finset (Fin d → ZMod 2)).filter (fun s =>
        (∑ v : Fin d → ZMod 2,
          if (∑ k : Fin d, s k * v k) = 0 then f v else -f v) ≠ 0)).card := by
  classical
  exact (h8_signed_submatrix_rank_le
    (fun x y => f (x + y)) row col left right).trans_eq
    (PEqualNP.Outside.L_lib_435 d f)

lemma h8_bool_sign_xor (x y : Bool) :
    (if xor x y then (-1 : ℚ) else 1) =
      (if x then (-1 : ℚ) else 1) * (if y then (-1 : ℚ) else 1) := by
  cases x <;> cases y <;> norm_num

lemma h8_bool_decoder_rank_le_walsh
    {α β : Type*} [Fintype α] [Fintype β] (d : ℕ)
    (decode : (Fin d → ZMod 2) → Bool)
    (row : α → (Fin d → ZMod 2)) (col : β → (Fin d → ZMod 2))
    (Q : α → Bool) (R : β → Bool) :
    let f : (Fin d → ZMod 2) → ℚ := fun x => if decode x then -1 else 1
    Matrix.rank (fun i j => if xor (xor (Q i) (R j)) (decode (row i + col j))
      then (-1 : ℚ) else 1 : Matrix α β ℚ) ≤
      ((Finset.univ : Finset (Fin d → ZMod 2)).filter (fun s =>
        (∑ v : Fin d → ZMod 2,
          if (∑ k : Fin d, s k * v k) = 0 then f v else -f v) ≠ 0)).card := by
  classical
  intro f
  have h : (fun i j => if xor (xor (Q i) (R j)) (decode (row i + col j))
      then (-1 : ℚ) else 1 : Matrix α β ℚ) =
      (fun i j => (if Q i then (-1 : ℚ) else 1) * f (row i + col j) *
        (if R j then (-1 : ℚ) else 1)) := by
    ext i j
    rw [h8_bool_sign_xor, h8_bool_sign_xor]
    dsimp [f]
    ring
  rw [h]
  exact h8_decoder_rank_le_walsh d f row col
    (fun i => if Q i then -1 else 1) (fun j => if R j then -1 else 1)

lemma h8_bool_decoder_rank_le
    {α β X : Type*} [Fintype α] [Fintype β] [Fintype X] [Add X]
    (decode : X → Bool) (row : α → X) (col : β → X)
    (Q : α → Bool) (R : β → Bool) :
    Matrix.rank (fun i j => if xor (xor (Q i) (R j)) (decode (row i + col j))
      then (-1 : ℚ) else 1 : Matrix α β ℚ) ≤
    Matrix.rank (fun x y => if decode (x + y) then (-1 : ℚ) else 1 : Matrix X X ℚ) := by
  classical
  have h : (fun i j => if xor (xor (Q i) (R j)) (decode (row i + col j))
      then (-1 : ℚ) else 1 : Matrix α β ℚ) =
      (fun i j => (if Q i then (-1 : ℚ) else 1) *
        (if decode (row i + col j) then (-1 : ℚ) else 1) *
        (if R j then (-1 : ℚ) else 1)) := by
    ext i j
    rw [h8_bool_sign_xor, h8_bool_sign_xor]
    ring
  rw [h]
  exact h8_signed_submatrix_rank_le
    (fun x y => if decode (x + y) then -1 else 1) row col
    (fun i => if Q i then -1 else 1) (fun j => if R j then -1 else 1)


open scoped BigOperators

def H8PairEquiv (t : ℕ) :
    ((Fin t → ZMod 2) × (Fin t → ZMod 2)) ≃ (Fin (t + t) → ZMod 2) where
  toFun x := Fin.append x.1 x.2
  invFun v := (fun i => v (Fin.castAdd t i), fun i => v (Fin.natAdd t i))
  left_inv x := by
    apply Prod.ext
    · funext i
      exact Fin.append_left _ _ _
    · funext i
      exact Fin.append_right _ _ _
  right_inv v := Fin.append_castAdd_natAdd

lemma H8PairEquiv_add (t : ℕ)
    (x y : (Fin t → ZMod 2) × (Fin t → ZMod 2)) :
    H8PairEquiv t (x + y) = H8PairEquiv t x + H8PairEquiv t y := by
  funext i
  change Fin.append (x.1 + y.1) (x.2 + y.2) i =
    Fin.append x.1 x.2 i + Fin.append y.1 y.2 i
  induction i using Fin.addCases <;>
    simp only [Fin.append_left, Fin.append_right, Pi.add_apply]

lemma H8PairEquiv_dot (t : ℕ)
    (s v : (Fin t → ZMod 2) × (Fin t → ZMod 2)) :
    (∑ i : Fin (t + t), H8PairEquiv t s i * H8PairEquiv t v i) =
      (∑ i : Fin t, s.1 i * v.1 i) + ∑ i : Fin t, s.2 i * v.2 i := by
  change (∑ i : Fin (t + t), Fin.append s.1 s.2 i * Fin.append v.1 v.2 i) = _
  rw [Fin.sum_univ_add]
  simp only [Fin.append_left, Fin.append_right]

lemma H8_paired_walsh_rank (t : ℕ)
    (f : ((Fin t → ZMod 2) × (Fin t → ZMod 2)) → ℚ) :
    Matrix.rank (fun x y => f (x + y) :
      Matrix ((Fin t → ZMod 2) × (Fin t → ZMod 2))
        ((Fin t → ZMod 2) × (Fin t → ZMod 2)) ℚ) =
    (Finset.univ.filter (fun s : (Fin t → ZMod 2) × (Fin t → ZMod 2) =>
      (∑ v : (Fin t → ZMod 2) × (Fin t → ZMod 2),
        if (∑ i : Fin t, (s.1 i * v.1 i + s.2 i * v.2 i)) = 0
        then f v else -f v) ≠ 0)).card := by
  classical
  let e := H8PairEquiv t
  let g : (Fin (t + t) → ZMod 2) → ℚ := fun v => f (e.symm v)
  let M : Matrix (Fin (t + t) → ZMod 2) (Fin (t + t) → ZMod 2) ℚ :=
    fun x y => g (x + y)
  let W := fun s : Fin (t + t) → ZMod 2 =>
    ∑ v : Fin (t + t) → ZMod 2,
      if (∑ i : Fin (t + t), s i * v i) = 0 then g v else -g v
  let Wp := fun s : (Fin t → ZMod 2) × (Fin t → ZMod 2) =>
    ∑ v : (Fin t → ZMod 2) × (Fin t → ZMod 2),
      if (∑ i : Fin t, (s.1 i * v.1 i + s.2 i * v.2 i)) = 0
      then f v else -f v
  have hM : (fun x y => f (x + y)) = M.submatrix e e := by
    funext x y
    change f (x + y) = f ((H8PairEquiv t).symm (H8PairEquiv t x + H8PairEquiv t y))
    rw [← H8PairEquiv_add]
    simp only [Equiv.symm_apply_apply]
  have hW (s : (Fin t → ZMod 2) × (Fin t → ZMod 2)) : W (e s) = Wp s := by
    dsimp [W, Wp]
    symm
    apply Fintype.sum_equiv e
    intro v
    simp only [g, Equiv.symm_apply_apply, e, H8PairEquiv_dot, Finset.sum_add_distrib]
  rw [hM, Matrix.rank_submatrix]
  change M.rank = (Finset.univ.filter (fun s => Wp s ≠ 0)).card
  rw [PEqualNP.Outside.L_lib_435 (t + t) g]
  change (Finset.univ.filter (fun s => W s ≠ 0)).card =
    (Finset.univ.filter (fun s => Wp s ≠ 0)).card
  symm
  apply Finset.card_bij (fun s _ => e s)
  · intro s hs
    simpa [hW] using hs
  · intro s hs v hv he
    exact e.injective he
  · intro v hv
    refine ⟨e.symm v, ?_, e.apply_symm_apply v⟩
    simpa [← hW, e.apply_symm_apply] using hv

lemma h8_paired_decoder_rank_le_walsh
    {α β : Type*} [Fintype α] [Fintype β] (t : ℕ)
    (f : ((Fin t → ZMod 2) × (Fin t → ZMod 2)) → ℚ)
    (row : α → ((Fin t → ZMod 2) × (Fin t → ZMod 2)))
    (col : β → ((Fin t → ZMod 2) × (Fin t → ZMod 2)))
    (left : α → ℚ) (right : β → ℚ) :
    Matrix.rank (fun i j => left i * f (row i + col j) * right j : Matrix α β ℚ) ≤
    (Finset.univ.filter (fun s : (Fin t → ZMod 2) × (Fin t → ZMod 2) =>
      (∑ v : (Fin t → ZMod 2) × (Fin t → ZMod 2),
        if (∑ i : Fin t, (s.1 i * v.1 i + s.2 i * v.2 i)) = 0
        then f v else -f v) ≠ 0)).card := by
  classical
  exact (h8_signed_submatrix_rank_le
    (fun x y => f (x + y)) row col left right).trans_eq
    (H8_paired_walsh_rank t f)


lemma decoder_walsh_card_bound (t : ℕ)
    (A B : Fin t → Fin t → ZMod 2) (c : Fin t → ZMod 2)
    (hA : ∀ i j, i ≤ j → A i j = 0)
    (hB : ∀ i j, i ≤ j → B i j = 0)
    (e : Cube t ≃ Cube t)
    (he : ∀ y, e y = triangular A B y) :
    let D := Finset.univ.filter (fun j => ∃ i, A i j ≠ 0 ∨ B i j ≠ 0)
    2 * (Finset.univ.filter (fun s => walshPair (decoder e c) s ≠ 0)).card ≤
      4 ^ t + 4 ^ (t - D.card) := by
  classical
  intro D
  have hsub :
      Finset.univ.filter (fun s => walshPair (decoder e c) s ≠ 0) ⊆
      Finset.univ.filter (fun s : Cube t => ∀ j,
        c j + ∑ i, (s.1 i * A i j + s.2 i * B i j) = 0 →
          s.1 j = 0 ∧ s.2 j = 0) := by
    intro s hs
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    have hsupport := (decoder_walsh_support A B c e he s).mp (Finset.mem_filter.mp hs).2
    intro j hj
    simpa [hj] using hsupport j
  exact (Nat.mul_le_mul_left 2 (Finset.card_le_card hsub)).trans
    (direct_source_count_bound t A B c hA hB)

lemma triangular_decoder_rank_bound
    {α β : Type*} [Fintype α] [Fintype β] (t : ℕ)
    (A B : Fin t → Fin t → ZMod 2) (c : Fin t → ZMod 2)
    (hA : ∀ i j, i ≤ j → A i j = 0)
    (hB : ∀ i j, i ≤ j → B i j = 0)
    (e : Cube t ≃ Cube t)
    (he : ∀ y, e y = triangular A B y)
    (row : α → Cube t) (col : β → Cube t)
    (left : α → ℚ) (right : β → ℚ) :
    let D := Finset.univ.filter (fun j => ∃ i, A i j ≠ 0 ∨ B i j ≠ 0)
    2 * Matrix.rank
      (fun i j => left i * decoder e c (row i + col j) * right j : Matrix α β ℚ) ≤
      4 ^ t + 4 ^ (t - D.card) := by
  classical
  intro D
  have hr : Matrix.rank
      (fun i j => left i * decoder e c (row i + col j) * right j : Matrix α β ℚ) ≤
      (Finset.univ.filter (fun s => walshPair (decoder e c) s ≠ 0)).card := by
    have h := h8_paired_decoder_rank_le_walsh t (decoder e c) row col left right
    convert h using 1
    congr 1
  exact (Nat.mul_le_mul_left 2 hr).trans
    (decoder_walsh_card_bound t A B c hA hB e he)

def normalRow {n m t : ℕ} (u v : Fin t → ℕ)
    (c : ℕ → ZMod 2) (a : ℕ → Fin (n + m) → ZMod 2) (i : Fin n) : Cube t :=
  ((fun z => c (u z) + a (u z) (Fin.castAdd m i)),
   (fun z => c (v z) + a (v z) (Fin.castAdd m i)))

def normalCol {n m t : ℕ} (u v : Fin t → ℕ)
    (a : ℕ → Fin (n + m) → ZMod 2) (j : Fin m) : Cube t :=
  ((fun z => a (u z) (Fin.natAdd n j)),
   (fun z => a (v z) (Fin.natAdd n j)))

lemma sign2_h5b2z (b : Bool) : sign2 (h5b2z b) = if b then (-1 : ℚ) else 1 := by
  cases b <;> norm_num [sign2, h5b2z]

lemma circuit_sign_decoder {n m t : ℕ} (C : Circuit) (u v : Fin t → ℕ)
    (c : ℕ → ZMod 2) (a : ℕ → Fin (n + m) → ZMod 2)
    (b : ℕ → Fin t → ZMod 2) (e : Cube t ≃ Cube t)
    (he : ∀ y, e y =
      ((fun i => y.1 i + ∑ j, b (u i) j * y.1 j * y.2 j),
       (fun i => y.2 i + ∑ j, b (v i) j * y.1 j * y.2 j)))
    (hf : ∀ k x, h5val (n + m) C k x = h5affineTerm c a k x +
      ∑ j, b k j * (h5val (n + m) C (u j) x * h5val (n + m) C (v j) x))
    (i : Fin n) (j : Fin m) :
    (if C.eval (PEqualNP.Represents.oneEach i j) then (-1 : ℚ) else 1) =
      sign2 (c C.output + a C.output (Fin.castAdd m i)) *
        decoder e (b C.output) (normalRow u v c a i + normalCol u v a j) *
        sign2 (a C.output (Fin.natAdd n j)) := by
  have hv : h5val (n + m) C C.output (h5oneEachRaw i j) =
      h5b2z (C.eval (PEqualNP.Represents.oneEach i j)) := by
    dsimp only [h5val, h5wiresOf, Circuit.eval, Circuit.wires]
    rw [h5oneEachRaw_ofFn]
    rfl
  rw [← sign2_h5b2z, ← hv,
    h5normal_decoder_eq C u v c a b e he hf C.output (h5oneEachRaw i j), sign2_add]
  change sign2 (h5affineTerm c a C.output (h5oneEachRaw i j)) *
    decoder e (b C.output) (h5affinePair u v c a (h5oneEachRaw i j)) = _
  rw [h5affineTerm, h5affine_oneEach, sign2_add, h5affinePair_oneEach]
  change sign2 (c C.output + a C.output (Fin.castAdd m i)) *
      sign2 (a C.output (Fin.natAdd n j)) *
      decoder e (b C.output) (normalRow u v c a i + normalCol u v a j) = _
  ring

lemma helper3_rank_zero_of_high_rank (r t k : Nat)
    (hbound : 2 * 4 ^ r * k ≤ (4 ^ r + 1) * 4 ^ t)
    (hhigh : 5 * 4 ^ t < 8 * k) : r = 0 := by
  by_cases hr : r = 0
  · exact hr
  have hfour : 4 ≤ 4 ^ r := by
    have h := Nat.pow_le_pow_right (n := 4) (by omega) (show 1 ≤ r by omega)
    simpa using h
  have hlarge := Nat.mul_le_mul_right (4 ^ t) hfour
  have hbound4 : 8 * (4 ^ r * k) ≤ 4 * (4 ^ r * 4 ^ t) + 4 * 4 ^ t := by
    calc
      8 * (4 ^ r * k) = 4 * (2 * 4 ^ r * k) := by simp only [← Nat.mul_assoc]
      _ ≤ 4 * ((4 ^ r + 1) * 4 ^ t) := Nat.mul_le_mul_left 4 hbound
      _ = 4 * (4 ^ r * 4 ^ t) + 4 * 4 ^ t := by
        simp only [Nat.add_mul, Nat.mul_add, Nat.one_mul]
  have hhighr : 5 * (4 ^ r * 4 ^ t) < 8 * (4 ^ r * k) := by
    calc
      5 * (4 ^ r * 4 ^ t) = 4 ^ r * (5 * 4 ^ t) := by ac_rfl
      _ < 4 ^ r * (8 * k) := Nat.mul_lt_mul_of_pos_left hhigh (Nat.pow_pos (by omega))
      _ = 8 * (4 ^ r * k) := by ac_rfl
  omega

lemma helper3_defect_bound_of_source_bound (r d t k s : Nat)
    (hrd : r ≤ d) (hdt : d ≤ t) (hks : k ≤ s)
    (hsource : 2 * s ≤ 4 ^ t + 4 ^ (t - d)) :
    2 * 4 ^ r * k ≤ (4 ^ r + 1) * 4 ^ t := by
  have hqpos : 0 < 4 ^ (d - r) := Nat.pow_pos (by omega)
  have hqone : 1 ≤ 4 ^ (d - r) := by omega
  have hdprod : 4 ^ d * 4 ^ (t - d) = 4 ^ t := by
    rw [← Nat.pow_add]
    congr 1
    omega
  have hrprod : 4 ^ (d - r) * 4 ^ r = 4 ^ d := by
    rw [← Nat.pow_add, Nat.sub_add_cancel hrd]
  have hkbound : 2 * k ≤ 4 ^ t + 4 ^ (t - d) := by omega
  have hmul := Nat.mul_le_mul_left (4 ^ d) hkbound
  rw [Nat.mul_add, hdprod] at hmul
  have hqbase := Nat.mul_le_mul_right (4 ^ t) hqone
  have hgoal :
      4 ^ (d - r) * (2 * 4 ^ r * k) ≤
        4 ^ (d - r) * ((4 ^ r + 1) * 4 ^ t) := by
    simp only [Nat.mul_add, Nat.add_mul, Nat.mul_assoc] at hqbase ⊢
    rw [← Nat.mul_assoc (4 ^ (d-r)) (4 ^ r) (4 ^ t), hrprod]
    have hleft : 4 ^ (d-r) * (2 * (4 ^ r * k)) = 2 * (4 ^ d * k) := by
      rw [Nat.mul_left_comm (4 ^ (d-r)) 2 (4 ^ r * k)]
      rw [← Nat.mul_assoc (4 ^ (d-r)) (4 ^ r) k, hrprod]
    rw [hleft]
    rw [Nat.mul_left_comm (4 ^ d) 2 k] at hmul
    simp only [Nat.one_mul] at hqbase ⊢
    omega
  exact Nat.le_of_mul_le_mul_left hgoal hqpos

lemma circuit_rank_bound (n m : ℕ) (C : Circuit)
    (hlen : ∀ g ∈ C.gates, g.inputs.length ≤ 2)
    (hback : ReadsBack (n + m) C) :
    let t := C.gates.countP h5nlGate
    let K : Matrix (Fin n) (Fin m) ℚ := fun i j =>
      if C.eval (PEqualNP.Represents.oneEach i j) then -1 else 1
    2 * 4 ^ (h5PostedDefect (n + m) C).rank * K.rank ≤
      (4 ^ (h5PostedDefect (n + m) C).rank + 1) * 4 ^ t := by
  classical
  intro t K
  obtain ⟨e0, c, a, b, hnl, hcover, hnf, hlower⟩ :=
    h5compact_normal_system (n + m) C hlen hback
  let u : Fin t → ℕ := fun i => h5input0 C (e0 i)
  let v : Fin t → ℕ := fun i => h5input1 C (e0 i)
  let A : Fin t → Fin t → ZMod 2 := fun i j => b (u i) j
  let B : Fin t → Fin t → ZMod 2 := fun i j => b (v i) j
  have hA : ∀ i j, i ≤ j → A i j = 0 := fun i j hij => (hlower i j hij).1
  have hB : ∀ i j, i ≤ j → B i j = 0 := fun i j hij => (hlower i j hij).2
  let e : Cube t ≃ Cube t := triangularEquiv A B
    (fun i j hij => hA i j (le_of_not_gt hij))
    (fun i j hij => hB i j (le_of_not_gt hij))
  have he : ∀ y, e y = triangular A B y := fun _ => rfl
  let D := h5SourceSet C e0 b
  have hdefect : (h5PostedDefect (n + m) C).rank ≤ D.card :=
    h5PostedDefect_rank_le_sources (n + m) C e0 hcover c a b
      (fun j x => h5val (n + m) C (u j) x * h5val (n + m) C (v j) x) hnf
  have hdt : D.card ≤ t := by
    simpa using Finset.card_le_univ D
  have hK : K = (fun i j =>
      sign2 (c C.output + a C.output (Fin.castAdd m i)) *
        decoder e (b C.output) (normalRow u v c a i + normalCol u v a j) *
        sign2 (a C.output (Fin.natAdd n j)) : Matrix (Fin n) (Fin m) ℚ) := by
    ext i j
    exact circuit_sign_decoder C u v c a b e he hnf i j
  have hsource : 2 * K.rank ≤ 4 ^ t + 4 ^ (t - D.card) := by
    rw [hK]
    exact triangular_decoder_rank_bound t A B (b C.output) hA hB e he
      (normalRow u v c a) (normalCol u v a)
      (fun i => sign2 (c C.output + a C.output (Fin.castAdd m i)))
      (fun j => sign2 (a C.output (Fin.natAdd n j)))
  exact helper3_defect_bound_of_source_bound _ D.card t K.rank K.rank
    hdefect hdt le_rfl hsource

end PEqualNP.Outside.L_meta_25740_aux

open PEqualNP.Outside.L_meta_25740_aux

theorem PEqualNP.Outside.L_meta_25740 :
let nonlinear := fun (g : PEqualNP.CircuitLowerBounds.Gate) =>
  (g.inputs.length == 2) &&
  xor (xor (g.op.eval [false,false]) (g.op.eval [false,true]))
      (xor (g.op.eval [true,false]) (g.op.eval [true,true]))
∀ (n m : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit),
  (∀ g ∈ C.gates, g.inputs.length ≤ 2) →
  PEqualNP.MetaComplexity.NestedCover.ReadsBack (n+m) C →
  let t := C.gates.countP nonlinear
  let raw := Fin (n+m) → Bool
  let W := fun (w : ℕ) (x : raw) => (C.wires (List.ofFn x)).getD w false
  let defect : Matrix (Fin (n+m+C.gates.length)) (raw × raw) (ZMod 2) := fun w v =>
    if (∃ g ∈ C.gates, nonlinear g = true ∧ w.val ∈ g.inputs) ∧
      xor (xor (W w.val v.1) (W w.val v.2))
          (xor (W w.val (fun i => xor (v.1 i) (v.2 i))) (W w.val (fun _ => false))) = true
    then 1 else 0
  let value := fun (a : Fin n) (b : Fin m) => C.eval (PEqualNP.Represents.oneEach a b)
  let K : Matrix (Fin n) (Fin m) ℚ := fun i j => if value i j then -1 else 1
  let V := Fin (2*t) → ZMod 2
  2 * 4^defect.rank * K.rank ≤ (4^defect.rank + 1) * 4^t ∧
  (5 * 4^t < 8 * K.rank → defect.rank = 0 ∧
    ∃ (row : Fin n → V) (col : Fin m → V) (Q : Fin n → Bool) (R : Fin m → Bool),
      ∀ i j, value i j = xor (xor (Q i) (R j))
        (decide ((∑ b : Fin (2*t), row i b * col j b) = 1))) := by
  classical
  intro nonlinear n m C hlen hback t raw W defect value K V
  have hdef : defect = h5PostedDefect (n + m) C := by
    ext w v
    dsimp only [defect, W, h5PostedDefect]
    congr 1
  have hbound := circuit_rank_bound n m C hlen hback
  change 2 * 4 ^ (h5PostedDefect (n + m) C).rank * K.rank ≤
    (4 ^ (h5PostedDefect (n + m) C).rank + 1) * 4 ^ t at hbound
  rw [← hdef] at hbound
  refine ⟨hbound, ?_⟩
  intro hhigh
  have hz : defect.rank = 0 :=
    helper3_rank_zero_of_high_rank defect.rank t K.rank hbound hhigh
  refine ⟨hz, ?_⟩
  apply factor_of_zero_defect C hlen hback
  have hD : defect = circuitDefect (n + m) C nlGate := by
    ext w v
    dsimp only [defect, W, circuitDefect]
    congr 1
  rw [← hD]
  exact hz
