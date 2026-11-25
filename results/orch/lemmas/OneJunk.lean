import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4675.OneJunk

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm
  PEqualNP.Outside.L_meta_4675.MaskingNext

lemma foldl_append_spec {α β : Type} (f : List α → β → α) :
    ∀ (l : List β) (acc : List α),
      (l.foldl (fun w b => w ++ [f w b]) acc).length = acc.length + l.length ∧
      (∀ i < acc.length, (l.foldl (fun w b => w ++ [f w b]) acc)[i]? = acc[i]?) ∧
      (∀ (j : ℕ) (b : β), l[j]? = some b →
        (l.foldl (fun w b => w ++ [f w b]) acc)[acc.length + j]? =
          some (f ((l.take j).foldl (fun w x => w ++ [f w x]) acc) b)) := by
  intro l
  induction l with
  | nil =>
    intro acc
    refine ⟨by simp, fun i _ => rfl, fun j b h => by simp at h⟩
  | cons a t ih =>
    intro acc
    have h1 := ih (acc ++ [f acc a])
    refine ⟨?_, ?_, ?_⟩
    · rw [List.foldl_cons, h1.1, List.length_append, List.length_singleton, List.length_cons]
      omega
    · intro i hi
      simp only [List.foldl_cons]
      have hi' : i < (acc ++ [f acc a]).length := by simp; omega
      rw [h1.2.1 i hi', List.getElem?_append_left hi]
    · intro j b hj
      cases j with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hj
        subst hj
        simp only [List.foldl_cons, Nat.add_zero, List.take_zero, List.foldl_nil]
        have hi' : acc.length < (acc ++ [f acc a]).length := by simp
        rw [h1.2.1 acc.length hi', List.getElem?_append_right (le_refl _)]
        simp
      | succ j' =>
        simp only [List.getElem?_cons_succ] at hj
        simp only [List.foldl_cons, List.take_succ_cons]
        have hstep := h1.2.2 j' b hj
        simp only [List.length_append, List.length_singleton] at hstep
        have heq : acc.length + (j' + 1) = acc.length + 1 + j' := by omega
        rw [heq]
        exact hstep

lemma foldl_append_take_getD {α β : Type} (f : List α → β → α) (d : α)
    (l : List β) (acc : List α) (k i : ℕ) (hi : i < acc.length + k) (hk : k ≤ l.length) :
    ((l.take k).foldl (fun w x => w ++ [f w x]) acc).getD i d =
      (l.foldl (fun w x => w ++ [f w x]) acc).getD i d := by
  have hsplit : l = l.take k ++ l.drop k := (List.take_append_drop k l).symm
  conv_rhs => rw [hsplit, List.foldl_append]
  have hlen : ((l.take k).foldl (fun w x => w ++ [f w x]) acc).length = acc.length + k := by
    rw [(foldl_append_spec f (l.take k) acc).1, List.length_take, Nat.min_eq_left hk]
  have hget := (foldl_append_spec f (l.drop k) ((l.take k).foldl (fun w x => w ++ [f w x]) acc)).2.1 i (by omega)
  simp only [List.getD_eq_getElem?_getD, hget]


lemma cones_length (n : ℕ) (C : Circuit) : (cones n C).length = C.gates.length := by
  unfold cones
  have h := (foldl_append_spec (fun cs g =>
    (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + cs.length))).flatMap
      (fun w => (w - n) :: cs.getD (w - n) [])) C.gates []).1
  change (C.gates.foldl (fun cs g => cs ++ [((g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + cs.length))).flatMap
      (fun w => (w - n) :: cs.getD (w - n) []))]) []).length = C.gates.length
  rw [h]
  simp

lemma cones_getD_eq (n : ℕ) (C : Circuit) (j : ℕ) (hj : j < C.gates.length) :
    (cones n C).getD j [] =
      ((gateAt C j).inputs.filter (fun w => decide (n ≤ w ∧ w < n + j))).flatMap
        (fun w => (w - n) :: (cones n C).getD (w - n) []) := by
  have hgetg : C.gates[j]? = some (gateAt C j) := by
    simp only [gateAt, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj, Option.getD_some]
  let f : List (List ℕ) → Gate → List ℕ := fun cs g =>
    (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + cs.length))).flatMap
      (fun w => (w - n) :: cs.getD (w - n) [])
  have hstep := (foldl_append_spec f C.gates []).2.2 j (gateAt C j) hgetg
  have hlen : ((C.gates.take j).foldl (fun w x => w ++ [f w x]) []).length = j := by
    rw [(foldl_append_spec f (C.gates.take j) []).1, List.length_nil, Nat.zero_add,
      List.length_take, Nat.min_eq_left (Nat.le_of_lt hj)]
  change (C.gates.foldl (fun w x => w ++ [f w x]) []).getD j [] = _
  simp only [List.length_nil, Nat.zero_add] at hstep
  rw [List.getD_eq_getElem?_getD, hstep, Option.getD_some]
  dsimp only [f]
  rw [hlen]
  apply List.flatMap_congr
  intro w hw
  simp only [List.mem_filter, decide_eq_true_eq] at hw
  congr 1
  exact foldl_append_take_getD f [] C.gates [] j (w - n) (by simp; omega) (Nat.le_of_lt hj)

lemma inCone_lt (n : ℕ) (C : Circuit) : ∀ j i, InCone n C i j → i < j := by
  intro j
  induction j using Nat.strong_induction_on with
  | ind j ih =>
    intro i hij
    by_cases hj : j < C.gates.length
    · unfold InCone at hij
      rw [cones_getD_eq n C j hj, List.mem_flatMap] at hij
      obtain ⟨w, hw, hmem⟩ := hij
      simp only [List.mem_filter, decide_eq_true_eq] at hw
      simp only [List.mem_cons] at hmem
      rcases hmem with rfl | hmem
      · omega
      · have hlt := ih (w - n) (by omega) i hmem
        omega
    · unfold InCone at hij
      have hlen : (cones n C).length = C.gates.length := cones_length n C
      have hnone : (cones n C)[j]? = none := List.getElem?_eq_none (by omega)
      simp [List.getD_eq_getElem?_getD, hnone] at hij

lemma inCone_of_input (n : ℕ) (C : Circuit) (k j : ℕ) (hj : j < C.gates.length)
    (hk : k < j) (hmem : n + k ∈ (gateAt C j).inputs) : InCone n C k j := by
  unfold InCone
  rw [cones_getD_eq n C j hj, List.mem_flatMap]
  refine ⟨n + k, ?_, ?_⟩
  · simp only [List.mem_filter, decide_eq_true_eq]; exact ⟨hmem, by omega, by omega⟩
  · simp

lemma inCone_trans_of_input (n : ℕ) (C : Circuit) (i k j : ℕ) (hj : j < C.gates.length)
    (hk : k < j) (hmem : n + k ∈ (gateAt C j).inputs) (hik : InCone n C i k) : InCone n C i j := by
  unfold InCone at hik ⊢
  rw [cones_getD_eq n C j hj, List.mem_flatMap]
  refine ⟨n + k, ?_, ?_⟩
  · simp only [List.mem_filter, decide_eq_true_eq]; exact ⟨hmem, by omega, by omega⟩
  · simp only [List.mem_cons, Nat.add_sub_cancel_left]; exact Or.inr hik

lemma operands (n : ℕ) (C : Circuit) (hAO : IsAO2 n C) (j : ℕ) (hj : j < C.gates.length) :
    (gateAt C j).inputs = [opnd C j 0, opnd C j 1] ∧
      ∀ b : Fin 2, opnd C j b ∈ (gateAt C j).inputs ∧ opnd C j b < n + j := by
  have hm : gateAt C j ∈ C.gates := by
    rw [gateAt_eq_getElem C j hj]
    exact List.getElem_mem hj
  obtain ⟨a, b, hab⟩ := List.length_eq_two.mp (hAO.2.2 _ hm)
  have h0 : opnd C j 0 = a := by simp [opnd, hab]
  have h1 : opnd C j 1 = b := by simp [opnd, hab]
  refine ⟨by rw [h0, h1]; exact hab, ?_⟩
  intro c
  have hmem : opnd C j c ∈ (gateAt C j).inputs := by fin_cases c <;> simp [h0, h1, hab]
  exact ⟨hmem, hAO.2.1 j hj _ hmem⟩

lemma reach_inCone_or_eq (n : ℕ) (C : Circuit) :
    ∀ k g, OrReaches n C (n + k) g → g = k ∨ InCone n C g k := by
  intro k
  induction k using Nat.strong_induction_on with
  | ind k ih =>
    intro g hg
    obtain ⟨hk, he | ⟨_, u, hu, hul, hur⟩⟩ := (orReaches_iff n C k g).mp hg
    · exact Or.inl he
    · have hn : n ≤ u := hur.1
      have hue : u = n + (u - n) := by omega
      have hrec := ih (u - n) (by omega) g (by rwa [← hue])
      rcases hrec with rfl | hc
      · exact Or.inr (inCone_of_input n C (u - n) k hk (by omega) (by rwa [← hue]))
      · exact Or.inr (inCone_trans_of_input n C g (u - n) k hk (by omega) (by rwa [← hue]) hc)

lemma operand_reach_inCone (n : ℕ) (C : Circuit) (hAO : IsAO2 n C) (j : ℕ)
    (hj : j < C.gates.length) (b : Fin 2) (k : ℕ) (hr : OrReaches n C (opnd C j b) k) :
    InCone n C k j := by
  obtain ⟨hm, hlt⟩ := (operands n C hAO j hj).2 b
  have hn : n ≤ opnd C j b := hr.1
  have he : opnd C j b = n + (opnd C j b - n) := by omega
  have hr' : OrReaches n C (n + (opnd C j b - n)) k := by rwa [← he]
  rcases reach_inCone_or_eq n C _ k hr' with rfl | hc
  · exact inCone_of_input n C _ j hj (by omega) (by rwa [← he])
  · exact inCone_trans_of_input n C k _ j hj (by omega) (by rwa [← he]) hc

lemma operand_and_is_junk (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hAO : IsAO2 n C) (hTop : TopForm G C) (q : ℕ)
    (honly : ∀ k < C.gates.length, (gateAt C k).op = GateOp.and → ¬ BelowF G C k → k = q)
    (j : ℕ) (hj : j < C.gates.length) (hand : (gateAt C j).op = GateOp.and)
    (b : Fin 2) (k : ℕ) (hk : k < C.gates.length) (hkand : (gateAt C k).op = GateOp.and)
    (hr : OrReaches n C (opnd C j b) k) : k = q := by
  apply honly k hk hkand
  intro hb
  exact hTop k hk j hj hkand hb hand (operand_reach_inCone n C hAO j hj b k hr)

lemma operand_semantics (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hAO : IsAO2 n C) (hTop : TopForm G C) (q : ℕ)
    (honly : ∀ k < C.gates.length, (gateAt C k).op = GateOp.and → ¬ BelowF G C k → k = q)
    (j : ℕ) (hj : j < C.gates.length) (hand : (gateAt C j).op = GateOp.and)
    (b : Fin 2) (x : Fin n → Bool) :
    PEqualNP.BlindGate.wireValue C n x (opnd C j b) = true ↔
      (∃ i ∈ side (n := n) C j b, x i = true) ∨
      OrReaches n C (opnd C j b) q ∧ gateVal n C q x = true := by
  constructor
  · intro hv
    have hw := ((operands n C hAO j hj).2 b).2
    rcases true_wire_source n C hAO x _ (by omega) hv with hi | ⟨k, hk, hr, hkand, hkv⟩
    · exact Or.inl hi
    · have he := operand_and_is_junk n G C hAO hTop q honly j hj hand b k hk hkand hr
      subst k
      exact Or.inr ⟨hr, hkv⟩
  · rintro (⟨i, hi, hxi⟩ | ⟨hr, hqv⟩)
    · exact orIn_true n C hAO x _ i hi hxi
    · exact orReaches_true n C hAO x q hqv _ hr

lemma junk_operand_pure (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hAO : IsAO2 n C) (hTop : TopForm G C) (q : ℕ)
    (hq : q < C.gates.length) (hand : (gateAt C q).op = GateOp.and)
    (honly : ∀ k < C.gates.length, (gateAt C k).op = GateOp.and → ¬ BelowF G C k → k = q)
    (b : Fin 2) (x : Fin n → Bool) :
    PEqualNP.BlindGate.wireValue C n x (opnd C q b) = true ↔
      ∃ i ∈ side (n := n) C q b, x i = true := by
  rw [operand_semantics n G C hAO hTop q honly q hq hand b x]
  have hnot : ¬ OrReaches n C (opnd C q b) q := by
    intro hr
    have hb := orReaches_bound n C q _ hr
    have hw := ((operands n C hAO q hq).2 b).2
    omega
  simp [hnot]

lemma and_value (n : ℕ) (C : Circuit) (hAO : IsAO2 n C) (j : ℕ)
    (hj : j < C.gates.length) (hand : (gateAt C j).op = GateOp.and) (x : Fin n → Bool) :
    gateVal n C j x = true ↔
      PEqualNP.BlindGate.wireValue C n x (opnd C j 0) = true ∧
      PEqualNP.BlindGate.wireValue C n x (opnd C j 1) = true := by
  change PEqualNP.BlindGate.wireValue C n x (n + j) = true ↔ _
  rw [wireValue_gate n C x j hj hAO.2.1, hand, (operands n C hAO j hj).1]
  simp [GateOp.eval]

lemma junk_semantics (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hAO : IsAO2 n C) (hTop : TopForm G C) (q : ℕ)
    (hq : q < C.gates.length) (hand : (gateAt C q).op = GateOp.and)
    (honly : ∀ k < C.gates.length, (gateAt C k).op = GateOp.and → ¬ BelowF G C k → k = q)
    (x : Fin n → Bool) : gateVal n C q x = true ↔
      (∃ i ∈ side (n := n) C q 0, x i = true) ∧
      (∃ i ∈ side (n := n) C q 1, x i = true) := by
  rw [and_value n C hAO q hq hand x,
    junk_operand_pure n G C hAO hTop q hq hand honly 0 x,
    junk_operand_pure n G C hAO hTop q hq hand honly 1 x]

lemma productive_reader_not_both (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hAO : IsAO2 n C) (q : ℕ) (hdirty : ¬ BelowF G C q)
    (j : ℕ) (hj : j < C.gates.length) (hand : (gateAt C j).op = GateOp.and)
    (hbelow : BelowF G C j) :
    ¬ (OrReaches n C (opnd C j 0) q ∧ OrReaches n C (opnd C j 1) q) := by
  intro hr
  apply hdirty
  intro x hv
  apply hbelow x
  rw [and_value n C hAO j hj hand x]
  exact ⟨orReaches_true n C hAO x q hv _ hr.1, orReaches_true n C hAO x q hv _ hr.2⟩

lemma productive_reader_semantics (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hAO : IsAO2 n C) (hTop : TopForm G C) (q : ℕ)
    (hq : q < C.gates.length) (hqand : (gateAt C q).op = GateOp.and)
    (hdirty : ¬ BelowF G C q)
    (honly : ∀ k < C.gates.length, (gateAt C k).op = GateOp.and → ¬ BelowF G C k → k = q)
    (j : ℕ) (hj : j < C.gates.length) (hand : (gateAt C j).op = GateOp.and)
    (hbelow : BelowF G C j) (b : Fin 2) (hr : OrReaches n C (opnd C j b) q)
    (x : Fin n → Bool) : gateVal n C j x = true ↔
      ((∃ i ∈ side (n := n) C q 0, x i = true) ∧
        (∃ i ∈ side (n := n) C q 1, x i = true) ∨
        (∃ i ∈ side (n := n) C j b, x i = true)) ∧
      (∃ i ∈ side (n := n) C j (1 - b), x i = true) := by
  have hnb := productive_reader_not_both n G C hAO q hdirty j hj hand hbelow
  have hsem := junk_semantics n G C hAO hTop q hq hqand honly x
  rw [and_value n C hAO j hj hand x,
    operand_semantics n G C hAO hTop q honly j hj hand 0 x,
    operand_semantics n G C hAO hTop q honly j hj hand 1 x]
  have hb : b = 0 ∨ b = 1 := by fin_cases b <;> simp
  rcases hb with rfl | rfl
  · have hn : ¬ OrReaches n C (opnd C j 1) q := fun h => hnb ⟨hr, h⟩
    simp only [hr, hn, true_and, false_and, or_false, hsem, sub_zero]
    constructor <;> rintro ⟨h0, h1⟩ <;> exact ⟨h0.symm, h1⟩
  · have hn : ¬ OrReaches n C (opnd C j 0) q := fun h => hnb ⟨h, hr⟩
    simp only [hr, hn, true_and, false_and, or_false, hsem, sub_self]
    constructor
    · rintro ⟨h0, h1⟩
      exact ⟨h1.symm, h0⟩
    · rintro ⟨h1, h0⟩
      exact ⟨h0, h1.symm⟩

lemma junk_sides_nonempty (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hAO : IsAO2 n C) (hTop : TopForm G C) (q : ℕ)
    (hq : q < C.gates.length) (hqand : (gateAt C q).op = GateOp.and)
    (hdirty : ¬ BelowF G C q)
    (honly : ∀ k < C.gates.length, (gateAt C k).op = GateOp.and → ¬ BelowF G C k → k = q) :
    (side (n := n) C q 0).Nonempty ∧ (side (n := n) C q 1).Nonempty := by
  have hw : ∃ x : Fin n → Bool, gateVal n C q x = true := by
    by_contra h
    apply hdirty
    intro x hx
    exact False.elim (h ⟨x, hx⟩)
  obtain ⟨x, hx⟩ := hw
  obtain ⟨⟨a, ha, _⟩, ⟨b, hb, _⟩⟩ := (junk_semantics n G C hAO hTop q hq hqand honly x).mp hx
  exact ⟨⟨a, ha⟩, ⟨b, hb⟩⟩

end PEqualNP.Outside.L_meta_4675.OneJunk
