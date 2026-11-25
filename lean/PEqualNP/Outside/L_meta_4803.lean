import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4803_aux

-- toolkit and cone lemmas copied from extra/submitted/L_meta_4846.lean (cones from the merged L_meta_2067)
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def val {n : ℕ} (gs : List Gate) (x : Fin n → Bool) (i : ℕ) : Bool :=
  (gs.foldl step (List.ofFn x)).getD i false

lemma fold_length (gs : List Gate) (w : List Bool) :
    (gs.foldl step w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, ih, List.length_cons]
    simp only [step, List.length_append, List.length_cons, List.length_nil]
    omega

lemma val_nil {n : ℕ} (x : Fin n → Bool) (i : ℕ) :
    val [] x i = if h : i < n then x ⟨i, h⟩ else false := by
  unfold val
  by_cases h : i < n
  · simp [List.getD_eq_getElem?_getD, h]
  · simp [List.getD_eq_getElem?_getD, h]

lemma val_snoc {n : ℕ} (gs : List Gate) (g : Gate) (x : Fin n → Bool) (i : ℕ) :
    val (gs ++ [g]) x i =
      if i = n + gs.length then g.op.eval (g.inputs.map fun j => val gs x j)
      else val gs x i := by
  unfold val
  rw [List.foldl_append]
  simp only [List.foldl_cons, List.foldl_nil, step]
  have hl : (gs.foldl step (List.ofFn x)).length = n + gs.length := by
    rw [fold_length]
    simp
  rcases lt_trichotomy i (n + gs.length) with h | h | h
  · rw [if_neg (by omega)]
    simp only [List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_left (by omega)]
  · rw [if_pos h]
    simp only [List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_right (by omega)]
    simp [hl, h]
  · rw [if_neg (by omega)]
    simp only [List.getD_eq_getElem?_getD]
    rw [List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by omega)]

lemma val_ge {n : ℕ} (gs : List Gate) (x : Fin n → Bool) (i : ℕ) (hi : n + gs.length ≤ i) :
    val gs x i = false := by
  unfold val
  have hl : (gs.foldl step (List.ofFn x)).length = n + gs.length := by
    rw [fold_length]
    simp
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
  rfl

lemma val_lt {n : ℕ} (gs : List Gate) (x : Fin n → Bool) (i : ℕ) (hi : i < n) :
    val gs x i = x ⟨i, hi⟩ := by
  induction gs using List.reverseRecOn with
  | nil =>
    rw [val_nil]
    simp [hi]
  | append_singleton gs g ih =>
    rw [val_snoc, if_neg (by omega)]
    exact ih

lemma val_gate {n : ℕ} (gs : List Gate) (x : Fin n → Bool) :
    ∀ (k : ℕ) (hk : k < gs.length), val gs x (n + k) =
      gs[k].op.eval (gs[k].inputs.map fun j => if j < n + k then val gs x j else false) := by
  induction gs using List.reverseRecOn with
  | nil =>
    intro k hk
    simp at hk
  | append_singleton gs g ih =>
    intro k hk
    by_cases hkl : k = gs.length
    · subst hkl
      have hgl : (gs ++ [g])[gs.length]'hk = g := by simp
      rw [hgl, val_snoc, if_pos rfl]
      congr 1
      apply List.map_congr_left
      intro j _
      by_cases hj : j < n + gs.length
      · rw [if_pos hj, val_snoc, if_neg (by omega)]
      · rw [if_neg hj, val_ge gs x j (by omega)]
    · have hk' : k < gs.length + 1 := by simpa using hk
      have hk2 : k < gs.length := by omega
      have hget : (gs ++ [g])[k]'hk = gs[k] := List.getElem_append_left hk2
      rw [hget, val_snoc, if_neg (by omega), ih k hk2]
      congr 1
      apply List.map_congr_left
      intro j _
      by_cases hj : j < n + k
      · rw [if_pos hj, if_pos hj, val_snoc, if_neg (by omega)]
      · rw [if_neg hj, if_neg hj]

def eof {n : ℕ} (u : Fin n) : Fin n → Bool := fun c => decide (c = u)

def pr {n : ℕ} (u v : Fin n) : Fin n → Bool := fun c => decide (c = u ∨ c = v)

-- cone characterisation (cones_len .. inCone_trans) copied from the merged L_meta_2067
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

lemma inCone_lt (n : ℕ) (C : Circuit) (i : ℕ) :
    ∀ j, InCone n C i j → i < j ∧ j < C.gates.length := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro h
    rw [inCone_iff] at h
    obtain ⟨h0, k, hk, _, h3 | h3⟩ := h
    · exact ⟨by omega, h0⟩
    · have := (ih k hk h3).1
      exact ⟨by omega, h0⟩

lemma inCone_trans (n : ℕ) (C : Circuit) (a k : ℕ) (hak : InCone n C a k) :
    ∀ j, InCone n C k j → InCone n C a j := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro h
    rw [inCone_iff] at h
    obtain ⟨h0, k2, hk2, hin, h3 | h3⟩ := h
    · subst h3
      rw [inCone_iff]
      exact ⟨h0, k, hk2, hin, Or.inr hak⟩
    · rw [inCone_iff]
      exact ⟨h0, k2, hk2, hin, Or.inr (ih k2 hk2 h3)⟩

lemma gateAt_eq (C : Circuit) (j : ℕ) (hj : j < C.gates.length) : gateAt C j = C.gates[j] := by
  unfold gateAt
  simp [List.getD_eq_getElem?_getD, hj]


-- geometry of the projective plane of order 3 on the 26 variables
def incB (p l : ℕ) : Bool :=
  decide ((p + 13 - l) % 13 = 0 ∨ (p + 13 - l) % 13 = 1 ∨ (p + 13 - l) % 13 = 3 ∨
    (p + 13 - l) % 13 = 9)

def adjB (u v : Fin 26) : Bool :=
  (decide (u.val < 13) && decide (13 ≤ v.val) && incB u.val (v.val - 13)) ||
    (decide (v.val < 13) && decide (13 ≤ u.val) && incB v.val (u.val - 13))

lemma inc_iff : ∀ p l : Fin 13, (p = l ∨ p = l + 1 ∨ p = l + 3 ∨ p = l + 9) ↔
    incB p.val l.val = true := by decide

lemma adj_symm (u v : Fin 26) : adjB u v = adjB v u := by
  unfold adjB; rw [Bool.or_comm]

lemma adj_irr : ∀ v : Fin 26, adjB v v = false := by decide

lemma adj_cl : ∀ p l : Fin 13, incB p.val l.val = true →
    adjB (Fin.castAdd 13 p) (Fin.natAdd 13 l) = true := by decide

lemma adj_diag : ∀ p : Fin 13, adjB (Fin.castAdd 13 p) (Fin.natAdd 13 p) = true := by decide

lemma cl_ne : ∀ p l : Fin 13, Fin.castAdd 13 p ≠ Fin.natAdd 13 l := by decide

lemma common : ∀ c c' : Fin 26, c ≠ c' →
    (Finset.univ.filter (fun y => adjB c y = true ∧ adjB c' y = true)).card ≤ 1 := by
  decide +kernel

lemma ecard : (Finset.univ.filter (fun p : Fin 26 × Fin 26 => adjB p.1 p.2 = true)).card = 104 := by
  decide +kernel


open Classical

-- abstract leaf count: a family closed under unions of two earlier members
lemma leaf_count {α : Type*} [DecidableEq α] (cls : ℕ → Prop) (T : ℕ → Finset α)
    (h : ∀ w, cls w → (T w).card ≤ 1 ∨ ∃ a b, a < w ∧ b < w ∧ cls a ∧ cls b ∧ T w = T a ∪ T b) :
    ∀ M (W : Finset ℕ), (∀ w ∈ W, w < M ∧ cls w) →
      (W.biUnion T).card ≤ W.card +
        ((Finset.range M).filter (fun k => cls k ∧ 2 ≤ (T k).card ∧ T k ⊆ W.biUnion T)).card := by
  intro M
  induction M with
  | zero =>
    intro W hW
    have : W = ∅ := by
      ext w
      simp only [Finset.notMem_empty, iff_false]
      intro hw
      exact absurd (hW w hw).1 (by omega)
    subst this
    simp
  | succ M ih =>
    intro W hW
    have hmono : ∀ U U' : Finset α, U ⊆ U' →
        ((Finset.range M).filter (fun k => cls k ∧ 2 ≤ (T k).card ∧ T k ⊆ U)).card ≤
        ((Finset.range (M + 1)).filter (fun k => cls k ∧ 2 ≤ (T k).card ∧ T k ⊆ U')).card := by
      intro U U' hU
      apply Finset.card_le_card
      intro k hk
      simp only [Finset.mem_filter, Finset.mem_range] at hk ⊢
      exact ⟨by omega, hk.2.1, hk.2.2.1, hk.2.2.2.trans hU⟩
    by_cases hM : M ∈ W
    · have hWe : W = insert M (W.erase M) := (Finset.insert_erase hM).symm
      have hW' : ∀ w ∈ W.erase M, w < M ∧ cls w := by
        intro w hw
        rw [Finset.mem_erase] at hw
        have := hW w hw.2
        exact ⟨by omega, this.2⟩
      have hnot : M ∉ W.erase M := Finset.notMem_erase M W
      have hcard : W.card = (W.erase M).card + 1 := by
        rw [Finset.card_erase_of_mem hM]
        have := Finset.card_pos.mpr ⟨M, hM⟩
        omega
      have hU : W.biUnion T = T M ∪ (W.erase M).biUnion T := by
        conv_lhs => rw [hWe]
        rw [Finset.biUnion_insert]
      by_cases h1 : (T M).card ≤ 1
      · have ih1 := ih (W.erase M) hW'
        have hsub : (W.erase M).biUnion T ⊆ W.biUnion T := by
          rw [hU]; exact Finset.subset_union_right
        have := hmono _ _ hsub
        have hu := Finset.card_union_le (T M) ((W.erase M).biUnion T)
        rw [hU] at this ⊢
        omega
      · rcases h M (hW M hM).2 with h2 | ⟨a, b, ha, hb, ca, cb, hT⟩
        · exact absurd h2 h1
        · set W2 := insert a (insert b (W.erase M)) with hW2
          have hW2' : ∀ w ∈ W2, w < M ∧ cls w := by
            intro w hw
            rw [hW2, Finset.mem_insert, Finset.mem_insert] at hw
            rcases hw with rfl | rfl | hw
            · exact ⟨ha, ca⟩
            · exact ⟨hb, cb⟩
            · exact hW' w hw
          have hU2 : W2.biUnion T = W.biUnion T := by
            rw [hW2, Finset.biUnion_insert, Finset.biUnion_insert, hU, hT, Finset.union_assoc]
          have hc2 : W2.card ≤ (W.erase M).card + 2 := by
            rw [hW2]
            have e1 := Finset.card_insert_le a (insert b (W.erase M))
            have e2 := Finset.card_insert_le b (W.erase M)
            omega
          have ih2 := ih W2 hW2'
          rw [hU2] at ih2
          have hsplit : (Finset.range (M + 1)).filter
              (fun k => cls k ∧ 2 ≤ (T k).card ∧ T k ⊆ W.biUnion T) =
              insert M ((Finset.range M).filter
                (fun k => cls k ∧ 2 ≤ (T k).card ∧ T k ⊆ W.biUnion T)) := by
            rw [Finset.range_add_one, Finset.filter_insert, if_pos]
            refine ⟨(hW M hM).2, by omega, ?_⟩
            rw [hU]; exact Finset.subset_union_left
          rw [hsplit, Finset.card_insert_of_notMem (by simp)]
          omega
    · have hW' : ∀ w ∈ W, w < M ∧ cls w := by
        intro w hw
        have := hW w hw
        have hne : w ≠ M := fun he => hM (he ▸ hw)
        exact ⟨by omega, this.2⟩
      have := ih W hW'
      have := hmono (W.biUnion T) (W.biUnion T) le_rfl
      omega

section circ

variable (C : Circuit)

lemma gv (hC : PEqualNP.TopForm.IsAO2 26 C) (w : ℕ) (h1 : 26 ≤ w) (h2 : w < 26 + C.gates.length) :
    ∃ a b, (gateAt C (w - 26)).inputs = [a, b] ∧ a < w ∧ b < w ∧
      ((gateAt C (w - 26)).op = GateOp.and ∨ (gateAt C (w - 26)).op = GateOp.or) ∧
      ∀ x : Fin 26 → Bool, val C.gates x w =
        (gateAt C (w - 26)).op.eval [val C.gates x a, val C.gates x b] := by
  obtain ⟨k, rfl⟩ : ∃ k, w = 26 + k := ⟨w - 26, by omega⟩
  have hk : k < C.gates.length := by omega
  have e : 26 + k - 26 = k := by omega
  rw [e]
  obtain ⟨hAO, hRB, hL⟩ := hC
  have hmem := List.getElem_mem hk
  have h2 := hL _ hmem
  have hop := hAO _ hmem
  rw [← gateAt_eq C k hk] at h2 hop
  obtain ⟨a, b, hab⟩ := List.length_eq_two.mp h2
  have ha := hRB k hk a (by rw [hab]; simp)
  have hb := hRB k hk b (by rw [hab]; simp)
  refine ⟨a, b, hab, ha, hb, hop, fun x => ?_⟩
  rw [val_gate C.gates x k hk, ← gateAt_eq C k hk, hab]
  simp [ha, hb]

lemma ev_and (p q : Bool) : GateOp.and.eval [p, q] = (p && q) := by simp [GateOp.eval]

lemma ev_or (p q : Bool) : GateOp.or.eval [p, q] = (p || q) := by simp [GateOp.eval]

def S (w : ℕ) : Finset (Fin 26) := Finset.univ.filter (fun v => val C.gates (eof v) w = true)

lemma mem_S (w : ℕ) (v : Fin 26) : v ∈ S C w ↔ val C.gates (eof v) w = true := by simp [S]

lemma S_inp (w : ℕ) (hw : w < 26) : S C w = {⟨w, hw⟩} := by
  ext v
  rw [mem_S, val_lt C.gates _ w hw]
  simp only [eof, decide_eq_true_eq, Finset.mem_singleton]
  exact eq_comm

lemma S_or (a b w : ℕ)
    (hv : ∀ x : Fin 26 → Bool, val C.gates x w = (val C.gates x a || val C.gates x b)) :
    S C w = S C a ∪ S C b := by
  ext v
  simp only [Finset.mem_union, mem_S, hv, Bool.or_eq_true]

def Lin (w : ℕ) : Prop := w < 26 ∨ (26 ≤ w ∧ w < 26 + C.gates.length ∧
  ∀ i, (gateAt C i).op = GateOp.and → 26 + i ≠ w ∧ ¬ InCone 26 C i (w - 26))

lemma cone_in (j a : ℕ) (hj : j < C.gates.length) (ha : a ∈ (gateAt C j).inputs)
    (h1 : 26 ≤ a) (h2 : a < 26 + j) : InCone 26 C (a - 26) j :=
  (inCone_iff 26 C (a - 26) j).mpr
    ⟨hj, a - 26, by omega, by rw [show 26 + (a - 26) = a by omega]; exact ha, Or.inl rfl⟩

lemma input_lin (j a : ℕ) (hj : j < C.gates.length) (ha : a ∈ (gateAt C j).inputs)
    (hlt : a < 26 + j) (hfree : ∀ i, (gateAt C i).op = GateOp.and → ¬ InCone 26 C i j) :
    Lin C a := by
  by_cases h1 : a < 26
  · exact Or.inl h1
  · right
    have hc := cone_in C j a hj ha (by omega) hlt
    refine ⟨by omega, by omega, fun i hi => ⟨?_, ?_⟩⟩
    · intro he
      apply hfree i hi
      rw [show i = a - 26 by omega]
      exact hc
    · intro hin
      exact hfree i hi (inCone_trans 26 C i (a - 26) hin j hc)

lemma lin_struct (hC : PEqualNP.TopForm.IsAO2 26 C) (w : ℕ) (hw : Lin C w) (h26 : 26 ≤ w) :
    ∃ a b, a < w ∧ b < w ∧ Lin C a ∧ Lin C b ∧ (gateAt C (w - 26)).op = GateOp.or ∧
      ∀ x : Fin 26 → Bool, val C.gates x w = (val C.gates x a || val C.gates x b) := by
  rcases hw with hw | ⟨_, hM, hfree⟩
  · omega
  obtain ⟨a, b, hab, ha, hb, hop, hv⟩ := gv C hC w h26 hM
  have hor : (gateAt C (w - 26)).op = GateOp.or := by
    rcases hop with hop | hop
    · exact absurd (by omega) (hfree (w - 26) hop).1
    · exact hop
  have hk : w - 26 < C.gates.length := by omega
  have hf : ∀ i, (gateAt C i).op = GateOp.and → ¬ InCone 26 C i (w - 26) :=
    fun i hi => (hfree i hi).2
  refine ⟨a, b, ha, hb, input_lin C (w - 26) a hk (by rw [hab]; simp) (by omega) hf,
    input_lin C (w - 26) b hk (by rw [hab]; simp) (by omega) hf, hor, fun x => ?_⟩
  rw [hv x, hor, ev_or]

lemma lin_sem (hC : PEqualNP.TopForm.IsAO2 26 C) : ∀ w, Lin C w → ∀ u v : Fin 26,
    (val C.gates (pr u v) w = true ↔ (u ∈ S C w ∨ v ∈ S C w)) := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hw u v
    by_cases h26 : w < 26
    · rw [S_inp C w h26, val_lt C.gates _ w h26]
      simp only [pr, decide_eq_true_eq, Finset.mem_singleton]
      constructor
      · rintro (h | h)
        · exact Or.inl h.symm
        · exact Or.inr h.symm
      · rintro (h | h)
        · exact Or.inl h.symm
        · exact Or.inr h.symm
    · obtain ⟨a, b, ha, hb, la, lb, _, hv⟩ := lin_struct C hC w hw (by omega)
      rw [hv, Bool.or_eq_true, ih a ha la, ih b hb lb, S_or C a b w hv]
      simp only [Finset.mem_union]
      tauto

lemma lin_ne (hC : PEqualNP.TopForm.IsAO2 26 C) : ∀ w, Lin C w → (S C w).Nonempty := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hw
    by_cases h26 : w < 26
    · rw [S_inp C w h26]; simp
    · obtain ⟨a, b, ha, hb, la, lb, _, hv⟩ := lin_struct C hC w hw (by omega)
      rw [S_or C a b w hv]
      obtain ⟨y, hy⟩ := ih a ha la
      exact ⟨y, Finset.mem_union_left _ hy⟩

lemma lin_cls (hC : PEqualNP.TopForm.IsAO2 26 C) (w : ℕ) (hw : Lin C w) :
    (S C w).card ≤ 1 ∨ ∃ a b, a < w ∧ b < w ∧ Lin C a ∧ Lin C b ∧ S C w = S C a ∪ S C b := by
  by_cases h26 : w < 26
  · left; rw [S_inp C w h26]; simp
  · obtain ⟨a, b, ha, hb, la, lb, _, hv⟩ := lin_struct C hC w hw (by omega)
    exact Or.inr ⟨a, b, ha, hb, la, lb, S_or C a b w hv⟩

def Z (w : ℕ) : Prop :=
  26 ≤ w ∧ w < 26 + C.gates.length ∧ ∀ v : Fin 26, val C.gates (eof v) w = false

lemma z_struct (hC : PEqualNP.TopForm.IsAO2 26 C) (w : ℕ) (hz : Z C w) :
    (gateAt C (w - 26)).op = GateOp.and ∨ ((gateAt C (w - 26)).op = GateOp.or ∧
      ∃ a b, (gateAt C (w - 26)).inputs = [a, b] ∧ a < w ∧ b < w ∧ Z C a ∧ Z C b ∧
        ∀ x : Fin 26 → Bool, val C.gates x w = (val C.gates x a || val C.gates x b)) := by
  obtain ⟨h1, h2, h3⟩ := hz
  obtain ⟨a, b, hab, ha, hb, hop, hv⟩ := gv C hC w h1 h2
  rcases hop with hop | hop
  · exact Or.inl hop
  · right
    have hv' : ∀ x : Fin 26 → Bool, val C.gates x w = (val C.gates x a || val C.gates x b) := by
      intro x; rw [hv x, hop, ev_or]
    have hza : ∀ c, c < w → (∀ v : Fin 26, val C.gates (eof v) w = false → val C.gates (eof v) c = false) →
        Z C c := by
      intro c hc hcv
      refine ⟨?_, by omega, fun v => hcv v (h3 v)⟩
      by_contra hlt
      push_neg at hlt
      have := hcv ⟨c, hlt⟩ (h3 _)
      rw [val_lt C.gates _ c hlt] at this
      simp [eof] at this
    refine ⟨hop, a, b, hab, ha, hb, hza a ha ?_, hza b hb ?_, hv'⟩
    · intro v hv0; rw [hv'] at hv0; simp only [Bool.or_eq_false_iff] at hv0; exact hv0.1
    · intro v hv0; rw [hv'] at hv0; simp only [Bool.or_eq_false_iff] at hv0; exact hv0.2

inductive Reach : ℕ → ℕ → Prop
  | self (w : ℕ) : 26 ≤ w → w < 26 + C.gates.length → (gateAt C (w - 26)).op = GateOp.and →
      Reach w w
  | up (j w a : ℕ) : 26 ≤ w → w < 26 + C.gates.length → (gateAt C (w - 26)).op = GateOp.or →
      a ∈ (gateAt C (w - 26)).inputs → Reach j a → Reach j w

lemma reach_and (hC : PEqualNP.TopForm.IsAO2 26 C) (j w : ℕ) (h : Reach C j w) :
    26 ≤ j ∧ j < 26 + C.gates.length ∧ (gateAt C (j - 26)).op = GateOp.and ∧ j ≤ w := by
  induction h with
  | self h1 h2 h3 => exact ⟨h1, h2, h3, le_rfl⟩
  | up w a h1 h2 _ h4 _ ih =>
    obtain ⟨a', b', hab, ha, hb, _, _⟩ := gv C hC w h1 h2
    rw [hab] at h4
    have : a < w := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h4
      rcases h4 with rfl | rfl <;> assumption
    exact ⟨ih.1, ih.2.1, ih.2.2.1, by omega⟩

lemma reach_val (hC : PEqualNP.TopForm.IsAO2 26 C) (j w : ℕ) (h : Reach C j w) :
    ∀ x : Fin 26 → Bool, val C.gates x j = true → val C.gates x w = true := by
  induction h with
  | self _ _ _ => exact fun x hx => hx
  | up w a h1 h2 h3 h4 _ ih =>
    intro x hx
    obtain ⟨a', b', hab, _, _, _, hv⟩ := gv C hC w h1 h2
    rw [hab] at h4
    rw [hv x, h3, ev_or, Bool.or_eq_true]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h4
    rcases h4 with rfl | rfl
    · exact Or.inl (ih x hx)
    · exact Or.inr (ih x hx)

lemma z_sem (hC : PEqualNP.TopForm.IsAO2 26 C) : ∀ w, Z C w → ∀ x : Fin 26 → Bool,
    val C.gates x w = true → ∃ j, Reach C j w ∧ val C.gates x j = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hz x hx
    rcases z_struct C hC w hz with hop | ⟨hop, a, b, hab, ha, hb, za, zb, hv⟩
    · exact ⟨w, Reach.self w hz.1 hz.2.1 hop, hx⟩
    · rw [hv, Bool.or_eq_true] at hx
      rcases hx with hx | hx
      · obtain ⟨j, hj, hjx⟩ := ih a ha za x hx
        exact ⟨j, Reach.up j w a hz.1 hz.2.1 hop (by rw [hab]; simp) hj, hjx⟩
      · obtain ⟨j, hj, hjx⟩ := ih b hb zb x hx
        exact ⟨j, Reach.up j w b hz.1 hz.2.1 hop (by rw [hab]; simp) hj, hjx⟩

lemma reach_inv (j w : ℕ) (h : Reach C j w) :
    (j = w ∧ 26 ≤ w ∧ w < 26 + C.gates.length ∧ (gateAt C (w - 26)).op = GateOp.and) ∨
    (26 ≤ w ∧ w < 26 + C.gates.length ∧ (gateAt C (w - 26)).op = GateOp.or ∧
      ∃ a ∈ (gateAt C (w - 26)).inputs, Reach C j a) := by
  cases h
  · exact Or.inl ⟨rfl, by assumption, by assumption, by assumption⟩
  · exact Or.inr ⟨by assumption, by assumption, by assumption, _, by assumption, by assumption⟩

noncomputable def A (w : ℕ) : Finset ℕ :=
  (Finset.range (26 + C.gates.length)).filter (fun j => Reach C j w)

lemma mem_A (hC : PEqualNP.TopForm.IsAO2 26 C) (j w : ℕ) : j ∈ A C w ↔ Reach C j w := by
  unfold A
  rw [Finset.mem_filter, Finset.mem_range]
  constructor
  · exact fun h => h.2
  · intro h
    exact ⟨(reach_and C hC j w h).2.1, h⟩

lemma A_and (hC : PEqualNP.TopForm.IsAO2 26 C) (w : ℕ) (h1 : 26 ≤ w)
    (h2 : w < 26 + C.gates.length) (hop : (gateAt C (w - 26)).op = GateOp.and) :
    A C w = {w} := by
  ext j
  rw [mem_A C hC, Finset.mem_singleton]
  constructor
  · intro h
    rcases reach_inv C j w h with ⟨h0, _⟩ | ⟨_, _, h3, _⟩
    · exact h0
    · rw [hop] at h3; exact absurd h3 (by simp)
  · rintro rfl
    exact Reach.self j h1 h2 hop

lemma z_cls (hC : PEqualNP.TopForm.IsAO2 26 C) (w : ℕ) (hz : Z C w) :
    (A C w).card ≤ 1 ∨ ∃ a b, a < w ∧ b < w ∧ Z C a ∧ Z C b ∧ A C w = A C a ∪ A C b := by
  rcases z_struct C hC w hz with hop | ⟨hop, a, b, hab, ha, hb, za, zb, _⟩
  · left; rw [A_and C hC w hz.1 hz.2.1 hop]; simp
  · right
    refine ⟨a, b, ha, hb, za, zb, ?_⟩
    ext j
    rw [Finset.mem_union, mem_A C hC, mem_A C hC, mem_A C hC]
    constructor
    · intro h
      rcases reach_inv C j w h with ⟨_, _, _, h3⟩ | ⟨_, _, _, a0, h4, h5⟩
      · rw [hop] at h3; exact absurd h3 (by simp)
      · rw [hab] at h4
        simp only [List.mem_cons, List.not_mem_nil, or_false] at h4
        rcases h4 with rfl | rfl
        · exact Or.inl h5
        · exact Or.inr h5
    · rintro (h | h)
      · exact Reach.up j w a hz.1 hz.2.1 hop (by rw [hab]; simp) h
      · exact Reach.up j w b hz.1 hz.2.1 hop (by rw [hab]; simp) h

end circ


section stars

variable (C : Circuit)

lemma spec (hF : ∀ x : Fin 26 → Bool, C.eval (List.ofFn x) = true ↔
      ∃ p l : Fin 13, (p = l ∨ p = l + 1 ∨ p = l + 3 ∨ p = l + 9) ∧
        x (Fin.castAdd 13 p) = true ∧ x (Fin.natAdd 13 l) = true) (u v : Fin 26) :
    val C.gates (pr u v) C.output = true ↔ adjB u v = true := by
  have e : val C.gates (pr u v) C.output = C.eval (List.ofFn (pr u v)) := rfl
  rw [e, hF]
  constructor
  · rintro ⟨p, l, hpl, h1, h2⟩
    rw [inc_iff] at hpl
    have hc := adj_cl p l hpl
    simp only [pr, decide_eq_true_eq] at h1 h2
    have hne := cl_ne p l
    rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
    · exact absurd (h1.trans h2.symm) hne
    · rw [← h1, ← h2]; exact hc
    · rw [← h1, ← h2, adj_symm]; exact hc
    · exact absurd (h1.trans h2.symm) hne
  · intro h
    unfold adjB at h
    simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
    rcases h with ⟨⟨h1, h2⟩, h3⟩ | ⟨⟨h1, h2⟩, h3⟩
    · refine ⟨⟨u.val, h1⟩, ⟨v.val - 13, by omega⟩, (inc_iff _ _).mpr h3, ?_, ?_⟩
      · simp only [pr, decide_eq_true_eq]; left; apply Fin.ext; rfl
      · simp only [pr, decide_eq_true_eq]; right; apply Fin.ext
        show 13 + (v.val - 13) = v.val; omega
    · refine ⟨⟨v.val, h1⟩, ⟨u.val - 13, by omega⟩, (inc_iff _ _).mpr h3, ?_, ?_⟩
      · simp only [pr, decide_eq_true_eq]; right; apply Fin.ext; rfl
      · simp only [pr, decide_eq_true_eq]; left; apply Fin.ext
        show 13 + (u.val - 13) = u.val; omega

lemma pr_self (v : Fin 26) : pr v v = eof v := by
  funext c; simp [pr, eof]

lemma out_Z (hout : ∀ u v : Fin 26, val C.gates (pr u v) C.output = true ↔ adjB u v = true) :
    Z C C.output := by
  have hf : ∀ v : Fin 26, val C.gates (eof v) C.output = false := by
    intro v
    rw [← pr_self]
    cases hv : val C.gates (pr v v) C.output
    · rfl
    · rw [hout, adj_irr] at hv; exact absurd hv (by simp)
  refine ⟨?_, ?_, hf⟩
  · by_contra h
    push_neg at h
    have := hf ⟨C.output, h⟩
    rw [val_lt C.gates _ _ h] at this
    simp [eof] at this
  · by_contra h
    push_neg at h
    have h1 := (hout (Fin.castAdd 13 (0 : Fin 13)) (Fin.natAdd 13 (0 : Fin 13))).mpr (adj_diag 0)
    rw [val_ge C.gates _ _ h] at h1
    exact absurd h1 (by simp)

def ia (j : ℕ) : ℕ := (gateAt C (j - 26)).inputs.getD 0 0

def ib (j : ℕ) : ℕ := (gateAt C (j - 26)).inputs.getD 1 0

lemma star (hC : PEqualNP.TopForm.IsAO2 26 C)
    (hno : ¬∃ x4 x5 : ℕ, (gateAt C x4).op = GateOp.and ∧ (gateAt C x5).op = GateOp.and ∧
      InCone 26 C x4 x5) (j : ℕ) (hj : Reach C j C.output) :
    Lin C (ia C j) ∧ Lin C (ib C j) ∧ ia C j < j ∧ ib C j < j ∧
      ∀ u v : Fin 26, (val C.gates (pr u v) j = true ↔
        (u ∈ S C (ia C j) ∨ v ∈ S C (ia C j)) ∧ (u ∈ S C (ib C j) ∨ v ∈ S C (ib C j))) := by
  obtain ⟨h1, h2, hop, _⟩ := reach_and C hC j _ hj
  obtain ⟨a, b, hab, ha, hb, _, hv⟩ := gv C hC j h1 h2
  have ea : ia C j = a := by simp [ia, hab]
  have eb : ib C j = b := by simp [ib, hab]
  rw [ea, eb]
  have hk : j - 26 < C.gates.length := by omega
  have hfree : ∀ i, (gateAt C i).op = GateOp.and → ¬ InCone 26 C i (j - 26) :=
    fun i hi hc => hno ⟨i, j - 26, hi, hop, hc⟩
  have la := input_lin C (j - 26) a hk (by rw [hab]; simp) (by omega) hfree
  have lb := input_lin C (j - 26) b hk (by rw [hab]; simp) (by omega) hfree
  refine ⟨la, lb, ha, hb, fun u v => ?_⟩
  rw [hv, hop, ev_and, Bool.and_eq_true, lin_sem C hC a la, lin_sem C hC b lb]

lemma star2 (hC : PEqualNP.TopForm.IsAO2 26 C)
    (hno : ¬∃ x4 x5 : ℕ, (gateAt C x4).op = GateOp.and ∧ (gateAt C x5).op = GateOp.and ∧
      InCone 26 C x4 x5)
    (hout : ∀ u v : Fin 26, val C.gates (pr u v) C.output = true ↔ adjB u v = true)
    (j : ℕ) (hj : Reach C j C.output) :
    (∀ v, ¬ (v ∈ S C (ia C j) ∧ v ∈ S C (ib C j))) ∧
    (∀ u ∈ S C (ia C j), ∀ v ∈ S C (ib C j), adjB u v = true) ∧
    ((S C (ia C j)).card = 1 ∨ (S C (ib C j)).card = 1) := by
  obtain ⟨la, lb, _, _, hs⟩ := star C hC hno j hj
  have hadj : ∀ u v, val C.gates (pr u v) j = true → adjB u v = true := by
    intro u v h
    exact (hout u v).mp (reach_val C hC j _ hj _ h)
  have hd : ∀ v, ¬ (v ∈ S C (ia C j) ∧ v ∈ S C (ib C j)) := by
    rintro v ⟨h1, h2⟩
    have := hadj v v ((hs v v).mpr ⟨Or.inl h1, Or.inl h2⟩)
    rw [adj_irr] at this
    exact absurd this (by simp)
  have hc : ∀ u ∈ S C (ia C j), ∀ v ∈ S C (ib C j), adjB u v = true :=
    fun u hu v hv => hadj u v ((hs u v).mpr ⟨Or.inl hu, Or.inr hv⟩)
  refine ⟨hd, hc, ?_⟩
  by_contra hne
  push_neg at hne
  have n1 := (lin_ne C hC _ la).card_pos
  have n2 := (lin_ne C hC _ lb).card_pos
  obtain ⟨p1, hp1, p2, hp2, hp⟩ := Finset.one_lt_card.mp (show 1 < (S C (ia C j)).card by omega)
  obtain ⟨q1, hq1, q2, hq2, hq⟩ := Finset.one_lt_card.mp (show 1 < (S C (ib C j)).card by omega)
  have := common p1 p2 hp
  have := Finset.card_le_one.mp this q1 (by simp [hc p1 hp1 q1 hq1, hc p2 hp2 q1 hq1])
    q2 (by simp [hc p1 hp1 q2 hq2, hc p2 hp2 q2 hq2])
  exact hq this

def cw (j : ℕ) : ℕ := if (S C (ia C j)).card = 1 then ia C j else ib C j

def lw (j : ℕ) : ℕ := if (S C (ia C j)).card = 1 then ib C j else ia C j

lemma cw_facts (hC : PEqualNP.TopForm.IsAO2 26 C)
    (hno : ¬∃ x4 x5 : ℕ, (gateAt C x4).op = GateOp.and ∧ (gateAt C x5).op = GateOp.and ∧
      InCone 26 C x4 x5)
    (hout : ∀ u v : Fin 26, val C.gates (pr u v) C.output = true ↔ adjB u v = true)
    (j : ℕ) (hj : Reach C j C.output) :
    (S C (cw C j)).card = 1 ∧ Lin C (lw C j) ∧ lw C j < j ∧
      (∀ c ∈ S C (cw C j), ∀ y ∈ S C (lw C j), adjB c y = true) := by
  obtain ⟨la, lb, ha, hb, _⟩ := star C hC hno j hj
  obtain ⟨_, hc, h1⟩ := star2 C hC hno hout j hj
  by_cases h : (S C (ia C j)).card = 1
  · simp only [cw, lw, if_pos h]
    exact ⟨h, lb, hb, hc⟩
  · simp only [cw, lw, if_neg h]
    refine ⟨h1.resolve_left h, la, ha, fun c hc' y hy => ?_⟩
    rw [adj_symm]
    exact hc y hy c hc'

lemma cover (hC : PEqualNP.TopForm.IsAO2 26 C)
    (hno : ¬∃ x4 x5 : ℕ, (gateAt C x4).op = GateOp.and ∧ (gateAt C x5).op = GateOp.and ∧
      InCone 26 C x4 x5)
    (hout : ∀ u v : Fin 26, val C.gates (pr u v) C.output = true ↔ adjB u v = true)
    (u v : Fin 26) (huv : adjB u v = true) :
    ∃ j, Reach C j C.output ∧ ((u ∈ S C (cw C j) ∧ v ∈ S C (lw C j)) ∨
      (v ∈ S C (cw C j) ∧ u ∈ S C (lw C j))) := by
  obtain ⟨j, hj, hv⟩ := z_sem C hC _ (out_Z C hout) _ ((hout u v).mpr huv)
  refine ⟨j, hj, ?_⟩
  obtain ⟨_, _, _, _, hs⟩ := star C hC hno j hj
  obtain ⟨hd, _, _⟩ := star2 C hC hno hout j hj
  have h := (hs u v).mp hv
  have hu := hd u
  have hv' := hd v
  by_cases hc : (S C (ia C j)).card = 1
  · simp only [cw, lw, if_pos hc]
    tauto
  · simp only [cw, lw, if_neg hc]
    tauto

end stars


section count

variable (C : Circuit)

lemma dbl (s : Finset ℕ) (T : ℕ → Finset (Fin 26)) (h : ∀ j ∈ s, (T j).card = 1) :
    ∑ c : Fin 26, (s.filter (fun j => c ∈ T j)).card = s.card := by
  simp only [Finset.card_filter]
  rw [Finset.sum_comm]
  have : ∀ j ∈ s, ∑ c : Fin 26, (if c ∈ T j then 1 else 0) = 1 := by
    intro j hj
    rw [Finset.sum_boole]
    simp [Finset.filter_mem_eq_inter, h j hj]
  rw [Finset.sum_congr rfl this]
  simp

noncomputable def G (c : Fin 26) : Finset ℕ :=
  (A C C.output).filter (fun j => c ∈ S C (cw C j))

noncomputable def D (c : Fin 26) : Finset (Fin 26) := (G C c).biUnion (fun j => S C (lw C j))

noncomputable def Lc (c : Fin 26) : Finset ℕ := (Finset.range (26 + C.gates.length)).filter
  (fun k => Lin C k ∧ 2 ≤ (S C k).card ∧ S C k ⊆ D C c)

noncomputable def LL : Finset ℕ := (Finset.range (26 + C.gates.length)).filter
  (fun k => Lin C k ∧ 2 ≤ (S C k).card)

noncomputable def PU : Finset ℕ := (Finset.range (26 + C.gates.length)).filter
  (fun k => Z C k ∧ 2 ≤ (A C k).card ∧ A C k ⊆ A C C.output)

lemma memG (c : Fin 26) (j : ℕ) : j ∈ G C c ↔ j ∈ A C C.output ∧ c ∈ S C (cw C j) := by
  simp [G]

lemma memD (c y : Fin 26) : y ∈ D C c ↔ ∃ j ∈ G C c, y ∈ S C (lw C j) := by
  simp [D]

variable (hC : PEqualNP.TopForm.IsAO2 26 C)
    (hno : ¬∃ x4 x5 : ℕ, (gateAt C x4).op = GateOp.and ∧ (gateAt C x5).op = GateOp.and ∧
      InCone 26 C x4 x5)
    (hout : ∀ u v : Fin 26, val C.gates (pr u v) C.output = true ↔ adjB u v = true)

include hC hno hout in
lemma dn (c : Fin 26) : ∀ y ∈ D C c, adjB c y = true := by
  intro y hy
  obtain ⟨j, hjG, hy⟩ := (memD C c y).mp hy
  obtain ⟨hjA, hc⟩ := (memG C c j).mp hjG
  exact (cw_facts C hC hno hout j ((mem_A C hC j _).mp hjA)).2.2.2 c hc y hy

include hC hno hout in
lemma dc_le (c : Fin 26) : (D C c).card ≤ (G C c).card + (Lc C c).card := by
  have hW : ∀ w ∈ (G C c).image (lw C), w < 26 + C.gates.length ∧ Lin C w := by
    intro w hw
    obtain ⟨j, hjG, rfl⟩ := Finset.mem_image.mp hw
    obtain ⟨hjA, _⟩ := (memG C c j).mp hjG
    have hr := (mem_A C hC j _).mp hjA
    obtain ⟨_, hl, hlt, _⟩ := cw_facts C hC hno hout j hr
    have := (reach_and C hC j _ hr).2.1
    exact ⟨by omega, hl⟩
  have h := leaf_count (Lin C) (S C) (lin_cls C hC) _ _ hW
  rw [Finset.image_biUnion] at h
  have hi : ((G C c).image (lw C)).card ≤ (G C c).card := Finset.card_image_le
  have h' : (D C c).card ≤ ((G C c).image (lw C)).card + (Lc C c).card := h
  omega

include hC hno hout in
lemma lsum : ∑ c : Fin 26, (Lc C c).card ≤ (LL C).card := by
  have hdisj : ((Finset.univ : Finset (Fin 26)) : Set (Fin 26)).PairwiseDisjoint (Lc C) := by
    intro c _ c' _ hne
    show Disjoint (Lc C c) (Lc C c')
    rw [Finset.disjoint_left]
    intro k hk hk'
    simp only [Lc, Finset.mem_filter] at hk hk'
    obtain ⟨y1, hy1, y2, hy2, hy⟩ := Finset.one_lt_card.mp (show 1 < (S C k).card by omega)
    have a1 := dn C hC hno hout c y1 (hk.2.2.2 hy1)
    have a2 := dn C hC hno hout c y2 (hk.2.2.2 hy2)
    have b1 := dn C hC hno hout c' y1 (hk'.2.2.2 hy1)
    have b2 := dn C hC hno hout c' y2 (hk'.2.2.2 hy2)
    have := Finset.card_le_one.mp (common c c' hne) y1 (by simp [a1, b1]) y2 (by simp [a2, b2])
    exact hy this
  rw [← Finset.card_biUnion hdisj]
  apply Finset.card_le_card
  intro k hk
  rw [Finset.mem_biUnion] at hk
  obtain ⟨c, _, hk⟩ := hk
  simp only [Lc, LL, Finset.mem_filter] at hk ⊢
  exact ⟨hk.1, hk.2.1, hk.2.2.1⟩

include hC hno hout in
lemma e_le : 104 ≤ 2 * ∑ c : Fin 26, (D C c).card := by
  set I : Finset (Fin 26 × Fin 26) :=
    Finset.univ.biUnion (fun c => (D C c).image (fun y => (c, y))) with hI
  have h1 : I.card ≤ ∑ c : Fin 26, (D C c).card :=
    le_trans Finset.card_biUnion_le (Finset.sum_le_sum fun c _ => Finset.card_image_le)
  have h2 : (Finset.univ.filter (fun p : Fin 26 × Fin 26 => adjB p.1 p.2 = true)) ⊆
      I ∪ I.image Prod.swap := by
    intro p hp
    rw [Finset.mem_filter] at hp
    obtain ⟨j, hj, h⟩ := cover C hC hno hout p.1 p.2 hp.2
    have hjA : j ∈ A C C.output := (mem_A C hC j _).mpr hj
    rcases h with ⟨hu, hv⟩ | ⟨hv, hu⟩
    · apply Finset.mem_union_left
      rw [hI, Finset.mem_biUnion]
      refine ⟨p.1, Finset.mem_univ _, Finset.mem_image.mpr ⟨p.2, ?_, rfl⟩⟩
      exact (memD C _ _).mpr ⟨j, (memG C _ _).mpr ⟨hjA, hu⟩, hv⟩
    · apply Finset.mem_union_right
      rw [Finset.mem_image]
      refine ⟨(p.2, p.1), ?_, rfl⟩
      rw [hI, Finset.mem_biUnion]
      refine ⟨p.2, Finset.mem_univ _, Finset.mem_image.mpr ⟨p.1, ?_, rfl⟩⟩
      exact (memD C _ _).mpr ⟨j, (memG C _ _).mpr ⟨hjA, hv⟩, hu⟩
  have h3 := Finset.card_le_card h2
  rw [ecard] at h3
  have h4 := Finset.card_union_le I (I.image Prod.swap)
  have h5 : (I.image Prod.swap).card ≤ I.card := Finset.card_image_le
  omega

include hC hno hout in
lemma gsum : ∑ c : Fin 26, (G C c).card = (A C C.output).card :=
  dbl (A C C.output) (fun j => S C (cw C j))
    (fun j hj => (cw_facts C hC hno hout j ((mem_A C hC j _).mp hj)).1)

include hC hno hout in
lemma cen : 13 ≤ (A C C.output).card := by
  set Cen := Finset.univ.filter (fun c : Fin 26 => (G C c).Nonempty) with hCen
  set f : Fin 26 → Fin 13 := fun c => ⟨c.val % 13, Nat.mod_lt _ (by norm_num)⟩ with hf
  have h1 : (Finset.univ : Finset (Fin 13)) ⊆ Cen.image f := by
    intro p _
    rw [Finset.mem_image]
    have hp := p.isLt
    obtain ⟨j, hj, h⟩ := cover C hC hno hout _ _ (adj_diag p)
    have hjA : j ∈ A C C.output := (mem_A C hC j _).mpr hj
    rcases h with ⟨hu, _⟩ | ⟨hv, _⟩
    · refine ⟨Fin.castAdd 13 p, ?_, ?_⟩
      · rw [hCen, Finset.mem_filter]
        exact ⟨Finset.mem_univ _, j, (memG C _ _).mpr ⟨hjA, hu⟩⟩
      · apply Fin.ext
        show p.val % 13 = p.val
        omega
    · refine ⟨Fin.natAdd 13 p, ?_, ?_⟩
      · rw [hCen, Finset.mem_filter]
        exact ⟨Finset.mem_univ _, j, (memG C _ _).mpr ⟨hjA, hv⟩⟩
      · apply Fin.ext
        show (13 + p.val) % 13 = p.val
        omega
  have h2 := Finset.card_le_card h1
  have h3 : (Cen.image f).card ≤ Cen.card := Finset.card_image_le
  have h4 : Cen.card ≤ ∑ c : Fin 26, (G C c).card := by
    rw [Finset.card_eq_sum_ones]
    calc ∑ c ∈ Cen, 1 ≤ ∑ c ∈ Cen, (G C c).card := Finset.sum_le_sum (fun c hc => by
            rw [hCen, Finset.mem_filter] at hc; exact hc.2.card_pos)
      _ ≤ ∑ c : Fin 26, (G C c).card := Finset.sum_le_sum_of_subset (Finset.subset_univ _)
  rw [gsum C hC hno hout] at h4
  simp only [Finset.card_univ, Fintype.card_fin] at h2
  omega

include hC hout in
lemma pu_le : (A C C.output).card ≤ 1 + (PU C).card := by
  have hz := out_Z C hout
  have h := leaf_count (Z C) (A C) (z_cls C hC) (26 + C.gates.length) {C.output} (by
    intro w hw
    rw [Finset.mem_singleton] at hw
    subst hw
    exact ⟨hz.2.1, hz⟩)
  rw [Finset.singleton_biUnion, Finset.card_singleton] at h
  exact h

include hC in
lemma size_le : (LL C).card + (A C C.output).card + (PU C).card ≤ C.gates.length := by
  have hLL : ∀ k ∈ LL C, 26 ≤ k ∧ k < 26 + C.gates.length ∧
      (gateAt C (k - 26)).op = GateOp.or := by
    intro k hk
    simp only [LL, Finset.mem_filter, Finset.mem_range] at hk
    have h26 : 26 ≤ k := by
      by_contra h
      push_neg at h
      have := hk.2.2
      rw [S_inp C k h, Finset.card_singleton] at this
      omega
    obtain ⟨_, _, _, _, _, _, hor, _⟩ := lin_struct C hC k hk.2.1 h26
    exact ⟨h26, hk.1, hor⟩
  have hAA : ∀ k ∈ A C C.output, 26 ≤ k ∧ k < 26 + C.gates.length ∧
      (gateAt C (k - 26)).op = GateOp.and := by
    intro k hk
    obtain ⟨h1, h2, h3, _⟩ := reach_and C hC k _ ((mem_A C hC k _).mp hk)
    exact ⟨h1, h2, h3⟩
  have hPP : ∀ k ∈ PU C, Z C k ∧ 2 ≤ (A C k).card := by
    intro k hk
    simp only [PU, Finset.mem_filter] at hk
    exact ⟨hk.2.1, hk.2.2.1⟩
  have d1 : Disjoint (LL C) (A C C.output) := by
    rw [Finset.disjoint_left]
    intro k h1 h2
    have := (hLL k h1).2.2
    rw [(hAA k h2).2.2] at this
    exact absurd this (by simp)
  have d2 : Disjoint (LL C ∪ A C C.output) (PU C) := by
    rw [Finset.disjoint_left]
    intro k h1 h2
    obtain ⟨hz, h2c⟩ := hPP k h2
    rcases Finset.mem_union.mp h1 with h1 | h1
    · simp only [LL, Finset.mem_filter] at h1
      have : S C k = ∅ := by
        apply Finset.eq_empty_of_forall_notMem
        intro v hv
        rw [mem_S, hz.2.2 v] at hv
        exact absurd hv (by simp)
      rw [this] at h1
      simp at h1
    · obtain ⟨a1, a2, a3⟩ := hAA k h1
      rw [A_and C hC k a1 a2 a3, Finset.card_singleton] at h2c
      omega
  have hsub : LL C ∪ A C C.output ∪ PU C ⊆ Finset.Ico 26 (26 + C.gates.length) := by
    intro k hk
    rw [Finset.mem_Ico]
    rcases Finset.mem_union.mp hk with hk | hk
    · rcases Finset.mem_union.mp hk with hk | hk
      · exact ⟨(hLL k hk).1, (hLL k hk).2.1⟩
      · exact ⟨(hAA k hk).1, (hAA k hk).2.1⟩
    · exact ⟨(hPP k hk).1.1, (hPP k hk).1.2.1⟩
  have := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint d2, Finset.card_union_of_disjoint d1, Nat.card_Ico] at this
  omega

end count

theorem main (C : Circuit) (hC : PEqualNP.TopForm.IsAO2 26 C)
    (hF : ∀ x : Fin 26 → Bool, C.eval (List.ofFn x) = true ↔
      ∃ p l : Fin 13, (p = l ∨ p = l + 1 ∨ p = l + 3 ∨ p = l + 9) ∧
        x (Fin.castAdd 13 p) = true ∧ x (Fin.natAdd 13 l) = true)
    (hno : ¬∃ x4 x5 : ℕ, (gateAt C x4).op = GateOp.and ∧ (gateAt C x5).op = GateOp.and ∧
      InCone 26 C x4 x5) : 64 ≤ C.size := by
  have hout := spec C hF
  have e1 := e_le C hC hno hout
  have e2 : ∑ c : Fin 26, (D C c).card ≤ (A C C.output).card + (LL C).card := by
    calc ∑ c : Fin 26, (D C c).card ≤ ∑ c : Fin 26, ((G C c).card + (Lc C c).card) :=
          Finset.sum_le_sum (fun c _ => dc_le C hC hno hout c)
      _ = ∑ c : Fin 26, (G C c).card + ∑ c : Fin 26, (Lc C c).card := Finset.sum_add_distrib
      _ ≤ (A C C.output).card + (LL C).card := by
          rw [gsum C hC hno hout]
          exact Nat.add_le_add_left (lsum C hC hno hout) _
  have e3 := cen C hC hno hout
  have e4 := pu_le C hC hout
  have e5 := size_le C hC
  show 64 ≤ C.gates.length
  omega

end PEqualNP.Outside.L_meta_4803_aux

theorem PEqualNP.Outside.L_meta_4803 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 (26 : ℕ) x1 → (∀ (x3 : Fin (26 : ℕ) → Bool), x1.eval (List.ofFn x3) = Bool.true ↔ ∃ (x4 : Fin (13 : ℕ)) (x5 : Fin (13 : ℕ)), (x4 = x5 ∨ x4 = x5 + (1 : Fin (13 : ℕ)) ∨ x4 = x5 + (3 : Fin (13 : ℕ)) ∨ x4 = x5 + (9 : Fin (13 : ℕ))) ∧ x3 (Fin.castAdd (13 : ℕ) x4) = Bool.true ∧ x3 (Fin.natAdd (13 : ℕ) x5) = Bool.true) → (¬∃ (x4 : ℕ) (x5 : ℕ), (PEqualNP.MetaComplexity.NestedCover.gateAt x1 x4).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x1 x5).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ PEqualNP.EdgeOwnership.InCone (26 : ℕ) x1 x4 x5) → (64 : ℕ) ≤ x1.size := by
  intro x1 hC hF hno
  exact PEqualNP.Outside.L_meta_4803_aux.main x1 hC hF hno
