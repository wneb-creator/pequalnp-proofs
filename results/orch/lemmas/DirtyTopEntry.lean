import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_9811.DirtyReader
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
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
      · rw [if_pos hi, foldl_getD_lt gs (stepWire w g) i (by simp [stepWire]; omega)]
        simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
      · rw [if_neg hi]; exact getD_ge w i (by omega)
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

lemma eval_eq_val (C : Circuit) (x : List Bool) : C.eval x = val C x C.output := rfl

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
    · rw [if_pos hlt] at h; exact ⟨i, hi, hlt, h⟩
    · rw [if_neg hlt] at h; cases h
  · rintro ⟨i, hi, hlt, h⟩
    exact ⟨i, hi, by rw [if_pos hlt]; exact h⟩

lemma val_and {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {r : ℕ}
    (hr : r < C.gates.length) (hop : (gateAt C r).op = GateOp.and) :
    val C x (n + r) = true ↔ ∀ i ∈ (gateAt C r).inputs, i < n + r ∧ val C x i = true := by
  rw [val_gate hx hr, hop]
  simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id_eq]
  constructor
  · intro h i hi
    have h' := h i hi
    by_cases hlt : i < n + r
    · rw [if_pos hlt] at h'; exact ⟨hlt, h'⟩
    · rw [if_neg hlt] at h'; cases h'
  · intro h i hi
    rw [if_pos (h i hi).1]; exact (h i hi).2

lemma val_ofFn {n : ℕ} (C : Circuit) (x : Fin n → Bool) (u : Fin n) :
    val C (List.ofFn x) u.val = x u := by
  rw [val_input (n := n) (by simp) u.isLt]
  simp [List.getD_eq_getElem?_getD]

lemma gateVal_eq_val (n : ℕ) (C : Circuit) (j : ℕ) (x : Fin n → Bool) :
    PEqualNP.EdgeOwnership.gateVal n C j x = val C (List.ofFn x) (n + j) := rfl


open PEqualNP.CleanedNonEdge

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


open PEqualNP.TopForm PEqualNP.EdgeOwnership

lemma chain {n : ℕ} {C : Circuit} (g : ℕ) :
    ∀ w, OrReaches n C w g → w = n + g ∨
      ∃ h, h < C.gates.length ∧ (gateAt C h).op = GateOp.or ∧
        n + g ∈ (gateAt C h).inputs ∧ g < h := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro h
    have hnw : n ≤ w := h.1
    obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
    obtain ⟨hk, h3⟩ := (orReaches_iff n C k g).mp h
    rcases h3 with rfl | ⟨hop, i, hi, hlt, hr⟩
    · exact Or.inl rfl
    · rcases ih i hlt hr with rfl | h4
      · exact Or.inr ⟨k, hk, hop, hi, by omega⟩
      · exact Or.inr h4

lemma orIn_and {n : ℕ} {C : Circuit} {g : ℕ} (hop : (gateAt C g).op = GateOp.and) :
    orIn n C (n + g) = ∅ := by
  apply Finset.eq_empty_of_forall_notMem
  intro i hi
  simp only [PEqualNP.TopForm.orIn, Finset.mem_filter, Finset.mem_univ, true_and] at hi
  rcases hi with h | ⟨k, hk, hr, hko, _⟩
  · have := i.isLt; omega
  · obtain ⟨_, h3⟩ := (orReaches_iff n C g k).mp hr
    rcases h3 with rfl | ⟨ho, _⟩
    · rw [hop] at hko; cases hko
    · rw [hop] at ho; cases ho


lemma bad_or_reader_extra {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (g h : ℕ)
    (hbad : ¬ BelowF G C g) (hempty : orIn n C (n + g) = ∅)
    (hh : h < C.gates.length) (hop : (gateAt C h).op = GateOp.or)
    (hin : n + g ∈ (gateAt C h).inputs) (hlt : g < h)
    (hlen : (gateAt C h).inputs.length = 2) :
    h ∈ orN G C \ lam G C := by
  rw [Finset.mem_sdiff]
  constructor
  · simp only [orN, gatesWhere, Finset.mem_filter, Finset.mem_range]
    refine ⟨hh, hop, ?_⟩
    intro hb
    apply hbad
    intro x hx
    have hv : gateVal n C h x = true := by
      rw [gateVal_eq_val]
      exact (val_or (n := n) (by simp) hh hop).mpr ⟨n + g, hin, by omega, hx⟩
    exact hb x hv
  · intro hl
    unfold lam at hl
    rw [Finset.mem_filter] at hl
    obtain ⟨_, h0, h1, _⟩ := hl
    match hi : (gateAt C h).inputs, hlen with
    | [u0, u1], _ =>
      rw [hi] at hin
      simp only [opnd, hi] at h0 h1
      simp at hin h0 h1
      rcases hin with e | e
      · rw [← e, hempty] at h0
        simp at h0
      · rw [← e, hempty] at h1
        simp at h1

lemma unique_bad_readers {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hcount : (orN G C \ lam G C).card ≤ 1)
    (g h k l : ℕ)
    (hbadg : ¬ BelowF G C g) (hemptyg : orIn n C (n + g) = ∅)
    (hh : h < C.gates.length) (hoph : (gateAt C h).op = GateOp.or)
    (hinh : n + g ∈ (gateAt C h).inputs) (hlth : g < h)
    (hlenh : (gateAt C h).inputs.length = 2)
    (hbadk : ¬ BelowF G C k) (hemptyk : orIn n C (n + k) = ∅)
    (hl : l < C.gates.length) (hopl : (gateAt C l).op = GateOp.or)
    (hinl : n + k ∈ (gateAt C l).inputs) (hltl : k < l)
    (hlenl : (gateAt C l).inputs.length = 2) : h = l := by
  apply Finset.card_le_one.mp hcount
  · exact bad_or_reader_extra G C g h hbadg hemptyg hh hoph hinh hlth hlenh
  · exact bad_or_reader_extra G C k l hbadk hemptyk hl hopl hinl hltl hlenl


lemma orIn_empty_of_inputs {n : ℕ} (C : Circuit) (h : ℕ)
    (hempty : ∀ w ∈ (gateAt C h).inputs, orIn n C w = ∅) :
    orIn n C (n + h) = ∅ := by
  apply Finset.eq_empty_of_forall_notMem
  intro v hv
  simp only [orIn, Finset.mem_filter, Finset.mem_univ, true_and] at hv
  rcases hv with hh | ⟨k,hk,hr,hop,hv⟩
  · have := v.isLt
    omega
  · obtain ⟨_, hreach⟩ := (orReaches_iff n C h k).mp hr
    rcases hreach with rfl | ⟨_,w,hw,_,hwr⟩
    · have hm : v ∈ orIn n C (v : ℕ) := by
        simp [orIn]
      rw [hempty _ hv] at hm
      simp at hm
    · have hm : v ∈ orIn n C w := by
        simp only [orIn, Finset.mem_filter, Finset.mem_univ, true_and]
        exact Or.inr ⟨k,hk,hwr,hop,hv⟩
      rw [hempty w hw] at hm
      simp at hm

lemma bad_or_reader_bad {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (g h : ℕ) (hbad : ¬ BelowF G C g)
    (hh : h < C.gates.length) (hop : (gateAt C h).op = GateOp.or)
    (hin : n + g ∈ (gateAt C h).inputs) (hlt : g < h) :
    ¬ BelowF G C h := by
  intro hb
  apply hbad
  intro x hx
  apply hb x
  rw [gateVal_eq_val]
  exact (val_or (n := n) (by simp) hh hop).mpr ⟨n + g, hin, by omega, hx⟩

lemma no_empty_or_chain {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hcount : (orN G C \ lam G C).card ≤ 1)
    (g h l : ℕ)
    (hbadg : ¬ BelowF G C g) (hemptyg : orIn n C (n + g) = ∅)
    (hh : h < C.gates.length) (hoph : (gateAt C h).op = GateOp.or)
    (hinh : n + g ∈ (gateAt C h).inputs) (hlth : g < h)
    (hlenh : (gateAt C h).inputs.length = 2)
    (hemptyh : orIn n C (n + h) = ∅)
    (hl : l < C.gates.length) (hopl : (gateAt C l).op = GateOp.or)
    (hinl : n + h ∈ (gateAt C l).inputs) (hltl : h < l)
    (hlenl : (gateAt C l).inputs.length = 2) : False := by
  have hbadh := bad_or_reader_bad G C g h hbadg hh hoph hinh hlth
  have he := unique_bad_readers G C hcount g h h l hbadg hemptyg hh hoph hinh hlth hlenh
    hbadh hemptyh hl hopl hinl hltl hlenl
  omega

lemma chain_with_reaches {n : ℕ} {C : Circuit} (g : ℕ) :
    ∀ w, OrReaches n C w g → w = n + g ∨
      ∃ h, h < C.gates.length ∧ (gateAt C h).op = GateOp.or ∧
        n + g ∈ (gateAt C h).inputs ∧ g < h ∧ OrReaches n C w h := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro h
    have hnw : n ≤ w := h.1
    obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
    obtain ⟨hk, h3⟩ := (orReaches_iff n C k g).mp h
    rcases h3 with rfl | ⟨hop, i, hi, hlt, hr⟩
    · exact Or.inl rfl
    · rcases ih i hlt hr with rfl | ⟨q,hq,hqo,hqi,hqg,hqr⟩
      · exact Or.inr ⟨k,hk,hop,hi,by omega,(orReaches_iff n C k k).mpr ⟨hk,Or.inl rfl⟩⟩
      · refine Or.inr ⟨q,hq,hqo,hqi,hqg,?_⟩
        exact (orReaches_iff n C k q).mpr ⟨hk,Or.inr ⟨hop,i,hi,hlt,hqr⟩⟩

lemma unique_dirty_entry {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hcount : (orN G C \ lam G C).card ≤ 1)
    (h2 : ∀ h < C.gates.length, (gateAt C h).inputs.length = 2)
    (g k w z : ℕ)
    (hbadg : ¬ BelowF G C g) (hemptyg : orIn n C (n + g) = ∅)
    (hbadk : ¬ BelowF G C k) (hemptyk : orIn n C (n + k) = ∅)
    (hw : (orIn n C w).Nonempty) (hz : (orIn n C z).Nonempty)
    (hwg : OrReaches n C w g) (hzk : OrReaches n C z k) : g = k := by
  by_contra hne
  obtain ⟨h,hh,hop,hgin,hgh,hwh⟩ : ∃ h, h < C.gates.length ∧
      (gateAt C h).op = GateOp.or ∧ n + g ∈ (gateAt C h).inputs ∧ g < h ∧ OrReaches n C w h := by
    rcases chain_with_reaches g w hwg with rfl | h
    · rw [hemptyg] at hw
      simp at hw
    · exact h
  obtain ⟨l,hl,lop,hkin,hkl,_⟩ : ∃ l, l < C.gates.length ∧
      (gateAt C l).op = GateOp.or ∧ n + k ∈ (gateAt C l).inputs ∧ k < l ∧ OrReaches n C z l := by
    rcases chain_with_reaches k z hzk with rfl | h
    · rw [hemptyk] at hz
      simp at hz
    · exact h
  have he := unique_bad_readers G C hcount g h k l hbadg hemptyg hh hop hgin hgh (h2 h hh)
    hbadk hemptyk hl lop hkin hkl (h2 l hl)
  subst l
  have hin : ∀ a ∈ (gateAt C h).inputs, a = n + g ∨ a = n + k := by
    intro x hx
    have hlen := h2 h hh
    match hi : (gateAt C h).inputs, hlen with
    | [a,b], _ =>
      simp only [hi, List.mem_cons, List.not_mem_nil, or_false] at hgin hkin hx
      omega
  have hemptyh : orIn n C (n + h) = ∅ := by
    apply orIn_empty_of_inputs C h
    intro a ha
    rcases hin a ha with rfl | rfl
    · exact hemptyg
    · exact hemptyk
  obtain ⟨l,hl,lop,hlin,hhl,_⟩ : ∃ l, l < C.gates.length ∧
      (gateAt C l).op = GateOp.or ∧ n + h ∈ (gateAt C l).inputs ∧ h < l ∧ OrReaches n C w l := by
    rcases chain_with_reaches h w hwh with he | h
    · rw [he,hemptyh] at hw
      simp at hw
    · exact h
  exact no_empty_or_chain G C hcount g h l hbadg hemptyg hh hop hgin hgh (h2 h hh)
    hemptyh hl lop hlin hhl (h2 l hl)


lemma dirty_support {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (g : ℕ) (hg : g ∈ junk G C) :
    ¬ BelowF G C g ∧ orIn n C (n + g) = ∅ := by
  unfold junk gatesWhere at hg
  have hd := (Finset.mem_filter.mp hg).2
  unfold IsDirtyAnd IsDirty at hd
  obtain ⟨hop,_,x,hx,hf⟩ := hd
  refine ⟨?_,orIn_and hop⟩
  intro hb
  have he := hb x hx
  rw [hf] at he
  cases he

lemma top_side_nonempty {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (a : ℕ) (ha : a ∈ tops G C) (hn : a ∉ centreless G C)
    (b : Fin 2) : (orIn n C (opnd C a b)).Nonempty := by
  apply Finset.nonempty_iff_ne_empty.mpr
  intro he
  apply hn
  apply Finset.mem_filter.mpr
  refine ⟨ha,?_⟩
  fin_cases b
  · exact Or.inl he
  · exact Or.inr he

lemma unique_top_dirty_entry {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hcount : (orN G C \ lam G C).card ≤ 1)
    (h2 : ∀ h < C.gates.length, (gateAt C h).inputs.length = 2)
    (hc : centreless G C = ∅)
    (g k a d : ℕ) (b e : Fin 2)
    (hg : g ∈ junk G C) (hk : k ∈ junk G C)
    (ha : a ∈ tops G C) (hd : d ∈ tops G C)
    (hga : OrReaches n C (opnd C a b) g)
    (hkd : OrReaches n C (opnd C d e) k) : g = k := by
  obtain ⟨hbadg,hemptyg⟩ := dirty_support G C g hg
  obtain ⟨hbadk,hemptyk⟩ := dirty_support G C k hk
  apply unique_dirty_entry G C hcount h2 g k (opnd C a b) (opnd C d e)
    hbadg hemptyg hbadk hemptyk
  · exact top_side_nonempty G C a ha (by rw [hc]; simp) b
  · exact top_side_nonempty G C d hd (by rw [hc]; simp) e
  · exact hga
  · exact hkd

end PEqualNP.Outside.L_meta_9811.DirtyReader
