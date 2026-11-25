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
lemma inCone_reader (n : ℕ) (C : Circuit) (i : ℕ) :
    ∀ j, InCone n C i j → ∃ r, r < C.gates.length ∧ i < r ∧ n + i ∈ (gateAt C r).inputs ∧
      (r = j ∨ InCone n C r j) := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro h
    have h' := h
    rw [inCone_iff] at h'
    obtain ⟨h0, k, hk, hin, h3 | h3⟩ := h'
    · subst h3
      exact ⟨j, h0, hk, hin, Or.inl rfl⟩
    · obtain ⟨r, hr, hir, hrin, h4⟩ := ih k hk h3
      refine ⟨r, hr, hir, hrin, Or.inr ?_⟩
      rw [inCone_iff]
      refine ⟨h0, k, hk, hin, ?_⟩
      rcases h4 with h4 | h4
      · exact Or.inl h4
      · exact Or.inr h4

lemma orReach_trans {n : ℕ} (C : Circuit) (g h : ℕ) :
    ∀ w, OrReaches n C w h → OrReaches n C (n + h) g → OrReaches n C w g := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hr hg
    have hnw := hr.1
    obtain ⟨r,rfl⟩ : ∃ r, w = n + r := ⟨w - n,by omega⟩
    obtain ⟨hr,hrr | ⟨hop,i,hi,hil,hir⟩⟩ := (orReaches_iff n C r h).mp hr
    · subst hrr
      exact hg
    · exact (orReaches_iff n C r g).mpr ⟨hr,Or.inr ⟨hop,i,hi,hil,ih i hil hir hg⟩⟩

lemma orReach_true {n : ℕ} (C : Circuit) (g : ℕ) (x : Fin n → Bool) :
    ∀ w, OrReaches n C w g → gateVal n C g x = true → val C (List.ofFn x) w = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hr hg
    have hnw := hr.1
    obtain ⟨r,rfl⟩ : ∃ r, w = n + r := ⟨w - n,by omega⟩
    obtain ⟨hr,hrr | ⟨hop,i,hi,hil,hir⟩⟩ := (orReaches_iff n C r g).mp hr
    · subst hrr
      exact hg
    · exact (val_or (n := n) (by simp) hr hop).mpr ⟨i,hi,hil,ih i hil hir hg⟩

lemma operand_of_mem {C : Circuit} {a w : ℕ}
    (h2 : (gateAt C a).inputs.length = 2) (hw : w ∈ (gateAt C a).inputs) :
    ∃ b : Fin 2, opnd C a b = w := by
  obtain ⟨u,v,h⟩ := List.length_eq_two.mp h2
  rw [h] at hw
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hw
  rcases hw with rfl | rfl
  · exact ⟨0,by simp [opnd,h]⟩
  · exact ⟨1,by simp [opnd,h]⟩

lemma cone_to_top_or {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (T : ℕ) (hT : T < C.gates.length)
    (h2 : ∀ r < C.gates.length, (gateAt C r).inputs.length = 2)
    (hops : ∀ r < C.gates.length, (gateAt C r).op = GateOp.and ∨ (gateAt C r).op = GateOp.or)
    (hlast : ∀ r < C.gates.length, T < r → (gateAt C r).op = GateOp.and → BelowF G C r) :
    ∀ r, T = r ∨ InCone n C T r →
      OrReaches n C (n + r) T ∨
      ∃ a ∈ tops G C, ∃ b : Fin 2, OrReaches n C (opnd C a b) T := by
  intro r
  induction r using Nat.strong_induction_on with
  | _ r ih =>
    intro h
    rcases h with rfl | h
    · exact Or.inl ((orReaches_iff n C T T).mpr ⟨hT,Or.inl rfl⟩)
    · have hTr := (inCone_lt n C T r h).1
      obtain ⟨hr,k,hkr,hkin,hpath⟩ := (inCone_iff n C T r).mp h
      rcases ih k hkr hpath with hk | ht
      · rcases hops r hr with ha | ho
        · right
          have ht : r ∈ tops G C := by
            simp only [tops,gatesWhere,Finset.mem_filter,Finset.mem_range]
            exact ⟨hr,ha,hlast r hr hTr ha⟩
          obtain ⟨b,hb⟩ := operand_of_mem (h2 r hr) hkin
          exact ⟨r,ht,b,by rw [hb]; exact hk⟩
        · exact Or.inl ((orReaches_iff n C r T).mpr
            ⟨hr,Or.inr ⟨ho,n + k,hkin,by omega,hk⟩⟩)
      · exact Or.inr ht

lemma last_dirty_top_entry {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (T : ℕ) (hcone : PEqualNP.Core.InOutputCone n C T)
    (hbad : ¬ BelowF G C T)
    (hout : ∀ x : Fin n → Bool, C.eval (List.ofFn x) = graphFun G ∅ x)
    (h2 : ∀ r < C.gates.length, (gateAt C r).inputs.length = 2)
    (hops : ∀ r < C.gates.length, (gateAt C r).op = GateOp.and ∨ (gateAt C r).op = GateOp.or)
    (hlast : ∀ r < C.gates.length, T < r → (gateAt C r).op = GateOp.and → BelowF G C r) :
    ∃ a ∈ tops G C, ∃ b : Fin 2, OrReaches n C (opnd C a b) T := by
  obtain ⟨hT,hc | ⟨hno,hc⟩⟩ := hcone
  · exfalso
    apply hbad
    intro x hx
    have he := hout x
    change val C (List.ofFn x) C.output = _ at he
    rw [hc] at he
    exact he.symm.trans hx
  · rcases cone_to_top_or G C T hT h2 hops hlast (C.output - n) (Or.inr hc) with hor | ht
    · exfalso
      apply hbad
      intro x hx
      have he := orReach_true C T x (n + (C.output - n)) hor hx
      have hn : n + (C.output - n) = C.output := by omega
      rw [hn] at he
      change C.eval (List.ofFn x) = true at he
      rw [hout x] at he
      exact he
    · exact ht

lemma entry_reader_source {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hcount : (orN G C \ lam G C).card ≤ 1)
    (h2 : ∀ r < C.gates.length, (gateAt C r).inputs.length = 2)
    (T g w h : ℕ)
    (hbadT : ¬ BelowF G C T) (hemptyT : orIn n C (n + T) = ∅)
    (hbadg : ¬ BelowF G C g) (hemptyg : orIn n C (n + g) = ∅)
    (hw : (orIn n C w).Nonempty) (hwT : OrReaches n C w T)
    (hh : h < C.gates.length) (hop : (gateAt C h).op = GateOp.or)
    (hin : n + g ∈ (gateAt C h).inputs) (hgh : g < h) : g = T := by
  obtain ⟨p,hp,pop,hTin,hTp,hwp⟩ : ∃ p, p < C.gates.length ∧
      (gateAt C p).op = GateOp.or ∧ n + T ∈ (gateAt C p).inputs ∧ T < p ∧ OrReaches n C w p := by
    rcases chain_with_reaches T w hwT with he | h
    · rw [he,hemptyT] at hw
      simp at hw
    · exact h
  have he := unique_bad_readers G C hcount T p g h hbadT hemptyT hp pop hTin hTp (h2 p hp)
    hbadg hemptyg hh hop hin hgh (h2 h hh)
  subst h
  have hgg : OrReaches n C (n + g) g :=
    (orReaches_iff n C g g).mpr ⟨by omega,Or.inl rfl⟩
  have hpg : OrReaches n C (n + p) g :=
    (orReaches_iff n C p g).mpr ⟨hp,Or.inr ⟨pop,n + g,hin,by omega,hgg⟩⟩
  have hwg := orReach_trans C g p w hwp hpg
  exact (unique_dirty_entry G C hcount h2 T g w w hbadT hemptyT hbadg hemptyg hw hw hwT hwg).symm

lemma and_bad_mem_junk {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (r : ℕ) (hr : r < C.gates.length)
    (hop : (gateAt C r).op = GateOp.and) (hbad : ¬ BelowF G C r) : r ∈ junk G C := by
  classical
  unfold junk gatesWhere
  apply Finset.mem_filter.mpr
  unfold BelowF at hbad
  push_neg at hbad
  obtain ⟨x,hx,hf⟩ := hbad
  refine ⟨Finset.mem_range.mpr hr,hop,hr,x,hx,?_⟩
  simpa using hf

lemma sole_reader_of_entry {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (g T : ℕ) (hne : g ≠ T)
    (hcount : (orN G C \ lam G C).card ≤ 1) (hc : centreless G C = ∅)
    (h2 : ∀ r < C.gates.length, (gateAt C r).inputs.length = 2)
    (hops : ∀ r < C.gates.length, (gateAt C r).op = GateOp.and ∨ (gateAt C r).op = GateOp.or)
    (hback : ∀ r < C.gates.length, ∀ w ∈ (gateAt C r).inputs, w < n + r)
    (hJ : ∀ r, r ∈ junk G C ↔ r = g ∨ r = T)
    (hentry : ∃ a ∈ tops G C, ∃ b : Fin 2, OrReaches n C (opnd C a b) T) :
    ∀ r < C.gates.length, n + g ∈ (gateAt C r).inputs → r = T := by
  have hg := (hJ g).mpr (Or.inl rfl)
  have hT := (hJ T).mpr (Or.inr rfl)
  obtain ⟨hbadg,hemptyg⟩ := dirty_support G C g hg
  obtain ⟨hbadT,hemptyT⟩ := dirty_support G C T hT
  obtain ⟨a,ha,b,hab⟩ := hentry
  have han := top_side_nonempty G C a ha (by rw [hc]; simp) b
  intro r hr hin
  have hgr : g < r := by have := hback r hr (n + g) hin; omega
  rcases hops r hr with hand | hor
  · have hbad : ¬ BelowF G C r := by
      intro hbelow
      have htop : r ∈ tops G C := by
        simp only [tops,gatesWhere,Finset.mem_filter,Finset.mem_range]
        exact ⟨hr,hand,hbelow⟩
      obtain ⟨e,he⟩ := operand_of_mem (h2 r hr) hin
      have hn := top_side_nonempty G C r htop (by rw [hc]; simp) e
      rw [he,hemptyg] at hn
      simp at hn
    rcases (hJ r).mp (and_bad_mem_junk G C r hr hand hbad) with he | he
    · omega
    · exact he
  · have he := entry_reader_source G C hcount h2 T g (opnd C a b) r hbadT hemptyT
      hbadg hemptyg han hab hr hor hin hgr
    exact (hne he).elim

lemma two_dirty_sole_reader {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (g T : ℕ) (hgT : g < T)
    (hAO : IsAO2 n C)
    (hF : PEqualNP.MetaComplexity.circuitFun n C = graphFun G ∅)
    (hcone : ∀ r < C.gates.length, PEqualNP.Core.InOutputCone n C r)
    (hJ : junk G C = {g,T})
    (hc : centreless G C = ∅) (hcount : (orN G C \ lam G C).card ≤ 1) :
    ∀ r < C.gates.length, n + g ∈ (gateAt C r).inputs → r = T := by
  have hj : ∀ r, r ∈ junk G C ↔ r = g ∨ r = T := by
    intro r
    rw [hJ]
    simp
  have h2 : ∀ r < C.gates.length, (gateAt C r).inputs.length = 2 :=
    fun r hr => hAO.2.2 _ (gateAt_mem hr)
  have hops : ∀ r < C.gates.length, (gateAt C r).op = GateOp.and ∨ (gateAt C r).op = GateOp.or :=
    fun r hr => hAO.1 _ (gateAt_mem hr)
  have hTmem := (hj T).mpr (Or.inr rfl)
  have hTlt : T < C.gates.length := by
    simpa only [junk,gatesWhere,Finset.mem_filter,Finset.mem_range] using
      (show T < C.gates.length from (Finset.mem_range.mp (Finset.mem_filter.mp hTmem).1))
  obtain ⟨hbadT,_⟩ := dirty_support G C T hTmem
  have hlast : ∀ r < C.gates.length, T < r → (gateAt C r).op = GateOp.and → BelowF G C r := by
    intro r hr hTr hop
    by_contra hbad
    have hm := and_bad_mem_junk G C r hr hop hbad
    rcases (hj r).mp hm with he | he <;> omega
  have hentry := last_dirty_top_entry G C T (hcone T hTlt) hbadT (fun x => congrFun hF x) h2 hops hlast
  exact sole_reader_of_entry G C g T (by omega) hcount hc h2 hops hAO.2.1 hj hentry


lemma two_dirty_chain {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (g T : ℕ) (hgT : g < T)
    (hAO : IsAO2 n C)
    (hF : PEqualNP.MetaComplexity.circuitFun n C = graphFun G ∅)
    (hcone : ∀ r < C.gates.length, PEqualNP.Core.InOutputCone n C r)
    (hJ : junk G C = {g,T})
    (hc : centreless G C = ∅) (hcount : (orN G C \ lam G C).card ≤ 1) :
    (∃ e : Fin 2, opnd C T e = n + g) ∧
    ∀ r < C.gates.length, n + g ∈ (gateAt C r).inputs → r = T := by
  have hsole := two_dirty_sole_reader G C g T hgT hAO hF hcone hJ hc hcount
  refine ⟨?_,hsole⟩
  have hg : g ∈ junk G C := by rw [hJ]; simp
  have hT : T ∈ junk G C := by rw [hJ]; simp
  have hglt : g < C.gates.length := Finset.mem_range.mp (Finset.mem_filter.mp hg).1
  have hTlt : T < C.gates.length := Finset.mem_range.mp (Finset.mem_filter.mp hT).1
  have hbadg := (dirty_support G C g hg).1
  obtain ⟨_,ho | ⟨hno,hco⟩⟩ := hcone g hglt
  · exfalso
    apply hbadg
    intro x hx
    have he := congrFun hF x
    change val C (List.ofFn x) C.output = _ at he
    rw [ho] at he
    exact he.symm.trans hx
  · obtain ⟨r,hr,_,hrin,_⟩ := inCone_reader n C g (C.output - n) hco
    have he := hsole r hr hrin
    rw [he] at hrin
    exact operand_of_mem (hAO.2.2 _ (gateAt_mem hTlt)) hrin

lemma orIn_input_mem {n : ℕ} (C : Circuit) (w : ℕ) (hw : w < n) (v : Fin n) :
    v ∈ orIn n C w ↔ (v : ℕ) = w := by
  simp only [orIn,Finset.mem_filter,Finset.mem_univ,true_and]
  constructor
  · rintro (h | ⟨k,_,hr,_,_⟩)
    · exact h
    · have := hr.1
      omega
  · exact Or.inl

lemma orIn_gate_iff {n : ℕ} (C : Circuit) (r : ℕ) (v : Fin n) :
    v ∈ orIn n C (n + r) ↔ r < C.gates.length ∧ (gateAt C r).op = GateOp.or ∧
      ∃ w ∈ (gateAt C r).inputs, w < n + r ∧ v ∈ orIn n C w := by
  constructor
  · intro hv
    simp only [orIn,Finset.mem_filter,Finset.mem_univ,true_and] at hv
    rcases hv with he | ⟨k,hk,hr,hop,hvin⟩
    · have := v.isLt
      omega
    · obtain ⟨hr,he | ⟨hro,w,hw,hwl,hwr⟩⟩ := (orReaches_iff n C r k).mp hr
      · subst he
        refine ⟨hr,hop,v,hvin,by have := v.isLt; omega,?_⟩
        simp [orIn]
      · refine ⟨hr,hro,w,hw,hwl,?_⟩
        simp only [orIn,Finset.mem_filter,Finset.mem_univ,true_and]
        exact Or.inr ⟨k,hk,hwr,hop,hvin⟩
  · rintro ⟨hr,hop,w,hw,hwl,hv⟩
    simp only [orIn,Finset.mem_filter,Finset.mem_univ,true_and] at hv ⊢
    right
    rcases hv with he | ⟨k,hk,hwr,hko,hvin⟩
    · refine ⟨r,hr,(orReaches_iff n C r r).mpr ⟨hr,Or.inl rfl⟩,hop,?_⟩
      rw [he]
      exact hw
    · exact ⟨k,hk,(orReaches_iff n C r k).mpr ⟨hr,Or.inr ⟨hop,w,hw,hwl,hwr⟩⟩,hko,hvin⟩

lemma pure_or_eval {n : ℕ} (C : Circuit) (hAO : IsAO2 n C) :
    ∀ w, w < n + C.gates.length →
      (∀ r < C.gates.length, (gateAt C r).op = GateOp.and → ¬ OrReaches n C w r) →
      (orIn n C w).Nonempty ∧
      ∀ x : Fin n → Bool, val C (List.ofFn x) w = decide (∃ v ∈ orIn n C w, x v = true) := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hw hno
    by_cases hwn : w < n
    · let v : Fin n := ⟨w,hwn⟩
      have hv : v ∈ orIn n C w := (orIn_input_mem C w hwn v).mpr rfl
      refine ⟨⟨v,hv⟩,?_⟩
      intro x
      apply Bool.eq_iff_iff.mpr
      simp only [decide_eq_true_eq]
      have he : val C (List.ofFn x) w = x v := val_ofFn C x v
      rw [he]
      constructor
      · intro hx
        exact ⟨v,hv,hx⟩
      · rintro ⟨u,hu,hux⟩
        have huv : u = v := Fin.ext ((orIn_input_mem C w hwn u).mp hu)
        simpa [huv] using hux
    · obtain ⟨r,rfl⟩ : ∃ r, w = n + r := ⟨w - n,by omega⟩
      have hr : r < C.gates.length := by omega
      have hm := gateAt_mem (C := C) hr
      have hop : (gateAt C r).op = GateOp.or := by
        rcases hAO.1 _ hm with ha | ho
        · exact False.elim (hno r hr ha ((orReaches_iff n C r r).mpr ⟨hr,Or.inl rfl⟩))
        · exact ho
      have hchildren : ∀ u ∈ (gateAt C r).inputs,
          (orIn n C u).Nonempty ∧
          ∀ x : Fin n → Bool, val C (List.ofFn x) u = decide (∃ v ∈ orIn n C u, x v = true) := by
        intro u hu
        have hul := hAO.2.1 r hr u hu
        apply ih u hul (by omega)
        intro k hk hka hur
        apply hno k hk hka
        exact (orReaches_iff n C r k).mpr ⟨hr,Or.inr ⟨hop,u,hu,hul,hur⟩⟩
      constructor
      · obtain ⟨a,b,he⟩ := List.length_eq_two.mp (hAO.2.2 _ hm)
        have ha : a ∈ (gateAt C r).inputs := by rw [he]; simp
        obtain ⟨v,hv⟩ := (hchildren a ha).1
        exact ⟨v,(orIn_gate_iff C r v).mpr ⟨hr,hop,a,ha,hAO.2.1 r hr a ha,hv⟩⟩
      · intro x
        apply Bool.eq_iff_iff.mpr
        simp only [decide_eq_true_eq]
        constructor
        · intro hx
          obtain ⟨u,hu,_,huv⟩ := (val_or (n := n) (by simp) hr hop).mp hx
          rw [(hchildren u hu).2 x] at huv
          obtain ⟨v,hvin,hvx⟩ := of_decide_eq_true huv
          exact ⟨v,(orIn_gate_iff C r v).mpr ⟨hr,hop,u,hu,hAO.2.1 r hr u hu,hvin⟩,hvx⟩
        · rintro ⟨v,hv,hvx⟩
          obtain ⟨_,_,u,hu,hul,hvu⟩ := (orIn_gate_iff C r v).mp hv
          apply (val_or (n := n) (by simp) hr hop).mpr
          refine ⟨u,hu,hul,?_⟩
          rw [(hchildren u hu).2 x]
          exact decide_eq_true ⟨v,hvu,hvx⟩

lemma orReach_cone {n : ℕ} (C : Circuit) (h : ℕ) :
    ∀ r, OrReaches n C (n + r) h → h = r ∨ InCone n C h r := by
  intro r
  induction r using Nat.strong_induction_on with
  | _ r ih =>
    intro hor
    obtain ⟨hr,he | ⟨_,w,hw,hwl,hwr⟩⟩ := (orReaches_iff n C r h).mp hor
    · exact Or.inl he
    · have hnw := hwr.1
      obtain ⟨k,rfl⟩ : ∃ k, w = n + k := ⟨w - n,by omega⟩
      have hkr : k < r := by omega
      exact Or.inr ((inCone_iff n C h r).mpr ⟨hr,k,hkr,hw,ih k hkr hwr⟩)

lemma operand_mem {C : Circuit} {a : ℕ}
    (h2 : (gateAt C a).inputs.length = 2) (b : Fin 2) :
    opnd C a b ∈ (gateAt C a).inputs := by
  obtain ⟨u,v,h⟩ := List.length_eq_two.mp h2
  fin_cases b <;> simp [opnd,h]

lemma operand_reach_cone {n : ℕ} (C : Circuit) (hAO : IsAO2 n C)
    (a h : ℕ) (ha : a < C.gates.length) (b : Fin 2)
    (hr : OrReaches n C (opnd C a b) h) : InCone n C h a := by
  have hm := operand_mem (hAO.2.2 _ (gateAt_mem ha)) b
  have hlt := hAO.2.1 a ha (opnd C a b) hm
  have hnw := hr.1
  obtain ⟨k,hk⟩ : ∃ k, opnd C a b = n + k := ⟨opnd C a b - n,by omega⟩
  rw [hk] at hr hm hlt
  exact (inCone_iff n C h a).mpr ⟨ha,k,by omega,hm,orReach_cone C h k hr⟩

lemma first_dirty_pure_inputs {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (g T : ℕ) (hgT : g < T)
    (hAO : IsAO2 n C) (hTop : TopForm G C) (hJ : junk G C = {g,T}) :
    ∀ b : Fin 2, (orIn n C (opnd C g b)).Nonempty ∧
      ∀ x : Fin n → Bool, val C (List.ofFn x) (opnd C g b) =
        decide (∃ v ∈ orIn n C (opnd C g b), x v = true) := by
  have hg : g ∈ junk G C := by rw [hJ]; simp
  have hgl : g < C.gates.length := Finset.mem_range.mp (Finset.mem_filter.mp hg).1
  have hgo : (gateAt C g).op = GateOp.and := (Finset.mem_filter.mp hg).2.1
  intro b
  have hm := operand_mem (hAO.2.2 _ (gateAt_mem hgl)) b
  have hwl := hAO.2.1 g hgl (opnd C g b) hm
  apply pure_or_eval C hAO (opnd C g b) (by omega)
  intro r hr hop hor
  have hco := operand_reach_cone C hAO g r hgl b hor
  have hrg := (inCone_lt n C r g hco).1
  have hb : BelowF G C r := by
    by_contra hbad
    have hj := and_bad_mem_junk G C r hr hop hbad
    rw [hJ] at hj
    simp only [Finset.mem_insert,Finset.mem_singleton] at hj
    rcases hj with he | he <;> omega
  exact hTop r hr g hgl hop hb hgo hco

lemma second_dirty_pure_opposite {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (g T : ℕ) (hgT : g < T)
    (hAO : IsAO2 n C) (hTop : TopForm G C) (hJ : junk G C = {g,T})
    (hsole : ∀ r < C.gates.length, n + g ∈ (gateAt C r).inputs → r = T)
    (e : Fin 2) (hother : opnd C T e ≠ n + g) :
    (orIn n C (opnd C T e)).Nonempty ∧
      ∀ x : Fin n → Bool, val C (List.ofFn x) (opnd C T e) =
        decide (∃ v ∈ orIn n C (opnd C T e), x v = true) := by
  have hT : T ∈ junk G C := by rw [hJ]; simp
  have hTl : T < C.gates.length := Finset.mem_range.mp (Finset.mem_filter.mp hT).1
  have hTo : (gateAt C T).op = GateOp.and := (Finset.mem_filter.mp hT).2.1
  have hm := operand_mem (hAO.2.2 _ (gateAt_mem hTl)) e
  have hwl := hAO.2.1 T hTl (opnd C T e) hm
  apply pure_or_eval C hAO (opnd C T e) (by omega)
  intro r hr hop hor
  have hco := operand_reach_cone C hAO T r hTl e hor
  have hrT := (inCone_lt n C r T hco).1
  by_cases hb : BelowF G C r
  · exact hTop r hr T hTl hop hb hTo hco
  · have hj := and_bad_mem_junk G C r hr hop hb
    rw [hJ] at hj
    simp only [Finset.mem_insert,Finset.mem_singleton] at hj
    rcases hj with he | he
    · subst r
      rcases chain g (opnd C T e) hor with he | ⟨q,hq,hqo,hqi,_⟩
      · exact hother he
      · have heq := hsole q hq hqi
        rw [heq,hTo] at hqo
        cases hqo
    · omega

lemma orIn_subset_of_reach {n : ℕ} (C : Circuit) (w h : ℕ)
    (hr : OrReaches n C w h) : orIn n C (n + h) ⊆ orIn n C w := by
  intro v hv
  simp only [orIn,Finset.mem_filter,Finset.mem_univ,true_and] at hv ⊢
  rcases hv with he | ⟨k,hk,hhr,hop,hvin⟩
  · have := v.isLt
    omega
  · exact Or.inr ⟨k,hk,orReach_trans C k h w hr hhr,hop,hvin⟩

lemma orIn_true {n : ℕ} (C : Circuit) (w : ℕ) (v : Fin n) (x : Fin n → Bool)
    (hv : v ∈ orIn n C w) (hx : x v = true) : val C (List.ofFn x) w = true := by
  simp only [orIn,Finset.mem_filter,Finset.mem_univ,true_and] at hv
  rcases hv with he | ⟨k,hk,hr,hop,hvin⟩
  · rw [← he,val_ofFn]
    exact hx
  · apply orReach_true C k x w hr
    rw [gateVal_eq_val]
    apply (val_or (n := n) (by simp) hk hop).mpr
    exact ⟨v,hvin,by have := v.isLt; omega,by rw [val_ofFn]; exact hx⟩

lemma graph_pair_adj {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (u v : Fin n) (h : graphFun G ∅ (pairInput u v) = true) : G.Adj u v := by
  simp [graphFun,pairInput] at h
  obtain ⟨a,b,hab,ha,hb⟩ := h
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
  · exact False.elim (G.irrefl hab)
  · exact hab
  · exact hab.symm
  · exact False.elim (G.irrefl hab)

lemma clean_cross_adj {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hAO : IsAO2 n C) (a : ℕ) (ha : a ∈ tops G C)
    (u v : Fin n) (hu : u ∈ side (n := n) C a 0) (hv : v ∈ side (n := n) C a 1) : G.Adj u v := by
  letI : DecidableEq GateOp := gateOpDecEq
  have hh := (Finset.mem_filter.mp ha)
  have hal : a < C.gates.length := Finset.mem_range.mp hh.1
  obtain ⟨hop,hbelow⟩ := hh.2
  apply graph_pair_adj G u v
  apply hbelow
  rw [gateVal_eq_val]
  apply (val_and (n := n) (by simp) hal hop).mpr
  have hin : (gateAt C a).inputs = [opnd C a 0,opnd C a 1] := by
    obtain ⟨p,q,he⟩ := List.length_eq_two.mp (hAO.2.2 _ (gateAt_mem hal))
    simp [opnd,he]
  intro w hw
  have hwl := hAO.2.1 a hal w hw
  refine ⟨hwl,?_⟩
  rw [hin] at hw
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hw
  rcases hw with rfl | rfl
  · exact orIn_true C _ u _ hu (by simp [pairInput])
  · exact orIn_true C _ v _ hv (by simp [pairInput])

lemma lambda_monochromatic {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hAO : IsAO2 n C) (color : Fin n → Bool)
    (hbip : ∀ u v, G.Adj u v → color u ≠ color v)
    (h : ℕ) (hlam : h ∈ lam G C) :
    ∃ b : Bool, ∀ v ∈ orIn n C (n + h), color v = b := by
  obtain ⟨_,_,_,a,ha,e,he,hreach⟩ := Finset.mem_filter.mp hlam
  have hne : (side (n := n) C a (1 - e)).Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨z,hz⟩ := hne
  refine ⟨!color z,?_⟩
  intro v hv
  have hvside := orIn_subset_of_reach C (opnd C a e) h hreach hv
  have hadj : G.Adj z v := by
    fin_cases e
    · have hz' : z ∈ side (n := n) C a 1 := by simpa using hz
      exact (clean_cross_adj G C hAO a ha v z hvside hz').symm
    · have hz' : z ∈ side (n := n) C a 0 := by simpa using hz
      exact clean_cross_adj G C hAO a ha z v hz' hvside
  have hne := hbip z v hadj
  cases hzv : color z <;> cases hvv : color v <;> simp_all

lemma pure_not_below {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (h : ℕ) (hne : (orIn n C (n + h)).Nonempty)
    (hsem : ∀ x : Fin n → Bool, val C (List.ofFn x) (n + h) =
      decide (∃ v ∈ orIn n C (n + h), x v = true)) : ¬ BelowF G C h := by
  intro hbelow
  obtain ⟨v,hv⟩ := hne
  have he : gateVal n C h (pairInput v v) = true := by
    rw [gateVal_eq_val,hsem]
    apply decide_eq_true
    exact ⟨v,hv,by simp [pairInput]⟩
  exact G.irrefl (graph_pair_adj G v v (hbelow _ he))

lemma pure_other_or_lambda {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (h p : ℕ) (hh : h < C.gates.length) (hop : (gateAt C h).op = GateOp.or)
    (hp : p ∈ orN G C \ lam G C) (hne : h ≠ p)
    (hcount : (orN G C \ lam G C).card ≤ 1)
    (hN : (orIn n C (n + h)).Nonempty)
    (hsem : ∀ x : Fin n → Bool, val C (List.ofFn x) (n + h) =
      decide (∃ v ∈ orIn n C (n + h), x v = true)) : h ∈ lam G C := by
  letI : DecidableEq GateOp := gateOpDecEq
  by_contra hn
  have hbad := pure_not_below G C h hN hsem
  have hor : h ∈ orN G C := by
    unfold orN gatesWhere
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hh,hop,hbad⟩
  have hmem := Finset.mem_sdiff.mpr ⟨hor,hn⟩
  exact hne (Finset.card_le_one.mp hcount h hmem p hp)

lemma pure_wire_before_T_monochromatic {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hAO : IsAO2 n C) (color : Fin n → Bool)
    (hbip : ∀ u v, G.Adj u v → color u ≠ color v)
    (g T p w : ℕ) (hJ : junk G C = {g,T})
    (hp : p ∈ orN G C \ lam G C) (hTp : T < p)
    (hcount : (orN G C \ lam G C).card ≤ 1)
    (hw : w < n + T) (hwg : w ≠ n + g)
    (hN : (orIn n C w).Nonempty)
    (hsem : ∀ x : Fin n → Bool, val C (List.ofFn x) w =
      decide (∃ v ∈ orIn n C w, x v = true)) :
    ∃ b : Bool, ∀ v ∈ orIn n C w, color v = b := by
  have hT : T ∈ junk G C := by rw [hJ]; simp
  have hTl : T < C.gates.length := Finset.mem_range.mp (Finset.mem_filter.mp hT).1
  by_cases hwn : w < n
  · let u : Fin n := ⟨w,hwn⟩
    refine ⟨color u,?_⟩
    intro v hv
    have he : v = u := Fin.ext ((orIn_input_mem C w hwn v).mp hv)
    rw [he]
  · obtain ⟨h,rfl⟩ : ∃ h, w = n + h := ⟨w - n,by omega⟩
    have hh : h < C.gates.length := by omega
    have hop : (gateAt C h).op = GateOp.or := by
      rcases hAO.1 _ (gateAt_mem hh) with ha | ho
      · have hj := and_bad_mem_junk G C h hh ha (pure_not_below G C h hN hsem)
        rw [hJ] at hj
        simp only [Finset.mem_insert,Finset.mem_singleton] at hj
        rcases hj with he | he <;> omega
      · exact ho
    have hlam := pure_other_or_lambda G C h p hh hop hp (by omega) hcount hN hsem
    exact lambda_monochromatic G C hAO color hbip h hlam

lemma and_gate_eval {n : ℕ} (C : Circuit) (hAO : IsAO2 n C) (a : ℕ)
    (ha : a < C.gates.length) (hop : (gateAt C a).op = GateOp.and) (x : Fin n → Bool) :
    gateVal n C a x = (val C (List.ofFn x) (opnd C a 0) && val C (List.ofFn x) (opnd C a 1)) := by
  have h2 := hAO.2.2 _ (gateAt_mem ha)
  have h0 := hAO.2.1 a ha _ (operand_mem h2 0)
  have h1 := hAO.2.1 a ha _ (operand_mem h2 1)
  have hin : (gateAt C a).inputs = [opnd C a 0,opnd C a 1] := by
    obtain ⟨u,v,he⟩ := List.length_eq_two.mp h2
    simp [opnd,he]
  rw [gateVal_eq_val,val_gate (n := n) (by simp) ha,hop,hin]
  simp [GateOp.eval,h0,h1]

lemma and_gate_oriented {n : ℕ} (C : Circuit) (hAO : IsAO2 n C) (a : ℕ)
    (ha : a < C.gates.length) (hop : (gateAt C a).op = GateOp.and) (e : Fin 2) (x : Fin n → Bool) :
    gateVal n C a x = (val C (List.ofFn x) (opnd C a e) && val C (List.ofFn x) (opnd C a (1-e))) := by
  fin_cases e
  · simpa using and_gate_eval C hAO a ha hop x
  · simpa [Bool.and_comm] using and_gate_eval C hAO a ha hop x

lemma extra_after_T {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (g T : ℕ) (hgT : g < T) (hAO : IsAO2 n C)
    (hF : PEqualNP.MetaComplexity.circuitFun n C = graphFun G ∅)
    (hcone : ∀ r < C.gates.length, PEqualNP.Core.InOutputCone n C r)
    (hJ : junk G C = {g,T}) (hc : centreless G C = ∅) :
    ∃ p ∈ orN G C \ lam G C, T < p := by
  have hT : T ∈ junk G C := by rw [hJ]; simp
  have hTl : T < C.gates.length := Finset.mem_range.mp (Finset.mem_filter.mp hT).1
  obtain ⟨hbadT,hemptyT⟩ := dirty_support G C T hT
  have h2 : ∀ r < C.gates.length, (gateAt C r).inputs.length = 2 :=
    fun r hr => hAO.2.2 _ (gateAt_mem hr)
  have hops : ∀ r < C.gates.length, (gateAt C r).op = GateOp.and ∨ (gateAt C r).op = GateOp.or :=
    fun r hr => hAO.1 _ (gateAt_mem hr)
  have hlast : ∀ r < C.gates.length, T < r → (gateAt C r).op = GateOp.and → BelowF G C r := by
    intro r hr hTr hop
    by_contra hbad
    have hm := and_bad_mem_junk G C r hr hop hbad
    rw [hJ] at hm
    simp only [Finset.mem_insert,Finset.mem_singleton] at hm
    rcases hm with he | he <;> omega
  obtain ⟨a,ha,b,hab⟩ := last_dirty_top_entry G C T (hcone T hTl) hbadT
    (fun x => congrFun hF x) h2 hops hlast
  have han := top_side_nonempty G C a ha (by rw [hc]; simp) b
  rcases chain T (opnd C a b) hab with he | ⟨p,hp,pop,hpin,hTp⟩
  · rw [he,hemptyT] at han
    simp at han
  · exact ⟨p,bad_or_reader_extra G C T p hbadT hemptyT hp pop hpin hTp (h2 p hp),hTp⟩

lemma dirty_chain_clauses {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (g T : ℕ) (hgT : g < T) (hAO : IsAO2 n C)
    (hTop : TopForm G C)
    (hF : PEqualNP.MetaComplexity.circuitFun n C = graphFun G ∅)
    (hcone : ∀ r < C.gates.length, PEqualNP.Core.InOutputCone n C r)
    (hJ : junk G C = {g,T}) (hc : centreless G C = ∅)
    (hcount : (orN G C \ lam G C).card ≤ 1)
    (color : Fin n → Bool) (hbip : ∀ u v, G.Adj u v → color u ≠ color v) :
    ∃ clauses : List (Finset (Fin n)), clauses.length ≤ 3 ∧
      (∀ S ∈ clauses, S.Nonempty ∧ ∃ b : Bool, ∀ v ∈ S, color v = b) ∧
      ∀ x : Fin n → Bool, gateVal n C T x = true ↔ ∀ S ∈ clauses, ∃ v ∈ S, x v = true := by
  obtain ⟨⟨e,he⟩,hsole⟩ := two_dirty_chain G C g T hgT hAO hF hcone hJ hc hcount
  obtain ⟨p,hp,hTp⟩ := extra_after_T G C g T hgT hAO hF hcone hJ hc
  have hg : g ∈ junk G C := by rw [hJ]; simp
  have hT : T ∈ junk G C := by rw [hJ]; simp
  have hgl : g < C.gates.length := Finset.mem_range.mp (Finset.mem_filter.mp hg).1
  have hTl : T < C.gates.length := Finset.mem_range.mp (Finset.mem_filter.mp hT).1
  have hgo : (gateAt C g).op = GateOp.and := (Finset.mem_filter.mp hg).2.1
  have hTo : (gateAt C T).op = GateOp.and := (Finset.mem_filter.mp hT).2.1
  let A := orIn n C (opnd C g 0)
  let B := orIn n C (opnd C g 1)
  have hA := first_dirty_pure_inputs G C g T hgT hAO hTop hJ 0
  have hB := first_dirty_pure_inputs G C g T hgT hAO hTop hJ 1
  have hw0 := hAO.2.1 g hgl _ (operand_mem (hAO.2.2 _ (gateAt_mem hgl)) 0)
  have hw1 := hAO.2.1 g hgl _ (operand_mem (hAO.2.2 _ (gateAt_mem hgl)) 1)
  have hcolA := pure_wire_before_T_monochromatic G C hAO color hbip g T p (opnd C g 0)
    hJ hp hTp hcount (by omega) (by omega) hA.1 hA.2
  have hcolB := pure_wire_before_T_monochromatic G C hAO color hbip g T p (opnd C g 1)
    hJ hp hTp hcount (by omega) (by omega) hB.1 hB.2
  have hgval : ∀ x : Fin n → Bool, gateVal n C g x =
      (decide (∃ v ∈ A, x v = true) && decide (∃ v ∈ B, x v = true)) := by
    intro x
    rw [and_gate_eval C hAO g hgl hgo x,hA.2 x,hB.2 x]
  have hTval : ∀ x : Fin n → Bool, gateVal n C T x =
      (gateVal n C g x && val C (List.ofFn x) (opnd C T (1-e))) := by
    intro x
    rw [and_gate_oriented C hAO T hTl hTo e x,he]
    rfl
  by_cases hcopy : opnd C T (1-e) = n + g
  · refine ⟨[A,B],by simp,?_,?_⟩
    · intro S hS
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hS
      rcases hS with rfl | rfl
      · exact ⟨hA.1,hcolA⟩
      · exact ⟨hB.1,hcolB⟩
    · intro x
      rw [hTval x,hcopy]
      change ((gateVal n C g x && gateVal n C g x) = true) ↔ _
      rw [Bool.and_self,hgval x]
      simp [Bool.and_eq_true]
  · let D := orIn n C (opnd C T (1-e))
    have hD := second_dirty_pure_opposite G C g T hgT hAO hTop hJ hsole (1-e) hcopy
    have hwd := hAO.2.1 T hTl _ (operand_mem (hAO.2.2 _ (gateAt_mem hTl)) (1-e))
    have hcolD := pure_wire_before_T_monochromatic G C hAO color hbip g T p (opnd C T (1-e))
      hJ hp hTp hcount hwd hcopy hD.1 hD.2
    refine ⟨[A,B,D],by simp,?_,?_⟩
    · intro S hS
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hS
      rcases hS with rfl | rfl | rfl
      · exact ⟨hA.1,hcolA⟩
      · exact ⟨hB.1,hcolB⟩
      · exact ⟨hD.1,hcolD⟩
    · intro x
      rw [hTval x,hgval x,hD.2 x]
      simp [Bool.and_eq_true,and_assoc,D]

lemma one_and_wire_eval {n : ℕ} (C : Circuit) (hAO : IsAO2 n C) (T : ℕ)
    (hTo : (gateAt C T).op = GateOp.and) :
    ∀ w, w < n + C.gates.length →
      (∀ r < C.gates.length, (gateAt C r).op = GateOp.and → OrReaches n C w r → r = T) →
      ∀ x : Fin n → Bool,
        val C (List.ofFn x) w = true ↔
          (∃ v ∈ orIn n C w, x v = true) ∨ (OrReaches n C w T ∧ gateVal n C T x = true) := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hw honly x
    by_cases hwn : w < n
    · let v : Fin n := ⟨w,hwn⟩
      have hv : v ∈ orIn n C w := (orIn_input_mem C w hwn v).mpr rfl
      have he : val C (List.ofFn x) w = x v := val_ofFn C x v
      rw [he]
      constructor
      · intro hx
        exact Or.inl ⟨v,hv,hx⟩
      · rintro (⟨u,hu,hux⟩ | ⟨hr,_⟩)
        · have huv : u = v := Fin.ext ((orIn_input_mem C w hwn u).mp hu)
          simpa [huv] using hux
        · have := hr.1
          omega
    · obtain ⟨r,rfl⟩ : ∃ r, w = n + r := ⟨w - n,by omega⟩
      have hr : r < C.gates.length := by omega
      rcases hAO.1 _ (gateAt_mem hr) with ha | ho
      · have hself := (orReaches_iff n C r r).mpr ⟨hr,Or.inl rfl⟩
        have he := honly r hr ha hself
        subst r
        have hempty := orIn_and (n := n) (C := C) hTo
        change gateVal n C T x = true ↔ _
        simp [hempty,hself]
      · have hchildren : ∀ u ∈ (gateAt C r).inputs,
            val C (List.ofFn x) u = true ↔
              (∃ v ∈ orIn n C u, x v = true) ∨ (OrReaches n C u T ∧ gateVal n C T x = true) := by
          intro u hu
          have hul := hAO.2.1 r hr u hu
          apply ih u hul (by omega)
          intro k hk hka huk
          apply honly k hk hka
          exact (orReaches_iff n C r k).mpr ⟨hr,Or.inr ⟨ho,u,hu,hul,huk⟩⟩
        constructor
        · intro hx
          obtain ⟨u,hu,_,hux⟩ := (val_or (n := n) (by simp) hr ho).mp hx
          rcases (hchildren u hu).mp hux with ⟨v,hvu,hvx⟩ | ⟨huT,hTx⟩
          · exact Or.inl ⟨v,(orIn_gate_iff C r v).mpr ⟨hr,ho,u,hu,hAO.2.1 r hr u hu,hvu⟩,hvx⟩
          · exact Or.inr ⟨(orReaches_iff n C r T).mpr ⟨hr,Or.inr ⟨ho,u,hu,hAO.2.1 r hr u hu,huT⟩⟩,hTx⟩
        · rintro (⟨v,hv,hvx⟩ | ⟨hTr,hTx⟩)
          · obtain ⟨_,_,u,hu,hul,hvu⟩ := (orIn_gate_iff C r v).mp hv
            exact (val_or (n := n) (by simp) hr ho).mpr ⟨u,hu,hul,(hchildren u hu).mpr (Or.inl ⟨v,hvu,hvx⟩)⟩
          · obtain ⟨_,he | ⟨_,u,hu,hul,huT⟩⟩ := (orReaches_iff n C r T).mp hTr
            · subst r
              rw [hTo] at ho
              cases ho
            · exact (val_or (n := n) (by simp) hr ho).mpr ⟨u,hu,hul,(hchildren u hu).mpr (Or.inr ⟨huT,hTx⟩)⟩

lemma top_side_decomposition {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (g T : ℕ) (hAO : IsAO2 n C) (hTop : TopForm G C)
    (hJ : junk G C = {g,T}) (hc : centreless G C = ∅)
    (hsole : ∀ r < C.gates.length, n + g ∈ (gateAt C r).inputs → r = T)
    (a : ℕ) (ha : a ∈ tops G C) (b : Fin 2) (x : Fin n → Bool) :
    val C (List.ofFn x) (opnd C a b) = true ↔
      (∃ v ∈ side (n := n) C a b, x v = true) ∨
      (OrReaches n C (opnd C a b) T ∧ gateVal n C T x = true) := by
  letI : DecidableEq GateOp := gateOpDecEq
  have hT : T ∈ junk G C := by rw [hJ]; simp
  have hTo : (gateAt C T).op = GateOp.and := (Finset.mem_filter.mp hT).2.1
  have hg : g ∈ junk G C := by rw [hJ]; simp
  have hemptyg := (dirty_support G C g hg).2
  have hal : a < C.gates.length := Finset.mem_range.mp (Finset.mem_filter.mp ha).1
  have hao : (gateAt C a).op = GateOp.and := (Finset.mem_filter.mp ha).2.1
  have hside := top_side_nonempty G C a ha (by rw [hc]; simp) b
  have hm := operand_mem (hAO.2.2 _ (gateAt_mem hal)) b
  have hwl := hAO.2.1 a hal (opnd C a b) hm
  apply one_and_wire_eval C hAO T hTo (opnd C a b) (by omega)
  intro r hr hop hor
  have hco := operand_reach_cone C hAO a r hal b hor
  by_cases hb : BelowF G C r
  · exact False.elim (hTop r hr a hal hop hb hao hco)
  · have hj := and_bad_mem_junk G C r hr hop hb
    rw [hJ] at hj
    simp only [Finset.mem_insert,Finset.mem_singleton] at hj
    rcases hj with he | he
    · subst r
      rcases chain g (opnd C a b) hor with he | ⟨q,hq,hqo,hqi,_⟩
      · rw [he,hemptyg] at hside
        simp at hside
      · have heq := hsole q hq hqi
        rw [heq,hTo] at hqo
        cases hqo
    · exact he

lemma top_not_both_reach_dirty {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hAO : IsAO2 n C) (T a : ℕ) (hT : T ∈ junk G C) (ha : a ∈ tops G C) :
    ¬ (OrReaches n C (opnd C a 0) T ∧ OrReaches n C (opnd C a 1) T) := by
  letI : DecidableEq GateOp := gateOpDecEq
  rintro ⟨h0,h1⟩
  apply (dirty_support G C T hT).1
  intro x hx
  have ha0 := orReach_true C T x (opnd C a 0) h0 hx
  have ha1 := orReach_true C T x (opnd C a 1) h1 hx
  have hal : a < C.gates.length := Finset.mem_range.mp (Finset.mem_filter.mp ha).1
  have hao : (gateAt C a).op = GateOp.and := (Finset.mem_filter.mp ha).2.1
  have hab : BelowF G C a := (Finset.mem_filter.mp ha).2.2
  apply hab x
  rw [and_gate_eval C hAO a hal hao x,ha0,ha1]
  rfl

lemma common_entry_primary {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (T w : ℕ)
    (hcount : (orN G C \ lam G C).card ≤ 1)
    (h2 : ∀ r < C.gates.length, (gateAt C r).inputs.length = 2)
    (hbadT : ¬ BelowF G C T) (hemptyT : orIn n C (n + T) = ∅)
    (hw : (orIn n C w).Nonempty) (hwT : OrReaches n C w T) :
    ∃ p ∈ orN G C \ lam G C, T < p ∧ (orIn n C (n + p)).Nonempty ∧
      ∀ u, (orIn n C u).Nonempty → OrReaches n C u T → orIn n C (n + p) ⊆ orIn n C u := by
  obtain ⟨p,hp,pop,hTin,hTp,hwp⟩ : ∃ p, p < C.gates.length ∧
      (gateAt C p).op = GateOp.or ∧ n + T ∈ (gateAt C p).inputs ∧ T < p ∧ OrReaches n C w p := by
    rcases chain_with_reaches T w hwT with he | h
    · rw [he,hemptyT] at hw
      simp at hw
    · exact h
  have hpExtra := bad_or_reader_extra G C T p hbadT hemptyT hp pop hTin hTp (h2 p hp)
  have hpN : (orIn n C (n + p)).Nonempty := by
    by_contra hn
    have hpEmpty : orIn n C (n + p) = ∅ := Finset.not_nonempty_iff_eq_empty.mp hn
    rcases chain_with_reaches p w hwp with he | ⟨q,hq,qop,hpin,hpq,_⟩
    · rw [he,hpEmpty] at hw
      simp at hw
    · exact no_empty_or_chain G C hcount T p q hbadT hemptyT hp pop hTin hTp (h2 p hp)
        hpEmpty hq qop hpin hpq (h2 q hq)
  refine ⟨p,hpExtra,hTp,hpN,?_⟩
  intro u hu huT
  obtain ⟨q,hq,qop,hTin',hTq,huq⟩ : ∃ q, q < C.gates.length ∧
      (gateAt C q).op = GateOp.or ∧ n + T ∈ (gateAt C q).inputs ∧ T < q ∧ OrReaches n C u q := by
    rcases chain_with_reaches T u huT with he | h
    · rw [he,hemptyT] at hu
      simp at hu
    · exact h
  have he := unique_bad_readers G C hcount T p T q hbadT hemptyT hp pop hTin hTp (h2 p hp)
    hbadT hemptyT hq qop hTin' hTq (h2 q hq)
  subst q
  exact orIn_subset_of_reach C u p huq

lemma wire_true_frontier {n : ℕ} (C : Circuit) (hAO : IsAO2 n C) :
    ∀ w, w < n + C.gates.length → ∀ x : Fin n → Bool, val C (List.ofFn x) w = true →
      (∃ v ∈ orIn n C w, x v = true) ∨
      ∃ a < C.gates.length, (gateAt C a).op = GateOp.and ∧
        OrReaches n C w a ∧ gateVal n C a x = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hw x hx
    by_cases hwn : w < n
    · let v : Fin n := ⟨w,hwn⟩
      have he : val C (List.ofFn x) w = x v := val_ofFn C x v
      exact Or.inl ⟨v,(orIn_input_mem C w hwn v).mpr rfl,by rwa [he] at hx⟩
    · obtain ⟨r,rfl⟩ : ∃ r, w = n + r := ⟨w-n,by omega⟩
      have hr : r < C.gates.length := by omega
      rcases hAO.1 _ (gateAt_mem hr) with ha | ho
      · exact Or.inr ⟨r,hr,ha,(orReaches_iff n C r r).mpr ⟨hr,Or.inl rfl⟩,hx⟩
      · obtain ⟨u,hu,hul,hux⟩ := (val_or (n := n) (by simp) hr ho).mp hx
        rcases ih u hul (by omega) x hux with ⟨v,hvu,hvx⟩ | ⟨a,hal,hao,hua,hax⟩
        · exact Or.inl ⟨v,(orIn_gate_iff C r v).mpr ⟨hr,ho,u,hu,hul,hvu⟩,hvx⟩
        · exact Or.inr ⟨a,hal,hao,(orReaches_iff n C r a).mpr ⟨hr,Or.inr ⟨ho,u,hu,hul,hua⟩⟩,hax⟩

lemma edge_top_trace {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hAO : IsAO2 n C)
    (hF : PEqualNP.MetaComplexity.circuitFun n C = graphFun G ∅)
    (u v : Fin n) (huv : G.Adj u v) :
    ∃ a ∈ tops G C, gateVal n C a (pairInput u v) = true := by
  letI : DecidableEq GateOp := gateOpDecEq
  have hout : val C (List.ofFn (pairInput u v)) C.output = true := by
    change PEqualNP.MetaComplexity.circuitFun n C (pairInput u v) = true
    rw [hF]
    simp only [graphFun,Bool.or_eq_true,decide_eq_true_eq]
    exact Or.inr ⟨u,v,huv,by simp [pairInput],by simp [pairInput]⟩
  have holt : C.output < n + C.gates.length := by
    by_contra hn
    have he := val_ge (n := n) (C := C) (x := List.ofFn (pairInput u v)) (by simp) (by omega : n + C.gates.length ≤ C.output)
    rw [he] at hout
    cases hout
  rcases wire_true_frontier C hAO C.output holt (pairInput u v) hout with ⟨z,hz,_⟩ | ⟨a,hal,hao,hra,hax⟩
  · have hzout := orIn_true C C.output z (pairInput z z) hz (by simp [pairInput])
    have hbad : graphFun G ∅ (pairInput z z) = true := by
      rw [← hF]
      exact hzout
    exact False.elim (G.irrefl (graph_pair_adj G z z hbad))
  · refine ⟨a,Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hal,hao,?_⟩,hax⟩
    intro x hx
    rw [← hF]
    exact orReach_true C a x C.output hra hx

lemma primary_pair_star {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hAO : IsAO2 n C) (a : ℕ) (ha : a ∈ tops G C) (u v : Fin n)
    (h0 : ∃ z ∈ side (n := n) C a 0, pairInput u v z = true)
    (h1 : ∃ z ∈ side (n := n) C a 1, pairInput u v z = true) :
    s(u,v) ∈ starEdges G C := by
  classical
  obtain ⟨p,hp,hpx⟩ := h0
  obtain ⟨q,hq,hqx⟩ := h1
  have hpv : p = u ∨ p = v := by simpa [pairInput] using hpx
  have hqv : q = u ∨ q = v := by simpa [pairInput] using hqx
  have hpq := clean_cross_adj G C hAO a ha p q hp hq
  have he : s(p,q) = s(u,v) := by
    rcases hpv with hpu | hpv <;> rcases hqv with hqu | hqv
    · rw [hpu,hqu] at hpq
      exact False.elim (G.irrefl hpq)
    · exact Sym2.eq_iff.mpr (Or.inl ⟨hpu,hqv⟩)
    · exact Sym2.eq_iff.mpr (Or.inr ⟨hpv,hqu⟩)
    · rw [hpv,hqv] at hpq
      exact False.elim (G.irrefl hpq)
  exact Finset.mem_biUnion.mpr ⟨a,ha,Finset.mem_image.mpr ⟨(p,q),Finset.mem_product.mpr ⟨hp,hq⟩,he⟩⟩

lemma primary_pair_star_oriented {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hAO : IsAO2 n C) (a : ℕ) (ha : a ∈ tops G C) (u v : Fin n) (b : Fin 2)
    (h0 : ∃ z ∈ side (n := n) C a b, pairInput u v z = true)
    (h1 : ∃ z ∈ side (n := n) C a (1-b), pairInput u v z = true) :
    s(u,v) ∈ starEdges G C := by
  fin_cases b
  · exact primary_pair_star G C hAO a ha u v h0 h1
  · exact primary_pair_star G C hAO a ha u v h1 h0

lemma clean_cross_adj_oriented {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hAO : IsAO2 n C) (a : ℕ) (ha : a ∈ tops G C) (b : Fin 2)
    (u v : Fin n) (hu : u ∈ side (n := n) C a b) (hv : v ∈ side (n := n) C a (1-b)) : G.Adj u v := by
  fin_cases b
  · exact clean_cross_adj G C hAO a ha u v hu hv
  · exact (clean_cross_adj G C hAO a ha v u hv hu).symm

lemma uncovered_top_signal {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (g T : ℕ) (hAO : IsAO2 n C) (hTop : TopForm G C)
    (hJ : junk G C = {g,T}) (hc : centreless G C = ∅)
    (hsole : ∀ r < C.gates.length, n + g ∈ (gateAt C r).inputs → r = T)
    (a : ℕ) (ha : a ∈ tops G C) (u v : Fin n)
    (hax : gateVal n C a (pairInput u v) = true) (hn : s(u,v) ∉ starEdges G C) :
    ∃ b : Fin 2, OrReaches n C (opnd C a b) T ∧ gateVal n C T (pairInput u v) = true ∧
      ∃ q ∈ side (n := n) C a (1-b), pairInput u v q = true := by
  letI : DecidableEq GateOp := gateOpDecEq
  have hal : a < C.gates.length := Finset.mem_range.mp (Finset.mem_filter.mp ha).1
  have hao : (gateAt C a).op = GateOp.and := (Finset.mem_filter.mp ha).2.1
  rw [and_gate_eval C hAO a hal hao (pairInput u v),Bool.and_eq_true] at hax
  have h0 := (top_side_decomposition G C g T hAO hTop hJ hc hsole a ha 0 (pairInput u v)).mp hax.1
  have h1 := (top_side_decomposition G C g T hAO hTop hJ hc hsole a ha 1 (pairInput u v)).mp hax.2
  rcases h0 with hp0 | ⟨hr0,hT0⟩ <;> rcases h1 with hp1 | ⟨hr1,hT1⟩
  · exact False.elim (hn (primary_pair_star G C hAO a ha u v hp0 hp1))
  · exact ⟨1,hr1,hT1,by simpa using hp0⟩
  · exact ⟨0,hr0,hT0,by simpa using hp1⟩
  · have hT : T ∈ junk G C := by rw [hJ]; simp
    exact False.elim (top_not_both_reach_dirty G C hAO T a hT ha ⟨hr0,hr1⟩)

lemma uncovered_edge_witness {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (g T : ℕ) (hAO : IsAO2 n C) (hTop : TopForm G C)
    (hF : PEqualNP.MetaComplexity.circuitFun n C = graphFun G ∅)
    (hJ : junk G C = {g,T}) (hc : centreless G C = ∅)
    (hsole : ∀ r < C.gates.length, n + g ∈ (gateAt C r).inputs → r = T)
    (z : Fin n)
    (hz : ∀ a ∈ tops G C, ∀ b : Fin 2, OrReaches n C (opnd C a b) T → z ∈ side (n := n) C a b)
    (u v : Fin n) (huv : G.Adj u v) (hn : s(u,v) ∉ starEdges G C) :
    gateVal n C T (pairInput u v) = true ∧ u ≠ z ∧ v ≠ z ∧
      ∃ a ∈ tops G C, ∃ b : Fin 2, OrReaches n C (opnd C a b) T ∧
        (∀ q ∈ side (n := n) C a (1-b), G.Adj z q) ∧
        ∃ q ∈ side (n := n) C a (1-b), q = u ∨ q = v := by
  obtain ⟨a,ha,hax⟩ := edge_top_trace G C hAO hF u v huv
  obtain ⟨b,hb,hTx,hq⟩ := uncovered_top_signal G C g T hAO hTop hJ hc hsole a ha u v hax hn
  have hzside := hz a ha b hb
  have hzx : pairInput u v z ≠ true := by
    intro hzx
    exact hn (primary_pair_star_oriented G C hAO a ha u v b ⟨z,hzside,hzx⟩ hq)
  have huz : u ≠ z := by
    intro he
    subst u
    exact hzx (by simp [pairInput])
  have hvz : v ≠ z := by
    intro he
    subst v
    exact hzx (by simp [pairInput])
  refine ⟨hTx,huz,hvz,a,ha,b,hb,?_,?_⟩
  · intro q hq
    exact clean_cross_adj_oriented G C hAO a ha b z q hzside hq
  · obtain ⟨q,hq,hqx⟩ := hq
    exact ⟨q,hq,by simpa [pairInput] using hqx⟩

end PEqualNP.Outside.L_meta_9811.DirtyReader
