import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1904_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

lemma exists_minimizer {α : Type*} (P : α → Prop) (measure : α → ℕ)
    (hex : ∃ a, P a) : ∃ a, P a ∧ ∀ b, P b → measure a ≤ measure b := by
  classical
  have h : ∃ k, ∃ a, P a ∧ measure a = k := by
    obtain ⟨a, ha⟩ := hex
    exact ⟨measure a, a, ha, rfl⟩
  obtain ⟨a, ha, hm⟩ := Nat.find_spec h
  refine ⟨a, ha, ?_⟩
  intro b hb
  rw [hm]
  exact Nat.find_min' h ⟨b, hb, rfl⟩

def Correct {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) : Prop :=
  Monotone2 C ∧ ∀ x : Fin n → Bool,
    C.eval (List.ofFn x) = decide (∃ u v, G.Adj u v ∧ x u = true ∧ x v = true)

noncomputable def dirtySet {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) : Finset ℕ := by
  classical
  exact (Finset.range C.size).filter (PEqualNP.CleanedNonEdge.IsDirtyAnd n G C)

lemma exists_extremal {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hex : ∃ C, Correct G C) :
    ∃ C, Correct G C ∧
      (∀ D, Correct G D → C.size ≤ D.size) ∧
      ∀ D, Correct G D → D.size ≤ C.size →
        (dirtySet G C).card ≤ (dirtySet G D).card := by
  classical
  obtain ⟨C, hC, hmin⟩ := exists_minimizer (Correct G) Circuit.size hex
  obtain ⟨D, ⟨hD, hsize⟩, hdirty⟩ := exists_minimizer
    (fun D => Correct G D ∧ D.size ≤ C.size)
    (fun D => (dirtySet G D).card) ⟨C, hC, le_rfl⟩
  refine ⟨D, hD, fun E hE => hsize.trans (hmin E hE), ?_⟩
  intro E hE hED
  exact hdirty E ⟨hE, hED.trans hsize⟩

lemma dirty_card_decreases {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C D : Circuit) (j : ℕ) (hsub : dirtySet G D ⊆ dirtySet G C)
    (hC : j ∈ dirtySet G C) (hD : j ∉ dirtySet G D) :
    (dirtySet G D).card < (dirtySet G C).card := by
  exact Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr
    ⟨hsub, fun h => hD (h.symm ▸ hC)⟩)

lemma extremal_no_repair {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit)
    (hmin : ∀ D, Correct G D → D.size ≤ C.size →
      (dirtySet G C).card ≤ (dirtySet G D).card)
    (D : Circuit) (hD : Correct G D) (hsize : D.size ≤ C.size)
    (hsub : dirtySet G D ⊆ dirtySet G C) (j : ℕ)
    (hCj : j ∈ dirtySet G C) : j ∈ dirtySet G D := by
  by_contra hDj
  exact Nat.not_lt_of_ge (hmin D hD hsize)
    (dirty_card_decreases G C D j hsub hCj hDj)

noncomputable def falseTrace {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) : Finset (ℕ × (Fin n → Bool)) := by
  classical
  exact ((Finset.range C.size).product Finset.univ).filter fun p =>
    (¬ ∃ u v, G.Adj u v ∧ p.2 u = true ∧ p.2 v = true) ∧
    (C.wires (List.ofFn p.2)).getD (n + p.1) false = true

lemma exists_trace_extremal {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hex : ∃ C, Correct G C) :
    ∃ C, Correct G C ∧
      (∀ D, Correct G D → C.size ≤ D.size) ∧
      ∀ D, Correct G D → D.size ≤ C.size →
        (falseTrace G C).card ≤ (falseTrace G D).card := by
  classical
  obtain ⟨C, hC, hmin⟩ := exists_minimizer (Correct G) Circuit.size hex
  obtain ⟨D, ⟨hD, hsize⟩, htrace⟩ := exists_minimizer
    (fun D => Correct G D ∧ D.size ≤ C.size)
    (fun D => (falseTrace G D).card) ⟨C, hC, le_rfl⟩
  refine ⟨D, hD, fun E hE => hsize.trans (hmin E hE), ?_⟩
  intro E hE hED
  exact htrace E ⟨hE, hED.trans hsize⟩

lemma falseTrace_subset {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C D : Circuit) (hlen : D.size ≤ C.size)
    (hdown : ∀ (x : Fin n → Bool) (j : ℕ), j < D.size →
      (D.wires (List.ofFn x)).getD (n+j) false = true →
      (C.wires (List.ofFn x)).getD (n+j) false = true) :
    falseTrace G D ⊆ falseTrace G C := by
  classical
  intro p hp
  have hm := (Finset.mem_filter.mp hp)
  have hj := Finset.mem_range.mp (Finset.mem_product.mp hm.1).1
  apply Finset.mem_filter.mpr
  exact ⟨Finset.mem_product.mpr ⟨Finset.mem_range.mpr (hj.trans_le hlen),
    Finset.mem_univ _⟩, hm.2.1, hdown p.2 p.1 hj hm.2.2⟩

lemma trace_extremal_no_decrease {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit)
    (hmin : ∀ D, Correct G D → D.size ≤ C.size →
      (falseTrace G C).card ≤ (falseTrace G D).card)
    (D : Circuit) (hD : Correct G D) (hsize : D.size ≤ C.size)
    (hdown : ∀ (x : Fin n → Bool) (j : ℕ), j < D.size →
      (D.wires (List.ofFn x)).getD (n+j) false = true →
      (C.wires (List.ofFn x)).getD (n+j) false = true)
    (j : ℕ) (hj : j < C.size) (x : Fin n → Bool)
    (hx : ¬ ∃ u v, G.Adj u v ∧ x u = true ∧ x v = true)
    (hCx : (C.wires (List.ofFn x)).getD (n+j) false = true) :
    (D.wires (List.ofFn x)).getD (n+j) false = true := by
  classical
  have hsub := falseTrace_subset G C D hsize hdown
  have heq : falseTrace G D = falseTrace G C :=
    Finset.eq_of_subset_of_card_le hsub (hmin D hD hsize)
  have hp : (j,x) ∈ falseTrace G C := by
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_product.mpr ⟨Finset.mem_range.mpr hj, Finset.mem_univ _⟩,
      hx, hCx⟩
  rw [← heq] at hp
  exact (Finset.mem_filter.mp hp).2.2


namespace Surgery


open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def deletionRun (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

def deletionIndex (k q i : ℕ) : ℕ :=
  if i < k then i else if i = k then q else i - 1

def deletionGate (k q : ℕ) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map (deletionIndex k q)⟩

lemma deletionRun_append (gs hs : List Gate) (w : List Bool) :
    deletionRun (gs ++ hs) w = deletionRun hs (deletionRun gs w) := by
  simp only [deletionRun, List.foldl_append]

lemma deletionRun_length (gs : List Gate) (w : List Bool) :
    (deletionRun gs w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [deletionRun, List.foldl_cons] at *
    rw [ih]
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega

lemma deletionRun_prefix (gs : List Gate) (w : List Bool) :
    ∃ t, deletionRun gs w = w ++ t := by
  induction gs generalizing w with
  | nil => exact ⟨[], by simp [deletionRun]⟩
  | cons g gs ih =>
    obtain ⟨t, ht⟩ := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    exact ⟨_ :: t, by simpa [deletionRun, List.foldl_cons, List.append_assoc] using ht⟩

lemma deletion_getD_core (p t : List Bool) (b : Bool) (q i : ℕ)
    (hq : (p ++ t).getD q false = b) :
    (p ++ b :: t).getD i false =
      (p ++ t).getD (deletionIndex p.length q i) false := by
  by_cases hi : i < p.length
  · simp only [deletionIndex, ite_eq_left hi]
    rw [List.getD_append _ _ _ _ hi, List.getD_append _ _ _ _ hi]
  · by_cases he : i = p.length
    · subst i
      simp only [deletionIndex, lt_self_iff_false, ite_false]
      rw [List.getD_eq_getElem?_getD,
        List.getElem?_append_right (by omega), Nat.sub_self]
      simp only [List.getElem?_cons_zero, Option.getD_some]
      exact hq.symm
    · have hgt : p.length < i := by omega
      have hge : p.length ≤ i - 1 := by omega
      have hd : i - p.length = (i - 1 - p.length) + 1 := by omega
      simp only [deletionIndex, ite_eq_right hi, ite_eq_right he]
      rw [List.getD_eq_getElem?_getD,
        List.getElem?_append_right (by omega), hd,
        List.getElem?_cons_succ]
      rw [List.getD_eq_getElem?_getD,
        List.getElem?_append_right hge]

lemma deletion_getD (p t : List Bool) (q i : ℕ)
    (hq : p.length + t.length ≤ q) :
    (p ++ false :: t).getD i false =
      (p ++ t).getD (deletionIndex p.length q i) false :=
  deletion_getD_core p t false q i (List.getD_eq_default _ _ (by simpa using hq))

lemma deletionRun_suffix (p t : List Bool) (gs : List Gate) (q : ℕ)
    (hq : p.length + t.length + gs.length ≤ q) :
    ∃ u, deletionRun gs (p ++ false :: t) = p ++ false :: u ∧
      deletionRun (gs.map (deletionGate p.length q)) (p ++ t) = p ++ u ∧
      u.length = t.length + gs.length := by
  induction gs generalizing t with
  | nil => exact ⟨t, rfl, rfl, by simp⟩
  | cons g gs ih =>
    let b := g.op.eval (g.inputs.map fun i => (p ++ false :: t).getD i false)
    have hvalue : (deletionGate p.length q g).op.eval
        ((deletionGate p.length q g).inputs.map fun i => (p ++ t).getD i false) = b := by
      simp only [deletionGate, List.map_map]
      congr 1
      apply List.map_congr_left
      intro i hi
      exact (deletion_getD p t q i (by omega)).symm
    obtain ⟨u, hu, hv, hl⟩ := ih (t ++ [b]) (by
      simp only [List.length_append, List.length_cons, List.length_nil] at *
      omega)
    refine ⟨u, ?_, ?_, ?_⟩
    · simpa only [deletionRun, List.foldl_cons, List.append_assoc,
        List.cons_append] using hu
    · simpa only [List.map_cons, deletionRun, List.foldl_cons, hvalue,
        List.append_assoc] using hv
    · simp only [List.length_append, List.length_cons, List.length_nil] at *
      omega

lemma deletionRun_gate_value (pre rest : List Gate) (g : Gate) (x : List Bool) :
    (deletionRun (pre ++ g :: rest) x).getD (x.length + pre.length) false =
      g.op.eval (g.inputs.map fun i => (deletionRun pre x).getD i false) := by
  let b := g.op.eval (g.inputs.map fun i => (deletionRun pre x).getD i false)
  have he : deletionRun (pre ++ g :: rest) x =
      deletionRun rest (deletionRun pre x ++ [b]) := by
    simp only [deletionRun, List.foldl_append, List.foldl_cons]
    rfl
  obtain ⟨t, ht⟩ := deletionRun_prefix rest (deletionRun pre x ++ [b])
  rw [he, ht, List.append_assoc]
  rw [← deletionRun_length pre x, List.getD_eq_getElem?_getD,
    List.getElem?_append_right (by omega), Nat.sub_self]
  rfl

lemma delete_false_gate_split (n : ℕ) (pre rest : List Gate) (g : Gate) (out : ℕ)
    (hm : Monotone2 ⟨pre ++ g :: rest, out⟩)
    (hz : ∀ x : Fin n → Bool,
      (Circuit.wires ⟨pre ++ g :: rest, out⟩ (List.ofFn x)).getD
        (n + pre.length) false = false) :
    ∃ D : Circuit, Monotone2 D ∧
      D.size + 1 = (Circuit.size ⟨pre ++ g :: rest, out⟩) ∧
      ∀ x : Fin n → Bool, D.eval (List.ofFn x) =
        (Circuit.eval ⟨pre ++ g :: rest, out⟩ (List.ofFn x)) := by
  let k := n + pre.length
  let q := n + pre.length + rest.length
  let D : Circuit := ⟨pre ++ rest.map (deletionGate k q), deletionIndex k q out⟩
  refine ⟨D, ?_, ?_, ?_⟩
  · intro h hh
    change h ∈ pre ++ rest.map (deletionGate k q) at hh
    rcases List.mem_append.mp hh with hh | hh
    · exact hm h (List.mem_append_left _ hh)
    · obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hh
      have H := hm a (List.mem_append_right _ (List.mem_cons_of_mem _ ha))
      exact ⟨H.1, by simpa [deletionGate] using H.2⟩
  · simp [D, Circuit.size, Nat.add_assoc]
  · intro x
    let p := deletionRun pre (List.ofFn x)
    have hp : p.length = k := by simp [p, deletionRun_length, k]
    have hzero : g.op.eval (g.inputs.map fun i => p.getD i false) = false := by
      have z := hz x
      change (deletionRun (pre ++ g :: rest) (List.ofFn x)).getD
        (n + pre.length) false = false at z
      have hv := deletionRun_gate_value pre rest g (List.ofFn x)
      simp only [List.length_ofFn] at hv
      rw [hv] at z
      exact z
    obtain ⟨u, hu, hv, hl⟩ := deletionRun_suffix p [] rest q (by simp [hp, q, k])
    have hOld : Circuit.wires ⟨pre ++ g :: rest, out⟩ (List.ofFn x) =
        p ++ false :: u := by
      change deletionRun (pre ++ g :: rest) (List.ofFn x) = _
      rw [deletionRun_append]
      change deletionRun rest (p ++ [g.op.eval (g.inputs.map fun i => p.getD i false)]) = _
      rw [hzero]
      exact hu
    have hNew : D.wires (List.ofFn x) = p ++ u := by
      change deletionRun (pre ++ rest.map (deletionGate k q)) (List.ofFn x) = _
      rw [deletionRun_append]
      simpa only [List.append_nil, hp] using hv
    change (D.wires (List.ofFn x)).getD (deletionIndex k q out) false =
      (Circuit.wires ⟨pre ++ g :: rest, out⟩ (List.ofFn x)).getD out false
    rw [hOld, hNew, ← hp]
    exact (deletion_getD p u q out (by simp only [List.length_nil, Nat.zero_add] at hl; dsimp [q, k] at hp ⊢; omega)).symm

lemma deletionRun_alias_suffix (p t : List Bool) (gs : List Gate) (r : ℕ)
    (hr : r < p.length) :
    ∃ u, deletionRun gs (p ++ p.getD r false :: t) = p ++ p.getD r false :: u ∧
      deletionRun (gs.map (deletionGate p.length r)) (p ++ t) = p ++ u ∧
      u.length = t.length + gs.length := by
  induction gs generalizing t with
  | nil => exact ⟨t, rfl, rfl, by simp⟩
  | cons g gs ih =>
    let b := g.op.eval (g.inputs.map fun i => (p ++ p.getD r false :: t).getD i false)
    have hvalue : (deletionGate p.length r g).op.eval
        ((deletionGate p.length r g).inputs.map fun i => (p ++ t).getD i false) = b := by
      simp only [deletionGate, List.map_map]
      congr 1
      apply List.map_congr_left
      intro i hi
      exact (deletion_getD_core p t (p.getD r false) r i
        (List.getD_append _ _ _ _ hr)).symm
    obtain ⟨u, hu, hv, hl⟩ := ih (t ++ [b])
    refine ⟨u, ?_, ?_, ?_⟩
    · simpa only [deletionRun, List.foldl_cons, List.append_assoc,
        List.cons_append] using hu
    · simpa only [List.map_cons, deletionRun, List.foldl_cons, hvalue,
        List.append_assoc] using hv
    · simp only [List.length_append, List.length_cons, List.length_nil] at *
      omega

lemma delete_alias_gate_split (n : ℕ) (pre rest : List Gate) (g : Gate) (out r : ℕ)
    (hr : r < n + pre.length)
    (hm : Monotone2 ⟨pre ++ g :: rest, out⟩)
    (hz : ∀ x : Fin n → Bool,
      (Circuit.wires ⟨pre ++ g :: rest, out⟩ (List.ofFn x)).getD
        (n + pre.length) false = (deletionRun pre (List.ofFn x)).getD r false) :
    ∃ D : Circuit, Monotone2 D ∧
      D.size + 1 = (Circuit.size ⟨pre ++ g :: rest, out⟩) ∧
      ∀ x : Fin n → Bool, D.eval (List.ofFn x) =
        (Circuit.eval ⟨pre ++ g :: rest, out⟩ (List.ofFn x)) := by
  let k := n + pre.length
  let D : Circuit := ⟨pre ++ rest.map (deletionGate k r), deletionIndex k r out⟩
  refine ⟨D, ?_, ?_, ?_⟩
  · intro h hh
    change h ∈ pre ++ rest.map (deletionGate k r) at hh
    rcases List.mem_append.mp hh with hh | hh
    · exact hm h (List.mem_append_left _ hh)
    · obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hh
      have H := hm a (List.mem_append_right _ (List.mem_cons_of_mem _ ha))
      exact ⟨H.1, by simpa [deletionGate] using H.2⟩
  · simp [D, Circuit.size, Nat.add_assoc]
  · intro x
    let p := deletionRun pre (List.ofFn x)
    have hp : p.length = k := by simp [p, deletionRun_length, k]
    have hzero : g.op.eval (g.inputs.map fun i => p.getD i false) = p.getD r false := by
      have z := hz x
      change (deletionRun (pre ++ g :: rest) (List.ofFn x)).getD
        (n + pre.length) false = p.getD r false at z
      have hv := deletionRun_gate_value pre rest g (List.ofFn x)
      simp only [List.length_ofFn] at hv
      rw [hv] at z
      exact z
    obtain ⟨u, hu, hv, hl⟩ := deletionRun_alias_suffix p [] rest r (by simpa [hp, k] using hr)
    have hOld : Circuit.wires ⟨pre ++ g :: rest, out⟩ (List.ofFn x) =
        p ++ p.getD r false :: u := by
      change deletionRun (pre ++ g :: rest) (List.ofFn x) = _
      rw [deletionRun_append]
      change deletionRun rest (p ++ [g.op.eval (g.inputs.map fun i => p.getD i false)]) = _
      rw [hzero]
      exact hu
    have hNew : D.wires (List.ofFn x) = p ++ u := by
      change deletionRun (pre ++ rest.map (deletionGate k r)) (List.ofFn x) = _
      rw [deletionRun_append]
      simpa only [List.append_nil, hp] using hv
    change (D.wires (List.ofFn x)).getD (deletionIndex k r out) false =
      (Circuit.wires ⟨pre ++ g :: rest, out⟩ (List.ofFn x)).getD out false
    rw [hOld, hNew, ← hp]
    exact (deletion_getD_core p u (p.getD r false) r out
      (List.getD_append _ _ _ _ (by simpa [hp, k] using hr))).symm




open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def run (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

def WireLE (v w : List Bool) : Prop :=
  ∀ i, v.getD i false = true → w.getD i false = true

lemma run_append (gs hs : List Gate) (w : List Bool) :
    run (gs ++ hs) w = run hs (run gs w) := by
  simp [run, List.foldl_append]

lemma run_length (gs : List Gate) (w : List Bool) :
    (run gs w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp [run]
  | cons g gs ih =>
    change (run gs (w ++ [_])).length = _
    rw [ih]
    simp
    omega

lemma wireLE_snoc {v w : List Bool} (hl : v.length = w.length) (h : WireLE v w)
    {a b : Bool} (hab : a = true → b = true) : WireLE (v ++ [a]) (w ++ [b]) := by
  intro i hi
  by_cases old : i < v.length
  · rw [List.getD_append _ _ _ _ old] at hi
    rw [List.getD_append _ _ _ _ (by omega)]
    exact h i hi
  · have hw : ¬ i < w.length := by omega
    simp only [List.getD_eq_getElem?_getD, List.getElem?_append, ite_eq_right hw, hl] at hi ⊢
    cases hiw : i - w.length with
    | zero => simpa [hiw] using hab (by simpa [hiw] using hi)
    | succ k => simp [hiw] at hi

lemma gate_mono {v w : List Bool} (h : WireLE v w) {g : Gate}
    (hop : g.op = .and ∨ g.op = .or) :
    g.op.eval (g.inputs.map fun i => v.getD i false) = true →
    g.op.eval (g.inputs.map fun i => w.getD i false) = true := by
  rcases hop with ha | ho
  · simp only [ha, GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id_eq]
    exact fun hv i hi => h i (hv i hi)
  · simp only [ho, GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id_eq]
    rintro ⟨i, hi, hv⟩
    exact ⟨i, hi, h i hv⟩

lemma run_mono (gs : List Gate) {v w : List Bool} (hl : v.length = w.length)
    (h : WireLE v w) (hm : ∀ g ∈ gs, g.op = .and ∨ g.op = .or) :
    WireLE (run gs v) (run gs w) := by
  induction gs generalizing v w with
  | nil => exact h
  | cons g gs ih =>
    apply ih
    · simpa using hl
    · exact wireLE_snoc hl h (gate_mono h (hm g (by simp)))
    · exact fun a ha => hm a (by simp [ha])

lemma bypass_safe_child {n : ℕ} (pre rest : List Gate) (g : Gate) (out r : ℕ)
    (F : (Fin n → Bool) → Bool)
    (hm : Monotone2 ⟨pre ++ g :: rest, out⟩)
    (hand : g.op = .and) (hr : r ∈ g.inputs)
    (hsafe : ∀ x : Fin n → Bool,
      (run pre (List.ofFn x)).getD r false = true → F x = true)
    (hcorrect : ∀ x : Fin n → Bool,
      (⟨pre ++ g :: rest, out⟩ : Circuit).eval (List.ofFn x) = F x) :
    Monotone2 ⟨pre ++ ⟨.or, [r]⟩ :: rest, out⟩ ∧
    (⟨pre ++ ⟨.or, [r]⟩ :: rest, out⟩ : Circuit).size =
      (⟨pre ++ g :: rest, out⟩ : Circuit).size ∧
    ∀ x : Fin n → Bool,
      (⟨pre ++ ⟨.or, [r]⟩ :: rest, out⟩ : Circuit).eval (List.ofFn x) = F x := by
  refine ⟨?_, by simp [Circuit.size], ?_⟩
  · intro a ha
    rcases List.mem_append.mp ha with hp | ht
    · exact hm a (List.mem_append_left _ hp)
    · rcases List.mem_cons.mp ht with he | ht
      · subst a
        simp
      · exact hm a (List.mem_append_right _ (List.mem_cons_of_mem _ ht))
  · intro x
    let w := run pre (List.ofFn x)
    let b := g.op.eval (g.inputs.map fun i => w.getD i false)
    let c := w.getD r false
    have hc : b = true → c = true := by
      intro hb
      have all : ∀ i ∈ g.inputs, w.getD i false = true := by
        simpa [b, hand, GateOp.eval] using hb
      exact all r hr
    have old : (run rest (w ++ [b])).getD out false = F x := by
      simpa only [Circuit.eval, Circuit.wires, List.foldl_append, List.foldl_cons,
        run, w, b] using hcorrect x
    have new : (⟨pre ++ ⟨.or, [r]⟩ :: rest, out⟩ : Circuit).eval (List.ofFn x) =
        (run rest (w ++ [c])).getD out false := by
      simp [Circuit.eval, Circuit.wires, run, List.foldl_append, GateOp.eval, w, c]
    rw [new]
    cases hf : F x with
    | false =>
      have hcf : c = false := by
        cases h : c
        · rfl
        · have ht := hsafe x h
          rw [hf] at ht
          contradiction
      have hbf : b = false := by
        cases h : b
        · rfl
        · have ht := hc h
          rw [hcf] at ht
          contradiction
      simpa [hcf, hbf, hf] using old
    | true =>
      have hh : WireLE (w ++ [b]) (w ++ [c]) :=
        wireLE_snoc rfl (fun _ h => h) hc
      have hrest : ∀ a ∈ rest, a.op = .and ∨ a.op = .or := by
        intro a ha
        simpa using (hm a (List.mem_append_right _ (List.mem_cons_of_mem _ ha))).1
      exact run_mono rest (by simp) hh hrest out (by simpa [hf] using old)


open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

lemma delete_safe_child {n : ℕ} (pre rest : List Gate) (g : Gate) (out r : ℕ)
    (F : (Fin n → Bool) → Bool)
    (hm : Monotone2 ⟨pre ++ g :: rest, out⟩)
    (hand : g.op = .and) (hr : r ∈ g.inputs)
    (hsafe : ∀ x : Fin n → Bool,
      (run pre (List.ofFn x)).getD r false = true → F x = true)
    (hcorrect : ∀ x : Fin n → Bool,
      (⟨pre ++ g :: rest, out⟩ : Circuit).eval (List.ofFn x) = F x) :
    ∃ D : Circuit, Monotone2 D ∧ D.size + 1 = (⟨pre ++ g :: rest, out⟩ : Circuit).size ∧
      ∀ x : Fin n → Bool, D.eval (List.ofFn x) = F x := by
  obtain ⟨hmono, hsize, hvalue⟩ := bypass_safe_child pre rest g out r F hm hand hr hsafe hcorrect
  have wire (x : Fin n → Bool) :
      (Circuit.wires ⟨pre ++ ⟨.or,[r]⟩ :: rest,out⟩ (List.ofFn x)).getD
        (n + pre.length) false = (deletionRun pre (List.ofFn x)).getD r false := by
    have e := deletionRun_gate_value pre rest ⟨.or,[r]⟩ (List.ofFn x)
    simpa [Circuit.wires, deletionRun, GateOp.eval] using e
  by_cases valid : r < n + pre.length
  · obtain ⟨D, hD, hDs, hDe⟩ := delete_alias_gate_split n pre rest ⟨.or,[r]⟩ out r valid hmono wire
    exact ⟨D, hD, hDs.trans hsize, fun x => (hDe x).trans (hvalue x)⟩
  · have zero (x : Fin n → Bool) :
        (Circuit.wires ⟨pre ++ ⟨.or,[r]⟩ :: rest,out⟩ (List.ofFn x)).getD
          (n + pre.length) false = false := by
      rw [wire]
      exact List.getD_eq_default _ _ (by simp [deletionRun_length]; omega)
    obtain ⟨D, hD, hDs, hDe⟩ := delete_false_gate_split n pre rest ⟨.or,[r]⟩ out hmono zero
    exact ⟨D, hD, hDs.trans hsize, fun x => (hDe x).trans (hvalue x)⟩

lemma minimal_and_child_not_below {n : ℕ} (pre rest : List Gate) (g : Gate) (out r : ℕ)
    (hmin : IsMinimalMonoCircuit n ⟨pre ++ g :: rest, out⟩)
    (hand : g.op = .and) (hr : r ∈ g.inputs) :
    ∃ x : Fin n → Bool, (run pre (List.ofFn x)).getD r false = true ∧
      (⟨pre ++ g :: rest,out⟩ : Circuit).eval (List.ofFn x) = false := by
  classical
  by_contra no
  have hs : ∀ x : Fin n → Bool, (run pre (List.ofFn x)).getD r false = true →
      (⟨pre ++ g :: rest,out⟩ : Circuit).eval (List.ofFn x) = true := by
    intro x hx
    cases he : (⟨pre ++ g :: rest,out⟩ : Circuit).eval (List.ofFn x)
    · exact (no ⟨x,hx,he⟩).elim
    · rfl
  obtain ⟨D,hD,hsize,hval⟩ := delete_safe_child pre rest g out r
    (fun x => (⟨pre ++ g :: rest,out⟩ : Circuit).eval (List.ofFn x))
    hmin.1 hand hr hs (fun _ => rfl)
  have hle := hmin.2 D hD (funext hval)
  omega


end Surgery

namespace Repair



open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def run (gs : List Gate) (w : List Bool) : List Bool := gs.foldl step w

def WireLE (v w : List Bool) : Prop :=
  ∀ i, v.getD i false = true → w.getD i false = true

lemma run_length (gs : List Gate) (w : List Bool) :
    (run gs w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp [run]
  | cons g gs ih =>
    change (run gs (step w g)).length = _
    rw [ih]
    simp [step]
    omega

lemma append_bit_le {v w : List Bool} (hlen : v.length = w.length)
    (hle : WireLE v w) {a b : Bool} (hab : a = true → b = true) :
    WireLE (v ++ [a]) (w ++ [b]) := by
  intro i hi
  by_cases hlt : i < v.length
  · simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hlt] at hi
    have hlt' : i < w.length := hlen ▸ hlt
    simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hlt']
    exact hle i hi
  · have hv : v.length ≤ i := by omega
    have hw : w.length ≤ i := by omega
    simp only [List.getD_eq_getElem?_getD, List.getElem?_append_right hv] at hi
    simp only [List.getD_eq_getElem?_getD, List.getElem?_append_right hw]
    rw [← hlen]
    cases hidx : i - v.length with
    | zero => simpa [hidx] using hab (by simpa [hidx] using hi)
    | succ k => simp [hidx] at hi

lemma gate_eval_le (g : Gate) (hop : g.op = GateOp.and ∨ g.op = GateOp.or)
    {v w : List Bool} (hle : WireLE v w) :
    g.op.eval (g.inputs.map fun i => v.getD i false) = true →
      g.op.eval (g.inputs.map fun i => w.getD i false) = true := by
  rcases hop with hop | hop
  · rw [hop]
    simp only [GateOp.eval, List.all_eq_true, List.mem_map, forall_exists_index,
      and_imp, forall_apply_eq_imp_iff₂]
    intro hv i hi
    exact hle i (hv i hi)
  · rw [hop]
    simp only [GateOp.eval, List.any_eq_true, List.mem_map]
    rintro ⟨b, ⟨i, hi, rfl⟩, hb⟩
    exact ⟨w.getD i false, ⟨i, hi, rfl⟩, hle i hb⟩

lemma run_le (gs : List Gate)
    (hmono : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
    {v w : List Bool} (hlen : v.length = w.length) (hle : WireLE v w) :
    WireLE (run gs v) (run gs w) := by
  induction gs generalizing v w with
  | nil => exact hle
  | cons g gs ih =>
    apply ih (fun g hg => hmono g (List.mem_cons_of_mem _ hg))
    · simp [step, hlen]
    · exact append_bit_le hlen hle (gate_eval_le g (hmono g (by simp)) hle)

lemma ofFn_le {n : ℕ} {x y : Fin n → Bool}
    (hxy : ∀ i, x i = true → y i = true) : WireLE (List.ofFn x) (List.ofFn y) := by
  intro i hi
  by_cases hin : i < n
  · simpa [List.getD_eq_getElem?_getD, hin] using hxy ⟨i, hin⟩
      (by simpa [List.getD_eq_getElem?_getD, hin] using hi)
  · simp [List.getD_eq_getElem?_getD, hin] at hi

lemma wires_mono {n : ℕ} {C : Circuit} (hC : Monotone2 C)
    {x y : Fin n → Bool} (hxy : ∀ i, x i = true → y i = true) :
    WireLE (C.wires (List.ofFn x)) (C.wires (List.ofFn y)) := by
  apply run_le C.gates
  · intro g hg
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using (hC g hg).1
  · simp
  · exact ofFn_le hxy

lemma edge_pair_extension {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    {C D : Circuit} (hD : Monotone2 D)
    (hC : ∀ x : Fin n → Bool, C.eval (List.ofFn x) =
      decide (∃ a b : Fin n, G.Adj a b ∧ x a = true ∧ x b = true))
    (hle : ∀ x : Fin n → Bool, D.eval (List.ofFn x) = true → C.eval (List.ofFn x) = true)
    (hpairs : ∀ a b : Fin n, G.Adj a b →
      D.eval (List.ofFn (PEqualNP.EdgeOwnership.pairInput a b)) = true) :
    ∀ x : Fin n → Bool, D.eval (List.ofFn x) =
      decide (∃ a b : Fin n, G.Adj a b ∧ x a = true ∧ x b = true) := by
  intro x
  apply Bool.eq_iff_iff.mpr
  rw [decide_eq_true_iff]
  constructor
  · intro hx
    exact of_decide_eq_true ((hC x).symm.trans (hle x hx))
  · rintro ⟨a, b, hab, ha, hb⟩
    apply wires_mono hD (y := x) (x := PEqualNP.EdgeOwnership.pairInput a b)
      (fun i hi => ?_) D.output (hpairs a b hab)
    have hi' : i = a ∨ i = b := of_decide_eq_true hi
    rcases hi' with rfl | rfl
    · exact ha
    · exact hb

lemma patch_le (pre post : List Gate) (g h : Gate) (out : ℕ) (x : List Bool)
    (hpost : ∀ q ∈ post, q.op = GateOp.and ∨ q.op = GateOp.or)
    (hgate : h.op.eval (h.inputs.map fun i => (run pre x).getD i false) = true →
      g.op.eval (g.inputs.map fun i => (run pre x).getD i false) = true) :
    WireLE (({gates := pre ++ h :: post, output := out} : Circuit).wires x)
      (({gates := pre ++ g :: post, output := out} : Circuit).wires x) := by
  change WireLE (run (pre ++ h :: post) x) (run (pre ++ g :: post) x)
  simp only [run, List.foldl_append, List.foldl_cons]
  apply run_le post hpost
  · simp [step]
  · exact append_bit_le rfl (fun _ hi => hi) hgate

lemma patch_agree (pre post : List Gate) (g h : Gate) (out : ℕ) (x : List Bool)
    (hgate : h.op.eval (h.inputs.map fun i => (run pre x).getD i false) =
      g.op.eval (g.inputs.map fun i => (run pre x).getD i false)) :
    ({gates := pre ++ h :: post, output := out} : Circuit).wires x =
      ({gates := pre ++ g :: post, output := out} : Circuit).wires x := by
  change run (pre ++ h :: post) x = run (pre ++ g :: post) x
  simp only [run, List.foldl_append, List.foldl_cons, step]
  change post.foldl step (run pre x ++ [_]) = post.foldl step (run pre x ++ [_])
  dsimp only [run] at hgate
  rw [hgate]


def hit {n} (G : SimpleGraph (Fin n)) (x : Fin n → Bool) :=
  ∃ a b, G.Adj a b ∧ x a = true ∧ x b = true

def mask {n} (S : Finset (Fin n)) (u : Fin n) := decide (u ∈ S)

lemma zero_critical_replacement {n : ℕ} (G : SimpleGraph (Fin n))
    (gate : (Fin n → Bool) → Bool)
    (tail : (Fin n → Bool) → Bool → Bool)
    (mono : ∀ x y : Fin n → Bool, ∀ p q : Bool,
      (∀ i, x i = true → y i = true) → (p = true → q = true) →
      tail x p = true → tail y q = true)
    (correct : ∀ x, tail x (gate x) = true ↔ hit G x)
    (survives : ∀ u v, G.Adj u v → tail (mask {u,v}) false = true) :
    ∀ x, tail x false = true ↔ hit G x := by
  intro x
  constructor
  · intro h
    exact (correct x).mp (mono x x false (gate x) (fun _ h => h)
      (by simp) h)
  · rintro ⟨u,v,uv,hu,hv⟩
    apply mono (mask {u,v}) x false false ?_ (fun h => h) (survives u v uv)
    intro i hi
    simp only [mask, decide_eq_true_eq, Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl
    · exact hu
    · exact hv

lemma single_critical_replacement {n : ℕ} (G : SimpleGraph (Fin n))
    (gate : (Fin n → Bool) → Bool)
    (tail : (Fin n → Bool) → Bool → Bool)
    (gate_mono : ∀ x y : Fin n → Bool,
      (∀ i, x i = true → y i = true) → gate x = true → gate y = true)
    (tail_mono : ∀ x y : Fin n → Bool, ∀ p q : Bool,
      (∀ i, x i = true → y i = true) → (p = true → q = true) →
      tail x p = true → tail y q = true)
    (correct : ∀ x, tail x (gate x) = true ↔ hit G x)
    (a b : Fin n) (edge : G.Adj a b)
    (essential : tail (mask {a,b}) false = false)
    (unique : ∀ u v, G.Adj u v → tail (mask {u,v}) false = false →
      (u = a ∧ v = b) ∨ (u = b ∧ v = a)) :
    (∀ x, (x a && x b) = true → gate x = true) ∧
    (∀ x, tail x (x a && x b) = true ↔ hit G x) := by
  have pair_on : gate (mask {a,b}) = true := by
    have yes := (correct (mask {a,b})).mpr
      ⟨a,b,edge,by simp [mask],by simp [mask]⟩
    cases h : gate (mask {a,b})
    · rw [h,essential] at yes
      contradiction
    · rfl
  have dominated : ∀ x, (x a && x b) = true → gate x = true := by
    intro x hx
    obtain ⟨ha,hb⟩ := Bool.and_eq_true_iff.mp hx
    apply gate_mono (mask {a,b}) x ?_ pair_on
    intro i hi
    simp only [mask, decide_eq_true_eq, Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl
    · exact ha
    · exact hb
  refine ⟨dominated,?_⟩
  intro x
  constructor
  · intro h
    exact (correct x).mp (tail_mono x x (x a && x b) (gate x)
      (fun _ h => h) (dominated x) h)
  · rintro ⟨u,v,uv,hu,hv⟩
    have sub : ∀ i, mask {u,v} i = true → x i = true := by
      intro i hi
      simp only [mask, decide_eq_true_eq, Finset.mem_insert, Finset.mem_singleton] at hi
      rcases hi with rfl | rfl
      · exact hu
      · exact hv
    cases survive : tail (mask {u,v}) false with
    | true =>
      exact tail_mono (mask {u,v}) x false (x a && x b) sub (by simp) survive
    | false =>
      have active : (x a && x b) = true := by
        rcases unique u v uv survive with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> simp [hu,hv]
      have yes := (correct (mask {u,v})).mpr
        ⟨u,v,uv,by simp [mask],by simp [mask]⟩
      exact tail_mono (mask {u,v}) x (gate (mask {u,v})) (x a && x b)
        sub (fun _ => active) yes

def patchCircuit (pre post : List Gate) (g : Gate) (out : ℕ) : Circuit :=
  ⟨pre ++ g :: post, out⟩

def gatePrefix {n : ℕ} (pre : List Gate) (g : Gate) (x : Fin n → Bool) : Bool :=
  g.op.eval (g.inputs.map fun i => (run pre (List.ofFn x)).getD i false)

def gateContext {n : ℕ} (pre post : List Gate) (out : ℕ)
    (x : Fin n → Bool) (p : Bool) : Bool :=
  (run post (run pre (List.ofFn x) ++ [p])).getD out false

lemma run_old_read (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (run gs w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    change (run gs (step w g)).getD i false = _
    rw [ih _ (by simp [step]; omega)]
    exact List.getD_append _ _ _ _ hi

lemma run_input {n : ℕ} (gs : List Gate) (x : Fin n → Bool) (i : Fin n) :
    (run gs (List.ofFn x)).getD i false = x i := by
  rw [run_old_read gs _ _ (by simp)]
  simp [List.getD_eq_getElem?_getD]

lemma gateContext_orig {n : ℕ} (pre post : List Gate) (g : Gate) (out : ℕ)
    (x : Fin n → Bool) :
    gateContext pre post out x (gatePrefix pre g x) =
      (patchCircuit pre post g out).eval (List.ofFn x) := by
  simp only [gateContext,gatePrefix,patchCircuit,Circuit.eval,Circuit.wires,
    run,List.foldl_append,List.foldl_cons]
  rfl

lemma gateContext_zero {n : ℕ} (pre post : List Gate) (out : ℕ)
    (x : Fin n → Bool) :
    gateContext pre post out x false =
      (patchCircuit pre post ⟨.or,[]⟩ out).eval (List.ofFn x) := by
  exact gateContext_orig pre post ⟨.or,[]⟩ out x

lemma gatePrefix_edge {n : ℕ} (pre : List Gate) (a b : Fin n) (x : Fin n → Bool) :
    gatePrefix pre ⟨.and,[a.val,b.val]⟩ x = (x a && x b) := by
  simp only [gatePrefix,GateOp.eval,List.map_cons,List.map_nil,List.all_cons,
    List.all_nil,id_eq,Bool.and_true]
  rw [run_input pre x a,run_input pre x b]

lemma gateContext_edge {n : ℕ} (pre post : List Gate) (out : ℕ) (a b : Fin n)
    (x : Fin n → Bool) :
    gateContext pre post out x (x a && x b) =
      (patchCircuit pre post ⟨.and,[a.val,b.val]⟩ out).eval (List.ofFn x) := by
  rw [←gatePrefix_edge pre a b x]
  exact gateContext_orig pre post ⟨.and,[a.val,b.val]⟩ out x

lemma gateContext_mono {n : ℕ} (pre post : List Gate) (out : ℕ)
    (hpre : ∀ g ∈ pre, g.op = GateOp.and ∨ g.op = GateOp.or)
    (hpost : ∀ g ∈ post, g.op = GateOp.and ∨ g.op = GateOp.or)
    (x y : Fin n → Bool) (p q : Bool)
    (hxy : ∀ i, x i = true → y i = true) (hpq : p = true → q = true) :
    gateContext pre post out x p = true → gateContext pre post out y q = true := by
  apply run_le post hpost (by simp [run_length]) _ out
  exact append_bit_le (by simp [run_length])
    (run_le pre hpre (by simp) (ofFn_le hxy)) hpq

lemma gatePrefix_mono {n : ℕ} (pre : List Gate) (g : Gate)
    (hpre : ∀ g ∈ pre, g.op = GateOp.and ∨ g.op = GateOp.or)
    (hg : g.op = GateOp.and ∨ g.op = GateOp.or)
    (x y : Fin n → Bool) (hxy : ∀ i, x i = true → y i = true) :
    gatePrefix pre g x = true → gatePrefix pre g y = true := by
  exact gate_eval_le g hg (run_le pre hpre (by simp) (ofFn_le hxy))

lemma patch_mono (pre post : List Gate) (g h : Gate) (out : ℕ)
    (hc : Monotone2 (patchCircuit pre post g out))
    (hh : (h.op = GateOp.and ∨ h.op = GateOp.or) ∧ h.inputs.length ≤ 2) :
    Monotone2 (patchCircuit pre post h out) := by
  intro q hq
  change q ∈ pre ++ h :: post at hq
  rcases List.mem_append.mp hq with hp | hpost
  · exact hc q (List.mem_append_left _ hp)
  · rcases List.mem_cons.mp hpost with rfl | ht
    · exact hh
    · exact hc q (List.mem_append_right _ (List.mem_cons_of_mem _ ht))

lemma single_edge_circuit_repair {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (pre post : List Gate) (g : Gate) (out : ℕ)
    (hc : Monotone2 (patchCircuit pre post g out))
    (correct : ∀ x : Fin n → Bool,
      (patchCircuit pre post g out).eval (List.ofFn x) = true ↔ hit G x)
    (a b : Fin n) (edge : G.Adj a b)
    (essential : (patchCircuit pre post ⟨.or,[]⟩ out).eval
      (List.ofFn (mask {a,b})) = false)
    (unique : ∀ u v, G.Adj u v →
      (patchCircuit pre post ⟨.or,[]⟩ out).eval (List.ofFn (mask {u,v})) = false →
      (u = a ∧ v = b) ∨ (u = b ∧ v = a)) :
    let C := patchCircuit pre post g out
    let D := patchCircuit pre post ⟨.and,[a.val,b.val]⟩ out
    Monotone2 D ∧ D.size = C.size ∧
    (∀ x : Fin n → Bool, D.eval (List.ofFn x) = true ↔ hit G x) ∧
    (∀ x : Fin n → Bool, WireLE (D.wires (List.ofFn x)) (C.wires (List.ofFn x))) := by
  dsimp only
  have hpre : ∀ q ∈ pre, q.op = GateOp.and ∨ q.op = GateOp.or := by
    intro q hq
    exact (hc q (List.mem_append_left _ hq)).1
  have hpost : ∀ q ∈ post, q.op = GateOp.and ∨ q.op = GateOp.or := by
    intro q hq
    exact (hc q (List.mem_append_right _ (List.mem_cons_of_mem _ hq))).1
  have hg : g.op = GateOp.and ∨ g.op = GateOp.or :=
    (hc g (List.mem_append_right _ List.mem_cons_self)).1
  obtain ⟨dom,works⟩ := single_critical_replacement G (gatePrefix pre g)
    (gateContext pre post out) (gatePrefix_mono pre g hpre hg)
    (gateContext_mono pre post out hpre hpost)
    (fun x => by simpa only [gateContext_orig] using correct x)
    a b edge (by simpa only [gateContext_zero] using essential)
    (fun u v huv hzero => unique u v huv (by simpa only [gateContext_zero] using hzero))
  refine ⟨patch_mono pre post g _ out hc ⟨Or.inl rfl,by simp⟩,?_,?_,?_⟩
  · simp [patchCircuit,Circuit.size]
  · intro x
    simpa only [gateContext_edge] using works x
  · intro x
    apply patch_le pre post g ⟨.and,[a.val,b.val]⟩ out (List.ofFn x) hpost
    change gatePrefix pre ⟨.and,[a.val,b.val]⟩ x = true → gatePrefix pre g x = true
    simpa only [gatePrefix_edge] using dom x

lemma patch_wire_value {n : ℕ} (pre post : List Gate) (g : Gate) (out : ℕ)
    (x : Fin n → Bool) :
    ((patchCircuit pre post g out).wires (List.ofFn x)).getD (n + pre.length) false =
      gatePrefix pre g x := by
  change (run (pre ++ g :: post) (List.ofFn x)).getD (n + pre.length) false = _
  simp only [run,List.foldl_append,List.foldl_cons]
  change (run post (run pre (List.ofFn x) ++ [gatePrefix pre g x])).getD
    (n + pre.length) false = _
  have hlen : (run pre (List.ofFn x)).length = n + pre.length := by simp [run_length]
  rw [run_old_read post _ _ (by simp [hlen])]
  rw [List.getD_append_right _ _ _ _ (by omega),hlen,Nat.sub_self]
  rfl

lemma repaired_gate_safe {n : ℕ} (G : SimpleGraph (Fin n))
    (pre post : List Gate) (out : ℕ) (a b : Fin n) (edge : G.Adj a b)
    (x : Fin n → Bool) :
    ((patchCircuit pre post ⟨.and,[a.val,b.val]⟩ out).wires
      (List.ofFn x)).getD (n + pre.length) false = true → hit G x := by
  rw [patch_wire_value,gatePrefix_edge]
  intro h
  obtain ⟨ha,hb⟩ := Bool.and_eq_true_iff.mp h
  exact ⟨a,b,edge,ha,hb⟩

lemma zero_edge_circuit_repair {n : ℕ} (G : SimpleGraph (Fin n))
    (pre post : List Gate) (g : Gate) (out : ℕ)
    (hc : Monotone2 (patchCircuit pre post g out))
    (correct : ∀ x : Fin n → Bool,
      (patchCircuit pre post g out).eval (List.ofFn x) = true ↔ hit G x)
    (survives : ∀ u v, G.Adj u v →
      (patchCircuit pre post ⟨.or,[]⟩ out).eval (List.ofFn (mask {u,v})) = true) :
    let C := patchCircuit pre post g out
    let D := patchCircuit pre post ⟨.or,[]⟩ out
    Monotone2 D ∧ D.size = C.size ∧
    (∀ x : Fin n → Bool, D.eval (List.ofFn x) = true ↔ hit G x) ∧
    (∀ x : Fin n → Bool, WireLE (D.wires (List.ofFn x)) (C.wires (List.ofFn x))) ∧
    (∀ x : Fin n → Bool, (D.wires (List.ofFn x)).getD (n + pre.length) false = false) := by
  dsimp only
  have hpre : ∀ q ∈ pre, q.op = GateOp.and ∨ q.op = GateOp.or := by
    intro q hq
    exact (hc q (List.mem_append_left _ hq)).1
  have hpost : ∀ q ∈ post, q.op = GateOp.and ∨ q.op = GateOp.or := by
    intro q hq
    exact (hc q (List.mem_append_right _ (List.mem_cons_of_mem _ hq))).1
  have works := zero_critical_replacement G (gatePrefix pre g) (gateContext pre post out)
    (gateContext_mono pre post out hpre hpost)
    (fun x => by simpa only [gateContext_orig] using correct x)
    (fun u v huv => by simpa only [gateContext_zero] using survives u v huv)
  refine ⟨patch_mono pre post g _ out hc ⟨Or.inr rfl,by simp⟩,?_,?_,?_,?_⟩
  · simp [patchCircuit,Circuit.size]
  · intro x
    simpa only [gateContext_zero] using works x
  · intro x
    apply patch_le pre post g ⟨.or,[]⟩ out (List.ofFn x) hpost
    simp [GateOp.eval]
  · intro x
    rw [patch_wire_value]
    rfl

lemma single_edge_circuit_repair_safe {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (pre post : List Gate) (g : Gate) (out : ℕ)
    (hc : Monotone2 (patchCircuit pre post g out))
    (correct : ∀ x : Fin n → Bool,
      (patchCircuit pre post g out).eval (List.ofFn x) = true ↔ hit G x)
    (a b : Fin n) (edge : G.Adj a b)
    (essential : (patchCircuit pre post ⟨.or,[]⟩ out).eval
      (List.ofFn (mask {a,b})) = false)
    (unique : ∀ u v, G.Adj u v →
      (patchCircuit pre post ⟨.or,[]⟩ out).eval (List.ofFn (mask {u,v})) = false →
      (u = a ∧ v = b) ∨ (u = b ∧ v = a)) :
    let C := patchCircuit pre post g out
    let D := patchCircuit pre post ⟨.and,[a.val,b.val]⟩ out
    Monotone2 D ∧ D.size = C.size ∧
    (∀ x : Fin n → Bool, D.eval (List.ofFn x) = true ↔ hit G x) ∧
    (∀ x : Fin n → Bool, WireLE (D.wires (List.ofFn x)) (C.wires (List.ofFn x))) ∧
    (∀ x : Fin n → Bool, (D.wires (List.ofFn x)).getD (n + pre.length) false = true → hit G x) := by
  obtain ⟨hm,hs,he,hl⟩ := single_edge_circuit_repair G pre post g out hc correct a b edge essential unique
  exact ⟨hm,hs,he,hl,repaired_gate_safe G pre post out a b edge⟩

lemma critical_gate_repair {n : ℕ} (G : SimpleGraph (Fin n))
    (pre post : List Gate) (g h : Gate) (out : ℕ)
    (hc : Monotone2 (patchCircuit pre post g out))
    (hh : (h.op = GateOp.and ∨ h.op = GateOp.or) ∧ h.inputs.length ≤ 2)
    (correct : ∀ x : Fin n → Bool,
      (patchCircuit pre post g out).eval (List.ofFn x) = true ↔ hit G x)
    (dominated : ∀ x : Fin n → Bool, gatePrefix pre h x = true → gatePrefix pre g x = true)
    (critical : ∀ u v, G.Adj u v →
      (patchCircuit pre post ⟨.or,[]⟩ out).eval (List.ofFn (mask {u,v})) = false →
        gatePrefix pre h (mask {u,v}) = true) :
    let C := patchCircuit pre post g out
    let D := patchCircuit pre post h out
    Monotone2 D ∧ D.size = C.size ∧
    (∀ x : Fin n → Bool, D.eval (List.ofFn x) = true ↔ hit G x) ∧
    (∀ x : Fin n → Bool, WireLE (D.wires (List.ofFn x)) (C.wires (List.ofFn x))) := by
  dsimp only
  have hD := patch_mono pre post g h out hc hh
  have hpost : ∀ q ∈ post, q.op = GateOp.and ∨ q.op = GateOp.or := by
    intro q hq
    exact (hc q (List.mem_append_right _ (List.mem_cons_of_mem _ hq))).1
  have pointwise (x : Fin n → Bool) :
      WireLE ((patchCircuit pre post h out).wires (List.ofFn x))
        ((patchCircuit pre post g out).wires (List.ofFn x)) :=
    patch_le pre post g h out (List.ofFn x) hpost (dominated x)
  have edges (u v : Fin n) (huv : G.Adj u v) :
      (patchCircuit pre post h out).eval (List.ofFn (mask {u,v})) = true := by
    cases hz : (patchCircuit pre post ⟨.or,[]⟩ out).eval (List.ofFn (mask {u,v})) with
    | false =>
      have hon := critical u v huv hz
      have gon := dominated _ hon
      have same := patch_agree pre post g h out (List.ofFn (mask {u,v})) (hon.trans gon.symm)
      change (patchCircuit pre post h out).wires (List.ofFn (mask {u,v})) =
        (patchCircuit pre post g out).wires (List.ofFn (mask {u,v})) at same
      change ((patchCircuit pre post h out).wires (List.ofFn (mask {u,v}))).getD out false = true
      rw [same]
      exact (correct _).mpr ⟨u,v,huv,by simp [mask],by simp [mask]⟩
    | true =>
      have low : WireLE
          ((patchCircuit pre post ⟨.or,[]⟩ out).wires (List.ofFn (mask {u,v})))
          ((patchCircuit pre post h out).wires (List.ofFn (mask {u,v}))) :=
        patch_le pre post h ⟨.or,[]⟩ out (List.ofFn (mask {u,v})) hpost (by simp [GateOp.eval])
      exact low out hz
  refine ⟨hD,by simp [patchCircuit,Circuit.size],?_,pointwise⟩
  intro x
  constructor
  · intro hx
    exact (correct x).mp (pointwise x out hx)
  · rintro ⟨u,v,huv,hu,hv⟩
    apply wires_mono hD (x := mask {u,v}) (y := x) ?_ out (edges u v huv)
    intro i hi
    simp only [mask,decide_eq_true_eq,Finset.mem_insert,Finset.mem_singleton] at hi
    rcases hi with rfl | rfl
    · exact hu
    · exact hv

lemma critical_gate_repair_safe {n : ℕ} (G : SimpleGraph (Fin n))
    (pre post : List Gate) (g h : Gate) (out : ℕ)
    (hc : Monotone2 (patchCircuit pre post g out))
    (hh : (h.op = GateOp.and ∨ h.op = GateOp.or) ∧ h.inputs.length ≤ 2)
    (correct : ∀ x : Fin n → Bool,
      (patchCircuit pre post g out).eval (List.ofFn x) = true ↔ hit G x)
    (dominated : ∀ x : Fin n → Bool, gatePrefix pre h x = true → gatePrefix pre g x = true)
    (critical : ∀ u v, G.Adj u v →
      (patchCircuit pre post ⟨.or,[]⟩ out).eval (List.ofFn (mask {u,v})) = false →
        gatePrefix pre h (mask {u,v}) = true)
    (safe : ∀ x : Fin n → Bool, gatePrefix pre h x = true → hit G x) :
    let C := patchCircuit pre post g out
    let D := patchCircuit pre post h out
    Monotone2 D ∧ D.size = C.size ∧
    (∀ x : Fin n → Bool, D.eval (List.ofFn x) = true ↔ hit G x) ∧
    (∀ x : Fin n → Bool, WireLE (D.wires (List.ofFn x)) (C.wires (List.ofFn x))) ∧
    (∀ x : Fin n → Bool, (D.wires (List.ofFn x)).getD (n + pre.length) false = true → hit G x) := by
  obtain ⟨hm,hs,he,hl⟩ := critical_gate_repair G pre post g h out hc hh correct dominated critical
  refine ⟨hm,hs,he,hl,?_⟩
  intro x
  simpa only [patch_wire_value] using safe x


lemma patch_get_ne (pre post : List Gate) (g h : Gate) (out k : ℕ)
    (hk : k ≠ pre.length) :
    (patchCircuit pre post h out).gates[k]? =
      (patchCircuit pre post g out).gates[k]? := by
  change (pre ++ h :: post)[k]? = (pre ++ g :: post)[k]?
  by_cases hlt : k < pre.length
  · rw [List.getElem?_append_left hlt, List.getElem?_append_left hlt]
  · have hle : pre.length ≤ k := by omega
    rw [List.getElem?_append_right hle, List.getElem?_append_right hle]
    obtain ⟨j, hj⟩ : ∃ j, k - pre.length = j + 1 := ⟨k - pre.length - 1, by omega⟩
    rw [hj]
    rfl

lemma patch_get_self (pre post : List Gate) (g : Gate) (out : ℕ) :
    (patchCircuit pre post g out).gates[pre.length]? = some g := by
  change (pre ++ g :: post)[pre.length]? = some g
  simp

lemma patch_preserves_safe {n : ℕ} (G : SimpleGraph (Fin n))
    (pre post : List Gate) (g h : Gate) (out : ℕ)
    (hdecrease : ∀ x : Fin n → Bool,
      WireLE ((patchCircuit pre post h out).wires (List.ofFn x))
        ((patchCircuit pre post g out).wires (List.ofFn x)))
    (hsafe : ∀ x : Fin n → Bool,
      ((patchCircuit pre post h out).wires (List.ofFn x)).getD (n + pre.length) false = true →
        hit G x)
    (k : ℕ)
    (hold : ∀ q : Gate, (patchCircuit pre post g out).gates[k]? = some q →
      q.op = GateOp.and → ∀ x : Fin n → Bool,
        ((patchCircuit pre post g out).wires (List.ofFn x)).getD (n + k) false = true → hit G x) :
    ∀ q : Gate, (patchCircuit pre post h out).gates[k]? = some q →
      q.op = GateOp.and → ∀ x : Fin n → Bool,
        ((patchCircuit pre post h out).wires (List.ofFn x)).getD (n + k) false = true → hit G x := by
  intro q hq hop x hx
  by_cases hk : k = pre.length
  · subst k
    exact hsafe x hx
  · exact hold q ((patch_get_ne pre post g h out k hk).symm.trans hq) hop x
      (hdecrease x (n + k) hx)


namespace ContextRectangle

open PEqualNP.EdgeOwnership

def PositiveMono {n : ℕ} (f : (Fin n → Bool) → Bool) : Prop :=
  ∀ x y, (∀ i, x i = true → y i = true) → f x = true → f y = true

lemma pair_true_iff {n : ℕ} {a b i : Fin n} :
    pairInput a b i = true ↔ i = a ∨ i = b := by
  simp [pairInput]

lemma cross_adj {n : ℕ} (G : SimpleGraph (Fin n))
    (p q : (Fin n → Bool) → Bool) (hp : PositiveMono p) (hq : PositiveMono q)
    (hsafe : ∀ x, p x = true → q x = true →
      ∃ u v, G.Adj u v ∧ x u = true ∧ x v = true)
    {a b : Fin n} (ha : p (pairInput a a) = true)
    (hb : q (pairInput b b) = true) : G.Adj a b := by
  have hpa : p (pairInput a b) = true := hp _ _ (by
    intro i hi
    have hia : i = a := by simpa [pairInput] using hi
    subst i
    simp [pairInput]) ha
  have hqb : q (pairInput a b) = true := hq _ _ (by
    intro i hi
    have hib : i = b := by simpa [pairInput] using hi
    subst i
    simp [pairInput]) hb
  obtain ⟨u, v, huv, hu, hv⟩ := hsafe _ hpa hqb
  rcases pair_true_iff.mp hu with rfl | rfl <;>
    rcases pair_true_iff.mp hv with rfl | rfl
  · exact False.elim (G.irrefl huv)
  · exact huv
  · exact huv.symm
  · exact False.elim (G.irrefl huv)

lemma cross_has_singleton_side {n : ℕ} (G : SimpleGraph (Fin n))
    (hc4 : ∀ a b c d, G.Adj a b → G.Adj b c → G.Adj c d → G.Adj d a →
      a = c ∨ b = d)
    (S T : Fin n → Prop) (hcross : ∀ a b, S a → T b → G.Adj a b) :
    (∀ a b, S a → S b → a = b) ∨ (∀ a b, T a → T b → a = b) := by
  classical
  by_cases hs : ∀ a b, S a → S b → a = b
  · exact Or.inl hs
  · right
    push Not at hs
    obtain ⟨a, c, ha, hc, hac⟩ := hs
    intro b d hb hd
    rcases hc4 a b c d (hcross _ _ ha hb) (hcross _ _ hc hb).symm
      (hcross _ _ hc hd) (hcross _ _ ha hd).symm with heq | heq
    · exact False.elim (hac heq)
    · exact heq

lemma cross_side_independent {n : ℕ} (G : SimpleGraph (Fin n))
    (htri : ∀ a b c, G.Adj a b → G.Adj b c → ¬G.Adj c a)
    (S T : Fin n → Prop) (hcross : ∀ a b, S a → T b → G.Adj a b)
    (ht : ∃ t, T t) : ∀ a b, S a → S b → ¬ G.Adj a b := by
  obtain ⟨t, ht⟩ := ht
  intro a b ha hb hab
  exact htri a b t hab (hcross _ _ hb ht) (hcross _ _ ha ht).symm

lemma singleton_support_star {n : ℕ} (G : SimpleGraph (Fin n))
    (hc4 : ∀ a b c d, G.Adj a b → G.Adj b c → G.Adj c d → G.Adj d a →
      a = c ∨ b = d)
    (p q : (Fin n → Bool) → Bool) (hp : PositiveMono p) (hq : PositiveMono q)
    (hsafe : ∀ x, p x = true → q x = true →
      ∃ u v, G.Adj u v ∧ x u = true ∧ x v = true) :
    (∀ a b, p (pairInput a a) = true → p (pairInput b b) = true → a = b) ∨
    (∀ a b, q (pairInput a a) = true → q (pairInput b b) = true → a = b) := by
  exact cross_has_singleton_side G hc4 _ _ (fun a b ha hb => cross_adj G p q hp hq hsafe ha hb)

end ContextRectangle

lemma circuit_context_rectangle {n : ℕ} (G : SimpleGraph (Fin n))
    (hc4 : ∀ a b c d, G.Adj a b → G.Adj b c → G.Adj c d → G.Adj d a →
      a = c ∨ b = d)
    (pre post : List Gate) (g : Gate) (out : ℕ)
    (hc : Monotone2 (patchCircuit pre post g out))
    (correct : ∀ x : Fin n → Bool,
      (patchCircuit pre post g out).eval (List.ofFn x) = true ↔ hit G x) :
    (∀ a b : Fin n,
      gatePrefix pre g (PEqualNP.EdgeOwnership.pairInput a a) = true →
      gatePrefix pre g (PEqualNP.EdgeOwnership.pairInput b b) = true → a = b) ∨
    (∀ a b : Fin n,
      gateContext pre post out (PEqualNP.EdgeOwnership.pairInput a a) true = true →
      gateContext pre post out (PEqualNP.EdgeOwnership.pairInput b b) true = true → a = b) := by
  have hpre : ∀ q ∈ pre, q.op = GateOp.and ∨ q.op = GateOp.or := by
    intro q hq
    exact (hc q (List.mem_append_left _ hq)).1
  have hpost : ∀ q ∈ post, q.op = GateOp.and ∨ q.op = GateOp.or := by
    intro q hq
    exact (hc q (List.mem_append_right _ (List.mem_cons_of_mem _ hq))).1
  have hg : g.op = GateOp.and ∨ g.op = GateOp.or :=
    (hc g (List.mem_append_right _ List.mem_cons_self)).1
  apply ContextRectangle.singleton_support_star G hc4 (gatePrefix pre g)
    (fun x => gateContext pre post out x true)
    (gatePrefix_mono pre g hpre hg)
    (fun x y hxy => gateContext_mono pre post out hpre hpost x y true true hxy (fun h => h))
  intro x hp hq
  apply (correct x).mp
  rw [← gateContext_orig pre post g out x, hp]
  exact hq


end Repair

namespace Construction

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge



namespace Builder

-- Circuit builder adapted from L_meta_1003.lean (H926, H926.EdgeUpper), strengthened to carry
-- monotonicity (AND/OR, fan-in two) and an upper bound on every AND gate's wire.

open PEqualNP PEqualNP.MetaComplexity PEqualNP.CircuitLowerBounds

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

lemma wires_eq (C : Circuit) (x : List Bool) : C.wires x = wiresFrom C.gates x := rfl

lemma wiresFrom_append (gs gs' : List Gate) (w : List Bool) :
    wiresFrom (gs ++ gs') w = wiresFrom gs' (wiresFrom gs w) := by
  simp [wiresFrom, List.foldl_append]

lemma wiresFrom_prefix (gs : List Gate) : ∀ w : List Bool,
    ∃ t : List Bool, wiresFrom gs w = w ++ t ∧ t.length = gs.length := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp [wiresFrom], rfl⟩
  | cons g gs ih =>
    intro w
    obtain ⟨t, ht, hl⟩ := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: t, ?_, by simp [hl]⟩
    have : wiresFrom (g :: gs) w
        = wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl
    rw [this, ht]; simp

lemma length_wiresFrom (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := wiresFrom_prefix gs w
  rw [ht]; simp [hl]

lemma getD_wiresFrom (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := wiresFrom_prefix gs w
  rw [ht, List.getD_append _ _ _ _ h]

lemma getD_snoc_ne {α : Type} (L : List α) (S d : α) (j : ℕ) (h : j ≠ L.length) :
    (L ++ [S]).getD j d = L.getD j d := by
  by_cases hj : j < L.length
  · exact List.getD_append _ _ _ _ hj
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

lemma getD_snoc_eq {α : Type} (L : List α) (S d : α) : (L ++ [S]).getD L.length d = S := by
  simp

lemma getD_ofFn {n : ℕ} (x : Fin n → Bool) (i : Fin n) :
    (List.ofFn x).getD (i : ℕ) false = x i := by simp

def OkM (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2

def Bld (n : ℕ) (P : (Fin n → Bool) → Prop) (F : (Fin n → Bool) → Bool) (s : ℕ) : Prop :=
  ∀ m, n ≤ m → ∃ (gs : List Gate) (out : ℕ), (∀ g ∈ gs, OkM g) ∧ gs.length ≤ s ∧
    out < m + gs.length ∧ (∀ w : List Bool, w.length = m →
      (wiresFrom gs w).getD out false = F (fun i => w.getD i false)) ∧
    ∀ (j : ℕ) (g : Gate), gs[j]? = some g → g.op = GateOp.and → ∀ w : List Bool, w.length = m →
      (wiresFrom gs w).getD (m + j) false = true → P (fun i => w.getD i false)

lemma bld_mono {n : ℕ} {P} {F : (Fin n → Bool) → Bool} {s s' : ℕ} (h : Bld n P F s)
    (hs : s ≤ s') : Bld n P F s' := by
  intro m hm
  obtain ⟨gs, out, ok, len, ho, ev, ha⟩ := h m hm
  exact ⟨gs, out, ok, le_trans len hs, ho, ev, ha⟩

lemma bld_congr {n : ℕ} {P} {F H : (Fin n → Bool) → Bool} {s : ℕ} (h : Bld n P F s)
    (e : ∀ x, F x = H x) : Bld n P H s := by
  intro m hm
  obtain ⟨gs, out, ok, len, ho, ev, ha⟩ := h m hm
  exact ⟨gs, out, ok, len, ho, fun w hw => by rw [ev w hw, e], ha⟩

lemma bld_var {n : ℕ} {P} (i : Fin n) : Bld n P (fun x => x i) 0 := by
  intro m hm
  refine ⟨[], i, by simp, le_rfl, by simp; omega, ?_, ?_⟩
  · intro w _
    simp [wiresFrom]
  · intro j g hj
    simp at hj

lemma bld_bin {n : ℕ} {P} (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or)
    (c : Bool → Bool → Bool) (hc : ∀ a b, op.eval [a, b] = c a b)
    {F H : (Fin n → Bool) → Bool} {s1 s2 : ℕ} (h1 : Bld n P F s1) (h2 : Bld n P H s2)
    (hA : op = GateOp.and → ∀ x, c (F x) (H x) = true → P x) :
    Bld n P (fun x => c (F x) (H x)) (s1 + s2 + 1) := by
  intro m hm
  obtain ⟨gs1, o1, ok1, len1, ho1, ev1, ha1⟩ := h1 m hm
  obtain ⟨gs2, o2, ok2, len2, ho2, ev2, ha2⟩ := h2 (m + gs1.length) (by omega)
  have main : ∀ w : List Bool, w.length = m →
      (wiresFrom gs2 (wiresFrom gs1 w)).length = m + gs1.length + gs2.length ∧
      (wiresFrom (gs1 ++ gs2 ++ [⟨op, [o1, o2]⟩]) w)
        = wiresFrom gs2 (wiresFrom gs1 w) ++
          [c (F (fun i : Fin n => w.getD i false)) (H (fun i : Fin n => w.getD i false))] ∧
      (fun i : Fin n => (wiresFrom gs1 w).getD i false) = (fun i : Fin n => w.getD i false) := by
    intro w hw
    rw [wiresFrom_append, wiresFrom_append]
    set v := wiresFrom gs1 w with hv
    have lv : v.length = m + gs1.length := by rw [hv, length_wiresFrom, hw]
    set u := wiresFrom gs2 v with hu
    have lu : u.length = m + gs1.length + gs2.length := by rw [hu, length_wiresFrom, lv]
    have hvw : (fun i : Fin n => v.getD i false) = (fun i : Fin n => w.getD i false) := by
      funext i
      rw [hv, getD_wiresFrom _ _ _ (by have := i.2; omega)]
    refine ⟨lu, ?_, hvw⟩
    have step : wiresFrom [⟨op, [o1, o2]⟩] u
        = u ++ [op.eval ([o1, o2].map fun i => u.getD i false)] := rfl
    rw [step]
    simp only [List.map_cons, List.map_nil, hc]
    have e1 : u.getD o1 false = F (fun i => w.getD i false) := by
      rw [hu, getD_wiresFrom _ _ _ (by omega), hv, ev1 w hw]
    have e2 : u.getD o2 false = H (fun i => w.getD i false) := by
      rw [hu, ev2 v lv, hvw]
    rw [e1, e2]
  refine ⟨gs1 ++ gs2 ++ [⟨op, [o1, o2]⟩], m + gs1.length + gs2.length, ?_, ?_, ?_, ?_, ?_⟩
  · intro g hg
    simp only [List.mem_append, List.mem_singleton] at hg
    rcases hg with (hg | hg) | hg
    · exact ok1 g hg
    · exact ok2 g hg
    · subst hg; rcases hop with h | h <;> simp [OkM, h]
  · simp; omega
  · simp; omega
  · intro w hw
    obtain ⟨lu, hm2, _⟩ := main w hw
    rw [hm2, ← lu, getD_snoc_eq]
  · intro j g hj hop' w hw hval
    obtain ⟨lu, hm2, hvw⟩ := main w hw
    rw [hm2] at hval
    rcases lt_or_ge j gs1.length with hj1 | hj1
    · have hg : gs1[j]? = some g := by
        rw [List.getElem?_append_left (by simp; omega), List.getElem?_append_left hj1] at hj
        exact hj
      apply ha1 j g hg hop' w hw
      rw [getD_snoc_ne _ _ _ _ (by omega), getD_wiresFrom _ _ _ (by
        rw [length_wiresFrom, hw]; omega)] at hval
      exact hval
    · rcases lt_or_ge j (gs1.length + gs2.length) with hj2 | hj2
      · obtain ⟨j', rfl⟩ : ∃ j', j = gs1.length + j' := ⟨j - gs1.length, by omega⟩
        have hg : gs2[j']? = some g := by
          rw [List.getElem?_append_left (by simp; omega),
            List.getElem?_append_right (by omega)] at hj
          simpa using hj
        have lv : (wiresFrom gs1 w).length = m + gs1.length := by rw [length_wiresFrom, hw]
        have := ha2 j' g hg hop' (wiresFrom gs1 w) lv
        rw [hvw] at this
        apply this
        rw [getD_snoc_ne _ _ _ _ (by omega)] at hval
        rw [← add_assoc] at hval
        exact hval
      · have hjeq : j = gs1.length + gs2.length := by
          by_contra hne
          have : (gs1 ++ gs2 ++ [(⟨op, [o1, o2]⟩ : Gate)])[j]? = none :=
            List.getElem?_eq_none (by simp; omega)
          rw [this] at hj
          simp at hj
        subst hjeq
        have hg : g = ⟨op, [o1, o2]⟩ := by
          rw [List.getElem?_append_right (by simp)] at hj
          simp at hj
          exact hj.symm
        subst hg
        rw [show m + (gs1.length + gs2.length) = (wiresFrom gs2 (wiresFrom gs1 w)).length by
          omega, getD_snoc_eq] at hval
        exact hA hop' _ hval

lemma bld_or {n : ℕ} {P} {F H : (Fin n → Bool) → Bool} {s1 s2 : ℕ} (h1 : Bld n P F s1)
    (h2 : Bld n P H s2) : Bld n P (fun x => F x || H x) (s1 + s2 + 1) :=
  bld_bin GateOp.or (Or.inr rfl) (· || ·) (by intro a b; simp [GateOp.eval]) h1 h2
    (by intro h; cases h)

lemma bld_and {n : ℕ} {P} {F H : (Fin n → Bool) → Bool} {s1 s2 : ℕ} (h1 : Bld n P F s1)
    (h2 : Bld n P H s2) (hP : ∀ x, F x = true → H x = true → P x) :
    Bld n P (fun x => F x && H x) (s1 + s2 + 1) :=
  bld_bin GateOp.and (Or.inl rfl) (· && ·) (by intro a b; simp [GateOp.eval]) h1 h2
    (by
      intro _ x hx
      simp only [Bool.and_eq_true] at hx
      exact hP x hx.1 hx.2)

lemma bld_anyList {n : ℕ} {P} (vs : List (Fin n)) : ∀ v : Fin n,
    Bld n P (fun x => (v :: vs).any fun j => x j) vs.length := by
  induction vs with
  | nil => intro v; exact bld_congr (bld_var v) (by intro x; simp)
  | cons w ws ih =>
    intro v
    have := bld_or (bld_var (P := P) v) (ih w)
    refine bld_congr (bld_mono this (by simp)) ?_
    intro x
    simp

lemma bld_anyFinset {n : ℕ} {P} (S : Finset (Fin n)) (hS : S.Nonempty) :
    Bld n P (fun x => decide (∃ v ∈ S, x v = true)) (S.card - 1) := by
  obtain ⟨v, vs, hl⟩ : ∃ v vs, S.toList = v :: vs := by
    cases h : S.toList with
    | nil => simp at h; exact absurd h hS.ne_empty
    | cons v vs => exact ⟨v, vs, rfl⟩
  have hc : S.card = vs.length + 1 := by rw [← Finset.length_toList, hl]; rfl
  refine bld_congr (bld_mono (bld_anyList vs v) (by omega)) ?_
  intro x
  rw [Bool.eq_iff_iff, decide_eq_true_iff, ← hl, List.any_eq_true]
  simp

open Classical in
lemma bld_edges (n : ℕ) (P : (Fin n → Bool) → Prop) (T : Finset (Fin n)) :
    ∀ E : Finset (Sym2 (Fin n)), E.Nonempty →
    (∀ e ∈ E, ∃ t ∈ T, t ∈ e) → (∀ x, (∃ e ∈ E, ∀ v ∈ e, x v = true) → P x) →
    Bld n P (fun x => decide (∃ e ∈ E, ∀ v ∈ e, x v = true)) (E.card + T.card - 1) := by
  induction T using Finset.induction_on with
  | empty =>
    intro E hE hc _
    obtain ⟨e, he⟩ := hE
    obtain ⟨t, ht, _⟩ := hc e he
    simp at ht
  | @insert t T0 htT ih =>
    intro E hE hc hPE
    set E1 := E.filter (fun e => t ∈ e) with hE1
    set E2 := E.filter (fun e => t ∉ e) with hE2
    have hsplit : E1.card + E2.card = E.card := Finset.card_filter_add_card_filter_not _
    have hcard : (insert t T0).card = T0.card + 1 := Finset.card_insert_of_notMem htT
    have c2 : ∀ e ∈ E2, ∃ t' ∈ T0, t' ∈ e := by
      intro e he
      rw [hE2, Finset.mem_filter] at he
      obtain ⟨t', ht', hte⟩ := hc e he.1
      rcases Finset.mem_insert.1 ht' with h | h
      · subst h; exact absurd hte he.2
      · exact ⟨t', h, hte⟩
    have p2 : ∀ x, (∃ e ∈ E2, ∀ v ∈ e, x v = true) → P x := by
      rintro x ⟨e, he, h⟩
      exact hPE x ⟨e, (Finset.mem_filter.1 he).1, h⟩
    set S := Finset.univ.filter (fun v : Fin n => s(t, v) ∈ E1) with hS
    have star : E1.Nonempty → Bld n P (fun x => decide (∃ e ∈ E1, ∀ v ∈ e, x v = true))
        E1.card := by
      intro h1
      have hSc : S.card ≤ E1.card := by
        refine Finset.card_le_card_of_injOn (fun v => s(t, v)) ?_ ?_
        · intro v hv
          simp only [hS, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hv
          exact hv
        · intro a _ b _ hab
          exact Sym2.congr_right.1 hab
      have hSne : S.Nonempty := by
        obtain ⟨e, he⟩ := h1
        have he' := he
        rw [hE1, Finset.mem_filter] at he'
        obtain ⟨b, hb⟩ := Sym2.mem_iff_exists.1 he'.2
        exact ⟨b, by simp [hS, ← hb, he]⟩
      have := bld_and (bld_var (P := P) t) (bld_anyFinset S hSne) (by
        intro x ht hv
        rw [decide_eq_true_iff] at hv
        obtain ⟨v, hv, hxv⟩ := hv
        refine hPE x ⟨s(t, v), (Finset.mem_filter.1 (Finset.mem_filter.1 hv).2).1, ?_⟩
        intro u hu
        rcases Sym2.mem_iff.1 hu with rfl | rfl <;> assumption)
      have hpos := hSne.card_pos
      refine bld_congr (bld_mono this (by omega)) ?_
      intro x
      rw [Bool.eq_iff_iff, Bool.and_eq_true, decide_eq_true_iff, decide_eq_true_iff]
      constructor
      · rintro ⟨ht, v, hv, hxv⟩
        refine ⟨s(t, v), (Finset.mem_filter.1 hv).2, ?_⟩
        intro u hu
        rcases Sym2.mem_iff.1 hu with rfl | rfl <;> assumption
      · rintro ⟨e, he, hall⟩
        have he' := he
        rw [hE1, Finset.mem_filter] at he'
        obtain ⟨b, hb⟩ := Sym2.mem_iff_exists.1 he'.2
        subst hb
        exact ⟨hall t (Sym2.mem_mk_left _ _), b, by simp [hS, he],
          hall b (Sym2.mem_mk_right _ _)⟩
    have key : ∀ x : Fin n → Bool, decide (∃ e ∈ E, ∀ v ∈ e, x v = true)
        = (decide (∃ e ∈ E1, ∀ v ∈ e, x v = true) || decide (∃ e ∈ E2, ∀ v ∈ e, x v = true)) := by
      intro x
      rw [Bool.eq_iff_iff]
      simp only [Bool.or_eq_true, decide_eq_true_iff, hE1, hE2, Finset.mem_filter]
      constructor
      · rintro ⟨e, he, h⟩
        by_cases hte : t ∈ e
        · exact Or.inl ⟨e, ⟨he, hte⟩, h⟩
        · exact Or.inr ⟨e, ⟨he, hte⟩, h⟩
      · rintro (⟨e, ⟨he, _⟩, h⟩ | ⟨e, ⟨he, _⟩, h⟩) <;> exact ⟨e, he, h⟩
    rw [hcard]
    by_cases h1 : E1.Nonempty
    · by_cases h2 : E2.Nonempty
      · have := bld_or (star h1) (ih E2 h2 c2 p2)
        have hp := h2.card_pos
        refine bld_congr (bld_mono this (by omega)) ?_
        intro x
        rw [key]
      · rw [Finset.not_nonempty_iff_eq_empty] at h2
        refine bld_congr (bld_mono (star h1) (by omega)) ?_
        intro x
        rw [key, h2]
        simp
    · rw [Finset.not_nonempty_iff_eq_empty] at h1
      have h2 : E2.Nonempty := by
        by_contra h2
        rw [Finset.not_nonempty_iff_eq_empty] at h2
        have := hE.card_pos
        rw [h1, h2] at hsplit
        simp at hsplit
        omega
      refine bld_congr (bld_mono (ih E2 h2 c2 p2) (by omega)) ?_
      intro x
      rw [key, h1]
      simp

lemma main (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (T : Finset (Fin n))
    (hc : ∀ u v, G.Adj u v → u ∈ T ∨ v ∈ T) :
    ∃ C : Circuit, Monotone2 C ∧
      (∀ x : Fin n → Bool, C.eval (List.ofFn x)
        = decide (∃ u v, G.Adj u v ∧ x u = true ∧ x v = true)) ∧
      C.size ≤ G.edgeFinset.card + T.card - 1 ∧
      ∀ (j : ℕ) (g : Gate), C.gates[j]? = some g → g.op = GateOp.and → ∀ x : Fin n → Bool,
        (C.wires (List.ofFn x)).getD (n + j) false = true →
          ∃ u v, G.Adj u v ∧ x u = true ∧ x v = true := by
  by_cases hE : ∃ i j : Fin n, G.Adj i j
  · obtain ⟨i0, j0, h0⟩ := hE
    have hne : G.edgeFinset.Nonempty := ⟨s(i0, j0), by simpa using h0⟩
    have cov : ∀ e ∈ G.edgeFinset, ∃ t ∈ T, t ∈ e := by
      intro e
      refine Sym2.ind (fun a b => ?_) e
      intro he
      rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at he
      rcases hc a b he with h | h
      · exact ⟨a, h, Sym2.mem_mk_left _ _⟩
      · exact ⟨b, h, Sym2.mem_mk_right _ _⟩
    have conv : ∀ x : Fin n → Bool, (∃ e ∈ G.edgeFinset, ∀ v ∈ e, x v = true) ↔
        (∃ i j : Fin n, G.Adj i j ∧ x i = true ∧ x j = true) := by
      intro x
      constructor
      · rintro ⟨e, he, h⟩
        revert he h
        refine Sym2.ind (fun a b => ?_) e
        intro he h
        rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at he
        exact ⟨a, b, he, h a (Sym2.mem_mk_left _ _), h b (Sym2.mem_mk_right _ _)⟩
      · rintro ⟨i, j, hij, hi, hj⟩
        refine ⟨s(i, j), by simpa using hij, ?_⟩
        intro v hv
        rcases Sym2.mem_iff.1 hv with rfl | rfl <;> assumption
    have hb := bld_edges n (fun x => ∃ i j : Fin n, G.Adj i j ∧ x i = true ∧ x j = true) T
      G.edgeFinset hne cov (fun x h => (conv x).1 h)
    obtain ⟨gs, out, ok, len, _, ev, ha⟩ := hb n le_rfl
    have hx : ∀ x : Fin n → Bool, (fun i : Fin n => (List.ofFn x).getD i false) = x := by
      intro x; funext i; exact getD_ofFn x i
    refine ⟨⟨gs, out⟩, ok, ?_, len, ?_⟩
    · intro x
      have e := ev (List.ofFn x) (by simp)
      rw [hx] at e
      simp only [Circuit.eval, wires_eq, e]
      exact decide_eq_decide.2 (conv x)
    · intro j g hj hop x hv
      have := ha j g hj hop (List.ofFn x) (by simp) hv
      rw [hx] at this
      exact this
  · refine ⟨⟨[], n⟩, ?_, ?_, ?_, ?_⟩
    · intro g hg; simp at hg
    · intro x
      have : ¬ ∃ u v, G.Adj u v ∧ x u = true ∧ x v = true := by
        rintro ⟨u, v, h, _⟩; exact hE ⟨u, v, h⟩
      simp only [Circuit.eval, Circuit.wires, List.foldl_nil, this, decide_false]
      exact List.getD_eq_default _ _ (by simp)
    · simp [Circuit.size]
    · intro j g hj; simp at hj


end Builder

namespace Selection

lemma exists_minimum_for_property (P : Circuit → Prop) (h : ∃ C, P C) :
    ∃ C, P C ∧ ∀ D, P D → C.size ≤ D.size := by
  classical
  have hs : ∃ s : ℕ, ∃ C, P C ∧ C.size = s := by
    obtain ⟨C, hC⟩ := h
    exact ⟨C.size, C, hC, rfl⟩
  obtain ⟨C, hC, hsize⟩ := Nat.find_spec hs
  refine ⟨C, hC, ?_⟩
  intro D hD
  rw [hsize]
  exact Nat.find_min' hs ⟨D, hD, rfl⟩

lemma exists_minimum_monotone {n : ℕ} (f : (Fin n → Bool) → Bool)
    (h : ∃ C, Monotone2 C ∧ ∀ x, C.eval (List.ofFn x) = f x) :
    ∃ C, Monotone2 C ∧ (∀ x, C.eval (List.ofFn x) = f x) ∧
      ∀ D, Monotone2 D → (∀ x, D.eval (List.ofFn x) = f x) → C.size ≤ D.size := by
  obtain ⟨C, hC, hmin⟩ := exists_minimum_for_property _ h
  exact ⟨C, hC.1, hC.2, fun D hD hDf => hmin D ⟨hD, hDf⟩⟩

lemma exists_minimum_monotone_with_property {n : ℕ} (f : (Fin n → Bool) → Bool)
    (P : Circuit → Prop)
    (h : ∃ C, Monotone2 C ∧ (∀ x, C.eval (List.ofFn x) = f x) ∧ P C) :
    ∃ C, Monotone2 C ∧ (∀ x, C.eval (List.ofFn x) = f x) ∧ P C ∧
      ∀ D, Monotone2 D → (∀ x, D.eval (List.ofFn x) = f x) → P D → C.size ≤ D.size := by
  obtain ⟨C, hC, hmin⟩ := exists_minimum_for_property _ h
  exact ⟨C, hC.1, hC.2.1, hC.2.2, fun D hD hDf hDP => hmin D ⟨hD, hDf, hDP⟩⟩

lemma exists_minimum_with_property_of_nonincreasing_normalization
    (P Q : Circuit → Prop) (h : ∃ C, P C)
    (hnorm : ∀ C, P C → ∃ D, P D ∧ Q D ∧ D.size ≤ C.size) :
    ∃ C, P C ∧ (∀ D, P D → C.size ≤ D.size) ∧ Q C := by
  obtain ⟨C, hC, hmin⟩ := exists_minimum_for_property P h
  obtain ⟨D, hD, hQ, hsize⟩ := hnorm C hC
  exact ⟨D, hD, fun E hE => hsize.trans (hmin E hE), hQ⟩

lemma exists_minimum_with_property_of_strict_descent
    (P Q : Circuit → Prop) (h : ∃ C, P C)
    (hdesc : ∀ C, P C → ¬ Q C → ∃ D, P D ∧ D.size < C.size) :
    ∃ C, P C ∧ (∀ D, P D → C.size ≤ D.size) ∧ Q C := by
  classical
  obtain ⟨C, hC, hmin⟩ := exists_minimum_for_property P h
  refine ⟨C, hC, hmin, ?_⟩
  by_contra hQ
  obtain ⟨D, hD, hsize⟩ := hdesc C hC hQ
  exact (Nat.not_lt_of_ge (hmin D hD)) hsize

lemma exists_lexicographic_minimum (P : Circuit → Prop) (rank : Circuit → ℕ)
    (h : ∃ C, P C) :
    ∃ C, P C ∧ (∀ D, P D → C.size ≤ D.size) ∧
      ∀ D, P D → D.size = C.size → rank C ≤ rank D := by
  classical
  obtain ⟨C, hC, hmin⟩ := exists_minimum_for_property P h
  have hs : ∃ r : ℕ, ∃ D, P D ∧ D.size = C.size ∧ rank D = r :=
    ⟨rank C, C, hC, rfl, rfl⟩
  obtain ⟨D, hD, hsize, hrank⟩ := Nat.find_spec hs
  refine ⟨D, hD, ?_, ?_⟩
  · intro E hE
    rw [hsize]
    exact hmin E hE
  · intro E hE hED
    rw [hrank]
    exact Nat.find_min' hs ⟨E, hE, hED.trans hsize, rfl⟩

lemma exists_minimum_with_property_of_lexicographic_descent
    (P Q : Circuit → Prop) (rank : Circuit → ℕ) (h : ∃ C, P C)
    (hdesc : ∀ C, P C → ¬ Q C → ∃ D, P D ∧ D.size ≤ C.size ∧
      (D.size = C.size → rank D < rank C)) :
    ∃ C, P C ∧ (∀ D, P D → C.size ≤ D.size) ∧ Q C := by
  classical
  obtain ⟨C, hC, hmin, hrank⟩ := exists_lexicographic_minimum P rank h
  refine ⟨C, hC, hmin, ?_⟩
  by_contra hQ
  obtain ⟨D, hD, hsize, hless⟩ := hdesc C hC hQ
  have heq := Nat.le_antisymm hsize (hmin D hD)
  exact (Nat.not_lt_of_ge (hrank D hD heq)) (hless heq)

lemma exists_minimum_with_property_iff_nonincreasing_normalization
    (P Q : Circuit → Prop) (h : ∃ C, P C) :
    (∃ C, P C ∧ (∀ D, P D → C.size ≤ D.size) ∧ Q C) ↔
      (∀ C, P C → ∃ D, P D ∧ Q D ∧ D.size ≤ C.size) := by
  constructor
  · rintro ⟨D, hD, hmin, hQ⟩ C hC
    exact ⟨D, hD, hQ, hmin C hC⟩
  · exact exists_minimum_with_property_of_nonincreasing_normalization P Q h

lemma exists_minimum_with_property_of_matching_bounds
    (P Q : Circuit → Prop) (bound : ℕ)
    (hupper : ∃ C, P C ∧ Q C ∧ C.size ≤ bound)
    (hlower : ∀ C, P C → bound ≤ C.size) :
    ∃ C, P C ∧ (∀ D, P D → C.size ≤ D.size) ∧ Q C := by
  obtain ⟨C, hC, hQ, hsize⟩ := hupper
  exact ⟨C, hC, fun D hD => hsize.trans (hlower D hD), hQ⟩

def EdgeCorrect {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) : Prop :=
  ∀ x : Fin n → Bool, C.eval (List.ofFn x) =
    decide (∃ a b : Fin n, G.Adj a b ∧ x a = true ∧ x b = true)

def EdgeSafe {n : ℕ} (G : SimpleGraph (Fin n)) (C : Circuit) : Prop :=
  ∀ j g, C.gates[j]? = some g → g.op = GateOp.and →
    ∀ x : Fin n → Bool, (C.wires (List.ofFn x)).getD (n + j) false = true →
      ∃ a b : Fin n, G.Adj a b ∧ x a = true ∧ x b = true

lemma exists_safe_minimum_of_cover_lower_bound {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (T : Finset (Fin n))
    (builder : ∃ C, Monotone2 C ∧ EdgeCorrect G C ∧
      C.size ≤ G.edgeFinset.card + T.card - 1 ∧ EdgeSafe G C)
    (lower : ∀ C, Monotone2 C → EdgeCorrect G C →
      G.edgeFinset.card + T.card - 1 ≤ C.size) :
    ∃ C, Monotone2 C ∧ EdgeCorrect G C ∧
      (∀ D, Monotone2 D → EdgeCorrect G D → C.size ≤ D.size) ∧ EdgeSafe G C := by
  obtain ⟨C, hmono, hcorrect, hsize, hsafe⟩ := builder
  exact ⟨C, hmono, hcorrect, fun D hD hcorrectD =>
    hsize.trans (lower D hD hcorrectD), hsafe⟩


end Selection

lemma junk_subset_of_pointwise_decrease {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C D : Circuit) (hsize : D.size ≤ C.size)
    (hops : ∀ j, j < D.size → (gateAt D j).op = GateOp.and →
      (gateAt C j).op = GateOp.and)
    (hval : ∀ j, j < D.size → ∀ x : Fin n → Bool,
      graphFun G ∅ x = false → gateVal n D j x = true → gateVal n C j x = true) :
    TopForm.junk G D ⊆ TopForm.junk G C := by
  intro j hj
  have hd : IsDirtyAnd n G D j := (Finset.mem_filter.mp hj).2
  obtain ⟨hop, hj, x, hx, hf⟩ := hd
  have hjD : j < D.size := hj
  have hjC : j < C.gates.length := lt_of_lt_of_le hjD hsize
  exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hjC,
    hops j hjD hop, hjC, x, hval j hjD x hf hx, hf⟩

lemma junk_ssubset_of_pointwise_repair {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C D : Circuit) (hsize : D.size ≤ C.size)
    (hops : ∀ j, j < D.size → (gateAt D j).op = GateOp.and →
      (gateAt C j).op = GateOp.and)
    (hval : ∀ j, j < D.size → ∀ x : Fin n → Bool,
      graphFun G ∅ x = false → gateVal n D j x = true → gateVal n C j x = true)
    (j : ℕ) (hdirty : IsDirtyAnd n G C j) (hclean : TopForm.BelowF G D j) :
    TopForm.junk G D ⊂ TopForm.junk G C := by
  classical
  refine Finset.ssubset_iff_subset_ne.mpr
    ⟨junk_subset_of_pointwise_decrease G C D hsize hops hval, ?_⟩
  intro heq
  have hj : j ∈ TopForm.junk G C := by
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hdirty.2.1, hdirty⟩
  rw [← heq] at hj
  have hd := (Finset.mem_filter.mp hj).2
  obtain ⟨x, hx, hf⟩ := hd.2.2
  have ht := hclean x hx
  rw [hf] at ht
  cases ht

lemma junk_card_lt_of_pointwise_repair {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C D : Circuit) (hsize : D.size ≤ C.size)
    (hops : ∀ j, j < D.size → (gateAt D j).op = GateOp.and →
      (gateAt C j).op = GateOp.and)
    (hval : ∀ j, j < D.size → ∀ x : Fin n → Bool,
      graphFun G ∅ x = false → gateVal n D j x = true → gateVal n C j x = true)
    (j : ℕ) (hdirty : IsDirtyAnd n G C j) (hclean : TopForm.BelowF G D j) :
    (TopForm.junk G D).card < (TopForm.junk G C).card :=
  Finset.card_lt_card (junk_ssubset_of_pointwise_repair G C D hsize hops hval j hdirty hclean)

lemma gateAt_patch_op (pre post : List Gate) (g h : Gate) (out : ℕ)
    (hop : h.op = GateOp.and → g.op = GateOp.and) (j : ℕ) :
    (gateAt ⟨pre ++ h :: post, out⟩ j).op = GateOp.and →
      (gateAt ⟨pre ++ g :: post, out⟩ j).op = GateOp.and := by
  by_cases hj : j < pre.length
  · simp only [gateAt, List.getD_append _ _ _ _ hj]
    exact id
  · have hj' : pre.length ≤ j := Nat.le_of_not_gt hj
    simp only [gateAt, List.getD_append_right _ _ _ _ hj']
    by_cases heq : j - pre.length = 0
    · simp only [heq, List.getD_cons_zero]
      exact hop
    · obtain ⟨k, hk⟩ : ∃ k, j - pre.length = k + 1 :=
        ⟨j - pre.length - 1, by omega⟩
      simp only [hk, List.getD_cons_succ]
      exact id

lemma junk_patch_ssubset {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (pre post : List Gate) (g h : Gate) (out : ℕ)
    (hop : h.op = GateOp.and → g.op = GateOp.and)
    (hval : ∀ j, j < pre.length + 1 + post.length → ∀ x : Fin n → Bool,
      graphFun G ∅ x = false →
      gateVal n ⟨pre ++ h :: post, out⟩ j x = true →
      gateVal n ⟨pre ++ g :: post, out⟩ j x = true)
    (hdirty : IsDirtyAnd n G ⟨pre ++ g :: post, out⟩ pre.length)
    (hclean : TopForm.BelowF G ⟨pre ++ h :: post, out⟩ pre.length) :
    TopForm.junk G ⟨pre ++ h :: post, out⟩ ⊂
      TopForm.junk G ⟨pre ++ g :: post, out⟩ := by
  apply junk_ssubset_of_pointwise_repair G _ _
    (by simp [Circuit.size])
    (fun j _ => gateAt_patch_op pre post g h out hop j)
    (fun j hj => hval j (by simpa [Circuit.size, Nat.add_assoc, Nat.add_comm,
      Nat.add_left_comm] using hj)) pre.length hdirty hclean

noncomputable def dirtyEvents {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit) : Finset (ℕ × (Fin n → Bool)) := by
  classical
  exact ((Finset.range C.size) ×ˢ Finset.univ).filter fun p =>
    (gateAt C p.1).op = GateOp.and ∧ gateVal n C p.1 p.2 = true ∧ graphFun G ∅ p.2 = false

lemma dirtyEvents_subset_of_pointwise_decrease {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C D : Circuit) (hsize : D.size ≤ C.size)
    (hops : ∀ j, j < D.size → (gateAt D j).op = GateOp.and →
      (gateAt C j).op = GateOp.and)
    (hval : ∀ j, j < D.size → ∀ x : Fin n → Bool,
      graphFun G ∅ x = false → gateVal n D j x = true → gateVal n C j x = true) :
    dirtyEvents G D ⊆ dirtyEvents G C := by
  classical
  intro p hp
  obtain ⟨hpair, hop, hx, hf⟩ := Finset.mem_filter.mp hp
  have hj : p.1 < D.size := Finset.mem_range.mp (Finset.mem_product.mp hpair).1
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_product.mpr ⟨Finset.mem_range.mpr (lt_of_lt_of_le hj hsize),
    Finset.mem_univ _⟩, hops p.1 hj hop, hval p.1 hj p.2 hf hx, hf⟩

lemma dirtyEvents_ssubset_of_killed_activation {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C D : Circuit) (hsub : dirtyEvents G D ⊆ dirtyEvents G C)
    (j : ℕ) (hj : j < C.size) (hop : (gateAt C j).op = GateOp.and)
    (x : Fin n → Bool) (hx : gateVal n C j x = true) (hf : graphFun G ∅ x = false)
    (hkill : gateVal n D j x = false) :
    dirtyEvents G D ⊂ dirtyEvents G C := by
  classical
  refine Finset.ssubset_iff_subset_ne.mpr ⟨hsub, ?_⟩
  intro heq
  have hmem : (j, x) ∈ dirtyEvents G C :=
    Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
      ⟨Finset.mem_range.mpr hj, Finset.mem_univ x⟩, hop, hx, hf⟩
  rw [← heq] at hmem
  have ht := (Finset.mem_filter.mp hmem).2.2.1
  rw [hkill] at ht
  cases ht

lemma dirtyEvents_card_lt_of_pointwise_decrease {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C D : Circuit) (hsize : D.size ≤ C.size)
    (hops : ∀ j, j < D.size → (gateAt D j).op = GateOp.and →
      (gateAt C j).op = GateOp.and)
    (hval : ∀ j, j < D.size → ∀ x : Fin n → Bool,
      graphFun G ∅ x = false → gateVal n D j x = true → gateVal n C j x = true)
    (j : ℕ) (hj : j < C.size) (hop : (gateAt C j).op = GateOp.and)
    (x : Fin n → Bool) (hx : gateVal n C j x = true) (hf : graphFun G ∅ x = false)
    (hkill : gateVal n D j x = false) :
    (dirtyEvents G D).card < (dirtyEvents G C).card := by
  exact Finset.card_lt_card (dirtyEvents_ssubset_of_killed_activation G C D
    (dirtyEvents_subset_of_pointwise_decrease G C D hsize hops hval) j hj hop x hx hf hkill)



end Construction

lemma exists_correct {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    ∃ C, Correct G C := by
  classical
  obtain ⟨C, hm, hf, _, _⟩ := Construction.Builder.main n G Finset.univ
    (fun _ _ _ => Or.inl (Finset.mem_univ _))
  exact ⟨C, hm, hf⟩

def LocallyStable {n : ℕ} (G : SimpleGraph (Fin n)) (C : Circuit) : Prop :=
  ∀ (pre post : List Gate) (g : Gate) (out : ℕ),
    C = Repair.patchCircuit pre post g out → ∀ h : Gate,
      ((h.op = GateOp.and ∨ h.op = GateOp.or) ∧ h.inputs.length ≤ 2) →
      (∀ x : Fin n → Bool, Repair.gatePrefix pre h x = true →
        Repair.gatePrefix pre g x = true) →
      (∀ u v, G.Adj u v →
        (Repair.patchCircuit pre post ⟨.or, []⟩ out).eval
          (List.ofFn (Repair.mask {u,v})) = false →
        Repair.gatePrefix pre h (Repair.mask {u,v}) = true) →
      ∀ x : Fin n → Bool, ¬ Repair.hit G x →
        Repair.gatePrefix pre h x = Repair.gatePrefix pre g x

lemma trace_extremal_locally_stable {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit) (hc : Correct G C)
    (hmin : ∀ D, Correct G D → D.size ≤ C.size →
      (falseTrace G C).card ≤ (falseTrace G D).card) : LocallyStable G C := by
  intro pre post g out hC h hh hdom hcrit x hx
  subst C
  have correct : ∀ y : Fin n → Bool,
      (Repair.patchCircuit pre post g out).eval (List.ofFn y) = true ↔ Repair.hit G y := by
    intro y
    rw [hc.2 y]
    exact decide_eq_true_iff
  obtain ⟨hm, hs, hf, hv⟩ := Repair.critical_gate_repair G pre post g h out hc.1 hh
    correct hdom hcrit
  have hD : Correct G (Repair.patchCircuit pre post h out) := by
    refine ⟨hm, ?_⟩
    intro y
    apply Bool.eq_iff_iff.mpr
    rw [decide_eq_true_iff]
    exact hf y
  apply Bool.eq_iff_iff.mpr
  refine ⟨hdom x, ?_⟩
  intro htrue
  have hCx : ((Repair.patchCircuit pre post g out).wires (List.ofFn x)).getD
      (n + pre.length) false = true := by
    simpa only [Repair.patch_wire_value] using htrue
  have hn := trace_extremal_no_decrease G (Repair.patchCircuit pre post g out)
    hmin (Repair.patchCircuit pre post h out) hD hs.le
    (fun y j _ => hv y (n+j)) pre.length
    (by simp [Repair.patchCircuit, Circuit.size]) x hx hCx
  simpa only [Repair.patch_wire_value] using hn

lemma exists_locally_stable_minimum {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] :
    ∃ C, Correct G C ∧ (∀ D, Correct G D → C.size ≤ D.size) ∧ LocallyStable G C := by
  obtain ⟨C, hc, hm, ht⟩ := exists_trace_extremal G (exists_correct G)
  exact ⟨C, hc, hm, trace_extremal_locally_stable G C hc ht⟩

def CriticalEdge {n : ℕ} (G : SimpleGraph (Fin n))
    (pre post : List Gate) (out : ℕ) (a b : Fin n) : Prop :=
  G.Adj a b ∧ (Repair.patchCircuit pre post ⟨.or, []⟩ out).eval
    (List.ofFn (Repair.mask {a,b})) = false

lemma trace_extremal_dirty_two_critical_edges {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (pre post : List Gate) (g : Gate) (out : ℕ)
    (hc : Correct G (Repair.patchCircuit pre post g out))
    (hmin : ∀ D, Correct G D → D.size ≤ (Repair.patchCircuit pre post g out).size →
      (falseTrace G (Repair.patchCircuit pre post g out)).card ≤ (falseTrace G D).card)
    (x : Fin n → Bool) (hx : ¬ Repair.hit G x)
    (hgx : Repair.gatePrefix pre g x = true) :
    ∃ a b c d, CriticalEdge G pre post out a b ∧ CriticalEdge G pre post out c d ∧
      ¬ ((c = a ∧ d = b) ∨ (c = b ∧ d = a)) := by
  classical
  have correct : ∀ y : Fin n → Bool,
      (Repair.patchCircuit pre post g out).eval (List.ofFn y) = true ↔ Repair.hit G y := by
    intro y
    rw [hc.2 y]
    exact decide_eq_true_iff
  have unchanged (D : Circuit) (hm : Monotone2 D)
      (hs : D.size = (Repair.patchCircuit pre post g out).size)
      (hf : ∀ y : Fin n → Bool, D.eval (List.ofFn y) = true ↔ Repair.hit G y)
      (hv : ∀ y : Fin n → Bool, Repair.WireLE (D.wires (List.ofFn y))
        ((Repair.patchCircuit pre post g out).wires (List.ofFn y))) :
      (D.wires (List.ofFn x)).getD (n + pre.length) false = true := by
    have hd : Correct G D := by
      refine ⟨hm, ?_⟩
      intro y
      apply Bool.eq_iff_iff.mpr
      rw [decide_eq_true_iff]
      exact hf y
    apply trace_extremal_no_decrease G (Repair.patchCircuit pre post g out) hmin D hd hs.le
      (fun y j _ => hv y (n+j)) pre.length
      (by simp [Repair.patchCircuit, Circuit.size]) x hx
    simpa only [Repair.patch_wire_value] using hgx
  by_cases hex : ∃ a b, CriticalEdge G pre post out a b
  · obtain ⟨a, b, hab⟩ := hex
    by_cases htwo : ∃ c d, CriticalEdge G pre post out c d ∧
        ¬ ((c = a ∧ d = b) ∨ (c = b ∧ d = a))
    · obtain ⟨c, d, hcd, hne⟩ := htwo
      exact ⟨a, b, c, d, hab, hcd, hne⟩
    · have unique : ∀ u v, G.Adj u v →
          (Repair.patchCircuit pre post ⟨.or, []⟩ out).eval
            (List.ofFn (Repair.mask {u,v})) = false →
          (u = a ∧ v = b) ∨ (u = b ∧ v = a) := by
        intro u v huv hz
        by_contra hne
        exact htwo ⟨u, v, ⟨huv, hz⟩, hne⟩
      obtain ⟨hm, hs, hf, hv, hsafe⟩ := Repair.single_edge_circuit_repair_safe G
        pre post g out hc.1 correct a b hab.1 hab.2 unique
      exact False.elim (hx (hsafe x (unchanged _ hm hs hf hv)))
  · have survives : ∀ u v, G.Adj u v →
        (Repair.patchCircuit pre post ⟨.or, []⟩ out).eval
          (List.ofFn (Repair.mask {u,v})) = true := by
      intro u v huv
      cases hz : (Repair.patchCircuit pre post ⟨.or, []⟩ out).eval
          (List.ofFn (Repair.mask {u,v})) with
      | false => exact False.elim (hex ⟨u, v, huv, hz⟩)
      | true => rfl
    obtain ⟨hm, hs, hf, hv, hzero⟩ := Repair.zero_edge_circuit_repair G
      pre post g out hc.1 correct survives
    have htrue := unchanged _ hm hs hf hv
    rw [hzero x] at htrue
    cases htrue

lemma exists_three_level_minimum {α : Type*} (P : α → Prop)
    (m₁ m₂ m₃ : α → ℕ) (hex : ∃ a, P a) :
    ∃ a, P a ∧ (∀ b, P b → m₁ a ≤ m₁ b) ∧
      (∀ b, P b → m₁ b ≤ m₁ a → m₂ a ≤ m₂ b) ∧
      ∀ b, P b → m₁ b ≤ m₁ a → m₂ b ≤ m₂ a → m₃ a ≤ m₃ b := by
  obtain ⟨a, ha, h₁⟩ := exists_minimizer P m₁ hex
  obtain ⟨b, ⟨hb, hba⟩, h₂⟩ := exists_minimizer
    (fun b => P b ∧ m₁ b ≤ m₁ a) m₂ ⟨a, ha, le_rfl⟩
  obtain ⟨c, ⟨hc, hca, hcb⟩, h₃⟩ := exists_minimizer
    (fun c => P c ∧ m₁ c ≤ m₁ a ∧ m₂ c ≤ m₂ b) m₃
    ⟨b, hb, hba, le_rfl⟩
  refine ⟨c, hc, fun d hd => hca.trans (h₁ d hd), ?_, ?_⟩
  · intro d hd hdc
    exact hcb.trans (h₂ d ⟨hd, hdc.trans hca⟩)
  · intro d hd hdc hdcb
    exact h₃ d ⟨hd, hdc.trans hca, hdcb.trans hcb⟩

lemma exists_dirty_trace_minimum {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] :
    ∃ C, Correct G C ∧ (∀ D, Correct G D → C.size ≤ D.size) ∧
      (∀ D, Correct G D → D.size ≤ C.size →
        (dirtySet G C).card ≤ (dirtySet G D).card) ∧
      ∀ D, Correct G D → D.size ≤ C.size →
        (dirtySet G D).card ≤ (dirtySet G C).card →
        (falseTrace G C).card ≤ (falseTrace G D).card := by
  exact exists_three_level_minimum (Correct G) Circuit.size
    (fun C => (dirtySet G C).card) (fun C => (falseTrace G C).card) (exists_correct G)

lemma dirty_trace_extremal_no_decrease {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit)
    (hmin : ∀ D, Correct G D → D.size ≤ C.size →
      (dirtySet G D).card ≤ (dirtySet G C).card →
      (falseTrace G C).card ≤ (falseTrace G D).card)
    (D : Circuit) (hD : Correct G D) (hsize : D.size ≤ C.size)
    (hdirty : dirtySet G D ⊆ dirtySet G C)
    (hdown : ∀ (x : Fin n → Bool) (j : ℕ), j < D.size →
      (D.wires (List.ofFn x)).getD (n+j) false = true →
      (C.wires (List.ofFn x)).getD (n+j) false = true)
    (j : ℕ) (hj : j < C.size) (x : Fin n → Bool)
    (hx : ¬ ∃ u v, G.Adj u v ∧ x u = true ∧ x v = true)
    (hCx : (C.wires (List.ofFn x)).getD (n+j) false = true) :
    (D.wires (List.ofFn x)).getD (n+j) false = true := by
  classical
  have hsub := falseTrace_subset G C D hsize hdown
  have heq : falseTrace G D = falseTrace G C :=
    Finset.eq_of_subset_of_card_le hsub (hmin D hD hsize (Finset.card_le_card hdirty))
  have hp : (j,x) ∈ falseTrace G C := by
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_product.mpr ⟨Finset.mem_range.mpr hj, Finset.mem_univ _⟩,
      hx, hCx⟩
  rw [← heq] at hp
  exact (Finset.mem_filter.mp hp).2.2

lemma dirtySet_eq_junk {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) : dirtySet G C = PEqualNP.TopForm.junk G C := rfl

lemma dirty_extremal_no_clean_patch {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (pre post : List Gate) (g h : Gate) (out : ℕ)
    (hmin : ∀ D, Correct G D → D.size ≤ (Repair.patchCircuit pre post g out).size →
      (dirtySet G (Repair.patchCircuit pre post g out)).card ≤ (dirtySet G D).card)
    (hD : Correct G (Repair.patchCircuit pre post h out))
    (hdown : ∀ x : Fin n → Bool,
      Repair.WireLE ((Repair.patchCircuit pre post h out).wires (List.ofFn x))
        ((Repair.patchCircuit pre post g out).wires (List.ofFn x)))
    (hbad : PEqualNP.CleanedNonEdge.IsDirtyAnd n G
      (Repair.patchCircuit pre post g out) pre.length)
    (hsafe : ∀ x : Fin n → Bool,
      ((Repair.patchCircuit pre post h out).wires (List.ofFn x)).getD
        (n + pre.length) false = true → Repair.hit G x) : False := by
  have hg : g.op = GateOp.and := by
    have h := hbad.1
    simpa [PEqualNP.MetaComplexity.NestedCover.gateAt, Repair.patchCircuit,
      List.getD_eq_getElem?_getD] using h
  have hclean : PEqualNP.TopForm.BelowF G (Repair.patchCircuit pre post h out)
      pre.length := by
    intro x hx
    have hit := hsafe x hx
    simpa [PEqualNP.MetaComplexity.NestedCover.graphFun, Repair.hit] using hit
  have hsub := Construction.junk_patch_ssubset G pre post g h out (fun _ => hg)
    (fun j _ x _ => hdown x (n+j)) hbad hclean
  have hlt := Finset.card_lt_card hsub
  have hle := hmin (Repair.patchCircuit pre post h out) hD
    (by simp [Repair.patchCircuit, Circuit.size])
  rw [dirtySet_eq_junk, dirtySet_eq_junk] at hle
  exact Nat.not_lt_of_ge hle hlt

lemma dirty_extremal_two_critical_edges {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (pre post : List Gate) (g : Gate) (out : ℕ)
    (hc : Correct G (Repair.patchCircuit pre post g out))
    (hmin : ∀ D, Correct G D → D.size ≤ (Repair.patchCircuit pre post g out).size →
      (dirtySet G (Repair.patchCircuit pre post g out)).card ≤ (dirtySet G D).card)
    (hbad : PEqualNP.CleanedNonEdge.IsDirtyAnd n G
      (Repair.patchCircuit pre post g out) pre.length) :
    ∃ a b c d, CriticalEdge G pre post out a b ∧ CriticalEdge G pre post out c d ∧
      ¬ ((c = a ∧ d = b) ∨ (c = b ∧ d = a)) := by
  classical
  have correct : ∀ y : Fin n → Bool,
      (Repair.patchCircuit pre post g out).eval (List.ofFn y) = true ↔ Repair.hit G y := by
    intro y
    rw [hc.2 y]
    exact decide_eq_true_iff
  have impossible (h : Gate) (hm : Monotone2 (Repair.patchCircuit pre post h out))
      (hf : ∀ y : Fin n → Bool,
        (Repair.patchCircuit pre post h out).eval (List.ofFn y) = true ↔ Repair.hit G y)
      (hv : ∀ y : Fin n → Bool,
        Repair.WireLE ((Repair.patchCircuit pre post h out).wires (List.ofFn y))
          ((Repair.patchCircuit pre post g out).wires (List.ofFn y)))
      (hsafe : ∀ y : Fin n → Bool,
        ((Repair.patchCircuit pre post h out).wires (List.ofFn y)).getD
          (n + pre.length) false = true → Repair.hit G y) : False := by
    apply dirty_extremal_no_clean_patch G pre post g h out hmin _ hv hbad hsafe
    refine ⟨hm, ?_⟩
    intro y
    apply Bool.eq_iff_iff.mpr
    rw [decide_eq_true_iff]
    exact hf y
  by_cases hex : ∃ a b, CriticalEdge G pre post out a b
  · obtain ⟨a, b, hab⟩ := hex
    by_cases htwo : ∃ c d, CriticalEdge G pre post out c d ∧
        ¬ ((c = a ∧ d = b) ∨ (c = b ∧ d = a))
    · obtain ⟨c, d, hcd, hne⟩ := htwo
      exact ⟨a, b, c, d, hab, hcd, hne⟩
    · have unique : ∀ u v, G.Adj u v →
          (Repair.patchCircuit pre post ⟨.or, []⟩ out).eval
            (List.ofFn (Repair.mask {u,v})) = false →
          (u = a ∧ v = b) ∨ (u = b ∧ v = a) := by
        intro u v huv hz
        by_contra hne
        exact htwo ⟨u, v, ⟨huv, hz⟩, hne⟩
      obtain ⟨hm, _, hf, hv, hs⟩ := Repair.single_edge_circuit_repair_safe G
        pre post g out hc.1 correct a b hab.1 hab.2 unique
      exact False.elim (impossible _ hm hf hv hs)
  · have survives : ∀ u v, G.Adj u v →
        (Repair.patchCircuit pre post ⟨.or, []⟩ out).eval
          (List.ofFn (Repair.mask {u,v})) = true := by
      intro u v huv
      cases hz : (Repair.patchCircuit pre post ⟨.or, []⟩ out).eval
          (List.ofFn (Repair.mask {u,v})) with
      | false => exact False.elim (hex ⟨u, v, huv, hz⟩)
      | true => rfl
    obtain ⟨hm, _, hf, hv, hz⟩ := Repair.zero_edge_circuit_repair G
      pre post g out hc.1 correct survives
    apply False.elim
    apply impossible _ hm hf hv
    intro y hy
    rw [hz y] at hy
    cases hy

lemma touching_two_edges_contains_center {V : Type*} (G : SimpleGraph V)
    (htri : ∀ a b c, G.Adj a b → G.Adj b c → ¬ G.Adj c a)
    (a b c u v : V) (hab : G.Adj a b) (hac : G.Adj a c) (hbc : b ≠ c)
    (huv : G.Adj u v)
    (h₁ : (u = a ∨ v = a) ∨ (u = b ∨ v = b))
    (h₂ : (u = a ∨ v = a) ∨ (u = c ∨ v = c)) : u = a ∨ v = a := by
  classical
  by_contra h
  rcases h₁.resolve_left h with hub | hvb
  · rcases h₂.resolve_left h with huc | hvc
    · exact hbc (hub.symm.trans huc)
    · subst u
      subst v
      exact htri a b c hab huv hac.symm
  · rcases h₂.resolve_left h with huc | hvc
    · subst u
      subst v
      exact htri a b c hab huv.symm hac.symm
    · exact hbc (hvb.symm.trans hvc)

lemma edge_family_star_or_disjoint {V : Type*} (G : SimpleGraph V)
    (htri : ∀ a b c, G.Adj a b → G.Adj b c → ¬ G.Adj c a)
    (P : V → V → Prop) (hP : ∀ a b, P a b → G.Adj a b)
    (hex : ∃ a b, P a b) :
    (∃ v, ∀ a b, P a b → a = v ∨ b = v) ∨
      ∃ a b c d, P a b ∧ P c d ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d := by
  classical
  by_cases hd : ∃ a b c d, P a b ∧ P c d ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d
  · exact Or.inr hd
  left
  have meet (a b c d : V) (hab : P a b) (hcd : P c d) :
      (c = a ∨ d = a) ∨ (c = b ∨ d = b) := by
    by_contra h
    push Not at h
    exact hd ⟨a,b,c,d,hab,hcd,Ne.symm h.1.1,Ne.symm h.1.2,
      Ne.symm h.2.1,Ne.symm h.2.2⟩
  obtain ⟨a,b,hab⟩ := hex
  by_cases ha : ∀ c d, P c d → c = a ∨ d = a
  · exact ⟨a,ha⟩
  push Not at ha
  obtain ⟨c,d,hcd,hca,hda⟩ := ha
  have hb : c = b ∨ d = b := (meet a b c d hab hcd).resolve_left
    (not_or.mpr ⟨hca,hda⟩)
  refine ⟨b, ?_⟩
  intro u v huv
  have h₁ : (u = b ∨ v = b) ∨ (u = a ∨ v = a) :=
    (meet a b u v hab huv).symm
  rcases hb with hcb | hdb
  · subst c
    exact touching_two_edges_contains_center G htri b a d u v
      (hP a b hab).symm (hP b d hcd) (Ne.symm hda) (hP u v huv)
      h₁ (meet b d u v hcd huv)
  · subst d
    exact touching_two_edges_contains_center G htri b a c u v
      (hP a b hab).symm (hP c b hcd).symm (Ne.symm hca) (hP u v huv)
      h₁ (meet c b u v hcd huv).symm

namespace Repair

namespace TwoSingletonRepair

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

lemma gatePrefix_or {n : ℕ} (pre : List Gate) (u w : Fin n) (x : Fin n → Bool) :
    gatePrefix pre ⟨.or, [u.val, w.val]⟩ x = (x u || x w) := by
  simp only [gatePrefix, GateOp.eval, List.map_cons, List.map_nil, List.any_cons,
    List.any_nil, id_eq, Bool.or_false]
  rw [run_input pre x u, run_input pre x w]

lemma two_singleton_circuit_repair {n : ℕ} (G : SimpleGraph (Fin n))
    (pre post : List Gate) (g : Gate) (out : ℕ)
    (hc : Monotone2 (patchCircuit pre post g out))
    (correct : ∀ x : Fin n → Bool,
      (patchCircuit pre post g out).eval (List.ofFn x) = true ↔ hit G x)
    (u w : Fin n)
    (hu : gatePrefix pre g (mask {u}) = true)
    (hw : gatePrefix pre g (mask {w}) = true)
    (critical : ∀ a b, G.Adj a b →
      (patchCircuit pre post ⟨.or, []⟩ out).eval (List.ofFn (mask {a, b})) = false →
        a = u ∨ b = u ∨ a = w ∨ b = w) :
    let C := patchCircuit pre post g out
    let D := patchCircuit pre post ⟨.or, [u.val, w.val]⟩ out
    Monotone2 D ∧ D.size = C.size ∧
    (∀ x : Fin n → Bool, D.eval (List.ofFn x) = true ↔ hit G x) ∧
    (∀ x : Fin n → Bool, WireLE (D.wires (List.ofFn x)) (C.wires (List.ofFn x))) ∧
    D.gates[pre.length]? = some ⟨.or, [u.val, w.val]⟩ := by
  dsimp only
  have hpre : ∀ q ∈ pre, q.op = GateOp.and ∨ q.op = GateOp.or := by
    intro q hq
    exact (hc q (List.mem_append_left _ hq)).1
  have hg : g.op = GateOp.and ∨ g.op = GateOp.or :=
    (hc g (List.mem_append_right _ List.mem_cons_self)).1
  have dominated : ∀ x : Fin n → Bool,
      gatePrefix pre ⟨.or, [u.val, w.val]⟩ x = true → gatePrefix pre g x = true := by
    intro x hx
    rw [gatePrefix_or] at hx
    simp only [Bool.or_eq_true] at hx
    rcases hx with hxu | hxw
    · apply gatePrefix_mono pre g hpre hg (mask {u}) x ?_ hu
      intro i hi
      have hiu : i = u := by simpa [mask] using hi
      subst i
      exact hxu
    · apply gatePrefix_mono pre g hpre hg (mask {w}) x ?_ hw
      intro i hi
      have hiw : i = w := by simpa [mask] using hi
      subst i
      exact hxw
  have keeps : ∀ a b, G.Adj a b →
      (patchCircuit pre post ⟨.or, []⟩ out).eval (List.ofFn (mask {a, b})) = false →
        gatePrefix pre ⟨.or, [u.val, w.val]⟩ (mask {a, b}) = true := by
    intro a b hab hz
    rw [gatePrefix_or]
    rcases critical a b hab hz with rfl | rfl | rfl | rfl <;> simp [mask]
  obtain ⟨hm, hs, he, hl⟩ := critical_gate_repair G pre post g
    ⟨.or, [u.val, w.val]⟩ out hc ⟨Or.inr rfl, by simp⟩ correct dominated keeps
  exact ⟨hm, hs, he, hl, by simp [patchCircuit]⟩

end TwoSingletonRepair

end Repair

lemma dirty_extremal_no_nonand_patch {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (pre post : List Gate) (g h : Gate) (out : ℕ)
    (hmin : ∀ D, Correct G D → D.size ≤ (Repair.patchCircuit pre post g out).size →
      (dirtySet G (Repair.patchCircuit pre post g out)).card ≤ (dirtySet G D).card)
    (hD : Correct G (Repair.patchCircuit pre post h out))
    (hdown : ∀ x : Fin n → Bool,
      Repair.WireLE ((Repair.patchCircuit pre post h out).wires (List.ofFn x))
        ((Repair.patchCircuit pre post g out).wires (List.ofFn x)))
    (hbad : PEqualNP.CleanedNonEdge.IsDirtyAnd n G
      (Repair.patchCircuit pre post g out) pre.length)
    (hop : h.op ≠ GateOp.and) : False := by
  classical
  have hsub : dirtySet G (Repair.patchCircuit pre post h out) ⊆
      dirtySet G (Repair.patchCircuit pre post g out) := by
    rw [dirtySet_eq_junk, dirtySet_eq_junk]
    apply Construction.junk_subset_of_pointwise_decrease G _ _
      (by simp [Repair.patchCircuit, Circuit.size])
    · intro j _
      exact Construction.gateAt_patch_op pre post g h out (fun h => False.elim (hop h)) j
    · intro j _ x _ hx
      exact hdown x (n+j) hx
  have hin : pre.length ∈ dirtySet G (Repair.patchCircuit pre post g out) :=
    Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hbad.2.1, hbad⟩
  have hout : pre.length ∉ dirtySet G (Repair.patchCircuit pre post h out) := by
    intro hmem
    have hh := (Finset.mem_filter.mp hmem).2.1
    apply hop
    simpa [PEqualNP.MetaComplexity.NestedCover.gateAt, Repair.patchCircuit,
      List.getD_eq_getElem?_getD] using hh
  exact Nat.not_lt_of_ge (hmin _ hD (by simp [Repair.patchCircuit, Circuit.size]))
    (dirty_card_decreases G _ _ pre.length hsub hin hout)

lemma dirty_extremal_no_two_singleton_cover {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (pre post : List Gate) (g : Gate) (out : ℕ)
    (hc : Correct G (Repair.patchCircuit pre post g out))
    (hmin : ∀ D, Correct G D → D.size ≤ (Repair.patchCircuit pre post g out).size →
      (dirtySet G (Repair.patchCircuit pre post g out)).card ≤ (dirtySet G D).card)
    (hbad : PEqualNP.CleanedNonEdge.IsDirtyAnd n G
      (Repair.patchCircuit pre post g out) pre.length)
    (u w : Fin n)
    (hu : Repair.gatePrefix pre g (Repair.mask {u}) = true)
    (hw : Repair.gatePrefix pre g (Repair.mask {w}) = true)
    (hcover : ∀ a b, CriticalEdge G pre post out a b →
      a = u ∨ b = u ∨ a = w ∨ b = w) : False := by
  have correct : ∀ x : Fin n → Bool,
      (Repair.patchCircuit pre post g out).eval (List.ofFn x) = true ↔ Repair.hit G x := by
    intro x
    rw [hc.2 x]
    exact decide_eq_true_iff
  obtain ⟨hm, _, he, hl, _⟩ := Repair.TwoSingletonRepair.two_singleton_circuit_repair
    G pre post g out hc.1 correct u w hu hw (fun a b ha hb => hcover a b ⟨ha,hb⟩)
  apply dirty_extremal_no_nonand_patch G pre post g ⟨.or,[u.val,w.val]⟩ out hmin _ hl hbad
    (by intro h; cases h)
  refine ⟨hm, ?_⟩
  intro x
  apply Bool.eq_iff_iff.mpr
  rw [decide_eq_true_iff]
  exact he x

lemma exists_first_dirty_split {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit)
    (hex : ∃ j, PEqualNP.CleanedNonEdge.IsDirtyAnd n G C j) :
    ∃ pre g post, C.gates = pre ++ g :: post ∧ g.op = GateOp.and ∧
      PEqualNP.CleanedNonEdge.IsDirtyAnd n G C pre.length ∧
      ∀ i < pre.length, ¬ PEqualNP.CleanedNonEdge.IsDirtyAnd n G C i := by
  classical
  let j := Nat.find hex
  have hbad : PEqualNP.CleanedNonEdge.IsDirtyAnd n G C j := Nat.find_spec hex
  have hj : j < C.gates.length := hbad.2.1
  let pre := C.gates.take j
  let g := C.gates[j]
  let post := C.gates.drop (j+1)
  have hlen : pre.length = j := by simp [pre, Nat.min_eq_left hj.le]
  have hsplit : C.gates = pre ++ g :: post := by
    dsimp [pre, g, post]
    rw [← List.drop_eq_getElem_cons hj, List.take_append_drop]
  refine ⟨pre, g, post, hsplit, ?_, hlen.symm ▸ hbad, ?_⟩
  · have h := hbad.1
    simpa [PEqualNP.MetaComplexity.NestedCover.gateAt, g,
      List.getD_eq_getElem?_getD, hj] using h
  · intro i hi
    apply Nat.find_min hex
    change i < j
    omega

lemma correct_minimal_mono {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hc : Correct G C) (hmin : ∀ D, Correct G D → C.size ≤ D.size) :
    IsMinimalMonoCircuit n C := by
  refine ⟨hc.1, ?_⟩
  intro D hd heq
  apply hmin D
  refine ⟨hd, ?_⟩
  intro x
  exact (congrFun heq x).trans (hc.2 x)

lemma and_safe_of_no_dirty {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (h : ∀ j, ¬ PEqualNP.CleanedNonEdge.IsDirtyAnd n G C j)
    (j : ℕ) (g : Gate) (hjg : C.gates[j]? = some g) (hg : g.op = GateOp.and)
    (x : Fin n → Bool)
    (hx : (C.wires (List.ofFn x)).getD (n+j) false = true) :
    ∃ a b, G.Adj a b ∧ x a = true ∧ x b = true := by
  classical
  by_contra hbad
  obtain ⟨hj, hget⟩ := List.getElem?_eq_some_iff.mp hjg
  apply h j
  refine ⟨?_, hj, x, hx, ?_⟩
  · simpa [PEqualNP.MetaComplexity.NestedCover.gateAt,
      List.getD_eq_getElem?_getD, hjg] using hg
  · simp [PEqualNP.MetaComplexity.NestedCover.graphFun, hbad]

end PEqualNP.Outside.L_meta_1904_aux
