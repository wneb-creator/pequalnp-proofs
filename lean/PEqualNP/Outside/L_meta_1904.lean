import PEqualNP.Defs

-- Helper certificates for independent review; the posted gap remains open.

namespace PEqualNP.Outside.L_meta_1904_aux

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




def SupportMonotone {n : ℕ} (f : (Fin n → Bool) → Bool) : Prop :=
  ∀ x y, (∀ v, x v = true → y v = true) → f x = true → f y = true

lemma supportMonotone_of_monotone {n : ℕ} (f : (Fin n → Bool) → Bool)
    (hf : Monotone f) : SupportMonotone f := by
  intro x y hxy hfx
  exact Bool.le_iff_imp.mp (hf (fun v => Bool.le_iff_imp.mpr (hxy v))) hfx

noncomputable def setInput {n : ℕ} (s : Set (Fin n)) : Fin n → Bool := by
  classical
  exact fun v => decide (v ∈ s)

def EdgeHolds {n : ℕ} (G : SimpleGraph (Fin n)) (x : Fin n → Bool) : Prop :=
  ∃ u v, G.Adj u v ∧ x u = true ∧ x v = true

noncomputable def edgeFunction {n : ℕ} (G : SimpleGraph (Fin n))
    (x : Fin n → Bool) : Bool := by
  classical
  exact decide (EdgeHolds G x)

lemma setInput_true_iff {n : ℕ} (s : Set (Fin n)) (v : Fin n) :
    setInput s v = true ↔ v ∈ s := by
  classical
  simp [setInput]

lemma exists_maximal_independent_superset {n : ℕ} (G : SimpleGraph (Fin n))
    {s : Set (Fin n)} (hs : G.IsIndepSet s) :
    ∃ t, s ⊆ t ∧ Maximal G.IsIndepSet t := by
  exact Finite.exists_le_maximal hs

lemma independent_support_iff {n : ℕ} (G : SimpleGraph (Fin n))
    (x : Fin n → Bool) :
    G.IsIndepSet {v | x v = true} ↔ ¬ EdgeHolds G x := by
  constructor
  · intro hs ⟨u, v, huv, hxu, hxv⟩
    exact hs hxu hxv huv.ne huv
  · intro h u hu v hv _ hadj
    exact h ⟨u, v, hadj, hu, hv⟩

lemma implies_edge_iff_rejects_maximal {n : ℕ} (G : SimpleGraph (Fin n))
    (f : (Fin n → Bool) → Bool) (hf : SupportMonotone f) :
    (∀ x, f x = true → EdgeHolds G x) ↔
      ∀ s, Maximal G.IsIndepSet s → f (setInput s) = false := by
  constructor
  · intro h s hs
    cases hfs : f (setInput s) with
    | false => rfl
    | true =>
      obtain ⟨u, v, huv, hu, hv⟩ := h _ hfs
      exact False.elim (hs.1 ((setInput_true_iff s u).mp hu)
        ((setInput_true_iff s v).mp hv) huv.ne huv)
  · intro h x hx
    by_contra he
    obtain ⟨s, hxs, hs⟩ := exists_maximal_independent_superset G
      ((independent_support_iff G x).mpr he)
    have htrue : f (setInput s) = true := hf x (setInput s)
      (fun v hv => (setInput_true_iff s v).mpr (hxs hv)) hx
    rw [h s hs] at htrue
    cases htrue

lemma equals_edge_iff_boundary {n : ℕ} (G : SimpleGraph (Fin n))
    (f : (Fin n → Bool) → Bool) (hf : SupportMonotone f) :
    (∀ x, f x = edgeFunction G x) ↔
      (∀ u v, G.Adj u v → f (setInput ({u, v} : Set (Fin n))) = true) ∧
      (∀ s, Maximal G.IsIndepSet s → f (setInput s) = false) := by
  constructor
  · intro h
    have himplies : ∀ x, f x = true → EdgeHolds G x := by
      intro x hx
      rw [h x] at hx
      simpa [edgeFunction] using hx
    refine ⟨?_, (implies_edge_iff_rejects_maximal G f hf).mp himplies⟩
    intro u v huv
    rw [h]
    simp only [edgeFunction, decide_eq_true_eq]
    exact ⟨u, v, huv, (setInput_true_iff _ _).mpr (by simp),
      (setInput_true_iff _ _).mpr (by simp)⟩
  · rintro ⟨hpairs, hmax⟩ x
    have himplies := (implies_edge_iff_rejects_maximal G f hf).mpr hmax
    have hiff : f x = true ↔ EdgeHolds G x := by
      refine ⟨himplies x, ?_⟩
      rintro ⟨u, v, huv, hu, hv⟩
      apply hf (setInput ({u, v} : Set (Fin n))) x ?_ (hpairs u v huv)
      intro w hw
      have hmem := (setInput_true_iff ({u, v} : Set (Fin n)) w).mp hw
      rcases hmem with hwu | hwv
      · simpa only [hwu] using hu
      · have hwv' : w = v := by simpa only [Set.mem_singleton_iff] using hwv
        simpa only [hwv'] using hv
    cases hfx : f x <;> cases hex : edgeFunction G x <;> try rfl
    · have he : EdgeHolds G x := by simpa [edgeFunction] using hex
      have := hiff.mpr he
      simp [hfx] at this
    · have he := hiff.mp hfx
      have : edgeFunction G x = true := by simpa [edgeFunction] using he
      simp [hex] at this



open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

lemma signed_boundary_transfer {n : ℕ} (G : SimpleGraph (Fin n))
    (f f' : (Fin n → Bool) → Bool)
    (hf : SupportMonotone f) (hf' : SupportMonotone f')
    (hcorrect : ∀ x, f x = edgeFunction G x)
    (hpositive : ∀ u v, G.Adj u v →
      f (setInput ({u, v} : Set (Fin n))) = true →
      f' (setInput ({u, v} : Set (Fin n))) = true)
    (hnegative : ∀ s, Maximal G.IsIndepSet s →
      f' (setInput s) = true → f (setInput s) = true) :
    ∀ x, f' x = edgeFunction G x := by
  have hboundary := (equals_edge_iff_boundary G f hf).mp hcorrect
  apply (equals_edge_iff_boundary G f' hf').mpr
  refine ⟨fun u v huv => hpositive u v huv (hboundary.1 u v huv), ?_⟩
  intro s hs
  cases he : f' (setInput s) with
  | false => rfl
  | true =>
    have hbad := hnegative s hs he
    rw [hboundary.2 s hs] at hbad
    cases hbad

lemma signed_circuit_support_monotone {n : ℕ} (C : Circuit)
    (hm : Monotone2 C) :
    SupportMonotone (fun x : Fin n → Bool => C.eval (List.ofFn x)) := by
  intro x y hxy htrue
  have hw : WireLE (List.ofFn x) (List.ofFn y) := by
    intro i hi
    by_cases hn : i < n
    · have hx : x ⟨i, hn⟩ = true := by
        simpa [List.getD_eq_getElem?_getD, List.getElem?_ofFn, hn] using hi
      simpa [List.getD_eq_getElem?_getD, List.getElem?_ofFn, hn] using hxy ⟨i, hn⟩ hx
    · simp [List.getD_eq_getElem?_getD, hn] at hi
  exact run_mono C.gates (by simp) hw (fun a ha => (hm a ha).1) C.output htrue

lemma signed_context_mono (pre rest : List Gate) (g g' : Gate) (out : ℕ)
    (x : List Bool)
    (hrest : ∀ a ∈ rest, a.op = .and ∨ a.op = .or)
    (hvalue : g.op.eval (g.inputs.map fun i => (run pre x).getD i false) = true →
      g'.op.eval (g'.inputs.map fun i => (run pre x).getD i false) = true) :
    (⟨pre ++ g :: rest, out⟩ : Circuit).eval x = true →
      (⟨pre ++ g' :: rest, out⟩ : Circuit).eval x = true := by
  have hw := wireLE_snoc (v := run pre x) (w := run pre x) rfl
    (fun _ h => h) hvalue
  have hs := run_mono rest (by simp) hw hrest out
  simpa only [Circuit.eval, Circuit.wires, run, List.foldl_append,
    List.foldl_cons] using hs

lemma signed_alias_monotone (pre rest : List Gate) (g : Gate) (out r : ℕ)
    (hm : Monotone2 ⟨pre ++ g :: rest, out⟩) :
    Monotone2 ⟨pre ++ ⟨.or, [r]⟩ :: rest, out⟩ := by
  intro a ha
  rcases List.mem_append.mp ha with hp | ht
  · exact hm a (List.mem_append_left _ hp)
  · rcases List.mem_cons.mp ht with he | ht
    · subst a
      simp
    · exact hm a (List.mem_append_right _ (List.mem_cons_of_mem _ ht))

lemma signed_alias_correct {n : ℕ} (G : SimpleGraph (Fin n))
    (pre rest : List Gate) (g : Gate) (out r : ℕ)
    (hm : Monotone2 ⟨pre ++ g :: rest, out⟩)
    (hcorrect : ∀ x : Fin n → Bool,
      (⟨pre ++ g :: rest, out⟩ : Circuit).eval (List.ofFn x) = edgeFunction G x)
    (hpositive : ∀ u v, G.Adj u v →
      g.op.eval (g.inputs.map fun i =>
        (run pre (List.ofFn (setInput ({u, v} : Set (Fin n))))).getD i false) = true →
      (run pre (List.ofFn (setInput ({u, v} : Set (Fin n))))).getD r false = true)
    (hnegative : ∀ s, Maximal G.IsIndepSet s →
      (run pre (List.ofFn (setInput s))).getD r false = true →
      g.op.eval (g.inputs.map fun i =>
        (run pre (List.ofFn (setInput s))).getD i false) = true) :
    ∀ x : Fin n → Bool,
      (⟨pre ++ ⟨.or, [r]⟩ :: rest, out⟩ : Circuit).eval (List.ofFn x) =
        edgeFunction G x := by
  have hm' := signed_alias_monotone pre rest g out r hm
  have hrest : ∀ a ∈ rest, a.op = .and ∨ a.op = .or := by
    intro a ha
    exact (hm a (List.mem_append_right _ (List.mem_cons_of_mem _ ha))).1
  apply signed_boundary_transfer G _ _
    (signed_circuit_support_monotone _ hm)
    (signed_circuit_support_monotone _ hm') hcorrect
  · intro u v huv
    apply signed_context_mono pre rest g ⟨.or, [r]⟩ out _ hrest
    simpa [GateOp.eval] using hpositive u v huv
  · intro s hs
    apply signed_context_mono pre rest ⟨.or, [r]⟩ g out _ hrest
    simpa [GateOp.eval] using hnegative s hs

lemma signed_boundary_delete {n : ℕ} (G : SimpleGraph (Fin n))
    (pre rest : List Gate) (g : Gate) (out r : ℕ)
    (hr : r < n + pre.length)
    (hm : Monotone2 ⟨pre ++ g :: rest, out⟩)
    (hcorrect : ∀ x : Fin n → Bool,
      (⟨pre ++ g :: rest, out⟩ : Circuit).eval (List.ofFn x) = edgeFunction G x)
    (hpositive : ∀ u v, G.Adj u v →
      g.op.eval (g.inputs.map fun i =>
        (run pre (List.ofFn (setInput ({u, v} : Set (Fin n))))).getD i false) = true →
      (run pre (List.ofFn (setInput ({u, v} : Set (Fin n))))).getD r false = true)
    (hnegative : ∀ s, Maximal G.IsIndepSet s →
      (run pre (List.ofFn (setInput s))).getD r false = true →
      g.op.eval (g.inputs.map fun i =>
        (run pre (List.ofFn (setInput s))).getD i false) = true) :
    ∃ D : Circuit, Monotone2 D ∧
      D.size + 1 = (⟨pre ++ g :: rest, out⟩ : Circuit).size ∧
      ∀ x : Fin n → Bool, D.eval (List.ofFn x) = edgeFunction G x := by
  have hm' := signed_alias_monotone pre rest g out r hm
  have hcorrect' := signed_alias_correct G pre rest g out r hm hcorrect hpositive hnegative
  have hwire (x : Fin n → Bool) :
      (Circuit.wires ⟨pre ++ ⟨.or, [r]⟩ :: rest, out⟩ (List.ofFn x)).getD
        (n + pre.length) false = (deletionRun pre (List.ofFn x)).getD r false := by
    have he := deletionRun_gate_value pre rest ⟨.or, [r]⟩ (List.ofFn x)
    simpa [Circuit.wires, deletionRun, GateOp.eval] using he
  obtain ⟨D, hD, hsize, hvalue⟩ :=
    delete_alias_gate_split n pre rest ⟨.or, [r]⟩ out r hr hm' hwire
  refine ⟨D, hD, ?_, fun x => (hvalue x).trans (hcorrect' x)⟩
  simpa [Circuit.size] using hsize

lemma minimal_signed_boundary_obstruction {n : ℕ} (G : SimpleGraph (Fin n))
    (pre rest : List Gate) (g : Gate) (out r : ℕ)
    (hr : r < n + pre.length)
    (hmin : IsMinimalMonoCircuit n ⟨pre ++ g :: rest, out⟩)
    (hcorrect : ∀ x : Fin n → Bool,
      (⟨pre ++ g :: rest, out⟩ : Circuit).eval (List.ofFn x) = edgeFunction G x)
    (hpositive : ∀ u v, G.Adj u v →
      g.op.eval (g.inputs.map fun i =>
        (run pre (List.ofFn (setInput ({u, v} : Set (Fin n))))).getD i false) = true →
      (run pre (List.ofFn (setInput ({u, v} : Set (Fin n))))).getD r false = true)
    (hnegative : ∀ s, Maximal G.IsIndepSet s →
      (run pre (List.ofFn (setInput s))).getD r false = true →
      g.op.eval (g.inputs.map fun i =>
        (run pre (List.ofFn (setInput s))).getD i false) = true) : False := by
  obtain ⟨D, hD, hsize, hvalue⟩ :=
    signed_boundary_delete G pre rest g out r hr hmin.1 hcorrect hpositive hnegative
  have heq : circuitFun n D = circuitFun n ⟨pre ++ g :: rest, out⟩ := by
    funext x
    exact (hvalue x).trans (hcorrect x).symm
  have hle := hmin.2 D hD heq
  omega

lemma signed_boundary_delete_any_index {n : ℕ} (G : SimpleGraph (Fin n))
    (pre rest : List Gate) (g : Gate) (out r : ℕ)
    (hm : Monotone2 ⟨pre ++ g :: rest, out⟩)
    (hcorrect : ∀ x : Fin n → Bool,
      (⟨pre ++ g :: rest, out⟩ : Circuit).eval (List.ofFn x) = edgeFunction G x)
    (hpositive : ∀ u v, G.Adj u v →
      g.op.eval (g.inputs.map fun i =>
        (run pre (List.ofFn (setInput ({u, v} : Set (Fin n))))).getD i false) = true →
      (run pre (List.ofFn (setInput ({u, v} : Set (Fin n))))).getD r false = true)
    (hnegative : ∀ s, Maximal G.IsIndepSet s →
      (run pre (List.ofFn (setInput s))).getD r false = true →
      g.op.eval (g.inputs.map fun i =>
        (run pre (List.ofFn (setInput s))).getD i false) = true) :
    ∃ D : Circuit, Monotone2 D ∧
      D.size + 1 = (⟨pre ++ g :: rest, out⟩ : Circuit).size ∧
      ∀ x : Fin n → Bool, D.eval (List.ofFn x) = edgeFunction G x := by
  by_cases hr : r < n + pre.length
  · exact signed_boundary_delete G pre rest g out r hr hm hcorrect hpositive hnegative
  · have hm' := signed_alias_monotone pre rest g out r hm
    have hcorrect' := signed_alias_correct G pre rest g out r hm hcorrect hpositive hnegative
    have hzero (x : Fin n → Bool) :
        (Circuit.wires ⟨pre ++ ⟨.or, [r]⟩ :: rest, out⟩ (List.ofFn x)).getD
          (n + pre.length) false = false := by
      have he := deletionRun_gate_value pre rest ⟨.or, [r]⟩ (List.ofFn x)
      have hz : (deletionRun pre (List.ofFn x)).getD r false = false :=
        List.getD_eq_default _ _ (by simp [deletionRun_length]; omega)
      have hw :
          (Circuit.wires ⟨pre ++ ⟨.or, [r]⟩ :: rest, out⟩ (List.ofFn x)).getD
            (n + pre.length) false = (deletionRun pre (List.ofFn x)).getD r false := by
        simpa [Circuit.wires, deletionRun, GateOp.eval] using he
      exact hw.trans hz
    obtain ⟨D, hD, hsize, hvalue⟩ :=
      delete_false_gate_split n pre rest ⟨.or, [r]⟩ out hm' hzero
    refine ⟨D, hD, ?_, fun x => (hvalue x).trans (hcorrect' x)⟩
    simpa [Circuit.size] using hsize

lemma minimal_gate_true_on_edge_pair {n : ℕ} (G : SimpleGraph (Fin n))
    (pre rest : List Gate) (g : Gate) (out : ℕ)
    (hmin : IsMinimalMonoCircuit n ⟨pre ++ g :: rest, out⟩)
    (hcorrect : ∀ x : Fin n → Bool,
      (⟨pre ++ g :: rest, out⟩ : Circuit).eval (List.ofFn x) = edgeFunction G x) :
    ∃ u v, G.Adj u v ∧
      g.op.eval (g.inputs.map fun i =>
        (run pre (List.ofFn (setInput ({u, v} : Set (Fin n))))).getD i false) = true := by
  classical
  by_contra hnone
  have hpositive : ∀ u v, G.Adj u v →
      g.op.eval (g.inputs.map fun i =>
        (run pre (List.ofFn (setInput ({u, v} : Set (Fin n))))).getD i false) = true →
      (run pre (List.ofFn (setInput ({u, v} : Set (Fin n))))).getD
        (n + pre.length) false = true := by
    intro u v huv htrue
    exact (hnone ⟨u, v, huv, htrue⟩).elim
  have hnegative : ∀ s, Maximal G.IsIndepSet s →
      (run pre (List.ofFn (setInput s))).getD (n + pre.length) false = true →
      g.op.eval (g.inputs.map fun i =>
        (run pre (List.ofFn (setInput s))).getD i false) = true := by
    intro s hs htrue
    have hz : (run pre (List.ofFn (setInput s))).getD (n + pre.length) false = false :=
      List.getD_eq_default _ _ (by simp [run_length])
    rw [hz] at htrue
    cases htrue
  obtain ⟨D, hD, hsize, hvalue⟩ := signed_boundary_delete_any_index G pre rest g out
    (n + pre.length) hmin.1 hcorrect hpositive hnegative
  have heq : circuitFun n D = circuitFun n ⟨pre ++ g :: rest, out⟩ := by
    funext x
    exact (hvalue x).trans (hcorrect x).symm
  have hle := hmin.2 D hD heq
  omega

-- Finite checks of local replacement and gate-index arguments.
open PEqualNP.CircuitLowerBounds

def reviewTriple : Circuit :=
  ⟨[⟨GateOp.and, [0, 1]⟩, ⟨GateOp.and, [3, 2]⟩], 5⟩

lemma reviewTriple_computes_empty_graph : ∀ x : Fin 3 → Bool,
    reviewTriple.eval (List.ofFn x) = false := by
  decide +kernel

lemma reviewTriple_large_witness :
    (reviewTriple.wires (List.ofFn (fun _ : Fin 3 => true))).getD 4 false = true := by
  decide +kernel

lemma reviewTriple_no_small_witness :
    ∀ S : Finset (Fin 3), S.card ≤ 2 →
      (reviewTriple.wires (List.ofFn (fun i => decide (i ∈ S)))).getD 4 false = false := by
  decide +kernel

lemma reviewTriple_earlier_witness :
    (reviewTriple.wires [true, true, false]).getD 3 false = true := by
  decide +kernel

def reviewForward : Circuit :=
  ⟨[⟨GateOp.or, [2]⟩, ⟨GateOp.and, [0, 0]⟩], 1⟩

def reviewRedirected : Circuit :=
  ⟨[⟨GateOp.or, [0]⟩], 1⟩

lemma review_forward_redirect_changes_value :
    reviewForward.eval [true] = false ∧ reviewRedirected.eval [true] = true := by
  decide +kernel

lemma review_forward_is_monotone2 : PEqualNP.MetaComplexity.Monotone2 reviewForward := by
  intro g hg
  simp only [reviewForward, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl <;>
    simp

def reviewP4 : Circuit :=
  ⟨[⟨GateOp.or, [0, 2]⟩, ⟨GateOp.or, [1, 3]⟩,
    ⟨GateOp.and, [4, 5]⟩, ⟨GateOp.or, [1, 2]⟩,
    ⟨GateOp.and, [6, 7]⟩], 8⟩

def reviewP4First : Circuit :=
  ⟨[⟨GateOp.or, [0, 2]⟩, ⟨GateOp.or, [1, 3]⟩,
    ⟨GateOp.or, [4]⟩, ⟨GateOp.or, [1, 2]⟩,
    ⟨GateOp.and, [6, 7]⟩], 8⟩

def reviewP4Second : Circuit :=
  ⟨[⟨GateOp.or, [0, 2]⟩, ⟨GateOp.or, [1, 3]⟩,
    ⟨GateOp.or, [5]⟩, ⟨GateOp.or, [1, 2]⟩,
    ⟨GateOp.and, [6, 7]⟩], 8⟩

lemma reviewP4_correct : ∀ x : Fin 4 → Bool,
    reviewP4.eval (List.ofFn x) = ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3)) := by
  decide +kernel

lemma reviewP4_bad :
    (reviewP4.wires [true, false, false, true]).getD 6 false = true ∧
    reviewP4.eval [true, false, false, true] = false := by
  decide +kernel

lemma reviewP4_bypass_first_wrong :
    reviewP4.eval [false, false, true, false] = false ∧
    reviewP4First.eval [false, false, true, false] = true := by
  decide +kernel

lemma reviewP4_bypass_second_wrong :
    reviewP4.eval [false, true, false, false] = false ∧
    reviewP4Second.eval [false, true, false, false] = true := by
  decide +kernel

def reviewEight (badGate : Gate) : Circuit :=
  ⟨[⟨GateOp.or, [3, 4]⟩, ⟨GateOp.or, [4, 6]⟩, ⟨GateOp.and, [8, 7]⟩,
    ⟨GateOp.or, [10, 1]⟩, ⟨GateOp.or, [6, 7]⟩, badGate,
    ⟨GateOp.or, [0, 13]⟩, ⟨GateOp.and, [14, 9]⟩, ⟨GateOp.or, [5, 12]⟩,
    ⟨GateOp.and, [11, 16]⟩, ⟨GateOp.or, [15, 17]⟩], 18⟩

lemma reviewEight_bypass_first_wrong :
    (reviewEight ⟨GateOp.and, [2, 12]⟩).eval [false, false, true, false, true, false, false, false] = false ∧
    (reviewEight ⟨GateOp.or, [2]⟩).eval [false, false, true, false, true, false, false, false] = true := by
  decide +kernel

lemma reviewEight_bypass_second_wrong :
    (reviewEight ⟨GateOp.and, [2, 12]⟩).eval [false, false, false, false, false, false, true, false] = false ∧
    (reviewEight ⟨GateOp.or, [12]⟩).eval [false, false, false, false, false, false, true, false] = true := by
  decide +kernel

-- Critical-row semantics for disjoint nontrivial stars.
abbrev reviewStarVertex {t : ℕ} (d : Fin t → ℕ) :=
  Σ i : Fin t, Fin (d i + 1)

def reviewStarGraph {t : ℕ} (d : Fin t → ℕ) : SimpleGraph (reviewStarVertex d) where
  Adj u v := u.1 = v.1 ∧
    ((u.2.val = 0 ∧ v.2.val ≠ 0) ∨ (u.2.val ≠ 0 ∧ v.2.val = 0))
  symm := ⟨by
    intro u v h
    rcases h with ⟨hc, h | h⟩
    · exact ⟨hc.symm, Or.inr ⟨h.2, h.1⟩⟩
    · exact ⟨hc.symm, Or.inl ⟨h.2, h.1⟩⟩⟩
  loopless := ⟨by
    intro u h
    rcases h with ⟨_, h | h⟩
    · exact h.2 h.1
    · exact h.1 h.2⟩

def reviewStarNegative {t : ℕ} (d : Fin t → ℕ) (b : Fin t → Bool)
    (v : reviewStarVertex d) : Bool :=
  if v.2.val = 0 then b v.1 else !(b v.1)

def reviewStarPositive {t : ℕ} (d : Fin t → ℕ) (b : Fin t → Bool)
    (v : reviewStarVertex d) : reviewStarVertex d → Bool :=
  Function.update (reviewStarNegative d b) v true

lemma reviewStar_negative_true_iff {t : ℕ} (d : Fin t → ℕ) (b : Fin t → Bool)
    (v : reviewStarVertex d) :
    reviewStarNegative d b v = true ↔ b v.1 = decide (v.2.val = 0) := by
  by_cases h : v.2.val = 0 <;> cases hb : b v.1 <;>
    simp [reviewStarNegative, h, hb]

lemma reviewStar_negative_independent {t : ℕ} (d : Fin t → ℕ) (b : Fin t → Bool)
    (u v : reviewStarVertex d) (adj : (reviewStarGraph d).Adj u v) :
    ¬ (reviewStarNegative d b u = true ∧ reviewStarNegative d b v = true) := by
  rintro ⟨hu, hv⟩
  rcases adj with ⟨comp, ⟨hu0, hv0⟩ | ⟨hu0, hv0⟩⟩ <;>
    cases hb : b v.1 <;> simp [reviewStarNegative, comp, hu0, hv0, hb] at hu hv

lemma reviewStar_update_preserves_true {α : Type*} [DecidableEq α]
    (x : α → Bool) (v w : α) (h : x w = true) :
    Function.update x v true w = true := by
  by_cases hw : w = v
  · subst w
    simp
  · simp [Function.update_of_ne hw, h]

lemma reviewStar_negative_le_positive {t : ℕ} (d : Fin t → ℕ) (b : Fin t → Bool)
    (v w : reviewStarVertex d) (h : reviewStarNegative d b w = true) :
    reviewStarPositive d b v w = true :=
  reviewStar_update_preserves_true _ _ _ h

lemma reviewStar_excluded_makes_positive {t : ℕ} (d : Fin t → ℕ)
    (nonempty : ∀ i, 0 < d i) (b : Fin t → Bool) (v : reviewStarVertex d)
    (excluded : reviewStarNegative d b v = false) :
    ∃ u w : reviewStarVertex d, (reviewStarGraph d).Adj u w ∧
      reviewStarPositive d b v u = true ∧ reviewStarPositive d b v w = true := by
  rcases v with ⟨i, a⟩
  by_cases ha : a.val = 0
  · have hb : b i = false := by simpa [reviewStarNegative, ha] using excluded
    let leaf : reviewStarVertex d := ⟨i, ⟨1, by have := nonempty i; omega⟩⟩
    refine ⟨⟨i, a⟩, leaf, ?_, by simp [reviewStarPositive], ?_⟩
    · exact ⟨rfl, Or.inl ⟨ha, by simp [leaf]⟩⟩
    · apply reviewStar_negative_le_positive
      simp [reviewStarNegative, leaf, hb]
  · have hb : b i = true := by simpa [reviewStarNegative, ha] using excluded
    let center : reviewStarVertex d := ⟨i, 0⟩
    refine ⟨⟨i, a⟩, center, ?_, by simp [reviewStarPositive], ?_⟩
    · exact ⟨rfl, Or.inr ⟨ha, rfl⟩⟩
    · apply reviewStar_negative_le_positive
      simp [reviewStarNegative, center, hb]

lemma reviewStar_vertex_eq {t : ℕ} (d : Fin t → ℕ)
    (u v : reviewStarVertex d) (comp : u.1 = v.1) (value : u.2.val = v.2.val) : u = v := by
  rcases u with ⟨i, a⟩
  rcases v with ⟨j, b⟩
  dsimp at comp value
  subst j
  have same : a = b := Fin.ext value
  subst b
  rfl

def reviewStarPacking {t : ℕ} (d : Fin t → ℕ) (S : Finset (reviewStarVertex d)) : Prop :=
  ∀ u ∈ S, ∀ v ∈ S, u ≠ v →
    ¬ (reviewStarGraph d).Adj u v ∧
      ∀ w, ¬ ((reviewStarGraph d).Adj u w ∧ (reviewStarGraph d).Adj v w)

lemma reviewStar_packing_component_injective {t : ℕ} (d : Fin t → ℕ)
    (S : Finset (reviewStarVertex d)) (packed : reviewStarPacking d S) :
    ∀ u ∈ S, ∀ v ∈ S, u.1 = v.1 → u = v := by
  intro u hu v hv comp
  by_contra different
  have constraints := packed u hu v hv different
  by_cases hu0 : u.2.val = 0
  · have hv0 : v.2.val ≠ 0 := by
      intro hv0
      apply different
      exact reviewStar_vertex_eq d u v comp (hu0.trans hv0.symm)
    exact constraints.1 ⟨comp, Or.inl ⟨hu0, hv0⟩⟩
  · by_cases hv0 : v.2.val = 0
    · exact constraints.1 ⟨comp, Or.inr ⟨hu0, hv0⟩⟩
    · let w : reviewStarVertex d := ⟨u.1, 0⟩
      exact constraints.2 w ⟨⟨rfl, Or.inr ⟨hu0, rfl⟩⟩,
        ⟨comp.symm, Or.inr ⟨hv0, rfl⟩⟩⟩

def reviewStarClause {t : ℕ} (d : Fin t → ℕ) (S : Finset (reviewStarVertex d))
    (x : reviewStarVertex d → Bool) : Bool :=
  decide (∃ v ∈ S, x v = true)

lemma reviewStar_clause_false_iff {t : ℕ} (d : Fin t → ℕ)
    (S : Finset (reviewStarVertex d)) (x : reviewStarVertex d → Bool) :
    reviewStarClause d S x = false ↔ ∀ v ∈ S, x v = false := by
  constructor
  · intro h v hv
    cases e : x v with
    | false => rfl
    | true =>
      have active : reviewStarClause d S x = true := decide_eq_true ⟨v, hv, e⟩
      rw [h] at active
      cases active
  · intro h
    exact decide_eq_false (by
      rintro ⟨v, hv, active⟩
      rw [h v hv] at active
      cases active)

lemma reviewStar_clause_update_separation {t : ℕ} (d : Fin t → ℕ)
    (S : Finset (reviewStarVertex d)) (x : reviewStarVertex d → Bool)
    (v : reviewStarVertex d) :
    (reviewStarClause d S (Function.update x v true) = true ∧ reviewStarClause d S x = false) ↔
      v ∈ S ∧ ∀ w ∈ S, x w = false := by
  constructor
  · rintro ⟨positive, negative⟩
    have all := (reviewStar_clause_false_iff d S x).mp negative
    have hit : ∃ w ∈ S, Function.update x v true w = true := of_decide_eq_true positive
    obtain ⟨w, hw, active⟩ := hit
    refine ⟨?_, all⟩
    by_cases same : w = v
    · simpa [same] using hw
    · simp [Function.update_of_ne same, all w hw] at active
  · rintro ⟨mem, all⟩
    refine ⟨decide_eq_true ⟨v, mem, by simp⟩, ?_⟩
    exact (reviewStar_clause_false_iff d S x).mpr all

lemma reviewStar_clause_row_separation {t : ℕ} (d : Fin t → ℕ)
    (S : Finset (reviewStarVertex d)) (b : Fin t → Bool) (v : reviewStarVertex d) :
    (reviewStarClause d S (reviewStarPositive d b v) = true ∧
      reviewStarClause d S (reviewStarNegative d b) = false) ↔
      v ∈ S ∧ ∀ w ∈ S, reviewStarNegative d b w = false :=
  reviewStar_clause_update_separation d S (reviewStarNegative d b) v

lemma reviewStar_negative_false_iff {t : ℕ} (d : Fin t → ℕ) (b : Fin t → Bool)
    (v : reviewStarVertex d) :
    reviewStarNegative d b v = false ↔ b v.1 = !(decide (v.2.val = 0)) := by
  by_cases h : v.2.val = 0 <;> cases hb : b v.1 <;>
    simp [reviewStarNegative, h, hb]

lemma reviewStar_packing_subtype_injective {t : ℕ} (d : Fin t → ℕ)
    (S : Finset (reviewStarVertex d)) (packed : reviewStarPacking d S) :
    Function.Injective (fun v : {v // v ∈ S} => v.val.1) := by
  intro u v comp
  apply Subtype.ext
  exact reviewStar_packing_component_injective d S packed u.val u.property v.val v.property comp

lemma reviewStar_negative_has_no_edge {t : ℕ} (d : Fin t → ℕ) (b : Fin t → Bool) :
    ¬ ∃ u v : reviewStarVertex d, (reviewStarGraph d).Adj u v ∧
      reviewStarNegative d b u = true ∧ reviewStarNegative d b v = true := by
  rintro ⟨u, v, adj, hu, hv⟩
  exact reviewStar_negative_independent d b u v adj ⟨hu, hv⟩

-- Input support and Boolean-cube counting for the star bound.
namespace HelperSupport

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

variable {n : ℕ}

lemma getD_snoc_ne {α : Type} (L : List α) (S d : α) (j : ℕ) (h : j ≠ L.length) :
    (L ++ [S]).getD j d = L.getD j d := by
  by_cases hj : j < L.length
  · exact List.getD_append _ _ _ _ hj
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

lemma getD_snoc_eq {α : Type} (L : List α) (S d : α) : (L ++ [S]).getD L.length d = S := by
  simp

/-- The support of a gate: the union of the supports of the wires it reads. -/
def gateSupp (L : List (Finset (Fin n))) (g : Gate) : Finset (Fin n) :=
  (g.inputs.map fun a => L.getD a ∅).foldr (· ∪ ·) ∅

lemma mem_foldr_union (l : List ℕ) (F : ℕ → Finset (Fin n)) (i : Fin n) :
    i ∈ (l.map F).foldr (· ∪ ·) ∅ ↔ ∃ a ∈ l, i ∈ F a := by
  induction l with
  | nil => simp
  | cons b l ih => simp [ih]

lemma mem_gateSupp (L : List (Finset (Fin n))) (g : Gate) (i : Fin n) :
    i ∈ gateSupp L g ↔ ∃ a ∈ g.inputs, i ∈ L.getD a ∅ :=
  mem_foldr_union _ _ _

/-- The supports of all wires, starting from the supports `L` of the wires present. -/
def suppsFrom (gs : List Gate) (L : List (Finset (Fin n))) : List (Finset (Fin n)) :=
  gs.foldl (fun L g => L ++ [gateSupp L g]) L

/-- The supports of the input wires: input `i` has support `{i}`. -/
def inputSupps (n : ℕ) : List (Finset (Fin n)) := List.ofFn fun i : Fin n => {i}

/-- Wire lists `w`, `w'` (for the inputs `x`, `y`) agree on every wire whose support `x` and
  `y` agree on. -/
def Agree (x y : Fin n → Bool) (L : List (Finset (Fin n))) (w w' : List Bool) : Prop :=
  L.length = w.length ∧ w.length = w'.length ∧
    ∀ j : ℕ, (∀ i ∈ L.getD j ∅, x i = y i) → w.getD j false = w'.getD j false

lemma agree_wiresFrom (x y : Fin n → Bool) (gs : List Gate) :
    ∀ (L : List (Finset (Fin n))) (w w' : List Bool), Agree x y L w w' →
      Agree x y (suppsFrom gs L) (wiresFrom gs w) (wiresFrom gs w') := by
  induction gs with
  | nil => intro L w w' h; exact h
  | cons g gs ih =>
    intro L w w' h
    obtain ⟨h1, h2, h3⟩ := h
    apply ih (L ++ [gateSupp L g])
      (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
      (w' ++ [g.op.eval (g.inputs.map fun i => w'.getD i false)])
    refine ⟨by simp [h1], by simp [h2], ?_⟩
    intro j hj
    by_cases hjl : j = L.length
    · subst hjl
      rw [getD_snoc_eq] at hj
      rw [h1, getD_snoc_eq, h2, getD_snoc_eq]
      congr 1
      apply List.map_congr_left
      intro a ha
      exact h3 a (fun i hi => hj i ((mem_gateSupp L g i).2 ⟨a, ha, hi⟩))
    · rw [getD_snoc_ne _ _ _ _ hjl] at hj
      rw [getD_snoc_ne _ _ _ _ (by omega), getD_snoc_ne _ _ _ _ (by omega)]
      exact h3 j hj

lemma agree_inputs (x y : Fin n → Bool) :
    Agree x y (inputSupps n) (List.ofFn x) (List.ofFn y) := by
  refine ⟨by simp [inputSupps], by simp, ?_⟩
  intro j hj
  by_cases hjn : j < n
  · have hx : x ⟨j, hjn⟩ = y ⟨j, hjn⟩ := hj _ (by simp [inputSupps, hjn])
    simp [hjn, hx]
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]

/-- Any set `W` of wires has a joint support of size at most `t + |W|`. -/
def Cnt (t : ℕ) (L : List (Finset (Fin n))) : Prop :=
  ∀ W : Finset ℕ, (W.biUnion fun j => L.getD j ∅).card ≤ t + W.card

lemma cnt_inputs : Cnt 0 (inputSupps n) := by
  intro W
  refine le_trans Finset.card_biUnion_le ?_
  rw [zero_add, Finset.card_eq_sum_ones]
  apply Finset.sum_le_sum
  intro j _
  by_cases hjn : j < n
  · simp [inputSupps, hjn]
  · rw [List.getD_eq_default _ _ (by simp [inputSupps]; omega)]; simp

lemma cnt_step (t : ℕ) (L : List (Finset (Fin n))) (g : Gate) (hg : g.inputs.length ≤ 2)
    (h : Cnt t L) : Cnt (t + 1) (L ++ [gateSupp L g]) := by
  intro W
  by_cases hW : L.length ∈ W
  · have hsub : (W.biUnion fun j => (L ++ [gateSupp L g]).getD j ∅)
        ⊆ ((W.erase L.length ∪ g.inputs.toFinset).biUnion fun j => L.getD j ∅) := by
      intro i hi
      rw [Finset.mem_biUnion] at hi ⊢
      obtain ⟨j, hjW, hij⟩ := hi
      by_cases hjl : j = L.length
      · subst hjl
        rw [getD_snoc_eq] at hij
        obtain ⟨a, ha, hia⟩ := (mem_gateSupp L g i).1 hij
        exact ⟨a, Finset.mem_union_right _ (List.mem_toFinset.2 ha), hia⟩
      · rw [getD_snoc_ne _ _ _ _ hjl] at hij
        exact ⟨j, Finset.mem_union_left _ (Finset.mem_erase.2 ⟨hjl, hjW⟩), hij⟩
    have hc1 : (W.erase L.length ∪ g.inputs.toFinset).card ≤ (W.card - 1) + 2 := by
      refine le_trans (Finset.card_union_le _ _) ?_
      rw [Finset.card_erase_of_mem hW]
      exact Nat.add_le_add_left (le_trans (List.toFinset_card_le _) hg) _
    have hWpos : 1 ≤ W.card := Finset.card_pos.2 ⟨_, hW⟩
    have := h (W.erase L.length ∪ g.inputs.toFinset)
    have := Finset.card_le_card hsub
    omega
  · have heq : (W.biUnion fun j => (L ++ [gateSupp L g]).getD j ∅)
        = (W.biUnion fun j => L.getD j ∅) := by
      apply Finset.biUnion_congr rfl
      intro j hj
      exact getD_snoc_ne _ _ _ _ (fun e => hW (e ▸ hj))
    rw [heq]
    have := h W
    omega

lemma cnt_suppsFrom (gs : List Gate) : ∀ (t : ℕ) (L : List (Finset (Fin n))),
    (∀ g ∈ gs, g.inputs.length ≤ 2) → Cnt t L → Cnt (t + gs.length) (suppsFrom gs L) := by
  induction gs with
  | nil => intro t L _ h; exact h
  | cons g gs ih =>
    intro t L hok h
    have := ih (t + 1) (L ++ [gateSupp L g]) (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
      (cnt_step t L g (hok g List.mem_cons_self) h)
    rw [List.length_cons, show t + (gs.length + 1) = t + 1 + gs.length by omega]
    exact this


def SeenInputs (L : List (Finset (Fin n))) (gs : List Gate) : Prop :=
  ∀ w : ℕ, ∀ i : Fin n, i ∈ L.getD w ∅ →
    w = i.val ∨ ∃ g ∈ gs, i.val ∈ g.inputs

lemma seen_inputs : SeenInputs (inputSupps n) [] := by
  intro w i hi
  by_cases hw : w < n
  · have hiw : i = ⟨w,hw⟩ := by simpa [inputSupps,hw] using hi
    exact Or.inl (congrArg Fin.val hiw).symm
  · simp [inputSupps,hw] at hi

lemma seen_step (L : List (Finset (Fin n))) (gs : List Gate) (g : Gate)
    (hseen : SeenInputs L gs) : SeenInputs (L ++ [gateSupp L g]) (gs ++ [g]) := by
  intro w i hi
  by_cases hw : w = L.length
  · subst w
    rw [getD_snoc_eq] at hi
    obtain ⟨a,ha,hia⟩ := (mem_gateSupp L g i).mp hi
    rcases hseen a i hia with heq | ⟨q,hq,hinput⟩
    · right
      exact ⟨g,by simp,heq ▸ ha⟩
    · exact Or.inr ⟨q,List.mem_append_left _ hq,hinput⟩
  · rw [getD_snoc_ne _ _ _ _ hw] at hi
    rcases hseen w i hi with heq | ⟨q,hq,hinput⟩
    · exact Or.inl heq
    · exact Or.inr ⟨q,List.mem_append_left _ hq,hinput⟩

lemma seen_suppsFrom (gs : List Gate) :
    ∀ (L : List (Finset (Fin n))) (pre : List Gate), SeenInputs L pre →
      SeenInputs (suppsFrom gs L) (pre ++ gs) := by
  induction gs with
  | nil => intro L pre h; simpa [suppsFrom] using h
  | cons g gs ih =>
    intro L pre h
    have hnext := ih (L ++ [gateSupp L g]) (pre ++ [g]) (seen_step L pre g h)
    simpa [suppsFrom,List.foldl_cons,List.append_assoc] using hnext

lemma output_support (m : ℕ) (C : Circuit)
    (hfan : ∀ g ∈ C.gates, g.inputs.length ≤ 2) :
    ∃ R : Finset (Fin m), R.card ≤ C.size + 1 ∧
      (∀ x y : Fin m → Bool, (∀ i ∈ R, x i = y i) →
        C.eval (List.ofFn x) = C.eval (List.ofFn y)) ∧
      ∀ i ∈ R, C.output = i.val ∨ ∃ g ∈ C.gates, i.val ∈ g.inputs := by
  let R := (suppsFrom C.gates (inputSupps m)).getD C.output ∅
  refine ⟨R,?_,?_,?_⟩
  · have bound := cnt_suppsFrom C.gates 0 (inputSupps m) hfan cnt_inputs {C.output}
    simpa only [Finset.singleton_biUnion,Finset.card_singleton,zero_add,Circuit.size] using bound
  · intro x y hxy
    exact (agree_wiresFrom x y C.gates _ _ _ (agree_inputs x y)).2.2 C.output hxy
  · intro i hi
    have hseen := seen_suppsFrom C.gates (inputSupps m) [] seen_inputs
    exact hseen C.output i hi

end HelperSupport

namespace CubeCounts

def prescribed {k : ℕ} (T : Finset (Fin k)) (b : Fin k → Bool) :
    Finset (Fin k → Bool) :=
  Finset.univ.filter fun y => ∀ i ∈ T, y i = b i

def prescribedEquiv {k : ℕ} (T : Finset (Fin k)) (b : Fin k → Bool) :
    ↥(prescribed T b) ≃ (↥(Tᶜ) → Bool) where
  toFun y i := y.val i.val
  invFun z := ⟨fun i => if hi : i ∈ T then b i else z ⟨i, by simpa using hi⟩, by
    simp only [prescribed, Finset.mem_filter, Finset.mem_univ, true_and]
    intro i hi
    simp [hi]⟩
  left_inv y := by
    apply Subtype.ext
    funext i
    by_cases hi : i ∈ T
    · have hy := (Finset.mem_filter.mp y.property).2 i hi
      simp [hi, hy]
    · simp [hi]
  right_inv z := by
    funext i
    have hi : i.val ∉ T := Finset.mem_compl.mp i.property
    simp [hi]

lemma prescribed_bits_card {k : ℕ} (T : Finset (Fin k)) (b : Fin k → Bool) :
    (prescribed T b).card = 2 ^ (k - T.card) := by
  calc
    (prescribed T b).card = Fintype.card ↥(prescribed T b) := (Fintype.card_coe _).symm
    _ = Fintype.card (↥(Tᶜ) → Bool) := Fintype.card_congr (prescribedEquiv T b)
    _ = 2 ^ (k - T.card) := by rw [Fintype.card_fun]; simp

lemma bool_ne_iff_eq_not (a b : Bool) : a ≠ b ↔ a = !b := by
  cases a <;> cases b <;> decide

def clauseConstraints {V : Type*} {k : ℕ} (S : Finset V)
    (coord : V → Fin k) (sign : V → Bool) : Finset (Fin k → Bool) :=
  Finset.univ.filter fun y => ∀ v ∈ S, y (coord v) ≠ sign v

lemma packed_clause_constraints_card {V : Type*} {k : ℕ} (S : Finset V)
    (coord : V → Fin k) (sign : V → Bool) (hinj : Set.InjOn coord (↑S : Set V)) :
    (clauseConstraints S coord sign).card = 2 ^ (k - S.card) := by
  classical
  let b : Fin k → Bool := fun i =>
    if hi : ∃ v ∈ S, coord v = i then !(sign (Classical.choose hi)) else false
  have hb : ∀ v ∈ S, b (coord v) = !(sign v) := by
    intro v hv
    have he : ∃ u ∈ S, coord u = coord v := ⟨v, hv, rfl⟩
    have hc : Classical.choose he = v :=
      hinj (Classical.choose_spec he).1 hv (Classical.choose_spec he).2
    simp only [b, dite_eq_left he, hc]
  have heq : clauseConstraints S coord sign = prescribed (S.image coord) b := by
    ext y
    simp only [clauseConstraints, prescribed, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro hy i hi
      obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hi
      rw [hb v hv]
      exact (bool_ne_iff_eq_not _ _).mp (hy v hv)
    · intro hy v hv
      apply (bool_ne_iff_eq_not _ _).mpr
      rw [← hb v hv]
      exact hy (coord v) (Finset.mem_image.mpr ⟨v, hv, rfl⟩)
  rw [heq, prescribed_bits_card, Finset.card_image_of_injOn hinj]

lemma one_coordinate_constraints_card {k : ℕ} (i : Fin k) (sign : Bool) :
    (Finset.univ.filter fun y : Fin k → Bool => y i ≠ sign).card = 2 ^ (k - 1) := by
  have h := packed_clause_constraints_card ({i} : Finset (Fin k)) id
    (fun _ => sign) (fun _ _ _ _ he => he)
  simpa [clauseConstraints] using h

lemma clause_capacity_bound (k r : ℕ) (hr : r ≤ k) :
    r * 2 ^ (k - r) ≤ 2 ^ (k - 1) := by
  cases r with
  | zero => simp
  | succ r =>
    have hpow : r + 1 ≤ 2 ^ r := by
      have h : r < 2 ^ r := Nat.lt_two_pow_self
      omega
    calc
      (r + 1) * 2 ^ (k - (r + 1)) ≤ 2 ^ r * 2 ^ (k - (r + 1)) :=
        Nat.mul_le_mul_right _ hpow
      _ = 2 ^ (r + (k - (r + 1))) := (pow_add _ _ _).symm
      _ = 2 ^ (k - 1) := by congr 1; omega

lemma packed_clause_capacity {V : Type*} {k : ℕ} (S : Finset V)
    (coord : V → Fin k) (sign : V → Bool) (hinj : Set.InjOn coord (↑S : Set V)) :
    S.card * (clauseConstraints S coord sign).card ≤ 2 ^ (k - 1) := by
  rw [packed_clause_constraints_card S coord sign hinj]
  apply clause_capacity_bound
  have h := Finset.card_le_univ (S.image coord)
  rw [Finset.card_image_of_injOn hinj, Fintype.card_fin] at h
  exact h

end CubeCounts


namespace ForestRows

variable {V : Type*} [Fintype V] [DecidableEq V] {k : ℕ}

def negative (coord : V → Fin k) (sign : V → Bool) (y : Fin k → Bool) : V → Bool :=
  fun v => decide (y (coord v) = sign v)

def positive (coord : V → Fin k) (sign : V → Bool) (v : V) (y : Fin k → Bool) : V → Bool :=
  fun w => negative coord sign y w || decide (w = v)

def clause (S : Finset V) (x : V → Bool) : Bool :=
  decide (∃ w ∈ S, x w = true)

omit [Fintype V] in
lemma clause_positive (coord : V → Fin k) (sign : V → Bool) (S : Finset V)
    (v : V) (y : Fin k → Bool) :
    clause S (positive coord sign v y) = true ↔
      clause S (negative coord sign y) = true ∨ v ∈ S := by
  simp only [clause, positive, decide_eq_true_eq, Bool.or_eq_true]
  constructor
  · rintro ⟨w, hw, h | h⟩
    · exact Or.inl ⟨w, hw, h⟩
    · exact Or.inr (h ▸ hw)
  · rintro (⟨w, hw, h⟩ | h)
    · exact ⟨w, hw, Or.inl h⟩
    · exact ⟨v, h, Or.inr rfl⟩

omit [Fintype V] [DecidableEq V] in
lemma clause_negative_false (coord : V → Fin k) (sign : V → Bool) (S : Finset V)
    (y : Fin k → Bool) :
    clause S (negative coord sign y) = false ↔ ∀ w ∈ S, y (coord w) ≠ sign w := by
  simp [clause, negative]

def adjacentRows (coord : V → Fin k) (sign : V → Bool) : Finset (V × (Fin k → Bool)) :=
  Finset.univ.filter fun p => negative coord sign p.2 p.1 = false

def separatedRows (coord : V → Fin k) (sign : V → Bool) (S : Finset V) :
    Finset (V × (Fin k → Bool)) :=
  (adjacentRows coord sign).filter fun p =>
    clause S (positive coord sign p.1 p.2) = true ∧
      clause S (negative coord sign p.2) = false

lemma separatedRows_eq_product (coord : V → Fin k) (sign : V → Bool) (S : Finset V) :
    separatedRows coord sign S =
      S ×ˢ (Finset.univ.filter fun y : Fin k → Bool => ∀ w ∈ S, y (coord w) ≠ sign w) := by
  ext p
  simp only [separatedRows, adjacentRows, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_product, clause_positive, clause_negative_false]
  constructor
  · rintro ⟨_, h | h, hn⟩
    · obtain ⟨w, hw, hwy⟩ := of_decide_eq_true h
      exact (hn w hw (of_decide_eq_true hwy)).elim
    · exact ⟨h, hn⟩
  · rintro ⟨hv, hn⟩
    refine ⟨?_, Or.inr hv, hn⟩
    simpa [negative] using hn p.1 hv

lemma separatedRows_card (coord : V → Fin k) (sign : V → Bool) (S : Finset V) :
    (separatedRows coord sign S).card =
      S.card * (Finset.univ.filter fun y : Fin k → Bool =>
        ∀ w ∈ S, y (coord w) ≠ sign w).card := by
  rw [separatedRows_eq_product, Finset.card_product]

omit [DecidableEq V] in
lemma adjacentRows_card_sum (coord : V → Fin k) (sign : V → Bool) :
    (adjacentRows coord sign).card =
      ∑ v : V, (Finset.univ.filter fun y : Fin k → Bool =>
        y (coord v) ≠ sign v).card := by
  simp only [adjacentRows, negative, Finset.card_eq_sum_ones, Finset.sum_filter,
    Fintype.sum_prod_type, decide_eq_false_iff_not]

omit [Fintype V] in
lemma output_change_separated {ι : Type*} (coord : V → Fin k) (sign : V → Bool)
    (A : ι → Finset V) (F : (ι → Bool) → Bool) (v : V) (y : Fin k → Bool)
    (hchange : F (fun i => clause (A i) (positive coord sign v y)) ≠
      F (fun i => clause (A i) (negative coord sign y))) :
    ∃ i, clause (A i) (positive coord sign v y) = true ∧
      clause (A i) (negative coord sign y) = false := by
  classical
  by_contra h
  push Not at h
  apply hchange
  congr 1
  funext i
  by_cases hn : clause (A i) (negative coord sign y) = true
  · rw [hn, (clause_positive coord sign (A i) v y).mpr (Or.inl hn)]
  · have hn' : clause (A i) (negative coord sign y) = false := by
      cases hb : clause (A i) (negative coord sign y) <;> simp_all
    have hp : clause (A i) (positive coord sign v y) = false := by
      cases hb : clause (A i) (positive coord sign v y) <;> simp_all
    rw [hp, hn']

lemma adjacentRows_covered_of_separation {ι : Type*} [Fintype ι] [DecidableEq ι]
    (coord : V → Fin k) (sign : V → Bool) (A : ι → Finset V)
    (hsep : ∀ p ∈ adjacentRows coord sign, ∃ i,
      clause (A i) (positive coord sign p.1 p.2) = true ∧
        clause (A i) (negative coord sign p.2) = false) :
    adjacentRows coord sign ⊆ Finset.univ.biUnion (separatedRows coord sign ∘ A) := by
  intro p hp
  obtain ⟨i, hi⟩ := hsep p hp
  exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, Finset.mem_filter.mpr ⟨hp, hi⟩⟩

lemma adjacentRows_covered {ι : Type*} [Fintype ι] [DecidableEq ι]
    (coord : V → Fin k) (sign : V → Bool) (A : ι → Finset V)
    (F : (ι → Bool) → Bool)
    (hchange : ∀ p ∈ adjacentRows coord sign,
      F (fun i => clause (A i) (positive coord sign p.1 p.2)) ≠
        F (fun i => clause (A i) (negative coord sign p.2))) :
    adjacentRows coord sign ⊆ Finset.univ.biUnion (separatedRows coord sign ∘ A) := by
  apply adjacentRows_covered_of_separation
  intro p hp
  exact output_change_separated coord sign A F p.1 p.2 (hchange p hp)

end ForestRows

namespace ForestRows

variable {V : Type*} [Fintype V] [DecidableEq V] {k : ℕ}

omit [DecidableEq V] in
lemma adjacentRows_card (coord : V → Fin k) (sign : V → Bool) :
    (adjacentRows coord sign).card = Fintype.card V * 2 ^ (k - 1) := by
  rw [adjacentRows_card_sum]
  simp_rw [CubeCounts.one_coordinate_constraints_card]
  simp

lemma separatedRows_capacity (coord : V → Fin k) (sign : V → Bool) (S : Finset V)
    (hinj : Set.InjOn coord (↑S : Set V)) :
    (separatedRows coord sign S).card ≤ 2 ^ (k - 1) := by
  rw [separatedRows_card]
  have heq : (Finset.univ.filter fun y : Fin k → Bool =>
      ∀ w ∈ S, y (coord w) ≠ sign w) = CubeCounts.clauseConstraints S coord sign := by
    ext y
    simp [CubeCounts.clauseConstraints]
  rw [heq]
  exact CubeCounts.packed_clause_capacity S coord sign hinj

lemma packing_sources_lower_bound {ι : Type*} [Fintype ι] [DecidableEq ι]
    (coord : V → Fin k) (sign : V → Bool) (A : ι → Finset V)
    (hpacking : ∀ i, Set.InjOn coord (↑(A i) : Set V))
    (hsep : ∀ p ∈ adjacentRows coord sign, ∃ i,
      clause (A i) (positive coord sign p.1 p.2) = true ∧
        clause (A i) (negative coord sign p.2) = false) :
    Fintype.card V ≤ Fintype.card ι := by
  have hcover := adjacentRows_covered_of_separation coord sign A hsep
  have hcount : Fintype.card V * 2 ^ (k - 1) ≤ Fintype.card ι * 2 ^ (k - 1) := by
    calc
      Fintype.card V * 2 ^ (k - 1) = (adjacentRows coord sign).card :=
        (adjacentRows_card coord sign).symm
      _ ≤ (Finset.univ.biUnion (separatedRows coord sign ∘ A)).card :=
        Finset.card_le_card hcover
      _ ≤ ∑ i : ι, (separatedRows coord sign (A i)).card :=
        Finset.card_biUnion_le
      _ ≤ ∑ _i : ι, 2 ^ (k - 1) := by
        exact Finset.sum_le_sum fun i _ => separatedRows_capacity coord sign (A i) (hpacking i)
      _ = Fintype.card ι * 2 ^ (k - 1) := by simp
  have hp : 0 < 2 ^ (k - 1) := Nat.pow_pos (by decide)
  by_contra h
  have hlt := Nat.mul_lt_mul_of_pos_right (Nat.lt_of_not_ge h) hp
  omega

lemma packing_factorization_lower_bound {ι : Type*} [Fintype ι] [DecidableEq ι]
    (coord : V → Fin k) (sign : V → Bool) (A : ι → Finset V)
    (hpacking : ∀ i, Set.InjOn coord (↑(A i) : Set V))
    (F : (ι → Bool) → Bool)
    (hchange : ∀ p ∈ adjacentRows coord sign,
      F (fun i => clause (A i) (positive coord sign p.1 p.2)) ≠
        F (fun i => clause (A i) (negative coord sign p.2))) :
    Fintype.card V ≤ Fintype.card ι := by
  apply packing_sources_lower_bound coord sign A hpacking
  intro p hp
  exact output_change_separated coord sign A F p.1 p.2 (hchange p hp)

end ForestRows

def reviewStarCoord {t : ℕ} (d : Fin t → ℕ) (v : reviewStarVertex d) : Fin t := v.1

def reviewStarSign {t : ℕ} (d : Fin t → ℕ) (v : reviewStarVertex d) : Bool :=
  decide (v.2.val = 0)

lemma reviewStar_forest_negative_eq {t : ℕ} (d : Fin t → ℕ) (b : Fin t → Bool) :
    ForestRows.negative (reviewStarCoord d) (reviewStarSign d) b = reviewStarNegative d b := by
  funext v
  by_cases h : v.2.val = 0 <;> cases hb : b v.1 <;>
    simp [ForestRows.negative, reviewStarCoord, reviewStarSign, reviewStarNegative, h, hb]

lemma reviewStar_forest_positive_eq {t : ℕ} (d : Fin t → ℕ) (b : Fin t → Bool)
    (v : reviewStarVertex d) :
    ForestRows.positive (reviewStarCoord d) (reviewStarSign d) v b = reviewStarPositive d b v := by
  funext w
  change (ForestRows.negative (reviewStarCoord d) (reviewStarSign d) b w || decide (w = v)) = _
  rw [reviewStar_forest_negative_eq]
  by_cases same : w = v
  · subst w
    simp [reviewStarPositive]
  · simp [reviewStarPositive, same]

lemma reviewStar_forest_clause_eq {t : ℕ} (d : Fin t → ℕ)
    (S : Finset (reviewStarVertex d)) (x : reviewStarVertex d → Bool) :
    ForestRows.clause S x = reviewStarClause d S x := rfl

lemma reviewStar_factorization_lower_bound {t : ℕ} (d : Fin t → ℕ)
    [DecidableRel (reviewStarGraph d).Adj] (nonempty : ∀ i, 0 < d i)
    {ι : Type*} [Fintype ι] [DecidableEq ι] (A : ι → Finset (reviewStarVertex d))
    (packed : ∀ i, reviewStarPacking d (A i)) (F : (ι → Bool) → Bool)
    (correct : ∀ x : reviewStarVertex d → Bool,
      F (fun i => reviewStarClause d (A i) x) =
        decide (∃ u v, (reviewStarGraph d).Adj u v ∧ x u = true ∧ x v = true)) :
    Fintype.card (reviewStarVertex d) ≤ Fintype.card ι := by
  refine ForestRows.packing_factorization_lower_bound
    (reviewStarCoord d) (reviewStarSign d) A ?_ F ?_
  · intro i u hu v hv comp
    exact reviewStar_packing_component_injective d (A i) (packed i) u hu v hv comp
  · intro p hp
    rcases p with ⟨v, b⟩
    have excluded : ForestRows.negative (reviewStarCoord d) (reviewStarSign d) b v = false :=
      (Finset.mem_filter.mp hp).2
    rw [reviewStar_forest_negative_eq] at excluded
    have negative :
        F (fun i => ForestRows.clause (A i)
          (ForestRows.negative (reviewStarCoord d) (reviewStarSign d) b)) = false := by
      rw [reviewStar_forest_negative_eq]
      change F (fun i => reviewStarClause d (A i) (reviewStarNegative d b)) = false
      rw [correct]
      exact decide_eq_false (reviewStar_negative_has_no_edge d b)
    have positive :
        F (fun i => ForestRows.clause (A i)
          (ForestRows.positive (reviewStarCoord d) (reviewStarSign d) v b)) = true := by
      rw [reviewStar_forest_positive_eq]
      change F (fun i => reviewStarClause d (A i) (reviewStarPositive d b v)) = true
      rw [correct]
      exact decide_eq_true (reviewStar_excluded_makes_positive d nonempty b v excluded)
    rw [positive, negative]
    decide

lemma reviewStar_packing_circuit_lower_bound {t : ℕ} (d : Fin t → ℕ)
    [DecidableRel (reviewStarGraph d).Adj] (nonempty : ∀ i, 0 < d i)
    {m : ℕ} (A : Fin m → Finset (reviewStarVertex d))
    (packed : ∀ i, reviewStarPacking d (A i))
    (C : PEqualNP.CircuitLowerBounds.Circuit)
    (fanin : ∀ g ∈ C.gates, g.inputs.length ≤ 2)
    (correct : ∀ x : reviewStarVertex d → Bool,
      C.eval (List.ofFn fun i => reviewStarClause d (A i) x) =
        decide (∃ u v, (reviewStarGraph d).Adj u v ∧ x u = true ∧ x v = true)) :
    Fintype.card (reviewStarVertex d) ≤ C.size + 1 := by
  obtain ⟨R, size, agreement, _⟩ := HelperSupport.output_support m C fanin
  let B : ↥R → Finset (reviewStarVertex d) := fun i => A i.val
  let F : (↥R → Bool) → Bool := fun z =>
    C.eval (List.ofFn fun i : Fin m => if hi : i ∈ R then z ⟨i, hi⟩ else false)
  have factors : ∀ x : reviewStarVertex d → Bool,
      F (fun i => reviewStarClause d (B i) x) =
        decide (∃ u v, (reviewStarGraph d).Adj u v ∧ x u = true ∧ x v = true) := by
    intro x
    have same := agreement
      (fun i => if hi : i ∈ R then reviewStarClause d (A i) x else false)
      (fun i => reviewStarClause d (A i) x)
      (by intro i hi; simp [hi])
    simpa only [F, B] using same.trans (correct x)
  have lower := reviewStar_factorization_lower_bound d nonempty B
    (fun i => packed i.val) F factors
  rw [Fintype.card_coe] at lower
  exact lower.trans size

lemma reviewStar_vertex_card {t : ℕ} (d : Fin t → ℕ) :
    Fintype.card (reviewStarVertex d) = (∑ i, d i) + t := by
  simp [reviewStarVertex, Fintype.card_sigma, Finset.sum_add_distrib]

lemma reviewStar_packing_circuit_sum_lower_bound {t : ℕ} (d : Fin t → ℕ)
    [DecidableRel (reviewStarGraph d).Adj] (nonempty : ∀ i, 0 < d i)
    {m : ℕ} (A : Fin m → Finset (reviewStarVertex d))
    (packed : ∀ i, reviewStarPacking d (A i))
    (C : PEqualNP.CircuitLowerBounds.Circuit)
    (fanin : ∀ g ∈ C.gates, g.inputs.length ≤ 2)
    (correct : ∀ x : reviewStarVertex d → Bool,
      C.eval (List.ofFn fun i => reviewStarClause d (A i) x) =
        decide (∃ u v, (reviewStarGraph d).Adj u v ∧ x u = true ∧ x v = true)) :
    (∑ i, d i) + t ≤ C.size + 1 := by
  rw [← reviewStar_vertex_card d]
  exact reviewStar_packing_circuit_lower_bound d nonempty A packed C fanin correct

end PEqualNP.Outside.L_meta_1904_aux
