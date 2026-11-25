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

end PEqualNP.Outside.L_meta_1904_aux
