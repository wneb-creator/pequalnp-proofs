import PEqualNP.Defs

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

lemma deletion_mono_replace_gate (pre post : List Gate) (g h : Gate) (out : ℕ)
    (hm : Monotone2 ⟨pre ++ g :: post, out⟩)
    (hh : h.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ h.inputs.length ≤ 2) :
    Monotone2 ⟨pre ++ h :: post, out⟩ := by
  intro a ha
  change a ∈ pre ++ h :: post at ha
  rcases List.mem_append.mp ha with ha | ha
  · exact hm a (List.mem_append_left _ ha)
  · rcases List.mem_cons.mp ha with rfl | ha
    · exact hh
    · exact hm a (List.mem_append_right _ (List.mem_cons_of_mem _ ha))

lemma erase_gate_of_zeroed_correct (n : ℕ) (pre post : List Gate) (g : Gate) (out : ℕ)
    (F : (Fin n → Bool) → Bool)
    (hm : Monotone2 ⟨pre ++ g :: post, out⟩)
    (hcorrect : ∀ x : Fin n → Bool,
      Circuit.eval ⟨pre ++ ⟨GateOp.or, []⟩ :: post, out⟩ (List.ofFn x) = F x) :
    ∃ D : Circuit, Monotone2 D ∧
      D.size + 1 = Circuit.size ⟨pre ++ g :: post, out⟩ ∧
      ∀ x : Fin n → Bool, D.eval (List.ofFn x) = F x := by
  have hm0 : Monotone2 ⟨pre ++ ⟨GateOp.or, []⟩ :: post, out⟩ :=
    deletion_mono_replace_gate pre post g ⟨GateOp.or, []⟩ out hm (by simp)
  have hz : ∀ x : Fin n → Bool,
      (Circuit.wires ⟨pre ++ ⟨GateOp.or, []⟩ :: post, out⟩ (List.ofFn x)).getD
        (n + pre.length) false = false := by
    intro x
    change (deletionRun (pre ++ ⟨GateOp.or, []⟩ :: post) (List.ofFn x)).getD
      (n + pre.length) false = false
    have h := deletionRun_gate_value pre post ⟨GateOp.or, []⟩ (List.ofFn x)
    simpa only [List.length_ofFn, List.map_nil, GateOp.eval, List.any_nil] using h
  obtain ⟨D, hD, hsize, heval⟩ :=
    delete_false_gate_split n pre post ⟨GateOp.or, []⟩ out hm0 hz
  exact ⟨D, hD, by simpa only [Circuit.size, List.length_append, List.length_cons] using hsize,
    fun x => (heval x).trans (hcorrect x)⟩

lemma erase_gate_of_aliased_correct (n : ℕ) (pre post : List Gate) (g : Gate) (out r : ℕ)
    (F : (Fin n → Bool) → Bool)
    (hm : Monotone2 ⟨pre ++ g :: post, out⟩)
    (hcorrect : ∀ x : Fin n → Bool,
      Circuit.eval ⟨pre ++ ⟨GateOp.or, [r]⟩ :: post, out⟩ (List.ofFn x) = F x) :
    ∃ D : Circuit, Monotone2 D ∧
      D.size + 1 = Circuit.size ⟨pre ++ g :: post, out⟩ ∧
      ∀ x : Fin n → Bool, D.eval (List.ofFn x) = F x := by
  have hm0 : Monotone2 ⟨pre ++ ⟨GateOp.or, [r]⟩ :: post, out⟩ :=
    deletion_mono_replace_gate pre post g ⟨GateOp.or, [r]⟩ out hm (by simp)
  have hz : ∀ x : Fin n → Bool,
      (Circuit.wires ⟨pre ++ ⟨GateOp.or, [r]⟩ :: post, out⟩ (List.ofFn x)).getD
        (n + pre.length) false = (deletionRun pre (List.ofFn x)).getD r false := by
    intro x
    change (deletionRun (pre ++ ⟨GateOp.or, [r]⟩ :: post) (List.ofFn x)).getD
      (n + pre.length) false = (deletionRun pre (List.ofFn x)).getD r false
    have h := deletionRun_gate_value pre post ⟨GateOp.or, [r]⟩ (List.ofFn x)
    simpa only [List.length_ofFn, List.map_cons, List.map_nil, GateOp.eval,
      List.any_cons, List.any_nil, id_eq, Bool.or_false] using h
  by_cases hr : r < n + pre.length
  · obtain ⟨D, hD, hsize, heval⟩ :=
      delete_alias_gate_split n pre post ⟨GateOp.or, [r]⟩ out r hr hm0 hz
    exact ⟨D, hD, by simpa only [Circuit.size, List.length_append, List.length_cons] using hsize,
    fun x => (heval x).trans (hcorrect x)⟩
  · have hzero : ∀ x : Fin n → Bool,
        (Circuit.wires ⟨pre ++ ⟨GateOp.or, [r]⟩ :: post, out⟩ (List.ofFn x)).getD
          (n + pre.length) false = false := by
      intro x
      rw [hz x]
      exact List.getD_eq_default _ _ (by simp only [deletionRun_length, List.length_ofFn]; omega)
    obtain ⟨D, hD, hsize, heval⟩ :=
      delete_false_gate_split n pre post ⟨GateOp.or, [r]⟩ out hm0 hzero
    exact ⟨D, hD, by simpa only [Circuit.size, List.length_append, List.length_cons] using hsize,
    fun x => (heval x).trans (hcorrect x)⟩

lemma no_zeroed_minimal (n : ℕ) (pre post : List Gate) (g : Gate) (out : ℕ)
    (F : (Fin n → Bool) → Bool)
    (hm : Monotone2 ⟨pre ++ g :: post, out⟩)
    (hleast : ∀ D : Circuit, Monotone2 D →
      (∀ x : Fin n → Bool, D.eval (List.ofFn x) = F x) →
      Circuit.size ⟨pre ++ g :: post, out⟩ ≤ D.size) :
    ¬ (∀ x : Fin n → Bool,
      Circuit.eval ⟨pre ++ ⟨GateOp.or, []⟩ :: post, out⟩ (List.ofFn x) = F x) := by
  intro hz
  obtain ⟨D, hD, hsize, heval⟩ := erase_gate_of_zeroed_correct n pre post g out F hm hz
  have h := hleast D hD heval
  omega

lemma no_aliased_minimal (n : ℕ) (pre post : List Gate) (g : Gate) (out r : ℕ)
    (F : (Fin n → Bool) → Bool)
    (hm : Monotone2 ⟨pre ++ g :: post, out⟩)
    (hleast : ∀ D : Circuit, Monotone2 D →
      (∀ x : Fin n → Bool, D.eval (List.ofFn x) = F x) →
      Circuit.size ⟨pre ++ g :: post, out⟩ ≤ D.size) :
    ¬ (∀ x : Fin n → Bool,
      Circuit.eval ⟨pre ++ ⟨GateOp.or, [r]⟩ :: post, out⟩ (List.ofFn x) = F x) := by
  intro hz
  obtain ⟨D, hD, hsize, heval⟩ := erase_gate_of_aliased_correct n pre post g out r F hm hz
  have h := hleast D hD heval
  omega

lemma signed_eval_mono {n : ℕ} (C : Circuit) (hm : Monotone2 C)
    {x y : Fin n → Bool} (hxy : ∀ i, x i = true → y i = true) :
    C.eval (List.ofFn x) = true → C.eval (List.ofFn y) = true := by
  have hinputs : WireLE (List.ofFn x) (List.ofFn y) := by
    intro i hi
    by_cases h : i < n
    · simpa [List.getD, List.getElem?_ofFn, h] using
        hxy ⟨i,h⟩ (by simpa [List.getD, List.getElem?_ofFn, h] using hi)
    · simp [List.getD, h] at hi
  exact run_mono C.gates (by simp) hinputs
    (fun g hg => by simpa using (hm g hg).1) C.output

lemma signed_boundary_alias_correct (n : ℕ) (pre post : List Gate) (g : Gate) (out r : ℕ)
    (F : (Fin n → Bool) → Bool) (P N : (Fin n → Bool) → Prop)
    (hm : Monotone2 ⟨pre ++ g :: post,out⟩)
    (hcorrect : ∀ x : Fin n → Bool,
      Circuit.eval ⟨pre ++ g :: post,out⟩ (List.ofFn x) = F x)
    (hpos_cover : ∀ x : Fin n → Bool, F x = true →
      ∃ y : Fin n → Bool, F y = true ∧ P y ∧ ∀ i, y i = true → x i = true)
    (hneg_cover : ∀ x : Fin n → Bool, F x = false →
      ∃ y : Fin n → Bool, F y = false ∧ N y ∧ ∀ i, x i = true → y i = true)
    (hpos : ∀ x : Fin n → Bool, P x →
      g.op.eval (g.inputs.map fun i => (run pre (List.ofFn x)).getD i false) = true →
      (run pre (List.ofFn x)).getD r false = true)
    (hneg : ∀ x : Fin n → Bool, N x →
      (run pre (List.ofFn x)).getD r false = true →
      g.op.eval (g.inputs.map fun i => (run pre (List.ofFn x)).getD i false) = true) :
    ∀ x : Fin n → Bool,
      Circuit.eval ⟨pre ++ ⟨GateOp.or,[r]⟩ :: post,out⟩ (List.ofFn x) = F x := by
  let D : Circuit := ⟨pre ++ ⟨GateOp.or,[r]⟩ :: post,out⟩
  have hD : Monotone2 D := deletion_mono_replace_gate pre post g _ out hm (by simp)
  have hpost : ∀ a ∈ post, a.op = .and ∨ a.op = .or := by
    intro a ha
    simpa using (hm a (List.mem_append_right _ (List.mem_cons_of_mem _ ha))).1
  let W := fun x : Fin n → Bool => run pre (List.ofFn x)
  let old := fun x : Fin n → Bool => g.op.eval (g.inputs.map fun i => (W x).getD i false)
  let new := fun x : Fin n → Bool => (W x).getD r false
  have old_eval (x : Fin n → Bool) :
      (run post (W x ++ [old x])).getD out false = F x := by
    simpa only [Circuit.eval,Circuit.wires,run,List.foldl_append,List.foldl_cons,W,old]
      using hcorrect x
  have new_eval (x : Fin n → Bool) : D.eval (List.ofFn x) =
      (run post (W x ++ [new x])).getD out false := by
    simp [D,Circuit.eval,Circuit.wires,run,List.foldl_append,GateOp.eval,W,new]
  have positive (x : Fin n → Bool) (hf : F x = true) (hp : P x) :
      D.eval (List.ofFn x) = true := by
    rw [new_eval]
    apply run_mono post (by simp)
      (wireLE_snoc rfl (fun _ h => h) (hpos x hp)) hpost out
    exact (old_eval x).trans hf
  have negative (x : Fin n → Bool) (hf : F x = false) (hn : N x) :
      D.eval (List.ofFn x) = false := by
    apply Bool.eq_false_iff.mpr
    intro hx
    rw [new_eval] at hx
    have h := run_mono post (by simp)
      (wireLE_snoc rfl (fun _ h => h) (hneg x hn)) hpost out hx
    rw [old_eval,hf] at h
    contradiction
  intro x
  change D.eval (List.ofFn x) = F x
  cases hf : F x with
  | true =>
    obtain ⟨y,hy,hp,hxy⟩ := hpos_cover x hf
    exact signed_eval_mono D hD hxy (positive y hy hp)
  | false =>
    obtain ⟨y,hy,hn,hxy⟩ := hneg_cover x hf
    apply Bool.eq_false_iff.mpr
    intro hx
    have h := signed_eval_mono D hD hxy hx
    rw [negative y hy hn] at h
    contradiction

lemma erase_gate_of_signed_boundary_order (n : ℕ) (pre post : List Gate) (g : Gate) (out r : ℕ)
    (F : (Fin n → Bool) → Bool) (P N : (Fin n → Bool) → Prop)
    (hm : Monotone2 ⟨pre ++ g :: post,out⟩)
    (hcorrect : ∀ x : Fin n → Bool,
      Circuit.eval ⟨pre ++ g :: post,out⟩ (List.ofFn x) = F x)
    (hpos_cover : ∀ x : Fin n → Bool, F x = true →
      ∃ y : Fin n → Bool, F y = true ∧ P y ∧ ∀ i, y i = true → x i = true)
    (hneg_cover : ∀ x : Fin n → Bool, F x = false →
      ∃ y : Fin n → Bool, F y = false ∧ N y ∧ ∀ i, x i = true → y i = true)
    (hpos : ∀ x : Fin n → Bool, P x →
      g.op.eval (g.inputs.map fun i => (run pre (List.ofFn x)).getD i false) = true →
      (run pre (List.ofFn x)).getD r false = true)
    (hneg : ∀ x : Fin n → Bool, N x →
      (run pre (List.ofFn x)).getD r false = true →
      g.op.eval (g.inputs.map fun i => (run pre (List.ofFn x)).getD i false) = true) :
    ∃ D : Circuit, Monotone2 D ∧ D.size + 1 = Circuit.size ⟨pre ++ g :: post,out⟩ ∧
      ∀ x : Fin n → Bool, D.eval (List.ofFn x) = F x := by
  exact erase_gate_of_aliased_correct n pre post g out r F hm
    (signed_boundary_alias_correct n pre post g out r F P N hm hcorrect
      hpos_cover hneg_cover hpos hneg)

namespace Redistribution

def oldOutput (a b c d e f g h : Bool) : Bool :=
  ((a || (((c || e) && (g || h)) && (c || h))) && (e || g)) ||
    ((b || (d && h)) && (f || (g || h)))

def newLeft (a c e g : Bool) : Bool :=
  (a || (c && g)) && (e || g)

def newRight (b d e f g h : Bool) : Bool :=
  (b || ((d || e) && h)) && (f || (g || h))

lemma redistribution : ∀ a b c d e f g h : Bool,
    oldOutput a b c d e f g h = newLeft a c e g || newRight b d e f g h := by
  decide +kernel

lemma inner_left_below : ∀ a b c d e f g h : Bool,
    c && g = true → oldOutput a b c d e f g h = true := by
  decide +kernel

lemma inner_right_below : ∀ a b c d e f g h : Bool,
    (d || e) && h = true → oldOutput a b c d e f g h = true := by
  decide +kernel

lemma outer_left_below : ∀ a b c d e f g h : Bool,
    newLeft a c e g = true → oldOutput a b c d e f g h = true := by
  decide +kernel

lemma outer_right_below : ∀ a b c d e f g h : Bool,
    newRight b d e f g h = true → oldOutput a b c d e f g h = true := by
  decide +kernel

end Redistribution

lemma minimal_gate_not_false_split (n : ℕ) (pre post : List Gate) (g : Gate) (out : ℕ)
    (hm : IsMinimalMonoCircuit n ⟨pre ++ g :: post, out⟩) :
    ¬ (∀ x : Fin n → Bool,
      g.op.eval (g.inputs.map fun i => (deletionRun pre (List.ofFn x)).getD i false) = false) := by
  intro hz
  have hz' : ∀ x : Fin n → Bool,
      (Circuit.wires ⟨pre ++ g :: post, out⟩ (List.ofFn x)).getD
        (n + pre.length) false = false := by
    intro x
    change (deletionRun (pre ++ g :: post) (List.ofFn x)).getD _ false = false
    have hv := deletionRun_gate_value pre post g (List.ofFn x)
    simp only [List.length_ofFn] at hv
    exact hv.trans (hz x)
  obtain ⟨D, hD, hsize, heval⟩ := delete_false_gate_split n pre post g out hm.1 hz'
  have hle := hm.2 D hD (funext heval)
  omega

lemma minimal_gate_not_alias_split (n : ℕ) (pre post : List Gate) (g : Gate) (out r : ℕ)
    (hm : IsMinimalMonoCircuit n ⟨pre ++ g :: post, out⟩) :
    ¬ (∀ x : Fin n → Bool,
      g.op.eval (g.inputs.map fun i => (deletionRun pre (List.ofFn x)).getD i false) =
        (deletionRun pre (List.ofFn x)).getD r false) := by
  intro hz
  by_cases hr : r < n + pre.length
  · have hz' : ∀ x : Fin n → Bool,
        (Circuit.wires ⟨pre ++ g :: post, out⟩ (List.ofFn x)).getD
          (n + pre.length) false = (deletionRun pre (List.ofFn x)).getD r false := by
      intro x
      change (deletionRun (pre ++ g :: post) (List.ofFn x)).getD _ false = _
      have hv := deletionRun_gate_value pre post g (List.ofFn x)
      simp only [List.length_ofFn] at hv
      exact hv.trans (hz x)
    obtain ⟨D, hD, hsize, heval⟩ := delete_alias_gate_split n pre post g out r hr hm.1 hz'
    have hle := hm.2 D hD (funext heval)
    omega
  · apply minimal_gate_not_false_split n pre post g out hm
    intro x
    rw [hz x]
    exact List.getD_eq_default _ _ (by simp only [deletionRun_length, List.length_ofFn]; omega)

lemma minimal_gate_regular_split (n : ℕ) (pre post : List Gate) (g : Gate) (out : ℕ)
    (hm : IsMinimalMonoCircuit n ⟨pre ++ g :: post, out⟩)
    (hn : g.op = GateOp.and → g.inputs ≠ []) :
    g.inputs.length = 2 ∧ ∀ i ∈ g.inputs, i < n + pre.length := by
  have hgm := hm.1 g (List.mem_append_right _ List.mem_cons_self)
  have hop : g.op = GateOp.and ∨ g.op = GateOp.or := by simpa using hgm.1
  have hlen := hgm.2
  have hz := minimal_gate_not_false_split n pre post g out hm
  have ha := fun r => minimal_gate_not_alias_split n pre post g out r hm
  cases hins : g.inputs with
  | nil =>
    rcases hop with hop | hop
    · exact False.elim (hn hop hins)
    · exact False.elim (hz (fun x => by simp [hins, hop, GateOp.eval]))
  | cons a ins =>
    cases ins with
    | nil =>
      apply False.elim (ha a ?_)
      intro x
      rcases hop with hop | hop <;> simp [hins, hop, GateOp.eval]
    | cons b ins =>
      cases ins with
      | cons c tail =>
        simp only [hins, List.length_cons] at hlen
        omega
      | nil =>
        refine ⟨by simp, ?_⟩
        have hfirst : a < n + pre.length := by
          by_contra hf
          have hfalse : ∀ x : Fin n → Bool,
              (deletionRun pre (List.ofFn x)).getD a false = false := fun x =>
            List.getD_eq_default _ _ (by simp only [deletionRun_length, List.length_ofFn]; omega)
          rcases hop with hop | hop
          · apply hz
            intro x
            simp only [hins, hop, GateOp.eval, List.map_cons, List.map_nil,
              List.all_cons, List.all_nil, id_eq]
            rw [hfalse x]
            simp
          · apply ha b
            intro x
            simp only [hins, hop, GateOp.eval, List.map_cons, List.map_nil,
              List.any_cons, List.any_nil, id_eq]
            rw [hfalse x]
            simp
        have hsecond : b < n + pre.length := by
          by_contra hf
          have hfalse : ∀ x : Fin n → Bool,
              (deletionRun pre (List.ofFn x)).getD b false = false := fun x =>
            List.getD_eq_default _ _ (by simp only [deletionRun_length, List.length_ofFn]; omega)
          rcases hop with hop | hop
          · apply hz
            intro x
            simp only [hins, hop, GateOp.eval, List.map_cons, List.map_nil,
              List.all_cons, List.all_nil, id_eq]
            rw [hfalse x]
            simp
          · apply ha a
            intro x
            simp only [hins, hop, GateOp.eval, List.map_cons, List.map_nil,
              List.any_cons, List.any_nil, id_eq]
            rw [hfalse x]
            simp
        intro i hi
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
        rcases hi with rfl | rfl
        · exact hfirst
        · exact hsecond

lemma minimal_ao2_of_no_nullary_and (n : ℕ) (C : Circuit)
    (hm : IsMinimalMonoCircuit n C)
    (hn : ∀ g ∈ C.gates, g.op = GateOp.and → g.inputs ≠ []) :
    PEqualNP.TopForm.IsAO2 n C := by
  have split_regular (pre post : List Gate) (g : Gate) (hs : C.gates = pre ++ g :: post) :
      g.inputs.length = 2 ∧ ∀ i ∈ g.inputs, i < n + pre.length := by
    have hc : C = ⟨pre ++ g :: post, C.output⟩ := by cases C; simp_all
    exact minimal_gate_regular_split n pre post g C.output (hc ▸ hm)
      (hn g (by simp [hs]))
  refine ⟨?_, ?_, ?_⟩
  · intro g hg
    simpa using (hm.1 g hg).1
  · intro j hj i hi
    let g := C.gates[j]
    let pre := C.gates.take j
    let post := C.gates.drop (j+1)
    have hsplit : C.gates = pre ++ g :: post :=
      (List.take_append_drop j C.gates).symm.trans (by rw [List.drop_eq_getElem_cons hj])
    have hpre : pre.length = j := by simp [pre, Nat.min_eq_left (Nat.le_of_lt hj)]
    have hgate : PEqualNP.MetaComplexity.NestedCover.gateAt C j = g := by
      simp only [PEqualNP.MetaComplexity.NestedCover.gateAt, List.getD_eq_getElem?_getD,
        List.getElem?_eq_getElem hj, Option.getD_some]
      rfl
    rw [hgate] at hi
    simpa only [hpre] using (split_regular pre post g hsplit).2 i hi
  · intro g hg
    obtain ⟨pre, post, hs⟩ := List.mem_iff_append.mp hg
    exact (split_regular pre post g hs).1

lemma minimal_ao2_of_safe_empty (n : ℕ) (C : Circuit) (F : (Fin n → Bool) → Bool)
    (hm : IsMinimalMonoCircuit n C)
    (hfalse : F (fun _ => false) = false)
    (hsafe : ∀ j g, C.gates[j]? = some g → g.op = GateOp.and →
      ∀ x : Fin n → Bool, (C.wires (List.ofFn x)).getD (n+j) false = true → F x = true) :
    PEqualNP.TopForm.IsAO2 n C := by
  apply minimal_ao2_of_no_nullary_and n C hm
  intro g hg hop hins
  obtain ⟨pre, post, hs⟩ := List.mem_iff_append.mp hg
  have hentry : C.gates[pre.length]? = some g := by simp [hs]
  have hgate : (C.wires (List.ofFn (fun _ : Fin n => false))).getD
      (n + pre.length) false = true := by
    change (deletionRun C.gates (List.ofFn (fun _ : Fin n => false))).getD _ false = true
    rw [hs]
    have hv := deletionRun_gate_value pre post g (List.ofFn (fun _ : Fin n => false))
    simpa only [List.length_ofFn, hins, List.map_nil, hop, GateOp.eval, List.all_nil] using hv
  have ht := hsafe pre.length g hentry hop (fun _ => false) hgate
  rw [hfalse] at ht
  contradiction

def familyDeletionCircuit (n : ℕ) (pre rest : List Gate) (out replacement : ℕ) : Circuit :=
  ⟨pre ++ rest.map (deletionGate (n + pre.length) replacement),
    deletionIndex (n + pre.length) replacement out⟩

lemma deletionIndex_primary (n k replacement t : ℕ) (ht : t < n) :
    deletionIndex (n + k) replacement t = t := by
  simp only [deletionIndex, ite_eq_left (show t < n + k by omega)]

lemma deletionGate_primary_mem (n k replacement t : ℕ) (g : Gate)
    (ht : t < n) (hg : t ∈ g.inputs) :
    t ∈ (deletionGate (n + k) replacement g).inputs := by
  have h := List.mem_map_of_mem (f := deletionIndex (n+k) replacement) hg
  rwa [deletionIndex_primary n k replacement t ht] at h

lemma deletion_family_false_explicit {ι : Type*} (n : ℕ) (input : ι → List Bool)
    (hlen : ∀ x, (input x).length = n) (pre rest : List Gate) (g : Gate) (out : ℕ)
    (hm : Monotone2 ⟨pre ++ g :: rest, out⟩)
    (hz : ∀ x : ι,
      (Circuit.wires ⟨pre ++ g :: rest, out⟩ (input x)).getD
        (n + pre.length) false = false) :
    let D := familyDeletionCircuit n pre rest out (n + pre.length + rest.length)
    Monotone2 D ∧ D.size + 1 = Circuit.size ⟨pre ++ g :: rest, out⟩ ∧
      ∀ x : ι, D.eval (input x) = Circuit.eval ⟨pre ++ g :: rest, out⟩ (input x) := by
  let k := n + pre.length
  let q := n + pre.length + rest.length
  let D : Circuit := ⟨pre ++ rest.map (deletionGate k q), deletionIndex k q out⟩
  change Monotone2 D ∧ D.size + 1 = Circuit.size ⟨pre ++ g :: rest, out⟩ ∧
    ∀ x : ι, D.eval (input x) = Circuit.eval ⟨pre ++ g :: rest, out⟩ (input x)
  refine ⟨?_, ?_, ?_⟩
  · intro h hh
    change h ∈ pre ++ rest.map (deletionGate k q) at hh
    rcases List.mem_append.mp hh with hh | hh
    · exact hm h (List.mem_append_left _ hh)
    · obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hh
      have H := hm a (List.mem_append_right _ (List.mem_cons_of_mem _ ha))
      exact ⟨H.1, by simpa [deletionGate] using H.2⟩
  · simp [D, Circuit.size, Nat.add_assoc]
  · intro x
    let p := deletionRun pre (input x)
    have hp : p.length = k := by simp [p, deletionRun_length, k, hlen x]
    have hzero : g.op.eval (g.inputs.map fun i => p.getD i false) = false := by
      have z := hz x
      change (deletionRun (pre ++ g :: rest) (input x)).getD
        (n + pre.length) false = false at z
      have hv := deletionRun_gate_value pre rest g (input x)
      rw [hlen x] at hv
      rw [hv] at z
      exact z
    obtain ⟨u, hu, hv, hl⟩ := deletionRun_suffix p [] rest q (by simp [hp, q, k])
    have hOld : Circuit.wires ⟨pre ++ g :: rest, out⟩ (input x) =
        p ++ false :: u := by
      change deletionRun (pre ++ g :: rest) (input x) = _
      rw [deletionRun_append]
      change deletionRun rest (p ++ [g.op.eval (g.inputs.map fun i => p.getD i false)]) = _
      rw [hzero]
      exact hu
    have hNew : D.wires (input x) = p ++ u := by
      change deletionRun (pre ++ rest.map (deletionGate k q)) (input x) = _
      rw [deletionRun_append]
      simpa only [List.append_nil, hp] using hv
    change (D.wires (input x)).getD (deletionIndex k q out) false =
      (Circuit.wires ⟨pre ++ g :: rest, out⟩ (input x)).getD out false
    rw [hOld, hNew, ← hp]
    exact (deletion_getD p u q out (by simp only [List.length_nil, Nat.zero_add] at hl; dsimp [q, k] at hp ⊢; omega)).symm

lemma deletion_family_alias_explicit {ι : Type*} (n : ℕ) (input : ι → List Bool)
    (hlen : ∀ x, (input x).length = n) (pre rest : List Gate) (g : Gate) (out r : ℕ)
    (hr : r < n + pre.length)
    (hm : Monotone2 ⟨pre ++ g :: rest, out⟩)
    (hz : ∀ x : ι,
      (Circuit.wires ⟨pre ++ g :: rest, out⟩ (input x)).getD
        (n + pre.length) false = (deletionRun pre (input x)).getD r false) :
    let D := familyDeletionCircuit n pre rest out r
    Monotone2 D ∧ D.size + 1 = Circuit.size ⟨pre ++ g :: rest, out⟩ ∧
      ∀ x : ι, D.eval (input x) = Circuit.eval ⟨pre ++ g :: rest, out⟩ (input x) := by
  let k := n + pre.length
  let D : Circuit := ⟨pre ++ rest.map (deletionGate k r), deletionIndex k r out⟩
  change Monotone2 D ∧ D.size + 1 = Circuit.size ⟨pre ++ g :: rest, out⟩ ∧
    ∀ x : ι, D.eval (input x) = Circuit.eval ⟨pre ++ g :: rest, out⟩ (input x)
  refine ⟨?_, ?_, ?_⟩
  · intro h hh
    change h ∈ pre ++ rest.map (deletionGate k r) at hh
    rcases List.mem_append.mp hh with hh | hh
    · exact hm h (List.mem_append_left _ hh)
    · obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hh
      have H := hm a (List.mem_append_right _ (List.mem_cons_of_mem _ ha))
      exact ⟨H.1, by simpa [deletionGate] using H.2⟩
  · simp [D, Circuit.size, Nat.add_assoc]
  · intro x
    let p := deletionRun pre (input x)
    have hp : p.length = k := by simp [p, deletionRun_length, k, hlen x]
    have hzero : g.op.eval (g.inputs.map fun i => p.getD i false) = p.getD r false := by
      have z := hz x
      change (deletionRun (pre ++ g :: rest) (input x)).getD
        (n + pre.length) false = p.getD r false at z
      have hv := deletionRun_gate_value pre rest g (input x)
      rw [hlen x] at hv
      rw [hv] at z
      exact z
    obtain ⟨u, hu, hv, hl⟩ := deletionRun_alias_suffix p [] rest r (by simpa [hp, k] using hr)
    have hOld : Circuit.wires ⟨pre ++ g :: rest, out⟩ (input x) =
        p ++ p.getD r false :: u := by
      change deletionRun (pre ++ g :: rest) (input x) = _
      rw [deletionRun_append]
      change deletionRun rest (p ++ [g.op.eval (g.inputs.map fun i => p.getD i false)]) = _
      rw [hzero]
      exact hu
    have hNew : D.wires (input x) = p ++ u := by
      change deletionRun (pre ++ rest.map (deletionGate k r)) (input x) = _
      rw [deletionRun_append]
      simpa only [List.append_nil, hp] using hv
    change (D.wires (input x)).getD (deletionIndex k r out) false =
      (Circuit.wires ⟨pre ++ g :: rest, out⟩ (input x)).getD out false
    rw [hOld, hNew, ← hp]
    exact (deletion_getD_core p u (p.getD r false) r out
      (List.getD_append _ _ _ _ (by simpa [hp, k] using hr))).symm

lemma deletion_family_alias_any_explicit {ι : Type*} (n : ℕ) (input : ι → List Bool)
    (hlen : ∀ x, (input x).length = n) (pre rest : List Gate) (g : Gate) (out r : ℕ)
    (hm : Monotone2 ⟨pre ++ g :: rest, out⟩)
    (hz : ∀ x : ι,
      (Circuit.wires ⟨pre ++ g :: rest, out⟩ (input x)).getD
        (n + pre.length) false = (deletionRun pre (input x)).getD r false) :
    ∃ replacement : ℕ,
      let D := familyDeletionCircuit n pre rest out replacement
      Monotone2 D ∧ D.size + 1 = Circuit.size ⟨pre ++ g :: rest, out⟩ ∧
        ∀ x : ι, D.eval (input x) = Circuit.eval ⟨pre ++ g :: rest, out⟩ (input x) := by
  by_cases hr : r < n + pre.length
  · exact ⟨r, deletion_family_alias_explicit n input hlen pre rest g out r hr hm hz⟩
  · refine ⟨n + pre.length + rest.length,
      deletion_family_false_explicit n input hlen pre rest g out hm ?_⟩
    intro x
    rw [hz x]
    exact List.getD_eq_default _ _ (by rw [deletionRun_length, hlen x]; omega)

lemma deletion_family_forced_and {ι : Type*} (n : ℕ) (input : ι → List Bool)
    (hlen : ∀ x, (input x).length = n) (pre rest : List Gate) (g : Gate) (out t : ℕ)
    (ht : t < n) (hop : g.op = GateOp.and) (hmem : t ∈ g.inputs)
    (hm : Monotone2 ⟨pre ++ g :: rest, out⟩)
    (hon : ∀ x : ι, (input x).getD t false = true) :
    ∃ replacement : ℕ,
      let D := familyDeletionCircuit n pre rest out replacement
      Monotone2 D ∧ D.size + 1 = Circuit.size ⟨pre ++ g :: rest, out⟩ ∧
        ∀ x : ι, D.eval (input x) = Circuit.eval ⟨pre ++ g :: rest, out⟩ (input x) := by
  have hprimary : ∀ x : ι, (deletionRun pre (input x)).getD t false = true := by
    intro x
    obtain ⟨tail, he⟩ := deletionRun_prefix pre (input x)
    rw [he, List.getD_append _ _ _ _ (by rw [hlen x]; exact ht)]
    exact hon x
  have hlenG := (hm g (List.mem_append_right _ List.mem_cons_self)).2
  have hlocal : ∃ r : ℕ, ∀ x : ι,
      g.op.eval (g.inputs.map fun i => (deletionRun pre (input x)).getD i false) =
        (deletionRun pre (input x)).getD r false := by
    cases hins : g.inputs with
    | nil => simp only [hins, List.not_mem_nil] at hmem
    | cons a ins =>
      cases ins with
      | nil => exact ⟨a, fun x => by simp [hop, GateOp.eval]⟩
      | cons b ins =>
        cases ins with
        | cons c tail => simp only [hins, List.length_cons] at hlenG; omega
        | nil =>
          simp only [hins, List.mem_cons, List.not_mem_nil, or_false] at hmem
          rcases hmem with rfl | rfl
          · refine ⟨b, fun x => ?_⟩
            simp only [hop, GateOp.eval, List.map_cons, List.map_nil,
              List.all_cons, List.all_nil, id_eq]
            rw [hprimary x]
            simp
          · refine ⟨a, fun x => ?_⟩
            simp only [hop, GateOp.eval, List.map_cons, List.map_nil,
              List.all_cons, List.all_nil, id_eq]
            rw [hprimary x]
            simp
  obtain ⟨r, hr⟩ := hlocal
  apply deletion_family_alias_any_explicit n input hlen pre rest g out r hm
  intro x
  change (deletionRun (pre ++ g :: rest) (input x)).getD _ false = _
  have hv := deletionRun_gate_value pre rest g (input x)
  rw [hlen x] at hv
  exact hv.trans (hr x)

lemma deletion_family_two_forced_ands {ι : Type*} (n : ℕ) (input : ι → List Bool)
    (hlen : ∀ x, (input x).length = n) (pre middle post : List Gate) (g h : Gate)
    (out t₁ t₂ : ℕ) (ht₁ : t₁ < n) (ht₂ : t₂ < n)
    (hop₁ : g.op = GateOp.and) (hop₂ : h.op = GateOp.and)
    (hmem₁ : t₁ ∈ g.inputs) (hmem₂ : t₂ ∈ h.inputs)
    (hm : Monotone2 ⟨pre ++ g :: (middle ++ h :: post), out⟩)
    (hon₁ : ∀ x : ι, (input x).getD t₁ false = true)
    (hon₂ : ∀ x : ι, (input x).getD t₂ false = true) :
    ∃ D : Circuit, Monotone2 D ∧
      D.size + 2 = Circuit.size ⟨pre ++ g :: (middle ++ h :: post), out⟩ ∧
      ∀ x : ι, D.eval (input x) =
        Circuit.eval ⟨pre ++ g :: (middle ++ h :: post), out⟩ (input x) := by
  obtain ⟨replacement, hm₁, hs₁, he₁⟩ :=
    deletion_family_forced_and n input hlen pre (middle ++ h :: post) g out t₁
      ht₁ hop₁ hmem₁ hm hon₁
  let k := n + pre.length
  let D₁ := familyDeletionCircuit n pre (middle ++ h :: post) out replacement
  let pre₂ := pre ++ middle.map (deletionGate k replacement)
  let post₂ := post.map (deletionGate k replacement)
  let h₂ := deletionGate k replacement h
  let out₂ := deletionIndex k replacement out
  have hshape : D₁ = ⟨pre₂ ++ h₂ :: post₂, out₂⟩ := by
    simp [D₁, familyDeletionCircuit, pre₂, post₂, h₂, out₂, k,
      List.map_append, List.append_assoc]
  have hm₂ : Monotone2 ⟨pre₂ ++ h₂ :: post₂, out₂⟩ := by
    rw [← hshape]
    exact hm₁
  have hop₂' : h₂.op = GateOp.and := hop₂
  have hmem₂' : t₂ ∈ h₂.inputs :=
    deletionGate_primary_mem n pre.length replacement t₂ h ht₂ hmem₂
  obtain ⟨replacement₂, hmD, hsD, heD⟩ :=
    deletion_family_forced_and n input hlen pre₂ post₂ h₂ out₂ t₂
      ht₂ hop₂' hmem₂' hm₂ hon₂
  let D := familyDeletionCircuit n pre₂ post₂ out₂ replacement₂
  refine ⟨D, hmD, ?_, ?_⟩
  · have hsD' : D.size + 1 = D₁.size := by rw [hshape]; exact hsD
    change D₁.size + 1 = _ at hs₁
    omega
  · intro x
    exact (heD x).trans (by rw [← hshape]; exact he₁ x)

lemma constant_snoc_agree (p : List Bool) (a b : Bool) (i : ℕ) (hi : i ≠ p.length) :
    (p ++ [a]).getD i false = (p ++ [b]).getD i false := by
  by_cases hl : i < p.length
  · rw [List.getD_append _ _ _ _ hl, List.getD_append _ _ _ _ hl]
  · rw [List.getD_eq_default _ _ (by simp; omega),
      List.getD_eq_default _ _ (by simp; omega)]

lemma constantRun_agree_except (gs : List Gate) (a b : List Bool) (k : ℕ)
    (hlen : a.length = b.length) (hk : k < a.length)
    (heq : ∀ i, i ≠ k → a.getD i false = b.getD i false)
    (hno : ∀ g ∈ gs, k ∉ g.inputs) :
    ∀ i, i ≠ k → (deletionRun gs a).getD i false = (deletionRun gs b).getD i false := by
  induction gs generalizing a b with
  | nil => exact heq
  | cons g gs ih =>
    have hval : g.op.eval (g.inputs.map fun i => a.getD i false) =
        g.op.eval (g.inputs.map fun i => b.getD i false) := by
      congr 1
      apply List.map_congr_left
      intro i hi
      exact heq i (fun e => hno g List.mem_cons_self (e ▸ hi))
    let va := g.op.eval (g.inputs.map fun i => a.getD i false)
    let vb := g.op.eval (g.inputs.map fun i => b.getD i false)
    have hlen' : (a ++ [va]).length = (b ++ [vb]).length := by simp [hlen]
    have hk' : k < (a ++ [va]).length := by simp; omega
    have heq' : ∀ i, i ≠ k → (a ++ [va]).getD i false = (b ++ [vb]).getD i false := by
      intro i hi
      by_cases hlt : i < a.length
      · rw [List.getD_append _ _ _ _ hlt,
          List.getD_append _ _ _ _ (by omega)]
        exact heq i hi
      · by_cases hsame : i = a.length
        · subst i
          rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega), Nat.sub_self]
          rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega), hlen, Nat.sub_self]
          exact hval
        · rw [List.getD_eq_default _ _ (by simp; omega),
            List.getD_eq_default _ _ (by simp; omega)]
    exact ih (a ++ [va]) (b ++ [vb]) hlen' hk' heq'
      (fun h hh => hno h (List.mem_cons_of_mem _ hh))

lemma zeroing_unread_correct (n : ℕ) (pre post : List Gate) (g : Gate) (out : ℕ)
    (hno : ∀ h ∈ post, n + pre.length ∉ h.inputs) (hout : out ≠ n + pre.length) :
    ∀ x : Fin n → Bool,
      Circuit.eval ⟨pre ++ g :: post, out⟩ (List.ofFn x) =
        Circuit.eval ⟨pre ++ ⟨GateOp.or, []⟩ :: post, out⟩ (List.ofFn x) := by
  intro x
  let p := deletionRun pre (List.ofFn x)
  let b := g.op.eval (g.inputs.map fun i => p.getD i false)
  have hp : p.length = n + pre.length := by simp [p, deletionRun_length]
  have heq := constantRun_agree_except post (p ++ [b]) (p ++ [false]) (n + pre.length)
    (by simp) (by simp [hp])
    (fun i hi => constant_snoc_agree p b false i (by rwa [hp])) hno out hout
  change (deletionRun (pre ++ g :: post) (List.ofFn x)).getD out false =
    (deletionRun (pre ++ ⟨GateOp.or, []⟩ :: post) (List.ofFn x)).getD out false
  rw [deletionRun_append, deletionRun_append]
  exact heq

lemma minimal_reader_constant_true (n : ℕ) (pre post : List Gate) (g : Gate) (out r : ℕ)
    (hm : IsMinimalMonoCircuit n ⟨pre ++ g :: post, out⟩)
    (hmem : r ∈ g.inputs)
    (htrue : ∀ x : Fin n → Bool, (deletionRun pre (List.ofFn x)).getD r false = true) : False := by
  have hgm := hm.1 g (List.mem_append_right _ List.mem_cons_self)
  have hop : g.op = GateOp.and ∨ g.op = GateOp.or := by simpa using hgm.1
  have hlen := hgm.2
  have ha := fun j => minimal_gate_not_alias_split n pre post g out j hm
  rcases hop with hop | hop
  · cases hins : g.inputs with
    | nil => simp only [hins, List.not_mem_nil] at hmem
    | cons a ins =>
      cases ins with
      | nil => exact ha a (fun x => by simp [hop, hins, GateOp.eval])
      | cons b ins =>
        cases ins with
        | cons c tail => simp only [hins, List.length_cons] at hlen; omega
        | nil =>
          simp only [hins, List.mem_cons, List.not_mem_nil, or_false] at hmem
          rcases hmem with rfl | rfl
          · apply ha b
            intro x
            simp only [hins, hop, GateOp.eval, List.map_cons, List.map_nil,
              List.all_cons, List.all_nil, id_eq]
            rw [htrue x]
            simp
          · apply ha a
            intro x
            simp only [hins, hop, GateOp.eval, List.map_cons, List.map_nil,
              List.all_cons, List.all_nil, id_eq]
            rw [htrue x]
            simp
  · apply ha r
    intro x
    rw [htrue x]
    simpa only [hop, GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id_eq]
      using (show ∃ i ∈ g.inputs, (deletionRun pre (List.ofFn x)).getD i false = true from
        ⟨r, hmem, htrue x⟩)

lemma minimal_no_nullary_and_split (n : ℕ) (pre post : List Gate) (g : Gate) (out : ℕ)
    (hm : IsMinimalMonoCircuit n ⟨pre ++ g :: post, out⟩)
    (hfalse : Circuit.eval ⟨pre ++ g :: post, out⟩ (List.ofFn (fun _ : Fin n => false)) = false)
    (hop : g.op = GateOp.and) (hins : g.inputs = []) : False := by
  have hno : ∀ h ∈ post, n + pre.length ∉ h.inputs := by
    intro h hh hread
    obtain ⟨middle, tail, hs⟩ := List.mem_iff_append.mp hh
    have he : (⟨pre ++ g :: post, out⟩ : Circuit) =
        ⟨(pre ++ g :: middle) ++ h :: tail, out⟩ := by simp [hs, List.append_assoc]
    apply minimal_reader_constant_true n (pre ++ g :: middle) tail h out (n + pre.length)
      (he ▸ hm) hread
    intro x
    have hv := deletionRun_gate_value pre middle g (List.ofFn x)
    simpa only [List.length_ofFn, hop, hins, List.map_nil, GateOp.eval, List.all_nil] using hv
  have hout : out ≠ n + pre.length := by
    intro he
    have hv := deletionRun_gate_value pre post g (List.ofFn (fun _ : Fin n => false))
    simp only [List.length_ofFn, hop, hins, List.map_nil, GateOp.eval, List.all_nil] at hv
    change (deletionRun (pre ++ g :: post) (List.ofFn (fun _ : Fin n => false))).getD out false = false at hfalse
    rw [he, hv] at hfalse
    contradiction
  obtain ⟨D, hD, hsD, heD⟩ := erase_gate_of_zeroed_correct n pre post g out
    (fun x => Circuit.eval ⟨pre ++ g :: post, out⟩ (List.ofFn x)) hm.1
    (fun x => (zeroing_unread_correct n pre post g out hno hout x).symm)
  have hle := hm.2 D hD (funext heD)
  omega

lemma minimal_ao2_of_false_empty (n : ℕ) (C : Circuit)
    (hm : IsMinimalMonoCircuit n C)
    (hfalse : C.eval (List.ofFn (fun _ : Fin n => false)) = false) :
    PEqualNP.TopForm.IsAO2 n C := by
  apply minimal_ao2_of_no_nullary_and n C hm
  intro g hg hop hins
  obtain ⟨pre, post, hs⟩ := List.mem_iff_append.mp hg
  have hc : C = ⟨pre ++ g :: post, C.output⟩ := by cases C; simp_all
  exact minimal_no_nullary_and_split n pre post g C.output (hc ▸ hm) (hc ▸ hfalse) hop hins

lemma minimal_binary_distinct_split (n : ℕ) (pre post : List Gate) (g : Gate)
    (out a b : ℕ) (hm : IsMinimalMonoCircuit n ⟨pre ++ g :: post, out⟩)
    (hins : g.inputs = [a, b]) : a ≠ b := by
  intro hab
  subst b
  apply minimal_gate_not_alias_split n pre post g out a hm
  intro x
  have hop : g.op = GateOp.and ∨ g.op = GateOp.or := by
    simpa using (hm.1 g (List.mem_append_right _ List.mem_cons_self)).1
  rcases hop with hop | hop <;> simp [hins, hop, GateOp.eval]

lemma minimal_last_gate_output (n : ℕ) (pre : List Gate) (g : Gate) (out : ℕ)
    (hm : IsMinimalMonoCircuit n ⟨pre ++ [g], out⟩) : out = n + pre.length := by
  by_contra hout
  have hsame := zeroing_unread_correct n pre [] g out (by simp) hout
  obtain ⟨D, hD, hs, he⟩ := erase_gate_of_zeroed_correct n pre [] g out
    (fun x => Circuit.eval ⟨pre ++ [g], out⟩ (List.ofFn x)) hm.1
    (fun x => (hsame x).symm)
  have hle := hm.2 D hD (funext he)
  omega

lemma deletion_family_forced_gate {ι : Type*} (n : ℕ) (input : ι → List Bool)
    (hlen : ∀ x, (input x).length = n) (pre rest : List Gate) (g : Gate) (out t : ℕ)
    (bit : Bool) (ht : t < n) (hmem : t ∈ g.inputs)
    (hm : Monotone2 ⟨pre ++ g :: rest, out⟩)
    (hon : ∀ x : ι, (input x).getD t false = bit) :
    ∃ replacement : ℕ,
      let D := familyDeletionCircuit n pre rest out replacement
      Monotone2 D ∧ D.size + 1 = Circuit.size ⟨pre ++ g :: rest, out⟩ ∧
        ∀ x : ι, D.eval (input x) = Circuit.eval ⟨pre ++ g :: rest, out⟩ (input x) := by
  have hprimary : ∀ x : ι, (deletionRun pre (input x)).getD t false = bit := by
    intro x
    obtain ⟨tail, he⟩ := deletionRun_prefix pre (input x)
    rw [he, List.getD_append _ _ _ _ (by rw [hlen x]; exact ht)]
    exact hon x
  have hgate := hm g (List.mem_append_right _ List.mem_cons_self)
  have hop : g.op = GateOp.and ∨ g.op = GateOp.or := by simpa using hgate.1
  have hlenG := hgate.2
  have hlocal : ∃ r : ℕ, ∀ x : ι,
      g.op.eval (g.inputs.map fun i => (deletionRun pre (input x)).getD i false) =
        (deletionRun pre (input x)).getD r false := by
    cases hins : g.inputs with
    | nil => simp only [hins, List.not_mem_nil] at hmem
    | cons a ins =>
      cases ins with
      | nil =>
        refine ⟨a, fun x => ?_⟩
        rcases hop with hop | hop <;> simp [hop, GateOp.eval]
      | cons b ins =>
        cases ins with
        | cons c tail => simp only [hins, List.length_cons] at hlenG; omega
        | nil =>
          simp only [hins, List.mem_cons, List.not_mem_nil, or_false] at hmem
          rcases hmem with rfl | rfl
          · cases bit with
            | false =>
              rcases hop with hop | hop
              · refine ⟨t, fun x => ?_⟩
                simp only [hop, GateOp.eval, List.map_cons, List.map_nil,
                  List.all_cons, List.all_nil, id_eq]
                rw [hprimary x]
                simp
              · refine ⟨b, fun x => ?_⟩
                simp only [hop, GateOp.eval, List.map_cons, List.map_nil,
                  List.any_cons, List.any_nil, id_eq]
                rw [hprimary x]
                simp
            | true =>
              rcases hop with hop | hop
              · refine ⟨b, fun x => ?_⟩
                simp only [hop, GateOp.eval, List.map_cons, List.map_nil,
                  List.all_cons, List.all_nil, id_eq]
                rw [hprimary x]
                simp
              · refine ⟨t, fun x => ?_⟩
                simp only [hop, GateOp.eval, List.map_cons, List.map_nil,
                  List.any_cons, List.any_nil, id_eq]
                rw [hprimary x]
                simp
          · cases bit with
            | false =>
              rcases hop with hop | hop
              · refine ⟨t, fun x => ?_⟩
                simp only [hop, GateOp.eval, List.map_cons, List.map_nil,
                  List.all_cons, List.all_nil, id_eq]
                rw [hprimary x]
                simp
              · refine ⟨a, fun x => ?_⟩
                simp only [hop, GateOp.eval, List.map_cons, List.map_nil,
                  List.any_cons, List.any_nil, id_eq]
                rw [hprimary x]
                simp
            | true =>
              rcases hop with hop | hop
              · refine ⟨a, fun x => ?_⟩
                simp only [hop, GateOp.eval, List.map_cons, List.map_nil,
                  List.all_cons, List.all_nil, id_eq]
                rw [hprimary x]
                simp
              · refine ⟨t, fun x => ?_⟩
                simp only [hop, GateOp.eval, List.map_cons, List.map_nil,
                  List.any_cons, List.any_nil, id_eq]
                rw [hprimary x]
                simp
  obtain ⟨r, hr⟩ := hlocal
  apply deletion_family_alias_any_explicit n input hlen pre rest g out r hm
  intro x
  change (deletionRun (pre ++ g :: rest) (input x)).getD _ false = _
  have hv := deletionRun_gate_value pre rest g (input x)
  rw [hlen x] at hv
  exact hv.trans (hr x)

lemma deletion_family_two_forced_gates {ι : Type*} (n : ℕ) (input : ι → List Bool)
    (hlen : ∀ x, (input x).length = n) (pre middle post : List Gate) (g h : Gate)
    (out t₁ t₂ : ℕ) (bit₁ bit₂ : Bool) (ht₁ : t₁ < n) (ht₂ : t₂ < n)
    (hmem₁ : t₁ ∈ g.inputs) (hmem₂ : t₂ ∈ h.inputs)
    (hm : Monotone2 ⟨pre ++ g :: (middle ++ h :: post), out⟩)
    (hon₁ : ∀ x : ι, (input x).getD t₁ false = bit₁)
    (hon₂ : ∀ x : ι, (input x).getD t₂ false = bit₂) :
    ∃ D : Circuit, Monotone2 D ∧
      D.size + 2 = Circuit.size ⟨pre ++ g :: (middle ++ h :: post), out⟩ ∧
      ∀ x : ι, D.eval (input x) =
        Circuit.eval ⟨pre ++ g :: (middle ++ h :: post), out⟩ (input x) := by
  obtain ⟨replacement, hm₁, hs₁, he₁⟩ :=
    deletion_family_forced_gate n input hlen pre (middle ++ h :: post) g out t₁ bit₁
      ht₁ hmem₁ hm hon₁
  let k := n + pre.length
  let D₁ := familyDeletionCircuit n pre (middle ++ h :: post) out replacement
  let pre₂ := pre ++ middle.map (deletionGate k replacement)
  let post₂ := post.map (deletionGate k replacement)
  let h₂ := deletionGate k replacement h
  let out₂ := deletionIndex k replacement out
  have hshape : D₁ = ⟨pre₂ ++ h₂ :: post₂, out₂⟩ := by
    simp [D₁, familyDeletionCircuit, pre₂, post₂, h₂, out₂, k,
      List.map_append, List.append_assoc]
  have hm₂ : Monotone2 ⟨pre₂ ++ h₂ :: post₂, out₂⟩ := by
    rw [← hshape]
    exact hm₁
  have hmem₂' : t₂ ∈ h₂.inputs :=
    deletionGate_primary_mem n pre.length replacement t₂ h ht₂ hmem₂
  obtain ⟨replacement₂, hmD, hsD, heD⟩ :=
    deletion_family_forced_gate n input hlen pre₂ post₂ h₂ out₂ t₂ bit₂
      ht₂ hmem₂' hm₂ hon₂
  let D := familyDeletionCircuit n pre₂ post₂ out₂ replacement₂
  refine ⟨D, hmD, ?_, ?_⟩
  · have hsD' : D.size + 1 = D₁.size := by rw [hshape]; exact hsD
    change D₁.size + 1 = _ at hs₁
    omega
  · intro x
    exact (heD x).trans (by rw [← hshape]; exact he₁ x)

lemma exists_measure_min {α : Type*} (P : α → Prop) (f : α → ℕ)
    (hex : ∃ x, P x) : ∃ x, P x ∧ ∀ y, P y → f x ≤ f y := by
  classical
  have hn : ∃ m, ∃ x, P x ∧ f x = m := by
    obtain ⟨x, hx⟩ := hex
    exact ⟨f x, x, hx, rfl⟩
  obtain ⟨x, hx, hfx⟩ := Nat.find_spec hn
  refine ⟨x, hx, fun y hy => ?_⟩
  rw [hfx]
  exact Nat.find_min' hn ⟨y, hy, rfl⟩

lemma ao2_mono {n : ℕ} {C : Circuit} (h : PEqualNP.TopForm.IsAO2 n C) :
    Monotone2 C := by
  intro g hg
  exact ⟨by simpa using h.1 g hg, (h.2.2 g hg).le⟩

lemma minimal_graph_is_least_ao (n : ℕ) (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit) (hm : IsMinimalMonoCircuit n C)
    (hc : circuitFun n C = PEqualNP.MetaComplexity.NestedCover.graphFun G ∅) :
    PEqualNP.TopForm.IsLeastAO G C := by
  refine ⟨minimal_ao2_of_false_empty n C hm ?_, hc, ?_⟩
  · have h := congrFun hc (fun _ => false)
    simpa [circuitFun, PEqualNP.MetaComplexity.NestedCover.graphFun] using h
  · intro D hD hcorrect
    exact hm.2 D (ao2_mono hD) (hcorrect.trans hc.symm)

def GraphExtremal (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (activity : Circuit → ℕ) (C : Circuit) : Prop :=
    IsMinimalMonoCircuit n C ∧
      circuitFun n C = PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ ∧
      PEqualNP.TopForm.TopForm G C ∧
      (∀ D : Circuit, IsMinimalMonoCircuit n D →
        circuitFun n D = PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ →
        (PEqualNP.TopForm.junk G C).card ≤ (PEqualNP.TopForm.junk G D).card) ∧
      (∀ D : Circuit, IsMinimalMonoCircuit n D →
        circuitFun n D = PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ →
        (PEqualNP.TopForm.junk G D).card = (PEqualNP.TopForm.junk G C).card →
        PEqualNP.TopForm.andPairs n C ≤ PEqualNP.TopForm.andPairs n D) ∧
      (∀ D : Circuit, IsMinimalMonoCircuit n D →
        circuitFun n D = PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ →
        (PEqualNP.TopForm.junk G D).card = (PEqualNP.TopForm.junk G C).card →
        PEqualNP.TopForm.andPairs n D = PEqualNP.TopForm.andPairs n C →
        activity C ≤ activity D)

lemma exists_top_form_extremal_of_rewrite (n : ℕ) (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (activity : Circuit → ℕ)
    (C₀ : Circuit) (hm₀ : IsMinimalMonoCircuit n C₀)
    (hc₀ : circuitFun n C₀ = PEqualNP.MetaComplexity.NestedCover.graphFun G ∅)
    (rewrite_safe : ∀ C : Circuit, PEqualNP.TopForm.IsLeastAO G C →
      ∀ i j, i < C.gates.length → j < C.gates.length →
        (PEqualNP.MetaComplexity.NestedCover.gateAt C i).op = GateOp.and →
        PEqualNP.TopForm.BelowF G C i →
        (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = GateOp.and →
        PEqualNP.EdgeOwnership.InCone n C i j →
        ∃ D : Circuit, PEqualNP.TopForm.IsLeastAO G D ∧ D.size = C.size ∧
          PEqualNP.TopForm.andPairs n D < PEqualNP.TopForm.andPairs n C ∧
          (PEqualNP.TopForm.junk G D).card = (PEqualNP.TopForm.junk G C).card) :
    ∃ C : Circuit, GraphExtremal n G activity C := by
  classical
  let P := fun C : Circuit => IsMinimalMonoCircuit n C ∧
    circuitFun n C = PEqualNP.MetaComplexity.NestedCover.graphFun G ∅
  obtain ⟨Cj, hCj, hjmin⟩ := exists_measure_min P
    (fun C => (PEqualNP.TopForm.junk G C).card) ⟨C₀, hm₀, hc₀⟩
  obtain ⟨Cp, ⟨hCp, hCpJ⟩, hpmin⟩ := exists_measure_min
    (fun C => P C ∧ (PEqualNP.TopForm.junk G C).card = (PEqualNP.TopForm.junk G Cj).card)
    (PEqualNP.TopForm.andPairs n) ⟨Cj, hCj, rfl⟩
  obtain ⟨C, ⟨hC, hCJ, hCP⟩, hamin⟩ := exists_measure_min
    (fun C => P C ∧ (PEqualNP.TopForm.junk G C).card = (PEqualNP.TopForm.junk G Cj).card ∧
      PEqualNP.TopForm.andPairs n C = PEqualNP.TopForm.andPairs n Cp)
    activity ⟨Cp, hCp, hCpJ, rfl⟩
  have pair_min (D : Circuit) (hD : P D)
      (hj : (PEqualNP.TopForm.junk G D).card = (PEqualNP.TopForm.junk G C).card) :
      PEqualNP.TopForm.andPairs n C ≤ PEqualNP.TopForm.andPairs n D := by
    rw [hCP]
    exact hpmin D ⟨hD, hj.trans hCJ⟩
  refine ⟨C, hC.1, hC.2, ?_, ?_, ?_, ?_⟩
  · intro i hi j hj hiop hisafe hjop hcone
    obtain ⟨D, hD, hs, hp, hjunk⟩ := rewrite_safe C
      (minimal_graph_is_least_ao n G C hC.1 hC.2) i j hi hj hiop hisafe hjop hcone
    have hmD : IsMinimalMonoCircuit n D := by
      refine ⟨ao2_mono hD.1, ?_⟩
      intro E hE he
      rw [hs]
      exact hC.1.2 E hE ((he.trans hD.2.1).trans hC.2.symm)
    have hle := pair_min D ⟨hmD, hD.2.1⟩ hjunk
    omega
  · intro D hm hc
    rw [hCJ]
    exact hjmin D ⟨hm, hc⟩
  · intro D hm hc hj
    exact pair_min D ⟨hm, hc⟩ hj
  · intro D hm hc hj hp
    exact hamin D ⟨⟨hm, hc⟩, hj.trans hCJ, hp.trans hCP⟩

namespace SafeLift


open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership

def stepW (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma foldl_len (gs : List Gate) (w : List Bool) :
    (gs.foldl stepW w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [stepW]
    omega

lemma foldl_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl stepW w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hlt : i < (stepW w g).length := by simp [stepW]; omega
    rw [ih (stepW w g) hlt]
    simp [stepW, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma foldl_char (gs : List Gate) (w : List Bool) :
    ∀ j, j < gs.length → (gs.foldl stepW w).getD (w.length + j) false =
      (gs.getD j ⟨GateOp.or, []⟩).op.eval ((gs.getD j ⟨GateOp.or, []⟩).inputs.map fun i =>
        if i < w.length + j then (gs.foldl stepW w).getD i false else false) := by
  induction gs using List.reverseRecOn with
  | nil => intro j hj; simp at hj
  | append_singleton gs g ih =>
    intro j hj
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
    have hlen := foldl_len gs w
    simp only [List.length_append, List.length_singleton] at hj
    have key : ∀ i, i < w.length + gs.length →
        (stepW (gs.foldl stepW w) g).getD i false = (gs.foldl stepW w).getD i false := by
      intro i hi
      simp only [stepW, List.getD_eq_getElem?_getD]
      rw [List.getElem?_append_left (by omega)]
    rcases Nat.lt_or_ge j gs.length with h | h
    · have e1 : (gs ++ [g]).getD j ⟨GateOp.or, []⟩ = gs.getD j ⟨GateOp.or, []⟩ := by
        simp only [List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_left h]
      rw [e1, key _ (by omega), ih j h]
      congr 1
      apply List.map_congr_left
      intro i _
      split_ifs with hi
      · rw [key i (by omega)]
      · rfl
    · have hj' : j = gs.length := by omega
      subst hj'
      have e1 : (gs ++ [g]).getD gs.length ⟨GateOp.or, []⟩ = g := by
        simp [List.getD_eq_getElem?_getD]
      rw [e1]
      have e2 : (stepW (gs.foldl stepW w) g).getD (w.length + gs.length) false =
          g.op.eval (g.inputs.map fun i => (gs.foldl stepW w).getD i false) := by
        simp only [stepW, List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_right (by omega)]
        simp [hlen]
      rw [e2]
      congr 1
      apply List.map_congr_left
      intro i _
      split_ifs with hi
      · rw [key i hi]
      · simp only [List.getD_eq_getElem?_getD]
        rw [List.getElem?_eq_none (by omega)]
        rfl

def wv (n : ℕ) (C : Circuit) (x : Fin n → Bool) (w : ℕ) : Bool :=
  (C.wires (List.ofFn x)).getD w false

lemma wires_eq (C : Circuit) (x : List Bool) : C.wires x = C.gates.foldl stepW x := rfl

lemma wv_input (n : ℕ) (C : Circuit) (x : Fin n → Bool) (w : ℕ) (hw : w < n) :
    wv n C x w = x ⟨w, hw⟩ := by
  unfold wv
  rw [wires_eq, foldl_getD_lt _ _ _ (by simpa using hw)]
  simp [List.getD_eq_getElem?_getD, hw]

def AOB (n : ℕ) (C : Circuit) : Prop :=
  ∀ j, j < C.gates.length →
    ((gateAt C j).op = GateOp.and ∨ (gateAt C j).op = GateOp.or) ∧
      ∀ i ∈ (gateAt C j).inputs, i < n + j

lemma wv_rec (n : ℕ) (C : Circuit) (x : Fin n → Bool) (hC : AOB n C) (j : ℕ)
    (hj : j < C.gates.length) :
    wv n C x (n + j) = (gateAt C j).op.eval ((gateAt C j).inputs.map (wv n C x)) := by
  have h := foldl_char C.gates (List.ofFn x) j hj
  simp only [List.length_ofFn] at h
  unfold wv gateAt
  rw [wires_eq, h]
  congr 1
  apply List.map_congr_left
  intro i hi
  rw [if_pos ((hC j hj).2 i hi)]

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

def tau (n r b w : ℕ) : ℕ := if w < n + r then w else if w = n + r then b else w - 1

def rho (r k : ℕ) : ℕ := if k < r then k else k + 1

def IsRedirect (n : ℕ) (C C' : Circuit) (r b : ℕ) : Prop :=
  ∀ k, k < C.gates.length - 1 →
    gateAt C' k = ⟨(gateAt C (rho r k)).op, (gateAt C (rho r k)).inputs.map (tau n r b)⟩

lemma transfer (n : ℕ) (C C' : Circuit) (r b : ℕ) (x : Fin n → Bool) (R : Bool → Bool → Prop)
    (hRrefl : ∀ a, R a a) (hRtrans : ∀ a b c, R a b → R b c → R a c)
    (hRand : ∀ (l : List ℕ) (f f' : ℕ → Bool), (∀ w ∈ l, R (f w) (f' w)) →
      R (GateOp.and.eval (l.map f)) (GateOp.and.eval (l.map f')))
    (hRor : ∀ (l : List ℕ) (f f' : ℕ → Bool), (∀ w ∈ l, R (f w) (f' w)) →
      R (GateOp.or.eval (l.map f)) (GateOp.or.eval (l.map f')))
    (hC : AOB n C) (hC' : AOB n C') (hr : r < C.gates.length) (hb : b < n + r)
    (hlen : C.gates.length - 1 ≤ C'.gates.length)
    (hred : IsRedirect n C C' r b) :
    ∀ w, w < n + C.gates.length → (n + r ≤ w → R (wv n C x (n + r)) (wv n C x b)) →
      R (wv n C x w) (wv n C' x (tau n r b w)) := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hw hR0
    by_cases h1 : w < n
    · have ht : tau n r b w = w := by unfold tau; rw [if_pos (by omega)]
      rw [ht, wv_input n C x w h1, wv_input n C' x w h1]
      exact hRrefl _
    · obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
      by_cases hk : k = r
      · subst hk
        have ht : tau n k b (n + k) = b := by unfold tau; simp
        have htb : tau n k b b = b := by unfold tau; rw [if_pos hb]
        have h2 := ih b (by omega) (by omega) (fun h => absurd h (by omega))
        rw [htb] at h2
        rw [ht]
        exact hRtrans _ _ _ (hR0 le_rfl) h2
      · have hkm : k < C.gates.length := by omega
        obtain ⟨k', hk'1, hk'2, hk'3⟩ : ∃ k', tau n r b (n + k) = n + k' ∧ rho r k' = k ∧
            k' < C.gates.length - 1 := by
          by_cases hkr : k < r
          · refine ⟨k, ?_, ?_, by omega⟩
            · unfold tau; rw [if_pos (by omega)]
            · unfold rho; rw [if_pos hkr]
          · refine ⟨k - 1, ?_, ?_, by omega⟩
            · unfold tau; rw [if_neg (by omega), if_neg (by omega)]; omega
            · unfold rho; rw [if_neg (by omega)]; omega
        have hg := hred k' hk'3
        rw [hk'2] at hg
        rw [hk'1, wv_rec n C x hC k hkm, wv_rec n C' x hC' k' (by omega), hg]
        simp only [List.map_map]
        have hin : ∀ w ∈ (gateAt C k).inputs,
            R (wv n C x w) ((wv n C' x ∘ tau n r b) w) := by
          intro w hw'
          have hlt := (hC k hkm).2 w hw'
          exact ih w hlt (by omega) (fun h => hR0 (by omega))
        rcases (hC k hkm).1 with hop | hop
        · rw [hop]; exact hRand _ _ _ hin
        · rw [hop]; exact hRor _ _ _ hin

lemma transfer_eq (n : ℕ) (C C' : Circuit) (r b : ℕ) (x : Fin n → Bool)
    (hC : AOB n C) (hC' : AOB n C') (hr : r < C.gates.length) (hb : b < n + r)
    (hlen : C.gates.length - 1 ≤ C'.gates.length)
    (hred : IsRedirect n C C' r b) :
    ∀ w, w < n + C.gates.length → (n + r ≤ w → wv n C x (n + r) = wv n C x b) →
      wv n C x w = wv n C' x (tau n r b w) := by
  refine transfer n C C' r b x (fun a b => a = b) (fun _ => rfl) (fun _ _ _ h1 h2 => h1.trans h2)
    ?_ ?_ hC hC' hr hb hlen hred
  · intro l f f' h
    rw [List.map_congr_left h]
  · intro l f f' h
    rw [List.map_congr_left h]

lemma transfer_le (n : ℕ) (C C' : Circuit) (r b : ℕ) (x : Fin n → Bool)
    (hC : AOB n C) (hC' : AOB n C') (hr : r < C.gates.length) (hb : b < n + r)
    (hlen : C.gates.length - 1 ≤ C'.gates.length)
    (hred : IsRedirect n C C' r b) :
    ∀ w, w < n + C.gates.length →
      (n + r ≤ w → (wv n C x (n + r) = true → wv n C x b = true)) →
      (wv n C x w = true → wv n C' x (tau n r b w) = true) := by
  refine transfer n C C' r b x (fun a b => a = true → b = true) (fun _ h => h)
    (fun _ _ _ h1 h2 h => h2 (h1 h)) ?_ ?_ hC hC' hr hb hlen hred
  · intro l f f' h hall
    simp only [GateOp.eval] at hall ⊢
    rw [List.all_eq_true] at hall ⊢
    intro v hv
    rw [List.mem_map] at hv
    obtain ⟨w, hw, rfl⟩ := hv
    exact h w hw (hall (f w) (List.mem_map.mpr ⟨w, hw, rfl⟩))
  · intro l f f' h hany
    simp only [GateOp.eval] at hany ⊢
    rw [List.any_eq_true] at hany ⊢
    obtain ⟨v, hv, hv2⟩ := hany
    rw [List.mem_map] at hv
    obtain ⟨w, hw, rfl⟩ := hv
    exact ⟨f' w, List.mem_map.mpr ⟨w, hw, rfl⟩, h w hw hv2⟩


def gfun (n : ℕ) (C : Circuit) (r b : ℕ) (top : Gate) (k : ℕ) : Gate :=
  if k < C.gates.length - 1 then
    ⟨(gateAt C (rho r k)).op, (gateAt C (rho r k)).inputs.map (tau n r b)⟩ else top

def V1 (n : ℕ) (C : Circuit) (r b : ℕ) : Circuit :=
  ⟨(List.range (C.gates.length - 1)).map (gfun n C r b ⟨GateOp.or, []⟩), tau n r b C.output⟩

def V2 (n : ℕ) (C : Circuit) (r b i : ℕ) : Circuit :=
  ⟨(List.range C.gates.length).map (gfun n C r b ⟨GateOp.or, [tau n r b C.output, n + i]⟩),
    n + C.gates.length - 1⟩

lemma gateAt_range (m : ℕ) (g : ℕ → Gate) (out k : ℕ) (hk : k < m) :
    gateAt ⟨(List.range m).map g, out⟩ k = g k := by
  simp [gateAt, List.getD_eq_getElem?_getD, hk]

lemma V1_len (n : ℕ) (C : Circuit) (r b : ℕ) :
    (V1 n C r b).gates.length = C.gates.length - 1 := by simp [V1]

lemma V2_len (n : ℕ) (C : Circuit) (r b i : ℕ) :
    (V2 n C r b i).gates.length = C.gates.length := by simp [V2]

lemma V1_gate (n : ℕ) (C : Circuit) (r b k : ℕ) (hk : k < C.gates.length - 1) :
    gateAt (V1 n C r b) k =
      ⟨(gateAt C (rho r k)).op, (gateAt C (rho r k)).inputs.map (tau n r b)⟩ := by
  unfold V1
  rw [gateAt_range _ _ _ _ hk]
  unfold gfun
  rw [if_pos hk]

lemma V2_gate (n : ℕ) (C : Circuit) (r b i k : ℕ) (hk : k < C.gates.length - 1) :
    gateAt (V2 n C r b i) k =
      ⟨(gateAt C (rho r k)).op, (gateAt C (rho r k)).inputs.map (tau n r b)⟩ := by
  unfold V2
  rw [gateAt_range _ _ _ _ (by omega)]
  unfold gfun
  rw [if_pos hk]

lemma V2_top (n : ℕ) (C : Circuit) (r b i : ℕ) (hm : 0 < C.gates.length) :
    gateAt (V2 n C r b i) (C.gates.length - 1) =
      ⟨GateOp.or, [tau n r b C.output, n + i]⟩ := by
  unfold V2
  rw [gateAt_range _ _ _ _ (by omega)]
  unfold gfun
  rw [if_neg (by omega)]

def AO2 (n : ℕ) (C : Circuit) : Prop :=
  ∀ j, j < C.gates.length →
    ((gateAt C j).op = GateOp.and ∨ (gateAt C j).op = GateOp.or) ∧
      (∃ a b, (gateAt C j).inputs = [a, b]) ∧ ∀ i ∈ (gateAt C j).inputs, i < n + j

lemma aob {n : ℕ} {C : Circuit} (h : AO2 n C) : AOB n C :=
  fun j hj => ⟨(h j hj).1, (h j hj).2.2⟩

lemma rho_lt (r k m : ℕ) (hr : r < m) (hk : k < m - 1) : rho r k < m := by
  unfold rho; split_ifs <;> omega

lemma tau_lt (n r b w k : ℕ) (hb : b < n + r) (hw : w < n + rho r k) :
    tau n r b w < n + k := by
  unfold tau; unfold rho at hw; split_ifs at hw ⊢ <;> omega

lemma tau_low (n r b w : ℕ) (hw : w < n + r) : tau n r b w = w := by
  unfold tau; rw [if_pos hw]

lemma tau_rho (n r b k : ℕ) : tau n r b (n + rho r k) = n + k := by
  unfold tau rho; split_ifs <;> omega

lemma eval_or_pair (f : ℕ → Bool) (a b : ℕ) :
    GateOp.or.eval ([a, b].map f) = (f a || f b) := by simp [GateOp.eval]

lemma eval_and_pair (f : ℕ → Bool) (a b : ℕ) :
    GateOp.and.eval ([a, b].map f) = (f a && f b) := by simp [GateOp.eval]

lemma V1_AO2 (n : ℕ) (C : Circuit) (r b : ℕ) (hC : AO2 n C) (hr : r < C.gates.length)
    (hb : b < n + r) : AO2 n (V1 n C r b) := by
  intro k hk
  rw [V1_len] at hk
  rw [V1_gate n C r b k hk]
  obtain ⟨h1, ⟨a, c, h2⟩, h3⟩ := hC (rho r k) (rho_lt r k _ hr hk)
  refine ⟨h1, ⟨tau n r b a, tau n r b c, by simp [h2]⟩, ?_⟩
  intro w hw
  simp only [List.mem_map] at hw
  obtain ⟨w0, hw0, rfl⟩ := hw
  exact tau_lt n r b w0 k hb (h3 w0 hw0)

lemma V2_AO2 (n : ℕ) (C : Circuit) (r b i : ℕ) (hC : AO2 n C) (hr : r < C.gates.length)
    (hb : b < n + r) (hi : i < r) (hout : C.output < n + C.gates.length) :
    AO2 n (V2 n C r b i) := by
  intro k hk
  rw [V2_len] at hk
  by_cases hk1 : k < C.gates.length - 1
  · rw [V2_gate n C r b i k hk1]
    obtain ⟨h1, ⟨a, c, h2⟩, h3⟩ := hC (rho r k) (rho_lt r k _ hr hk1)
    refine ⟨h1, ⟨tau n r b a, tau n r b c, by simp [h2]⟩, ?_⟩
    intro w hw
    simp only [List.mem_map] at hw
    obtain ⟨w0, hw0, rfl⟩ := hw
    exact tau_lt n r b w0 k hb (h3 w0 hw0)
  · have hk2 : k = C.gates.length - 1 := by omega
    subst hk2
    rw [V2_top n C r b i (by omega)]
    refine ⟨Or.inr rfl, ⟨_, _, rfl⟩, ?_⟩
    intro w hw
    have hw' : w = tau n r b C.output ∨ w = n + i := by simpa using hw
    rcases hw' with rfl | rfl
    · unfold tau; split_ifs <;> omega
    · omega

lemma V1_red (n : ℕ) (C : Circuit) (r b : ℕ) : IsRedirect n C (V1 n C r b) r b :=
  fun k hk => V1_gate n C r b k hk

lemma V2_red (n : ℕ) (C : Circuit) (r b i : ℕ) : IsRedirect n C (V2 n C r b i) r b :=
  fun k hk => V2_gate n C r b i k hk

lemma V1_fun (n : ℕ) (C : Circuit) (r b : ℕ) (x : Fin n → Bool) (hC : AO2 n C)
    (hr : r < C.gates.length) (hb : b < n + r) (hout : C.output < n + C.gates.length)
    (h1 : wv n C x b = true → wv n C x C.output = true)
    (h2 : wv n C x b = false → wv n C x (n + r) = false) :
    wv n (V1 n C r b) x (V1 n C r b).output = wv n C x C.output := by
  have hC' := V1_AO2 n C r b hC hr hb
  have hlen : C.gates.length - 1 ≤ (V1 n C r b).gates.length := by rw [V1_len]
  show wv n (V1 n C r b) x (tau n r b C.output) = wv n C x C.output
  cases hbv : wv n C x b with
  | true =>
    rw [h1 hbv]
    exact transfer_le n C _ r b x (aob hC) (aob hC') hr hb hlen (V1_red n C r b) C.output hout
      (fun _ _ => hbv) (h1 hbv)
  | false =>
    exact (transfer_eq n C _ r b x (aob hC) (aob hC') hr hb hlen (V1_red n C r b) C.output hout
      (fun _ => by rw [h2 hbv, hbv])).symm

lemma V2_low (n : ℕ) (C : Circuit) (r b i : ℕ) (x : Fin n → Bool) (hC : AO2 n C)
    (hr : r < C.gates.length) (hb : b < n + r) (hi : i < r)
    (hout : C.output < n + C.gates.length) :
    ∀ w, w < n + r → wv n (V2 n C r b i) x w = wv n C x w := by
  intro w hw
  have h := transfer_eq n C _ r b x (aob hC) (aob (V2_AO2 n C r b i hC hr hb hi hout)) hr hb
    (by rw [V2_len]; omega) (V2_red n C r b i) w (by omega) (fun h => absurd h (by omega))
  rw [tau_low n r b w hw] at h
  exact h.symm

lemma V2_same (n : ℕ) (C : Circuit) (r b i : ℕ) (x : Fin n → Bool) (hC : AO2 n C)
    (hr : r < C.gates.length) (hb : b < n + r) (hi : i < r)
    (hout : C.output < n + C.gates.length) (h0 : wv n C x (n + r) = wv n C x b) :
    ∀ w, w < n + C.gates.length → wv n (V2 n C r b i) x (tau n r b w) = wv n C x w := by
  intro w hw
  exact (transfer_eq n C _ r b x (aob hC) (aob (V2_AO2 n C r b i hC hr hb hi hout)) hr hb
    (by rw [V2_len]; omega) (V2_red n C r b i) w hw (fun _ => h0)).symm

lemma V2_out (n : ℕ) (C : Circuit) (r b i : ℕ) (x : Fin n → Bool) (hC : AO2 n C)
    (hr : r < C.gates.length) (hb : b < n + r) (hi : i < r)
    (hout : C.output < n + C.gates.length)
    (hbel : wv n C x (n + i) = true → wv n C x C.output = true)
    (h0 : wv n C x (n + i) = false → wv n C x (n + r) = wv n C x b) :
    wv n (V2 n C r b i) x (V2 n C r b i).output = wv n C x C.output := by
  have hC' := V2_AO2 n C r b i hC hr hb hi hout
  have hm : 0 < C.gates.length := by omega
  have e : (V2 n C r b i).output = n + (C.gates.length - 1) := by
    show n + C.gates.length - 1 = _
    omega
  rw [e, wv_rec n _ x (aob hC') (C.gates.length - 1) (by rw [V2_len]; omega),
    V2_top n C r b i hm]
  have hi' := V2_low n C r b i x hC hr hb hi hout (n + i) (by omega)
  dsimp only
  rw [eval_or_pair, hi']
  cases hv : wv n C x (n + i) with
  | true => rw [hbel hv]; simp
  | false =>
    rw [V2_same n C r b i x hC hr hb hi hout (h0 hv) C.output hout]; simp

lemma V1_fun_top (n : ℕ) (D : Circuit) (r c i y : ℕ) (x : Fin n → Bool) (hD : AO2 n D)
    (hr : r < D.gates.length - 1) (hc : c < n + r) (hi : i < r)
    (hout : D.output = n + (D.gates.length - 1))
    (htop : gateAt D (D.gates.length - 1) = ⟨GateOp.or, [y, n + i]⟩)
    (h0 : wv n D x (n + i) = false → wv n D x (n + r) = wv n D x c) :
    wv n (V1 n D r c) x (V1 n D r c).output = wv n D x D.output := by
  have hr' : r < D.gates.length := by omega
  have hE := V1_AO2 n D r c hD hr' hc
  have hlen : D.gates.length - 1 ≤ (V1 n D r c).gates.length := by rw [V1_len]
  have hred := V1_red n D r c
  show wv n (V1 n D r c) x (tau n r c D.output) = wv n D x D.output
  cases hv : wv n D x (n + i) with
  | false =>
    exact (transfer_eq n D _ r c x (aob hD) (aob hE) hr' hc hlen hred D.output (by omega)
      (fun _ => h0 hv)).symm
  | true =>
    have e1 : wv n D x D.output = true := by
      rw [hout, wv_rec n D x (aob hD) _ (by omega), htop]
      dsimp only
      rw [eval_or_pair, hv]; simp
    have e2 : tau n r c D.output = n + (D.gates.length - 2) := by
      rw [hout]; unfold tau; rw [if_neg (by omega), if_neg (by omega)]; omega
    have e3 : gateAt (V1 n D r c) (D.gates.length - 2) =
        ⟨GateOp.or, [tau n r c y, n + i]⟩ := by
      rw [V1_gate n D r c _ (by omega)]
      have hrho : rho r (D.gates.length - 2) = D.gates.length - 1 := by
        unfold rho; rw [if_neg (by omega)]; omega
      rw [hrho, htop]
      simp [tau_low n r c (n + i) (by omega)]
    have e4 : wv n (V1 n D r c) x (n + i) = true := by
      have h := transfer_eq n D _ r c x (aob hD) (aob hE) hr' hc hlen hred (n + i) (by omega)
        (fun h => absurd h (by omega))
      rw [tau_low n r c (n + i) (by omega)] at h
      rw [← h, hv]
    rw [e1, e2, wv_rec n _ x (aob hE) _ (by rw [V1_len]; omega), e3]
    dsimp only
    rw [eval_or_pair, e4]; simp

def Least (n : ℕ) (C : Circuit) : Prop :=
  AO2 n C ∧ ∀ D : Circuit, AO2 n D → (∀ x, wv n D x D.output = wv n C x C.output) →
    C.gates.length ≤ D.gates.length

lemma reader_or (n : ℕ) (C : Circuit) (hL : Least n C) (hout : C.output < n + C.gates.length)
    (i r : ℕ) (hr : r < C.gates.length)
    (hbel : ∀ x, wv n C x (n + i) = true → wv n C x C.output = true)
    (hin : n + i ∈ (gateAt C r).inputs) :
    (gateAt C r).op = GateOp.or ∧ ∃ c, c ≠ n + i ∧ c < n + r ∧
      ((gateAt C r).inputs = [n + i, c] ∨ (gateAt C r).inputs = [c, n + i]) := by
  obtain ⟨hop, ⟨a, c0, hab⟩, hlt⟩ := hL.1 r hr
  have hir : n + i < n + r := hlt _ hin
  have hin' : n + i = a ∨ n + i = c0 := by rw [hab] at hin; simpa using hin
  by_contra hcon
  have key : ∀ x, wv n C x (n + i) = false → wv n C x (n + r) = false := by
    intro x hx
    rw [wv_rec n C x (aob hL.1) r hr, hab]
    rcases hop with hop | hop
    · rw [hop, eval_and_pair]
      rcases hin' with h | h
      · rw [← h, hx]; rfl
      · rw [← h, hx]; simp
    · rw [hop, eval_or_pair]
      have ha : a = n + i := by
        by_contra hne
        apply hcon
        refine ⟨hop, a, hne, hlt a (by rw [hab]; simp), ?_⟩
        rcases hin' with h | h
        · exact absurd h.symm hne
        · right; rw [hab, h]
      have hc : c0 = n + i := by
        by_contra hne
        apply hcon
        refine ⟨hop, c0, hne, hlt c0 (by rw [hab]; simp), ?_⟩
        left; rw [hab, ha]
      rw [ha, hc, hx]; rfl
  have hfun : ∀ x, wv n (V1 n C r (n + i)) x (V1 n C r (n + i)).output = wv n C x C.output :=
    fun x => V1_fun n C r (n + i) x hL.1 hr hir hout (hbel x) (key x)
  have hle := hL.2 _ (V1_AO2 n C r (n + i) hL.1 hr hir) hfun
  rw [V1_len] at hle
  omega

lemma reader_unique (n : ℕ) (C : Circuit) (hL : Least n C)
    (hout : C.output < n + C.gates.length) (i r1 r2 : ℕ) (h12 : r1 < r2)
    (hr2 : r2 < C.gates.length)
    (hbel : ∀ x, wv n C x (n + i) = true → wv n C x C.output = true)
    (hin1 : n + i ∈ (gateAt C r1).inputs) (hin2 : n + i ∈ (gateAt C r2).inputs) : False := by
  have hr1 : r1 < C.gates.length := by omega
  obtain ⟨hop1, c1, hc1, hc1lt, hi1⟩ := reader_or n C hL hout i r1 hr1 hbel hin1
  obtain ⟨hop2, c2, hc2, hc2lt, hi2⟩ := reader_or n C hL hout i r2 hr2 hbel hin2
  have hir1 : i < r1 := by have := (hL.1 r1 hr1).2.2 _ hin1; omega
  have hir2 : i < r2 := by omega
  have k2 : ∀ x, wv n C x (n + i) = false → wv n C x (n + r2) = wv n C x c2 := by
    intro x hx
    rw [wv_rec n C x (aob hL.1) r2 hr2, hop2]
    rcases hi2 with h | h
    · rw [h, eval_or_pair, hx]; rfl
    · rw [h, eval_or_pair, hx]; simp
  have k1 : ∀ x, wv n C x (n + i) = false → wv n C x (n + r1) = wv n C x c1 := by
    intro x hx
    rw [wv_rec n C x (aob hL.1) r1 hr1, hop1]
    rcases hi1 with h | h
    · rw [h, eval_or_pair, hx]; rfl
    · rw [h, eval_or_pair, hx]; simp
  have hD : AO2 n (V2 n C r2 c2 i) := V2_AO2 n C r2 c2 i hL.1 hr2 hc2lt hir2 hout
  have hDlen := V2_len n C r2 c2 i
  have hDfun : ∀ x, wv n (V2 n C r2 c2 i) x (V2 n C r2 c2 i).output = wv n C x C.output :=
    fun x => V2_out n C r2 c2 i x hL.1 hr2 hc2lt hir2 hout (hbel x) (k2 x)
  have hDout : (V2 n C r2 c2 i).output = n + ((V2 n C r2 c2 i).gates.length - 1) := by
    rw [hDlen]
    show n + C.gates.length - 1 = n + (C.gates.length - 1)
    omega
  have hDtop : gateAt (V2 n C r2 c2 i) ((V2 n C r2 c2 i).gates.length - 1) =
      ⟨GateOp.or, [tau n r2 c2 C.output, n + i]⟩ := by
    rw [hDlen]
    exact V2_top n C r2 c2 i (by omega)
  have h0 : ∀ x, wv n (V2 n C r2 c2 i) x (n + i) = false →
      wv n (V2 n C r2 c2 i) x (n + r1) = wv n (V2 n C r2 c2 i) x c1 := by
    intro x hx
    rw [V2_low n C r2 c2 i x hL.1 hr2 hc2lt hir2 hout (n + i) (by omega)] at hx
    rw [V2_low n C r2 c2 i x hL.1 hr2 hc2lt hir2 hout (n + r1) (by omega),
      V2_low n C r2 c2 i x hL.1 hr2 hc2lt hir2 hout c1 (by omega)]
    exact k1 x hx
  have hEfun : ∀ x, wv n (V1 n (V2 n C r2 c2 i) r1 c1) x (V1 n (V2 n C r2 c2 i) r1 c1).output =
      wv n C x C.output := fun x =>
    (V1_fun_top n (V2 n C r2 c2 i) r1 c1 i (tau n r2 c2 C.output) x hD (by rw [hDlen]; omega)
      hc1lt hir1 hDout hDtop (h0 x)).trans (hDfun x)
  have hle := hL.2 _ (V1_AO2 n (V2 n C r2 c2 i) r1 c1 hD (by rw [hDlen]; omega) hc1lt) hEfun
  rw [V1_len, hDlen] at hle
  omega

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

lemma V2_cone (n : ℕ) (C : Circuit) (r c i : ℕ) (hC : AO2 n C) (hr : r < C.gates.length)
    (hc : c < n + r) (hcin : c ∈ (gateAt C r).inputs) (a' : ℕ) :
    ∀ b', b' < C.gates.length - 1 → InCone n (V2 n C r c i) a' b' →
      InCone n C (rho r a') (rho r b') := by
  intro b'
  induction b' using Nat.strong_induction_on with
  | _ b' ih =>
    intro hb' h
    rw [inCone_iff] at h
    obtain ⟨_, k', hk', hin, h3⟩ := h
    rw [V2_gate n C r c i b' hb'] at hin
    simp only [List.mem_map] at hin
    obtain ⟨w, hw, hwk⟩ := hin
    have hbm : rho r b' < C.gates.length := rho_lt r b' _ hr hb'
    have hwlt := (hC (rho r b') hbm).2.2 w hw
    have hrb : rho r b' ≤ b' + 1 := by unfold rho; split_ifs <;> omega
    have hrb2 : b' < r → rho r b' = b' := by intro h; unfold rho; rw [if_pos h]
    have hstep : InCone n C (rho r k') (rho r b') := by
      unfold tau at hwk
      by_cases h1 : w < n + r
      · rw [if_pos h1] at hwk
        have e : rho r k' = k' := by unfold rho; rw [if_pos (by omega)]
        rw [e, inCone_iff]
        refine ⟨hbm, k', by omega, ?_, Or.inl rfl⟩
        rw [← hwk]; exact hw
      · rw [if_neg h1] at hwk
        by_cases h2 : w = n + r
        · rw [if_pos h2] at hwk
          have e : rho r k' = k' := by unfold rho; rw [if_pos (by omega)]
          rw [e]
          have s1 : InCone n C k' r := by
            rw [inCone_iff]
            refine ⟨hr, k', by omega, ?_, Or.inl rfl⟩
            rw [← hwk]; exact hcin
          have s2 : InCone n C r (rho r b') := by
            rw [inCone_iff]
            refine ⟨hbm, r, by omega, ?_, Or.inl rfl⟩
            rw [← h2]; exact hw
          exact inCone_trans n C k' r s1 _ s2
        · rw [if_neg h2] at hwk
          have e : rho r k' = k' + 1 := by unfold rho; rw [if_neg (by omega)]
          rw [e, inCone_iff]
          refine ⟨hbm, k' + 1, by omega, ?_, Or.inl rfl⟩
          have e2 : n + (k' + 1) = w := by omega
          rw [e2]; exact hw
    rcases h3 with h3 | h3
    · rw [h3]; exact hstep
    · exact inCone_trans n C _ _ (ih k' hk' (by omega) h3) _ hstep

lemma V2_no_reader (n : ℕ) (C : Circuit) (r c i : ℕ) (hr : r < C.gates.length)
    (hi : i < r) (hci : c ≠ n + i)
    (huniq : ∀ k, k < C.gates.length → n + i ∈ (gateAt C k).inputs → k = r) :
    ∀ k', k' < C.gates.length - 1 → n + i ∉ (gateAt (V2 n C r c i) k').inputs := by
  intro k' hk' hin
  rw [V2_gate n C r c i k' hk'] at hin
  simp only [List.mem_map] at hin
  obtain ⟨w, hw, hwk⟩ := hin
  have hbm : rho r k' < C.gates.length := rho_lt r k' _ hr hk'
  have hne : rho r k' ≠ r := by unfold rho; split_ifs <;> omega
  unfold tau at hwk
  by_cases h1 : w < n + r
  · rw [if_pos h1] at hwk
    rw [hwk] at hw
    exact hne (huniq _ hbm hw)
  · rw [if_neg h1] at hwk
    by_cases h2 : w = n + r
    · rw [if_pos h2] at hwk
      exact hci hwk
    · rw [if_neg h2] at hwk
      omega

lemma V2_no_cone (n : ℕ) (C : Circuit) (r c i : ℕ) (hr : r < C.gates.length)
    (hi : i < r) (hci : c ≠ n + i)
    (huniq : ∀ k, k < C.gates.length → n + i ∈ (gateAt C k).inputs → k = r) :
    ∀ j', j' < C.gates.length - 1 → ¬ InCone n (V2 n C r c i) i j' := by
  intro j' hj' h
  obtain ⟨r', _, _, hrin, h4⟩ := inCone_reader n _ i j' h
  have hr'j : r' ≤ j' := by
    rcases h4 with h4 | h4
    · omega
    · have := (inCone_lt n _ r' j' h4).1
      omega
  exact V2_no_reader n C r c i hr hi hci huniq r' (by omega) hrin


lemma rho_inj (r : ℕ) : Function.Injective (rho r) := by
  intro a b h
  unfold rho at h
  split_ifs at h <;> omega

lemma rho_ne (r k : ℕ) : rho r k ≠ r := by
  unfold rho; split_ifs <;> omega

lemma rho_surj (r k m : ℕ) (hr : r < m) (hk : k < m) (hne : k ≠ r) : ∃ k', k' < m - 1 ∧ rho r k' = k := by
  by_cases h : k < r
  · exact ⟨k, by omega, by unfold rho; rw [if_pos h]⟩
  · exact ⟨k - 1, by omega, by unfold rho; rw [if_neg (by omega)]; omega⟩

lemma wires_len (n : ℕ) (C : Circuit) (x : Fin n → Bool) :
    (C.wires (List.ofFn x)).length = n + C.gates.length := by
  rw [wires_eq, foldl_len, List.length_ofFn]

lemma out_lt (n : ℕ) (C : Circuit) (x : Fin n → Bool) (h : wv n C x C.output = true) :
    C.output < n + C.gates.length := by
  by_contra hge
  unfold wv at h
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by rw [wires_len]; omega)] at h
  simp at h

lemma step3_core (n : ℕ) (C : Circuit) (hL : Least n C) (hout : C.output < n + C.gates.length)
    (i j : ℕ) (hbel : ∀ x, wv n C x (n + i) = true → wv n C x C.output = true)
    (hcone : InCone n C i j) :
    ∃ r c, r < C.gates.length ∧ i < r ∧ c < n + r ∧ c ≠ n + i ∧ c ∈ (gateAt C r).inputs ∧
      (gateAt C r).op = GateOp.or ∧
      (∀ k, k < C.gates.length → n + i ∈ (gateAt C k).inputs → k = r) ∧
      (∀ x, wv n C x (n + i) = false → wv n C x (n + r) = wv n C x c) := by
  obtain ⟨r, hr, hir, hrin, _⟩ := inCone_reader n C i j hcone
  obtain ⟨hop, c, hc, hclt, hi⟩ := reader_or n C hL hout i r hr hbel hrin
  refine ⟨r, c, hr, hir, hclt, hc, ?_, hop, ?_, ?_⟩
  · rcases hi with h | h <;> rw [h] <;> simp
  · intro k hk hkin
    rcases Nat.lt_trichotomy k r with h | h | h
    · exact (reader_unique n C hL hout i k r h hr hbel hkin hrin).elim
    · exact h
    · exact (reader_unique n C hL hout i r k h hk hbel hrin hkin).elim
  · intro x hx
    rw [wv_rec n C x (aob hL.1) r hr, hop]
    rcases hi with h | h
    · rw [h, eval_or_pair, hx]; rfl
    · rw [h, eval_or_pair, hx]; simp

lemma least_of_same (n : ℕ) (C D : Circuit) (hL : Least n C) (hD : AO2 n D)
    (hfun : ∀ x, wv n D x D.output = wv n C x C.output)
    (hlen : D.gates.length = C.gates.length) : Least n D :=
  ⟨hD, fun E hE hEf => by rw [hlen]; exact hL.2 E hE (fun x => (hEf x).trans (hfun x))⟩

lemma V2_gateval (n : ℕ) (C : Circuit) (r c i : ℕ) (x : Fin n → Bool) (hC : AO2 n C)
    (hr : r < C.gates.length) (hb : c < n + r) (hi : i < r)
    (hout : C.output < n + C.gates.length) (h0 : wv n C x (n + r) = wv n C x c)
    (k' : ℕ) (hk' : k' < C.gates.length - 1) :
    wv n (V2 n C r c i) x (n + k') = wv n C x (n + rho r k') := by
  have h := V2_same n C r c i x hC hr hb hi hout h0 (n + rho r k')
    (by have := rho_lt r k' _ hr hk'; omega)
  rw [tau_rho] at h
  exact h

lemma V2_below (n : ℕ) (C : Circuit) (r c i : ℕ) (F : (Fin n → Bool) → Bool) (hC : AO2 n C)
    (hr : r < C.gates.length) (hb : c < n + r) (hi : i < r)
    (hout : C.output < n + C.gates.length)
    (hbelF : ∀ x, wv n C x (n + i) = true → F x = true)
    (h0 : ∀ x, wv n C x (n + i) = false → wv n C x (n + r) = wv n C x c)
    (k' : ℕ) (hk' : k' < C.gates.length - 1) :
    (∀ x, wv n (V2 n C r c i) x (n + k') = true → F x = true) ↔
      (∀ x, wv n C x (n + rho r k') = true → F x = true) := by
  constructor
  · intro h x hv
    cases hx : wv n C x (n + i) with
    | true => exact hbelF x hx
    | false =>
      apply h x
      rw [V2_gateval n C r c i x hC hr hb hi hout (h0 x hx) k' hk']
      exact hv
  · intro h x hv
    cases hx : wv n C x (n + i) with
    | true => exact hbelF x hx
    | false =>
      apply h x
      rw [← V2_gateval n C r c i x hC hr hb hi hout (h0 x hx) k' hk']
      exact hv


lemma card_filter_rho (m r : ℕ) (hr : r < m) (P Q : ℕ → Prop) [DecidablePred P]
    [DecidablePred Q]
    (hPQ : ∀ k', k' < m - 1 → (Q k' ↔ P (rho r k'))) (hPr : ¬ P r) (hQ : ¬ Q (m - 1)) :
    ((Finset.range m).filter Q).card = ((Finset.range m).filter P).card := by
  apply Finset.card_bij (fun k' _ => rho r k')
  · intro k' hk'
    rw [Finset.mem_filter, Finset.mem_range] at hk' ⊢
    have hlt : k' < m - 1 := by
      rcases Nat.lt_or_ge k' (m - 1) with h | h
      · exact h
      · have hk'' : k' = m - 1 := by omega
        rw [hk''] at hk'
        exact absurd hk'.2 hQ
    exact ⟨rho_lt r k' m hr hlt, (hPQ k' hlt).mp hk'.2⟩
  · intro a _ b _ h
    exact rho_inj r h
  · intro k hk
    rw [Finset.mem_filter, Finset.mem_range] at hk
    have hne : k ≠ r := fun h => hPr (h ▸ hk.2)
    obtain ⟨k', hk'1, hk'2⟩ := rho_surj r k m hr hk.1 hne
    refine ⟨k', ?_, hk'2⟩
    rw [Finset.mem_filter, Finset.mem_range]
    exact ⟨by omega, (hPQ k' hk'1).mpr (hk'2 ▸ hk.2)⟩

lemma card_pairs_rho (m r : ℕ) (hr : r < m) (P Q : ℕ → ℕ → Prop)
    [DecidablePred (fun p : ℕ × ℕ => P p.1 p.2)] [DecidablePred (fun p : ℕ × ℕ => Q p.1 p.2)]
    (hQP : ∀ a' b', a' < m → b' < m → Q a' b' →
      a' < m - 1 ∧ b' < m - 1 ∧ P (rho r a') (rho r b'))
    (i j : ℕ) (hi : i < m) (hj : j < m) (hP : P i j)
    (hne : ∀ a' b', Q a' b' → ¬ (rho r a' = i ∧ rho r b' = j)) :
    ((Finset.range m ×ˢ Finset.range m).filter (fun p : ℕ × ℕ => Q p.1 p.2)).card <
      ((Finset.range m ×ˢ Finset.range m).filter (fun p : ℕ × ℕ => P p.1 p.2)).card := by
  have hinj : Function.Injective (fun p : ℕ × ℕ => (rho r p.1, rho r p.2)) := by
    intro p q h
    simp only [Prod.mk.injEq] at h
    exact Prod.ext (rho_inj r h.1) (rho_inj r h.2)
  rw [← Finset.card_image_of_injective _ hinj]
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_of_subset]
  · refine ⟨(i, j), ?_, ?_⟩
    · rw [Finset.mem_filter, Finset.mem_product, Finset.mem_range, Finset.mem_range]
      exact ⟨⟨hi, hj⟩, hP⟩
    · intro hmem
      rw [Finset.mem_image] at hmem
      obtain ⟨⟨a', b'⟩, hab, heq⟩ := hmem
      rw [Finset.mem_filter] at hab
      simp only [Prod.mk.injEq] at heq
      exact hne a' b' hab.2 heq
  · intro p hp
    rw [Finset.mem_image] at hp
    obtain ⟨⟨a', b'⟩, hab, rfl⟩ := hp
    rw [Finset.mem_filter, Finset.mem_product, Finset.mem_range, Finset.mem_range] at hab
    obtain ⟨h1, h2, h3⟩ := hQP a' b' hab.1.1 hab.1.2 hab.2
    rw [Finset.mem_filter, Finset.mem_product, Finset.mem_range, Finset.mem_range]
    exact ⟨⟨rho_lt r a' m hr h1, rho_lt r b' m hr h2⟩, h3⟩


lemma step3_struct (n : ℕ) (C : Circuit) (F : (Fin n → Bool) → Bool) (hL : Least n C)
    (hF : ∀ x, wv n C x C.output = F x) (hout : C.output < n + C.gates.length)
    (i j : ℕ) (hbel : ∀ x, wv n C x (n + i) = true → F x = true)
    (hcone : InCone n C i j) :
    ∃ (C' : Circuit) (r : ℕ), r < C.gates.length ∧ i < r ∧ Least n C' ∧
      (∀ x, wv n C' x C'.output = F x) ∧ C'.gates.length = C.gates.length ∧
      (∀ k', k' < C.gates.length - 1 → (gateAt C' k').op = (gateAt C (rho r k')).op) ∧
      (gateAt C' (C.gates.length - 1)).op = GateOp.or ∧ (gateAt C r).op = GateOp.or ∧
      (∀ k', k' < C.gates.length - 1 →
        ((∀ x, wv n C' x (n + k') = true → F x = true) ↔
          (∀ x, wv n C x (n + rho r k') = true → F x = true))) ∧
      (∀ a' b', b' < C.gates.length - 1 → InCone n C' a' b' →
        InCone n C (rho r a') (rho r b')) ∧
      (∀ j', j' < C.gates.length - 1 → ¬ InCone n C' i j') := by
  have hbel' : ∀ x, wv n C x (n + i) = true → wv n C x C.output = true :=
    fun x h => by rw [hF]; exact hbel x h
  obtain ⟨r, c, hr, hir, hclt, hci, hcin, hop, huniq, h0⟩ :=
    step3_core n C hL hout i j hbel' hcone
  have hD := V2_AO2 n C r c i hL.1 hr hclt hir hout
  have hfun : ∀ x, wv n (V2 n C r c i) x (V2 n C r c i).output = wv n C x C.output :=
    fun x => V2_out n C r c i x hL.1 hr hclt hir hout (hbel' x) (h0 x)
  refine ⟨V2 n C r c i, r, hr, hir, least_of_same n C _ hL hD hfun (V2_len n C r c i),
    fun x => (hfun x).trans (hF x), V2_len n C r c i, ?_, ?_, hop, ?_, ?_, ?_⟩
  · intro k' hk'
    rw [V2_gate n C r c i k' hk']
  · rw [V2_top n C r c i (by omega)]
  · intro k' hk'
    exact V2_below n C r c i F hL.1 hr hclt hir hout hbel h0 k' hk'
  · intro a' b' hb' h
    exact V2_cone n C r c i hL.1 hr hclt hcin a' b' hb' h
  · exact V2_no_cone n C r c i hr hir hci huniq

lemma pairs_lt (n : ℕ) (C C' : Circuit) (r i j : ℕ) (hr : r < C.gates.length) (hir : i < r)
    (hlen : C'.gates.length = C.gates.length)
    (hops : ∀ k', k' < C.gates.length - 1 → (gateAt C' k').op = (gateAt C (rho r k')).op)
    (htop : (gateAt C' (C.gates.length - 1)).op = GateOp.or)
    (hcone : ∀ a' b', b' < C.gates.length - 1 → InCone n C' a' b' →
        InCone n C (rho r a') (rho r b'))
    (hno : ∀ j', j' < C.gates.length - 1 → ¬ InCone n C' i j')
    (hi : (gateAt C i).op = GateOp.and) (hj : (gateAt C j).op = GateOp.and)
    (hij : InCone n C i j)
    [DecidablePred (fun p : ℕ × ℕ => (gateAt C p.1).op = GateOp.and ∧
      (gateAt C p.2).op = GateOp.and ∧ InCone n C p.1 p.2)]
    [DecidablePred (fun p : ℕ × ℕ => (gateAt C' p.1).op = GateOp.and ∧
      (gateAt C' p.2).op = GateOp.and ∧ InCone n C' p.1 p.2)] :
    ((Finset.range C'.gates.length ×ˢ Finset.range C'.gates.length).filter
      (fun p : ℕ × ℕ => (gateAt C' p.1).op = GateOp.and ∧
        (gateAt C' p.2).op = GateOp.and ∧ InCone n C' p.1 p.2)).card <
    ((Finset.range C.gates.length ×ˢ Finset.range C.gates.length).filter
      (fun p : ℕ × ℕ => (gateAt C p.1).op = GateOp.and ∧
        (gateAt C p.2).op = GateOp.and ∧ InCone n C p.1 p.2)).card := by
  rw [hlen]
  have hjm := (inCone_lt n C i j hij)
  refine card_pairs_rho C.gates.length r hr
    (fun a b => (gateAt C a).op = GateOp.and ∧ (gateAt C b).op = GateOp.and ∧ InCone n C a b)
    (fun a b => (gateAt C' a).op = GateOp.and ∧ (gateAt C' b).op = GateOp.and ∧
      InCone n C' a b) ?_ i j (by omega) hjm.2 ⟨hi, hj, hij⟩ ?_
  · rintro a' b' _ hb' ⟨ha, hb, hab⟩
    have hb'' : b' < C.gates.length - 1 := by
      rcases Nat.lt_or_ge b' (C.gates.length - 1) with h | h
      · exact h
      · have e : b' = C.gates.length - 1 := by omega
        rw [e, htop] at hb
        exact absurd hb (by simp)
    have ha' := (inCone_lt n C' a' b' hab).1
    have ha'' : a' < C.gates.length - 1 := by omega
    refine ⟨ha'', hb'', ?_, ?_, hcone a' b' hb'' hab⟩
    · rw [← hops a' ha'']; exact ha
    · rw [← hops b' hb'']; exact hb
  · rintro a' b' ⟨_, hb, hab⟩ ⟨h1, _⟩
    have hb'' : b' < C.gates.length - 1 := by
      rcases Nat.lt_or_ge b' (C.gates.length - 1) with h | h
      · exact h
      · have hb3 := (inCone_lt n C' a' b' hab).2
        have e : b' = C.gates.length - 1 := by omega
        rw [e, htop] at hb
        exact absurd hb (by simp)
    have e : rho r i = i := by unfold rho; rw [if_pos hir]
    have e2 : a' = i := rho_inj r (h1.trans e.symm)
    rw [e2] at hab
    exact hno b' hb'' hab

lemma junk_eq (n : ℕ) (C C' : Circuit) (F : (Fin n → Bool) → Bool) (r : ℕ)
    (hr : r < C.gates.length)
    (hlen : C'.gates.length = C.gates.length)
    (hops : ∀ k', k' < C.gates.length - 1 → (gateAt C' k').op = (gateAt C (rho r k')).op)
    (htop : (gateAt C' (C.gates.length - 1)).op = GateOp.or)
    (hopr : (gateAt C r).op = GateOp.or)
    (hbelow : ∀ k', k' < C.gates.length - 1 →
        ((∀ x, wv n C' x (n + k') = true → F x = true) ↔
          (∀ x, wv n C x (n + rho r k') = true → F x = true)))
    [DecidablePred (fun k : ℕ => (gateAt C k).op = GateOp.and ∧
      ¬ ∀ x, wv n C x (n + k) = true → F x = true)]
    [DecidablePred (fun k : ℕ => (gateAt C' k).op = GateOp.and ∧
      ¬ ∀ x, wv n C' x (n + k) = true → F x = true)] :
    ((Finset.range C'.gates.length).filter (fun k : ℕ => (gateAt C' k).op = GateOp.and ∧
      ¬ ∀ x, wv n C' x (n + k) = true → F x = true)).card =
    ((Finset.range C.gates.length).filter (fun k : ℕ => (gateAt C k).op = GateOp.and ∧
      ¬ ∀ x, wv n C x (n + k) = true → F x = true)).card := by
  rw [hlen]
  apply card_filter_rho C.gates.length r hr
  · intro k' hk'
    rw [hops k' hk', hbelow k' hk']
  · rintro ⟨h, _⟩
    rw [hopr] at h
    exact absurd h (by simp)
  · rintro ⟨h, _⟩
    rw [htop] at h
    exact absurd h (by simp)

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

lemma foldl_getD_lt2 (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
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
      rw [Nat.add_zero, foldl_getD_lt2 gs (stepWire w g) w.length h1]
      simp only [List.getElem_cons_zero]
      have h2 : (stepWire w g).getD w.length false =
          g.op.eval (g.inputs.map fun i => w.getD i false) := by
        simp [stepWire, List.getD_eq_getElem?_getD]
      rw [h2]
      congr 1
      apply List.map_congr_left
      intro i _
      by_cases hi : i < w.length
      · rw [if_pos hi, foldl_getD_lt2 gs (stepWire w g) i (by simp [stepWire]; omega)]
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
  unfold val; rw [wires_eq_foldl]; exact foldl_getD_lt2 _ _ _ (by omega)

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

def OpMono (R : Bool → Bool → Prop) : Prop :=
  ∀ (op : GateOp), (op = GateOp.and ∨ op = GateOp.or) → ∀ (l : List ℕ) (f g : ℕ → Bool),
    (∀ i ∈ l, R (f i) (g i)) → R (op.eval (l.map f)) (op.eval (l.map g))

lemma opMono_eq : OpMono Eq := by
  intro op _ l f g h
  rw [List.map_congr_left h]

lemma opMono_imp : OpMono (fun a b => a = true → b = true) := by
  intro op hop l f g h
  rcases hop with rfl | rfl
  · simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id_eq]
    intro h1 i hi; exact h i hi (h1 i hi)
  · simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id_eq]
    rintro ⟨i, hi, h1⟩; exact ⟨i, hi, h i hi h1⟩

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

lemma val_prefix {n : ℕ} {C D : Circuit} {x : List Bool} (hx : x.length = n) {m : ℕ}
    (hmC : m ≤ C.gates.length) (hmD : m ≤ D.gates.length)
    (hg : ∀ k < m, gateAt D k = gateAt C k) : ∀ u, u < n + m → val D x u = val C x u := by
  intro u
  induction u using Nat.strong_induction_on with
  | _ u ih =>
    intro hu
    by_cases hun : u < n
    · rw [val_input hx hun, val_input hx hun]
    · obtain ⟨k, rfl⟩ : ∃ k, u = n + k := ⟨u - n, by omega⟩
      have hk : k < m := by omega
      rw [val_gate hx (by omega), val_gate hx (by omega), hg k hk]
      congr 1
      apply List.map_congr_left
      intro i _
      by_cases hi : i < n + k
      · rw [if_pos hi, if_pos hi]; exact ih i hi (by omega)
      · rw [if_neg hi, if_neg hi]

def aliasWire (w i u : ℕ) : ℕ := if u = w then i else if w < u then u - 1 else u

def aliasGate (w i : ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map (aliasWire w i)⟩

def bypass (n : ℕ) (C : Circuit) (r i : ℕ) : Circuit :=
  ⟨(List.range (C.gates.length - 1)).map (fun k =>
      if k < r then gateAt C k else aliasGate (n + r) i (gateAt C (k + 1))),
    aliasWire (n + r) i C.output⟩

lemma bypass_length (n : ℕ) (C : Circuit) (r i : ℕ) :
    (bypass n C r i).gates.length = C.gates.length - 1 := by simp [bypass]

lemma bypass_output (n : ℕ) (C : Circuit) (r i : ℕ) :
    (bypass n C r i).output = aliasWire (n + r) i C.output := rfl

lemma gateAt_bypass {n : ℕ} {C : Circuit} {r i k : ℕ} (hk : k < C.gates.length - 1) :
    gateAt (bypass n C r i) k =
      if k < r then gateAt C k else aliasGate (n + r) i (gateAt C (k + 1)) := by
  have hk' : k < (bypass n C r i).gates.length := by rw [bypass_length]; exact hk
  rw [gateAt_eq hk']
  simp [bypass]

lemma bypass_val_lt {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {r i : ℕ}
    (hr : r < C.gates.length) : ∀ u, u < n + r → val (bypass n C r i) x u = val C x u := by
  apply val_prefix hx (by omega) (by rw [bypass_length]; omega)
  intro k hk
  rw [gateAt_bypass (by omega), if_pos hk]

lemma aliasWire_self (w i : ℕ) : aliasWire w i w = i := by simp [aliasWire]

lemma aliasWire_lt_self {w i u : ℕ} (hu : u < w) : aliasWire w i u = u := by
  unfold aliasWire; rw [if_neg (by omega), if_neg (by omega)]

lemma aliasWire_gt_self {w i u : ℕ} (hu : w < u) : aliasWire w i u = u - 1 := by
  unfold aliasWire; rw [if_neg (by omega), if_pos hu]

lemma bypass_rel {R : Bool → Bool → Prop} (hrefl : ∀ b, R b b) (hmono : OpMono R)
    {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n)
    (hAO : ∀ k < C.gates.length,
      (gateAt C k).op = GateOp.and ∨ (gateAt C k).op = GateOp.or)
    {r i : ℕ} (hr : r < C.gates.length) (hi : i < n + r ∨ n + C.gates.length ≤ i)
    (hR : (∃ k, r < k ∧ k < C.gates.length ∧ n + r ∈ (gateAt C k).inputs) →
      R (val C x (n + r)) (val C x i)) :
    ∀ u, u ≠ n + r → R (val C x u) (val (bypass n C r i) x (aliasWire (n + r) i u)) := by
  intro u
  induction u using Nat.strong_induction_on with
  | _ u ih =>
    intro hne
    by_cases hlt : u < n + r
    · rw [aliasWire_lt_self hlt, bypass_val_lt hx hr u hlt]; exact hrefl _
    · rw [aliasWire_gt_self (by omega)]
      by_cases hge : n + C.gates.length ≤ u
      · rw [val_ge hx hge, val_ge hx (by rw [bypass_length]; omega)]; exact hrefl _
      · obtain ⟨k, rfl⟩ : ∃ k, u = n + (k + 1) := ⟨u - n - 1, by omega⟩
        have hk1 : k + 1 < C.gates.length := by omega
        have hkr : ¬ k < r := by omega
        have e : n + (k + 1) - 1 = n + k := by omega
        rw [e, val_gate hx hk1, val_gate hx (by rw [bypass_length]; omega),
          gateAt_bypass (by omega), if_neg hkr]
        simp only [aliasGate, List.map_map]
        refine hmono _ (hAO _ hk1) _ _ _ ?_
        intro i' hi'
        simp only [Function.comp_apply]
        by_cases h1 : i' = n + r
        · subst h1
          rw [aliasWire_self, if_pos (by omega)]
          have hgi : (if i < n + k then val (bypass n C r i) x i else false) = val C x i := by
            rcases hi with hi | hi
            · rw [if_pos (by omega), bypass_val_lt hx hr i hi]
            · rw [if_neg (by omega), val_ge hx hi]
          rw [hgi]
          exact hR ⟨k + 1, by omega, hk1, hi'⟩
        · by_cases h2 : i' < n + r
          · rw [aliasWire_lt_self h2, if_pos (by omega), if_pos (by omega),
              bypass_val_lt hx hr i' h2]
            exact hrefl _
          · by_cases h3 : i' < n + (k + 1)
            · have key := ih i' h3 h1
              rw [aliasWire_gt_self (by omega)] at key
              rw [aliasWire_gt_self (by omega), if_pos h3, if_pos (by omega)]
              exact key
            · rw [aliasWire_gt_self (by omega), if_neg h3, if_neg (by omega)]
              exact hrefl _

lemma bypass_eval_rel {R : Bool → Bool → Prop} (hrefl : ∀ b, R b b) (hmono : OpMono R)
    {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n)
    (hAO : ∀ k < C.gates.length,
      (gateAt C k).op = GateOp.and ∨ (gateAt C k).op = GateOp.or)
    {r i : ℕ} (hr : r < C.gates.length) (hi : i < n + r ∨ n + C.gates.length ≤ i)
    (hR : R (val C x (n + r)) (val C x i)) :
    R (C.eval x) ((bypass n C r i).eval x) := by
  rw [eval_eq_val, eval_eq_val, bypass_output]
  by_cases h : C.output = n + r
  · have hgi : val (bypass n C r i) x i = val C x i := by
      rcases hi with hi | hi
      · exact bypass_val_lt hx hr i hi
      · rw [val_ge hx hi, val_ge hx (by rw [bypass_length]; omega)]
    rw [h, aliasWire_self, hgi]; exact hR
  · exact bypass_rel hrefl hmono hx hAO hr hi (fun _ => hR) _ h

lemma bypass_eval_eq {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n)
    (hAO : ∀ k < C.gates.length,
      (gateAt C k).op = GateOp.and ∨ (gateAt C k).op = GateOp.or)
    {r i : ℕ} (hr : r < C.gates.length) (hi : i < n + r ∨ n + C.gates.length ≤ i)
    (hR : val C x (n + r) = val C x i) :
    (bypass n C r i).eval x = C.eval x :=
  (bypass_eval_rel (R := Eq) (fun _ => rfl) opMono_eq hx hAO hr hi hR).symm

lemma bypass_eval_unread {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n)
    (hAO : ∀ k < C.gates.length,
      (gateAt C k).op = GateOp.and ∨ (gateAt C k).op = GateOp.or)
    {r i : ℕ} (hr : r < C.gates.length) (hi : i < n + r ∨ n + C.gates.length ≤ i)
    (hout : C.output ≠ n + r)
    (hno : ∀ k, r < k → k < C.gates.length → n + r ∉ (gateAt C k).inputs) :
    (bypass n C r i).eval x = C.eval x := by
  rw [eval_eq_val, eval_eq_val, bypass_output]
  exact (bypass_rel (R := Eq) (fun _ => rfl) opMono_eq hx hAO hr hi
    (fun ⟨k, hrk, hk, hm⟩ => absurd hm (hno k hrk hk)) _ hout).symm

lemma bypass_AO {n : ℕ} {C : Circuit} {r i : ℕ} (hr : r < C.gates.length)
    (hAO : ∀ k < C.gates.length,
      (gateAt C k).op = GateOp.and ∨ (gateAt C k).op = GateOp.or) :
    ∀ k < (bypass n C r i).gates.length,
      (gateAt (bypass n C r i) k).op = GateOp.and ∨
        (gateAt (bypass n C r i) k).op = GateOp.or := by
  intro k hk
  rw [bypass_length] at hk
  rw [gateAt_bypass hk]
  split_ifs with h
  · exact hAO k (by omega)
  · exact hAO (k + 1) (by omega)

lemma bypass_mem {n : ℕ} {C : Circuit} {r i : ℕ} :
    ∀ g ∈ (bypass n C r i).gates, ∃ g' ∈ C.gates, g.op = g'.op ∧
      g.inputs.length = g'.inputs.length := by
  intro g hg
  simp only [bypass, List.mem_map, List.mem_range] at hg
  obtain ⟨k, hk, rfl⟩ := hg
  split_ifs with h
  · exact ⟨gateAt C k, gateAt_mem (by omega), rfl, rfl⟩
  · exact ⟨gateAt C (k + 1), gateAt_mem (by omega), rfl, by simp [aliasGate]⟩

lemma aliasWire_lt {w i u m : ℕ} (hi : i < w) (hwm : w ≤ m) (hu : u < m + 1) :
    aliasWire w i u < m := by
  unfold aliasWire; split_ifs <;> omega

lemma bypass_readsBack {n : ℕ} {C : Circuit} {r i : ℕ} (hi : i < n + r)
    (hRB : ∀ k < C.gates.length, ∀ u ∈ (gateAt C k).inputs, u < n + k) :
    ∀ k < (bypass n C r i).gates.length,
      ∀ u ∈ (gateAt (bypass n C r i) k).inputs, u < n + k := by
  intro k hk u hu
  rw [bypass_length] at hk
  rw [gateAt_bypass hk] at hu
  split_ifs at hu with h
  · exact hRB k (by omega) u hu
  · simp only [aliasGate, List.mem_map] at hu
    obtain ⟨u', hu', rfl⟩ := hu
    have := hRB (k + 1) (by omega) u' hu'
    exact aliasWire_lt hi (by omega) (by omega)

lemma two_elems {l : List ℕ} (hl : l.length ≤ 2) {p a : ℕ} (hp : p ∈ l) (ha : a ∈ l)
    (hne : a ≠ p) : ∀ u ∈ l, u = p ∨ u = a := by
  match l, hl with
  | [], _ => simp at hp
  | [u], _ =>
    simp only [List.mem_singleton] at hp ha
    omega
  | [u, v], _ =>
    intro w hw
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp ha hw
    omega
  | _ :: _ :: _ :: _, h => simp at h

lemma hxl {n : ℕ} (x : Fin n → Bool) : (List.ofFn x).length = n := List.length_ofFn

lemma h_and_dead {n : ℕ} {C : Circuit} {k p : ℕ} (hk : k < C.gates.length)
    (hop : (gateAt C k).op = GateOp.and) (hp : p ∈ (gateAt C k).inputs)
    (hdead : ∀ x : Fin n → Bool, ¬ (p < n + k ∧ val C (List.ofFn x) p = true)) :
    ∀ x : Fin n → Bool, val C (List.ofFn x) (n + k) = false := by
  intro x
  by_contra hc
  rw [Bool.not_eq_false] at hc
  exact hdead x ((val_and (hxl x) hk hop).mp hc p hp)

lemma h_or_live {n : ℕ} {C : Circuit} {k p : ℕ} (hk : k < C.gates.length)
    (hop : (gateAt C k).op = GateOp.or) (hp : p ∈ (gateAt C k).inputs)
    (hlive : ∀ x : Fin n → Bool, p < n + k ∧ val C (List.ofFn x) p = true) :
    ∀ x : Fin n → Bool, val C (List.ofFn x) (n + k) = true := by
  intro x
  exact (val_or (hxl x) hk hop).mpr ⟨p, hp, hlive x⟩

lemma h_or_dead {n : ℕ} {C : Circuit} {k p : ℕ} (hk : k < C.gates.length)
    (hlen : (gateAt C k).inputs.length ≤ 2)
    (hop : (gateAt C k).op = GateOp.or) (hp : p ∈ (gateAt C k).inputs)
    (hdead : ∀ x : Fin n → Bool, ¬ (p < n + k ∧ val C (List.ofFn x) p = true)) :
    (∀ x : Fin n → Bool, val C (List.ofFn x) (n + k) = false) ∨
      ∃ b, b < n + k ∧
        ∀ x : Fin n → Bool, val C (List.ofFn x) (n + k) = val C (List.ofFn x) b := by
  by_cases hb : ∃ b ∈ (gateAt C k).inputs, b ≠ p ∧ b < n + k
  · obtain ⟨b, hbm, hbp, hbk⟩ := hb
    right
    refine ⟨b, hbk, fun x => ?_⟩
    have h2 := two_elems hlen hp hbm hbp
    rw [Bool.eq_iff_iff, val_or (hxl x) hk hop]
    constructor
    · rintro ⟨u, hu, hlt, hv⟩
      rcases h2 u hu with h3 | h3
      · rw [h3] at hlt hv
        exact absurd ⟨hlt, hv⟩ (hdead x)
      · rw [h3] at hv
        exact hv
    · intro hv; exact ⟨b, hbm, hbk, hv⟩
  · left
    intro x
    by_contra hc
    rw [Bool.not_eq_false] at hc
    obtain ⟨u, hu, hlt, hv⟩ := (val_or (hxl x) hk hop).mp hc
    by_cases hup : u = p
    · rw [hup] at hlt hv
      exact hdead x ⟨hlt, hv⟩
    · exact hb ⟨u, hu, hup, hlt⟩

lemma h_and_live {n : ℕ} {C : Circuit} {k p : ℕ} (hk : k < C.gates.length)
    (hlen : (gateAt C k).inputs.length ≤ 2)
    (hop : (gateAt C k).op = GateOp.and) (hp : p ∈ (gateAt C k).inputs)
    (hlive : ∀ x : Fin n → Bool, p < n + k ∧ val C (List.ofFn x) p = true) :
    (∀ x : Fin n → Bool, val C (List.ofFn x) (n + k) = true) ∨
    (∀ x : Fin n → Bool, val C (List.ofFn x) (n + k) = false) ∨
      ∃ b, b < n + k ∧
        ∀ x : Fin n → Bool, val C (List.ofFn x) (n + k) = val C (List.ofFn x) b := by
  by_cases hb : ∃ b ∈ (gateAt C k).inputs, b ≠ p
  · obtain ⟨b, hbm, hbp⟩ := hb
    have h2 := two_elems hlen hp hbm hbp
    right
    by_cases hbk : b < n + k
    · right
      refine ⟨b, hbk, fun x => ?_⟩
      rw [Bool.eq_iff_iff, val_and (hxl x) hk hop]
      constructor
      · intro h; exact (h b hbm).2
      · intro hv u hu
        rcases h2 u hu with h3 | h3
        · rw [h3]; exact hlive x
        · rw [h3]; exact ⟨hbk, hv⟩
    · left
      intro x
      by_contra hc
      rw [Bool.not_eq_false] at hc
      exact hbk ((val_and (hxl x) hk hop).mp hc b hbm).1
  · left
    intro x
    rw [val_and (hxl x) hk hop]
    intro u hu
    by_cases hup : u = p
    · rw [hup]; exact hlive x
    · exact absurd ⟨u, hu, hup⟩ hb

lemma normal (n : ℕ) (C : Circuit) (hn : 0 < n) (F : (Fin n → Bool) → Bool)
    (Good : Circuit → Prop)
    (hAO : ∀ k < C.gates.length, (gateAt C k).op = GateOp.and ∨ (gateAt C k).op = GateOp.or)
    (hlen2 : ∀ k < C.gates.length, (gateAt C k).inputs.length ≤ 2)
    (hbyp : ∀ r i, r < C.gates.length → i < n + r → Good (bypass n C r i))
    (hF : ∀ x : Fin n → Bool, C.eval (List.ofFn x) = F x)
    (hF0 : ∃ x, F x = false) (hF1 : ∃ x, F x = true)
    (hmin : ∀ D, Good D →
      (∀ x : Fin n → Bool, D.eval (List.ofFn x) = C.eval (List.ofFn x)) →
      C.gates.length ≤ D.gates.length) :
    ∀ k < C.gates.length, (∃ a b, (gateAt C k).inputs = [a, b]) ∧
      ∀ u ∈ (gateAt C k).inputs, u < n + k := by
  have nodup : ∀ r i, r < C.gates.length → i < n + r →
      ¬ ∀ x : Fin n → Bool, val C (List.ofFn x) (n + r) = val C (List.ofFn x) i := by
    intro r i hr hi h
    have := hmin _ (hbyp r i hr hi)
      (fun x => bypass_eval_eq (hxl x) hAO hr (Or.inl hi) (h x))
    rw [bypass_length] at this; omega
  have unread : ∀ r, r < C.gates.length → C.output ≠ n + r →
      ¬ ∀ k, r < k → k < C.gates.length → n + r ∉ (gateAt C k).inputs := by
    intro r hr hout hno
    have := hmin _ (hbyp r 0 hr (by omega))
      (fun x => bypass_eval_unread (hxl x) hAO hr (Or.inl (by omega)) hout hno)
    rw [bypass_length] at this; omega
  have nofalse : ∀ m r, C.gates.length - r = m → r < C.gates.length →
      ¬ ∀ x : Fin n → Bool, val C (List.ofFn x) (n + r) = false := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
      intro r hm hr hP
      obtain ⟨x1, hx1⟩ := hF1
      have hout : C.output ≠ n + r := by
        intro h
        have h1 := hF x1
        rw [eval_eq_val, h, hP x1, hx1] at h1
        exact absurd h1 (by simp)
      apply unread r hr hout
      intro k hrk hk hmem
      have hdead : ∀ x : Fin n → Bool,
          ¬ (n + r < n + k ∧ val C (List.ofFn x) (n + r) = true) := by
        intro x h; rw [hP x] at h; exact absurd h.2 (by simp)
      rcases hAO k hk with hop | hop
      · exact ih (C.gates.length - k) (by omega) k rfl hk (h_and_dead hk hop hmem hdead)
      · rcases h_or_dead hk (hlen2 k hk) hop hmem hdead with h | ⟨b, hb, h⟩
        · exact ih (C.gates.length - k) (by omega) k rfl hk h
        · exact nodup k b hk hb h
  have nofalse' : ∀ r, r < C.gates.length →
      ¬ ∀ x : Fin n → Bool, val C (List.ofFn x) (n + r) = false :=
    fun r hr => nofalse _ r rfl hr
  have notrue : ∀ m r, C.gates.length - r = m → r < C.gates.length →
      ¬ ∀ x : Fin n → Bool, val C (List.ofFn x) (n + r) = true := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
      intro r hm hr hP
      obtain ⟨x0, hx0⟩ := hF0
      have hout : C.output ≠ n + r := by
        intro h
        have h1 := hF x0
        rw [eval_eq_val, h, hP x0, hx0] at h1
        exact absurd h1 (by simp)
      apply unread r hr hout
      intro k hrk hk hmem
      have hlive : ∀ x : Fin n → Bool,
          n + r < n + k ∧ val C (List.ofFn x) (n + r) = true :=
        fun x => ⟨by omega, hP x⟩
      rcases hAO k hk with hop | hop
      · rcases h_and_live hk (hlen2 k hk) hop hmem hlive with h | h | ⟨b, hb, h⟩
        · exact ih (C.gates.length - k) (by omega) k rfl hk h
        · exact nofalse' k hk h
        · exact nodup k b hk hb h
      · exact ih (C.gates.length - k) (by omega) k rfl hk (h_or_live hk hop hmem hlive)
  have notrue' : ∀ r, r < C.gates.length →
      ¬ ∀ x : Fin n → Bool, val C (List.ofFn x) (n + r) = true :=
    fun r hr => notrue _ r rfl hr
  intro k hk
  have hback : ∀ u ∈ (gateAt C k).inputs, u < n + k := by
    intro u hu
    by_contra hlt
    have hdead : ∀ x : Fin n → Bool, ¬ (u < n + k ∧ val C (List.ofFn x) u = true) :=
      fun x h => hlt h.1
    rcases hAO k hk with hop | hop
    · exact nofalse' k hk (h_and_dead hk hop hu hdead)
    · rcases h_or_dead hk (hlen2 k hk) hop hu hdead with h | ⟨b, hb, h⟩
      · exact nofalse' k hk h
      · exact nodup k b hk hb h
  refine ⟨?_, hback⟩
  have h2 := hlen2 k hk
  rcases hl : (gateAt C k).inputs with _ | ⟨a, _ | ⟨b, _ | ⟨c, t⟩⟩⟩
  · exfalso
    rcases hAO k hk with hop | hop
    · apply notrue' k hk
      intro x
      rw [val_and (hxl x) hk hop, hl]
      intro u hu
      simp at hu
    · apply nofalse' k hk
      intro x
      by_contra hc
      rw [Bool.not_eq_false, val_or (hxl x) hk hop, hl] at hc
      obtain ⟨u, hu, _⟩ := hc
      simp at hu
  · exfalso
    have ha : a < n + k := hback a (by rw [hl]; simp)
    apply nodup k a hk ha
    intro x
    rw [Bool.eq_iff_iff]
    rcases hAO k hk with hop | hop
    · rw [val_and (hxl x) hk hop, hl]
      simp [ha]
    · rw [val_or (hxl x) hk hop, hl]
      simp [ha]
  · exact ⟨a, b, rfl⟩
  · rw [hl] at h2
    exact absurd h2 (by simp only [List.length_cons]; omega)

lemma wv_val (n : ℕ) (C : Circuit) (x : Fin n → Bool) (w : ℕ) :
    wv n C x w = val C (List.ofFn x) w := rfl

lemma eval_wv (n : ℕ) (C : Circuit) (x : Fin n → Bool) :
    C.eval (List.ofFn x) = wv n C x C.output := rfl

lemma gateVal_wv (n : ℕ) (C : Circuit) (j : ℕ) (x : Fin n → Bool) :
    gateVal n C j x = wv n C x (n + j) := rfl

lemma mem_gates_iff (C : Circuit) (g : Gate) :
    g ∈ C.gates ↔ ∃ j, j < C.gates.length ∧ gateAt C j = g := by
  constructor
  · intro h
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem h
    exact ⟨j, hj, gateAt_eq hj⟩
  · rintro ⟨j, hj, rfl⟩
    exact gateAt_mem hj

lemma AO2_mem {n : ℕ} {C : Circuit} (h : AO2 n C) :
    ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2 := by
  intro g hg
  obtain ⟨j, hj, rfl⟩ := (mem_gates_iff C g).mp hg
  obtain ⟨h1, ⟨a, b, h2⟩, _⟩ := h j hj
  exact ⟨h1, by rw [h2]; rfl⟩

lemma AO2_readsBack {n : ℕ} {C : Circuit} (h : AO2 n C) : ReadsBack n C :=
  fun j hj => (h j hj).2.2

lemma to_AO2 (n : ℕ) (C : Circuit) (hn : 0 < n) (F : (Fin n → Bool) → Bool)
    (Good : Circuit → Prop)
    (hAO : ∀ k < C.gates.length, (gateAt C k).op = GateOp.and ∨ (gateAt C k).op = GateOp.or)
    (hlen2 : ∀ k < C.gates.length, (gateAt C k).inputs.length ≤ 2)
    (hbyp : ∀ r i, r < C.gates.length → i < n + r → Good (bypass n C r i))
    (hF : ∀ x : Fin n → Bool, C.eval (List.ofFn x) = F x)
    (hF0 : ∃ x, F x = false) (hF1 : ∃ x, F x = true)
    (hmin : ∀ D, Good D →
      (∀ x : Fin n → Bool, D.eval (List.ofFn x) = C.eval (List.ofFn x)) →
      C.gates.length ≤ D.gates.length) : AO2 n C :=
  fun k hk => ⟨hAO k hk, normal n C hn F Good hAO hlen2 hbyp hF hF0 hF1 hmin k hk⟩

lemma graphFun_false {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    graphFun G ∅ (fun _ => false) = false := by
  simp [graphFun]

lemma graphFun_iff {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (x : Fin n → Bool) :
    graphFun G ∅ x = true ↔ ∃ u v, G.Adj u v ∧ x u = true ∧ x v = true := by
  simp [graphFun]

lemma graphFun_true {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (h : G.edgeFinset.Nonempty) : graphFun G ∅ (fun _ => true) = true := by
  obtain ⟨e, he⟩ := h
  rw [SimpleGraph.mem_edgeFinset] at he
  induction e using Sym2.ind with
  | _ u v =>
    rw [SimpleGraph.mem_edgeSet] at he
    rw [graphFun_iff]
    exact ⟨u, v, he, rfl, rfl⟩

lemma pos_of_edge {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (h : G.edgeFinset.Nonempty) : 0 < n := by
  obtain ⟨e, _⟩ := h
  induction e using Sym2.ind with
  | _ u v => exact Nat.lt_of_le_of_lt (Nat.zero_le _) u.isLt

lemma main_abs (n : ℕ) (C : Circuit) (F : (Fin n → Bool) → Bool) (hC : AO2 n C)
    (hF : ∀ x, wv n C x C.output = F x) (hF1 : ∃ x, F x = true)
    (hmin : ∀ D : Circuit, AO2 n D → (∀ x, wv n D x D.output = F x) →
      C.gates.length ≤ D.gates.length)
    (i j : ℕ) (hbel : ∀ x, wv n C x (n + i) = true → F x = true)
    (hcone : InCone n C i j) :
    ∃ (C' : Circuit) (r : ℕ), r < C.gates.length ∧ i < r ∧ Least n C' ∧
      (∀ x, wv n C' x C'.output = F x) ∧ C'.gates.length = C.gates.length ∧
      (∀ k', k' < C.gates.length - 1 → (gateAt C' k').op = (gateAt C (rho r k')).op) ∧
      (gateAt C' (C.gates.length - 1)).op = GateOp.or ∧ (gateAt C r).op = GateOp.or ∧
      (∀ k', k' < C.gates.length - 1 →
        ((∀ x, wv n C' x (n + k') = true → F x = true) ↔
          (∀ x, wv n C x (n + rho r k') = true → F x = true))) ∧
      (∀ a' b', b' < C.gates.length - 1 → InCone n C' a' b' →
        InCone n C (rho r a') (rho r b')) ∧
      (∀ j', j' < C.gates.length - 1 → ¬ InCone n C' i j') := by
  have hL : Least n C := ⟨hC, fun D hD hfun => hmin D hD (fun x => (hfun x).trans (hF x))⟩
  obtain ⟨x1, hx1⟩ := hF1
  have hout : C.output < n + C.gates.length := out_lt n C x1 (by rw [hF, hx1])
  exact step3_struct n C F hL hF hout i j hbel hcone

lemma junk_eq2 (n : ℕ) (C C' : Circuit) (F : (Fin n → Bool) → Bool) (r : ℕ)
    (hr : r < C.gates.length)
    (hlen : C'.gates.length = C.gates.length)
    (hops : ∀ k', k' < C.gates.length - 1 → (gateAt C' k').op = (gateAt C (rho r k')).op)
    (htop : (gateAt C' (C.gates.length - 1)).op = GateOp.or)
    (hopr : (gateAt C r).op = GateOp.or)
    (hbelow : ∀ k', k' < C.gates.length - 1 →
        ((∀ x, wv n C' x (n + k') = true → F x = true) ↔
          (∀ x, wv n C x (n + rho r k') = true → F x = true)))
    (S S' : Finset ℕ)
    (hS : ∀ k, k ∈ S ↔ k < C.gates.length ∧ (gateAt C k).op = GateOp.and ∧
      ¬ ∀ x, wv n C x (n + k) = true → F x = true)
    (hS' : ∀ k, k ∈ S' ↔ k < C'.gates.length ∧ (gateAt C' k).op = GateOp.and ∧
      ¬ ∀ x, wv n C' x (n + k) = true → F x = true) :
    S'.card = S.card := by
  classical
  have e : S = (Finset.range C.gates.length).filter (fun k : ℕ =>
      (gateAt C k).op = GateOp.and ∧ ¬ ∀ x, wv n C x (n + k) = true → F x = true) := by
    ext k; rw [hS, Finset.mem_filter, Finset.mem_range]
  have e' : S' = (Finset.range C'.gates.length).filter (fun k : ℕ =>
      (gateAt C' k).op = GateOp.and ∧ ¬ ∀ x, wv n C' x (n + k) = true → F x = true) := by
    ext k; rw [hS', Finset.mem_filter, Finset.mem_range]
  rw [e, e']
  exact junk_eq n C C' F r hr hlen hops htop hopr hbelow

lemma pairs_lt2 (n : ℕ) (C C' : Circuit) (r i j : ℕ) (hr : r < C.gates.length) (hir : i < r)
    (hlen : C'.gates.length = C.gates.length)
    (hops : ∀ k', k' < C.gates.length - 1 → (gateAt C' k').op = (gateAt C (rho r k')).op)
    (htop : (gateAt C' (C.gates.length - 1)).op = GateOp.or)
    (hcone : ∀ a' b', b' < C.gates.length - 1 → InCone n C' a' b' →
        InCone n C (rho r a') (rho r b'))
    (hno : ∀ j', j' < C.gates.length - 1 → ¬ InCone n C' i j')
    (hi : (gateAt C i).op = GateOp.and) (hj : (gateAt C j).op = GateOp.and)
    (hij : InCone n C i j)
    (T T' : Finset (ℕ × ℕ))
    (hT : ∀ p : ℕ × ℕ, p ∈ T ↔ (p.1 < C.gates.length ∧ p.2 < C.gates.length) ∧
      (gateAt C p.1).op = GateOp.and ∧ (gateAt C p.2).op = GateOp.and ∧ InCone n C p.1 p.2)
    (hT' : ∀ p : ℕ × ℕ, p ∈ T' ↔ (p.1 < C'.gates.length ∧ p.2 < C'.gates.length) ∧
      (gateAt C' p.1).op = GateOp.and ∧ (gateAt C' p.2).op = GateOp.and ∧
        InCone n C' p.1 p.2) :
    T'.card < T.card := by
  classical
  have e : T = (Finset.range C.gates.length ×ˢ Finset.range C.gates.length).filter
      (fun p : ℕ × ℕ => (gateAt C p.1).op = GateOp.and ∧
        (gateAt C p.2).op = GateOp.and ∧ InCone n C p.1 p.2) := by
    ext p
    rw [hT, Finset.mem_filter, Finset.mem_product, Finset.mem_range, Finset.mem_range]
  have e' : T' = (Finset.range C'.gates.length ×ˢ Finset.range C'.gates.length).filter
      (fun p : ℕ × ℕ => (gateAt C' p.1).op = GateOp.and ∧
        (gateAt C' p.2).op = GateOp.and ∧ InCone n C' p.1 p.2) := by
    ext p
    rw [hT', Finset.mem_filter, Finset.mem_product, Finset.mem_range, Finset.mem_range]
  rw [e, e']
  exact pairs_lt n C C' r i j hr hir hlen hops htop hcone hno hi hj hij

lemma junk_mem {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) (k : ℕ) :
    k ∈ PEqualNP.TopForm.junk G C ↔ k < C.gates.length ∧ (gateAt C k).op = GateOp.and ∧
      ¬ ∀ x, wv n C x (n + k) = true → graphFun G ∅ x = true := by
  unfold PEqualNP.TopForm.junk PEqualNP.TopForm.gatesWhere
  simp only [Finset.mem_filter, Finset.mem_range]
  unfold PEqualNP.CleanedNonEdge.IsDirtyAnd PEqualNP.CleanedNonEdge.IsDirty
  constructor
  · rintro ⟨h1, h2, _, x, hx1, hx2⟩
    refine ⟨h1, h2, fun h => ?_⟩
    have h3 := h x hx1
    rw [hx2] at h3
    exact absurd h3 (by simp)
  · rintro ⟨h1, h2, h3⟩
    refine ⟨h1, h2, h1, ?_⟩
    by_contra hc
    apply h3
    intro x hx
    by_contra hf
    exact hc ⟨x, hx, by simpa using hf⟩

lemma to_real {n : ℕ} {D : Circuit} (hD : AO2 n D) : PEqualNP.TopForm.IsAO2 n D :=
  ⟨fun g hg => (AO2_mem hD g hg).1, AO2_readsBack hD, fun g hg => (AO2_mem hD g hg).2⟩

lemma of_real {n : ℕ} {C : Circuit} (h : PEqualNP.TopForm.IsAO2 n C) : AO2 n C := by
  obtain ⟨h1, h2, h3⟩ := h
  intro k hk
  exact ⟨h1 _ (gateAt_mem hk), List.length_eq_two.mp (h3 _ (gateAt_mem hk)), h2 k hk⟩


open PEqualNP.MetaComplexity
lemma safe_and_below_and_rewrite : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : PEqualNP.CircuitLowerBounds.Circuit),
  G.edgeFinset.Nonempty → PEqualNP.TopForm.IsLeastAO G C →
  ∀ (i j : ℕ), i < C.gates.length → j < C.gates.length →
    (PEqualNP.MetaComplexity.NestedCover.gateAt C i).op = PEqualNP.CircuitLowerBounds.GateOp.and →
    PEqualNP.TopForm.BelowF G C i →
    (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.and →
    PEqualNP.EdgeOwnership.InCone n C i j →
    ∃ C' : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.TopForm.IsLeastAO G C' ∧ C'.size = C.size ∧
      PEqualNP.TopForm.andPairs n C' < PEqualNP.TopForm.andPairs n C ∧
      (PEqualNP.TopForm.junk G C').card = (PEqualNP.TopForm.junk G C).card := by
  intro n G _ C hne hL i j hi hj hiand hbel hjand hcone
  obtain ⟨hAO, hfun, hmin⟩ := hL
  have hF : ∀ x : Fin n → Bool, wv n C x C.output = graphFun G ∅ x :=
    fun x => congrFun hfun x
  have hC : AO2 n C := of_real hAO
  obtain ⟨C', r, hr, hir, hL', hF', hlen, hops, htop, hopr, hbelow, hcone', hno⟩ :=
    main_abs n C (graphFun G ∅) hC hF ⟨_, graphFun_true G hne⟩
      (fun D hD hDf => hmin D (to_real hD) (funext hDf)) i j hbel hcone
  refine ⟨C', ⟨to_real hL'.1, funext hF', fun D hD hDf => ?_⟩, hlen, ?_, ?_⟩
  · show C'.gates.length ≤ D.gates.length
    rw [hlen]; exact hmin D hD hDf
  · unfold PEqualNP.TopForm.andPairs
    apply pairs_lt2 n C C' r i j hr hir hlen hops htop hcone' hno hiand hjand hcone
    · intro p
      simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range]
    · intro p
      simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range]
  · exact junk_eq2 n C C' (graphFun G ∅) r hr hlen hops htop hopr hbelow _ _
      (junk_mem G C) (junk_mem G C')

end SafeLift

lemma exists_top_form_extremal (n : ℕ) (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (hG : G.edgeFinset.Nonempty) (activity : Circuit → ℕ)
    (C₀ : Circuit) (hm₀ : IsMinimalMonoCircuit n C₀)
    (hc₀ : circuitFun n C₀ = PEqualNP.MetaComplexity.NestedCover.graphFun G ∅) :
    ∃ C : Circuit, GraphExtremal n G activity C := by
  exact exists_top_form_extremal_of_rewrite n G activity C₀ hm₀ hc₀
    (fun C hC => SafeLift.safe_and_below_and_rewrite n G C hG hC)

lemma exists_top_form_extremal_from_circuit (n : ℕ) (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (hG : G.edgeFinset.Nonempty) (activity : Circuit → ℕ)
    (C₀ : Circuit) (hm₀ : Monotone2 C₀)
    (hc₀ : circuitFun n C₀ = PEqualNP.MetaComplexity.NestedCover.graphFun G ∅) :
    ∃ C : Circuit, GraphExtremal n G activity C := by
  obtain ⟨D, ⟨hmD, hcD⟩, hsize⟩ := exists_measure_min
    (fun D => Monotone2 D ∧ circuitFun n D = PEqualNP.MetaComplexity.NestedCover.graphFun G ∅)
    Circuit.size ⟨C₀, hm₀, hc₀⟩
  have hminimal : IsMinimalMonoCircuit n D :=
    ⟨hmD, fun E hmE he => hsize E ⟨hmE, he.trans hcD⟩⟩
  exact exists_top_form_extremal n G hG activity D hminimal hcD

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership
  PEqualNP.CleanedNonEdge

lemma first_dirty_no_and_ancestor {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (j : ℕ) (htop : PEqualNP.TopForm.TopForm G C)
    (hdirty : IsDirtyAnd n G C j)
    (hfirst : ∀ i < j, ¬ IsDirtyAnd n G C i) :
    ∀ i, InCone n C i j → (gateAt C i).op ≠ GateOp.and := by
  intro i hcone hiand
  have hij := SafeLift.inCone_lt n C i j hcone
  have hil : i < C.gates.length := hij.1.trans hij.2
  have hbelow : PEqualNP.TopForm.BelowF G C i := by
    intro x hx
    cases hf : graphFun G ∅ x with
    | false => exact False.elim (hfirst i hij.1 ⟨hiand, hil, x, hx, hf⟩)
    | true => rfl
  exact htop i hil j hij.2 hiand hbelow hdirty.1 hcone

lemma first_dirty_ancestors_or {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (j : ℕ) (hAO : PEqualNP.TopForm.IsAO2 n C)
    (htop : PEqualNP.TopForm.TopForm G C) (hdirty : IsDirtyAnd n G C j)
    (hfirst : ∀ i < j, ¬ IsDirtyAnd n G C i) :
    ∀ i, InCone n C i j → (gateAt C i).op = GateOp.or := by
  intro i hcone
  have hij := SafeLift.inCone_lt n C i j hcone
  have hop := (SafeLift.aob (SafeLift.of_real hAO) i (hij.1.trans hij.2)).1
  rcases hop with hop | hop
  · exact False.elim (first_dirty_no_and_ancestor G C j htop hdirty hfirst i hcone hop)
  · exact hop

lemma pure_or_operand_support (n : ℕ) (C : Circuit) (j : ℕ)
    (hC : SafeLift.AOB n C) (hj : j < C.gates.length)
    (hanc : ∀ i, InCone n C i j → (gateAt C i).op = GateOp.or)
    (w : ℕ) (hw : w ∈ (gateAt C j).inputs) :
    ∃ S : Finset (Fin n), ∀ x : Fin n → Bool,
      SafeLift.wv n C x w = decide (∃ u ∈ S, x u = true) := by
  classical
  have build : ∀ v : ℕ, (v < n ∨ ∃ k, v = n+k ∧ InCone n C k j) →
      ∃ S : Finset (Fin n), ∀ x : Fin n → Bool,
        SafeLift.wv n C x v = decide (∃ u ∈ S, x u = true) := by
    intro v
    induction v using Nat.strong_induction_on with
    | _ v ih =>
      intro hv
      by_cases hin : v < n
      · refine ⟨{⟨v, hin⟩}, fun x => ?_⟩
        rw [SafeLift.wv_input n C x v hin]
        simp
      · obtain ⟨k, rfl, hcone⟩ := hv.resolve_left hin
        have hkl := (SafeLift.inCone_lt n C k j hcone).1.trans hj
        have hop := hanc k hcone
        have each (r : {r // r ∈ (gateAt C k).inputs}) :
            ∃ S : Finset (Fin n), ∀ x : Fin n → Bool,
              SafeLift.wv n C x r.val = decide (∃ u ∈ S, x u = true) := by
          apply ih r.val ((hC k hkl).2 r.val r.property)
          by_cases hr : r.val < n
          · exact Or.inl hr
          · have hrl : r.val-n < k := by have ht := (hC k hkl).2 r.val r.property; omega
            have hre : n + (r.val-n) = r.val := by omega
            have hrcone : InCone n C (r.val-n) k := by
              rw [SafeLift.inCone_iff]
              exact ⟨hkl, r.val-n, hrl, by simpa only [hre] using r.property, Or.inl rfl⟩
            exact Or.inr ⟨r.val-n, hre.symm, SafeLift.inCone_trans n C (r.val-n) k hrcone j hcone⟩
        choose sets hsets using each
        let S : Finset (Fin n) := ((gateAt C k).inputs.attach.toFinset).biUnion sets
        refine ⟨S, fun x => ?_⟩
        rw [SafeLift.wv_rec n C x hC k hkl, hop]
        apply Bool.eq_iff_iff.mpr
        simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply,
          id_eq, decide_eq_true_eq]
        constructor
        · rintro ⟨r, hr, hv⟩
          let q : {r // r ∈ (gateAt C k).inputs} := ⟨r, hr⟩
          have hs : ∃ u ∈ sets q, x u = true := by
            apply of_decide_eq_true
            exact (hsets q x).symm.trans hv
          obtain ⟨u, hu, hxu⟩ := hs
          refine ⟨u, ?_, hxu⟩
          exact Finset.mem_biUnion.mpr ⟨q, by simp, hu⟩
        · rintro ⟨u, hu, hxu⟩
          obtain ⟨q, _, hqu⟩ := Finset.mem_biUnion.mp hu
          refine ⟨q.val, q.property, ?_⟩
          exact (hsets q x).trans (decide_eq_true ⟨u, hqu, hxu⟩)
  apply build w
  by_cases hwi : w < n
  · exact Or.inl hwi
  · have hwlt := (hC j hj).2 w hw
    have hwe : n + (w-n) = w := by omega
    refine Or.inr ⟨w-n, hwe.symm, ?_⟩
    rw [SafeLift.inCone_iff]
    exact ⟨hj, w-n, by omega, by simpa only [hwe] using hw, Or.inl rfl⟩

lemma first_dirty_operand_support {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (j : ℕ) (hAO : PEqualNP.TopForm.IsAO2 n C)
    (htop : PEqualNP.TopForm.TopForm G C) (hdirty : IsDirtyAnd n G C j)
    (hfirst : ∀ i < j, ¬ IsDirtyAnd n G C i)
    (w : ℕ) (hw : w ∈ (gateAt C j).inputs) :
    ∃ S : Finset (Fin n), ∀ x : Fin n → Bool,
      SafeLift.wv n C x w = decide (∃ u ∈ S, x u = true) :=
  pure_or_operand_support n C j (SafeLift.aob (SafeLift.of_real hAO)) hdirty.2.1
    (first_dirty_ancestors_or G C j hAO htop hdirty hfirst) w hw

lemma first_dirty_product_support {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (j : ℕ) (hAO : PEqualNP.TopForm.IsAO2 n C)
    (htop : PEqualNP.TopForm.TopForm G C) (hdirty : IsDirtyAnd n G C j)
    (hfirst : ∀ i < j, ¬ IsDirtyAnd n G C i) :
    ∃ (a b : ℕ) (A B : Finset (Fin n)), (gateAt C j).inputs = [a,b] ∧
      (∀ x : Fin n → Bool, SafeLift.wv n C x a = decide (∃ u ∈ A, x u = true)) ∧
      (∀ x : Fin n → Bool, SafeLift.wv n C x b = decide (∃ u ∈ B, x u = true)) ∧
      ∀ x : Fin n → Bool, gateVal n C j x =
        (decide (∃ u ∈ A, x u = true) && decide (∃ u ∈ B, x u = true)) := by
  obtain ⟨a, b, hab⟩ := (SafeLift.of_real hAO j hdirty.2.1).2.1
  obtain ⟨A, hA⟩ := first_dirty_operand_support G C j hAO htop hdirty hfirst a (by simp [hab])
  obtain ⟨B, hB⟩ := first_dirty_operand_support G C j hAO htop hdirty hfirst b (by simp [hab])
  refine ⟨a, b, A, B, hab, hA, hB, fun x => ?_⟩
  change SafeLift.wv n C x (n+j) = _
  rw [SafeLift.wv_rec n C x (SafeLift.aob (SafeLift.of_real hAO)) j hdirty.2.1,
    hdirty.1, hab]
  simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil,
    id_eq, Bool.and_true, hA x, hB x]

lemma and_ancestors_or_of_prior_below {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (j : ℕ) (hAO : PEqualNP.TopForm.IsAO2 n C)
    (htop : PEqualNP.TopForm.TopForm G C) (hj : j < C.gates.length)
    (hjand : (gateAt C j).op = GateOp.and)
    (hprior : ∀ i < j, (gateAt C i).op = GateOp.and → PEqualNP.TopForm.BelowF G C i) :
    ∀ i, InCone n C i j → (gateAt C i).op = GateOp.or := by
  intro i hcone
  have hij := SafeLift.inCone_lt n C i j hcone
  have hil := hij.1.trans hj
  rcases (SafeLift.aob (SafeLift.of_real hAO) i hil).1 with hiand | hior
  · exact False.elim (htop i hil j hj hiand (hprior i hij.1 hiand) hjand hcone)
  · exact hior

lemma and_product_support_of_prior_below {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (j : ℕ) (hAO : PEqualNP.TopForm.IsAO2 n C)
    (htop : PEqualNP.TopForm.TopForm G C) (hj : j < C.gates.length)
    (hjand : (gateAt C j).op = GateOp.and)
    (hprior : ∀ i < j, (gateAt C i).op = GateOp.and → PEqualNP.TopForm.BelowF G C i) :
    ∃ (a b : ℕ) (A B : Finset (Fin n)), (gateAt C j).inputs = [a,b] ∧
      (∀ x : Fin n → Bool, SafeLift.wv n C x a = decide (∃ u ∈ A, x u = true)) ∧
      (∀ x : Fin n → Bool, SafeLift.wv n C x b = decide (∃ u ∈ B, x u = true)) ∧
      ∀ x : Fin n → Bool, gateVal n C j x =
        (decide (∃ u ∈ A, x u = true) && decide (∃ u ∈ B, x u = true)) := by
  have hanc := and_ancestors_or_of_prior_below G C j hAO htop hj hjand hprior
  have hC := SafeLift.aob (SafeLift.of_real hAO)
  obtain ⟨a, b, hab⟩ := (SafeLift.of_real hAO j hj).2.1
  obtain ⟨A, hA⟩ := pure_or_operand_support n C j hC hj hanc a (by simp [hab])
  obtain ⟨B, hB⟩ := pure_or_operand_support n C j hC hj hanc b (by simp [hab])
  refine ⟨a, b, A, B, hab, hA, hB, fun x => ?_⟩
  change SafeLift.wv n C x (n+j) = _
  rw [SafeLift.wv_rec n C x hC j hj, hjand, hab]
  simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil,
    id_eq, Bool.and_true, hA x, hB x]

lemma critical_boundary_gate_correct (n : ℕ) (pre post : List Gate) (g h : Gate) (out : ℕ)
    (F : (Fin n → Bool) → Bool) (P N : (Fin n → Bool) → Prop)
    (hm : Monotone2 ⟨pre ++ g :: post, out⟩)
    (hh : h.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ h.inputs.length ≤ 2)
    (hcorrect : ∀ x : Fin n → Bool,
      Circuit.eval ⟨pre ++ g :: post, out⟩ (List.ofFn x) = F x)
    (hpos_cover : ∀ x : Fin n → Bool, F x = true →
      ∃ y : Fin n → Bool, F y = true ∧ P y ∧ ∀ i, y i = true → x i = true)
    (hneg_cover : ∀ x : Fin n → Bool, F x = false →
      ∃ y : Fin n → Bool, F y = false ∧ N y ∧ ∀ i, x i = true → y i = true)
    (hpos : ∀ x : Fin n → Bool, F x = true → P x →
      Circuit.eval ⟨pre ++ ⟨GateOp.or, []⟩ :: post, out⟩ (List.ofFn x) = false →
      h.op.eval (h.inputs.map fun i => (run pre (List.ofFn x)).getD i false) = true)
    (hneg : ∀ x : Fin n → Bool, N x →
      h.op.eval (h.inputs.map fun i => (run pre (List.ofFn x)).getD i false) = true →
      g.op.eval (g.inputs.map fun i => (run pre (List.ofFn x)).getD i false) = true) :
    ∀ x : Fin n → Bool,
      Circuit.eval ⟨pre ++ h :: post, out⟩ (List.ofFn x) = F x := by
  let D : Circuit := ⟨pre ++ h :: post, out⟩
  have hD : Monotone2 D := deletion_mono_replace_gate pre post g h out hm hh
  have hpost : ∀ a ∈ post, a.op = .and ∨ a.op = .or := by
    intro a ha
    simpa using (hm a (List.mem_append_right _ (List.mem_cons_of_mem _ ha))).1
  let W := fun x : Fin n → Bool => run pre (List.ofFn x)
  let old := fun x : Fin n → Bool => g.op.eval (g.inputs.map fun i => (W x).getD i false)
  let new := fun x : Fin n → Bool => h.op.eval (h.inputs.map fun i => (W x).getD i false)
  have old_eval (x : Fin n → Bool) :
      (run post (W x ++ [old x])).getD out false = F x := by
    simpa only [Circuit.eval, Circuit.wires, run, List.foldl_append, List.foldl_cons, W, old]
      using hcorrect x
  have new_eval (x : Fin n → Bool) : D.eval (List.ofFn x) =
      (run post (W x ++ [new x])).getD out false := by
    simp only [D, Circuit.eval, Circuit.wires, run, List.foldl_append, List.foldl_cons, W, new]
  have zero_eval (x : Fin n → Bool) :
      Circuit.eval ⟨pre ++ ⟨GateOp.or, []⟩ :: post, out⟩ (List.ofFn x) =
        (run post (W x ++ [false])).getD out false := by
    simp [Circuit.eval, Circuit.wires, run, List.foldl_append, GateOp.eval, W]
  have positive (x : Fin n → Bool) (hf : F x = true) (hp : P x) :
      D.eval (List.ofFn x) = true := by
    rw [new_eval]
    cases hz : Circuit.eval ⟨pre ++ ⟨GateOp.or, []⟩ :: post, out⟩ (List.ofFn x) with
    | false =>
      have hn : new x = true := hpos x hf hp hz
      apply run_mono post (by simp)
        (wireLE_snoc rfl (fun _ h => h) (fun _ => hn)) hpost out
      exact (old_eval x).trans hf
    | true =>
      apply run_mono post (by simp)
        (wireLE_snoc (a := false) (b := new x) rfl (fun _ h => h) (by intro h; cases h)) hpost out
      exact (zero_eval x).symm.trans hz
  have negative (x : Fin n → Bool) (hf : F x = false) (hn : N x) :
      D.eval (List.ofFn x) = false := by
    apply Bool.eq_false_iff.mpr
    intro hx
    rw [new_eval] at hx
    have ht := run_mono post (by simp)
      (wireLE_snoc rfl (fun _ h => h) (hneg x hn)) hpost out hx
    rw [old_eval, hf] at ht
    contradiction
  intro x
  change D.eval (List.ofFn x) = F x
  cases hf : F x with
  | true =>
    obtain ⟨y, hy, hp, hxy⟩ := hpos_cover x hf
    exact signed_eval_mono D hD hxy (positive y hy hp)
  | false =>
    obtain ⟨y, hy, hn, hxy⟩ := hneg_cover x hf
    apply Bool.eq_false_iff.mpr
    intro hx
    have ht := signed_eval_mono D hD hxy hx
    rw [negative y hy hn] at ht
    contradiction

lemma erase_gate_of_critical_boundary (n : ℕ) (pre post : List Gate) (g : Gate) (out r : ℕ)
    (F : (Fin n → Bool) → Bool) (P N : (Fin n → Bool) → Prop)
    (hm : Monotone2 ⟨pre ++ g :: post, out⟩)
    (hcorrect : ∀ x : Fin n → Bool,
      Circuit.eval ⟨pre ++ g :: post, out⟩ (List.ofFn x) = F x)
    (hpos_cover : ∀ x : Fin n → Bool, F x = true →
      ∃ y : Fin n → Bool, F y = true ∧ P y ∧ ∀ i, y i = true → x i = true)
    (hneg_cover : ∀ x : Fin n → Bool, F x = false →
      ∃ y : Fin n → Bool, F y = false ∧ N y ∧ ∀ i, x i = true → y i = true)
    (hpos : ∀ x : Fin n → Bool, F x = true → P x →
      Circuit.eval ⟨pre ++ ⟨GateOp.or, []⟩ :: post, out⟩ (List.ofFn x) = false →
      (run pre (List.ofFn x)).getD r false = true)
    (hneg : ∀ x : Fin n → Bool, N x →
      (run pre (List.ofFn x)).getD r false = true →
      g.op.eval (g.inputs.map fun i => (run pre (List.ofFn x)).getD i false) = true) :
    ∃ D : Circuit, Monotone2 D ∧ D.size + 1 = Circuit.size ⟨pre ++ g :: post, out⟩ ∧
      ∀ x : Fin n → Bool, D.eval (List.ofFn x) = F x := by
  apply erase_gate_of_aliased_correct n pre post g out r F hm
  apply critical_boundary_gate_correct n pre post g ⟨GateOp.or, [r]⟩ out F P N
    hm (by simp) hcorrect hpos_cover hneg_cover
  · intro x hf hp hz
    simpa only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil,
      id_eq, Bool.or_false] using hpos x hf hp hz
  · intro x hn
    simpa only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil,
      id_eq, Bool.or_false] using hneg x hn

lemma negative_replacement_wires_le (n : ℕ) (pre post : List Gate) (g h : Gate) (out : ℕ)
    (F : (Fin n → Bool) → Bool)
    (hm : Monotone2 ⟨pre ++ g :: post, out⟩)
    (hneg : ∀ x : Fin n → Bool, F x = false →
      h.op.eval (h.inputs.map fun i => (run pre (List.ofFn x)).getD i false) = true →
      g.op.eval (g.inputs.map fun i => (run pre (List.ofFn x)).getD i false) = true) :
    ∀ x : Fin n → Bool, F x = false → ∀ w : ℕ,
      (Circuit.wires ⟨pre ++ h :: post, out⟩ (List.ofFn x)).getD w false = true →
      (Circuit.wires ⟨pre ++ g :: post, out⟩ (List.ofFn x)).getD w false = true := by
  intro x hf
  change WireLE (run (pre ++ h :: post) (List.ofFn x))
    (run (pre ++ g :: post) (List.ofFn x))
  rw [run_append, run_append]
  have hpost : ∀ a ∈ post, a.op = .and ∨ a.op = .or := by
    intro a ha
    simpa using (hm a (List.mem_append_right _ (List.mem_cons_of_mem _ ha))).1
  exact run_mono post (by simp)
    (wireLE_snoc rfl (fun _ h => h) (hneg x hf)) hpost


lemma cone_nonincrease_primary_rewire (n : ℕ) (C D : Circuit)
    (hlen : D.gates.length = C.gates.length)
    (hdeps : ∀ j < D.gates.length, ∀ w : ℕ, n ≤ w →
      w ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt D j).inputs →
      w ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs) :
    ∀ i j, PEqualNP.EdgeOwnership.InCone n D i j → PEqualNP.EdgeOwnership.InCone n C i j := by
  intro i j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro hcone
    obtain ⟨hj, k, hkj, hw, hpath⟩ := (SafeLift.inCone_iff n D i j).mp hcone
    apply (SafeLift.inCone_iff n C i j).mpr
    refine ⟨by simpa only [hlen] using hj, k, hkj, hdeps j hj (n+k) (by omega) hw, ?_⟩
    rcases hpath with hpath | hpath
    · exact Or.inl hpath
    · exact Or.inr (ih k hkj hpath)

lemma andPairs_nonincrease_primary_rewire (n : ℕ) (C D : Circuit)
    (hlen : D.gates.length = C.gates.length)
    (hdeps : ∀ j < D.gates.length, ∀ w : ℕ, n ≤ w →
      w ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt D j).inputs →
      w ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs)
    (hops : ∀ j < D.gates.length,
      (PEqualNP.MetaComplexity.NestedCover.gateAt D j).op = GateOp.and →
      (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = GateOp.and) :
    PEqualNP.TopForm.andPairs n D ≤ PEqualNP.TopForm.andPairs n C := by
  unfold PEqualNP.TopForm.andPairs
  apply Finset.card_le_card
  rintro ⟨i,j⟩ hp
  simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hp ⊢
  obtain ⟨⟨hi,hj⟩, hiand, hjand, hcone⟩ := hp
  exact ⟨⟨by simpa only [hlen] using hi, by simpa only [hlen] using hj⟩,
    hops i hi hiand, hops j hj hjand, cone_nonincrease_primary_rewire n C D hlen hdeps i j hcone⟩


def supportValue {n : ℕ} (A : Finset (Fin n)) (x : Fin n → Bool) : Bool :=
  decide (∃ a ∈ A, x a = true)

lemma overlap_operand_switch_negative {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (A B : Finset (Fin n)) (c : Fin n)
    (hremote : ∀ a ∈ A, a ∉ B → G.Adj c a)
    (x : Fin n → Bool) (hfalse : graphFun G ∅ x = false)
    (hnew : supportValue A x && x c = true) :
    supportValue A x && supportValue B x = true := by
  have ha : supportValue A x = true := by
    cases h : supportValue A x <;> simp_all
  have hc : x c = true := by simpa [ha] using hnew
  have ha' : ∃ a ∈ A, x a = true := by simpa only [supportValue, decide_eq_true_eq] using ha
  obtain ⟨a, haA, hxa⟩ := ha'
  suffices hb : supportValue B x = true by simp [ha, hb]
  by_cases haB : a ∈ B
  · exact decide_eq_true ⟨a, haB, hxa⟩
  · have hpos : graphFun G ∅ x = true := by
      simpa [graphFun] using (show ∃ u v, G.Adj u v ∧ x u = true ∧ x v = true from
        ⟨c, a, hremote a haA haB, hc, hxa⟩)
    rw [hfalse] at hpos
    contradiction

lemma overlap_operand_switch_singleton {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (A B : Finset (Fin n)) (c u : Fin n)
    (huA : u ∈ A) (huB : u ∈ B) (hcu : c ≠ u) :
    let x : Fin n → Bool := fun v => decide (v = u)
    graphFun G ∅ x = false ∧
      (supportValue A x && supportValue B x) = true ∧
      (supportValue A x && x c) = false := by
  simp [graphFun, supportValue, huA, huB, hcu]


namespace SharedSupport


open PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm

def setInput {n : ℕ} (X : Finset (Fin n)) : Fin n → Bool :=
  fun w => decide (w ∈ X)

def InputMonotone {n : ℕ} (f : (Fin n → Bool) → Bool) : Prop :=
  ∀ x y, (∀ w, x w = true → y w = true) → f x = true → f y = true

/-- A set omitting a center needs distinct vertices to cover its distinct neighbors. -/
lemma neighbor_cover_card {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hfour : NoFourCycle G) (v : Fin n) (L X : Finset (Fin n))
    (hL : ∀ l ∈ L, G.Adj v l) (hv : v ∉ X)
    (hcover : ∀ l ∈ L, ∃ x ∈ X, G.Adj x l) : L.card ≤ X.card := by
  classical
  let f : L → X := fun l =>
    ⟨Classical.choose (hcover l l.property), (Classical.choose_spec (hcover l l.property)).1⟩
  have hf : ∀ l : L, G.Adj (f l) l := fun l =>
    (Classical.choose_spec (hcover l l.property)).2
  have hinj : Function.Injective f := by
    intro l₁ l₂ heq
    apply Subtype.ext
    have hvf : v ≠ (f l₁ : Fin n) := by
      intro he
      exact hv (he ▸ (f l₁).property)
    have hc := hfour v (f l₁) hvf
    apply Finset.card_le_one.mp hc
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hL l₁ l₁.property, hf l₁⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hL l₂ l₂.property, by
        rw [heq]
        exact hf l₂⟩
  simpa using Fintype.card_le_of_injective f hinj

/-- Negative graph inputs are precisely independent vertex sets. -/
lemma graphFun_setInput_false_iff {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (X : Finset (Fin n)) :
    graphFun G ∅ (setInput X) = false ↔
      ∀ a ∈ X, ∀ b ∈ X, ¬ G.Adj a b := by
  simp [graphFun, setInput]
  aesop

/-- If `U` accepts every singleton in `L` and `U AND D` is below the edge function,
  every negative input accepted by `D` must neighbor every vertex of `L`. -/
lemma neighbor_cover_of_safe_and {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (L X : Finset (Fin n))
    (U D : (Fin n → Bool) → Bool)
    (hUm : InputMonotone U) (hDm : InputMonotone D)
    (hU : ∀ l ∈ L, U (setInput {l}) = true)
    (hbelow : ∀ x, U x = true → D x = true → graphFun G ∅ x = true)
    (hX : graphFun G ∅ (setInput X) = false)
    (hD : D (setInput X) = true) :
    ∀ l ∈ L, ∃ x ∈ X, G.Adj x l := by
  classical
  intro l hl
  by_contra hn
  have hXi := (graphFun_setInput_false_iff G X).mp hX
  have hins : ∀ a ∈ insert l X, ∀ b ∈ insert l X, ¬ G.Adj a b := by
    intro a ha b hb hab
    rcases Finset.mem_insert.mp ha with hal | ha
    · rcases Finset.mem_insert.mp hb with hbl | hb
      · rw [hal, hbl] at hab
        exact G.irrefl hab
      · rw [hal] at hab
        exact hn ⟨b, hb, hab.symm⟩
    · rcases Finset.mem_insert.mp hb with hbl | hb
      · rw [hbl] at hab
        exact hn ⟨a, ha, hab⟩
      · exact hXi a ha b hb hab
  have hUi : U (setInput (insert l X)) = true := by
    apply hUm (setInput {l}) (setInput (insert l X)) ?_ (hU l hl)
    intro w hw
    simpa only [setInput, decide_eq_true_eq, Finset.mem_singleton] using
      (show w ∈ insert l X from by
        have he : w = l := by simpa only [setInput, decide_eq_true_eq,
          Finset.mem_singleton] using hw
        simp [he])
  have hDi : D (setInput (insert l X)) = true := by
    apply hDm (setInput X) (setInput (insert l X)) ?_ hD
    intro w hw
    have hwX : w ∈ X := by simpa only [setInput, decide_eq_true_eq] using hw
    simpa only [setInput, decide_eq_true_eq] using Finset.mem_insert_of_mem hwX
  have hfalse := (graphFun_setInput_false_iff G (insert l X)).mpr hins
  have htrue := hbelow (setInput (insert l X)) hUi hDi
  exact Bool.noConfusion (hfalse.symm.trans htrue)

/-- A negative witness omitting the center has at least as many vertices as the
  shared singleton support. No triangle-free assumption is needed. -/
lemma safe_and_negative_witness_card {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (hfour : NoFourCycle G)
    (v : Fin n) (L X : Finset (Fin n))
    (hL : ∀ l ∈ L, G.Adj v l) (hv : v ∉ X)
    (U D : (Fin n → Bool) → Bool)
    (hUm : InputMonotone U) (hDm : InputMonotone D)
    (hU : ∀ l ∈ L, U (setInput {l}) = true)
    (hbelow : ∀ x, U x = true → D x = true → graphFun G ∅ x = true)
    (hX : graphFun G ∅ (setInput X) = false)
    (hD : D (setInput X) = true) : L.card ≤ X.card := by
  exact neighbor_cover_card G hfour v L X hL hv
    (neighbor_cover_of_safe_and G L X U D hUm hDm hU hbelow hX hD)

end SharedSupport


lemma GraphExtremal.activity_le_of_nonincrease {n : ℕ} {G : SimpleGraph (Fin n)}
    [DecidableRel G.Adj] {activity : Circuit → ℕ} {C D : Circuit}
    (hC : GraphExtremal n G activity C) (hmD : Monotone2 D)
    (hcD : circuitFun n D = graphFun G ∅) (hsize : D.size ≤ C.size)
    (hjunk : (PEqualNP.TopForm.junk G D).card ≤ (PEqualNP.TopForm.junk G C).card)
    (hpairs : PEqualNP.TopForm.andPairs n D ≤ PEqualNP.TopForm.andPairs n C) :
    activity C ≤ activity D := by
  have hminD : IsMinimalMonoCircuit n D := by
    refine ⟨hmD, ?_⟩
    intro E hmE he
    exact hsize.trans (hC.1.2 E hmE ((he.trans hcD).trans hC.2.1.symm))
  have hj : (PEqualNP.TopForm.junk G D).card = (PEqualNP.TopForm.junk G C).card :=
    Nat.le_antisymm hjunk (hC.2.2.2.1 D hminD hcD)
  have hp : PEqualNP.TopForm.andPairs n D = PEqualNP.TopForm.andPairs n C :=
    Nat.le_antisymm hpairs (hC.2.2.2.2.1 D hminD hcD hj)
  exact hC.2.2.2.2.2 D hminD hcD hj hp

end PEqualNP.Outside.L_meta_1904_aux
