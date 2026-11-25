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

end PEqualNP.Outside.L_meta_1904_aux
