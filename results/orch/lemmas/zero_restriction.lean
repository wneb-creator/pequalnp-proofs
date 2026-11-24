import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3451

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover

def zResWire {m n : ℕ} (r : Fin m → Option (Fin n)) (i : ℕ) : Option ℕ :=
  if hi : i < m then (r ⟨i, hi⟩).map Fin.val else some (n + (i - m))

def zResGate (ρ : ℕ → Option ℕ) (g : Gate) : Gate :=
  match g.op with
  | .and => if g.inputs.any (fun i => (ρ i).isNone) then ⟨.or, []⟩
      else ⟨.and, g.inputs.filterMap ρ⟩
  | op => ⟨op, g.inputs.filterMap ρ⟩

def zResCircuit {m n : ℕ} (r : Fin m → Option (Fin n)) (C : Circuit) : Circuit :=
  ⟨C.gates.map (zResGate (zResWire r)), (zResWire r C.output).getD (n + C.size)⟩

def zResInput {m n : ℕ} (r : Fin m → Option (Fin n)) (z : Fin n → Bool) : Fin m → Bool :=
  fun i => (r i).elim false z

lemma zRes_size {m n : ℕ} (r : Fin m → Option (Fin n)) (C : Circuit) :
    (zResCircuit r C).size = C.size := by
  simp [zResCircuit, Circuit.size]

lemma zRes_gate_mono (ρ : ℕ → Option ℕ) (g : Gate)
    (hop : g.op = .and ∨ g.op = .or) (hlen : g.inputs.length ≤ 2) :
    ((zResGate ρ g).op = .and ∨ (zResGate ρ g).op = .or) ∧
      (zResGate ρ g).inputs.length ≤ 2 := by
  rcases g with ⟨op, ins⟩
  rcases hop with rfl | rfl
  · simp only [zResGate]
    split
    · simp
    · exact ⟨Or.inl rfl, (List.length_filterMap_le ρ ins).trans hlen⟩
  · exact ⟨Or.inr rfl, (List.length_filterMap_le ρ ins).trans hlen⟩

lemma zRes_monotone {m n : ℕ} (r : Fin m → Option (Fin n)) (C : Circuit)
    (hC : Monotone2 C) : Monotone2 (zResCircuit r C) := by
  intro g hg
  obtain ⟨g₀, hg₀, rfl⟩ := List.mem_map.mp hg
  exact zRes_gate_mono _ _ (hC g₀ hg₀).1 (hC g₀ hg₀).2

lemma zRes_gate_eval (ρ : ℕ → Option ℕ) (g : Gate) (a b : ℕ → Bool)
    (hop : g.op = .and ∨ g.op = .or) (hlen : g.inputs.length ≤ 2)
    (hval : ∀ i, (ρ i).elim false b = a i) :
    (zResGate ρ g).op.eval ((zResGate ρ g).inputs.map b) =
      g.op.eval (g.inputs.map a) := by
  rcases g with ⟨op, ins⟩
  rcases hop with rfl | rfl
  all_goals
    rcases ins with _ | ⟨i, _ | ⟨j, _ | ⟨k, ins⟩⟩⟩
    · simp [zResGate, GateOp.eval]
    · specialize hval i
      cases hρ : ρ i <;> simp_all [zResGate, GateOp.eval]
    · have hi := hval i
      have hj := hval j
      cases hρi : ρ i <;> cases hρj : ρ j <;> simp_all [zResGate, GateOp.eval]
    · simp at hlen

lemma zRes_snoc (w : List Bool) (v : Bool) (i : ℕ) :
    (w ++ [v]).getD i false = if i = w.length then v else w.getD i false := by
  by_cases hi : i < w.length
  · rw [List.getD_append _ _ _ _ hi, if_neg (by omega)]
  · rw [List.getD_append_right _ _ _ _ (by omega)]
    by_cases he : i = w.length
    · subst i; simp
    · rw [if_neg he, List.getD_eq_default w false (by omega),
        List.getD_eq_default [v] false (by simp; omega)]

lemma zRes_wire_gate {m n : ℕ} (r : Fin m → Option (Fin n)) (j : ℕ) :
    zResWire r (m + j) = some (n + j) := by
  simp [zResWire]

lemma zRes_step_rel {m n : ℕ} (r : Fin m → Option (Fin n))
    (a b : List Bool) (k : ℕ) (ha : a.length = m + k) (hb : b.length = n + k)
    (hv : ∀ i, (zResWire r i).elim false (fun j => b.getD j false) = a.getD i false)
    (v : Bool) :
    ∀ i, (zResWire r i).elim false (fun j => (b ++ [v]).getD j false) =
      (a ++ [v]).getD i false := by
  intro i
  have hv_i := hv i
  rw [zRes_snoc, ha]
  by_cases hi : i < m
  · have he : i ≠ m + k := by omega
    rw [if_neg he]
    rw [zResWire, dif_pos hi] at hv_i ⊢
    cases hri : r ⟨i, hi⟩ with
    | none => simpa [hri] using hv_i
    | some j =>
      have hj : j.val < b.length := by rw [hb]; omega
      simp only [hri, Option.map_some, Option.elim_some] at hv_i ⊢
      rw [List.getD_append _ _ _ _ hj]
      exact hv_i
  · rw [zResWire, dif_neg hi] at hv_i ⊢
    simp only [Option.elim_some]
    rw [zRes_snoc, hb]
    by_cases he : i = m + k
    · subst i; simp
    · have he' : n + (i - m) ≠ n + k := by omega
      rw [if_neg he, if_neg he']
      simpa [zResWire, hi] using hv_i

lemma zRes_fold_rel {m n : ℕ} (r : Fin m → Option (Fin n)) (gs : List Gate) :
    ∀ (a b : List Bool) (k : ℕ), a.length = m + k → b.length = n + k →
      (∀ g ∈ gs, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2) →
      (∀ i, (zResWire r i).elim false (fun j => b.getD j false) = a.getD i false) →
      ∀ i, (zResWire r i).elim false (fun j =>
        ((gs.map (zResGate (zResWire r))).foldl
          (fun w g => w ++ [g.op.eval (g.inputs.map fun t => w.getD t false)]) b).getD j false) =
        (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun t => w.getD t false)]) a).getD i false := by
  induction gs with
  | nil => intro a b k ha hb hgs hv i; exact hv i
  | cons g gs ih =>
    intro a b k ha hb hgs hv
    have hg := hgs g (by simp)
    have he := zRes_gate_eval (zResWire r) g (fun i => a.getD i false)
      (fun i => b.getD i false) hg.1 hg.2 hv
    simp only [List.map_cons, List.foldl_cons, he]
    apply ih _ _ (k + 1)
    · simp [ha]; omega
    · simp [hb]; omega
    · intro g' hg'; exact hgs g' (by simp [hg'])
    · exact zRes_step_rel r a b k ha hb hv _

lemma zRes_input_rel {m n : ℕ} (r : Fin m → Option (Fin n)) (z : Fin n → Bool) (i : ℕ) :
    (zResWire r i).elim false (fun j => (List.ofFn z).getD j false) =
      (List.ofFn (zResInput r z)).getD i false := by
  by_cases hi : i < m
  · simp only [zResWire, dif_pos hi]
    rw [List.getD_eq_getElem _ _ (by simp [hi])]
    simp only [List.getElem_ofFn, zResInput]
    cases hr : r ⟨i, hi⟩ with
    | none => rfl
    | some j => simp [j.isLt]
  · simp [zResWire, hi, List.getD_eq_default, zResInput]

lemma zRes_wires {m n : ℕ} (r : Fin m → Option (Fin n)) (C : Circuit)
    (hC : Monotone2 C) (z : Fin n → Bool) (i : ℕ) :
    (zResWire r i).elim false (fun j => ((zResCircuit r C).wires (List.ofFn z)).getD j false) =
      (C.wires (List.ofFn (zResInput r z))).getD i false := by
  exact zRes_fold_rel r C.gates _ _ 0 (by simp) (by simp) hC
    (zRes_input_rel r z) i

lemma zRes_wires_gate {m n : ℕ} (r : Fin m → Option (Fin n)) (C : Circuit)
    (hC : Monotone2 C) (z : Fin n → Bool) (j : ℕ) :
    ((zResCircuit r C).wires (List.ofFn z)).getD (n + j) false =
      (C.wires (List.ofFn (zResInput r z))).getD (m + j) false := by
  simpa [zRes_wire_gate] using zRes_wires r C hC z (m + j)

lemma zRes_gateAt {m n : ℕ} (r : Fin m → Option (Fin n)) (C : Circuit) (j : ℕ) :
    gateAt (zResCircuit r C) j = zResGate (zResWire r) (gateAt C j) := by
  have he : zResGate (zResWire r) ⟨.or, []⟩ = ⟨.or, []⟩ := rfl
  unfold gateAt zResCircuit
  change (C.gates.map (zResGate (zResWire r))).getD j _ = _
  simpa only [he] using List.getD_map (n := j) C.gates ⟨GateOp.or, []⟩
    (zResGate (zResWire r))

lemma zRes_inputs (ρ : ℕ → Option ℕ) (g : Gate) (i : ℕ)
    (hi : i ∈ (zResGate ρ g).inputs) : ∃ j ∈ g.inputs, ρ j = some i := by
  cases g with
  | mk op ins =>
    cases op <;> simp only [zResGate] at hi
    · split at hi
      · simp at hi
      · exact List.mem_filterMap.mp hi
    all_goals exact List.mem_filterMap.mp hi

lemma zRes_wire_lt {m n : ℕ} (r : Fin m → Option (Fin n)) (i j k : ℕ)
    (hi : i < m + k) (hr : zResWire r i = some j) : j < n + k := by
  by_cases him : i < m
  · simp only [zResWire, dif_pos him] at hr
    cases he : r ⟨i, him⟩ with
    | none => simp [he] at hr
    | some t => simp [he] at hr; subst j; omega
  · simp only [zResWire, dif_neg him, Option.some.injEq] at hr
    omega

lemma zRes_readsBack {m n : ℕ} (r : Fin m → Option (Fin n)) (C : Circuit)
    (hC : ReadsBack m C) : ReadsBack n (zResCircuit r C) := by
  intro j hj i hi
  have hj' : j < C.gates.length := by simpa [zResCircuit] using hj
  rw [zRes_gateAt] at hi
  obtain ⟨k, hk, hki⟩ := zRes_inputs _ _ _ hi
  exact zRes_wire_lt r k i j (hC j hj' k hk) hki

lemma zRes_and_source (ρ : ℕ → Option ℕ) (g : Gate)
    (h : (zResGate ρ g).op = .and) : g.op = .and := by
  cases g with
  | mk op ins =>
    cases op <;> simp_all [zResGate]

lemma zRes_and_wire {m n : ℕ} (r : Fin m → Option (Fin n)) (C : Circuit)
    (hC : Monotone2 C) (j : ℕ) (hj : (gateAt (zResCircuit r C) j).op = .and)
    (z : Fin n → Bool) :
    (gateAt C j).op = .and ∧
      ((zResCircuit r C).wires (List.ofFn z)).getD (n + j) false =
        (C.wires (List.ofFn (zResInput r z))).getD (m + j) false := by
  rw [zRes_gateAt] at hj
  exact ⟨zRes_and_source _ _ hj, zRes_wires_gate r C hC z j⟩

lemma zRes_wires_length (C : Circuit) (x : List Bool) :
    (C.wires x).length = x.length + C.gates.length := by
  have hf : ∀ (gs : List Gate) (w : List Bool),
      (gs.foldl (fun a g => a ++ [g.op.eval (g.inputs.map fun i => a.getD i false)]) w).length =
        w.length + gs.length := by
    intro gs
    induction gs with
    | nil => intro w; simp
    | cons g gs ih =>
      intro w
      simp only [List.foldl_cons, List.length_cons]
      rw [ih]
      simp; omega
  exact hf C.gates x

lemma zRes_eval {m n : ℕ} (r : Fin m → Option (Fin n)) (C : Circuit)
    (hC : Monotone2 C) (z : Fin n → Bool) :
    circuitFun n (zResCircuit r C) z = circuitFun m C (zResInput r z) := by
  have hv := zRes_wires r C hC z C.output
  change ((zResCircuit r C).wires (List.ofFn z)).getD
      ((zResWire r C.output).getD (n + C.size)) false = _
  cases hr : zResWire r C.output with
  | none =>
    simp only [hr, Option.elim_none] at hv
    rw [Option.getD_none, List.getD_eq_default _ false (by
      rw [zRes_wires_length]
      simp [zResCircuit, Circuit.size])]
    exact hv
  | some j => simpa [hr, circuitFun, Circuit.eval] using hv

end PEqualNP.Outside.L_meta_3451
