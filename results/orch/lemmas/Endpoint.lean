import PEqualNP.Defs
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.GetD

namespace PEqualNP.Outside.L_meta_2592.Endpoint

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun acc g => acc ++ [g.op.eval (g.inputs.map fun i => acc.getD i false)]) w

lemma getD_snoc_eq (l : List Bool) (b : Bool) : (l ++ [b]).getD l.length false = b := by
  simp

lemma gateOp_eval_mono (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or)
    (l₁ l₂ : List Bool) (hlen : l₁.length = l₂.length)
    (hle : ∀ i, l₁.getD i false = true → l₂.getD i false = true) :
    op.eval l₁ = true → op.eval l₂ = true := by
  rcases hop with rfl | rfl
  · simp only [GateOp.eval, List.all_eq_true, id_eq]
    intro h b hb
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hb
    have h1 : l₁.getD i false = true := by
      have hi1 : i < l₁.length := by omega
      rw [List.getD_eq_getElem _ _ hi1]
      exact h _ (List.getElem_mem hi1)
    have h2 := hle i h1
    rwa [List.getD_eq_getElem _ _ hi] at h2
  · simp only [GateOp.eval, List.any_eq_true, id_eq]
    rintro ⟨b, hb, rfl⟩
    obtain ⟨i, hi, hbi⟩ := List.getElem_of_mem hb
    have h1 : l₁.getD i false = true := by
      rw [List.getD_eq_getElem _ _ hi]; exact hbi
    have h2 := hle i h1
    have hi2 : i < l₂.length := by omega
    rw [List.getD_eq_getElem _ _ hi2] at h2
    exact ⟨l₂[i], List.getElem_mem hi2, h2⟩

lemma wiresFrom_mono (gs : List Gate)
    (hmono : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) :
    ∀ (w₁ w₂ : List Bool), w₁.length = w₂.length →
      (∀ i, w₁.getD i false = true → w₂.getD i false = true) →
      ∀ i, (wiresFrom gs w₁).getD i false = true → (wiresFrom gs w₂).getD i false = true := by
  induction gs with
  | nil =>
    intro w₁ w₂ _ hle i hi
    exact hle i hi
  | cons g gs ih =>
    intro w₁ w₂ hlen hle i hi
    have hstep1 : wiresFrom (g :: gs) w₁ =
        wiresFrom gs (w₁ ++ [g.op.eval (g.inputs.map fun j => w₁.getD j false)]) := rfl
    have hstep2 : wiresFrom (g :: gs) w₂ =
        wiresFrom gs (w₂ ++ [g.op.eval (g.inputs.map fun j => w₂.getD j false)]) := rfl
    rw [hstep1] at hi
    rw [hstep2]
    apply ih (fun g' hg' => hmono g' (List.mem_cons_of_mem g hg')) _ _ (by simp [hlen]) _ i hi
    intro j hj
    by_cases hlt : j < w₁.length
    · rw [List.getD_append _ _ _ _ hlt] at hj
      rw [List.getD_append _ _ _ _ (by omega)]
      exact hle j hj
    · by_cases heq : j = w₁.length
      · subst heq
        rw [getD_snoc_eq] at hj
        rw [hlen, getD_snoc_eq]
        exact gateOp_eval_mono g.op (hmono g List.mem_cons_self)
          (g.inputs.map fun k => w₁.getD k false) (g.inputs.map fun k => w₂.getD k false)
          (by simp) (by
            intro t ht
            by_cases ht_lt : t < g.inputs.length
            · rw [List.getD_eq_getElem _ _ (by simpa using ht_lt)] at ht
              rw [List.getD_eq_getElem _ _ (by simpa using ht_lt)]
              simp only [List.getElem_map] at ht ⊢
              exact hle _ ht
            · rw [List.getD_eq_default _ _ (by simpa using Nat.le_of_not_lt ht_lt)] at ht
              exact Bool.noConfusion ht) hj
      · rw [List.getD_eq_default _ _ (by simp; omega)] at hj
        exact Bool.noConfusion hj

lemma eval_mono2 (C : Circuit) (mono : Monotone2 C) {n : ℕ} (x y : Fin n → Bool)
    (hle : ∀ k, x k = true → y k = true) (hx : C.eval (List.ofFn x) = true) :
    C.eval (List.ofFn y) = true := by
  have hm : ∀ g ∈ C.gates, g.op = GateOp.and ∨ g.op = GateOp.or := by
    intro g hg
    have h := (mono g hg).1
    simpa using h
  refine wiresFrom_mono C.gates hm (List.ofFn x) (List.ofFn y) (by simp) ?_
    C.output hx
  intro j hj
  by_cases hjlt : j < n
  · rw [List.getD_eq_getElem _ _ (by simpa using hjlt)] at hj ⊢
    simp only [List.getElem_ofFn] at hj ⊢
    exact hle ⟨j, hjlt⟩ hj
  · rw [List.getD_eq_default _ _ (by simp; omega)] at hj
    exact Bool.noConfusion hj

lemma eval_monotone (C : Circuit) (mono : Monotone2 C) (n : ℕ) :
    Monotone (fun x : Fin n → Bool => C.eval (List.ofFn x)) := by
  intro x y hxy
  change C.eval (List.ofFn x) ≤ C.eval (List.ofFn y)
  apply Bool.le_iff_imp.mpr
  intro hx
  apply eval_mono2 C mono x y ?_ hx
  intro i hi
  exact (Bool.le_iff_imp.mp (hxy i)) hi

lemma negated_output_exclusion {n : ℕ} (C : Circuit) (mono : Monotone2 C)
    (f : (Fin n → Bool) → Bool) (bottom : f (fun _ => false) = false)
    (top : f (fun _ => true) = true) :
    ¬ ∀ x : Fin n → Bool, Bool.not (C.eval (List.ofFn x)) = f x := by
  intro correct
  have low := correct (fun _ => false)
  have high := correct (fun _ => true)
  rw [bottom] at low
  rw [top] at high
  have lo : C.eval (List.ofFn (fun _ : Fin n => false)) = true := by
    cases h : C.eval (List.ofFn (fun _ : Fin n => false)) <;> simp_all
  have hi := eval_mono2 C mono (fun _ : Fin n => false) (fun _ => true)
    (fun _ _ => rfl) lo
  rw [hi] at high
  cases high


lemma wiresFrom_length (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp [wiresFrom]
  | cons g gs ih =>
    change (wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])).length = _
    rw [ih]
    simp [Nat.add_comm, Nat.add_left_comm]

lemma append_not_eval {n : ℕ} (C : Circuit) (x : Fin n → Bool) :
    (Circuit.mk (C.gates ++ [⟨GateOp.not, [C.output]⟩]) (n + C.size)).eval
      (List.ofFn x) = Bool.not (C.eval (List.ofFn x)) := by
  have len : (C.wires (List.ofFn x)).length = n + C.size := by
    simpa [wiresFrom, Circuit.wires, Circuit.size] using wiresFrom_length C.gates (List.ofFn x)
  unfold Circuit.eval Circuit.wires
  simp only [List.foldl_append, List.foldl_cons, List.foldl_nil]
  change ((C.wires (List.ofFn x)) ++ [Bool.not (C.eval (List.ofFn x))]).getD (n + C.size) false = _
  rw [← len]
  simp [Circuit.eval, Circuit.wires]

lemma append_not_exclusion {n : ℕ} (C : Circuit) (mono : Monotone2 C)
    (f : (Fin n → Bool) → Bool) (bottom : f (fun _ => false) = false)
    (top : f (fun _ => true) = true) :
    ¬ ∀ x : Fin n → Bool,
      (Circuit.mk (C.gates ++ [⟨GateOp.not, [C.output]⟩]) (n + C.size)).eval
        (List.ofFn x) = f x := by
  simpa only [append_not_eval] using negated_output_exclusion C mono f bottom top


lemma terminal_not_exclusion {n : ℕ} (gs : List Gate) (ins : List ℕ)
    (mono : Monotone2 ⟨gs, 0⟩)
    (f : (Fin n → Bool) → Bool) (bottom : f (fun _ => false) = false)
    (top : f (fun _ => true) = true) :
    ¬ ∀ x : Fin n → Bool,
      (Circuit.mk (gs ++ [⟨GateOp.not, ins⟩]) (n + gs.length)).eval
        (List.ofFn x) = f x := by
  cases ins with
  | nil =>
    intro correct
    have eq := correct (fun _ => false)
    have len := wiresFrom_length gs (List.ofFn (fun _ : Fin n => false))
    simp only [List.length_ofFn] at len
    simp only [Circuit.eval, Circuit.wires, List.foldl_append, List.foldl_cons,
      List.foldl_nil, List.map_nil, GateOp.eval, List.headD_nil] at eq
    change ((wiresFrom gs (List.ofFn (fun _ : Fin n => false))) ++ [true]).getD
      (n + gs.length) false = _ at eq
    rw [← len] at eq
    simp only [getD_snoc_eq, bottom] at eq
    cases eq
  | cons i rest =>
    intro correct
    apply append_not_exclusion (Circuit.mk gs i) mono f bottom top
    intro x
    have eq := correct x
    simpa only [Circuit.eval, Circuit.wires, List.foldl_append, List.foldl_cons,
      List.foldl_nil, List.map_cons, List.map_nil, GateOp.eval, List.headD_cons,
      Circuit.size] using eq

end PEqualNP.Outside.L_meta_2592.Endpoint
