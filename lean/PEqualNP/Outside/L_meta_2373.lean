import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2373_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun acc g => acc ++ [g.op.eval (g.inputs.map fun i => acc.getD i false)]) w
lemma getD_snoc_eq (l : List Bool) (b : Bool) : (l ++ [b]).getD l.length false = b := by simp
lemma gateOp_eval_mono (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or)
    (l₁ l₂ : List Bool) (hlen : l₁.length = l₂.length)
    (hle : ∀ i, l₁.getD i false = true → l₂.getD i false = true) :
    op.eval l₁ = true → op.eval l₂ = true := by
  rcases hop with rfl | rfl
  · change l₁.all id = true → l₂.all id = true
    simp only [List.all_eq_true, id_eq]
    intro h b hb
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hb
    have h1 : l₁.getD i false = true := by
      have hi1 : i < l₁.length := by omega
      rw [List.getD_eq_getElem _ _ hi1]
      exact h _ (List.getElem_mem hi1)
    have h2 := hle i h1
    rwa [List.getD_eq_getElem _ _ hi] at h2
  · change l₁.any id = true → l₂.any id = true
    simp only [List.any_eq_true, id_eq]
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
def rows : List ℕ := [3, 6, 12, 17, 24, 33, 50, 66, 69, 104, 116, 132, 138, 160, 201, 208, 264, 276, 288, 320, 385, 402, 521, 528, 548, 554, 576, 640, 770, 773]
def pos : List ℕ := [3, 6, 12, 17, 24, 33, 66, 132, 160, 264, 288, 320, 528, 576, 640]
def neg : List ℕ := [50, 69, 104, 116, 138, 201, 208, 276, 385, 402, 521, 548, 554, 770, 773]
def bits (r : ℕ) (i : Fin 10) := r.testBit i.val
def edge (x : Fin 10 → Bool) : Bool :=
  (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 4 && x 9) || (x 5 && x 7) || (x 7 && x 9) || (x 9 && x 6) || (x 6 && x 8) || (x 8 && x 5)
def below (a b : Fin 10 → Bool) : Bool := (List.finRange 10).all fun i => !(a i) || b i
lemma below_elim {a b} (h : below a b = true) {i : Fin 10} (hi : a i = true) : b i = true := by
  have hh := List.all_eq_true.mp h i (by simp)
  simpa [hi] using hh
set_option maxRecDepth 20000 in
lemma endpoints : ∀ r : Fin 1024,
    (if edge (bits r) then pos.any (fun q => below (bits q) (bits r))
     else neg.any (fun q => below (bits r) (bits q))) = true := by decide +kernel
lemma liftRows (f : (Fin 10 → Bool) → Bool)
    (hm : ∀ a b : Fin 10 → Bool, (∀ i, a i = true → b i = true) → f a = true → f b = true)
    (hr : ∀ q ∈ rows, f (bits q) = decide (q ∈ pos)) : ∀ x, f x = edge x := by
  intro x
  let w := BitVec.ofBoolListLE (List.ofFn x)
  have hw : w.toNat < 1024 := by
    have h := w.isLt
    simpa [w] using h
  let r : Fin 1024 := ⟨w.toNat, hw⟩
  have eqx : bits r = x := by
    funext i
    change w.getLsbD i.val = x i
    rw [BitVec.getLsbD_ofBoolListLE, List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn]
  have coverage := endpoints r
  rw [eqx] at coverage
  have hpRows : ∀ q ∈ pos, q ∈ rows := by decide +kernel
  have hnRows : ∀ q ∈ neg, q ∈ rows ∧ q ∉ pos := by decide +kernel
  cases he : edge x with
  | false =>
    rw [he] at coverage
    obtain ⟨q, hq, hle⟩ := List.any_eq_true.mp coverage
    have hn := hnRows q hq
    have hval := hr q hn.1
    rw [decide_eq_false hn.2] at hval
    cases hf : f x with
    | false => rfl
    | true =>
      have := hm x (bits q) (fun _ hi => below_elim hle hi) hf
      rw [hval] at this
      contradiction
  | true =>
    rw [he] at coverage
    obtain ⟨q, hq, hle⟩ := List.any_eq_true.mp coverage
    exact hm (bits q) x (fun _ hi => below_elim hle hi) (by simpa [hq] using hr q (hpRows q hq))
lemma eval_mono (C : Circuit) (hm : Monotone2 C) (x y : List Bool) (len : x.length=y.length)
    (hle : ∀ i, x.getD i false = true → y.getD i false = true) :
    C.eval x = true → C.eval y = true := by
  exact wiresFrom_mono C.gates (fun g hg => by simpa using (hm g hg).1) x y len hle C.output
lemma apply_boundary (C : Circuit) (hm : Monotone2 C)
    (hr : ∀ r ∈ rows, C.eval (List.ofFn (bits r)) = decide (r ∈ pos)) :
    ∀ x, C.eval (List.ofFn x) = edge x := by
  apply liftRows _ _ hr
  intro a b hab
  apply eval_mono C hm _ _ (by simp)
  intro i hi
  by_cases hl : i < 10
  · have ha : i < (List.ofFn a).length := by simpa only [List.length_ofFn] using hl
    have hb : i < (List.ofFn b).length := by simpa only [List.length_ofFn] using hl
    rw [List.getD_eq_getElem _ _ ha, List.getElem_ofFn] at hi
    rw [List.getD_eq_getElem _ _ hb, List.getElem_ofFn]
    exact hab _ hi
  · rw [List.getD_eq_default _ _ (by simp; omega)] at hi
    contradiction

lemma boundary_size : rows.length = 30 ∧ pos.length = 15 ∧ neg.length = 15 := by
  decide +kernel

lemma boundary_values : ∀ r ∈ rows, edge (bits r) = decide (r ∈ pos) := by
  decide +kernel

lemma circuit_boundary_iff (C : Circuit) (hm : Monotone2 C) :
    (∀ r ∈ rows, C.eval (List.ofFn (bits r)) = decide (r ∈ pos)) ↔
      ∀ x : Fin 10 → Bool, C.eval (List.ofFn x) = edge x := by
  constructor
  · exact apply_boundary C hm
  · intro h r hr
    exact (h (bits r)).trans (boundary_values r hr)

end PEqualNP.Outside.L_meta_2373_aux
