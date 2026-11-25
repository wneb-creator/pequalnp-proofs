import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2592_aux.LeanRoute
open PEqualNP.CircuitLowerBounds

def wf (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

lemma getD_snoc_lt (L : List Bool) (a : Bool) (w : ℕ) (h : w < L.length) :
    (L ++ [a]).getD w false = L.getD w false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

lemma getD_snoc_eq (L : List Bool) (a : Bool) : (L ++ [a]).getD L.length false = a := by
  simp [List.getD_eq_getElem?_getD]

lemma getD_snoc_gt (L : List Bool) (a : Bool) (w : ℕ) (h : L.length < w) :
    (L ++ [a]).getD w false = false := by
  rw [List.getD_eq_default]; simp; omega

lemma eval_mono (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or) (ins : List ℕ)
    (U V : List Bool) (h : ∀ i, U.getD i false = true → V.getD i false = true) :
    op.eval (ins.map fun i => U.getD i false) = true →
    op.eval (ins.map fun i => V.getD i false) = true := by
  rcases hop with rfl | rfl
  · simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp, id]
    exact fun hall i hi => h i (hall i hi)
  · simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp, id]
    exact fun ⟨i, hi, hv⟩ => ⟨i, hi, h i hv⟩

lemma ofFn_mono (n : ℕ) (x y : Fin n → Bool) (hxy : ∀ v : Fin n, x v = true → y v = true)
    (w : ℕ) : (List.ofFn x).getD w false = true → (List.ofFn y).getD w false = true := by
  by_cases hw : w < n
  · simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, hw, dite_true, Option.getD_some]
    exact hxy ⟨w, hw⟩
  · rw [List.getD_eq_default _ _ (by simp; omega)]
    simp

lemma mono2 (gs : List Gate)
    (hleg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) :
    ∀ U V : List Bool, U.length = V.length →
      (∀ i, U.getD i false = true → V.getD i false = true) →
      ∀ i, (wf gs U).getD i false = true → (wf gs V).getD i false = true := by
  induction gs with
  | nil => intro U V _ h i; exact h i
  | cons g gs ih =>
    intro U V hlen h i
    have hg := (hleg g (by simp)).1
    have := ih (fun g' hg' => hleg g' (by simp [hg']))
      (U ++ [g.op.eval (g.inputs.map fun i => U.getD i false)])
      (V ++ [g.op.eval (g.inputs.map fun i => V.getD i false)]) (by simp [hlen]) (by
        intro t
        rcases Nat.lt_trichotomy t U.length with ht | ht | ht
        · rw [getD_snoc_lt _ _ _ ht, getD_snoc_lt _ _ _ (by omega)]; exact h t
        · subst ht
          rw [getD_snoc_eq]
          have e2 := getD_snoc_eq V (g.op.eval (g.inputs.map fun i => V.getD i false))
          rw [← hlen] at e2
          rw [e2]
          exact eval_mono g.op hg g.inputs U V h
        · rw [getD_snoc_gt _ _ _ ht]; intro hf; exact absurd hf (by simp)) i
    simpa [wf] using this


lemma mono_not_cannot_rise (C : Circuit) (hC : PEqualNP.MetaComplexity.Monotone2 C)
    (n : ℕ) (x y : Fin n → Bool) (hxy : ∀ v, x v = true → y v = true)
    (hx : !C.eval (List.ofFn x) = false) (hy : !C.eval (List.ofFn y) = true) : False := by
  have pos : C.eval (List.ofFn x) = true := by simpa using hx
  have neg : C.eval (List.ofFn y) = false := by simpa using hy
  have rising := mono2 C.gates (fun g hg => ⟨by
      rcases (hC g hg).1 with h | h
      · exact Or.inl h
      · exact Or.inr h, (hC g hg).2⟩)
    (List.ofFn x) (List.ofFn y) (by simp) (ofFn_mono n x y hxy) C.output pos
  change C.eval (List.ofFn y) = true at rising
  rw [neg] at rising
  cases rising

lemma no_complement_petersen (C : Circuit) (hC : PEqualNP.MetaComplexity.Monotone2 C) :
    ¬ ∀ x : Fin 10 → Bool, !C.eval (List.ofFn x) =
      (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
       x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 4 && x 9 ||
       x 5 && x 7 || x 7 && x 9 || x 9 && x 6 || x 6 && x 8 || x 8 && x 5) := by
  intro h
  exact mono_not_cannot_rise C hC 10 (fun _ => false) (fun _ => true)
    (by simp) (by simpa using h (fun _ => false)) (by simpa using h (fun _ => true))


lemma wf_length (gs : List Gate) (w : List Bool) :
    (wf gs w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp [wf]
  | cons g gs ih =>
    change (wf gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])).length = _
    rw [ih]
    simp
    omega

lemma wf_fixed_input (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (wf gs w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    change (wf gs (w ++ [g.op.eval (g.inputs.map fun j => w.getD j false)])).getD i false = _
    rw [ih _ (by simp; omega), getD_snoc_lt _ _ _ hi]

lemma not_input_gate_mono (v : ℕ) (g : Gate)
    (basis : g.op = .and ∨ g.op = .or ∨ g.op = .not)
    (reads : (g.op = .not → g.inputs.head? = some v) ∧
      (g.op = .and ∨ g.op = .or → v ∉ g.inputs))
    (U V : List Bool) (atV : U.getD v false = true)
    (other : ∀ i, i ≠ v → U.getD i false = true → V.getD i false = true) :
    g.op.eval (g.inputs.map fun i => U.getD i false) = true →
    g.op.eval (g.inputs.map fun i => V.getD i false) = true := by
  rcases basis with hand | hor | hnot
  · have avoids := reads.2 (Or.inl hand)
    rw [hand]
    simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp, id]
    intro hall i hi
    exact other i (by intro eq; subst i; exact avoids hi) (hall i hi)
  · have avoids := reads.2 (Or.inr hor)
    rw [hor]
    simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp, id]
    rintro ⟨i, hi, hu⟩
    exact ⟨i, hi, other i (by intro eq; subst i; exact avoids hi) hu⟩
  · have head := reads.1 hnot
    rcases args : g.inputs with _ | ⟨a, rest⟩
    · simp [args] at head
    · have av : a = v := by simpa [args] using head
      subst a
      simp [hnot, GateOp.eval, args, atV]

lemma not_input_wf_mono (gs : List Gate) (v : ℕ)
    (hleg : ∀ g ∈ gs, (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧
      (g.op = .not → g.inputs.head? = some v) ∧
      (g.op = .and ∨ g.op = .or → v ∉ g.inputs)) :
    ∀ U V : List Bool, U.length = V.length → v < U.length → U.getD v false = true →
      (∀ i, i ≠ v → U.getD i false = true → V.getD i false = true) →
      ∀ i, i ≠ v → (wf gs U).getD i false = true → (wf gs V).getD i false = true := by
  induction gs with
  | nil => intro U V _ _ _ h i hi; exact h i hi
  | cons g gs ih =>
    intro U V hlen hv hU h i hi
    have hg := hleg g (by simp)
    have next := ih (fun g' hg' => hleg g' (by simp [hg']))
      (U ++ [g.op.eval (g.inputs.map fun j => U.getD j false)])
      (V ++ [g.op.eval (g.inputs.map fun j => V.getD j false)])
      (by simp [hlen]) (by simp; omega)
      (by rw [getD_snoc_lt _ _ _ hv]; exact hU)
      (by
        intro t ht
        rcases Nat.lt_trichotomy t U.length with lt | eq | gt
        · rw [getD_snoc_lt _ _ _ lt, getD_snoc_lt _ _ _ (by omega)]
          exact h t ht
        · subst t
          rw [getD_snoc_eq]
          have e := getD_snoc_eq V (g.op.eval (g.inputs.map fun j => V.getD j false))
          rw [← hlen] at e
          rw [e]
          exact not_input_gate_mono v g hg.1 hg.2 U V hU h
        · rw [getD_snoc_gt _ _ _ gt]
          simp) i hi
    simpa [wf] using next

lemma not_input_eval_antitone (C : Circuit) (n : ℕ) (v : Fin n)
    (hleg : ∀ g ∈ C.gates, (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧
      (g.op = .not → g.inputs.head? = some v.val) ∧
      (g.op = .and ∨ g.op = .or → v.val ∉ g.inputs))
    (x y : Fin n → Bool) (hy : y v = true)
    (hxy : ∀ i, i ≠ v → x i = y i) (hout : C.output ≠ v.val) :
    C.eval (List.ofFn y) = true → C.eval (List.ofFn x) = true := by
  apply not_input_wf_mono C.gates v.val hleg (List.ofFn y) (List.ofFn x)
    (by simp) (by simpa using v.isLt) ?_ ?_ C.output hout
  · simp [List.getD_eq_getElem?_getD, List.getElem?_ofFn, v.isLt, hy]
  · intro i hiv
    by_cases hn : i < n
    · simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, hn, dite_true,
        Option.getD_some]
      rw [hxy ⟨i, hn⟩ (by intro e; apply hiv; exact congrArg Fin.val e)]
      exact id
    · rw [List.getD_eq_default _ _ (by simp; omega)]
      simp


def petersen (x : Fin 10 → Bool) : Bool :=
  x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
  x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 4 && x 9 ||
  x 5 && x 7 || x 7 && x 9 || x 9 && x 6 || x 6 && x 8 || x 8 && x 5

def neighbor : Fin 10 → Fin 10 := ![1, 0, 1, 2, 3, 0, 1, 2, 3, 4]

lemma petersen_witness (v : Fin 10) :
    (fun i => decide (i = v ∨ i = neighbor v)) v = true ∧
    (∀ i, i ≠ v → decide (i = neighbor v) = decide (i = v ∨ i = neighbor v)) ∧
    petersen (fun i => decide (i = neighbor v)) = false ∧
    petersen (fun i => decide (i = v ∨ i = neighbor v)) = true := by
  have all : ∀ v : Fin 10,
      (fun i => decide (i = v ∨ i = neighbor v)) v = true ∧
      (∀ i, i ≠ v → decide (i = neighbor v) = decide (i = v ∨ i = neighbor v)) ∧
      petersen (fun i => decide (i = neighbor v)) = false ∧
      petersen (fun i => decide (i = v ∨ i = neighbor v)) = true := by decide
  exact all v

lemma petersen_singleton (v : Fin 10) : petersen (fun i => decide (i = v)) = false := by
  have all : ∀ v : Fin 10, petersen (fun i => decide (i = v)) = false := by decide
  exact all v

lemma not_input_cannot_compute_petersen (C : Circuit) (v : Fin 10)
    (hleg : ∀ g ∈ C.gates, (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧
      (g.op = .not → g.inputs.head? = some v.val) ∧
      (g.op = .and ∨ g.op = .or → v.val ∉ g.inputs)) :
    ¬ ∀ x : Fin 10 → Bool, C.eval (List.ofFn x) = petersen x := by
  intro computes
  have hout : C.output ≠ v.val := by
    intro out
    have computed := computes (fun i => decide (i = v))
    change (wf C.gates (List.ofFn (fun i => decide (i = v)))).getD C.output false = _ at computed
    rw [out, wf_fixed_input _ _ _ (by simpa using v.isLt)] at computed
    simp [List.getD_eq_getElem?_getD, List.getElem?_ofFn, v.isLt, petersen_singleton] at computed
  obtain ⟨atV, others, negative, positive⟩ := petersen_witness v
  have transfer := not_input_eval_antitone C 10 v hleg
    (fun i => decide (i = neighbor v)) (fun i => decide (i = v ∨ i = neighbor v))
    atV others hout
  have contradiction := transfer ((computes _).trans positive)
  rw [computes, negative] at contradiction
  cases contradiction


lemma masked_gate_eval (g : Gate) (v u : ℕ) (b : Bool)
    (masked : v ∈ g.inputs → u ∈ g.inputs ∧ g.op = if b then .or else .and)
    (U V : List Bool) (hU : U.getD u false = b) (hV : V.getD u false = b)
    (other : ∀ i, i ≠ v → U.getD i false = V.getD i false) :
    g.op.eval (g.inputs.map fun i => U.getD i false) =
    g.op.eval (g.inputs.map fun i => V.getD i false) := by
  by_cases occurs : v ∈ g.inputs
  · obtain ⟨present, op⟩ := masked occurs
    cases b with
    | false =>
      have uu : (g.inputs.map fun i => U.getD i false).all id = false := by
        apply List.all_eq_false.mpr
        exact ⟨false, List.mem_map.mpr ⟨u, present, hU⟩, rfl⟩
      have vv : (g.inputs.map fun i => V.getD i false).all id = false := by
        apply List.all_eq_false.mpr
        exact ⟨false, List.mem_map.mpr ⟨u, present, hV⟩, rfl⟩
      simpa [op, GateOp.eval, uu, vv]
    | true =>
      have uu : (g.inputs.map fun i => U.getD i false).any id = true := by
        apply List.any_eq_true.mpr
        exact ⟨true, List.mem_map.mpr ⟨u, present, hU⟩, rfl⟩
      have vv : (g.inputs.map fun i => V.getD i false).any id = true := by
        apply List.any_eq_true.mpr
        exact ⟨true, List.mem_map.mpr ⟨u, present, hV⟩, rfl⟩
      simpa [op, GateOp.eval, uu, vv]
  · congr 1
    apply List.map_congr_left
    intro i hi
    exact other i (by intro eq; subst i; exact occurs hi)

lemma masked_wf_eq (gs : List Gate) (v u : ℕ) (b : Bool)
    (masked : ∀ g ∈ gs, v ∈ g.inputs → u ∈ g.inputs ∧ g.op = if b then .or else .and) :
    ∀ U V : List Bool, U.length = V.length → u < U.length →
      U.getD u false = b → V.getD u false = b →
      (∀ i, i ≠ v → U.getD i false = V.getD i false) →
      ∀ i, i ≠ v → (wf gs U).getD i false = (wf gs V).getD i false := by
  induction gs with
  | nil => intro U V _ _ _ _ h i hi; exact h i hi
  | cons g gs ih =>
    intro U V hlen hu hU hV h i hi
    have step := masked_gate_eval g v u b (masked g (by simp)) U V hU hV h
    have next := ih (fun g' hg' => masked g' (by simp [hg']))
      (U ++ [g.op.eval (g.inputs.map fun j => U.getD j false)])
      (V ++ [g.op.eval (g.inputs.map fun j => V.getD j false)])
      (by simp [hlen]) (by simp; omega)
      (by rw [getD_snoc_lt _ _ _ hu]; exact hU)
      (by rw [getD_snoc_lt _ _ _ (by omega)]; exact hV)
      (by
        intro t ht
        rcases Nat.lt_trichotomy t U.length with lt | eq | gt
        · rw [getD_snoc_lt _ _ _ lt, getD_snoc_lt _ _ _ (by omega)]
          exact h t ht
        · subst t
          rw [getD_snoc_eq]
          have e := getD_snoc_eq V (g.op.eval (g.inputs.map fun j => V.getD j false))
          rw [← hlen] at e
          rw [e]
          exact step
        · rw [getD_snoc_gt _ _ _ gt, getD_snoc_gt _ _ _ (by omega)]) i hi
    simpa [wf] using next

lemma masked_petersen_witness (v u : Fin 10) (distinct : v ≠ u) (b : Bool) :
    ∃ x : Fin 10 → Bool, x u = b ∧ petersen x = false ∧
      petersen (Function.update x v true) = true := by
  have allCases : ∀ (v u : Fin 10), v ≠ u → ∀ b : Bool, ∃ w : Fin 10,
      let x := fun i => if b then decide (i = u ∨ i = w) else decide (i = w)
      x u = b ∧ petersen x = false ∧ petersen (Function.update x v true) = true := by decide
  obtain ⟨w, hw⟩ := allCases v u distinct b
  exact ⟨_, hw⟩

lemma primary_mask_cannot_compute_petersen (C : Circuit) (v u : Fin 10)
    (distinct : v ≠ u) (b : Bool)
    (masked : ∀ g ∈ C.gates, v.val ∈ g.inputs →
      u.val ∈ g.inputs ∧ g.op = if b then .or else .and) :
    ¬ ∀ x : Fin 10 → Bool, C.eval (List.ofFn x) = petersen x := by
  intro computes
  have hout : C.output ≠ v.val := by
    intro out
    have computed := computes (fun i => decide (i = v))
    change (wf C.gates (List.ofFn (fun i => decide (i = v)))).getD C.output false = _ at computed
    rw [out, wf_fixed_input _ _ _ (by simpa using v.isLt)] at computed
    simp [List.getD_eq_getElem?_getD, List.getElem?_ofFn, v.isLt, petersen_singleton] at computed
  obtain ⟨x, hu, hx, hy⟩ := masked_petersen_witness v u distinct b
  have agree := masked_wf_eq C.gates v.val u.val b masked
    (List.ofFn x) (List.ofFn (Function.update x v true))
    (by simp) (by simpa using u.isLt)
    (by simp [List.getD_eq_getElem?_getD, List.getElem?_ofFn, u.isLt, hu])
    (by simp [List.getD_eq_getElem?_getD, List.getElem?_ofFn, u.isLt,
      Function.update_of_ne (Ne.symm distinct), hu])
    (by
      intro i hiv
      by_cases hn : i < 10
      · simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, hn, dite_true,
          Option.getD_some]
        rw [Function.update_of_ne (by intro eq; apply hiv; exact congrArg Fin.val eq)]
      · rw [List.getD_eq_default _ _ (by simp; omega),
          List.getD_eq_default _ _ (by simp; omega)]) C.output hout
  change C.eval (List.ofFn x) = C.eval (List.ofFn (Function.update x v true)) at agree
  rw [computes, computes, hx, hy] at agree
  cases agree

end PEqualNP.Outside.L_meta_2592_aux.LeanRoute
