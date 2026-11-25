import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3451_aux.Surgery

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma fold_length (gs : List Gate) (w : List Bool) :
    (gs.foldl step w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [step]
    omega

def oldCircuit (n : ℕ) (gs : List Gate) (a b c d : ℕ) : Circuit :=
  ⟨gs ++ [⟨.and, [a, b]⟩, ⟨.or, [c, d]⟩,
    ⟨.and, [n + gs.length, n + gs.length + 1]⟩], n + gs.length + 2⟩

def newCircuit (n : ℕ) (gs : List Gate) (a b c d : ℕ) : Circuit :=
  ⟨gs ++ [⟨.and, [c, b]⟩, ⟨.and, [d, a]⟩,
    ⟨.or, [n + gs.length, n + gs.length + 1]⟩], n + gs.length + 2⟩

lemma equal_size (n : ℕ) (gs : List Gate) (a b c d : ℕ) :
    (newCircuit n gs a b c d).size = (oldCircuit n gs a b c d).size := by
  simp [newCircuit, oldCircuit, Circuit.size]

lemma bool_split : ∀ a b c d : Bool, (c = true → a = true) → (d = true → b = true) →
    ((a && b) && (c || d)) = ((c && b) || (d && a)) := by
  decide

lemma run_three (w : List Bool) (a b c d : ℕ)
    (_ha : a < w.length) (_hb : b < w.length) (hc : c < w.length) (hd : d < w.length)
    (op0 op1 op2 : GateOp) :
    (([⟨op0, [a, b]⟩, ⟨op1, [c, d]⟩,
      ⟨op2, [w.length, w.length + 1]⟩] : List Gate).foldl step w).getD
      (w.length + 2) false =
    op2.eval [op0.eval [w.getD a false, w.getD b false],
      op1.eval [w.getD c false, w.getD d false]] := by
  let A := op0.eval [w.getD a false, w.getD b false]
  let B := op1.eval [w.getD c false, w.getD d false]
  have h0 : step w ⟨op0, [a, b]⟩ = w ++ [A] := rfl
  have h1 : step (w ++ [A]) ⟨op1, [c, d]⟩ = w ++ [A, B] := by
    simp only [step, List.map_cons, List.map_nil,
      List.getD_append _ _ _ _ hc, List.getD_append _ _ _ _ hd]
    simp [B, List.append_assoc]
  have h2 : step (w ++ [A, B]) ⟨op2, [w.length, w.length + 1]⟩ =
      w ++ [A, B, op2.eval [A, B]] := by
    simp [step, List.getD_eq_getElem?_getD, List.append_assoc]
  simp only [List.foldl_cons, List.foldl_nil, h0, h1, h2]
  simp [List.getD_eq_getElem?_getD, A, B]

lemma output_old (n : ℕ) (gs : List Gate) (a b c d : ℕ)
    (ha : a < n + gs.length) (hb : b < n + gs.length)
    (hc : c < n + gs.length) (hd : d < n + gs.length) (x : Fin n → Bool) :
    circuitFun n (oldCircuit n gs a b c d) x =
      (((( ⟨gs, 0⟩ : Circuit).wires (List.ofFn x)).getD a false &&
        ((⟨gs, 0⟩ : Circuit).wires (List.ofFn x)).getD b false) &&
      (((⟨gs, 0⟩ : Circuit).wires (List.ofFn x)).getD c false ||
        ((⟨gs, 0⟩ : Circuit).wires (List.ofFn x)).getD d false)) := by
  let w := gs.foldl step (List.ofFn x)
  have hw : w.length = n + gs.length := by simp [w, fold_length]
  have h := run_three w a b c d (by omega) (by omega) (by omega) (by omega)
    GateOp.and GateOp.or GateOp.and
  rw [hw] at h
  change ((gs ++ ([⟨.and, [a, b]⟩, ⟨.or, [c, d]⟩,
    ⟨.and, [n + gs.length, n + gs.length + 1]⟩] : List Gate)).foldl step (List.ofFn x)).getD
    (n + gs.length + 2) false = ((w.getD a false && w.getD b false) &&
      (w.getD c false || w.getD d false))
  rw [List.foldl_append]
  simpa only [GateOp.eval, List.all_cons, List.all_nil, List.any_cons, List.any_nil,
    id_eq, Bool.and_true, Bool.or_false] using h

lemma output_new (n : ℕ) (gs : List Gate) (a b c d : ℕ)
    (ha : a < n + gs.length) (hb : b < n + gs.length)
    (hc : c < n + gs.length) (hd : d < n + gs.length) (x : Fin n → Bool) :
    circuitFun n (newCircuit n gs a b c d) x =
      (((( ⟨gs, 0⟩ : Circuit).wires (List.ofFn x)).getD c false &&
        ((⟨gs, 0⟩ : Circuit).wires (List.ofFn x)).getD b false) ||
      (((⟨gs, 0⟩ : Circuit).wires (List.ofFn x)).getD d false &&
        ((⟨gs, 0⟩ : Circuit).wires (List.ofFn x)).getD a false)) := by
  let w := gs.foldl step (List.ofFn x)
  have hw : w.length = n + gs.length := by simp [w, fold_length]
  have h := run_three w c b d a (by omega) (by omega) (by omega) (by omega)
    GateOp.and GateOp.and GateOp.or
  rw [hw] at h
  change ((gs ++ ([⟨.and, [c, b]⟩, ⟨.and, [d, a]⟩,
    ⟨.or, [n + gs.length, n + gs.length + 1]⟩] : List Gate)).foldl step (List.ofFn x)).getD
    (n + gs.length + 2) false = ((w.getD c false && w.getD b false) ||
      (w.getD d false && w.getD a false))
  rw [List.foldl_append]
  simpa only [GateOp.eval, List.all_cons, List.all_nil, List.any_cons, List.any_nil,
    id_eq, Bool.and_true, Bool.or_false] using h

lemma same_function (n : ℕ) (gs : List Gate) (a b c d : ℕ)
    (ha : a < n + gs.length) (hb : b < n + gs.length)
    (hc : c < n + gs.length) (hd : d < n + gs.length)
    (hca : ∀ x : Fin n → Bool,
      ((⟨gs, 0⟩ : Circuit).wires (List.ofFn x)).getD c false = true →
      ((⟨gs, 0⟩ : Circuit).wires (List.ofFn x)).getD a false = true)
    (hdb : ∀ x : Fin n → Bool,
      ((⟨gs, 0⟩ : Circuit).wires (List.ofFn x)).getD d false = true →
      ((⟨gs, 0⟩ : Circuit).wires (List.ofFn x)).getD b false = true) :
    circuitFun n (newCircuit n gs a b c d) = circuitFun n (oldCircuit n gs a b c d) := by
  funext x
  rw [output_new n gs a b c d ha hb hc hd x, output_old n gs a b c d ha hb hc hd x]
  exact (bool_split _ _ _ _ (hca x) (hdb x)).symm

lemma monotone_models (n : ℕ) (gs : List Gate) (a b c d : ℕ)
    (hm : Monotone2 (⟨gs, 0⟩ : Circuit)) :
    Monotone2 (oldCircuit n gs a b c d) ∧ Monotone2 (newCircuit n gs a b c d) := by
  constructor
  · intro g hg
    simp [oldCircuit] at hg
    rcases hg with hg | rfl | rfl | rfl
    · exact hm g hg
    all_goals simp
  · intro g hg
    simp [newCircuit] at hg
    rcases hg with hg | rfl | rfl | rfl
    · exact hm g hg
    all_goals simp

lemma readsBack_snoc (n : ℕ) (gs : List Gate) (g : Gate) (out : ℕ)
    (hback : ReadsBack n (⟨gs, 0⟩ : Circuit))
    (hg : ∀ i ∈ g.inputs, i < n + gs.length) :
    ReadsBack n (⟨gs ++ [g], out⟩ : Circuit) := by
  intro j hj i hi
  by_cases hlt : j < gs.length
  · have he : gateAt (⟨gs ++ [g], out⟩ : Circuit) j = gateAt (⟨gs, 0⟩ : Circuit) j := by
      exact List.getD_append _ _ _ _ hlt
    rw [he] at hi
    exact hback j hlt i hi
  · have heq : j = gs.length := by
      change j < (gs ++ [g]).length at hj
      simp only [List.length_append, List.length_singleton] at hj
      omega
    subst j
    have he : gateAt (⟨gs ++ [g], out⟩ : Circuit) gs.length = g := by
      simp [gateAt, List.getD_eq_getElem?_getD]
    rw [he] at hi
    exact hg i hi

lemma back_models (n : ℕ) (gs : List Gate) (a b c d : ℕ)
    (ha : a < n + gs.length) (hb : b < n + gs.length)
    (hc : c < n + gs.length) (hd : d < n + gs.length)
    (hback : ReadsBack n (⟨gs, 0⟩ : Circuit)) :
    ReadsBack n (oldCircuit n gs a b c d) ∧ ReadsBack n (newCircuit n gs a b c d) := by
  have first (u v : ℕ) (hu : u < n + gs.length) (hv : v < n + gs.length) (op : GateOp) :
      ReadsBack n (⟨gs ++ [⟨op, [u, v]⟩], 0⟩ : Circuit) := by
    apply readsBack_snoc n gs _ 0 hback
    intro i hi
    simp at hi
    rcases hi with rfl | rfl <;> assumption
  have three (u v r s : ℕ) (hu : u < n + gs.length) (hv : v < n + gs.length)
      (hr : r < n + gs.length) (hs : s < n + gs.length) (op0 op1 op2 : GateOp) :
      ReadsBack n (⟨gs ++ [⟨op0, [u, v]⟩, ⟨op1, [r, s]⟩,
        ⟨op2, [n + gs.length, n + gs.length + 1]⟩], n + gs.length + 2⟩ : Circuit) := by
    have h0 := first u v hu hv op0
    have h1 : ReadsBack n (⟨(gs ++ [⟨op0, [u, v]⟩]) ++ [⟨op1, [r, s]⟩], 0⟩ : Circuit) := by
      apply readsBack_snoc n _ _ 0 h0
      intro i hi
      simp at hi
      simp only [List.length_append, List.length_singleton]
      rcases hi with rfl | rfl <;> omega
    have h2 := readsBack_snoc n _ ⟨op2, [n + gs.length, n + gs.length + 1]⟩
      (n + gs.length + 2) h1 (by
        intro i hi
        simp at hi
        simp only [List.length_append, List.length_singleton]
        rcases hi with rfl | rfl <;> omega)
    simpa only [List.append_assoc, List.cons_append, List.nil_append] using h2
  exact ⟨three a b c d ha hb hc hd .and .or .and,
    three c b d a hc hb hd ha .and .and .or⟩

lemma run_three_wires (w : List Bool) (a b c d : ℕ)
    (hc : c < w.length) (hd : d < w.length) (op0 op1 op2 : GateOp) :
    ([⟨op0, [a, b]⟩, ⟨op1, [c, d]⟩,
      ⟨op2, [w.length, w.length + 1]⟩] : List Gate).foldl step w =
    w ++ [op0.eval [w.getD a false, w.getD b false],
      op1.eval [w.getD c false, w.getD d false],
      op2.eval [op0.eval [w.getD a false, w.getD b false],
        op1.eval [w.getD c false, w.getD d false]]] := by
  let A := op0.eval [w.getD a false, w.getD b false]
  let B := op1.eval [w.getD c false, w.getD d false]
  have h0 : step w ⟨op0, [a, b]⟩ = w ++ [A] := rfl
  have h1 : step (w ++ [A]) ⟨op1, [c, d]⟩ = w ++ [A, B] := by
    simp only [step, List.map_cons, List.map_nil,
      List.getD_append _ _ _ _ hc, List.getD_append _ _ _ _ hd]
    simp [B, List.append_assoc]
  have h2 : step (w ++ [A, B]) ⟨op2, [w.length, w.length + 1]⟩ =
      w ++ [A, B, op2.eval [A, B]] := by
    simp [step, List.getD_eq_getElem?_getD, List.append_assoc]
  simp only [List.foldl_cons, List.foldl_nil, h0, h1, h2]
  rfl

lemma wires_new (n : ℕ) (gs : List Gate) (a b c d : ℕ)
    (ha : a < n + gs.length) (hd : d < n + gs.length) (x : Fin n → Bool) :
    let w := (⟨gs, 0⟩ : Circuit).wires (List.ofFn x)
    (newCircuit n gs a b c d).wires (List.ofFn x) =
      w ++ [w.getD c false && w.getD b false, w.getD d false && w.getD a false,
        (w.getD c false && w.getD b false) || (w.getD d false && w.getD a false)] := by
  let w := gs.foldl step (List.ofFn x)
  have hw : w.length = n + gs.length := by simp [w, fold_length]
  have h := run_three_wires w c b d a (by omega) (by omega)
    GateOp.and GateOp.and GateOp.or
  rw [hw] at h
  change (gs ++ ([⟨.and, [c, b]⟩, ⟨.and, [d, a]⟩,
    ⟨.or, [n + gs.length, n + gs.length + 1]⟩] : List Gate)).foldl step (List.ofFn x) =
    w ++ [w.getD c false && w.getD b false, w.getD d false && w.getD a false,
      (w.getD c false && w.getD b false) || (w.getD d false && w.getD a false)]
  rw [List.foldl_append]
  simpa only [GateOp.eval, List.all_cons, List.all_nil, List.any_cons, List.any_nil,
    id_eq, Bool.and_true, Bool.or_false] using h

lemma fold_early (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl step w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [List.foldl_cons]
    rw [ih (step w g) (by simp [step]; omega)]
    exact List.getD_append _ _ _ _ hi

lemma prefix_wire_new (n : ℕ) (gs : List Gate) (a b c d w : ℕ)
    (hw : w < n + gs.length) (x : Fin n → Bool) :
    ((newCircuit n gs a b c d).wires (List.ofFn x)).getD w false =
      ((⟨gs, 0⟩ : Circuit).wires (List.ofFn x)).getD w false := by
  change ((gs ++ ([⟨.and, [c, b]⟩, ⟨.and, [d, a]⟩,
    ⟨.or, [n + gs.length, n + gs.length + 1]⟩] : List Gate)).foldl step (List.ofFn x)).getD
    w false = (gs.foldl step (List.ofFn x)).getD w false
  rw [List.foldl_append]
  apply fold_early
  simpa [fold_length] using hw

lemma suffix_below_new_output (n : ℕ) (gs : List Gate) (a b c d : ℕ)
    (ha : a < n + gs.length) (hb : b < n + gs.length)
    (hc : c < n + gs.length) (hd : d < n + gs.length)
    (j : ℕ) (hge : gs.length ≤ j) (hj : j < (newCircuit n gs a b c d).gates.length)
    (hand : (gateAt (newCircuit n gs a b c d) j).op = GateOp.and)
    (x : Fin n → Bool)
    (ht : ((newCircuit n gs a b c d).wires (List.ofFn x)).getD (n + j) false = true) :
    circuitFun n (newCircuit n gs a b c d) x = true := by
  have hj' : j = gs.length ∨ j = gs.length + 1 ∨ j = gs.length + 2 := by
    simp only [newCircuit, List.length_append, List.length_cons, List.length_nil] at hj
    omega
  have hw : ((⟨gs, 0⟩ : Circuit).wires (List.ofFn x)).length = n + gs.length := by
    exact (fold_length gs (List.ofFn x)).trans (by simp)
  rw [output_new n gs a b c d ha hb hc hd x]
  rw [wires_new n gs a b c d ha hd x] at ht
  rcases hj' with rfl | rfl | rfl
  · have hA : (((⟨gs, 0⟩ : Circuit).wires (List.ofFn x)).getD c false &&
        ((⟨gs, 0⟩ : Circuit).wires (List.ofFn x)).getD b false) = true := by
      simpa [← hw, List.getD_eq_getElem?_getD] using ht
    rw [hA]
    rfl
  · have hB : (((⟨gs, 0⟩ : Circuit).wires (List.ofFn x)).getD d false &&
        ((⟨gs, 0⟩ : Circuit).wires (List.ofFn x)).getD a false) = true := by
      simpa [← Nat.add_assoc, ← hw, List.getD_eq_getElem?_getD] using ht
    rw [hB]
    exact Bool.or_true _
  · have ho : (gateAt (newCircuit n gs a b c d) (gs.length + 2)).op = GateOp.or := by
      simp [gateAt, newCircuit, List.getD_eq_getElem?_getD]
    rw [ho] at hand
    cases hand

lemma clean_new (n : ℕ) (gs : List Gate) (a b c d : ℕ)
    (ha : a < n + gs.length) (hb : b < n + gs.length)
    (hc : c < n + gs.length) (hd : d < n + gs.length)
    (F : (Fin n → Bool) → Bool)
    (hprefix : ∀ j < gs.length, (gateAt (⟨gs, 0⟩ : Circuit) j).op = GateOp.and →
      ∀ x : Fin n → Bool, F x = false →
        ((⟨gs, 0⟩ : Circuit).wires (List.ofFn x)).getD (n + j) false = false)
    (houtput : ∀ x : Fin n → Bool, circuitFun n (newCircuit n gs a b c d) x = F x) :
    ∀ j < (newCircuit n gs a b c d).gates.length,
      (gateAt (newCircuit n gs a b c d) j).op = GateOp.and →
      ∀ x : Fin n → Bool, F x = false →
        ((newCircuit n gs a b c d).wires (List.ofFn x)).getD (n + j) false = false := by
  intro j hj hand x hx
  by_cases hp : j < gs.length
  · have hgate : gateAt (newCircuit n gs a b c d) j = gateAt (⟨gs, 0⟩ : Circuit) j :=
      List.getD_append _ _ _ _ hp
    rw [hgate] at hand
    rw [prefix_wire_new n gs a b c d (n + j) (by omega) x]
    exact hprefix j hp hand x hx
  · cases hv : ((newCircuit n gs a b c d).wires (List.ofFn x)).getD (n + j) false with
    | false => rfl
    | true =>
      have h := suffix_below_new_output n gs a b c d ha hb hc hd j (by omega) hj hand x hv
      rw [houtput x, hx] at h
      cases h

lemma normalizes_suffix (n : ℕ) (gs : List Gate) (a b c d : ℕ)
    (ha : a < n + gs.length) (hb : b < n + gs.length)
    (hc : c < n + gs.length) (hd : d < n + gs.length)
    (hm : Monotone2 (⟨gs, 0⟩ : Circuit)) (hr : ReadsBack n (⟨gs, 0⟩ : Circuit))
    (hca : ∀ x : Fin n → Bool,
      ((⟨gs, 0⟩ : Circuit).wires (List.ofFn x)).getD c false = true →
      ((⟨gs, 0⟩ : Circuit).wires (List.ofFn x)).getD a false = true)
    (hdb : ∀ x : Fin n → Bool,
      ((⟨gs, 0⟩ : Circuit).wires (List.ofFn x)).getD d false = true →
      ((⟨gs, 0⟩ : Circuit).wires (List.ofFn x)).getD b false = true)
    (hprefix : ∀ j < gs.length, (gateAt (⟨gs, 0⟩ : Circuit) j).op = GateOp.and →
      ∀ x : Fin n → Bool, circuitFun n (oldCircuit n gs a b c d) x = false →
        ((⟨gs, 0⟩ : Circuit).wires (List.ofFn x)).getD (n + j) false = false) :
    Monotone2 (newCircuit n gs a b c d) ∧ ReadsBack n (newCircuit n gs a b c d) ∧
    (newCircuit n gs a b c d).size = (oldCircuit n gs a b c d).size ∧
    circuitFun n (newCircuit n gs a b c d) = circuitFun n (oldCircuit n gs a b c d) ∧
    ∀ j < (newCircuit n gs a b c d).gates.length,
      (gateAt (newCircuit n gs a b c d) j).op = GateOp.and →
      ∀ x : Fin n → Bool, circuitFun n (oldCircuit n gs a b c d) x = false →
        ((newCircuit n gs a b c d).wires (List.ofFn x)).getD (n + j) false = false := by
  have hf := same_function n gs a b c d ha hb hc hd hca hdb
  refine ⟨(monotone_models n gs a b c d hm).2, (back_models n gs a b c d ha hb hc hd hr).2,
    equal_size n gs a b c d, hf, ?_⟩
  exact clean_new n gs a b c d ha hb hc hd _ hprefix (fun x => congrFun hf x)

lemma bool_split_on_false : ∀ a b c d : Bool,
    (((a && b) && (c || d)) = false → c = true → a = true) →
    (((a && b) && (c || d)) = false → d = true → b = true) →
    ((a && b) && (c || d)) = ((c && b) || (d && a)) := by
  decide

lemma same_function_on_false (n : ℕ) (gs : List Gate) (a b c d : ℕ)
    (ha : a < n + gs.length) (hb : b < n + gs.length)
    (hc : c < n + gs.length) (hd : d < n + gs.length)
    (hca : ∀ x : Fin n → Bool, circuitFun n (oldCircuit n gs a b c d) x = false →
      ((⟨gs, 0⟩ : Circuit).wires (List.ofFn x)).getD c false = true →
      ((⟨gs, 0⟩ : Circuit).wires (List.ofFn x)).getD a false = true)
    (hdb : ∀ x : Fin n → Bool, circuitFun n (oldCircuit n gs a b c d) x = false →
      ((⟨gs, 0⟩ : Circuit).wires (List.ofFn x)).getD d false = true →
      ((⟨gs, 0⟩ : Circuit).wires (List.ofFn x)).getD b false = true) :
    circuitFun n (newCircuit n gs a b c d) = circuitFun n (oldCircuit n gs a b c d) := by
  funext x
  rw [output_new n gs a b c d ha hb hc hd x, output_old n gs a b c d ha hb hc hd x]
  symm
  apply bool_split_on_false
  · intro hf ht
    exact hca x ((output_old n gs a b c d ha hb hc hd x).trans hf) ht
  · intro hf ht
    exact hdb x ((output_old n gs a b c d ha hb hc hd x).trans hf) ht

lemma normalizes_suffix_on_false (n : ℕ) (gs : List Gate) (a b c d : ℕ)
    (ha : a < n + gs.length) (hb : b < n + gs.length)
    (hc : c < n + gs.length) (hd : d < n + gs.length)
    (hm : Monotone2 (⟨gs, 0⟩ : Circuit)) (hr : ReadsBack n (⟨gs, 0⟩ : Circuit))
    (hca : ∀ x : Fin n → Bool, circuitFun n (oldCircuit n gs a b c d) x = false →
      ((⟨gs, 0⟩ : Circuit).wires (List.ofFn x)).getD c false = true →
      ((⟨gs, 0⟩ : Circuit).wires (List.ofFn x)).getD a false = true)
    (hdb : ∀ x : Fin n → Bool, circuitFun n (oldCircuit n gs a b c d) x = false →
      ((⟨gs, 0⟩ : Circuit).wires (List.ofFn x)).getD d false = true →
      ((⟨gs, 0⟩ : Circuit).wires (List.ofFn x)).getD b false = true)
    (hprefix : ∀ j < gs.length, (gateAt (⟨gs, 0⟩ : Circuit) j).op = GateOp.and →
      ∀ x : Fin n → Bool, circuitFun n (oldCircuit n gs a b c d) x = false →
        ((⟨gs, 0⟩ : Circuit).wires (List.ofFn x)).getD (n + j) false = false) :
    Monotone2 (newCircuit n gs a b c d) ∧ ReadsBack n (newCircuit n gs a b c d) ∧
    (newCircuit n gs a b c d).size = (oldCircuit n gs a b c d).size ∧
    circuitFun n (newCircuit n gs a b c d) = circuitFun n (oldCircuit n gs a b c d) ∧
    ∀ j < (newCircuit n gs a b c d).gates.length,
      (gateAt (newCircuit n gs a b c d) j).op = GateOp.and →
      ∀ x : Fin n → Bool, circuitFun n (oldCircuit n gs a b c d) x = false →
        ((newCircuit n gs a b c d).wires (List.ofFn x)).getD (n + j) false = false := by
  have hf := same_function_on_false n gs a b c d ha hb hc hd hca hdb
  refine ⟨(monotone_models n gs a b c d hm).2, (back_models n gs a b c d ha hb hc hd hr).2,
    equal_size n gs a b c d, hf, ?_⟩
  exact clean_new n gs a b c d ha hb hc hd _ hprefix (fun x => congrFun hf x)

end PEqualNP.Outside.L_meta_3451_aux.Surgery
