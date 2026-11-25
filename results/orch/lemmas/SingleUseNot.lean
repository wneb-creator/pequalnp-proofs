import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_10760_aux.SingleUseFactors

def binary (d a b : Bool) : Bool := if d then a || b else a && b

lemma partner_value (d a : Bool) (H : Bool → Bool)
    (diff : H (binary d false a) ≠ H (binary d true a)) : a = !d := by
  cases d <;> cases a <;> simp [binary] at *

def target (x : Fin 7 → Bool) : Bool :=
  (x 0 && x 2) || (x 1 && x 3) || (x 0 && x 4) || (x 1 && x 4) ||
  (x 2 && x 4) || (x 0 && x 5) || (x 1 && x 5) || (x 3 && x 5) ||
  (x 0 && x 6) || (x 2 && x 6) || (x 3 && x 6) || (x 5 && x 6)

def point (b : Fin 128) (i : Fin 7) : Bool := b.val.testBit i.val

def force (i : Fin 7) (x : Fin 7 → Bool) : Fin 7 → Bool :=
  fun j => if j = i then true else x j

def critical (i j : Fin 7) (d : Bool) (b : Fin 128) : Prop :=
  point b i = false ∧ target (point b) = false ∧
    target (force i (point b)) = true ∧ point b j = d

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
lemma critical_exists : ∀ (i j : Fin 7) (d : Bool), i ≠ j →
    ∃ b : Fin 128, critical i j d b := by
  unfold critical
  decide +kernel

lemma no_raw_partner (i j : Fin 7) (ne : i ≠ j) (d : Bool)
    (K : Bool → (Fin 7 → Bool) → Bool)
    (blind : ∀ z x, K z (force i x) = K z x)
    (factor : ∀ x, target x = K (binary d (x i) (x j)) x) : False := by
  obtain ⟨b, hi, low, high, hj⟩ := critical_exists i j d ne
  have ji : j ≠ i := Ne.symm ne
  have same : binary d (force i (point b) i) (force i (point b) j) =
      binary d (point b i) (point b j) := by
    cases d <;> simp [binary, force, ji, hi, hj]
  have eq : target (force i (point b)) = target (point b) := by
    rw [factor, factor, same, blind]
  rw [high, low] at eq
  contradiction

end PEqualNP.Outside.L_meta_10760_aux.SingleUseFactors

namespace PEqualNP.Outside.L_meta_10760_aux.SingleUseCircuit

open PEqualNP.CircuitLowerBounds

def binaryOp (d : Bool) : GateOp := if d then .or else .and

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun k => w.getD k false)]

lemma getD_snoc_ne (w : List Bool) (v : Bool) (k : ℕ) (ne : k ≠ w.length) :
    (w ++ [v]).getD k false = w.getD k false := by
  by_cases lt : k < w.length
  · exact List.getD_append _ _ _ _ lt
  · rw [List.getD_eq_default _ _ (by simp; omega),
      List.getD_eq_default _ _ (by omega)]

lemma snoc_agree (i : ℕ) (w w' : List Bool) (v : Bool)
    (len : w.length = w'.length)
    (agree : ∀ k, k ≠ i → w.getD k false = w'.getD k false) :
    ∀ k, k ≠ i → (w ++ [v]).getD k false = (w' ++ [v]).getD k false := by
  intro k ki
  by_cases eq : k = w.length
  · subst k
    simp [len]
  · rw [getD_snoc_ne w v k eq, getD_snoc_ne w' v k (by omega)]
    exact agree k ki

lemma gate_agree (i j : ℕ) (d : Bool) (g : Gate) (w w' : List Bool)
    (spec : i ∈ g.inputs → g.op = binaryOp d ∧
      (g.inputs = [i, j] ∨ g.inputs = [j, i]))
    (left : w.getD j false = d) (right : w'.getD j false = d)
    (agree : ∀ k, k ≠ i → w.getD k false = w'.getD k false) :
    g.op.eval (g.inputs.map fun k => w.getD k false) =
      g.op.eval (g.inputs.map fun k => w'.getD k false) := by
  by_cases reads : i ∈ g.inputs
  · obtain ⟨op, args | args⟩ := spec reads
    · simp only [List.getD_eq_getElem?_getD] at left right
      cases d <;> simp [op, args, binaryOp, GateOp.eval, left, right]
    · simp only [List.getD_eq_getElem?_getD] at left right
      cases d <;> simp [op, args, binaryOp, GateOp.eval, left, right]
  · apply congrArg g.op.eval
    apply List.map_congr_left
    intro k hk
    exact agree k (fun eq => reads (eq ▸ hk))

lemma fold_agree (i j : ℕ) (d : Bool) : ∀ (gs : List Gate),
    (∀ g ∈ gs, i ∈ g.inputs → g.op = binaryOp d ∧
      (g.inputs = [i, j] ∨ g.inputs = [j, i])) →
    ∀ (w w' : List Bool), w.length = w'.length → j < w.length →
      w.getD j false = d → w'.getD j false = d →
      (∀ k, k ≠ i → w.getD k false = w'.getD k false) →
      ∀ o, o ≠ i →
        (gs.foldl step w).getD o false = (gs.foldl step w').getD o false := by
  intro gs
  induction gs with
  | nil => intro _ w w' _ _ _ _ agree; exact agree
  | cons g gs ih =>
    intro spec w w' len lt left right agree
    have val := gate_agree i j d g w w' (spec g (by simp)) left right agree
    apply ih (fun g hg => spec g (by simp [hg])) (step w g) (step w' g)
    · simp [step, len]
    · simp only [step, List.length_append, List.length_singleton]; omega
    · exact (List.getD_append _ _ _ _ lt).trans left
    · exact (List.getD_append _ _ _ _ (by omega)).trans right
    · unfold step
      rw [val]
      exact snoc_agree i w w' _ len agree

lemma eval_agree (gs : List Gate) (o i j : ℕ) (d : Bool) (w w' : List Bool)
    (spec : ∀ g ∈ gs, i ∈ g.inputs → g.op = binaryOp d ∧
      (g.inputs = [i, j] ∨ g.inputs = [j, i]))
    (len : w.length = w'.length) (lt : j < w.length)
    (left : w.getD j false = d) (right : w'.getD j false = d)
    (agree : ∀ k, k ≠ i → w.getD k false = w'.getD k false)
    (output : o ≠ i) : Circuit.eval ⟨gs, o⟩ w = Circuit.eval ⟨gs, o⟩ w' :=
  fold_agree i j d gs spec w w' len lt left right agree o output

end PEqualNP.Outside.L_meta_10760_aux.SingleUseCircuit

namespace PEqualNP.Outside.L_meta_10760_aux.SingleUseBridge

open PEqualNP.CircuitLowerBounds
open PEqualNP.Outside.L_meta_10760_aux.SingleUseFactors
open PEqualNP.Outside.L_meta_10760_aux.SingleUseCircuit

lemma fold_prefix (gs : List Gate) : ∀ (w : List Bool) (k : ℕ), k < w.length →
    (gs.foldl step w).getD k false = w.getD k false := by
  induction gs with
  | nil => intros; rfl
  | cons g gs ih =>
    intro w k lt
    change (gs.foldl step (step w g)).getD k false = w.getD k false
    rw [ih (step w g) k (by simp only [step, List.length_append, List.length_singleton]; omega)]
    exact List.getD_append _ _ _ _ lt

lemma ofFn_get (x : Fin 7 → Bool) (i : Fin 7) :
    (List.ofFn x).getD i.val false = x i := by
  rw [List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn]

lemma eval_input (gs : List Gate) (x : Fin 7 → Bool) (i : Fin 7) :
    Circuit.eval ⟨gs, i.val⟩ (List.ofFn x) = x i := by
  change (gs.foldl step (List.ofFn x)).getD i.val false = x i
  rw [fold_prefix gs (List.ofFn x) i.val (by simp)]
  exact ofFn_get x i

lemma target_not_input (gs : List Gate) (o : ℕ)
    (computes : ∀ x : Fin 7 → Bool, Circuit.eval ⟨gs, o⟩ (List.ofFn x) = target x)
    (i : Fin 7) : o ≠ i.val := by
  intro eq
  subst o
  have singles : ∀ i : Fin 7, target (fun k => decide (k = i)) = false := by
    decide +kernel
  have same := computes (fun k => decide (k = i))
  rw [eval_input, singles i] at same
  simp at same

lemma no_raw_circuit (gs : List Gate) (o : ℕ) (i j : Fin 7)
    (ne : i ≠ j) (d : Bool)
    (spec : ∀ g ∈ gs, i.val ∈ g.inputs → g.op = binaryOp d ∧
      (g.inputs = [i.val, j.val] ∨ g.inputs = [j.val, i.val]))
    (computes : ∀ x : Fin 7 → Bool, Circuit.eval ⟨gs, o⟩ (List.ofFn x) = target x) :
    False := by
  obtain ⟨b, hi, low, high, hj⟩ := critical_exists i j d ne
  have left : (List.ofFn (point b)).getD j.val false = d := by
    rw [ofFn_get]; exact hj
  have right : (List.ofFn (force i (point b))).getD j.val false = d := by
    rw [ofFn_get]
    simpa [force, Ne.symm ne] using hj
  have agree : ∀ k, k ≠ i.val →
      (List.ofFn (point b)).getD k false =
        (List.ofFn (force i (point b))).getD k false := by
    intro k ki
    by_cases small : k < 7
    · have different : (⟨k, small⟩ : Fin 7) ≠ i := by
        intro eq
        have val := congrArg Fin.val eq
        exact ki val
      change (List.ofFn (point b)).getD (⟨k, small⟩ : Fin 7).val false =
        (List.ofFn (force i (point b))).getD (⟨k, small⟩ : Fin 7).val false
      rw [ofFn_get, ofFn_get]
      simp [force, different]
    · rw [List.getD_eq_default _ _ (by simp; omega),
        List.getD_eq_default _ _ (by simp; omega)]
  have same := eval_agree gs o i.val j.val d
    (List.ofFn (point b)) (List.ofFn (force i (point b))) spec
    (by simp) (by simp) left right agree (target_not_input gs o computes i)
  rw [computes, computes, low, high] at same
  contradiction

end PEqualNP.Outside.L_meta_10760_aux.SingleUseBridge

namespace PEqualNP.Outside.L_meta_10760_aux.SingleUseNot

open PEqualNP.CircuitLowerBounds
open PEqualNP.Outside.L_meta_10760_aux.SingleUseCircuit
open PEqualNP.Outside.L_meta_10760_aux.SingleUseFactors
open PEqualNP.Outside.L_meta_10760_aux.SingleUseBridge

def readerShape (i : ℕ) (g : Gate) : Prop :=
  (g.op = .not ∧ ∃ rest, g.inputs = i :: rest) ∨
    ((g.op = .and ∨ g.op = .or) ∧ i ∉ g.inputs)

lemma gate_antitone (i : ℕ) (g : Gate) (w w' : List Bool)
    (shape : readerShape i g) (flipped : w'.getD i false = true)
    (decreases : ∀ k, k ≠ i → w'.getD k false = true → w.getD k false = true) :
    g.op.eval (g.inputs.map fun k => w'.getD k false) = true →
      g.op.eval (g.inputs.map fun k => w.getD k false) = true := by
  intro h
  rcases shape with ⟨op, rest, args⟩ | ⟨op | op, excludes⟩
  · rw [op, args] at h
    change (!(w'.getD i false)) = true at h
    rw [flipped] at h
    contradiction
  · rw [op] at h ⊢
    change (g.inputs.map fun k => w'.getD k false).all id = true at h
    change (g.inputs.map fun k => w.getD k false).all id = true
    apply List.all_eq_true.mpr
    intro v hv
    obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hv
    exact decreases k (fun eq => excludes (eq ▸ hk))
      (List.all_eq_true.mp h _ (List.mem_map.mpr ⟨k, hk, rfl⟩))
  · rw [op] at h ⊢
    change (g.inputs.map fun k => w'.getD k false).any id = true at h
    change (g.inputs.map fun k => w.getD k false).any id = true
    obtain ⟨v, hv, yes⟩ := List.any_eq_true.mp h
    obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hv
    exact List.any_eq_true.mpr ⟨w.getD k false, List.mem_map.mpr ⟨k, hk, rfl⟩,
      decreases k (fun eq => excludes (eq ▸ hk)) yes⟩

lemma snoc_decreases (i : ℕ) (w w' : List Bool) (v v' : Bool)
    (len : w.length = w'.length)
    (decreases : ∀ k, k ≠ i → w'.getD k false = true → w.getD k false = true)
    (value : v' = true → v = true) :
    ∀ k, k ≠ i → (w' ++ [v']).getD k false = true →
      (w ++ [v]).getD k false = true := by
  intro k ki h
  by_cases eq : k = w.length
  · subst k
    simpa [len] using value (by simpa [len] using h)
  · rw [getD_snoc_ne w' v' k (by omega)] at h
    rw [getD_snoc_ne w v k eq]
    exact decreases k ki h

lemma fold_antitone (i : ℕ) : ∀ (gs : List Gate),
    (∀ g ∈ gs, readerShape i g) → ∀ (w w' : List Bool),
      w.length = w'.length → i < w.length → w'.getD i false = true →
      (∀ k, k ≠ i → w'.getD k false = true → w.getD k false = true) →
      ∀ o, o ≠ i → (gs.foldl step w').getD o false = true →
        (gs.foldl step w).getD o false = true := by
  intro gs
  induction gs with
  | nil => intro _ w w' _ _ _ decreases; exact decreases
  | cons g gs ih =>
    intro shape w w' len lt flipped decreases
    apply ih (fun g hg => shape g (by simp [hg])) (step w g) (step w' g)
    · simp [step, len]
    · simp only [step, List.length_append, List.length_singleton]; omega
    · exact (List.getD_append _ _ _ _ (by omega)).trans flipped
    · exact snoc_decreases i w w' _ _ len decreases
        (gate_antitone i g w w' (shape g (by simp)) flipped decreases)

lemma no_not_circuit (gs : List Gate) (o : ℕ) (i : Fin 7)
    (shape : ∀ g ∈ gs, readerShape i.val g)
    (computes : ∀ x : Fin 7 → Bool, Circuit.eval ⟨gs, o⟩ (List.ofFn x) = target x) :
    False := by
  let j : Fin 7 := if i = 0 then 1 else 0
  have ne : i ≠ j := by
    by_cases eq : i = 0
    · simp [j, eq]
    · simpa [j, eq] using eq
  obtain ⟨b, hi, low, high, _⟩ := critical_exists i j false ne
  have flipped : (List.ofFn (force i (point b))).getD i.val false = true := by
    rw [ofFn_get]
    simp [force]
  have decreases : ∀ k, k ≠ i.val →
      (List.ofFn (force i (point b))).getD k false = true →
        (List.ofFn (point b)).getD k false = true := by
    intro k ki h
    by_cases small : k < 7
    · have different : (⟨k, small⟩ : Fin 7) ≠ i := by
        intro eq
        exact ki (congrArg Fin.val eq)
      change (List.ofFn (force i (point b))).getD (⟨k, small⟩ : Fin 7).val false = true at h
      change (List.ofFn (point b)).getD (⟨k, small⟩ : Fin 7).val false = true
      rw [ofFn_get] at h ⊢
      simpa [force, different] using h
    · rw [List.getD_eq_default _ _ (by simp; omega)] at h
      contradiction
  have out : Circuit.eval ⟨gs, o⟩ (List.ofFn (force i (point b))) = true := by
    rw [computes, high]
  have lower := fold_antitone i.val gs shape (List.ofFn (point b))
    (List.ofFn (force i (point b))) (by simp) (by simp) flipped decreases o
    (target_not_input gs o computes i) out
  change Circuit.eval ⟨gs, o⟩ (List.ofFn (point b)) = true at lower
  rw [computes, low] at lower
  contradiction

end PEqualNP.Outside.L_meta_10760_aux.SingleUseNot
