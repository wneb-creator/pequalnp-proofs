import Mathlib
import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_997.Window
open PEqualNP.CircuitLowerBounds
def run (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

lemma run_cons (g : Gate) (gs : List Gate) (x : List Bool) :
    run (g :: gs) x = run gs (x ++ [g.op.eval (g.inputs.map fun i => x.getD i false)]) :=
  rfl

lemma run_length (gs : List Gate) (x : List Bool) :
    (run gs x).length = x.length + gs.length := by
  induction gs generalizing x with
  | nil => simp [run]
  | cons g gs ih => rw [run_cons, ih]; simp; omega

lemma run_getD (gs : List Gate) (x : List Bool) (w : ℕ) (hw : w < x.length) :
    (run gs x).getD w false = x.getD w false := by
  induction gs generalizing x with
  | nil => rfl
  | cons g gs ih =>
    rw [run_cons, ih _ (by simp; omega), List.getD_append _ _ _ _ hw]

lemma run_split (gs : List Gate) (x : List Bool) (j : ℕ) :
    run gs x = run (gs.drop j) (run (gs.take j) x) := by
  simpa only [run, List.foldl_append] using
    congrArg (fun l : List Gate => run l x) (List.take_append_drop j gs).symm

def value {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ) : Bool :=
  (C.wires (List.ofFn x)).getD w false

lemma input_value {n : ℕ} (C : Circuit) (x : Fin n → Bool) (p : Fin n) :
    value C x p = x p := by
  change (run C.gates (List.ofFn x)).getD p false = x p
  have hp : (p : ℕ) < (List.ofFn x).length := by simp
  rw [run_getD _ _ _ hp, List.getD_eq_getElem _ _ hp]
  simp

lemma missing_value {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ)
    (hw : n + C.size ≤ w) : value C x w = false := by
  change (run C.gates (List.ofFn x)).getD w false = false
  exact List.getD_eq_default _ _ (by simpa [run_length, Circuit.size] using hw)

lemma gate_value {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ)
    (hn : n ≤ w) (hw : w < n + C.size) :
    let g := C.gates[w - n]'(by unfold Circuit.size at hw; omega)
    value C x w = g.op.eval (g.inputs.map fun r => if r < w then value C x r else false) := by
  let j := w - n
  have hj : j < C.gates.length := by unfold j Circuit.size at *; omega
  let g := C.gates[j]
  let earlier := run (C.gates.take j) (List.ofFn x)
  have plen : earlier.length = w := by
    simp [earlier, run_length, Nat.min_eq_left hj.le, j]; omega
  have split : run C.gates (List.ofFn x) = run (g :: C.gates.drop (j + 1)) earlier := by
    rw [run_split C.gates (List.ofFn x) j, List.drop_eq_getElem_cons hj]
  have read (r : ℕ) : earlier.getD r false = if r < w then value C x r else false := by
    by_cases hr : r < w
    · rw [ite_eq_left hr]
      change earlier.getD r false = (run C.gates (List.ofFn x)).getD r false
      rw [split]
      exact (run_getD _ earlier r (by simpa only [plen] using hr)).symm
    · rw [ite_eq_right hr]
      exact List.getD_eq_default _ _ (by omega)
  change (run C.gates (List.ofFn x)).getD w false =
    g.op.eval (g.inputs.map fun r => if r < w then value C x r else false)
  rw (occs := [1]) [split]
  rw (occs := [1]) [run_cons]
  rw [run_getD _ _ _ (by simp [plen]), List.getD_append_right _ _ _ _ (by omega)]
  simp only [plen, Nat.sub_self, List.getD_cons_zero, read]

lemma repl_eval_mono (g : Gate) (hop : g.op = GateOp.and ∨ g.op = GateOp.or) (f f' : ℕ → Bool)
    (h : ∀ r ∈ g.inputs, f r = true → f' r = true) :
    g.op.eval (g.inputs.map f) = true → g.op.eval (g.inputs.map f') = true := by
  rcases hop with hop | hop
  · simp only [hop, GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id_eq]
    exact fun hx r hr => h r hr (hx r hr)
  · simp only [hop, GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id_eq]
    exact fun ⟨r, hr, hx⟩ => ⟨r, hr, h r hr hx⟩

lemma repl_eval_congr (g : Gate) (f f' : ℕ → Bool) (h : ∀ r ∈ g.inputs, f r = f' r) :
    g.op.eval (g.inputs.map f) = g.op.eval (g.inputs.map f') := by
  rw [List.map_congr_left h]


def freeze (C : Circuit) (t : ℕ) (b : Bool) : Circuit :=
  ⟨C.gates.set t ⟨if b then GateOp.and else GateOp.or, []⟩, C.output⟩

lemma freeze_size (C : Circuit) (t : ℕ) (b : Bool) :
    (freeze C t b).size = C.size := by simp [freeze, Circuit.size]

lemma freeze_value {n : ℕ} (C : Circuit) (t : Fin C.gates.length)
    (b : Bool) (x : Fin n → Bool) : value (freeze C t b) x (n + t) = b := by
  rw [gate_value _ _ _ (by omega) (by rw [freeze_size]; simp only [Circuit.size]; omega)]
  cases b <;> simp [freeze, GateOp.eval]

lemma freeze_other {n : ℕ} (C : Circuit) (t : ℕ) (b : Bool)
    (x : Fin n → Bool) (w : ℕ) (hn : n ≤ w) (hw : w < n + C.size)
    (hne : w ≠ n + t) :
    value (freeze C t b) x w = (C.gates[w-n]'(by unfold Circuit.size at hw; omega)).op.eval
      ((C.gates[w-n]'(by unfold Circuit.size at hw; omega)).inputs.map fun r =>
        if r < w then value (freeze C t b) x r else false) := by
  rw [gate_value _ _ _ hn (by rw [freeze_size]; exact hw)]
  have h : t ≠ w - n := by omega
  simp [freeze, h]

lemma freeze_eq {n : ℕ} (C : Circuit) (t : Fin C.gates.length)
    (b : Bool) (x : Fin n → Bool) (ht : value C x (n+t) = b) (w : ℕ) :
    value (freeze C t b) x w = value C x w := by
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    by_cases hn : w < n
    · have h1 := input_value C x ⟨w, hn⟩
      have h2 := input_value (freeze C t b) x ⟨w, hn⟩
      simpa only using h2.trans h1.symm
    by_cases hw : w < n + C.size
    · by_cases he : w = n + t
      · rw [he, freeze_value, ht]
      · rw [freeze_other _ _ _ _ _ (by omega) hw he,
          gate_value C x w (by omega) hw]
        apply repl_eval_congr
        intro r _
        by_cases hr : r < w
        · simpa [hr] using ih r hr
        · simp [hr]
    · rw [missing_value C x w (by omega),
        missing_value (freeze C t b) x w (by rw [freeze_size]; omega)]

lemma before_mono {n : ℕ} (C : Circuit) (t : ℕ)
    (hg : ∀ g ∈ C.gates, g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not)
    (hnot : ∀ i : Fin C.gates.length, (C.gates.get i).op = GateOp.not → (i : ℕ) = t)
    (x y : Fin n → Bool) (hxy : ∀ p, x p = true → y p = true)
    (w : ℕ) (hw : w < n + t) : value C x w = true → value C y w = true := by
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    by_cases hn : w < n
    · have h1 := input_value C x ⟨w, hn⟩
      have h2 := input_value C y ⟨w, hn⟩
      simp only at h1 h2
      rw [h1,h2]
      exact hxy _
    by_cases hl : w < n + C.size
    · rw [gate_value C x w (by omega) hl, gate_value C y w (by omega) hl]
      have hi : w - n < C.gates.length := by unfold Circuit.size at hl; omega
      have hop : (C.gates[w-n]'hi).op = GateOp.and ∨ (C.gates[w-n]'hi).op = GateOp.or := by
        have hne : (C.gates[w-n]'hi).op ≠ GateOp.not := by
          intro he
          have hh := hnot ⟨w-n,hi⟩ he
          simp only at hh
          omega
        rcases hg C.gates[w-n] (List.getElem_mem _) with ha | ho | ht
        · exact Or.inl ha
        · exact Or.inr ho
        · exact (hne ht).elim
      apply repl_eval_mono _ hop
      intro r _
      by_cases hr : r < w
      · simpa [hr] using ih r hr (by omega)
      · simp [hr]
    · rw [missing_value C x w (by omega)]
      simp

lemma not_of_drop {n : ℕ} (C : Circuit) (t : Fin C.gates.length)
    (hg : ∀ g ∈ C.gates, g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not)
    (hnot : ∀ i : Fin C.gates.length, (C.gates.get i).op = GateOp.not → i.val = t.val)
    (x y : Fin n → Bool) (hxy : ∀ p, x p = true → y p = true)
    (hx : value C x (n+t) = true) (hy : value C y (n+t) = false) :
    (C.gates.get t).op = GateOp.not := by
  by_contra hn
  have hop : (C.gates.get t).op = GateOp.and ∨ (C.gates.get t).op = GateOp.or := by
    rcases hg (C.gates.get t) (List.get_mem C.gates t) with ha | ho | ht
    · exact Or.inl ha
    · exact Or.inr ho
    · exact (hn ht).elim
  rw [gate_value C x (n+t) (by omega) (by simp only [Circuit.size]; omega)] at hx
  rw [gate_value C y (n+t) (by omega) (by simp only [Circuit.size]; omega)] at hy
  simp only [Nat.add_sub_cancel_left, List.get_eq_getElem] at hx hy hop
  have ht := repl_eval_mono (C.gates.get t) hop
    (fun r => if r < n+t then value C x r else false)
    (fun r => if r < n+t then value C y r else false) (by
      intro r _
      by_cases hr : r < n+t
      · simpa [hr] using before_mono C t hg hnot x y hxy r hr
      · simp [hr]) hx
  simp only [List.get_eq_getElem] at ht
  rw [hy] at ht
  simp at ht

lemma not_false_above {n : ℕ} (C : Circuit) (t : Fin C.gates.length)
    (hg : ∀ g ∈ C.gates, g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not)
    (hnot : ∀ i : Fin C.gates.length, (C.gates.get i).op = GateOp.not → i.val = t.val)
    (ht : (C.gates.get t).op = GateOp.not)
    (x y : Fin n → Bool) (hxy : ∀ p, x p = true → y p = true)
    (hx : value C x (n+t) = false) : value C y (n+t) = false := by
  rw [gate_value C x (n+t) (by omega) (by simp only [Circuit.size]; omega)] at hx
  rw [gate_value C y (n+t) (by omega) (by simp only [Circuit.size]; omega)]
  simp only [Nat.add_sub_cancel_left] at hx ⊢
  have ht2 : C.gates[t.val].op = GateOp.not := by simpa only [List.get_eq_getElem] using ht
  rw [ht2] at hx ⊢
  simp only [GateOp.eval] at hx ⊢
  cases hs : C.gates[t.val].inputs with
  | nil => simp [hs] at hx
  | cons r rs =>
    simp only [hs, List.map_cons, List.headD_cons] at hx ⊢
    by_cases hr : r < n+t
    · simpa [hr] using before_mono C t hg hnot x y hxy r hr (by simpa [hr] using hx)
    · simp [hr] at hx

lemma freeze_good (C : Circuit) (t : Fin C.gates.length) (b : Bool)
    (hg : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2)
    (hnot : ∀ i : Fin C.gates.length, (C.gates.get i).op = GateOp.not → i.val = t.val) :
    ∀ g ∈ (freeze C t b).gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
  intro g hmem
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hmem
  have hj0 : j < C.gates.length := by simpa [freeze] using hj
  by_cases he : t.val = j
  · cases b <;> simp [freeze, he]
  · have eq : (freeze C t b).gates[j] = C.gates[j] := by simp [freeze, he]
    rw [eq]
    obtain ⟨hop, har⟩ := hg C.gates[j] (List.getElem_mem _)
    refine ⟨?_, har⟩
    rcases hop with ha | ho | hn
    · exact Or.inl ha
    · exact Or.inr ho
    · exact (he (hnot ⟨j,hj0⟩ hn).symm).elim

lemma freeze_false_le {n : ℕ} (C : Circuit) (t : Fin C.gates.length)
    (hg : ∀ g ∈ C.gates, g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not)
    (hnot : ∀ i : Fin C.gates.length, (C.gates.get i).op = GateOp.not → i.val = t.val)
    (x : Fin n → Bool) (w : ℕ) :
    value (freeze C t false) x w = true → value C x w = true := by
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    by_cases hn : w < n
    · have h1 := input_value C x ⟨w,hn⟩
      have h2 := input_value (freeze C t false) x ⟨w,hn⟩
      simp only at h1 h2
      rw [h1,h2]
      exact id
    by_cases hw : w < n+C.size
    · by_cases he : w = n+t
      · rw [he, freeze_value]
        simp
      · rw [freeze_other _ _ _ _ _ (by omega) hw he, gate_value C x w (by omega) hw]
        have hj : w-n < C.gates.length := by unfold Circuit.size at hw; omega
        have hop : (C.gates[w-n]'hj).op = GateOp.and ∨ (C.gates[w-n]'hj).op = GateOp.or := by
          rcases hg C.gates[w-n] (List.getElem_mem _) with ha | ho | ht
          · exact Or.inl ha
          · exact Or.inr ho
          · have hh := hnot ⟨w-n,hj⟩ ht
            simp only at hh
            omega
        apply repl_eval_mono _ hop
        intro r _
        by_cases hr : r < w
        · simpa [hr] using ih r hr
        · simp [hr]
    · rw [missing_value (freeze C t false) x w (by rw [freeze_size]; omega)]
      simp

lemma positive_window_not {n : ℕ} (C : Circuit) (t : ℕ) (Y : Finset (Fin n))
    (hg : ∀ g ∈ C.gates, g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not)
    (hnot : ∀ i : Fin C.gates.length, (C.gates.get i).op = GateOp.not → i.val = t)
    (hk : 0 < Y.card)
    (hsmall : ∀ x : Fin n → Bool, (Finset.univ.filter fun v => x v = true).card < Y.card →
      value C x (n+t) = true)
    (hY : value C (fun v => decide (v ∈ Y)) (n+t) = false) :
    ∃ ht : t < C.gates.length, (C.gates.get ⟨t,ht⟩).op = GateOp.not ∧
      ∀ x : Fin n → Bool, (∀ p ∈ Y, x p = true) → value C x (n+t) = false := by
  have hempty : value C (fun _ => false) (n+t) = true := hsmall _ (by simpa using hk)
  have ht : t < C.gates.length := by
    by_contra h
    have hf := missing_value C (fun _ : Fin n => false) (n+t) (by unfold Circuit.size; omega)
    rw [hf] at hempty
    simp at hempty
  have hn : (C.gates.get ⟨t,ht⟩).op = GateOp.not :=
    not_of_drop C ⟨t,ht⟩ hg hnot (fun _ => false) (fun v => decide (v ∈ Y))
      (by simp) hempty hY
  refine ⟨ht, hn, ?_⟩
  intro x hx
  exact not_false_above C ⟨t,ht⟩ hg hnot hn _ x
    (fun p hp => hx p (of_decide_eq_true hp)) hY

end PEqualNP.Outside.L_meta_997.Window
