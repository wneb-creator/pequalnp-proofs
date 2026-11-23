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

namespace PEqualNP.Outside.L_meta_997.SparseCount
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

lemma gate_inputs {n : ℕ} (C : Circuit)
    (hG : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (w : ℕ) (hn : n ≤ w) (hw : w < n + C.size) :
    ∃ P : Finset ℕ, P.card ≤ 2 ∧ (∀ r ∈ P, r < w) ∧
      ∀ (x y : Fin n → Bool), (∀ r ∈ P, value C x r = true → value C y r = true) →
        value C x w = true → value C y w = true := by
  let g := C.gates[w - n]'(by unfold Circuit.size at hw; omega)
  obtain ⟨hop, hlen⟩ := hG g (List.getElem_mem _)
  let P := g.inputs.toFinset.filter (· < w)
  refine ⟨P, (Finset.card_filter_le _ _).trans ((List.toFinset_card_le g.inputs).trans hlen), ?_, ?_⟩
  · exact fun r hr => (Finset.mem_filter.mp hr).2
  · intro x y hxy hx
    have step (r) (hr : r ∈ g.inputs) :
        (if r < w then value C x r else false) = true →
        (if r < w then value C y r else false) = true := by
      by_cases h : r < w
      · simpa [h] using hxy r (Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr hr,h⟩)
      · simp [h]
    have form (z : Fin n → Bool) :
        value C z w = g.op.eval (g.inputs.map fun r => if r < w then value C z r else false) :=
      gate_value C z w hn hw
    rw [form x] at hx
    rw [form y]
    rcases hop with hop|hop
    · simp only [hop, GateOp.eval, List.all_eq_true, List.mem_map, id_eq] at hx ⊢
      intro b hb
      obtain ⟨r,hr,rfl⟩ := hb
      exact step r hr (hx _ ⟨r,hr,rfl⟩)
    · simp only [hop, GateOp.eval, List.any_eq_true, List.mem_map, id_eq] at hx ⊢
      obtain ⟨b,⟨r,hr,rfl⟩,hv⟩ := hx
      exact ⟨_, ⟨r,hr,rfl⟩, step r hr hv⟩

lemma value_mono {n : ℕ} (C : Circuit)
    (hG : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (x y : Fin n → Bool) (hxy : ∀ p, x p = true → y p = true) (w : ℕ) :
    value C x w = true → value C y w = true := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases hn : w < n
    · let p : Fin n := ⟨w, hn⟩
      change value C x p = true → value C y p = true
      simpa only [input_value] using hxy p
    by_cases hw : w < n + C.size
    · obtain ⟨P, _, hP, hstep⟩ := gate_inputs C hG w (by omega) hw
      exact hstep x y fun r hr => ih r (hP r hr)
    · simp [missing_value C x w (by omega)]

lemma cut {n : ℕ} (C : Circuit)
    (hG : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (G : Finset ℕ) (hGates : ∀ w ∈ G, n ≤ w ∧ w < n + C.size)
    (t : ℕ) (F : Finset ℕ) (hF : ∀ w ∈ F, w ∈ G → w < t) :
    ∃ B : Finset ℕ, Disjoint B G ∧ B.card ≤ F.card + (G.filter (· < t)).card ∧
      ∀ x y : Fin n → Bool, (∀ w ∈ B, value C x w = true → value C y w = true) →
        ∀ w ∈ F, value C x w = true → value C y w = true := by
  induction t generalizing F with
  | zero =>
    exact ⟨F, Finset.disjoint_left.mpr (fun w hw hg => by have := hF w hw hg; omega),
      Nat.le_add_right .., fun _ _ h => h⟩
  | succ t ih =>
    by_cases hex : t ∈ F ∧ t ∈ G
    · obtain ⟨P, hPcard, hP, hp⟩ := gate_inputs C hG t (hGates t hex.2).1 (hGates t hex.2).2
      let F' := F.erase t ∪ P
      have hF' : ∀ w ∈ F', w ∈ G → w < t := by
        intro w hw hg
        rcases Finset.mem_union.mp hw with hw | hw
        · have hne := (Finset.mem_erase.mp hw).1
          have hlt := hF w (Finset.mem_erase.mp hw).2 hg
          omega
        · exact hP w hw
      obtain ⟨B, hd, hc, hi⟩ := ih F' hF'
      have hsize : F'.card ≤ F.card + 1 := by
        have hu := Finset.card_union_le (F.erase t) P
        have he := Finset.card_erase_add_one hex.1
        change F'.card ≤ _ at hu
        omega
      have hfilter : G.filter (· < t + 1) = insert t (G.filter (· < t)) := by
        ext w
        simp only [Finset.mem_filter, Finset.mem_insert]
        constructor
        · rintro ⟨hg, hlt⟩
          by_cases h : w = t
          · exact Or.inl h
          · exact Or.inr ⟨hg, by omega⟩
        · rintro (rfl | ⟨hg, hlt⟩)
          · exact ⟨hex.2, by omega⟩
          · exact ⟨hg, by omega⟩
      refine ⟨B, hd, ?_, ?_⟩
      · rw [hfilter, Finset.card_insert_of_notMem (by simp)]
        omega
      · intro x y hxy w hw
        by_cases h : w = t
        · subst w
          exact hp x y fun r hr => hi x y hxy r (Finset.mem_union_right _ hr)
        · exact hi x y hxy w (Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨h, hw⟩))
    · have hF' : ∀ w ∈ F, w ∈ G → w < t := by
        intro w hw hg
        have hne : w ≠ t := fun e => hex ⟨e ▸ hw, e ▸ hg⟩
        have hlt := hF w hw hg
        omega
      obtain ⟨B, hd, hc, hi⟩ := ih F hF'
      have hle : (G.filter (· < t)).card ≤ (G.filter (· < t + 1)).card :=
        Finset.card_le_card fun w hw =>
          Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hw).1, by have := (Finset.mem_filter.mp hw).2; omega⟩
      exact ⟨B, hd, by omega, hi⟩

def support {n : ℕ} (C : Circuit) (w : ℕ) : Finset (Fin n) :=
  Finset.univ.filter (fun p => value C (fun q => decide (q = p)) w = true)

lemma mem_support {n : ℕ} (C : Circuit) (w : ℕ) (p : Fin n) :
    p ∈ support C w ↔ value C (fun q => decide (q = p)) w = true := by
  simp [support]

lemma support_gate {n : ℕ} (C : Circuit) (w : ℕ) (h : 2 ≤ (support (n := n) C w).card) :
    n ≤ w ∧ w < n + C.size := by
  constructor
  · by_contra! hw
    let p : Fin n := ⟨w, hw⟩
    have hs : support C w ⊆ {p} := by
      intro q hq
      have hv := (mem_support C w q).mp hq
      change value C (fun r => decide (r = q)) p = true at hv
      simpa [input_value, eq_comm] using hv
    have hb := Finset.card_le_card hs
    simp at hb
    omega
  · by_contra! hw
    have hs : support (n := n) C w = ∅ := by
      ext q
      simp [mem_support, missing_value C _ w hw]
    simp [hs] at h


def assigned {n : ℕ} (C : Circuit) (T : Finset (Fin n)) : Finset ℕ :=
  (Finset.Ico n (n + C.size)).filter fun w => support C w ⊆ T ∧ 2 ≤ (support (n := n) C w).card

-- A small cut leaves some point of T uncovered by its clean wires.
-- Each other wire can be made true by a single point outside T.
-- Adapted from L-meta-270. Count only the singleton inputs accepted by the output.
lemma card_assigned {n k c : ℕ} (C : Circuit) (T : Finset (Fin n)) (o : ℕ)
    (hG : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hsparse : ∀ x : Fin n → Bool, (Finset.univ.filter (fun q => x q = true)).card ≤ k →
      (∀ q ∈ T, x q = false) → value C x o = false)
    (hk : c ≤ k) (hc : c + 1 ≤ (support (n := n) C o).card) : c ≤ (assigned C T).card := by
  classical
  let G := assigned C T
  by_contra! hsmall
  have hgate : ∀ w ∈ G, n ≤ w ∧ w < n + C.size := by
    intro w hw
    exact Finset.mem_Ico.mp (Finset.mem_filter.mp hw).1
  obtain ⟨B, hd, hBcard, hcut⟩ := cut C hG G hgate (n + C.size) {o}
    (fun w _ hw => (hgate w hw).2)
  have hb : B.card ≤ c := by
    have hfilter := Finset.card_filter_le G (fun w => w < n + C.size)
    simp only [Finset.card_singleton] at hBcard
    change G.card < c at hsmall
    omega
  let clean (w : ℕ) : Finset (Fin n) := if support C w ⊆ T then support C w else ∅
  have hclean : ∀ w ∈ B, (clean w).card ≤ 1 := by
    intro w hw
    by_cases hs : support C w ⊆ T
    · change (if support C w ⊆ T then support (n := n) C w else ∅).card ≤ 1
      rw [ite_eq_left hs]
      by_contra! hlarge
      exact Finset.disjoint_left.mp hd hw
        (Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr (support_gate C w (by omega)), hs, by omega⟩)
    · simp [clean, hs]
  have hcover : (B.biUnion clean).card < (support (n := n) C o).card := by
    have h := Finset.card_biUnion_le_card_mul B clean 1 hclean
    simp only [mul_one] at h
    omega
  obtain ⟨p, hp, hpnot⟩ := Finset.exists_mem_notMem_of_card_lt_card hcover
  let D := B.filter (fun w => ¬ support C w ⊆ T)
  have hout (w : {w // w ∈ D}) : ∃ q : Fin n, q ∈ support C w.val ∧ q ∉ T := by
    by_contra! h
    exact (Finset.mem_filter.mp w.property).2 h
  choose q hq using hout
  let U := D.attach.image q
  let y : Fin n → Bool := fun r => decide (r ∈ U)
  have hu : U.card ≤ k := calc
    U.card ≤ D.attach.card := Finset.card_image_le
    _ = D.card := Finset.card_attach
    _ ≤ B.card := Finset.card_filter_le _ _
    _ ≤ k := hb.trans hk
  have hyfalse : value C y o = false := by
    apply hsparse y
    · have hset : Finset.univ.filter (fun r => y r = true) = U := by ext r; simp [y]
      rwa [hset]
    · intro r hr
      have hnot : r ∉ U := by
        intro hmem
        obtain ⟨w, _, rfl⟩ := Finset.mem_image.mp hmem
        exact (hq w).2 hr
      simp [y, hnot]
  have hytrue : value C y o = true := by
    apply hcut (fun r => decide (r = p)) y _ o (Finset.mem_singleton_self o) ((mem_support C o p).mp hp)
    intro w hw hx
    by_cases hs : support C w ⊆ T
    · exact False.elim (hpnot (Finset.mem_biUnion.mpr
        ⟨w, hw, by simpa only [clean, ite_eq_left hs, mem_support] using hx⟩))
    · let d : {w // w ∈ D} := ⟨w, Finset.mem_filter.mpr ⟨hw, hs⟩⟩
      apply value_mono C hG (fun r => decide (r = q d)) y _ w ((mem_support C w (q d)).mp (hq d).1)
      intro r hr
      have he : r = q d := of_decide_eq_true hr
      subst r
      have hm : q d ∈ U := Finset.mem_image_of_mem q (Finset.mem_attach D d)
      simp [y, hm]
  simp [hyfalse] at hytrue


lemma sum_min_card_le {n m k : ℕ} (C : Circuit) (S : Fin m → Finset (Fin n))
    (o : Fin m → ℕ)
    (hG : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hinter : ∀ i j, i ≠ j → (S i ∩ S j).card ≤ 1)
    (hsingle : ∀ i p, value C (fun q => decide (q = p)) (o i) = true ↔ p ∈ S i)
    (hsparse : ∀ i (x : Fin n → Bool), (Finset.univ.filter (fun q => x q = true)).card < k →
      (∀ q ∈ S i, x q = false) → value C x (o i) = false) :
    (∑ i, min k (S i).card) ≤ C.size + m := by
  classical
  let G (i : Fin m) := assigned C (S i)
  let c (i : Fin m) := min k (S i).card - 1
  have hd : ((Finset.univ : Finset (Fin m)) : Set (Fin m)).PairwiseDisjoint G := by
    intro i _ j _ hij
    refine Finset.disjoint_left.mpr fun w hwi hwj => ?_
    have hi := (Finset.mem_filter.mp hwi).2
    have hj := (Finset.mem_filter.mp hwj).2
    have hsub : support C w ⊆ S i ∩ S j := fun p hp => Finset.mem_inter.mpr ⟨hi.1 hp, hj.1 hp⟩
    have hle := Finset.card_le_card hsub
    have hsmall := hinter i j hij
    omega
  have bound (i : Fin m) : c i ≤ (G i).card := by
    by_cases hz : c i = 0
    · simp [hz]
    have hcs : c i + 1 ≤ (S i).card := by
      have := min_le_right k (S i).card
      dsimp [c] at *
      omega
    have hck : c i ≤ k - 1 := by
      have := min_le_left k (S i).card
      dsimp [c] at *
      omega
    have hs : support C (o i) = S i := by
      ext p
      exact (mem_support C (o i) p).trans (hsingle i p)
    apply card_assigned C (S i) (o i) hG (k := k - 1)
    · intro x hx hnone
      apply hsparse i x _ hnone
      have : 0 < k := by dsimp [c] at hz; omega
      omega
    · exact hck
    · simpa [hs] using hcs
  have hc : (∑ i, c i) ≤ C.size := by
    calc
      (∑ i, c i) ≤ ∑ i, (G i).card := Finset.sum_le_sum fun i _ => bound i
      _ = (Finset.univ.biUnion G).card := (Finset.card_biUnion hd).symm
      _ ≤ (Finset.Ico n (n + C.size)).card := Finset.card_le_card fun w hw => by
        obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp hw
        exact (Finset.mem_filter.mp hi).1
      _ = C.size := by simp
  calc
    (∑ i, min k (S i).card) ≤ ∑ i, (c i + 1) := by
      apply Finset.sum_le_sum
      intro i _
      dsimp [c]
      omega
    _ = (∑ i, c i) + m := by simp [Finset.sum_add_distrib]
    _ ≤ C.size + m := Nat.add_le_add_right hc _


lemma sum_min_card_le_of_window {n m k : ℕ} (C : Circuit) (S : Fin m → Finset (Fin n))
    (o : Fin m → ℕ)
    (hG : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hinter : ∀ i j, i ≠ j → (S i ∩ S j).card ≤ 1)
    (hwindow : ∀ i (x : Fin n → Bool), (Finset.univ.filter (fun q => x q = true)).card < k →
      value C x (o i) = decide (∃ p ∈ S i, x p = true)) :
    (∑ i, min k (S i).card) ≤ C.size + m := by
  classical
  by_cases hk : k ≤ 1
  · have hsum : (∑ i, min k (S i).card) ≤ m := by
      calc
        (∑ i, min k (S i).card) ≤ ∑ _i : Fin m, 1 :=
          Finset.sum_le_sum fun i _ => (min_le_left _ _).trans hk
        _ = m := by simp
    omega
  apply sum_min_card_le C S o hG hinter
  · intro i p
    have hx : (Finset.univ.filter (fun q : Fin n => decide (q = p) = true)).card < k := by
      have he : (Finset.univ.filter (fun q : Fin n => decide (q = p) = true)) = {p} := by
        ext q
        simp
      rw [he, Finset.card_singleton]
      omega
    rw [hwindow i _ hx]
    simp
  · intro i x hx hnone
    rw [hwindow i x hx]
    simp only [decide_eq_false_iff_not, not_exists, not_and]
    intro p hp
    rw [hnone p hp]
    decide

end PEqualNP.Outside.L_meta_997.SparseCount

namespace PEqualNP.Outside.L_meta_997.RefundOutputs

open PEqualNP.CircuitLowerBounds
open PEqualNP.Outside.L_meta_997.Window

def refund {n m : ℕ} (S : Fin m → Finset (Fin n)) (C : Circuit)
    (y : Finset (Fin n)) : Finset (Fin C.gates.length) :=
  Finset.univ.filter fun g =>
    (∃ i, ∀ p, value C (fun v => decide (v = p)) (n + g) = true ↔ p ∈ S i) ∧
    (∃ i, Disjoint (S i) y ∧ ∀ p, p ∉ y →
      (value C (fun v => decide (v ∈ y ∨ v = p)) (n + g) = true ↔ p ∈ S i))

def largeHeavy {n m : ℕ} (S : Fin m → Finset (Fin n))
    (y : Finset (Fin n)) (k : ℕ) : Finset (Fin m) :=
  Finset.univ.filter fun i => Disjoint (S i) y ∧ k < (S i).card

theorem singleton_signature {n m : ℕ} (S : Fin m → Finset (Fin n))
    (C : Circuit) (o : Fin m → ℕ)
    (hfun : ∀ i x, value C x (o i) = decide (∃ p ∈ S i, x p = true)) :
    ∀ i p, value C (fun v => decide (v = p)) (o i) = true ↔ p ∈ S i := by
  intro i p
  rw [hfun]
  simp

theorem output_gate_bounds {n m : ℕ} (S : Fin m → Finset (Fin n))
    (C : Circuit) (o : Fin m → ℕ)
    (hfun : ∀ i x, value C x (o i) = decide (∃ p ∈ S i, x p = true))
    (i : Fin m) (hi : 2 ≤ (S i).card) :
    n ≤ o i ∧ o i < n + C.gates.length := by
  obtain ⟨p, hp, q, hq, hpq⟩ := Finset.one_lt_card.mp (by omega : 1 < (S i).card)
  have hsp := (singleton_signature S C o hfun i p).mpr hp
  have hsq := (singleton_signature S C o hfun i q).mpr hq
  constructor
  · by_contra! ho
    let r : Fin n := ⟨o i, ho⟩
    change value C (fun v => decide (v = p)) r.val = true at hsp
    change value C (fun v => decide (v = q)) r.val = true at hsq
    rw [input_value] at hsp hsq
    have hrp : r = p := of_decide_eq_true hsp
    have hrq : r = q := of_decide_eq_true hsq
    exact hpq (hrp.symm.trans hrq)
  · by_contra! ho
    rw [missing_value C _ (o i) (by simpa [Circuit.size] using ho)] at hsp
    exact Bool.false_ne_true hsp

theorem disjoint_output_refunded {n m : ℕ} (S : Fin m → Finset (Fin n))
    (C : Circuit) (o : Fin m → ℕ) (y : Finset (Fin n))
    (hfun : ∀ i x, value C x (o i) = decide (∃ p ∈ S i, x p = true))
    (i : Fin m) (hi : 2 ≤ (S i).card) (hiy : Disjoint (S i) y) :
    ∃ g ∈ refund S C y, n + (g : ℕ) = o i := by
  have hb := output_gate_bounds S C o hfun i hi
  let g : Fin C.gates.length := ⟨o i - n, by omega⟩
  have hg : n + (g : ℕ) = o i := by dsimp [g]; omega
  refine ⟨g, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, hg⟩
  constructor
  · exact ⟨i, fun p => hg ▸ singleton_signature S C o hfun i p⟩
  · refine ⟨i, hiy, ?_⟩
    intro p _
    rw [hg, hfun, decide_eq_true_eq]
    constructor
    · rintro ⟨q, hq, hval⟩
      have hv : q ∈ y ∨ q = p := of_decide_eq_true hval
      rcases hv with hqy | rfl
      · exact False.elim (Finset.disjoint_left.mp hiy hq hqy)
      · exact hq
    · intro hp
      exact ⟨p, hp, by simp⟩

theorem large_heavy_refund_bound {n m : ℕ} (S : Fin m → Finset (Fin n))
    (C : Circuit) (o : Fin m → ℕ) (y : Finset (Fin n)) (k : ℕ)
    (hk : 1 ≤ k)
    (hint : ∀ i j, i ≠ j → (S i ∩ S j).card ≤ 1)
    (hfun : ∀ i x, value C x (o i) = decide (∃ p ∈ S i, x p = true)) :
    (largeHeavy S y k).card ≤ (refund S C y).card := by
  classical
  have hinj : Set.InjOn o (↑(largeHeavy S y k) : Set (Fin m)) := by
    intro i hi j hj hij
    by_contra hne
    have hset : S i = S j := by
      ext p
      rw [← singleton_signature S C o hfun i p, hij,
        singleton_signature S C o hfun j p]
    have hlarge := (Finset.mem_filter.mp hi).2.2
    have hsmall := hint i j hne
    rw [hset, Finset.inter_self] at hsmall
    rw [hset] at hlarge
    omega
  have hsub : (largeHeavy S y k).image o ⊆
      (refund S C y).image (fun g : Fin C.gates.length => n + (g : ℕ)) := by
    intro w hw
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hw
    have hd := (Finset.mem_filter.mp hi).2
    obtain ⟨g, hg, heq⟩ := disjoint_output_refunded S C o y hfun i (by omega) hd.1
    exact Finset.mem_image.mpr ⟨g, hg, heq⟩
  calc
    (largeHeavy S y k).card = ((largeHeavy S y k).image o).card :=
      (Finset.card_image_iff.mpr hinj).symm
    _ ≤ ((refund S C y).image (fun g : Fin C.gates.length => n + (g : ℕ))).card := Finset.card_le_card hsub
    _ ≤ (refund S C y).card := Finset.card_image_le

theorem bounded_heavy_size_finish {n m : ℕ} (S : Fin m → Finset (Fin n))
    (C : Circuit) (o : Fin m → ℕ) (y : Finset (Fin n)) (k : ℕ)
    (hk : 1 ≤ k)
    (hint : ∀ i j, i ≠ j → (S i ∩ S j).card ≤ 1)
    (hfun : ∀ i x, value C x (o i) = decide (∃ p ∈ S i, x p = true))
    (hsize : ∀ i, Disjoint (S i) y → (S i).card ≤ k + 1)
    (hlight : (∑ i, min k (S i).card) ≤ C.gates.length + m) :
    (∑ i, if Disjoint (S i) y then (S i).card else min k (S i).card) ≤
      C.gates.length + (refund S C y).card + m := by
  classical
  have hterm : ∀ i : Fin m,
      (if Disjoint (S i) y then (S i).card else min k (S i).card) ≤
      min k (S i).card + (if Disjoint (S i) y ∧ k < (S i).card then 1 else 0) := by
    intro i
    by_cases hd : Disjoint (S i) y
    · have hs := hsize i hd
      by_cases hbig : k < (S i).card
      · simp [hd, hbig, Nat.min_eq_left (by omega : k ≤ (S i).card)]
        omega
      · simp [hd, hbig, Nat.min_eq_right (by omega : (S i).card ≤ k)]
    · simp [hd]
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hterm i)
  simp only [Finset.sum_add_distrib] at hs
  have hcount : (∑ i : Fin m, if Disjoint (S i) y ∧ k < (S i).card then 1 else 0) =
      (largeHeavy S y k).card := by simp [largeHeavy]
  rw [hcount] at hs
  have hr := large_heavy_refund_bound S C o y k hk hint hfun
  omega

end PEqualNP.Outside.L_meta_997.RefundOutputs

namespace PEqualNP.Outside.L_meta_997.RefundOutputs

open PEqualNP.CircuitLowerBounds
open PEqualNP.Outside.L_meta_997.Window

theorem bounded_heavy_size_one_not {n m : ℕ} (S : Fin m → Finset (Fin n))
    (C : Circuit) (o : Fin m → ℕ) (t : ℕ) (y : Finset (Fin n))
    (hy : 1 ≤ y.card)
    (hint : ∀ i j, i ≠ j → (S i ∩ S j).card ≤ 1)
    (hgood : ∀ g ∈ C.gates,
      (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2)
    (hnot : ∀ i : Fin C.gates.length, (C.gates.get i).op = GateOp.not → i.val = t)
    (hfun : ∀ i x, value C x (o i) = decide (∃ p ∈ S i, x p = true))
    (hsmall : ∀ x : Fin n → Bool,
      (Finset.univ.filter fun v => x v = true).card < y.card → value C x (n + t) = true)
    (hsize : ∀ i, Disjoint (S i) y → (S i).card ≤ y.card + 1) :
    (∑ i, if Disjoint (S i) y then (S i).card else min y.card (S i).card) ≤
      C.gates.length + (refund S C y).card + m := by
  have hempty := hsmall (fun _ => false) (by simpa using hy)
  have ht : t < C.gates.length := by
    by_contra! hbad
    rw [missing_value C _ (n + t) (by simpa [Circuit.size] using Nat.add_le_add_left hbad n)] at hempty
    exact Bool.false_ne_true hempty
  let tf : Fin C.gates.length := ⟨t, ht⟩
  have hlight : (∑ i, min y.card (S i).card) ≤ C.gates.length + m := by
    have hh := SparseCount.sum_min_card_le_of_window (k := y.card)
      (freeze C tf true) S o (freeze_good C tf true hgood hnot) hint (by
        intro i x hx
        change value (freeze C tf true) x (o i) = _
        rw [freeze_eq C tf true x (hsmall x hx), hfun])
    simpa [freeze, Circuit.size] using hh
  exact bounded_heavy_size_finish S C o y y.card hy hint hfun hsize hlight

end PEqualNP.Outside.L_meta_997.RefundOutputs
