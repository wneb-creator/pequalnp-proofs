import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1477.GateInvariant
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



def Mixing {n : ℕ} (C : Circuit) (x y z : Fin n → Bool) (w : ℕ) : Prop :=
  value C z w = true ∧ value C x w = false ∧ value C y w = false

lemma first_mixing_gate {n : ℕ} (C : Circuit)
    (hC : PEqualNP.MetaComplexity.Monotone2 C) (x y z : Fin n → Bool)
    (hin : ∀ i, z i = true → x i = true ∨ y i = true)
    (out : ℕ) (hout : Mixing C x y z out) :
    ∃ (w a b : ℕ) (h : w - n < C.gates.length), n ≤ w ∧
      C.gates[w - n] = ⟨GateOp.and, [a, b]⟩ ∧ a < w ∧ b < w ∧
      value C z a = true ∧ value C z b = true ∧
      ((value C x a = false ∧ value C y a = true ∧
        value C x b = true ∧ value C y b = false) ∨
       (value C x a = true ∧ value C y a = false ∧
        value C x b = false ∧ value C y b = true)) := by
  classical
  have hex : ∃ w, Mixing C x y z w := ⟨out, hout⟩
  let w := Nat.find hex
  have hw : Mixing C x y z w := Nat.find_spec hex
  have hmin : ∀ r < w, ¬ Mixing C x y z r := fun r hr => Nat.find_min hex hr
  have hn : n ≤ w := by
    by_contra! hn
    obtain ⟨hz, hx, hy⟩ := hw
    change value C z (⟨w, hn⟩ : Fin n) = true at hz
    change value C x (⟨w, hn⟩ : Fin n) = false at hx
    change value C y (⟨w, hn⟩ : Fin n) = false at hy
    have ez := input_value C z ⟨w, hn⟩
    have ex := input_value C x ⟨w, hn⟩
    have ey := input_value C y ⟨w, hn⟩
    change value C z w = z ⟨w, hn⟩ at ez
    change value C x w = x ⟨w, hn⟩ at ex
    change value C y w = y ⟨w, hn⟩ at ey
    rw [ez] at hz
    rw [ex] at hx
    rw [ey] at hy
    rcases hin ⟨w, hn⟩ hz with h | h <;> simp_all
  have hsize : w < n + C.size := by
    by_contra! h
    have := hw.1
    simp [missing_value C z w h] at this
  have hj : w - n < C.gates.length := by unfold Circuit.size at hsize; omega
  let g := C.gates[w - n]
  obtain ⟨hop, hlen⟩ := hC g (List.getElem_mem _)
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
  let rd := fun t : Fin n → Bool => fun r => if r < w then value C t r else false
  have hf (t : Fin n → Bool) : value C t w = g.op.eval (g.inputs.map (rd t)) :=
    gate_value C t w hn hsize
  have hz := hw.1
  have hx := hw.2.1
  have hy := hw.2.2
  rw [hf] at hz hx hy
  have hread (r) : ¬ (rd z r = true ∧ rd x r = false ∧ rd y r = false) := by
    rintro ⟨hzr, hxr, hyr⟩
    have hr : r < w := by by_contra h; simp [rd, h] at hzr
    apply hmin r hr
    simpa [Mixing, rd, hr] using And.intro hzr (And.intro hxr hyr)
  rcases hop with hop | hop
  · rcases hl : g.inputs with _ | ⟨a, l⟩
    · simp [hop, hl, GateOp.eval] at hx
    · rcases l with _ | ⟨b, l⟩
      · have ha := hread a
        simp [hop, hl, GateOp.eval] at hz hx hy
        exact False.elim (ha ⟨hz, hx, hy⟩)
      · have hnil : l = [] := by simpa [hl] using hlen
        subst l
        have hzz : rd z a = true ∧ rd z b = true := by
          simpa [hop, hl, GateOp.eval] using hz
        have hza := hzz.1
        have hzb := hzz.2
        have ha : a < w := by by_contra h; simp [rd, h] at hza
        have hb : b < w := by by_contra h; simp [rd, h] at hzb
        refine ⟨w, a, b, hj, hn, ?_, ha, hb, ?_, ?_, ?_⟩
        · change g = _
          cases hg : g with
          | mk op inputs => simp_all
        · simpa [rd, ha] using hza
        · simpa [rd, hb] using hzb
        have hna := hread a
        have hnb := hread b
        have hcross :
            (rd x a = false ∧ rd y a = true ∧ rd x b = true ∧ rd y b = false) ∨
            (rd x a = true ∧ rd y a = false ∧ rd x b = false ∧ rd y b = true) := by
          cases hxa : rd x a <;> cases hya : rd y a <;>
            cases hxb : rd x b <;> cases hyb : rd y b <;>
            simp_all [hop, hl, GateOp.eval]
        simpa [rd, ha, hb] using hcross
  · have hzo : ∃ r ∈ g.inputs, rd z r = true := by
      simpa only [hop, GateOp.eval, List.any_map, List.any_eq_true,
        Function.comp_apply, id_eq] using hz
    have hxo : ∀ r ∈ g.inputs, rd x r = false := by
      simpa [hop, GateOp.eval, List.any_map] using hx
    have hyo : ∀ r ∈ g.inputs, rd y r = false := by
      simpa [hop, GateOp.eval, List.any_map] using hy
    obtain ⟨r, hr, hzr⟩ := hzo
    exact False.elim (hread r ⟨hzr, hxo r hr, hyo r hr⟩)

end PEqualNP.Outside.L_meta_1477.GateInvariant
