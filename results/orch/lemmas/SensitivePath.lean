import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1477.SensitivePath
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




def zeroAt (C : Circuit) (j : ℕ) : Circuit :=
  ⟨C.gates.set j ⟨GateOp.or, []⟩, C.output⟩

lemma zeroAt_size (C : Circuit) (j : ℕ) : (zeroAt C j).size = C.size := by
  simp [zeroAt, Circuit.size]

lemma zeroAt_gate (C : Circuit) (j k : ℕ) (hk : k < C.gates.length) (hne : j ≠ k) :
    (zeroAt C j).gates[k]'(by simpa [zeroAt] using hk) = C.gates[k] := by
  exact List.getElem_set_of_ne hne _ _

def Changed {n : ℕ} (C : Circuit) (x : Fin n → Bool) (j w : ℕ) : Prop :=
  value C x w = true ∧ value (zeroAt C j) x w = false

lemma changed_bounds {n : ℕ} (C : Circuit) (x : Fin n → Bool) (j w : ℕ)
    (hw : Changed C x j w) : n ≤ w ∧ w < n + C.size := by
  constructor
  · by_contra h
    have hn : w < n := by omega
    have hv := input_value C x ⟨w, hn⟩
    have hz := input_value (zeroAt C j) x ⟨w, hn⟩
    change value C x w = x ⟨w, hn⟩ at hv
    change value (zeroAt C j) x w = x ⟨w, hn⟩ at hz
    change value C x w = true ∧ value (zeroAt C j) x w = false at hw
    rw [hv, hz] at hw
    exact Bool.noConfusion (hw.1.symm.trans hw.2)
  · by_contra h
    have hfalse := missing_value C x w (by omega)
    exact Bool.noConfusion (hw.1.symm.trans hfalse)

lemma eval_change_input (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or)
    (l : List ℕ) (hi lo : ℕ → Bool)
    (hhi : op.eval (l.map hi) = true) (hlo : op.eval (l.map lo) = false) :
    (∃ a ∈ l, hi a = true ∧ lo a = false) ∧
      (op = GateOp.and → ∀ a ∈ l, hi a = true) ∧
      (op = GateOp.or → ∀ a ∈ l, lo a = false) := by
  rcases hop with rfl | rfl
  · have hall : ∀ a ∈ l, hi a = true := by simpa [GateOp.eval] using hhi
    have hex : ∃ a ∈ l, lo a = false := by
      by_contra hn
      have hl : ∀ a ∈ l, lo a = true := by
        intro a ha
        cases h : lo a
        · exact False.elim (hn ⟨a, ha, h⟩)
        · rfl
      have ht : GateOp.and.eval (l.map lo) = true := by simpa [GateOp.eval] using hl
      rw [hlo] at ht
      cases ht
    obtain ⟨a, ha, hla⟩ := hex
    exact ⟨⟨a, ha, hall a ha, hla⟩, fun _ => hall, by simp⟩
  · have hex : ∃ a ∈ l, hi a = true := by simpa [GateOp.eval] using hhi
    have hall : ∀ a ∈ l, lo a = false := by
      intro a ha
      apply Bool.eq_false_iff.mpr
      intro ht
      have ht' : GateOp.or.eval (l.map lo) = true := by
        simpa [GateOp.eval] using (show ∃ b ∈ l, lo b = true from ⟨a, ha, ht⟩)
      rw [hlo] at ht'
      cases ht'
    obtain ⟨a, ha, hha⟩ := hex
    exact ⟨⟨a, ha, hha, hall a ha⟩, by simp, fun _ => hall⟩

lemma changed_predecessor {n : ℕ} (C : Circuit)
    (hC : PEqualNP.MetaComplexity.Monotone2 C)
    (x : Fin n → Bool) (j w : ℕ) (hw : Changed C x j w) (hne : w ≠ n + j) :
    ∃ (a : ℕ) (h : w - n < C.gates.length), a < w ∧
      a ∈ C.gates[w - n].inputs ∧ Changed C x j a ∧
      (C.gates[w - n].op = GateOp.and →
        ∀ b ∈ C.gates[w - n].inputs, b < w ∧ value C x b = true) ∧
      (C.gates[w - n].op = GateOp.or →
        ∀ b ∈ C.gates[w - n].inputs, b < w → value (zeroAt C j) x b = false) := by
  have hb := changed_bounds C x j w hw
  have hk : w - n < C.gates.length := by
    have hh := hb.2
    change w < n + C.gates.length at hh
    omega
  have hne' : j ≠ w - n := by omega
  let g := C.gates[w - n]
  have hop : g.op = GateOp.and ∨ g.op = GateOp.or := by
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using (hC g (List.getElem_mem hk)).1
  have hv := gate_value C x w hb.1 hb.2
  have hz := gate_value (zeroAt C j) x w hb.1 (by rw [zeroAt_size]; exact hb.2)
  have hzk : w - n < (zeroAt C j).gates.length := by simpa [zeroAt] using hk
  have hzg := zeroAt_gate C j (w - n) hk hne'
  change value (zeroAt C j) x w =
    (zeroAt C j).gates[w - n].op.eval
      ((zeroAt C j).gates[w - n].inputs.map
        fun r => if r < w then value (zeroAt C j) x r else false) at hz
  rw [hzg] at hz
  have hh : g.op.eval (g.inputs.map fun r => if r < w then value C x r else false) = true :=
    hv.symm.trans hw.1
  have hl : g.op.eval (g.inputs.map fun r => if r < w then value (zeroAt C j) x r else false) = false :=
    hz.symm.trans hw.2
  obtain ⟨⟨a, ha, hat, haf⟩, hand, hor⟩ := eval_change_input g.op hop g.inputs _ _ hh hl
  have haw : a < w := by
    by_contra h
    simp [h] at hat
  refine ⟨a, hk, haw, ha, ⟨?_, ?_⟩, ?_, ?_⟩
  · simpa [haw] using hat
  · simpa [haw] using haf
  · intro hop b hb
    have ht := hand hop b hb
    have hbw : b < w := by
      by_contra h
      simp [h] at ht
    exact ⟨hbw, by simpa [hbw] using ht⟩
  · intro hop b hb hbw
    simpa [hbw] using hor hop b hb



def SensitiveStep {n : ℕ} (C : Circuit) (x : Fin n → Bool) (j a b : ℕ) : Prop :=
  a < b ∧ n ≤ b ∧ b < n + C.size ∧
    a ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C (b - n)).inputs ∧
    Changed C x j a ∧ Changed C x j b ∧
    ((PEqualNP.MetaComplexity.NestedCover.gateAt C (b - n)).op = GateOp.and →
      ∀ r ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C (b - n)).inputs,
        r < b ∧ value C x r = true) ∧
    ((PEqualNP.MetaComplexity.NestedCover.gateAt C (b - n)).op = GateOp.or →
      ∀ r ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C (b - n)).inputs,
        r < b → value (zeroAt C j) x r = false)

lemma changed_sensitive_step {n : ℕ} (C : Circuit)
    (hC : PEqualNP.MetaComplexity.Monotone2 C)
    (x : Fin n → Bool) (j w : ℕ) (hw : Changed C x j w) (hne : w ≠ n + j) :
    ∃ a, SensitiveStep C x j a w := by
  obtain ⟨a, h, haw, ha, hac, hand, hor⟩ := changed_predecessor C hC x j w hw hne
  have hb := changed_bounds C x j w hw
  refine ⟨a, haw, hb.1, hb.2, ?_, hac, hw, ?_, ?_⟩
  · simpa only [PEqualNP.MetaComplexity.NestedCover.gateAt,
      List.getD_eq_getElem _ _ h] using ha
  · simpa only [PEqualNP.MetaComplexity.NestedCover.gateAt,
      List.getD_eq_getElem _ _ h] using hand
  · simpa only [PEqualNP.MetaComplexity.NestedCover.gateAt,
      List.getD_eq_getElem _ _ h] using hor

lemma changed_path {n : ℕ} (C : Circuit)
    (hC : PEqualNP.MetaComplexity.Monotone2 C) (x : Fin n → Bool) (j w : ℕ)
    (hw : Changed C x j w) :
    Relation.ReflTransGen (SensitiveStep C x j) (n + j) w := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases he : w = n + j
    · subst w
      exact Relation.ReflTransGen.refl
    · obtain ⟨a, ha⟩ := changed_sensitive_step C hC x j w hw he
      exact (ih a ha.1 ha.2.2.2.2.1).tail ha

lemma changed_after {n : ℕ} (C : Circuit)
    (hC : PEqualNP.MetaComplexity.Monotone2 C) (x : Fin n → Bool) (j w : ℕ)
    (hw : Changed C x j w) : n + j ≤ w := by
  have hp := changed_path C hC x j w hw
  clear hw
  induction hp with
  | refl => exact le_rfl
  | tail _ hstep ih => exact ih.trans hstep.1.le



def CleanWire {n : ℕ} (C : Circuit) (F : (Fin n → Bool) → Bool) (w : ℕ) : Prop :=
  ∀ x : Fin n → Bool, value C x w = true → F x = true

lemma value_gateAt {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ)
    (hn : n ≤ w) (hw : w < n + C.size) :
    value C x w = (PEqualNP.MetaComplexity.NestedCover.gateAt C (w - n)).op.eval
      ((PEqualNP.MetaComplexity.NestedCover.gateAt C (w - n)).inputs.map
        fun r => if r < w then value C x r else false) := by
  have hk : w - n < C.gates.length := by
    change w < n + C.gates.length at hw
    omega
  simpa only [PEqualNP.MetaComplexity.NestedCover.gateAt,
    List.getD_eq_getElem _ _ hk] using gate_value C x w hn hw

lemma or_input_clean {n : ℕ} (C : Circuit) (F : (Fin n → Bool) → Bool)
    (a w : ℕ) (hn : n ≤ w) (hw : w < n + C.size) (ha : a < w)
    (hai : a ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C (w - n)).inputs)
    (hop : (PEqualNP.MetaComplexity.NestedCover.gateAt C (w - n)).op = GateOp.or)
    (hclean : CleanWire C F w) : CleanWire C F a := by
  intro x hx
  apply hclean x
  rw [value_gateAt C x w hn hw, hop]
  simp only [GateOp.eval, List.any_eq_true, List.mem_map, id_eq]
  refine ⟨true, ⟨a, hai, ?_⟩, rfl⟩
  simp [ha, hx]

lemma first_changed_clean_and {n : ℕ} (C : Circuit)
    (hC : PEqualNP.MetaComplexity.Monotone2 C) (F : (Fin n → Bool) → Bool)
    (x : Fin n → Bool) (j o : ℕ)
    (ho : Changed C x j o) (hco : CleanWire C F o)
    (hjdirty : ¬ CleanWire C F (n + j)) :
    ∃ w a : ℕ, n + j < w ∧ Changed C x j w ∧ CleanWire C F w ∧
      (PEqualNP.MetaComplexity.NestedCover.gateAt C (w - n)).op = GateOp.and ∧
      SensitiveStep C x j a w ∧
      ∀ r < w, Changed C x j r → ¬ CleanWire C F r := by
  classical
  have hex : ∃ w, Changed C x j w ∧ CleanWire C F w := ⟨o, ho, hco⟩
  let w := Nat.find hex
  have hwp : Changed C x j w ∧ CleanWire C F w := Nat.find_spec hex
  have hleast (r : ℕ) (hr : r < w) (hrc : Changed C x j r) : ¬ CleanWire C F r := by
    intro hcl
    exact Nat.find_min hex hr ⟨hrc, hcl⟩
  have hafter := changed_after C hC x j w hwp.1
  have hne : w ≠ n + j := by
    intro h
    rw [h] at hwp
    exact hjdirty hwp.2
  have hstrict : n + j < w := by omega
  obtain ⟨a, has⟩ := changed_sensitive_step C hC x j w hwp.1 hne
  have hk : w - n < C.gates.length := by
    have ht := has.2.2.1
    change w < n + C.gates.length at ht
    omega
  have hop : (PEqualNP.MetaComplexity.NestedCover.gateAt C (w - n)).op = GateOp.and ∨
      (PEqualNP.MetaComplexity.NestedCover.gateAt C (w - n)).op = GateOp.or := by
    simpa only [PEqualNP.MetaComplexity.NestedCover.gateAt, List.getD_eq_getElem _ _ hk,
      Set.mem_insert_iff, Set.mem_singleton_iff] using
      (hC C.gates[w - n] (List.getElem_mem hk)).1
  have hand : (PEqualNP.MetaComplexity.NestedCover.gateAt C (w - n)).op = GateOp.and := by
    rcases hop with h | h
    · exact h
    · exact False.elim (hleast a has.1 has.2.2.2.2.1
        (or_input_clean C F a w has.2.1 has.2.2.1 has.1 has.2.2.2.1 h hwp.2))
  exact ⟨w, a, hstrict, hwp.1, hwp.2, hand, has, hleast⟩



def OrSensitiveStep {n : ℕ} (C : Circuit) (x : Fin n → Bool) (j a b : ℕ) : Prop :=
  SensitiveStep C x j a b ∧
    (PEqualNP.MetaComplexity.NestedCover.gateAt C (b - n)).op = GateOp.or

lemma changed_or_path_before {n : ℕ} (C : Circuit)
    (hC : PEqualNP.MetaComplexity.Monotone2 C) (F : (Fin n → Bool) → Bool)
    (x : Fin n → Bool) (j stop : ℕ)
    (hunclean : ∀ r < stop, Changed C x j r → ¬ CleanWire C F r)
    (hunique : ∀ r, n ≤ r → r < n + C.size →
      (PEqualNP.MetaComplexity.NestedCover.gateAt C (r - n)).op = GateOp.and →
      ¬ CleanWire C F r → r = n + j)
    (w : ℕ) (hws : w < stop) (hw : Changed C x j w) :
    Relation.ReflTransGen (OrSensitiveStep C x j) (n + j) w := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases he : w = n + j
    · subst w
      exact Relation.ReflTransGen.refl
    · obtain ⟨a, has⟩ := changed_sensitive_step C hC x j w hw he
      have hk : w - n < C.gates.length := by
        have hlow := has.2.1
        have ht := has.2.2.1
        change w < n + C.gates.length at ht
        omega
      have hop : (PEqualNP.MetaComplexity.NestedCover.gateAt C (w - n)).op = GateOp.and ∨
          (PEqualNP.MetaComplexity.NestedCover.gateAt C (w - n)).op = GateOp.or := by
        simpa only [PEqualNP.MetaComplexity.NestedCover.gateAt, List.getD_eq_getElem _ _ hk,
          Set.mem_insert_iff, Set.mem_singleton_iff] using
          (hC C.gates[w - n] (List.getElem_mem hk)).1
      have hor : (PEqualNP.MetaComplexity.NestedCover.gateAt C (w - n)).op = GateOp.or := by
        rcases hop with h | h
        · exact False.elim (he (hunique w has.2.1 has.2.2.1 h (hunclean w hws hw)))
        · exact h
      exact (ih a has.1 (has.1.trans hws) has.2.2.2.2.1).tail ⟨has, hor⟩

lemma first_changed_clean_and_or_path {n : ℕ} (C : Circuit)
    (hC : PEqualNP.MetaComplexity.Monotone2 C) (F : (Fin n → Bool) → Bool)
    (x : Fin n → Bool) (j o : ℕ)
    (ho : Changed C x j o) (hco : CleanWire C F o)
    (hjdirty : ¬ CleanWire C F (n + j))
    (hunique : ∀ r, n ≤ r → r < n + C.size →
      (PEqualNP.MetaComplexity.NestedCover.gateAt C (r - n)).op = GateOp.and →
      ¬ CleanWire C F r → r = n + j) :
    ∃ w a : ℕ, n + j < w ∧ Changed C x j w ∧ CleanWire C F w ∧
      (PEqualNP.MetaComplexity.NestedCover.gateAt C (w - n)).op = GateOp.and ∧
      SensitiveStep C x j a w ∧
      Relation.ReflTransGen (OrSensitiveStep C x j) (n + j) a := by
  obtain ⟨w, a, hjw, hw, hclean, hop, has, hfirst⟩ :=
    first_changed_clean_and C hC F x j o ho hco hjdirty
  exact ⟨w, a, hjw, hw, hclean, hop, has,
    changed_or_path_before C hC F x j w hfirst hunique a has.1 has.2.2.2.2.1⟩



lemma or_input_true {n : ℕ} (C : Circuit) (x : Fin n → Bool)
    (a w : ℕ) (hn : n ≤ w) (hw : w < n + C.size) (ha : a < w)
    (hai : a ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C (w - n)).inputs)
    (hop : (PEqualNP.MetaComplexity.NestedCover.gateAt C (w - n)).op = GateOp.or)
    (hat : value C x a = true) : value C x w = true := by
  rw [value_gateAt C x w hn hw, hop]
  simp only [GateOp.eval, List.any_eq_true, List.mem_map, id_eq]
  refine ⟨true, ⟨a, hai, ?_⟩, rfl⟩
  simp [ha, hat]

lemma or_sensitive_path_true {n : ℕ} (C : Circuit) (x y : Fin n → Bool) (j a b : ℕ)
    (hp : Relation.ReflTransGen (OrSensitiveStep C x j) a b)
    (ha : value C y a = true) : value C y b = true := by
  induction hp with
  | refl => exact ha
  | tail _ hs ih =>
    exact or_input_true C y _ _ hs.1.2.1 hs.1.2.2.1 hs.1.1 hs.1.2.2.2.1 hs.2 ih

lemma clean_and_mask {n : ℕ} (C : Circuit) (F : (Fin n → Bool) → Bool)
    (w a b g : ℕ) (c : Fin n) (hn : n ≤ w) (hw : w < n + C.size)
    (ha : a < w) (hb : b < w)
    (hg : PEqualNP.MetaComplexity.NestedCover.gateAt C (w - n) = ⟨GateOp.and, [a, b]⟩)
    (hclean : CleanWire C F w)
    (hga : ∀ y : Fin n → Bool, value C y g = true → value C y a = true)
    (hcb : ∀ y : Fin n → Bool, y c = true → value C y b = true) :
    ∀ y : Fin n → Bool, value C y g = true → y c = true → F y = true := by
  intro y hgy hcy
  apply hclean y
  rw [value_gateAt C y w hn hw, hg]
  simp [GateOp.eval, ha, hb, hga y hgy, hcb y hcy]

end PEqualNP.Outside.L_meta_1477.SensitivePath
