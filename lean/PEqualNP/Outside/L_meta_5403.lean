import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_5403

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge

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

lemma gate_mono {n : ℕ} (C : Circuit) (k : ℕ) (hk : k < C.gates.length)
    (hop : C.gates[k].op = GateOp.and ∨ C.gates[k].op = GateOp.or)
    (x y : Fin n → Bool)
    (h : ∀ r ∈ C.gates[k].inputs, r < n + k → value C x r = true → value C y r = true) :
    value C x (n + k) = true → value C y (n + k) = true := by
  have hw : n + k < n + C.size := by unfold Circuit.size; omega
  have hx := gate_value C x (n + k) (by omega) hw
  have hy := gate_value C y (n + k) (by omega) hw
  simp only [Nat.add_sub_cancel_left] at hx hy
  rw [hx, hy]
  have hr (r : ℕ) (hm : r ∈ C.gates[k].inputs) :
      (if r < n + k then value C x r else false) = true →
      (if r < n + k then value C y r else false) = true := by
    by_cases h' : r < n + k
    · simpa [h'] using h r hm h'
    · simp [h']
  rcases hop with hop | hop
  · simp only [hop, GateOp.eval, List.all_eq_true, id_eq]
    intro hx b hb
    obtain ⟨r, hm, rfl⟩ := List.mem_map.mp hb
    exact hr r hm (hx _ (List.mem_map.mpr ⟨r, hm, rfl⟩))
  · simp only [hop, GateOp.eval, List.any_eq_true, id_eq]
    intro hx
    obtain ⟨b, hb, rfl⟩ := hx
    obtain ⟨r, hm, hv⟩ := List.mem_map.mp hb
    exact ⟨_, List.mem_map.mpr ⟨r, hm, rfl⟩, hr r hm hv⟩

lemma and_value {n : ℕ} (C : Circuit) (k : ℕ) (hk : k < C.gates.length)
    (hop : C.gates[k].op = GateOp.and) (x : Fin n → Bool) :
    value C x (n + k) = true ↔ ∀ r ∈ C.gates[k].inputs, r < n + k ∧ value C x r = true := by
  have hw : n + k < n + C.size := by unfold Circuit.size; omega
  have hx := gate_value C x (n + k) (by omega) hw
  simp only [Nat.add_sub_cancel_left] at hx
  rw [hx, hop]
  simp [GateOp.eval]

lemma mono {n : ℕ} (C : Circuit) (x y : Fin n → Bool) (h : ∀ v, x v = true → y v = true)
    (hN : ∀ k, ∀ hk : k < C.gates.length,
      ¬ (C.gates[k].op = GateOp.and ∨ C.gates[k].op = GateOp.or) →
      value C x (n + k) = true → value C y (n + k) = true) (w : ℕ) :
    value C x w = true → value C y w = true := by
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    by_cases hn : w < n
    · let p : Fin n := ⟨w, hn⟩
      change value C x p = true → value C y p = true
      simpa only [input_value] using h p
    by_cases hw : w < n + C.gates.length
    · have hk : w - n < C.gates.length := by omega
      have hwk : w = n + (w - n) := by omega
      rw [hwk]
      by_cases hop : C.gates[w - n].op = GateOp.and ∨ C.gates[w - n].op = GateOp.or
      · exact gate_mono C (w - n) hk hop x y fun r _ hlt => ih r (by omega)
      · exact hN (w - n) hk hop
    · simp [missing_value C x w (by unfold Circuit.size; omega)]

lemma andOr_mono {n : ℕ} (C : Circuit) (hC : AndOrOnly C)
    (x y : Fin n → Bool) (hxy : ∀ i, x i = true → y i = true) (w : ℕ) :
    value C x w = true → value C y w = true := by
  apply mono C x y hxy
  intro k hk hn
  exact (hn (hC _ (List.getElem_mem hk))).elim

lemma and_gate_true {n : ℕ} (C : Circuit) (t : ℕ) (hA : IsAO2 n C) (ht : t < C.gates.length)
    (hop : (gateAt C t).op = GateOp.and) (x : Fin n → Bool)
    (h0 : value C x (opnd C t 0) = true) (h1 : value C x (opnd C t 1) = true) :
    gateVal n C t x = true := by
  have hg : gateAt C t = C.gates[t] := by simp [gateAt, ht]
  have hlen : C.gates[t].inputs.length = 2 := hA.2.2 _ (List.getElem_mem ht)
  obtain ⟨a, c, hac⟩ := List.length_eq_two.mp hlen
  have hrb := hA.2.1 t ht
  rw [hg, hac] at hrb
  have hop' : C.gates[t].op = GateOp.and := by rw [← hg]; exact hop
  have h0' : value C x a = true := by simpa [opnd, hg, hac] using h0
  have h1' : value C x c = true := by simpa [opnd, hg, hac] using h1
  show value C x (n + t) = true
  rw [and_value C t ht hop' x, hac]
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact ⟨hrb _ (by simp), h0'⟩
  · exact ⟨hrb _ (by simp), h1'⟩

lemma killer {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) (t : ℕ)
    (b : Fin 2) (u v w : Fin n) (hA : IsAO2 n C) (ht : t < C.gates.length)
    (hop : (gateAt C t).op = GateOp.and) (hB : BelowF G C t) (huv : ¬ G.Adj u v)
    (h1 : wireVal n C (opnd C t b) (pairInput u v) = true)
    (h2 : wireVal n C (opnd C t (1 - b)) (pairInput w w) = true) :
    G.Adj w u ∨ G.Adj w v := by
  let x : Fin n → Bool := fun z => decide (z = u ∨ z = v ∨ z = w)
  have m1 : value C x (opnd C t b) = true :=
    andOr_mono C hA.1 (pairInput u v) x (by
      intro i hi
      simp only [pairInput, decide_eq_true_eq, x] at hi ⊢
      tauto) _ h1
  have m2 : value C x (opnd C t (1 - b)) = true :=
    andOr_mono C hA.1 (pairInput w w) x (by
      intro i hi
      simp only [pairInput, decide_eq_true_eq, x] at hi ⊢
      tauto) _ h2
  have hall : value C x (opnd C t 0) = true ∧ value C x (opnd C t 1) = true := by
    obtain rfl | rfl : b = 0 ∨ b = 1 := by fin_cases b <;> simp
    · exact ⟨m1, m2⟩
    · exact ⟨m2, m1⟩
  have hg := and_gate_true C t hA ht hop x hall.1 hall.2
  have hF := hB x hg
  simp only [graphFun, Finset.notMem_empty, false_and, exists_false, decide_false,
    Bool.false_or, decide_eq_true_eq, x] at hF
  obtain ⟨a, c, hac, ha, hc⟩ := hF
  rcases ha with rfl | rfl | rfl <;> rcases hc with rfl | rfl | rfl <;>
    first
    | exact (G.irrefl hac).elim
    | exact (huv hac).elim
    | exact (huv hac.symm).elim
    | exact Or.inl hac.symm
    | exact Or.inr hac.symm
    | exact Or.inl hac
    | exact Or.inr hac

end PEqualNP.Outside.L_meta_5403

theorem PEqualNP.Outside.L_meta_5403 : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : PEqualNP.CircuitLowerBounds.Circuit) (s : Fin n → Bool) (t1 t2 : ℕ) (b1 b2 : Fin 2) (u1 v1 u2 v2 w1 w2 : Fin n), PEqualNP.TopForm.IsAO2 n C → PEqualNP.TopForm.NoFourCycle G → (∀ x y : Fin n, G.Adj x y → s x ≠ s y) → t1 < C.gates.length → t2 < C.gates.length → (PEqualNP.MetaComplexity.NestedCover.gateAt C t1).op = PEqualNP.CircuitLowerBounds.GateOp.and → (PEqualNP.MetaComplexity.NestedCover.gateAt C t2).op = PEqualNP.CircuitLowerBounds.GateOp.and → PEqualNP.TopForm.BelowF G C t1 → PEqualNP.TopForm.BelowF G C t2 → PEqualNP.TopForm.opnd C t1 (1 - b1) = PEqualNP.TopForm.opnd C t2 (1 - b2) → ¬ G.Adj u1 v1 → ¬ G.Adj u2 v2 → s u1 = s w1 → s u2 = s w1 → s v1 ≠ s w1 → s v2 ≠ s w1 → v1 ≠ v2 → s w2 = s w1 → PEqualNP.CleanedNonEdge.wireVal n C (PEqualNP.TopForm.opnd C t1 b1) (PEqualNP.EdgeOwnership.pairInput u1 v1) = true → PEqualNP.CleanedNonEdge.wireVal n C (PEqualNP.TopForm.opnd C t2 b2) (PEqualNP.EdgeOwnership.pairInput u2 v2) = true → PEqualNP.CleanedNonEdge.wireVal n C (PEqualNP.TopForm.opnd C t1 (1 - b1)) (PEqualNP.EdgeOwnership.pairInput w1 w1) = true → PEqualNP.CleanedNonEdge.wireVal n C (PEqualNP.TopForm.opnd C t1 (1 - b1)) (PEqualNP.EdgeOwnership.pairInput w2 w2) = true → w1 = w2 := by
  intro n G _ C s t1 t2 b1 b2 u1 v1 u2 v2 w1 w2 hA hN hs ht1 ht2 hop1 hop2 hB1 hB2 hK hu1 hu2 hsu1 hsu2 hsv1 hsv2 hv12 hsw2 hp1 hp2 hk1 hk2
  have hk1' : PEqualNP.CleanedNonEdge.wireVal n C (PEqualNP.TopForm.opnd C t2 (1 - b2)) (PEqualNP.EdgeOwnership.pairInput w1 w1) = true := by
    rw [← hK]; exact hk1
  have hk2' : PEqualNP.CleanedNonEdge.wireVal n C (PEqualNP.TopForm.opnd C t2 (1 - b2)) (PEqualNP.EdgeOwnership.pairInput w2 w2) = true := by
    rw [← hK]; exact hk2
  have e1 := PEqualNP.Outside.L_meta_5403.killer G C t1 b1 u1 v1 w1 hA ht1 hop1 hB1 hu1 hp1 hk1
  have e2 := PEqualNP.Outside.L_meta_5403.killer G C t1 b1 u1 v1 w2 hA ht1 hop1 hB1 hu1 hp1 hk2
  have e3 := PEqualNP.Outside.L_meta_5403.killer G C t2 b2 u2 v2 w1 hA ht2 hop2 hB2 hu2 hp2 hk1'
  have e4 := PEqualNP.Outside.L_meta_5403.killer G C t2 b2 u2 v2 w2 hA ht2 hop2 hB2 hu2 hp2 hk2'
  have a1 : G.Adj w1 v1 := e1.resolve_left (fun h => hs _ _ h hsu1.symm)
  have a2 : G.Adj w2 v1 := e2.resolve_left (fun h => hs _ _ h (hsw2.trans hsu1.symm))
  have a3 : G.Adj w1 v2 := e3.resolve_left (fun h => hs _ _ h hsu2.symm)
  have a4 : G.Adj w2 v2 := e4.resolve_left (fun h => hs _ _ h (hsw2.trans hsu2.symm))
  by_contra hne
  have hc := hN w1 w2 hne
  have hsub : ({v1, v2} : Finset (Fin n)) ⊆ Finset.univ.filter fun z => G.Adj w1 z ∧ G.Adj w2 z := by
    intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl
    · simp [a1, a2]
    · simp [a3, a4]
  have hle := Finset.card_le_card hsub
  rw [Finset.card_pair hv12] at hle
  omega
