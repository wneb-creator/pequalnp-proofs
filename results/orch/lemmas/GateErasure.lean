import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1477.GateErasure
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



def redirect (cut miss i : ℕ) : ℕ :=
  if i = cut then miss else if cut < i then i - 1 else i

lemma redirect_getD (w : List Bool) (cut miss : ℕ)
    (hm : w.length ≤ miss) (hz : w.getD cut false = false) (i : ℕ) :
    (w.eraseIdx cut).getD (redirect cut miss i) false = w.getD i false := by
  by_cases he : i = cut
  · subst i
    rw [show redirect cut miss cut = miss by simp [redirect]]
    rw [List.getD_eq_default _ _ ((List.length_eraseIdx_le w cut).trans hm), hz]
  · by_cases hi : i < cut
    · have hn : ¬ cut < i := by omega
      simp only [redirect, ite_eq_right he, ite_eq_right hn]
      simp only [List.getD_eq_getElem?_getD, List.getElem?_eraseIdx_of_lt hi]
    · have hci : cut < i := by omega
      simp only [redirect, ite_eq_right he, ite_eq_left hci, List.getD_eq_getElem?_getD]
      rw [List.getElem?_eraseIdx_of_ge (by omega)]
      simp only [show i - 1 + 1 = i by omega]

def mappedGate (cut miss : ℕ) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map (redirect cut miss)⟩

lemma mappedGate_eval (w : List Bool) (cut miss : ℕ)
    (hm : w.length ≤ miss) (hz : w.getD cut false = false) (g : Gate) :
    (mappedGate cut miss g).op.eval
        ((mappedGate cut miss g).inputs.map fun i => (w.eraseIdx cut).getD i false) =
      g.op.eval (g.inputs.map fun i => w.getD i false) := by
  simp only [mappedGate, List.map_map]
  congr 1
  apply List.map_congr_left
  intro i _
  exact redirect_getD w cut miss hm hz i

lemma run_map_erase (gs : List Gate) (cut miss : ℕ) :
    ∀ w : List Bool, cut < w.length → w.getD cut false = false →
      w.length + gs.length ≤ miss →
      run (gs.map (mappedGate cut miss)) (w.eraseIdx cut) = (run gs w).eraseIdx cut := by
  induction gs with
  | nil => intro w _ _ _; rfl
  | cons g gs ih =>
    intro w hc hz hm
    simp only [List.map_cons, run_cons]
    rw [mappedGate_eval w cut miss (by simp only [List.length_cons] at hm; omega) hz]
    rw [← List.eraseIdx_append_of_lt_length hc]
    apply ih
    · simp only [List.length_append, List.length_singleton]; omega
    · rw [List.getD_append _ _ _ _ hc]; exact hz
    · simp only [List.length_append, List.length_singleton, List.length_cons, List.length_nil] at hm ⊢
      omega


lemma run_append (xs ys : List Gate) (w : List Bool) :
    run (xs ++ ys) w = run ys (run xs w) := by
  simp only [run, List.foldl_append]

def prune (n : ℕ) (C : Circuit) (j : ℕ) : Circuit :=
  { gates := C.gates.take j ++
      (C.gates.drop (j + 1)).map (mappedGate (n + j) (n + C.size))
    output := redirect (n + j) (n + C.size) C.output }

lemma prune_size (n : ℕ) (C : Circuit) (j : ℕ) (hj : j < C.size) :
    (prune n C j).size + 1 = C.size := by
  simp only [prune, Circuit.size, List.length_append, List.length_take,
    List.length_map, List.length_drop]
  unfold Circuit.size at hj
  omega

lemma prune_monotone (n : ℕ) (C : Circuit) (j : ℕ)
    (hC : PEqualNP.MetaComplexity.Monotone2 C) :
    PEqualNP.MetaComplexity.Monotone2 (prune n C j) := by
  intro g hg
  rcases List.mem_append.mp hg with hg | hg
  · exact hC g (List.mem_of_mem_take hg)
  · obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hg
    simpa [mappedGate] using hC a (List.mem_of_mem_drop ha)

lemma prune_eval (n : ℕ) (C : Circuit) (j : ℕ) (hj : j < C.size)
    (x : List Bool) (hx : x.length = n) :
    (prune n C j).eval x =
      (run (C.gates.drop (j + 1)) (run (C.gates.take j) x ++ [false])).getD C.output false := by
  let a := run (C.gates.take j) x
  let w := a ++ [false]
  have hja : j < C.gates.length := hj
  have hal : a.length = n + j := by simp [a, run_length, hx, Nat.min_eq_left hja.le]
  have hwc : n + j < w.length := by simp [w, hal]
  have hwl : w.length + (C.gates.drop (j + 1)).length = n + C.size := by
    simp only [w, List.length_append, List.length_singleton, hal, List.length_drop, Circuit.size]
    omega
  have hwz : w.getD (n + j) false = false := by
    rw [← hal]
    simp [w]
  have hwe : w.eraseIdx (n + j) = a := by
    rw [← hal]
    simp [w, List.eraseIdx_append_of_length_le]
  have hrun : (prune n C j).wires x =
      (run (C.gates.drop (j + 1)) w).eraseIdx (n + j) := by
    change run ((prune n C j).gates) x = _
    simp only [prune, run_append]
    change run ((C.gates.drop (j + 1)).map (mappedGate (n + j) (n + C.size))) a = _
    rw [← hwe]
    exact run_map_erase _ _ _ w hwc hwz hwl.le
  change ((prune n C j).wires x).getD (redirect (n + j) (n + C.size) C.output) false = _
  rw [hrun]
  apply redirect_getD
  · rw [run_length, hwl]
  · rw [run_getD _ _ _ hwc]
    exact hwz

lemma wires_split_gate (C : Circuit) (x : List Bool) (j : ℕ) (hj : j < C.gates.length) :
    C.wires x =
      run (C.gates.drop (j + 1))
        (run (C.gates.take j) x ++
          [C.gates[j].op.eval
            (C.gates[j].inputs.map fun i => (run (C.gates.take j) x).getD i false)]) := by
  have hs : C.gates = C.gates.take j ++ C.gates[j] :: C.gates.drop (j + 1) := by simp
  change run C.gates x = _
  conv_lhs => rw [hs]
  rw [run_append, run_cons]

lemma prune_eval_of_false (n : ℕ) (C : Circuit) (j : ℕ) (hj : j < C.size)
    (x : List Bool) (hx : x.length = n)
    (hz : (C.wires x).getD (n + j) false = false) :
    (prune n C j).eval x = C.eval x := by
  have hja : j < C.gates.length := hj
  let a := run (C.gates.take j) x
  have hal : a.length = n + j := by simp [a, run_length, hx, Nat.min_eq_left hja.le]
  have hv : (C.wires x).getD (n + j) false =
      C.gates[j].op.eval (C.gates[j].inputs.map fun i => a.getD i false) := by
    rw [wires_split_gate C x j hja]
    change (run (C.gates.drop (j + 1)) (a ++ [_])).getD (n + j) false = _
    rw [run_getD _ _ _ (by simp [hal]), ← hal]
    simp [a]
  rw [hv] at hz
  rw [prune_eval n C j hj x hx]
  unfold Circuit.eval
  rw [wires_split_gate C x j hja]
  change (run (C.gates.drop (j + 1)) (a ++ [false])).getD C.output false = _
  rw [show C.gates[j].op.eval
    (C.gates[j].inputs.map fun i => (run (C.gates.take j) x).getD i false) = false from hz]


def LeList (a b : List Bool) : Prop :=
  ∀ i, a.getD i false = true → b.getD i false = true

lemma leList_snoc (a b : List Bool) (c d : Bool)
    (hl : a.length = b.length) (hab : LeList a b) (hcd : c = true → d = true) :
    LeList (a ++ [c]) (b ++ [d]) := by
  intro i hi
  by_cases hia : i < a.length
  · rw [List.getD_append _ _ _ _ hia] at hi
    rw [List.getD_append _ _ _ _ (by omega)]
    exact hab i hi
  · rw [List.getD_append_right _ _ _ _ (by omega)] at hi
    rw [List.getD_append_right _ _ _ _ (by omega), ← hl]
    by_cases he : i - a.length = 0
    · rw [he] at hi ⊢
      simp only [List.getD_cons_zero] at hi ⊢
      exact hcd hi
    · obtain ⟨k, hk⟩ : ∃ k, i - a.length = k + 1 := ⟨i - a.length - 1, by omega⟩
      rw [hk] at hi
      simp at hi

lemma gate_eval_mono (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or)
    (l : List ℕ) (f g : ℕ → Bool) (h : ∀ i, f i = true → g i = true) :
    op.eval (l.map f) = true → op.eval (l.map g) = true := by
  rcases hop with rfl | rfl
  · simp only [GateOp.eval, List.all_eq_true, List.mem_map, id_eq]
    intro H x hx
    obtain ⟨i, hi, rfl⟩ := hx
    exact h i (H (f i) ⟨i, hi, rfl⟩)
  · simp only [GateOp.eval, List.any_eq_true, List.mem_map, id_eq]
    rintro ⟨x, ⟨i, hi, rfl⟩, hx⟩
    exact ⟨g i, ⟨i, hi, rfl⟩, h i hx⟩

lemma run_mono (gs : List Gate)
    (hgs : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) :
    ∀ a b : List Bool, a.length = b.length → LeList a b →
      LeList (run gs a) (run gs b) := by
  induction gs with
  | nil => intro a b _ hab; exact hab
  | cons g gs ih =>
    intro a b hl hab
    rw [run_cons, run_cons]
    apply ih (fun g' hg' => hgs g' (List.mem_cons_of_mem _ hg'))
    · simp [hl]
    · apply leList_snoc a b _ _ hl hab
      exact gate_eval_mono g.op (hgs g List.mem_cons_self) g.inputs _ _ hab

lemma wires_mono {n : ℕ} (C : Circuit) (hC : PEqualNP.MetaComplexity.Monotone2 C)
    (x y : Fin n → Bool) (hxy : ∀ i, x i = true → y i = true) (w : ℕ) :
    (C.wires (List.ofFn x)).getD w false = true →
      (C.wires (List.ofFn y)).getD w false = true := by
  apply run_mono C.gates
  · intro g hg
    have h := (hC g hg).1
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using h
  · simp
  · intro i hi
    by_cases hin : i < n
    · simpa [hin] using hxy ⟨i, hin⟩ (by simpa [hin] using hi)
    · simp [hin] at hi

lemma prune_eval_le (n : ℕ) (C : Circuit) (j : ℕ) (hj : j < C.size)
    (hC : PEqualNP.MetaComplexity.Monotone2 C) (x : List Bool) (hx : x.length = n) :
    (prune n C j).eval x = true → C.eval x = true := by
  rw [prune_eval n C j hj x hx]
  unfold Circuit.eval
  rw [wires_split_gate C x j hj]
  apply run_mono (C.gates.drop (j + 1))
  · intro g hg
    have h := (hC g (List.mem_of_mem_drop hg)).1
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using h
  · simp
  · apply leList_snoc _ _ _ _ rfl (fun _ h => h)
    simp

lemma minimal_gate_fires_on_basis {n : ℕ} (C : Circuit)
    (hmin : PEqualNP.MetaComplexity.IsMinimalMonoCircuit n C)
    (P : (Fin n → Bool) → Prop)
    (hcover : ∀ x : Fin n → Bool, C.eval (List.ofFn x) = true →
      ∃ y : Fin n → Bool, P y ∧ C.eval (List.ofFn y) = true ∧
        ∀ i, y i = true → x i = true)
    (j : ℕ) (hj : j < C.size) :
    ∃ y : Fin n → Bool, P y ∧ (C.wires (List.ofFn y)).getD (n + j) false = true := by
  classical
  by_contra hnone
  have hz (y : Fin n → Bool) (hy : P y) :
      (C.wires (List.ofFn y)).getD (n + j) false = false := by
    apply Bool.eq_false_iff.mpr
    intro h
    exact hnone ⟨y, hy, h⟩
  let D := prune n C j
  have hD : PEqualNP.MetaComplexity.Monotone2 D := prune_monotone n C j hmin.1
  have hev (x : Fin n → Bool) : D.eval (List.ofFn x) = C.eval (List.ofFn x) := by
    cases hx : C.eval (List.ofFn x) with
    | false =>
      apply Bool.eq_false_iff.mpr
      intro hd
      have ht := prune_eval_le n C j hj hmin.1 (List.ofFn x) (by simp) hd
      simp [hx] at ht
    | true =>
      obtain ⟨y, hy, hyt, hxy⟩ := hcover x hx
      have hDy : D.eval (List.ofFn y) = true := by
        change (prune n C j).eval (List.ofFn y) = true
        rw [prune_eval_of_false n C j hj (List.ofFn y) (by simp) (hz y hy), hyt]
      exact wires_mono D hD y x hxy D.output hDy
  have hsize : C.size ≤ D.size := by
    apply hmin.2 D hD
    funext x
    exact hev x
  have hd := prune_size n C j hj
  change D.size + 1 = C.size at hd
  omega


lemma minimal_graph_gate_fires {n : ℕ} (C : Circuit)
    (hmin : PEqualNP.MetaComplexity.IsMinimalMonoCircuit n C)
    (G : Fin n → Fin n → Prop)
    (hcorrect : ∀ x : Fin n → Bool, C.eval (List.ofFn x) = true ↔
      ∃ u v, G u v ∧ x u = true ∧ x v = true)
    (j : ℕ) (hj : j < C.size) :
    ∃ u v, G u v ∧
      (C.wires (List.ofFn (fun i => decide (i = u ∨ i = v)))).getD (n + j) false = true := by
  classical
  let P := fun y : Fin n → Bool =>
    ∃ u v, G u v ∧ y = (fun i => decide (i = u ∨ i = v))
  have hcover (x : Fin n → Bool) (hx : C.eval (List.ofFn x) = true) :
      ∃ y : Fin n → Bool, P y ∧ C.eval (List.ofFn y) = true ∧
        ∀ i, y i = true → x i = true := by
    obtain ⟨u, v, huv, hu, hv⟩ := (hcorrect x).mp hx
    refine ⟨(fun i => decide (i = u ∨ i = v)), ⟨u, v, huv, rfl⟩, ?_, ?_⟩
    · apply (hcorrect _).mpr
      exact ⟨u, v, huv, by simp, by simp⟩
    · intro i hi
      rcases of_decide_eq_true hi with rfl | rfl <;> assumption
  obtain ⟨y, ⟨u, v, huv, rfl⟩, hfire⟩ := minimal_gate_fires_on_basis C hmin P hcover j hj
  exact ⟨u, v, huv, hfire⟩

end PEqualNP.Outside.L_meta_1477.GateErasure
