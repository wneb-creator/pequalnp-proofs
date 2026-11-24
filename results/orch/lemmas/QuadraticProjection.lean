import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1477.GateReplacement

open PEqualNP.CircuitLowerBounds

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma step_len (w : List Bool) (g : Gate) : (step w g).length = w.length + 1 := by
  simp [step]

lemma step_lt (w : List Bool) (g : Gate) (i : ℕ) (hi : i < w.length) :
    (step w g).getD i false = w.getD i false := by
  simp [step, List.getD, List.getElem?_append_left hi]

lemma step_last (w : List Bool) (g : Gate) (k : ℕ) (hk : k = w.length) :
    (step w g).getD k false = g.op.eval (g.inputs.map fun i => w.getD i false) := by
  subst hk
  simp [step, List.getD]

def W {n : ℕ} (gs : List Gate) (x : Fin n → Bool) : List Bool :=
  gs.foldl step (List.ofFn x)

lemma W_len {n : ℕ} (gs : List Gate) (x : Fin n → Bool) :
    (W gs x).length = n + gs.length := by
  have h : ∀ (gs : List Gate) (w : List Bool), (gs.foldl step w).length = w.length + gs.length := by
    intro gs
    induction gs with
    | nil => intro w; simp
    | cons g gs ih =>
      intro w
      rw [List.foldl_cons, ih, step_len, List.length_cons]
      omega
  rw [W, h]
  simp

lemma W_snoc {n : ℕ} (gs : List Gate) (g : Gate) (x : Fin n → Bool) :
    W (gs ++ [g]) x = step (W gs x) g := by
  simp [W, List.foldl_append]

lemma W_val {n : ℕ} (gs : List Gate) (g : Gate) (x : Fin n → Bool) (t : ℕ) :
    (W (gs ++ [g]) x).getD t false =
      if t = n + gs.length then g.op.eval (g.inputs.map fun i => (W gs x).getD i false)
      else (W gs x).getD t false := by
  rw [W_snoc]
  by_cases ht : t = n + gs.length
  · rw [if_pos ht, step_last _ _ _ (by rw [W_len]; exact ht)]
  · rw [if_neg ht]
    by_cases hlt : t < n + gs.length
    · exact step_lt _ _ _ (by rw [W_len]; exact hlt)
    · rw [List.getD_eq_default _ _ (by rw [step_len, W_len]; omega),
        List.getD_eq_default _ _ (by rw [W_len]; omega)]

lemma bool_le_iff_true (a b : Bool) : a ≤ b ↔ (a = true → b = true) := by
  cases a <;> cases b <;> decide

lemma op_mono (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or)
    (ins : List ℕ) (f g : ℕ → Bool) (h : ∀ i, f i ≤ g i) :
    op.eval (ins.map f) ≤ op.eval (ins.map g) := by
  rw [bool_le_iff_true]
  intro hf
  rcases hop with rfl | rfl
  · simp only [GateOp.eval, List.all_eq_true] at hf ⊢
    intro b hb
    rcases List.mem_map.mp hb with ⟨i, hi, rfl⟩
    exact (bool_le_iff_true _ _).mp (h i)
      (hf (f i) (List.mem_map.mpr ⟨i, hi, rfl⟩))
  · simp only [GateOp.eval, List.any_eq_true] at hf ⊢
    rcases hf with ⟨b, hb, hbt⟩
    rcases List.mem_map.mp hb with ⟨i, hi, rfl⟩
    exact ⟨g i, List.mem_map.mpr ⟨i, hi, rfl⟩,
      (bool_le_iff_true _ _).mp (h i) hbt⟩

lemma step_mono (w v : List Bool) (g : Gate)
    (hop : g.op = GateOp.and ∨ g.op = GateOp.or)
    (hlen : w.length = v.length) (h : ∀ i, w.getD i false ≤ v.getD i false) :
    ∀ i, (step w g).getD i false ≤ (step v g).getD i false := by
  intro i
  by_cases hi : i < w.length
  · rw [step_lt _ _ _ hi, step_lt _ _ _ (by omega)]
    exact h i
  · by_cases heq : i = w.length
    · rw [step_last _ _ _ heq, step_last _ _ _ (heq.trans hlen)]
      exact op_mono g.op hop _ _ _ h
    · rw [List.getD_eq_default _ _ (by rw [step_len]; omega),
        List.getD_eq_default _ _ (by rw [step_len]; omega)]

lemma fold_mono (gs : List Gate)
    (hgs : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
    (w v : List Bool) (hlen : w.length = v.length)
    (h : ∀ i, w.getD i false ≤ v.getD i false) :
    ∀ i, (gs.foldl step w).getD i false ≤ (gs.foldl step v).getD i false := by
  induction gs generalizing w v with
  | nil => exact h
  | cons g gs ih =>
    simp only [List.foldl_cons]
    apply ih (fun a ha => hgs a (List.mem_cons_of_mem _ ha))
    · simp only [step_len, hlen]
    · exact step_mono w v g (hgs g (by simp)) hlen h

lemma fold_preserves (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl step w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [List.foldl_cons, ih _ (by rw [step_len]; omega), step_lt _ _ _ hi]

def zeroGate : Gate := ⟨GateOp.or, []⟩

lemma step_zero_le (w : List Bool) (g : Gate) :
    ∀ i, (step w zeroGate).getD i false ≤ (step w g).getD i false := by
  intro i
  by_cases hi : i < w.length
  · rw [step_lt _ _ _ hi, step_lt _ _ _ hi]
  · by_cases heq : i = w.length
    · rw [step_last _ _ _ heq, step_last _ _ _ heq]
      simp [zeroGate, GateOp.eval]
    · rw [List.getD_eq_default _ _ (by rw [step_len]; omega),
        List.getD_eq_default _ _ (by rw [step_len]; omega)]


def gateValue (w : List Bool) (g : Gate) : Bool :=
  g.op.eval (g.inputs.map fun i => w.getD i false)

lemma step_replace_le (w : List Bool) (g h : Gate)
    (hle : gateValue w h ≤ gateValue w g) :
    ∀ i, (step w h).getD i false ≤ (step w g).getD i false := by
  intro i
  by_cases hi : i < w.length
  · rw [step_lt _ _ _ hi, step_lt _ _ _ hi]
  · by_cases heq : i = w.length
    · rw [step_last _ _ _ heq, step_last _ _ _ heq]
      exact hle
    · rw [List.getD_eq_default _ _ (by rw [step_len]; omega),
        List.getD_eq_default _ _ (by rw [step_len]; omega)]

lemma set_gate_le (gs : List Gate)
    (hgs : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
    (w : List Bool) (k : ℕ) (h : Gate)
    (hle : gateValue ((gs.take k).foldl step w) h ≤
      gateValue ((gs.take k).foldl step w) (gs.getD k zeroGate)) :
    ∀ i, ((gs.set k h).foldl step w).getD i false ≤
      (gs.foldl step w).getD i false := by
  induction gs generalizing w k with
  | nil => intro i; simp
  | cons g gs ih =>
    cases k with
    | zero =>
      simp only [List.set_cons_zero, List.foldl_cons]
      apply fold_mono gs (fun a ha => hgs a (List.mem_cons_of_mem _ ha))
      · simp only [step_len]
      · apply step_replace_le
        simpa using hle
    | succ k =>
      simpa only [List.set_cons_succ, List.foldl_cons] using
        ih (fun a ha => hgs a (List.mem_cons_of_mem _ ha)) (step w g) k
          (by simpa using hle)

lemma set_gate_eq_of_local_eq (gs : List Gate) (w : List Bool) (k : ℕ) (h : Gate)
    (heq : gateValue ((gs.take k).foldl step w) h =
      gateValue ((gs.take k).foldl step w) (gs.getD k zeroGate)) :
    (gs.set k h).foldl step w = gs.foldl step w := by
  induction gs generalizing w k with
  | nil => simp
  | cons g gs ih =>
    cases k with
    | zero =>
      have hs : step w h = step w g := by
        have he : gateValue w h = gateValue w g := by simpa using heq
        exact congrArg (fun b => w ++ [b]) he
      simp only [List.set_cons_zero, List.foldl_cons, hs]
    | succ k =>
      simpa only [List.set_cons_succ, List.foldl_cons] using
        ih (step w g) k (by simpa using heq)

lemma set_zero_le_set_gate (gs : List Gate)
    (hgs : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
    (w : List Bool) (k : ℕ) (h : Gate) :
    ∀ i, ((gs.set k zeroGate).foldl step w).getD i false ≤
      ((gs.set k h).foldl step w).getD i false := by
  induction gs generalizing w k with
  | nil => intro i; simp
  | cons g gs ih =>
    cases k with
    | zero =>
      simp only [List.set_cons_zero, List.foldl_cons]
      apply fold_mono gs (fun a ha => hgs a (List.mem_cons_of_mem _ ha))
      · simp only [step_len]
      · exact step_zero_le w h
    | succ k =>
      simpa only [List.set_cons_succ, List.foldl_cons] using
        ih (fun a ha => hgs a (List.mem_cons_of_mem _ ha)) (step w g) k

lemma set_gate_true_of_sensitive_preserved (gs : List Gate)
    (hgs : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
    (w : List Bool) (k out : ℕ) (h : Gate)
    (hout : (gs.foldl step w).getD out false = true)
    (hsensitive : ((gs.set k zeroGate).foldl step w).getD out false = false →
      gateValue ((gs.take k).foldl step w) h =
        gateValue ((gs.take k).foldl step w) (gs.getD k zeroGate)) :
    ((gs.set k h).foldl step w).getD out false = true := by
  cases hz : ((gs.set k zeroGate).foldl step w).getD out false with
  | false => rw [set_gate_eq_of_local_eq gs w k h (hsensitive hz)]; exact hout
  | true => exact Bool.le_iff_imp.mp (set_zero_le_set_gate gs hgs w k h out) hz

def replaceGate (C : Circuit) (k : ℕ) (g : Gate) : Circuit :=
  { C with gates := C.gates.set k g }

lemma replaceGate_size (C : Circuit) (k : ℕ) (g : Gate) :
    (replaceGate C k g).size = C.size := by
  simp [replaceGate, Circuit.size]


lemma list_set_all {α : Type*} (P : α → Prop) (gs : List α) (k : ℕ) (h : α)
    (hgs : ∀ g ∈ gs, P g) (hh : P h) : ∀ g ∈ gs.set k h, P g := by
  induction gs generalizing k with
  | nil => simp
  | cons g gs ih =>
    cases k with
    | zero =>
      simp only [List.set_cons_zero, List.mem_cons]
      intro a ha
      rcases ha with rfl | ha
      · exact hh
      · exact hgs a (List.mem_cons_of_mem _ ha)
    | succ k =>
      simp only [List.set_cons_succ, List.mem_cons]
      intro a ha
      rcases ha with rfl | ha
      · exact hgs _ (by simp)
      · exact ih k (fun b hb => hgs b (List.mem_cons_of_mem _ hb)) a ha

lemma replaceGate_monotone2 (C : Circuit) (k : ℕ) (g : Gate)
    (hC : PEqualNP.MetaComplexity.Monotone2 C)
    (hg : g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2) :
    PEqualNP.MetaComplexity.Monotone2 (replaceGate C k g) :=
  list_set_all _ C.gates k g hC hg

lemma circuitFun_monotone {n : ℕ} (C : Circuit)
    (hC : ∀ g ∈ C.gates, g.op = GateOp.and ∨ g.op = GateOp.or) :
    Monotone (PEqualNP.MetaComplexity.circuitFun n C) := by
  intro x y hxy
  apply fold_mono C.gates hC (List.ofFn x) (List.ofFn y) (by simp)
  intro i
  by_cases hi : i < n
  · rw [List.getD_eq_getElem _ _ (by simpa using hi),
      List.getD_eq_getElem _ _ (by simpa using hi)]
    simpa using hxy ⟨i, hi⟩
  · rw [List.getD_eq_default _ _ (by simpa using hi),
      List.getD_eq_default _ _ (by simpa using hi)]

lemma pairInput_le {n : ℕ} {u v : Fin n} {x : Fin n → Bool}
    (hu : x u = true) (hv : x v = true) : PEqualNP.EdgeOwnership.pairInput u v ≤ x := by
  intro i
  rw [bool_le_iff_true]
  intro hi
  simp only [PEqualNP.EdgeOwnership.pairInput, decide_eq_true_eq] at hi
  rcases hi with rfl | rfl <;> assumption

lemma graph_eq_of_le_and_pairs {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (f : (Fin n → Bool) → Bool) (hm : Monotone f)
    (hle : ∀ x, f x ≤ PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ x)
    (hpairs : ∀ u v, G.Adj u v → f (PEqualNP.EdgeOwnership.pairInput u v) = true) :
    f = PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ := by
  funext x
  apply le_antisymm (hle x)
  rw [bool_le_iff_true]
  intro hg
  simp [PEqualNP.MetaComplexity.NestedCover.graphFun] at hg
  rcases hg with ⟨u, v, huv, hu, hv⟩
  exact (bool_le_iff_true _ _).mp (hm (pairInput_le hu hv)) (hpairs u v huv)

lemma replaceGate_graph_correct {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (k : ℕ) (h : Gate)
    (hC : ∀ g ∈ C.gates, g.op = GateOp.and ∨ g.op = GateOp.or)
    (hh : h.op = GateOp.and ∨ h.op = GateOp.or)
    (hgraph : PEqualNP.MetaComplexity.circuitFun n C =
      PEqualNP.MetaComplexity.NestedCover.graphFun G ∅)
    (hle : ∀ x : Fin n → Bool,
      gateValue ((C.gates.take k).foldl step (List.ofFn x)) h ≤
        gateValue ((C.gates.take k).foldl step (List.ofFn x)) (C.gates.getD k zeroGate))
    (hkeep : ∀ u v : Fin n, G.Adj u v →
      ((C.gates.set k zeroGate).foldl step
        (List.ofFn (PEqualNP.EdgeOwnership.pairInput u v))).getD C.output false = false →
      gateValue ((C.gates.take k).foldl step
        (List.ofFn (PEqualNP.EdgeOwnership.pairInput u v))) h =
      gateValue ((C.gates.take k).foldl step
        (List.ofFn (PEqualNP.EdgeOwnership.pairInput u v))) (C.gates.getD k zeroGate)) :
    PEqualNP.MetaComplexity.circuitFun n (replaceGate C k h) =
      PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ := by
  apply graph_eq_of_le_and_pairs
  · exact circuitFun_monotone (replaceGate C k h) (list_set_all _ C.gates k h hC hh)
  · intro x
    rw [← hgraph]
    exact set_gate_le C.gates hC (List.ofFn x) k h (hle x) C.output
  · intro u v huv
    apply set_gate_true_of_sensitive_preserved C.gates hC
      (List.ofFn (PEqualNP.EdgeOwnership.pairInput u v)) k C.output h
    · change PEqualNP.MetaComplexity.circuitFun n C
        (PEqualNP.EdgeOwnership.pairInput u v) = true
      rw [hgraph]
      simp only [PEqualNP.MetaComplexity.NestedCover.graphFun, Finset.notMem_empty,
        false_and, exists_false, decide_false, Bool.false_or, decide_eq_true_eq]
      exact ⟨u, v, huv, by simp [PEqualNP.EdgeOwnership.pairInput],
        by simp [PEqualNP.EdgeOwnership.pairInput]⟩
    · exact hkeep u v huv


lemma prefix_input {n : ℕ} (gs : List Gate) (x : Fin n → Bool) (k : ℕ) (a : Fin n) :
    ((gs.take k).foldl step (List.ofFn x)).getD a.val false = x a := by
  rw [fold_preserves _ _ _ (by simpa using a.isLt)]
  rw [List.getD_eq_getElem _ _ (by simpa using a.isLt)]
  simp

lemma set_gate_value_at (gs : List Gate) (w : List Bool) (k : ℕ) (h : Gate)
    (hk : k < gs.length) :
    ((gs.set k h).foldl step w).getD (w.length + k) false =
      gateValue ((gs.take k).foldl step w) h := by
  induction gs generalizing w k with
  | nil => simp at hk
  | cons g gs ih =>
    cases k with
    | zero =>
      simp only [List.set_cons_zero, List.foldl_cons, Nat.add_zero, List.take_zero,
        List.foldl_nil]
      rw [fold_preserves _ _ _ (by rw [step_len]; omega), step_last _ _ _ rfl]
      rfl
    | succ k =>
      have hi := ih (step w g) k (by simpa using hk)
      simpa only [List.set_cons_succ, List.foldl_cons, List.take_succ_cons,
        step_len, Nat.add_assoc, Nat.add_comm 1 k] using hi

lemma replace_and_with_input_graph_correct {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit) (k u v : ℕ) (a : Fin n)
    (hC : ∀ g ∈ C.gates, g.op = GateOp.and ∨ g.op = GateOp.or)
    (hgraph : PEqualNP.MetaComplexity.circuitFun n C =
      PEqualNP.MetaComplexity.NestedCover.graphFun G ∅)
    (hgate : C.gates.getD k zeroGate = ⟨GateOp.and, [u, v]⟩)
    (hdom : ∀ x : Fin n → Bool,
      x a ≤ ((C.gates.take k).foldl step (List.ofFn x)).getD u false)
    (hkeep : ∀ p q : Fin n, G.Adj p q →
      ((C.gates.set k zeroGate).foldl step
        (List.ofFn (PEqualNP.EdgeOwnership.pairInput p q))).getD C.output false = false →
      PEqualNP.EdgeOwnership.pairInput p q a = true) :
    PEqualNP.MetaComplexity.circuitFun n (replaceGate C k ⟨GateOp.and, [a.val, v]⟩) =
      PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ := by
  apply replaceGate_graph_correct G C k _ hC (Or.inl rfl) hgraph
  · intro x
    simp only [gateValue, hgate, List.map_cons, List.map_nil, GateOp.eval,
      List.all_cons, List.all_nil, Bool.and_true, prefix_input]
    apply Bool.le_iff_imp.mpr
    intro h
    simp only [Bool.and_eq_true] at h ⊢
    exact ⟨Bool.le_iff_imp.mp (hdom x) h.1, h.2⟩
  · intro p q hpq hz
    have ha := hkeep p q hpq hz
    have hu := Bool.le_iff_imp.mp (hdom (PEqualNP.EdgeOwnership.pairInput p q)) ha
    rw [hgate]
    simp only [gateValue, List.map_cons, List.map_nil, GateOp.eval, List.all_cons,
      List.all_nil, Bool.and_true, prefix_input, ha, hu]

lemma replaced_star_below_graph {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit) (k v : ℕ) (a : Fin n)
    (hk : k < C.gates.length)
    (hmask : ∀ x : Fin n → Bool, x a = true →
      ((C.gates.take k).foldl step (List.ofFn x)).getD v false = true →
      PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ x = true) :
    PEqualNP.TopForm.BelowF G (replaceGate C k ⟨GateOp.and, [a.val, v]⟩) k := by
  intro x hx
  change ((C.gates.set k ⟨GateOp.and, [a.val, v]⟩).foldl step (List.ofFn x)).getD
    (n + k) false = true at hx
  have he := set_gate_value_at C.gates (List.ofFn x) k ⟨GateOp.and, [a.val, v]⟩ hk
  simp only [List.length_ofFn] at he
  rw [he] at hx
  simp only [gateValue, List.map_cons, List.map_nil, GateOp.eval,
    List.all_cons, List.all_nil, Bool.and_true, prefix_input, Bool.and_eq_true] at hx
  exact hmask x hx.1 hx.2

end PEqualNP.Outside.L_meta_1477.GateReplacement


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



end PEqualNP.Outside.L_meta_1477.SensitivePath

namespace PEqualNP.Outside.L_meta_1477.SemanticOverride

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
open GateReplacement

def constantGate (b : Bool) : Gate :=
  if b then ⟨GateOp.and, []⟩ else ⟨GateOp.or, []⟩

lemma gateValue_constant (w : List Bool) (b : Bool) : gateValue w (constantGate b) = b := by
  cases b <;> rfl

def auxiliary {n : ℕ} (C : Circuit) (j : ℕ) (f : (Fin n → Bool) → Bool)
    (x : Fin n → Bool) : Circuit := replaceGate C j (constantGate (f x))

def value {n : ℕ} (C : Circuit) (j : ℕ) (f : (Fin n → Bool) → Bool)
    (w : ℕ) (x : Fin n → Bool) : Bool := SensitivePath.value (auxiliary C j f x) x w

lemma value_input {n : ℕ} (C : Circuit) (j : ℕ) (f : (Fin n → Bool) → Bool)
    (a : Fin n) (x : Fin n → Bool) : value C j f a.val x = x a :=
  SensitivePath.input_value (auxiliary C j f x) x a

lemma value_at {n : ℕ} (C : Circuit) (j : ℕ) (f : (Fin n → Bool) → Bool)
    (hj : j < C.gates.length) (x : Fin n → Bool) : value C j f (n + j) x = f x := by
  have h := set_gate_value_at C.gates (List.ofFn x) j (constantGate (f x)) hj
  simp only [List.length_ofFn, gateValue_constant] at h
  exact h

lemma take_set_same {α : Type*} (gs : List α) (j : ℕ) (a : α) :
    (gs.set j a).take j = gs.take j := by
  induction gs generalizing j with
  | nil => simp
  | cons g gs ih => cases j <;> simp_all

lemma prefix_wire {n : ℕ} (C : Circuit) (x : Fin n → Bool) (j r : ℕ)
    (hj : j < C.gates.length) (hr : r < n + j) :
    ((C.gates.take j).foldl step (List.ofFn x)).getD r false = SensitivePath.value C x r := by
  have hlen : ((C.gates.take j).foldl step (List.ofFn x)).length = n + j := by
    change (W (C.gates.take j) x).length = _
    rw [W_len, List.length_take, Nat.min_eq_left (by omega)]
  have he := fold_preserves (C.gates.drop j) ((C.gates.take j).foldl step (List.ofFn x))
    r (by rw [hlen]; exact hr)
  change _ = (C.gates.foldl step (List.ofFn x)).getD r false
  symm
  simpa only [← List.foldl_append, List.take_append_drop] using he

lemma value_before {n : ℕ} (C : Circuit) (j : ℕ) (f : (Fin n → Bool) → Bool)
    (hj : j < C.gates.length) (r : ℕ) (hr : r < n + j) (x : Fin n → Bool) :
    value C j f r x = SensitivePath.value C x r := by
  have haux := prefix_wire (auxiliary C j f x) x j r (by simpa [auxiliary, replaceGate] using hj) hr
  have hold := prefix_wire C x j r hj hr
  change _ = SensitivePath.value (auxiliary C j f x) x r at haux
  rw [show (auxiliary C j f x).gates.take j = C.gates.take j by
    exact take_set_same C.gates j (constantGate (f x))] at haux
  exact haux.symm.trans hold

lemma value_binary {n : ℕ} (C : Circuit) (j : ℕ) (f : (Fin n → Bool) → Bool)
    (k : ℕ) (hk : k < C.gates.length) (hkj : k ≠ j)
    (op : GateOp) (l r : ℕ) (hg : C.gates[k] = ⟨op, [l, r]⟩)
    (hl : l < n + k) (hr : r < n + k) (x : Fin n → Bool) :
    value C j f (n + k) x = op.eval [value C j f l x, value C j f r x] := by
  let D := auxiliary C j f x
  have hkD : k < D.gates.length := by simpa [D, auxiliary, replaceGate] using hk
  have hD : D.gates[k] = ⟨op, [l, r]⟩ := by
    have he : (C.gates.set j (constantGate (f x)))[k]'(by simpa using hk) = C.gates[k] :=
      List.getElem_set_of_ne (Ne.symm hkj) _ _
    exact he.trans hg
  have hv := SensitivePath.gate_value D x (n + k) (by omega)
    (by change n + k < n + D.gates.length; omega)
  simp only [Nat.add_sub_cancel_left] at hv
  rw [hD] at hv
  simpa only [List.map_cons, List.map_nil, ite_eq_left hl, ite_eq_left hr, value, D] using hv

lemma value_le {n : ℕ} (C : Circuit) (j : ℕ) (f : (Fin n → Bool) → Bool)
    (hC : ∀ g ∈ C.gates, g.op = GateOp.and ∨ g.op = GateOp.or)
    (hle : ∀ x : Fin n → Bool, f x ≤
      gateValue ((C.gates.take j).foldl step (List.ofFn x)) (C.gates.getD j zeroGate))
    (w : ℕ) (x : Fin n → Bool) : value C j f w x ≤ SensitivePath.value C x w := by
  apply set_gate_le C.gates hC (List.ofFn x) j (constantGate (f x))
  rw [gateValue_constant]
  exact hle x

lemma output_true {n : ℕ} (C : Circuit) (j : ℕ) (f : (Fin n → Bool) → Bool)
    (hC : ∀ g ∈ C.gates, g.op = GateOp.and ∨ g.op = GateOp.or)
    (x : Fin n → Bool) (hx : C.eval (List.ofFn x) = true)
    (hkeep : ((C.gates.set j zeroGate).foldl step (List.ofFn x)).getD C.output false = false →
      f x = gateValue ((C.gates.take j).foldl step (List.ofFn x)) (C.gates.getD j zeroGate)) :
    value C j f C.output x = true := by
  apply set_gate_true_of_sensitive_preserved C.gates hC (List.ofFn x) j C.output
    (constantGate (f x)) hx
  intro hz
  rw [gateValue_constant]
  exact hkeep hz

lemma compiled_graph_correct {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C D : Circuit) (j : ℕ) (f : (Fin n → Bool) → Bool)
    (hC : ∀ g ∈ C.gates, g.op = GateOp.and ∨ g.op = GateOp.or)
    (hfun : PEqualNP.MetaComplexity.circuitFun n C = graphFun G ∅)
    (hle : ∀ x : Fin n → Bool, f x ≤
      gateValue ((C.gates.take j).foldl step (List.ofFn x)) (C.gates.getD j zeroGate))
    (hkeep : ∀ u v : Fin n, G.Adj u v →
      ((C.gates.set j zeroGate).foldl step (List.ofFn (PEqualNP.EdgeOwnership.pairInput u v))).getD
        C.output false = false → f (PEqualNP.EdgeOwnership.pairInput u v) =
      gateValue ((C.gates.take j).foldl step (List.ofFn (PEqualNP.EdgeOwnership.pairInput u v)))
        (C.gates.getD j zeroGate))
    (hD : PEqualNP.MetaComplexity.Monotone2 D)
    (hval : ∀ x : Fin n → Bool, D.eval (List.ofFn x) = value C j f C.output x) :
    PEqualNP.MetaComplexity.circuitFun n D = graphFun G ∅ := by
  apply graph_eq_of_le_and_pairs
  · apply circuitFun_monotone D
    intro g hg
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using (hD g hg).1
  · intro x
    rw [show PEqualNP.MetaComplexity.circuitFun n D x = value C j f C.output x from hval x]
    rw [← hfun]
    exact value_le C j f hC hle C.output x
  · intro u v huv
    rw [show PEqualNP.MetaComplexity.circuitFun n D (PEqualNP.EdgeOwnership.pairInput u v) =
      value C j f C.output (PEqualNP.EdgeOwnership.pairInput u v) from hval _]
    apply output_true C j f hC _ ?_ (hkeep u v huv)
    change PEqualNP.MetaComplexity.circuitFun n C (PEqualNP.EdgeOwnership.pairInput u v) = true
    rw [hfun]
    simp only [graphFun, Finset.notMem_empty, false_and, exists_false, decide_false,
      Bool.false_or, decide_eq_true_eq]
    exact ⟨u, v, huv, by simp [PEqualNP.EdgeOwnership.pairInput], by simp [PEqualNP.EdgeOwnership.pairInput]⟩

end PEqualNP.Outside.L_meta_1477.SemanticOverride

namespace PEqualNP.Outside.L_meta_1477.QuadraticProjection

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership
open GateReplacement

def quadraticPart {n : ℕ} (f : (Fin n → Bool) → Bool) (x : Fin n → Bool) : Bool :=
  decide (∃ u v : Fin n, f (pairInput u v) = true ∧ x u = true ∧ x v = true)

lemma pair_le {n : ℕ} (x : Fin n → Bool) (u v : Fin n) (hu : x u = true) (hv : x v = true) :
    pairInput u v ≤ x := by
  intro w
  apply Bool.le_iff_imp.mpr
  intro hw
  simp only [pairInput, decide_eq_true_eq] at hw
  rcases hw with rfl | rfl
  · exact hu
  · exact hv

lemma quadraticPart_le {n : ℕ} (f : (Fin n → Bool) → Bool) (hm : Monotone f)
    (x : Fin n → Bool) : quadraticPart f x ≤ f x := by
  apply Bool.le_iff_imp.mpr
  intro hx
  obtain ⟨u, v, hf, hu, hv⟩ := of_decide_eq_true hx
  exact Bool.le_iff_imp.mp (hm (pair_le x u v hu hv)) hf

lemma quadraticPart_pair {n : ℕ} (f : (Fin n → Bool) → Bool) (hm : Monotone f)
    (u v : Fin n) : quadraticPart f (pairInput u v) = f (pairInput u v) := by
  apply le_antisymm (quadraticPart_le f hm _)
  apply Bool.le_iff_imp.mpr
  intro hf
  apply decide_eq_true
  exact ⟨u, v, hf, by simp [pairInput], by simp [pairInput]⟩

lemma quadraticPart_mono {n : ℕ} (f : (Fin n → Bool) → Bool) : Monotone (quadraticPart f) := by
  intro x y hxy
  apply Bool.le_iff_imp.mpr
  intro hx
  obtain ⟨u, v, hf, hu, hv⟩ := of_decide_eq_true hx
  apply decide_eq_true
  exact ⟨u, v, hf, Bool.le_iff_imp.mp (hxy u) hu, Bool.le_iff_imp.mp (hxy v) hv⟩

lemma local_gate_value {n : ℕ} (C : Circuit) (j : ℕ) (hj : j < C.gates.length)
    (x : Fin n → Bool) :
    gateValue ((C.gates.take j).foldl step (List.ofFn x)) (C.gates.getD j zeroGate) =
      SensitivePath.value C x (n + j) := by
  have hv := SensitivePath.gate_value C x (n + j) (by omega)
    (by change n + j < n + C.gates.length; omega)
  simp only [Nat.add_sub_cancel_left] at hv
  rw [hv]
  unfold gateValue
  rw [List.getD_eq_getElem _ _ hj]
  congr 1
  apply List.map_congr_left
  intro r _
  by_cases hr : r < n + j
  · rw [if_pos hr, SemanticOverride.prefix_wire C x j r hj hr]
  · rw [if_neg hr]
    apply List.getD_eq_default
    change (W (C.gates.take j) x).length ≤ r
    rw [W_len, List.length_take, Nat.min_eq_left (by omega)]
    omega

lemma wire_mono {n : ℕ} (C : Circuit)
    (hC : ∀ g ∈ C.gates, g.op = GateOp.and ∨ g.op = GateOp.or) (w : ℕ) :
    Monotone (fun x : Fin n → Bool => SensitivePath.value C x w) :=
  circuitFun_monotone ⟨C.gates, w⟩ hC

lemma projection_override_le {n : ℕ} (C : Circuit) (j : ℕ) (hj : j < C.gates.length)
    (hC : ∀ g ∈ C.gates, g.op = GateOp.and ∨ g.op = GateOp.or)
    (w : ℕ) (x : Fin n → Bool) :
    SemanticOverride.value C j (quadraticPart (fun y => SensitivePath.value C y (n + j))) w x ≤
      SensitivePath.value C x w := by
  apply SemanticOverride.value_le C j _ hC
  intro y
  rw [local_gate_value C j hj y]
  exact quadraticPart_le _ (wire_mono C hC _) y

lemma projection_override_pair_output {n : ℕ} (C : Circuit) (j : ℕ)
    (hj : j < C.gates.length)
    (hC : ∀ g ∈ C.gates, g.op = GateOp.and ∨ g.op = GateOp.or)
    (u v : Fin n) (hx : C.eval (List.ofFn (pairInput u v)) = true) :
    SemanticOverride.value C j (quadraticPart (fun y => SensitivePath.value C y (n + j)))
      C.output (pairInput u v) = true := by
  apply SemanticOverride.output_true C j _ hC _ hx
  intro _
  rw [local_gate_value C j hj, quadraticPart_pair _ (wire_mono C hC _)]

end PEqualNP.Outside.L_meta_1477.QuadraticProjection
