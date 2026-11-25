import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2592_aux.MonotoneWires

open PEqualNP.CircuitLowerBounds

def Above (v w : List Bool) : Prop :=
  v.length = w.length ∧ ∀ i, v.getD i false = true → w.getD i false = true

lemma snoc_ne {α : Type} (v : List α) (a d : α) (i : ℕ) (hi : i ≠ v.length) :
    (v ++ [a]).getD i d = v.getD i d := by
  by_cases hlt : i < v.length
  · exact List.getD_append _ _ _ _ hlt
  · rw [List.getD_eq_default _ _ (by simp; omega),
      List.getD_eq_default _ _ (by omega)]

lemma above_snoc {v w : List Bool} {a b : Bool} (h : Above v w)
    (hab : a = true → b = true) : Above (v ++ [a]) (w ++ [b]) := by
  refine ⟨by simp [h.1], ?_⟩
  intro i hi
  by_cases hiv : i = v.length
  · subst i
    have ha : a = true := by simpa using hi
    rw [h.1]
    simpa using hab ha
  · rw [snoc_ne _ _ _ _ hiv] at hi
    rw [snoc_ne _ _ _ _ (by rw [← h.1]; exact hiv)]
    exact h.2 i hi

def run (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

lemma run_above (gs : List Gate)
    (hgs : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) :
    ∀ v w : List Bool, Above v w → Above (run gs v) (run gs w) := by
  induction gs with
  | nil => intro v w h; exact h
  | cons g gs ih =>
    intro v w h
    simp only [run, List.foldl_cons]
    apply ih (fun k hk => hgs k (List.mem_cons_of_mem g hk))
    apply above_snoc h
    rcases hgs g List.mem_cons_self with hop | hop
    · rw [hop]
      simp only [GateOp.eval, List.all_eq_true, List.mem_map, id]
      intro all b hb
      obtain ⟨i, hi, rfl⟩ := hb
      exact h.2 i (all _ ⟨i, hi, rfl⟩)
    · rw [hop]
      simp only [GateOp.eval, List.any_eq_true, List.mem_map, id]
      rintro ⟨b, ⟨i, hi, rfl⟩, hb⟩
      exact ⟨_, ⟨i, hi, rfl⟩, h.2 i hb⟩

lemma ofFn_above {n : ℕ} (x y : Fin n → Bool)
    (hxy : ∀ i, x i = true → y i = true) : Above (List.ofFn x) (List.ofFn y) := by
  refine ⟨by simp, ?_⟩
  intro i hi
  by_cases hin : i < n
  · have hx : (List.ofFn x).getD i false = x ⟨i, hin⟩ := by simp [hin]
    have hy : (List.ofFn y).getD i false = y ⟨i, hin⟩ := by simp [hin]
    rw [hx] at hi
    rw [hy]
    exact hxy _ hi
  · rw [List.getD_eq_default _ _ (by simp; omega)] at hi
    cases hi

lemma wire_monotone {n : ℕ} (C : Circuit)
    (mono : ∀ g ∈ C.gates, g.op = GateOp.and ∨ g.op = GateOp.or) (o : ℕ) :
    Monotone (fun x : Fin n → Bool => (C.wires (List.ofFn x)).getD o false) := by
  intro x y hxy
  have hx : Above (run C.gates (List.ofFn x)) (run C.gates (List.ofFn y)) :=
    run_above C.gates mono _ _ (ofFn_above x y (fun i hi =>
      Bool.le_iff_imp.mp (hxy i) hi))
  exact Bool.le_iff_imp.mpr (hx.2 o)

lemma eval_monotone {n : ℕ} (C : Circuit)
    (mono : ∀ g ∈ C.gates, g.op = GateOp.and ∨ g.op = GateOp.or) :
    Monotone (fun x : Fin n → Bool => C.eval (List.ofFn x)) :=
  wire_monotone C mono C.output

lemma eval_above (C : Circuit)
    (mono : ∀ g ∈ C.gates, g.op = GateOp.and ∨ g.op = GateOp.or)
    {v w : List Bool} (h : Above v w) : C.eval v ≤ C.eval w := by
  have hx := run_above C.gates mono v w h
  exact Bool.le_iff_imp.mpr (hx.2 C.output)

lemma splice_monotone {n : ℕ} (P Q : Circuit)
    (mp : ∀ g ∈ P.gates, g.op = GateOp.and ∨ g.op = GateOp.or)
    (mq : ∀ g ∈ Q.gates, g.op = GateOp.and ∨ g.op = GateOp.or) :
    Monotone (fun x : (Fin n → Bool) × Bool =>
      Q.eval (P.wires (List.ofFn x.1) ++ [x.2])) := by
  intro x y hxy
  apply eval_above Q mq
  apply above_snoc
  · exact run_above P.gates mp _ _ (ofFn_above x.1 y.1 (fun i hi =>
      Bool.le_iff_imp.mp (hxy.1 i) hi))
  · exact Bool.le_iff_imp.mp hxy.2

lemma one_not_parts (pre post : List Gate) (ins : List ℕ) (out : ℕ)
    (fan : PEqualNP.MetaComplexity.FanInTwo
      ⟨pre ++ ⟨GateOp.not, ins⟩ :: post, out⟩)
    (one : PEqualNP.NotBracket.notCount
      ⟨pre ++ ⟨GateOp.not, ins⟩ :: post, out⟩ = 1) :
    (∀ g ∈ pre, g.op = GateOp.and ∨ g.op = GateOp.or) ∧
    (∀ g ∈ post, g.op = GateOp.and ∨ g.op = GateOp.or) := by
  let _ : DecidableEq GateOp := lineDegreeGateOpDecEq
  have counts :
      (pre.filter (fun g => decide (g.op = GateOp.not))).length +
      (post.filter (fun g => decide (g.op = GateOp.not))).length = 0 := by
    have total :
        (pre.filter (fun g => decide (g.op = GateOp.not))).length +
        ((post.filter (fun g => decide (g.op = GateOp.not))).length + 1) = 1 := by
      simpa [PEqualNP.NotBracket.notCount, List.filter_append] using one
    omega
  have noPre : pre.filter (fun g => decide (g.op = GateOp.not)) = [] :=
    List.length_eq_zero_iff.mp (by omega)
  have noPost : post.filter (fun g => decide (g.op = GateOp.not)) = [] :=
    List.length_eq_zero_iff.mp (by omega)
  have remove (g : Gate) (mem : g ∈ pre ++ ⟨GateOp.not, ins⟩ :: post)
      (hn : g.op ≠ GateOp.not) : g.op = GateOp.and ∨ g.op = GateOp.or := by
    have hop := (fan g mem).1
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
    rcases hop with ha | ho | hnot
    · exact Or.inl ha
    · exact Or.inr ho
    · exact (hn hnot).elim
  constructor
  · intro g hg
    apply remove g (List.mem_append.mpr (Or.inl hg))
    intro hn
    have mem : g ∈ pre.filter (fun h => decide (h.op = GateOp.not)) :=
      List.mem_filter.mpr ⟨hg, decide_eq_true hn⟩
    rw [noPre] at mem
    cases mem
  · intro g hg
    apply remove g (List.mem_append.mpr (Or.inr (List.mem_cons_of_mem _ hg)))
    intro hn
    have mem : g ∈ post.filter (fun h => decide (h.op = GateOp.not)) :=
      List.mem_filter.mpr ⟨hg, decide_eq_true hn⟩
    rw [noPost] at mem
    cases mem

end PEqualNP.Outside.L_meta_2592_aux.MonotoneWires
