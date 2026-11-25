import Mathlib.Tactic
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3451_aux

lemma universal_row_other_unique (N : ℕ) (I : Fin N → Fin N → Prop)
    (h4 : ∀ p p' l l' : Fin N, p ≠ p' → l ≠ l' →
      ¬ (I p l ∧ I p l' ∧ I p' l ∧ I p' l'))
    (p p' : Fin N) (hp : ∀ l, I p l) (hne : p ≠ p')
    (l l' : Fin N) (hpl : I p' l) (hpl' : I p' l') : l = l' := by
  by_contra hl
  exact h4 p p' l l' hne hl ⟨hp l, hp l', hpl, hpl'⟩

lemma universal_column_other_unique (N : ℕ) (I : Fin N → Fin N → Prop)
    (h4 : ∀ p p' l l' : Fin N, p ≠ p' → l ≠ l' →
      ¬ (I p l ∧ I p l' ∧ I p' l ∧ I p' l'))
    (l l' : Fin N) (hl : ∀ p, I p l) (hne : l ≠ l')
    (p p' : Fin N) (hpl : I p l') (hpl' : I p' l') : p = p' := by
  by_contra hp
  exact h4 p p' l l' hp hne ⟨hl p, hpl, hl p', hpl'⟩

lemma universal_row_column_edges (N : ℕ) (I : Fin N → Fin N → Prop)
    (h4 : ∀ p p' l l' : Fin N, p ≠ p' → l ≠ l' →
      ¬ (I p l ∧ I p l' ∧ I p' l ∧ I p' l'))
    (p0 l0 : Fin N) (hp0 : ∀ l, I p0 l) (hl0 : ∀ p, I p l0)
    (p l : Fin N) : I p l ↔ p = p0 ∨ l = l0 := by
  constructor
  · intro h
    by_cases hp : p = p0
    · exact Or.inl hp
    · right
      by_contra hl
      exact h4 p0 p l0 l (Ne.symm hp) (Ne.symm hl)
        ⟨hp0 l0, hp0 l, hl0 p, h⟩
  · rintro (rfl | rfl)
    · exact hp0 l
    · exact hl0 p

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

lemma point_ne_line (N : ℕ) (p l : Fin N) : Fin.castAdd N p ≠ Fin.natAdd N l := by
  intro h
  have hv := congrArg Fin.val h
  dsimp at hv
  omega

lemma incidence_point_false (N : ℕ) (I : Fin N → Fin N → Prop) (C : Circuit)
    (sem : ∀ z : Fin (N + N) → Bool, circuitFun (N + N) C z = true ↔
      ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true)
    (p : Fin N) :
    circuitFun (N + N) C (fun k => decide (k = Fin.castAdd N p)) = false := by
  cases h : circuitFun (N + N) C (fun k => decide (k = Fin.castAdd N p)) with
  | false => rfl
  | true =>
    obtain ⟨q, l, hi, hq, hl⟩ := (sem _).mp h
    exact (point_ne_line N p l (of_decide_eq_true hl).symm).elim

lemma incidence_line_false (N : ℕ) (I : Fin N → Fin N → Prop) (C : Circuit)
    (sem : ∀ z : Fin (N + N) → Bool, circuitFun (N + N) C z = true ↔
      ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true)
    (l : Fin N) :
    circuitFun (N + N) C (fun k => decide (k = Fin.natAdd N l)) = false := by
  cases h : circuitFun (N + N) C (fun k => decide (k = Fin.natAdd N l)) with
  | false => rfl
  | true =>
    obtain ⟨p, m, hi, hp, hm⟩ := (sem _).mp h
    exact (point_ne_line N p l (of_decide_eq_true hp)).elim

lemma incidence_nonedge_false (N : ℕ) (I : Fin N → Fin N → Prop) (C : Circuit)
    (sem : ∀ z : Fin (N + N) → Bool, circuitFun (N + N) C z = true ↔
      ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true)
    (p l : Fin N) (nonedge : ¬ I p l) :
    circuitFun (N + N) C
      (fun k => decide (k = Fin.castAdd N p ∨ k = Fin.natAdd N l)) = false := by
  cases h : circuitFun (N + N) C
      (fun k => decide (k = Fin.castAdd N p ∨ k = Fin.natAdd N l)) with
  | false => rfl
  | true =>
    obtain ⟨q, m, hi, hq, hm⟩ := (sem _).mp h
    have eqp : q = p := by
      rcases of_decide_eq_true hq with hp | hl
      · apply Fin.ext
        exact congrArg (fun x : Fin (N + N) => x.val) hp
      · exact (point_ne_line N q l hl).elim
    have eql : m = l := by
      rcases of_decide_eq_true hm with hp | hl
      · exact (point_ne_line N p m hp.symm).elim
      · apply Fin.ext
        have hv := congrArg Fin.val hl
        dsimp at hv
        omega
    exact (nonedge (eqp ▸ eql ▸ hi)).elim

def wireStep (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def wireLE (a b : List Bool) : Prop :=
  ∀ i, a.getD i false = true → b.getD i false = true

lemma eval_mono (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or) (l : List ℕ)
    (f f' : ℕ → Bool) (h : ∀ i, f i = true → f' i = true) :
    op.eval (l.map f) = true → op.eval (l.map f') = true := by
  rcases hop with rfl | rfl
  · simp only [GateOp.eval, List.all_eq_true, List.mem_map, id]
    intro H x hx
    obtain ⟨i, hi, rfl⟩ := hx
    exact h i (H (f i) ⟨i, hi, rfl⟩)
  · simp only [GateOp.eval, List.any_eq_true, List.mem_map, id]
    rintro ⟨x, ⟨i, hi, rfl⟩, hx⟩
    exact ⟨f' i, ⟨i, hi, rfl⟩, h i hx⟩

lemma fold_mono (gs : List Gate) (hgs : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) :
    ∀ a b : List Bool, a.length = b.length → wireLE a b →
      wireLE (gs.foldl wireStep a) (gs.foldl wireStep b) := by
  induction gs with
  | nil => intro a b _ h; exact h
  | cons g gs ih =>
    intro a b hl h
    rw [List.foldl_cons, List.foldl_cons]
    apply ih (fun g' hg' => hgs g' (List.mem_cons_of_mem _ hg'))
    · simp [wireStep, hl]
    · intro i hi
      unfold wireStep at hi ⊢
      by_cases hia : i < a.length
      · rw [List.getD_append _ _ _ _ hia] at hi
        rw [List.getD_append _ _ _ _ (by omega)]
        exact h i hi
      · rw [List.getD_append_right _ _ _ _ (by omega)] at hi
        rw [List.getD_append_right _ _ _ _ (by omega)]
        rw [← hl]
        by_cases he : i - a.length = 0
        · rw [he] at hi ⊢
          simp only [List.getD_cons_zero] at hi ⊢
          exact eval_mono g.op (hgs g List.mem_cons_self) _ _ _ (fun k => h k) hi
        · obtain ⟨m, hm⟩ : ∃ m, i - a.length = m + 1 := ⟨i - a.length - 1, by omega⟩
          rw [hm] at hi
          simp at hi

lemma wires_mono (n : ℕ) (C : Circuit) (hC : Monotone2 C)
    (a b : Fin n → Bool) (h : ∀ i, a i = true → b i = true) :
    wireLE (C.wires (List.ofFn a)) (C.wires (List.ofFn b)) := by
  apply fold_mono C.gates (fun g hg => by simpa using (hC g hg).1)
  · simp
  · intro i hi
    by_cases hin : i < n
    · simpa [List.getD_eq_getElem?_getD, hin] using
        h ⟨i, hin⟩ (by simpa [List.getD_eq_getElem?_getD, hin] using hi)
    · rw [List.getD_eq_default _ _ (by simpa using Nat.le_of_not_gt hin)] at hi
      cases hi

lemma nonedge_point_false (N : ℕ) (C : Circuit) (hC : Monotone2 C)
    (p l : Fin N) (w : ℕ)
    (zero : (C.wires (List.ofFn (fun k : Fin (N + N) =>
      decide (k = Fin.castAdd N p ∨ k = Fin.natAdd N l)))).getD w false = false) :
    (C.wires (List.ofFn (fun k : Fin (N + N) =>
      decide (k = Fin.castAdd N p)))).getD w false = false := by
  cases hv : (C.wires (List.ofFn (fun k : Fin (N + N) =>
      decide (k = Fin.castAdd N p)))).getD w false with
  | false => rfl
  | true =>
    have below : ∀ k : Fin (N + N), decide (k = Fin.castAdd N p) = true →
        decide (k = Fin.castAdd N p ∨ k = Fin.natAdd N l) = true := by
      intro k hk
      simp only [decide_eq_true_eq] at hk ⊢
      exact Or.inl hk
    have impossible := wires_mono (N + N) C hC _ _ below w hv
    rw [zero] at impossible
    cases impossible

lemma nonedge_line_false (N : ℕ) (C : Circuit) (hC : Monotone2 C)
    (p l : Fin N) (w : ℕ)
    (zero : (C.wires (List.ofFn (fun k : Fin (N + N) =>
      decide (k = Fin.castAdd N p ∨ k = Fin.natAdd N l)))).getD w false = false) :
    (C.wires (List.ofFn (fun k : Fin (N + N) =>
      decide (k = Fin.natAdd N l)))).getD w false = false := by
  cases hv : (C.wires (List.ofFn (fun k : Fin (N + N) =>
      decide (k = Fin.natAdd N l)))).getD w false with
  | false => rfl
  | true =>
    have below : ∀ k : Fin (N + N), decide (k = Fin.natAdd N l) = true →
        decide (k = Fin.castAdd N p ∨ k = Fin.natAdd N l) = true := by
      intro k hk
      simp only [decide_eq_true_eq] at hk ⊢
      exact Or.inr hk
    have impossible := wires_mono (N + N) C hC _ _ below w hv
    rw [zero] at impossible
    cases impossible

lemma singleton_clean_of_nonedge (N : ℕ) (I : Fin N → Fin N → Prop) (C : Circuit)
    (hC : Monotone2 C)
    (point_misses : ∀ p : Fin N, ∃ l : Fin N, ¬ I p l)
    (line_misses : ∀ l : Fin N, ∃ p : Fin N, ¬ I p l)
    (clean : ∀ j < C.gates.length, (NestedCover.gateAt C j).op = GateOp.and →
      ∀ p l : Fin N, ¬ I p l →
        (C.wires (List.ofFn (fun k : Fin (N + N) =>
          decide (k = Fin.castAdd N p ∨ k = Fin.natAdd N l)))).getD
            (N + N + j) false = false) :
    ∀ j < C.gates.length, (NestedCover.gateAt C j).op = GateOp.and →
      (∀ p : Fin N, (C.wires (List.ofFn (fun k : Fin (N + N) =>
        decide (k = Fin.castAdd N p)))).getD (N + N + j) false = false) ∧
      ∀ l : Fin N, (C.wires (List.ofFn (fun k : Fin (N + N) =>
        decide (k = Fin.natAdd N l)))).getD (N + N + j) false = false := by
  intro j hj hop
  constructor
  · intro p
    obtain ⟨l, hl⟩ := point_misses p
    exact nonedge_point_false N C hC p l (N + N + j) (clean j hj hop p l hl)
  · intro l
    obtain ⟨p, hp⟩ := line_misses l
    exact nonedge_line_false N C hC p l (N + N + j) (clean j hj hop p l hp)

end PEqualNP.Outside.L_meta_3451_aux
