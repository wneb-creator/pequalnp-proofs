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

lemma no_incidence (N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I]
    (C : PEqualNP.CircuitLowerBounds.Circuit) (hI : ∀ p l, ¬ I p l) :
    ∃ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 D ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (N + N) D ∧ D.size ≤ C.size ∧ (∀ z : Fin (N + N) → Bool, PEqualNP.MetaComplexity.circuitFun (N + N) D z = true ↔ ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) ∧ (∀ j < D.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt D j).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∀ p0 l0 : Fin N, ¬ I p0 l0 → (D.wires (List.ofFn (fun ke : Fin (N + N) => decide (ke = Fin.castAdd N p0 ∨ ke = Fin.natAdd N l0)))).getD (N + N + j) false = false) ∧ (∀ j < D.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt D j).op = PEqualNP.CircuitLowerBounds.GateOp.and → (∀ p : Fin N, (D.wires (List.ofFn (fun kc : Fin (N + N) => decide (kc = Fin.castAdd N p)))).getD (N + N + j) false = false) ∧ ∀ l : Fin N, (D.wires (List.ofFn (fun kd : Fin (N + N) => decide (kd = Fin.natAdd N l)))).getD (N + N + j) false = false) := by
  let D : PEqualNP.CircuitLowerBounds.Circuit := ⟨[], N + N⟩
  refine ⟨D, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [D, PEqualNP.MetaComplexity.Monotone2]
  · simp [D, PEqualNP.MetaComplexity.NestedCover.ReadsBack]
  · simp [D, PEqualNP.CircuitLowerBounds.Circuit.size]
  · intro z
    simp [D, PEqualNP.MetaComplexity.circuitFun,
      PEqualNP.CircuitLowerBounds.Circuit.eval, PEqualNP.CircuitLowerBounds.Circuit.wires,
      hI]
  · simp [D]
  · simp [D]

lemma positive_size (N : ℕ) (I : Fin N → Fin N → Prop)
    (C : PEqualNP.CircuitLowerBounds.Circuit) (hI : ∃ p l, I p l)
    (hfun : ∀ z : Fin (N + N) → Bool,
      PEqualNP.MetaComplexity.circuitFun (N + N) C z = true ↔
      ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) :
    0 < C.size := by
  by_contra hsize
  have hg : C.gates = [] := by
    apply List.length_eq_zero_iff.mp
    exact Nat.eq_zero_of_not_pos hsize
  by_cases hout : C.output < N + N
  · let k : Fin (N + N) := ⟨C.output, hout⟩
    have hone : PEqualNP.MetaComplexity.circuitFun (N + N) C
        (fun v => decide (v = k)) = true := by
      simp [PEqualNP.MetaComplexity.circuitFun,
        PEqualNP.CircuitLowerBounds.Circuit.eval, PEqualNP.CircuitLowerBounds.Circuit.wires,
        hg, List.getD_eq_getElem?_getD, hout, k]
    obtain ⟨p, l, _, hp, hl⟩ := (hfun _).mp hone
    have he : Fin.castAdd N p = Fin.natAdd N l :=
      (of_decide_eq_true hp).trans (of_decide_eq_true hl).symm
    have hv := congrArg Fin.val he
    simp only [Fin.val_castAdd, Fin.val_natAdd] at hv
    omega
  · have hall : PEqualNP.MetaComplexity.circuitFun (N + N) C (fun _ => true) = true := by
      apply (hfun _).mpr
      obtain ⟨p, l, hpl⟩ := hI
      exact ⟨p, l, hpl, rfl, rfl⟩
    simp [PEqualNP.MetaComplexity.circuitFun,
      PEqualNP.CircuitLowerBounds.Circuit.eval, PEqualNP.CircuitLowerBounds.Circuit.wires,
      hg, List.getD_eq_getElem?_getD, hout] at hall

lemma one_input_each (N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I]
    (C : PEqualNP.CircuitLowerBounds.Circuit) (hN : N = 1)
    (hfun : ∀ z : Fin (N + N) → Bool,
      PEqualNP.MetaComplexity.circuitFun (N + N) C z = true ↔
      ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) :
    ∃ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 D ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (N + N) D ∧ D.size ≤ C.size ∧ (∀ z : Fin (N + N) → Bool, PEqualNP.MetaComplexity.circuitFun (N + N) D z = true ↔ ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) ∧ (∀ j < D.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt D j).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∀ p0 l0 : Fin N, ¬ I p0 l0 → (D.wires (List.ofFn (fun ke : Fin (N + N) => decide (ke = Fin.castAdd N p0 ∨ ke = Fin.natAdd N l0)))).getD (N + N + j) false = false) ∧ (∀ j < D.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt D j).op = PEqualNP.CircuitLowerBounds.GateOp.and → (∀ p : Fin N, (D.wires (List.ofFn (fun kc : Fin (N + N) => decide (kc = Fin.castAdd N p)))).getD (N + N + j) false = false) ∧ ∀ l : Fin N, (D.wires (List.ofFn (fun kd : Fin (N + N) => decide (kd = Fin.natAdd N l)))).getD (N + N + j) false = false) := by
  subst N
  by_cases hI : I 0 0
  · have hsize := positive_size 1 I C ⟨0, 0, hI⟩ hfun
    let D : PEqualNP.CircuitLowerBounds.Circuit :=
      ⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 1]⟩], 2⟩
    refine ⟨D, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [D, PEqualNP.MetaComplexity.Monotone2]
    · norm_num [D, PEqualNP.MetaComplexity.NestedCover.ReadsBack,
        PEqualNP.MetaComplexity.NestedCover.gateAt]
    · exact hsize
    · intro z
      simp [D, PEqualNP.MetaComplexity.circuitFun,
        PEqualNP.CircuitLowerBounds.Circuit.eval, PEqualNP.CircuitLowerBounds.Circuit.wires,
        PEqualNP.CircuitLowerBounds.GateOp.eval, List.ofFn_succ, hI]
    · simp [hI]
    · norm_num [D, PEqualNP.MetaComplexity.NestedCover.gateAt,
        PEqualNP.CircuitLowerBounds.Circuit.wires,
        PEqualNP.CircuitLowerBounds.GateOp.eval, List.ofFn_succ]
  · exact no_incidence 1 I C (by simpa using hI)

lemma cast_point_ne_line {N : ℕ} (p l : Fin N) :
    Fin.castAdd N p ≠ Fin.natAdd N l := by
  intro h
  have hv := congrArg Fin.val h
  simp only [Fin.val_castAdd, Fin.val_natAdd] at hv
  omega

def edgeCircuit {N : ℕ} (p l : Fin N) : PEqualNP.CircuitLowerBounds.Circuit :=
  ⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.and, [p.val, N + l.val]⟩], N + N⟩

lemma edgeCircuit_value {N : ℕ} (p l : Fin N) (z : Fin (N + N) → Bool) :
    PEqualNP.MetaComplexity.circuitFun (N + N) (edgeCircuit p l) z =
      (z (Fin.castAdd N p) && z (Fin.natAdd N l)) := by
  have hp : p.val < N + N := by omega
  have hl : N + l.val < N + N := by omega
  simp [edgeCircuit, PEqualNP.MetaComplexity.circuitFun,
    PEqualNP.CircuitLowerBounds.Circuit.eval, PEqualNP.CircuitLowerBounds.Circuit.wires,
    PEqualNP.CircuitLowerBounds.GateOp.eval, List.getD_eq_getElem?_getD,
    List.getElem?_ofFn, hp, hl]
  congr 2
  apply Fin.ext
  simp [Nat.add_comm]

lemma single_incidence (N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I]
    (C : PEqualNP.CircuitLowerBounds.Circuit) (p0 l0 : Fin N)
    (hI : ∀ p l, I p l ↔ p = p0 ∧ l = l0)
    (hfun : ∀ z : Fin (N + N) → Bool,
      PEqualNP.MetaComplexity.circuitFun (N + N) C z = true ↔
      ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) :
    ∃ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 D ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (N + N) D ∧ D.size ≤ C.size ∧ (∀ z : Fin (N + N) → Bool, PEqualNP.MetaComplexity.circuitFun (N + N) D z = true ↔ ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) ∧ (∀ j < D.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt D j).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∀ p0 l0 : Fin N, ¬ I p0 l0 → (D.wires (List.ofFn (fun ke : Fin (N + N) => decide (ke = Fin.castAdd N p0 ∨ ke = Fin.natAdd N l0)))).getD (N + N + j) false = false) ∧ (∀ j < D.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt D j).op = PEqualNP.CircuitLowerBounds.GateOp.and → (∀ p : Fin N, (D.wires (List.ofFn (fun kc : Fin (N + N) => decide (kc = Fin.castAdd N p)))).getD (N + N + j) false = false) ∧ ∀ l : Fin N, (D.wires (List.ofFn (fun kd : Fin (N + N) => decide (kd = Fin.natAdd N l)))).getD (N + N + j) false = false) := by
  have hsize := positive_size N I C ⟨p0, l0, (hI p0 l0).mpr ⟨rfl, rfl⟩⟩ hfun
  refine ⟨edgeCircuit p0 l0, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [edgeCircuit, PEqualNP.MetaComplexity.Monotone2]
  · intro j hj i hi
    have hj0 : j = 0 := by simpa [edgeCircuit] using hj
    subst j
    simp only [edgeCircuit, PEqualNP.MetaComplexity.NestedCover.gateAt,
      List.getD_cons_zero, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl <;> omega
  · exact hsize
  · intro z
    simp [edgeCircuit_value, hI]
  · intro j hj hand p l hnot
    have hj0 : j = 0 := by simpa [edgeCircuit] using hj
    subst j
    change PEqualNP.MetaComplexity.circuitFun (N + N) (edgeCircuit p0 l0)
      (fun k => decide (k = Fin.castAdd N p ∨ k = Fin.natAdd N l)) = false
    rw [edgeCircuit_value]
    have hpl : ¬ (p = p0 ∧ l = l0) := by simpa only [hI] using hnot
    simp [Fin.ext_iff] at hpl ⊢
    omega
  · intro j hj hand
    have hj0 : j = 0 := by simpa [edgeCircuit] using hj
    subst j
    constructor
    · intro p
      change PEqualNP.MetaComplexity.circuitFun (N + N) (edgeCircuit p0 l0)
        (fun k => decide (k = Fin.castAdd N p)) = false
      rw [edgeCircuit_value]
      simp [Fin.ext_iff]
      omega
    · intro l
      change PEqualNP.MetaComplexity.circuitFun (N + N) (edgeCircuit p0 l0)
        (fun k => decide (k = Fin.natAdd N l)) = false
      rw [edgeCircuit_value]
      simp [Fin.ext_iff]
      omega

namespace Padding

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def padWire (N w : ℕ) : ℕ :=
  if w < N then w else if w < N + N then w + 1 else w + 2

def padGate (N : ℕ) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map (padWire N)⟩

def padCircuit (N : ℕ) (C : Circuit) : Circuit :=
  ⟨C.gates.map (padGate N), padWire N C.output⟩

def padStep (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma padWire_lt (N s w : ℕ) (_hs : N + N ≤ s) (hw : w < s) :
    padWire N w < s + 2 := by
  unfold padWire
  split_ifs <;> omega

lemma padWire_ge (N s w : ℕ) (hs : N + N ≤ s) (hw : s ≤ w) :
    padWire N w = w + 2 := by
  unfold padWire
  split_ifs <;> omega

lemma append_agree (N : ℕ) (a b : List Bool) (hl : b.length = a.length + 2)
    (hn : N + N ≤ a.length)
    (h : ∀ i, b.getD (padWire N i) false = a.getD i false) (v : Bool) :
    ∀ i, (b ++ [v]).getD (padWire N i) false = (a ++ [v]).getD i false := by
  intro i
  by_cases hi : i < a.length
  · rw [List.getD_append _ _ _ _ (by rw [hl]; exact padWire_lt N _ i hn hi),
      List.getD_append _ _ _ _ hi]
    exact h i
  · rw [padWire_ge N a.length i hn (by omega),
      List.getD_append_right _ _ _ _ (by omega),
      List.getD_append_right _ _ _ _ (by omega)]
    congr 1
    omega

lemma step_agree (N : ℕ) (g : Gate) (a b : List Bool) (hl : b.length = a.length + 2)
    (hn : N + N ≤ a.length)
    (h : ∀ i, b.getD (padWire N i) false = a.getD i false) :
    ∀ i, (padStep b (padGate N g)).getD (padWire N i) false =
      (padStep a g).getD i false := by
  have hg : (padGate N g).op.eval
      ((padGate N g).inputs.map fun i => b.getD i false) =
      g.op.eval (g.inputs.map fun i => a.getD i false) := by
    simp only [padGate, List.map_map, Function.comp_def, h]
  unfold padStep
  rw [hg]
  exact append_agree N a b hl hn h _

lemma fold_agree (N : ℕ) (gs : List Gate) : ∀ (a b : List Bool),
    b.length = a.length + 2 → N + N ≤ a.length →
    (∀ i, b.getD (padWire N i) false = a.getD i false) →
    ∀ i, ((gs.map (padGate N)).foldl padStep b).getD (padWire N i) false =
      (gs.foldl padStep a).getD i false := by
  induction gs with
  | nil => intro a b hl hn h; exact h
  | cons g gs ih =>
    intro a b hl hn h
    simp only [List.map_cons, List.foldl_cons]
    apply ih
    · simp [padStep, hl]
    · simp only [padStep, List.length_append, List.length_singleton]
      omega
    · exact step_agree N g a b hl hn h

def restrictInput (N : ℕ) (z : Fin ((N + 1) + (N + 1)) → Bool) :
    Fin (N + N) → Bool :=
  fun i => z ⟨padWire N i.val, by
    have := padWire_lt N (N + N) i.val (by omega) i.isLt
    omega⟩

lemma wires_agree (N : ℕ) (C : Circuit) (z : Fin ((N + 1) + (N + 1)) → Bool) :
    ∀ i, ((padCircuit N C).wires (List.ofFn z)).getD (padWire N i) false =
      (C.wires (List.ofFn (restrictInput N z))).getD i false := by
  apply fold_agree N C.gates
  · simp
    omega
  · simp
  · intro i
    by_cases hi : i < N + N
    · have hp : padWire N i < (N + 1) + (N + 1) := by
        have := padWire_lt N (N + N) i (by omega) hi
        omega
      simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, dite_eq_left hp,
        dite_eq_left hi, Option.getD_some, restrictInput]
    · have hp : (N + 1) + (N + 1) ≤ padWire N i := by
        rw [padWire_ge N (N + N) i (by omega) (by omega)]
        omega
      rw [List.getD_eq_default _ _ (by simpa only [List.length_ofFn] using hp),
        List.getD_eq_default _ _ (by simpa only [List.length_ofFn] using Nat.le_of_not_gt hi)]

lemma circuitFun_agree (N : ℕ) (C : Circuit)
    (z : Fin ((N + 1) + (N + 1)) → Bool) :
    circuitFun ((N + 1) + (N + 1)) (padCircuit N C) z =
      circuitFun (N + N) C (restrictInput N z) :=
  wires_agree N C z C.output

lemma size_pad (N : ℕ) (C : Circuit) : (padCircuit N C).size = C.size := by
  simp [padCircuit, Circuit.size]

lemma monotone_pad (N : ℕ) (C : Circuit) (hC : Monotone2 C) :
    Monotone2 (padCircuit N C) := by
  intro g hg
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hg
  simpa [padGate] using hC q hq

lemma gateAt_pad (N : ℕ) (C : Circuit) (j : ℕ) (hj : j < C.gates.length) :
    NestedCover.gateAt (padCircuit N C) j = padGate N (NestedCover.gateAt C j) := by
  simp [NestedCover.gateAt, padCircuit, List.getD_eq_getElem?_getD, hj]

lemma readsBack_pad (N : ℕ) (C : Circuit) (hC : NestedCover.ReadsBack (N + N) C) :
    NestedCover.ReadsBack ((N + 1) + (N + 1)) (padCircuit N C) := by
  intro j hj i hi
  have hj' : j < C.gates.length := by simpa [padCircuit] using hj
  rw [gateAt_pad N C j hj'] at hi
  obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hi
  have := padWire_lt N (N + N + j) w (by omega) (hC j hj' w hw)
  omega

def padIncidence (N : ℕ) (I : Fin N → Fin N → Prop) (p l : Fin (N + 1)) : Prop :=
  ∃ hp : p.val < N, ∃ hl : l.val < N, I ⟨p.val, hp⟩ ⟨l.val, hl⟩

lemma point_misses (N : ℕ) (I : Fin N → Fin N → Prop) (p : Fin (N + 1)) :
    ∃ l : Fin (N + 1), ¬ padIncidence N I p l := by
  refine ⟨⟨N, by omega⟩, ?_⟩
  rintro ⟨hp, hl, hi⟩
  exact (Nat.lt_irrefl N) hl

lemma line_misses (N : ℕ) (I : Fin N → Fin N → Prop) (l : Fin (N + 1)) :
    ∃ p : Fin (N + 1), ¬ padIncidence N I p l := by
  refine ⟨⟨N, by omega⟩, ?_⟩
  rintro ⟨hp, hl, hi⟩
  exact (Nat.lt_irrefl N) hp

lemma noFourCycle_pad (N : ℕ) (I : Fin N → Fin N → Prop)
    (hI : ∀ p p' l l' : Fin N, p ≠ p' → l ≠ l' →
      ¬ (I p l ∧ I p l' ∧ I p' l ∧ I p' l')) :
    ∀ p p' l l' : Fin (N + 1), p ≠ p' → l ≠ l' →
      ¬ (padIncidence N I p l ∧ padIncidence N I p l' ∧
        padIncidence N I p' l ∧ padIncidence N I p' l') := by
  intro p p' l l' hpp hll h
  obtain ⟨hp, hl, hpl⟩ := h.1
  obtain ⟨_, hl', hpl'⟩ := h.2.1
  obtain ⟨hp', _, hp'l⟩ := h.2.2.1
  obtain ⟨_, _, hp'l'⟩ := h.2.2.2
  apply hI ⟨p.val, hp⟩ ⟨p'.val, hp'⟩ ⟨l.val, hl⟩ ⟨l'.val, hl'⟩
  · intro he
    apply hpp
    exact Fin.ext (congrArg (fun x : Fin N => x.val) he)
  · intro he
    apply hll
    exact Fin.ext (congrArg (fun x : Fin N => x.val) he)
  · exact ⟨hpl, hpl', hp'l, hp'l'⟩

lemma restrict_point (N : ℕ) (z : Fin ((N + 1) + (N + 1)) → Bool) (p : Fin N) :
    restrictInput N z (Fin.castAdd N p) =
      z (Fin.castAdd (N + 1) p.castSucc) := by
  unfold restrictInput
  congr 1
  apply Fin.ext
  simp [padWire, p.isLt]

lemma restrict_line (N : ℕ) (z : Fin ((N + 1) + (N + 1)) → Bool) (l : Fin N) :
    restrictInput N z (Fin.natAdd N l) =
      z (Fin.natAdd (N + 1) l.castSucc) := by
  unfold restrictInput
  congr 1
  apply Fin.ext
  change padWire N (N + l.val) = N + 1 + l.val
  unfold padWire
  split_ifs <;> omega

lemma computes_pad (N : ℕ) (I : Fin N → Fin N → Prop) (C : Circuit)
    (sem : ∀ z : Fin (N + N) → Bool, circuitFun (N + N) C z = true ↔
      ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) :
    ∀ z : Fin ((N + 1) + (N + 1)) → Bool,
      circuitFun ((N + 1) + (N + 1)) (padCircuit N C) z = true ↔
      ∃ p l : Fin (N + 1), padIncidence N I p l ∧
        z (Fin.castAdd (N + 1) p) = true ∧ z (Fin.natAdd (N + 1) l) = true := by
  intro z
  rw [circuitFun_agree, sem]
  constructor
  · rintro ⟨p, l, hi, hp, hl⟩
    refine ⟨p.castSucc, l.castSucc, ⟨p.isLt, l.isLt, hi⟩, ?_, ?_⟩
    · simpa only [restrict_point] using hp
    · simpa only [restrict_line] using hl
  · rintro ⟨p, l, ⟨hp, hl, hi⟩, hz, hw⟩
    refine ⟨⟨p.val, hp⟩, ⟨l.val, hl⟩, hi, ?_, ?_⟩
    · rw [restrict_point]
      exact hz
    · rw [restrict_line]
      exact hw

end Padding

end PEqualNP.Outside.L_meta_3451_aux
