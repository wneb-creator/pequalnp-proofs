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

namespace Restriction

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

lemma any_filterMap {α β : Type} (f : α → Option β) (g : β → Bool) (xs : List α) :
    (xs.filterMap f).any g = xs.any (fun x => ((f x).map g).getD false) := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    cases ha : f a <;> simp [ha, ih]

lemma all_filterMap {α β : Type} (f : α → Option β) (g : β → Bool) (xs : List α) :
    xs.all (fun x => ((f x).map g).getD false) =
      if xs.any (fun x => (f x).isNone) then false else (xs.filterMap f).all g := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    cases ha : f a with
    | none => simp [ha]
    | some b =>
      simp only [List.all_cons, ha, Option.map_some, Option.getD_some, List.any_cons,
        Option.isNone_some, Bool.false_or, List.filterMap_cons]
      rw [ih]
      split <;> simp_all

def wireMap {m n : ℕ} (ρ : Fin m → Option (Fin n)) (w : ℕ) : Option ℕ :=
  if h : w < m then (ρ ⟨w, h⟩).map Fin.val else some (n + (w - m))

def gate {m n : ℕ} (ρ : Fin m → Option (Fin n)) (g : Gate) : Gate :=
  match g.op with
  | .and =>
    if g.inputs.any (fun w => (wireMap ρ w).isNone) then ⟨.or, []⟩
    else ⟨.and, g.inputs.filterMap (wireMap ρ)⟩
  | op => ⟨op, g.inputs.filterMap (wireMap ρ)⟩

def circuit {m n : ℕ} (ρ : Fin m → Option (Fin n)) (C : Circuit) : Circuit :=
  ⟨C.gates.map (gate ρ), (wireMap ρ C.output).getD (n + C.size)⟩

def input {m n : ℕ} (ρ : Fin m → Option (Fin n)) (z : Fin n → Bool) : Fin m → Bool :=
  fun i => ((ρ i).map z).getD false

lemma wireMap_last {m n : ℕ} (ρ : Fin m → Option (Fin n)) (i t : ℕ) :
    wireMap ρ i = some (n + t) ↔ i = m + t := by
  unfold wireMap
  split_ifs with hi
  · cases hρ : ρ ⟨i, hi⟩ with
    | none => simp; omega
    | some k => simp only [Option.map_some, Option.some.injEq]; omega
  · simp only [Option.some.injEq]
    omega

lemma gate_value {m n : ℕ} (ρ : Fin m → Option (Fin n)) (g : Gate)
    (xs ys : List Bool) (hop : g.op = .and ∨ g.op = .or)
    (hxy : ∀ i, xs.getD i false = ((wireMap ρ i).map (fun j => ys.getD j false)).getD false) :
    g.op.eval (g.inputs.map (fun i => xs.getD i false)) =
      (gate ρ g).op.eval ((gate ρ g).inputs.map (fun i => ys.getD i false)) := by
  rcases g with ⟨op, ins⟩
  simp only at hop
  rcases hop with rfl | rfl
  · simp only [gate]
    split_ifs with hnone
    · simp only [GateOp.eval, List.all_map, List.map_nil, List.any_nil]
      simp only [Function.id_comp]
      simp_rw [hxy]
      rw [all_filterMap]
      simp [hnone]
    · simp only [GateOp.eval, List.all_map]
      simp only [Function.id_comp]
      simp_rw [hxy]
      rw [all_filterMap]
      simp [hnone]
  · simp only [gate, GateOp.eval, List.any_map]
    simp_rw [hxy]
    exact (any_filterMap _ _ _).symm

lemma getD_snoc {α : Type} (xs : List α) (a d : α) (i : ℕ) :
    (xs ++ [a]).getD i d = if i = xs.length then a else xs.getD i d := by
  by_cases hi : i < xs.length
  · rw [List.getD_append _ _ _ _ hi]
    simp [Nat.ne_of_lt hi]
  · rw [List.getD_append_right _ _ _ _ (by omega)]
    by_cases he : i = xs.length
    · simp [he]
    · rw [List.getD_eq_default _ _ (by simp; omega),
        List.getD_eq_default _ _ (by omega)]
      simp [he]

lemma extend_values {m n t : ℕ} (ρ : Fin m → Option (Fin n)) (xs ys : List Bool)
    (hx : xs.length = m + t) (hy : ys.length = n + t)
    (hxy : ∀ i, xs.getD i false = ((wireMap ρ i).map (fun j => ys.getD j false)).getD false)
    (b : Bool) :
    ∀ i, (xs ++ [b]).getD i false =
      ((wireMap ρ i).map (fun j => (ys ++ [b]).getD j false)).getD false := by
  intro i
  rw [getD_snoc]
  by_cases hi : i = m + t
  · have hm := (wireMap_last ρ i t).mpr hi
    rw [ite_eq_left (hi.trans hx.symm), hm]
    simp only [Option.map_some, Option.getD_some]
    rw [getD_snoc, hy, ite_eq_left rfl]
  · simp only [hx, hi, ↓reduceIte]
    rw [hxy]
    cases hm : wireMap ρ i with
    | none => rfl
    | some j =>
      have hj : j ≠ n + t := by
        intro he
        apply hi
        apply (wireMap_last ρ i t).mp
        simpa [he] using hm
      simp only [Option.map_some, Option.getD_some]
      rw [getD_snoc, hy, ite_eq_right hj]

def run (gs : List Gate) (xs : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map (fun i => w.getD i false))]) xs

lemma run_length (gs : List Gate) (xs : List Bool) :
    (run gs xs).length = xs.length + gs.length := by
  induction gs generalizing xs with
  | nil => simp [run]
  | cons g gs ih =>
    simp only [run, List.foldl_cons] at *
    rw [ih]
    simp
    omega

lemma initial_values {m n : ℕ} (ρ : Fin m → Option (Fin n)) (z : Fin n → Bool) :
    ∀ i, (List.ofFn (input ρ z)).getD i false =
      ((wireMap ρ i).map (fun j => (List.ofFn z).getD j false)).getD false := by
  intro i
  by_cases hi : i < m
  · cases hr : ρ ⟨i, hi⟩ with
    | none => simp [input, wireMap, hi, hr, List.getD_eq_getElem?_getD]
    | some j => simp [input, wireMap, hi, hr, List.getD_eq_getElem?_getD]
  · have hni : ¬ n + (i - m) < n := by omega
    simp [wireMap, hi, hni, List.getD_eq_getElem?_getD]

lemma run_values {m n : ℕ} (ρ : Fin m → Option (Fin n)) (gs : List Gate)
    (hop : ∀ g ∈ gs, g.op = .and ∨ g.op = .or)
    (t : ℕ) (xs ys : List Bool) (hx : xs.length = m + t) (hy : ys.length = n + t)
    (hxy : ∀ i, xs.getD i false = ((wireMap ρ i).map (fun j => ys.getD j false)).getD false) :
    ∀ i, (run gs xs).getD i false =
      ((wireMap ρ i).map (fun j => (run (gs.map (gate ρ)) ys).getD j false)).getD false := by
  induction gs generalizing t xs ys with
  | nil => exact hxy
  | cons g gs ih =>
    have hv := gate_value ρ g xs ys (hop g (by simp)) hxy
    change ∀ i, (run gs (xs ++ [g.op.eval (g.inputs.map (fun j => xs.getD j false))])).getD i false = _
    apply ih (fun g hg => hop g (by simp [hg])) (t + 1)
    · simp [hx]
      omega
    · simp [hy]
      omega
    · dsimp only
      rw [← hv]
      exact extend_values ρ xs ys hx hy hxy _

lemma wires {m n : ℕ} (ρ : Fin m → Option (Fin n)) (C : Circuit)
    (hmono : Monotone2 C) (z : Fin n → Bool) :
    ∀ i, (C.wires (List.ofFn (input ρ z))).getD i false =
      ((wireMap ρ i).map (fun j => ((circuit ρ C).wires (List.ofFn z)).getD j false)).getD false := by
  apply run_values ρ C.gates _ 0 (List.ofFn (input ρ z)) (List.ofFn z)
    (by simp) (by simp) (initial_values ρ z)
  intro g hg
  simpa using (hmono g hg).1

lemma size {m n : ℕ} (ρ : Fin m → Option (Fin n)) (C : Circuit) :
    (circuit ρ C).size = C.size := by
  simp [circuit, Circuit.size]

lemma mono {m n : ℕ} (ρ : Fin m → Option (Fin n)) (C : Circuit)
    (hmono : Monotone2 C) : Monotone2 (circuit ρ C) := by
  intro g hg
  obtain ⟨g0, hg0, rfl⟩ := List.mem_map.mp hg
  have hm := hmono g0 hg0
  have hop : g0.op = .and ∨ g0.op = .or := by simpa using hm.1
  have hlen := List.length_filterMap_le (f := wireMap ρ) (l := g0.inputs)
  rcases g0 with ⟨op, ins⟩
  simp only at hop hm hlen
  rcases hop with rfl | rfl
  · simp only [gate]
    split_ifs <;> simp_all
    omega
  · simp only [gate]
    simp_all
    omega

lemma eval {m n : ℕ} (ρ : Fin m → Option (Fin n)) (C : Circuit)
    (hmono : Monotone2 C) (z : Fin n → Bool) :
    circuitFun n (circuit ρ C) z = circuitFun m C (input ρ z) := by
  have hv := wires ρ C hmono z C.output
  change ((circuit ρ C).wires (List.ofFn z)).getD (wireMap ρ C.output |>.getD (n + C.size)) false = _
  cases ho : wireMap ρ C.output with
  | some j => simpa only [ho, Option.map_some, Option.getD_some, circuitFun, Circuit.eval] using hv.symm
  | none =>
    have hl : ((circuit ρ C).wires (List.ofFn z)).length = n + C.size := by
      change (run (C.gates.map (gate ρ)) (List.ofFn z)).length = _
      simp [run_length, Circuit.size]
    simp only [Option.getD_none]
    rw [List.getD_eq_default _ _ hl.le]
    simpa only [ho, Option.map_none, Option.getD_none, circuitFun, Circuit.eval] using hv.symm

lemma gate_value_at {m n : ℕ} (ρ : Fin m → Option (Fin n)) (C : Circuit)
    (hmono : Monotone2 C) (z : Fin n → Bool) (j : ℕ) :
    PEqualNP.EdgeOwnership.gateVal n (circuit ρ C) j z =
      PEqualNP.EdgeOwnership.gateVal m C j (input ρ z) := by
  have hv := wires ρ C hmono z (m + j)
  have hm := (wireMap_last ρ (m + j) j).mpr rfl
  simpa only [hm, Option.map_some, Option.getD_some, PEqualNP.EdgeOwnership.gateVal] using hv.symm

lemma input_mem {m n : ℕ} (ρ : Fin m → Option (Fin n)) (g : Gate) (i : ℕ)
    (hi : i ∈ (gate ρ g).inputs) : ∃ w ∈ g.inputs, wireMap ρ w = some i := by
  rcases g with ⟨op, ins⟩
  cases op <;> simp only [gate] at hi
  · split_ifs at hi with hnone
    · simp at hi
    · exact List.mem_filterMap.mp hi
  all_goals exact List.mem_filterMap.mp hi

lemma mapped_lt {m n : ℕ} (ρ : Fin m → Option (Fin n)) (w i t : ℕ)
    (hw : w < m + t) (hi : wireMap ρ w = some i) : i < n + t := by
  unfold wireMap at hi
  split_ifs at hi with hm
  · cases hρ : ρ ⟨w, hm⟩ with
    | none => simp [hρ] at hi
    | some k => simp only [hρ, Option.map_some, Option.some.injEq] at hi; omega
  · simp only [Option.some.injEq] at hi
    omega

lemma gate_at {m n : ℕ} (ρ : Fin m → Option (Fin n)) (C : Circuit) (j : ℕ) :
    NestedCover.gateAt (circuit ρ C) j = gate ρ (NestedCover.gateAt C j) := by
  exact List.getD_map C.gates ⟨.or, []⟩ (gate ρ)

lemma readsBack {m n : ℕ} (ρ : Fin m → Option (Fin n)) (C : Circuit)
    (hback : NestedCover.ReadsBack m C) : NestedCover.ReadsBack n (circuit ρ C) := by
  intro j hj i hi
  rw [gate_at] at hi
  obtain ⟨w, hw, hmap⟩ := input_mem ρ _ i hi
  have hj' : j < C.gates.length := by simpa [circuit] using hj
  exact mapped_lt ρ w i j (hback j hj' w hw) hmap

lemma gate_and_origin {m n : ℕ} (ρ : Fin m → Option (Fin n)) (g : Gate)
    (h : (gate ρ g).op = .and) : g.op = .and := by
  rcases g with ⟨op, ins⟩
  cases op <;> simp_all [gate]

lemma and_origin {m n : ℕ} (ρ : Fin m → Option (Fin n)) (C : Circuit) (j : ℕ)
    (h : (NestedCover.gateAt (circuit ρ C) j).op = .and) :
    (NestedCover.gateAt C j).op = .and := by
  rw [gate_at] at h
  exact gate_and_origin ρ _ h

lemma rejects {m n : ℕ} (ρ : Fin m → Option (Fin n)) (C : Circuit)
    (hmono : Monotone2 C) (z : Fin n → Bool)
    (h : ∀ j < C.gates.length, (NestedCover.gateAt C j).op = .and →
      PEqualNP.EdgeOwnership.gateVal m C j (input ρ z) = false) :
    ∀ j < (circuit ρ C).gates.length, (NestedCover.gateAt (circuit ρ C) j).op = .and →
      PEqualNP.EdgeOwnership.gateVal n (circuit ρ C) j z = false := by
  intro j hj hand
  rw [gate_value_at ρ C hmono z j]
  exact h j (by simpa [circuit] using hj) (and_origin ρ C j hand)

end Restriction

namespace Bridge

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_3451_aux.Padding

def inputMap (N : ℕ) : Fin ((N + 1) + (N + 1)) → Option (Fin (N + N)) :=
  Fin.addCases
    (fun p : Fin (N + 1) => if h : p.val < N then some (Fin.castAdd N ⟨p.val, h⟩) else none)
    (fun l : Fin (N + 1) => if h : l.val < N then some (Fin.natAdd N ⟨l.val, h⟩) else none)

def embedInput (N : ℕ) : Fin (N + N) → Fin ((N + 1) + (N + 1)) :=
  Fin.addCases (fun p => Fin.castAdd (N + 1) p.castSucc)
    (fun l => Fin.natAdd (N + 1) l.castSucc)

lemma inputMap_embed (N : ℕ) (i : Fin (N + N)) :
    inputMap N (embedInput N i) = some i := by
  refine Fin.addCases (fun p => ?_) (fun l => ?_) i
  · rw [embedInput, Fin.addCases_left, inputMap, Fin.addCases_left]
    simp only [Fin.val_castSucc]
    rw [dite_eq_left p.isLt]
  · rw [embedInput, Fin.addCases_right, inputMap, Fin.addCases_right]
    simp only [Fin.val_castSucc]
    rw [dite_eq_left l.isLt]

lemma inputMap_some (N : ℕ) (k : Fin ((N + 1) + (N + 1))) (i : Fin (N + N))
    (h : inputMap N k = some i) : embedInput N i = k := by
  revert h
  refine Fin.addCases (fun p => ?_) (fun l => ?_) k
  · intro h
    simp only [inputMap, Fin.addCases_left] at h
    split_ifs at h with hp
    cases Option.some.inj h
    rw [embedInput, Fin.addCases_left]
    rfl
  · intro h
    simp only [inputMap, Fin.addCases_right] at h
    split_ifs at h with hl
    cases Option.some.inj h
    rw [embedInput, Fin.addCases_right]
    rfl

lemma inputMap_iff (N : ℕ) (k : Fin ((N + 1) + (N + 1))) (i : Fin (N + N)) :
    inputMap N k = some i ↔ k = embedInput N i := by
  constructor
  · exact fun h => (inputMap_some N k i h).symm
  · rintro rfl
    exact inputMap_embed N i

lemma lifted_singleton (N : ℕ) (i : Fin (N + N)) :
    PEqualNP.Outside.L_meta_3451_aux.Restriction.input (inputMap N) (fun k => decide (k = i)) =
      fun k => decide (k = embedInput N i) := by
  funext k
  unfold PEqualNP.Outside.L_meta_3451_aux.Restriction.input
  cases h : inputMap N k with
  | none =>
    have hn : k ≠ embedInput N i := by
      intro he
      have := (inputMap_iff N k i).mpr he
      rw [h] at this
      cases this
    simp [hn]
  | some j =>
    simp only [Option.map_some, Option.getD_some]
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq]
    constructor
    · intro he
      subst j
      exact (inputMap_iff N k i).mp h
    · intro he
      have hh := (inputMap_iff N k i).mpr he
      rw [h] at hh
      exact Option.some.inj hh

lemma lifted_pair (N : ℕ) (i j : Fin (N + N)) :
    PEqualNP.Outside.L_meta_3451_aux.Restriction.input (inputMap N)
      (fun k => decide (k = i ∨ k = j)) =
      fun k => decide (k = embedInput N i ∨ k = embedInput N j) := by
  funext k
  have hi := congrFun (lifted_singleton N i) k
  have hj := congrFun (lifted_singleton N j) k
  unfold PEqualNP.Outside.L_meta_3451_aux.Restriction.input at hi hj ⊢
  cases h : inputMap N k <;> simp_all

open PEqualNP.Outside.L_meta_3451_aux

lemma computes_restrict (N : ℕ) (I : Fin N → Fin N → Prop) (C : Circuit)
    (hC : Monotone2 C)
    (sem : ∀ z : Fin ((N + 1) + (N + 1)) → Bool,
      circuitFun ((N + 1) + (N + 1)) C z = true ↔
      ∃ p l : Fin (N + 1), padIncidence N I p l ∧
        z (Fin.castAdd (N + 1) p) = true ∧ z (Fin.natAdd (N + 1) l) = true) :
    ∀ z : Fin (N + N) → Bool,
      circuitFun (N + N) (Restriction.circuit (inputMap N) C) z = true ↔
      ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true := by
  intro z
  rw [Restriction.eval (inputMap N) C hC z, sem]
  constructor
  · rintro ⟨p, l, ⟨hp, hl, hi⟩, hz, hw⟩
    refine ⟨⟨p.val, hp⟩, ⟨l.val, hl⟩, hi, ?_, ?_⟩
    · simpa only [Restriction.input, inputMap, Fin.addCases_left, dite_eq_left hp,
        Option.map_some, Option.getD_some] using hz
    · simpa only [Restriction.input, inputMap, Fin.addCases_right, dite_eq_left hl,
        Option.map_some, Option.getD_some] using hw
  · rintro ⟨p, l, hi, hp, hl⟩
    refine ⟨p.castSucc, l.castSucc, ⟨p.isLt, l.isLt, hi⟩, ?_, ?_⟩
    · simpa only [Restriction.input, inputMap, Fin.addCases_left, Fin.val_castSucc,
        dite_eq_left p.isLt, Option.map_some, Option.getD_some] using hp
    · simpa only [Restriction.input, inputMap, Fin.addCases_right, Fin.val_castSucc,
        dite_eq_left l.isLt, Option.map_some, Option.getD_some] using hl

def PairNormalizes : Prop :=
  ∀ (N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (C : Circuit),
    (∀ p p' l l' : Fin N, p ≠ p' → l ≠ l' → ¬ (I p l ∧ I p l' ∧ I p' l ∧ I p' l')) →
    Monotone2 C → NestedCover.ReadsBack (N + N) C →
    (∀ z : Fin (N + N) → Bool, circuitFun (N + N) C z = true ↔
      ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) →
    ∃ D : Circuit, Monotone2 D ∧ NestedCover.ReadsBack (N + N) D ∧ D.size ≤ C.size ∧
      (∀ z : Fin (N + N) → Bool, circuitFun (N + N) D z = true ↔
        ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) ∧
      (∀ j < D.gates.length, (NestedCover.gateAt D j).op = GateOp.and →
        ∀ p l : Fin N, ¬ I p l →
          (D.wires (List.ofFn (fun k : Fin (N + N) =>
            decide (k = Fin.castAdd N p ∨ k = Fin.natAdd N l)))).getD
              (N + N + j) false = false)

lemma full_of_pair (hyp : PairNormalizes) :
    ∀ (N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (C : Circuit),
      (∀ p p' l l' : Fin N, p ≠ p' → l ≠ l' → ¬ (I p l ∧ I p l' ∧ I p' l ∧ I p' l')) →
      Monotone2 C → NestedCover.ReadsBack (N + N) C →
      (∀ z : Fin (N + N) → Bool, circuitFun (N + N) C z = true ↔
        ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) →
      ∃ D : Circuit, Monotone2 D ∧ NestedCover.ReadsBack (N + N) D ∧ D.size ≤ C.size ∧
        (∀ z : Fin (N + N) → Bool, circuitFun (N + N) D z = true ↔
          ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) ∧
        (∀ j < D.gates.length, (NestedCover.gateAt D j).op = GateOp.and →
          ∀ p l : Fin N, ¬ I p l →
            (D.wires (List.ofFn (fun k : Fin (N + N) =>
              decide (k = Fin.castAdd N p ∨ k = Fin.natAdd N l)))).getD
                (N + N + j) false = false) ∧
        (∀ j < D.gates.length, (NestedCover.gateAt D j).op = GateOp.and →
          (∀ p : Fin N, (D.wires (List.ofFn (fun k : Fin (N + N) =>
            decide (k = Fin.castAdd N p)))).getD (N + N + j) false = false) ∧
          ∀ l : Fin N, (D.wires (List.ofFn (fun k : Fin (N + N) =>
            decide (k = Fin.natAdd N l)))).getD (N + N + j) false = false) := by
  classical
  intro N I _ C hfour hmono hback sem
  obtain ⟨D, dm, db, ds, de, dp⟩ := hyp (N + 1) (padIncidence N I) (padCircuit N C)
    (noFourCycle_pad N I hfour) (monotone_pad N C hmono) (readsBack_pad N C hback)
    (computes_pad N I C sem)
  have dz := singleton_clean_of_nonedge (N + 1) (padIncidence N I) D dm
    (point_misses N I) (line_misses N I) dp
  refine ⟨Restriction.circuit (inputMap N) D, Restriction.mono _ D dm,
    Restriction.readsBack _ D db, ?_, computes_restrict N I D dm de, ?_, ?_⟩
  · rw [Restriction.size]
    simpa only [size_pad] using ds
  · intro j hj hand p l hn
    change PEqualNP.EdgeOwnership.gateVal (N + N)
      (Restriction.circuit (inputMap N) D) j
      (fun k => decide (k = Fin.castAdd N p ∨ k = Fin.natAdd N l)) = false
    rw [Restriction.gate_value_at _ D dm, lifted_pair]
    simp only [embedInput, Fin.addCases_left, Fin.addCases_right]
    apply dp j (by simpa only [Restriction.circuit, List.length_map] using hj)
      (Restriction.and_origin _ D j hand) p.castSucc l.castSucc
    rintro ⟨_, _, hi⟩
    exact hn hi
  · intro j hj hand
    have hj' : j < D.gates.length := by
      simpa only [Restriction.circuit, List.length_map] using hj
    have hand' := Restriction.and_origin _ D j hand
    constructor
    · intro p
      change PEqualNP.EdgeOwnership.gateVal (N + N)
        (Restriction.circuit (inputMap N) D) j
        (fun k => decide (k = Fin.castAdd N p)) = false
      rw [Restriction.gate_value_at _ D dm, lifted_singleton]
      simp only [embedInput, Fin.addCases_left]
      exact (dz j hj' hand').1 p.castSucc
    · intro l
      change PEqualNP.EdgeOwnership.gateVal (N + N)
        (Restriction.circuit (inputMap N) D) j
        (fun k => decide (k = Fin.natAdd N l)) = false
      rw [Restriction.gate_value_at _ D dm, lifted_singleton]
      simp only [embedInput, Fin.addCases_right]
      exact (dz j hj' hand').2 l.castSucc

lemma pair_iff_full : PairNormalizes ↔ (∀ (N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (C : PEqualNP.CircuitLowerBounds.Circuit), (∀ p p' l l' : Fin N, p ≠ p' → l ≠ l' → ¬ (I p l ∧ I p l' ∧ I p' l ∧ I p' l')) → PEqualNP.MetaComplexity.Monotone2 C → PEqualNP.MetaComplexity.NestedCover.ReadsBack (N + N) C → (∀ z : Fin (N + N) → Bool, PEqualNP.MetaComplexity.circuitFun (N + N) C z = true ↔ ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) → ∃ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 D ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (N + N) D ∧ D.size ≤ C.size ∧ (∀ z : Fin (N + N) → Bool, PEqualNP.MetaComplexity.circuitFun (N + N) D z = true ↔ ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) ∧ (∀ j < D.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt D j).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∀ p0 l0 : Fin N, ¬ I p0 l0 → (D.wires (List.ofFn (fun ke : Fin (N + N) => decide (ke = Fin.castAdd N p0 ∨ ke = Fin.natAdd N l0)))).getD (N + N + j) false = false) ∧ (∀ j < D.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt D j).op = PEqualNP.CircuitLowerBounds.GateOp.and → (∀ p : Fin N, (D.wires (List.ofFn (fun kc : Fin (N + N) => decide (kc = Fin.castAdd N p)))).getD (N + N + j) false = false) ∧ ∀ l : Fin N, (D.wires (List.ofFn (fun kd : Fin (N + N) => decide (kd = Fin.natAdd N l)))).getD (N + N + j) false = false)) := by
  constructor
  · exact full_of_pair
  · intro h N I _ C hfour hm hb hs
    obtain ⟨D, dm, db, ds, de, dp, _⟩ := h N I C hfour hm hb hs
    exact ⟨D, dm, db, ds, de, dp⟩

end Bridge

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def sharedOrExample : Circuit :=
  ⟨[⟨.or, [0, 1]⟩, ⟨.or, [3, 4]⟩, ⟨.and, [6, 7]⟩,
    ⟨.and, [2, 5]⟩, ⟨.or, [8, 9]⟩, ⟨.and, [10, 0]⟩,
    ⟨.and, [10, 4]⟩, ⟨.or, [11, 12]⟩, ⟨.or, [13, 9]⟩], 14⟩

def sharedOrIncidence (p l : Fin 3) : Prop :=
  (p = 0 ∧ (l = 0 ∨ l = 1)) ∨ (p = 1 ∧ l = 1) ∨ (p = 2 ∧ l = 2)

def sharedOrClean : Circuit :=
  ⟨[⟨.or, [3, 4]⟩, ⟨.and, [0, 6]⟩, ⟨.and, [1, 4]⟩,
    ⟨.or, [7, 8]⟩, ⟨.and, [2, 5]⟩, ⟨.or, [9, 10]⟩], 11⟩

lemma sharedOrExample_sizes : sharedOrExample.size = 9 ∧ sharedOrClean.size = 6 := by
  decide

set_option synthInstance.maxSize 1000 in
lemma sharedOrIncidence_c4_free :
    ∀ p p' l l' : Fin 3, p ≠ p' → l ≠ l' →
      ¬ (sharedOrIncidence p l ∧ sharedOrIncidence p l' ∧
        sharedOrIncidence p' l ∧ sharedOrIncidence p' l') := by
  unfold sharedOrIncidence
  decide

lemma sharedOrExample_model :
    Monotone2 sharedOrExample ∧ NestedCover.ReadsBack 6 sharedOrExample ∧
      Monotone2 sharedOrClean ∧ NestedCover.ReadsBack 6 sharedOrClean := by
  let := NestedCover.gateOpDecEq
  unfold Monotone2
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
lemma sharedOrExample_computes :
    ∀ z : Fin 6 → Bool, circuitFun 6 sharedOrExample z = true ↔
      ∃ p l : Fin 3, sharedOrIncidence p l ∧
        z (Fin.castAdd 3 p) = true ∧ z (Fin.natAdd 3 l) = true := by
  unfold sharedOrIncidence
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
lemma sharedOrClean_computes :
    ∀ z : Fin 6 → Bool, circuitFun 6 sharedOrClean z = true ↔
      ∃ p l : Fin 3, sharedOrIncidence p l ∧
        z (Fin.castAdd 3 p) = true ∧ z (Fin.natAdd 3 l) = true := by
  unfold sharedOrIncidence
  decide

lemma sharedOrExample_dirty :
    ¬ sharedOrIncidence 1 0 ∧
      (sharedOrExample.wires (List.ofFn (fun k : Fin 6 => decide (k = 1 ∨ k = 3)))).getD
        8 false = true := by
  unfold sharedOrIncidence
  decide

lemma sharedOrExample_replace_left :
    circuitFun 6 (PEqualNP.FactorSubst.substReads sharedOrExample 6 2 (fun _ => 6))
      (fun k => decide (k = 0)) = true ∧
    circuitFun 6 sharedOrExample (fun k => decide (k = 0)) = false := by
  decide

lemma sharedOrExample_replace_right :
    circuitFun 6 (PEqualNP.FactorSubst.substReads sharedOrExample 6 2 (fun _ => 7))
      (fun k => decide (k = 4)) = true ∧
    circuitFun 6 sharedOrExample (fun k => decide (k = 4)) = false := by
  decide

lemma sharedOrExample_only_reader :
    PEqualNP.TopForm.readers 6 sharedOrExample 2 = {4} := by
  decide

lemma sharedOrExample_no_factor_substitution (sigma : ℕ → ℕ)
    (hs : sigma 4 = 6 ∨ sigma 4 = 7) :
    circuitFun 6 (PEqualNP.FactorSubst.substReads sharedOrExample 6 2 sigma) ≠
      circuitFun 6 sharedOrExample := by
  have heq : PEqualNP.FactorSubst.substReads sharedOrExample 6 2 sigma =
      PEqualNP.FactorSubst.substReads sharedOrExample 6 2 (fun _ => sigma 4) := by
    rfl
  rw [heq]
  rcases hs with hs | hs
  · rw [hs]
    intro he
    have hx := congrFun he (fun k => decide (k = 0))
    rw [sharedOrExample_replace_left.1, sharedOrExample_replace_left.2] at hx
    cases hx
  · rw [hs]
    intro he
    have hx := congrFun he (fun k => decide (k = 4))
    rw [sharedOrExample_replace_right.1, sharedOrExample_replace_right.2] at hx
    cases hx

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
set_option synthInstance.maxSize 1000 in
lemma sharedOrClean_rejects :
    (∀ j < sharedOrClean.gates.length, (NestedCover.gateAt sharedOrClean j).op = GateOp.and →
      ∀ p l : Fin 3, ¬ sharedOrIncidence p l →
        (sharedOrClean.wires (List.ofFn (fun k : Fin 6 =>
          decide (k = Fin.castAdd 3 p ∨ k = Fin.natAdd 3 l)))).getD (6 + j) false = false) ∧
    (∀ j < sharedOrClean.gates.length, (NestedCover.gateAt sharedOrClean j).op = GateOp.and →
      ∀ k : Fin 6, (sharedOrClean.wires (List.ofFn (fun w : Fin 6 => decide (w = k)))).getD
        (6 + j) false = false) := by
  let := NestedCover.gateOpDecEq
  unfold sharedOrIncidence
  decide

namespace Surgery

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma fold_length (gs : List Gate) (w : List Bool) :
    (gs.foldl step w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [step]
    omega

def oldCircuit (n : ℕ) (gs : List Gate) (a b c d : ℕ) : Circuit :=
  ⟨gs ++ [⟨.and, [a, b]⟩, ⟨.or, [c, d]⟩,
    ⟨.and, [n + gs.length, n + gs.length + 1]⟩], n + gs.length + 2⟩

def newCircuit (n : ℕ) (gs : List Gate) (a b c d : ℕ) : Circuit :=
  ⟨gs ++ [⟨.and, [c, b]⟩, ⟨.and, [d, a]⟩,
    ⟨.or, [n + gs.length, n + gs.length + 1]⟩], n + gs.length + 2⟩

lemma equal_size (n : ℕ) (gs : List Gate) (a b c d : ℕ) :
    (newCircuit n gs a b c d).size = (oldCircuit n gs a b c d).size := by
  simp [newCircuit, oldCircuit, Circuit.size]

lemma bool_split : ∀ a b c d : Bool, (c = true → a = true) → (d = true → b = true) →
    ((a && b) && (c || d)) = ((c && b) || (d && a)) := by
  decide

lemma run_three (w : List Bool) (a b c d : ℕ)
    (_ha : a < w.length) (_hb : b < w.length) (hc : c < w.length) (hd : d < w.length)
    (op0 op1 op2 : GateOp) :
    (([⟨op0, [a, b]⟩, ⟨op1, [c, d]⟩,
      ⟨op2, [w.length, w.length + 1]⟩] : List Gate).foldl step w).getD
      (w.length + 2) false =
    op2.eval [op0.eval [w.getD a false, w.getD b false],
      op1.eval [w.getD c false, w.getD d false]] := by
  let A := op0.eval [w.getD a false, w.getD b false]
  let B := op1.eval [w.getD c false, w.getD d false]
  have h0 : step w ⟨op0, [a, b]⟩ = w ++ [A] := rfl
  have h1 : step (w ++ [A]) ⟨op1, [c, d]⟩ = w ++ [A, B] := by
    simp only [step, List.map_cons, List.map_nil,
      List.getD_append _ _ _ _ hc, List.getD_append _ _ _ _ hd]
    simp [B, List.append_assoc]
  have h2 : step (w ++ [A, B]) ⟨op2, [w.length, w.length + 1]⟩ =
      w ++ [A, B, op2.eval [A, B]] := by
    simp [step, List.getD_eq_getElem?_getD, List.append_assoc]
  simp only [List.foldl_cons, List.foldl_nil, h0, h1, h2]
  simp [List.getD_eq_getElem?_getD, A, B]

lemma output_old (n : ℕ) (gs : List Gate) (a b c d : ℕ)
    (ha : a < n + gs.length) (hb : b < n + gs.length)
    (hc : c < n + gs.length) (hd : d < n + gs.length) (x : Fin n → Bool) :
    circuitFun n (oldCircuit n gs a b c d) x =
      (((( ⟨gs, 0⟩ : Circuit).wires (List.ofFn x)).getD a false &&
        ((⟨gs, 0⟩ : Circuit).wires (List.ofFn x)).getD b false) &&
      (((⟨gs, 0⟩ : Circuit).wires (List.ofFn x)).getD c false ||
        ((⟨gs, 0⟩ : Circuit).wires (List.ofFn x)).getD d false)) := by
  let w := gs.foldl step (List.ofFn x)
  have hw : w.length = n + gs.length := by simp [w, fold_length]
  have h := run_three w a b c d (by omega) (by omega) (by omega) (by omega)
    GateOp.and GateOp.or GateOp.and
  rw [hw] at h
  change ((gs ++ ([⟨.and, [a, b]⟩, ⟨.or, [c, d]⟩,
    ⟨.and, [n + gs.length, n + gs.length + 1]⟩] : List Gate)).foldl step (List.ofFn x)).getD
    (n + gs.length + 2) false = ((w.getD a false && w.getD b false) &&
      (w.getD c false || w.getD d false))
  rw [List.foldl_append]
  simpa only [GateOp.eval, List.all_cons, List.all_nil, List.any_cons, List.any_nil,
    id_eq, Bool.and_true, Bool.or_false] using h

lemma output_new (n : ℕ) (gs : List Gate) (a b c d : ℕ)
    (ha : a < n + gs.length) (hb : b < n + gs.length)
    (hc : c < n + gs.length) (hd : d < n + gs.length) (x : Fin n → Bool) :
    circuitFun n (newCircuit n gs a b c d) x =
      (((( ⟨gs, 0⟩ : Circuit).wires (List.ofFn x)).getD c false &&
        ((⟨gs, 0⟩ : Circuit).wires (List.ofFn x)).getD b false) ||
      (((⟨gs, 0⟩ : Circuit).wires (List.ofFn x)).getD d false &&
        ((⟨gs, 0⟩ : Circuit).wires (List.ofFn x)).getD a false)) := by
  let w := gs.foldl step (List.ofFn x)
  have hw : w.length = n + gs.length := by simp [w, fold_length]
  have h := run_three w c b d a (by omega) (by omega) (by omega) (by omega)
    GateOp.and GateOp.and GateOp.or
  rw [hw] at h
  change ((gs ++ ([⟨.and, [c, b]⟩, ⟨.and, [d, a]⟩,
    ⟨.or, [n + gs.length, n + gs.length + 1]⟩] : List Gate)).foldl step (List.ofFn x)).getD
    (n + gs.length + 2) false = ((w.getD c false && w.getD b false) ||
      (w.getD d false && w.getD a false))
  rw [List.foldl_append]
  simpa only [GateOp.eval, List.all_cons, List.all_nil, List.any_cons, List.any_nil,
    id_eq, Bool.and_true, Bool.or_false] using h

lemma same_function (n : ℕ) (gs : List Gate) (a b c d : ℕ)
    (ha : a < n + gs.length) (hb : b < n + gs.length)
    (hc : c < n + gs.length) (hd : d < n + gs.length)
    (hca : ∀ x : Fin n → Bool,
      ((⟨gs, 0⟩ : Circuit).wires (List.ofFn x)).getD c false = true →
      ((⟨gs, 0⟩ : Circuit).wires (List.ofFn x)).getD a false = true)
    (hdb : ∀ x : Fin n → Bool,
      ((⟨gs, 0⟩ : Circuit).wires (List.ofFn x)).getD d false = true →
      ((⟨gs, 0⟩ : Circuit).wires (List.ofFn x)).getD b false = true) :
    circuitFun n (newCircuit n gs a b c d) = circuitFun n (oldCircuit n gs a b c d) := by
  funext x
  rw [output_new n gs a b c d ha hb hc hd x, output_old n gs a b c d ha hb hc hd x]
  exact (bool_split _ _ _ _ (hca x) (hdb x)).symm

lemma monotone_models (n : ℕ) (gs : List Gate) (a b c d : ℕ)
    (hm : Monotone2 (⟨gs, 0⟩ : Circuit)) :
    Monotone2 (oldCircuit n gs a b c d) ∧ Monotone2 (newCircuit n gs a b c d) := by
  constructor
  · intro g hg
    simp [oldCircuit] at hg
    rcases hg with hg | rfl | rfl | rfl
    · exact hm g hg
    all_goals simp
  · intro g hg
    simp [newCircuit] at hg
    rcases hg with hg | rfl | rfl | rfl
    · exact hm g hg
    all_goals simp

lemma readsBack_snoc (n : ℕ) (gs : List Gate) (g : Gate) (out : ℕ)
    (hback : ReadsBack n (⟨gs, 0⟩ : Circuit))
    (hg : ∀ i ∈ g.inputs, i < n + gs.length) :
    ReadsBack n (⟨gs ++ [g], out⟩ : Circuit) := by
  intro j hj i hi
  by_cases hlt : j < gs.length
  · have he : gateAt (⟨gs ++ [g], out⟩ : Circuit) j = gateAt (⟨gs, 0⟩ : Circuit) j := by
      exact List.getD_append _ _ _ _ hlt
    rw [he] at hi
    exact hback j hlt i hi
  · have heq : j = gs.length := by
      change j < (gs ++ [g]).length at hj
      simp only [List.length_append, List.length_singleton] at hj
      omega
    subst j
    have he : gateAt (⟨gs ++ [g], out⟩ : Circuit) gs.length = g := by
      simp [gateAt, List.getD_eq_getElem?_getD]
    rw [he] at hi
    exact hg i hi

lemma back_models (n : ℕ) (gs : List Gate) (a b c d : ℕ)
    (ha : a < n + gs.length) (hb : b < n + gs.length)
    (hc : c < n + gs.length) (hd : d < n + gs.length)
    (hback : ReadsBack n (⟨gs, 0⟩ : Circuit)) :
    ReadsBack n (oldCircuit n gs a b c d) ∧ ReadsBack n (newCircuit n gs a b c d) := by
  have first (u v : ℕ) (hu : u < n + gs.length) (hv : v < n + gs.length) (op : GateOp) :
      ReadsBack n (⟨gs ++ [⟨op, [u, v]⟩], 0⟩ : Circuit) := by
    apply readsBack_snoc n gs _ 0 hback
    intro i hi
    simp at hi
    rcases hi with rfl | rfl <;> assumption
  have three (u v r s : ℕ) (hu : u < n + gs.length) (hv : v < n + gs.length)
      (hr : r < n + gs.length) (hs : s < n + gs.length) (op0 op1 op2 : GateOp) :
      ReadsBack n (⟨gs ++ [⟨op0, [u, v]⟩, ⟨op1, [r, s]⟩,
        ⟨op2, [n + gs.length, n + gs.length + 1]⟩], n + gs.length + 2⟩ : Circuit) := by
    have h0 := first u v hu hv op0
    have h1 : ReadsBack n (⟨(gs ++ [⟨op0, [u, v]⟩]) ++ [⟨op1, [r, s]⟩], 0⟩ : Circuit) := by
      apply readsBack_snoc n _ _ 0 h0
      intro i hi
      simp at hi
      simp only [List.length_append, List.length_singleton]
      rcases hi with rfl | rfl <;> omega
    have h2 := readsBack_snoc n _ ⟨op2, [n + gs.length, n + gs.length + 1]⟩
      (n + gs.length + 2) h1 (by
        intro i hi
        simp at hi
        simp only [List.length_append, List.length_singleton]
        rcases hi with rfl | rfl <;> omega)
    simpa only [List.append_assoc, List.cons_append, List.nil_append] using h2
  exact ⟨three a b c d ha hb hc hd .and .or .and,
    three c b d a hc hb hd ha .and .and .or⟩

lemma run_three_wires (w : List Bool) (a b c d : ℕ)
    (hc : c < w.length) (hd : d < w.length) (op0 op1 op2 : GateOp) :
    ([⟨op0, [a, b]⟩, ⟨op1, [c, d]⟩,
      ⟨op2, [w.length, w.length + 1]⟩] : List Gate).foldl step w =
    w ++ [op0.eval [w.getD a false, w.getD b false],
      op1.eval [w.getD c false, w.getD d false],
      op2.eval [op0.eval [w.getD a false, w.getD b false],
        op1.eval [w.getD c false, w.getD d false]]] := by
  let A := op0.eval [w.getD a false, w.getD b false]
  let B := op1.eval [w.getD c false, w.getD d false]
  have h0 : step w ⟨op0, [a, b]⟩ = w ++ [A] := rfl
  have h1 : step (w ++ [A]) ⟨op1, [c, d]⟩ = w ++ [A, B] := by
    simp only [step, List.map_cons, List.map_nil,
      List.getD_append _ _ _ _ hc, List.getD_append _ _ _ _ hd]
    simp [B, List.append_assoc]
  have h2 : step (w ++ [A, B]) ⟨op2, [w.length, w.length + 1]⟩ =
      w ++ [A, B, op2.eval [A, B]] := by
    simp [step, List.getD_eq_getElem?_getD, List.append_assoc]
  simp only [List.foldl_cons, List.foldl_nil, h0, h1, h2]
  rfl

lemma wires_new (n : ℕ) (gs : List Gate) (a b c d : ℕ)
    (ha : a < n + gs.length) (hd : d < n + gs.length) (x : Fin n → Bool) :
    let w := (⟨gs, 0⟩ : Circuit).wires (List.ofFn x)
    (newCircuit n gs a b c d).wires (List.ofFn x) =
      w ++ [w.getD c false && w.getD b false, w.getD d false && w.getD a false,
        (w.getD c false && w.getD b false) || (w.getD d false && w.getD a false)] := by
  let w := gs.foldl step (List.ofFn x)
  have hw : w.length = n + gs.length := by simp [w, fold_length]
  have h := run_three_wires w c b d a (by omega) (by omega)
    GateOp.and GateOp.and GateOp.or
  rw [hw] at h
  change (gs ++ ([⟨.and, [c, b]⟩, ⟨.and, [d, a]⟩,
    ⟨.or, [n + gs.length, n + gs.length + 1]⟩] : List Gate)).foldl step (List.ofFn x) =
    w ++ [w.getD c false && w.getD b false, w.getD d false && w.getD a false,
      (w.getD c false && w.getD b false) || (w.getD d false && w.getD a false)]
  rw [List.foldl_append]
  simpa only [GateOp.eval, List.all_cons, List.all_nil, List.any_cons, List.any_nil,
    id_eq, Bool.and_true, Bool.or_false] using h

lemma fold_early (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl step w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [List.foldl_cons]
    rw [ih (step w g) (by simp [step]; omega)]
    exact List.getD_append _ _ _ _ hi

lemma prefix_wire_new (n : ℕ) (gs : List Gate) (a b c d w : ℕ)
    (hw : w < n + gs.length) (x : Fin n → Bool) :
    ((newCircuit n gs a b c d).wires (List.ofFn x)).getD w false =
      ((⟨gs, 0⟩ : Circuit).wires (List.ofFn x)).getD w false := by
  change ((gs ++ ([⟨.and, [c, b]⟩, ⟨.and, [d, a]⟩,
    ⟨.or, [n + gs.length, n + gs.length + 1]⟩] : List Gate)).foldl step (List.ofFn x)).getD
    w false = (gs.foldl step (List.ofFn x)).getD w false
  rw [List.foldl_append]
  apply fold_early
  simpa [fold_length] using hw

lemma suffix_below_new_output (n : ℕ) (gs : List Gate) (a b c d : ℕ)
    (ha : a < n + gs.length) (hb : b < n + gs.length)
    (hc : c < n + gs.length) (hd : d < n + gs.length)
    (j : ℕ) (hge : gs.length ≤ j) (hj : j < (newCircuit n gs a b c d).gates.length)
    (hand : (gateAt (newCircuit n gs a b c d) j).op = GateOp.and)
    (x : Fin n → Bool)
    (ht : ((newCircuit n gs a b c d).wires (List.ofFn x)).getD (n + j) false = true) :
    circuitFun n (newCircuit n gs a b c d) x = true := by
  have hj' : j = gs.length ∨ j = gs.length + 1 ∨ j = gs.length + 2 := by
    simp only [newCircuit, List.length_append, List.length_cons, List.length_nil] at hj
    omega
  have hw : ((⟨gs, 0⟩ : Circuit).wires (List.ofFn x)).length = n + gs.length := by
    exact (fold_length gs (List.ofFn x)).trans (by simp)
  rw [output_new n gs a b c d ha hb hc hd x]
  rw [wires_new n gs a b c d ha hd x] at ht
  rcases hj' with rfl | rfl | rfl
  · have hA : (((⟨gs, 0⟩ : Circuit).wires (List.ofFn x)).getD c false &&
        ((⟨gs, 0⟩ : Circuit).wires (List.ofFn x)).getD b false) = true := by
      simpa [← hw, List.getD_eq_getElem?_getD] using ht
    rw [hA]
    rfl
  · have hB : (((⟨gs, 0⟩ : Circuit).wires (List.ofFn x)).getD d false &&
        ((⟨gs, 0⟩ : Circuit).wires (List.ofFn x)).getD a false) = true := by
      simpa [← Nat.add_assoc, ← hw, List.getD_eq_getElem?_getD] using ht
    rw [hB]
    exact Bool.or_true _
  · have ho : (gateAt (newCircuit n gs a b c d) (gs.length + 2)).op = GateOp.or := by
      simp [gateAt, newCircuit, List.getD_eq_getElem?_getD]
    rw [ho] at hand
    cases hand

lemma clean_new (n : ℕ) (gs : List Gate) (a b c d : ℕ)
    (ha : a < n + gs.length) (hb : b < n + gs.length)
    (hc : c < n + gs.length) (hd : d < n + gs.length)
    (F : (Fin n → Bool) → Bool)
    (hprefix : ∀ j < gs.length, (gateAt (⟨gs, 0⟩ : Circuit) j).op = GateOp.and →
      ∀ x : Fin n → Bool, F x = false →
        ((⟨gs, 0⟩ : Circuit).wires (List.ofFn x)).getD (n + j) false = false)
    (houtput : ∀ x : Fin n → Bool, circuitFun n (newCircuit n gs a b c d) x = F x) :
    ∀ j < (newCircuit n gs a b c d).gates.length,
      (gateAt (newCircuit n gs a b c d) j).op = GateOp.and →
      ∀ x : Fin n → Bool, F x = false →
        ((newCircuit n gs a b c d).wires (List.ofFn x)).getD (n + j) false = false := by
  intro j hj hand x hx
  by_cases hp : j < gs.length
  · have hgate : gateAt (newCircuit n gs a b c d) j = gateAt (⟨gs, 0⟩ : Circuit) j :=
      List.getD_append _ _ _ _ hp
    rw [hgate] at hand
    rw [prefix_wire_new n gs a b c d (n + j) (by omega) x]
    exact hprefix j hp hand x hx
  · cases hv : ((newCircuit n gs a b c d).wires (List.ofFn x)).getD (n + j) false with
    | false => rfl
    | true =>
      have h := suffix_below_new_output n gs a b c d ha hb hc hd j (by omega) hj hand x hv
      rw [houtput x, hx] at h
      cases h

lemma normalizes_suffix (n : ℕ) (gs : List Gate) (a b c d : ℕ)
    (ha : a < n + gs.length) (hb : b < n + gs.length)
    (hc : c < n + gs.length) (hd : d < n + gs.length)
    (hm : Monotone2 (⟨gs, 0⟩ : Circuit)) (hr : ReadsBack n (⟨gs, 0⟩ : Circuit))
    (hca : ∀ x : Fin n → Bool,
      ((⟨gs, 0⟩ : Circuit).wires (List.ofFn x)).getD c false = true →
      ((⟨gs, 0⟩ : Circuit).wires (List.ofFn x)).getD a false = true)
    (hdb : ∀ x : Fin n → Bool,
      ((⟨gs, 0⟩ : Circuit).wires (List.ofFn x)).getD d false = true →
      ((⟨gs, 0⟩ : Circuit).wires (List.ofFn x)).getD b false = true)
    (hprefix : ∀ j < gs.length, (gateAt (⟨gs, 0⟩ : Circuit) j).op = GateOp.and →
      ∀ x : Fin n → Bool, circuitFun n (oldCircuit n gs a b c d) x = false →
        ((⟨gs, 0⟩ : Circuit).wires (List.ofFn x)).getD (n + j) false = false) :
    Monotone2 (newCircuit n gs a b c d) ∧ ReadsBack n (newCircuit n gs a b c d) ∧
    (newCircuit n gs a b c d).size = (oldCircuit n gs a b c d).size ∧
    circuitFun n (newCircuit n gs a b c d) = circuitFun n (oldCircuit n gs a b c d) ∧
    ∀ j < (newCircuit n gs a b c d).gates.length,
      (gateAt (newCircuit n gs a b c d) j).op = GateOp.and →
      ∀ x : Fin n → Bool, circuitFun n (oldCircuit n gs a b c d) x = false →
        ((newCircuit n gs a b c d).wires (List.ofFn x)).getD (n + j) false = false := by
  have hf := same_function n gs a b c d ha hb hc hd hca hdb
  refine ⟨(monotone_models n gs a b c d hm).2, (back_models n gs a b c d ha hb hc hd hr).2,
    equal_size n gs a b c d, hf, ?_⟩
  exact clean_new n gs a b c d ha hb hc hd _ hprefix (fun x => congrFun hf x)

lemma bool_split_on_false : ∀ a b c d : Bool,
    (((a && b) && (c || d)) = false → c = true → a = true) →
    (((a && b) && (c || d)) = false → d = true → b = true) →
    ((a && b) && (c || d)) = ((c && b) || (d && a)) := by
  decide

lemma same_function_on_false (n : ℕ) (gs : List Gate) (a b c d : ℕ)
    (ha : a < n + gs.length) (hb : b < n + gs.length)
    (hc : c < n + gs.length) (hd : d < n + gs.length)
    (hca : ∀ x : Fin n → Bool, circuitFun n (oldCircuit n gs a b c d) x = false →
      ((⟨gs, 0⟩ : Circuit).wires (List.ofFn x)).getD c false = true →
      ((⟨gs, 0⟩ : Circuit).wires (List.ofFn x)).getD a false = true)
    (hdb : ∀ x : Fin n → Bool, circuitFun n (oldCircuit n gs a b c d) x = false →
      ((⟨gs, 0⟩ : Circuit).wires (List.ofFn x)).getD d false = true →
      ((⟨gs, 0⟩ : Circuit).wires (List.ofFn x)).getD b false = true) :
    circuitFun n (newCircuit n gs a b c d) = circuitFun n (oldCircuit n gs a b c d) := by
  funext x
  rw [output_new n gs a b c d ha hb hc hd x, output_old n gs a b c d ha hb hc hd x]
  symm
  apply bool_split_on_false
  · intro hf ht
    exact hca x ((output_old n gs a b c d ha hb hc hd x).trans hf) ht
  · intro hf ht
    exact hdb x ((output_old n gs a b c d ha hb hc hd x).trans hf) ht

lemma normalizes_suffix_on_false (n : ℕ) (gs : List Gate) (a b c d : ℕ)
    (ha : a < n + gs.length) (hb : b < n + gs.length)
    (hc : c < n + gs.length) (hd : d < n + gs.length)
    (hm : Monotone2 (⟨gs, 0⟩ : Circuit)) (hr : ReadsBack n (⟨gs, 0⟩ : Circuit))
    (hca : ∀ x : Fin n → Bool, circuitFun n (oldCircuit n gs a b c d) x = false →
      ((⟨gs, 0⟩ : Circuit).wires (List.ofFn x)).getD c false = true →
      ((⟨gs, 0⟩ : Circuit).wires (List.ofFn x)).getD a false = true)
    (hdb : ∀ x : Fin n → Bool, circuitFun n (oldCircuit n gs a b c d) x = false →
      ((⟨gs, 0⟩ : Circuit).wires (List.ofFn x)).getD d false = true →
      ((⟨gs, 0⟩ : Circuit).wires (List.ofFn x)).getD b false = true)
    (hprefix : ∀ j < gs.length, (gateAt (⟨gs, 0⟩ : Circuit) j).op = GateOp.and →
      ∀ x : Fin n → Bool, circuitFun n (oldCircuit n gs a b c d) x = false →
        ((⟨gs, 0⟩ : Circuit).wires (List.ofFn x)).getD (n + j) false = false) :
    Monotone2 (newCircuit n gs a b c d) ∧ ReadsBack n (newCircuit n gs a b c d) ∧
    (newCircuit n gs a b c d).size = (oldCircuit n gs a b c d).size ∧
    circuitFun n (newCircuit n gs a b c d) = circuitFun n (oldCircuit n gs a b c d) ∧
    ∀ j < (newCircuit n gs a b c d).gates.length,
      (gateAt (newCircuit n gs a b c d) j).op = GateOp.and →
      ∀ x : Fin n → Bool, circuitFun n (oldCircuit n gs a b c d) x = false →
        ((newCircuit n gs a b c d).wires (List.ofFn x)).getD (n + j) false = false := by
  have hf := same_function_on_false n gs a b c d ha hb hc hd hca hdb
  refine ⟨(monotone_models n gs a b c d hm).2, (back_models n gs a b c d ha hb hc hd hr).2,
    equal_size n gs a b c d, hf, ?_⟩
  exact clean_new n gs a b c d ha hb hc hd _ hprefix (fun x => congrFun hf x)

end Surgery

namespace Boundary

def Independent {ι : Type*} (E : ι → ι → Prop) (s : Finset ι) : Prop :=
  ∀ u ∈ s, ∀ v ∈ s, ¬ E u v

def MaximalIndependent {ι : Type*} (E : ι → ι → Prop) (s : Finset ι) : Prop :=
  Independent E s ∧ ∀ t : Finset ι, s ⊆ t → Independent E t → t = s

lemma exists_maximal_independent {ι : Type*} [Fintype ι] [DecidableEq ι]
    (E : ι → ι → Prop) (s : Finset ι) (hs : Independent E s) :
    ∃ t : Finset ι, s ⊆ t ∧ MaximalIndependent E t := by
  classical
  let family : Finset (Finset ι) := Finset.univ.filter fun t =>
    s ⊆ t ∧ Independent E t
  have hmem : s ∈ family := by simp [family, hs]
  obtain ⟨t, ht, hcard⟩ := family.exists_max_image Finset.card ⟨s, hmem⟩
  have hprops : s ⊆ t ∧ Independent E t := (Finset.mem_filter.mp ht).2
  refine ⟨t, hprops.1, hprops.2, ?_⟩
  intro u htu hu
  have huf : u ∈ family := by
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hprops.1.trans htu, hu⟩
  exact (Finset.eq_of_subset_of_card_le htu (hcard u huf)).symm

lemma boundary_complete {ι : Type*} [Fintype ι] [DecidableEq ι]
    (E : ι → ι → Prop) (g : (ι → Bool) → Bool)
    (hmono : ∀ x y : ι → Bool,
      (∀ i, x i = true → y i = true) → g x = true → g y = true)
    (hedge : ∀ u v, E u v → g (fun i => decide (i = u ∨ i = v)) = true)
    (hmax : ∀ s : Finset ι, MaximalIndependent E s →
      g (fun i => decide (i ∈ s)) = false) :
    ∀ x : ι → Bool, g x = true ↔ ∃ u v, E u v ∧ x u = true ∧ x v = true := by
  classical
  intro x
  constructor
  · intro hx
    by_contra hno
    let s : Finset ι := Finset.univ.filter fun i => x i = true
    have hs : Independent E s := by
      intro u hu v hv huv
      exact hno ⟨u, v, huv, (Finset.mem_filter.mp hu).2,
        (Finset.mem_filter.mp hv).2⟩
    obtain ⟨t, hst, ht⟩ := exists_maximal_independent E s hs
    have hxt : ∀ i, x i = true → decide (i ∈ t) = true := by
      intro i hi
      exact decide_eq_true (hst (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩))
    have httrue := hmono x (fun i => decide (i ∈ t)) hxt hx
    rw [hmax t ht] at httrue
    contradiction
  · rintro ⟨u, v, huv, hu, hv⟩
    apply hmono (fun i => decide (i = u ∨ i = v)) x _ (hedge u v huv)
    intro i hi
    rcases of_decide_eq_true hi with rfl | rfl
    · exact hu
    · exact hv

lemma maximal_iff_single_extensions {ι : Type*} [Fintype ι] [DecidableEq ι]
    (E : ι → ι → Prop) (s : Finset ι) :
    MaximalIndependent E s ↔ Independent E s ∧
      ∀ i, i ∉ s → ¬ Independent E (insert i s) := by
  constructor
  · rintro ⟨hs, hmax⟩
    refine ⟨hs, ?_⟩
    intro i hi hins
    have heq := hmax (insert i s) (Finset.subset_insert _ _) hins
    exact hi (heq ▸ Finset.mem_insert_self i s)
  · rintro ⟨hs, hsingle⟩
    refine ⟨hs, ?_⟩
    intro t hst ht
    apply Finset.Subset.antisymm _ hst
    intro i hi
    by_contra his
    apply hsingle i his
    intro u hu v hv
    apply ht u (Finset.insert_subset hi hst hu) v (Finset.insert_subset hi hst hv)

def edgeFunction {ι : Type*} [Fintype ι] (E : ι → ι → Prop) [DecidableRel E]
    (x : ι → Bool) : Bool :=
  decide (∃ u v, E u v ∧ x u = true ∧ x v = true)

lemma edgeFunction_false_iff {ι : Type*} [Fintype ι] [DecidableEq ι]
    (E : ι → ι → Prop) [DecidableRel E] (s : Finset ι) :
    edgeFunction E (fun i => decide (i ∈ s)) = false ↔ Independent E s := by
  classical
  simp only [edgeFunction, decide_eq_false_iff_not, decide_eq_true_eq]
  unfold Independent
  aesop

lemma boundary_complete_tests {ι : Type*} [Fintype ι] [DecidableEq ι]
    (E : ι → ι → Prop) [DecidableRel E] (g : (ι → Bool) → Bool)
    (hmono : ∀ x y : ι → Bool,
      (∀ i, x i = true → y i = true) → g x = true → g y = true)
    (hedge : ∀ u v, E u v → g (fun i => decide (i = u ∨ i = v)) = true)
    (hmax : ∀ x : ι → Bool, edgeFunction E x = false →
      (∀ i, x i = false →
        edgeFunction E (fun j => if j = i then true else x j) = true) →
      g x = false) :
    ∀ x : ι → Bool, g x = edgeFunction E x := by
  classical
  have hneg : ∀ s : Finset ι, MaximalIndependent E s →
      g (fun i => decide (i ∈ s)) = false := by
    intro s hs
    apply hmax _ ((edgeFunction_false_iff E s).mpr hs.1)
    intro i hi
    have his : i ∉ s := of_decide_eq_false hi
    have hn := (maximal_iff_single_extensions E s).mp hs |>.2 i his
    have hfunc : (fun j => if j = i then true else decide (j ∈ s)) =
        (fun j => decide (j ∈ insert i s)) := by
      funext j
      by_cases hji : j = i <;> simp [hji]
    rw [hfunc]
    have hnot := (edgeFunction_false_iff E (insert i s)).not.mpr hn
    cases heq : edgeFunction E (fun j => decide (j ∈ insert i s)) <;> simp_all
  intro x
  have heq := boundary_complete E g hmono hedge hneg x
  have hgraph : edgeFunction E x = true ↔
      ∃ u v, E u v ∧ x u = true ∧ x v = true := by simp [edgeFunction]
  have hbool := heq.trans hgraph.symm
  cases hx : g x <;> cases hf : edgeFunction E x <;> simp_all

end Boundary

namespace Four

abbrev Mask := BitVec 16

def inputs : List Mask := [43690, 52428, 61680, 65280]

def choices (xs : List Mask) : List Mask :=
  (0 :: 65535 :: xs ++ xs.flatMap (fun a => xs.flatMap (fun b => [a &&& b, a ||| b]))).eraseDups

def possible : ℕ → List Mask → Mask → Bool
  | 0, xs, t => t == 0 || xs.contains t
  | k + 1, xs, t => (t == 0 || xs.contains t) ||
    (choices xs).any (fun a => possible k (xs ++ [a]) t)

def target (r : Fin 16) : Mask :=
  ([0, 41120, 43520, 43680, 49344, 57568, 60096, 60128,
    52224, 60576, 60928, 61088, 52416, 60640, 61120, 61152] : List Mask).getD r.val 0

def bound (r : Fin 16) : ℕ :=
  [0, 1, 1, 2, 1, 2, 3, 4, 1, 3, 2, 4, 2, 4, 4, 3].getD r.val 0

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

lemma mem_choices_zero (xs : List Mask) : (0 : Mask) ∈ choices xs := by
  simp [choices]

lemma mem_choices_top (xs : List Mask) : BitVec.allOnes 16 ∈ choices xs := by
  have ht : BitVec.allOnes 16 = (65535 : Mask) := rfl
  simp [choices, ht]

lemma mem_choices_of_mem (xs : List Mask) (a : Mask) (ha : a ∈ xs) : a ∈ choices xs := by
  simp [choices, ha]

lemma mem_choices_and (xs : List Mask) (a b : Mask) (ha : a ∈ xs) (hb : b ∈ xs) :
    a &&& b ∈ choices xs := by
  simp only [choices, List.mem_eraseDups, List.mem_cons, List.mem_append, List.mem_flatMap,
    List.not_mem_nil, or_false]
  exact Or.inr ⟨a, ha, b, hb, Or.inl rfl⟩

lemma mem_choices_or (xs : List Mask) (a b : Mask) (ha : a ∈ xs) (hb : b ∈ xs) :
    a ||| b ∈ choices xs := by
  simp only [choices, List.mem_eraseDups, List.mem_cons, List.mem_append, List.mem_flatMap,
    List.not_mem_nil, or_false]
  exact Or.inr ⟨a, ha, b, hb, Or.inr rfl⟩

lemma possible_now (k : ℕ) (xs : List Mask) (t : Mask) (h : t = 0 ∨ t ∈ xs) :
    possible k xs t = true := by
  cases k <;> simp_all [possible]

lemma possible_step (k : ℕ) (xs : List Mask) (a t : Mask)
    (ha : a ∈ choices xs) (h : possible k (xs ++ [a]) t = true) :
    possible (k + 1) xs t = true := by
  simp only [possible, Bool.or_eq_true, List.any_eq_true]
  exact Or.inr ⟨a, ha, h⟩

lemma possible_mono (k l : ℕ) (hkl : k ≤ l) (xs : List Mask) (t : Mask)
    (h : possible k xs t = true) : possible l xs t = true := by
  induction k generalizing l xs with
  | zero =>
    apply possible_now
    simpa [possible] using h
  | succ k ih =>
    cases l with
    | zero => omega
    | succ l =>
      simp only [possible, Bool.or_eq_true, List.any_eq_true] at h ⊢
      rcases h with h | ⟨a, ha, ht⟩
      · exact Or.inl h
      · exact Or.inr ⟨a, ha, ih l (by omega) _ ht⟩

def opTable (op : GateOp) (xs : List Mask) : Mask :=
  match op with
  | .and => xs.foldr (· &&& ·) (BitVec.allOnes 16)
  | .or => xs.foldr (· ||| ·) 0
  | _ => 0

def gateTable (g : Gate) (xs : List Mask) : Mask :=
  opTable g.op (g.inputs.map (fun i => xs.getD i 0))

def runTable (gs : List Gate) (xs : List Mask) : List Mask :=
  gs.foldl (fun w g => w ++ [gateTable g w]) xs

lemma lookup_mem (xs : List Mask) (i : ℕ) (hi : i < xs.length) : xs.getD i 0 ∈ xs := by
  rw [List.getD_eq_getElem xs 0 hi]
  exact List.getElem_mem hi

lemma or_bottom (a : Mask) : a ||| (0 : Mask) = a := BitVec.or_zero

lemma gateTable_mem (g : Gate) (xs : List Mask)
    (hop : g.op = .and ∨ g.op = .or) (hlen : g.inputs.length ≤ 2)
    (hback : ∀ i ∈ g.inputs, i < xs.length) : gateTable g xs ∈ choices xs := by
  rcases g with ⟨op, ins⟩
  simp only at hop hlen hback
  cases ins with
  | nil =>
    rcases hop with rfl | rfl
    · exact mem_choices_top xs
    · exact mem_choices_zero xs
  | cons a rest =>
    have ha := lookup_mem xs a (hback a (by simp))
    cases rest with
    | nil =>
      rcases hop with rfl | rfl <;>
        simpa only [gateTable, opTable, List.map_cons, List.map_nil, List.foldr_cons,
          List.foldr_nil, BitVec.and_allOnes, or_bottom] using mem_choices_of_mem xs _ ha
    | cons b rest =>
      have hb := lookup_mem xs b (hback b (by simp))
      have hr : rest = [] := by simpa using hlen
      subst rest
      rcases hop with rfl | rfl
      · simpa only [gateTable, opTable, List.map_cons, List.map_nil, List.foldr_cons,
          List.foldr_nil, BitVec.and_allOnes, or_bottom] using mem_choices_and xs _ _ ha hb
      · simpa only [gateTable, opTable, List.map_cons, List.map_nil, List.foldr_cons,
          List.foldr_nil, BitVec.and_allOnes, or_bottom] using mem_choices_or xs _ _ ha hb

lemma runTable_possible (gs : List Gate) (xs : List Mask)
    (hop : ∀ g ∈ gs, g.op = .and ∨ g.op = .or)
    (hlen : ∀ g ∈ gs, g.inputs.length ≤ 2)
    (hback : ∀ j < gs.length, ∀ i ∈ (gs.getD j ⟨.or, []⟩).inputs, i < xs.length + j)
    (out : ℕ) : possible gs.length xs ((runTable gs xs).getD out 0) = true := by
  induction gs generalizing xs with
  | nil =>
    apply possible_now
    by_cases ho : out < xs.length
    · exact Or.inr (lookup_mem xs out ho)
    · exact Or.inl (List.getD_eq_default xs 0 (by omega))
  | cons g gs ih =>
    have hg := gateTable_mem g xs (hop g (by simp)) (hlen g (by simp)) (by
      simpa using hback 0 (by simp))
    apply possible_step gs.length xs (gateTable g xs) _ hg
    apply ih
    · intro g hg; exact hop g (by simp [hg])
    · intro g hg; exact hlen g (by simp [hg])
    · intro j hj i hi
      have hb := hback (j + 1) (by simp; omega) i (by simpa using hi)
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hb

def outputTable (C : Circuit) : Mask := (runTable C.gates inputs).getD C.output 0

lemma output_possible (C : Circuit) (hm : Monotone2 C) (hb : NestedCover.ReadsBack 4 C) :
    possible C.size inputs (outputTable C) = true := by
  apply runTable_possible C.gates inputs
  · intro g hg; simpa using (hm g hg).1
  · intro g hg; exact (hm g hg).2
  · exact hb

lemma getD_bits (xs : List Mask) (a : Fin 16) (i : ℕ) :
    (xs.map (fun v => v.getLsbD a.val)).getD i false = (xs.getD i 0).getLsbD a.val := by
  simpa using List.getD_map xs (0 : Mask) (fun v => v.getLsbD a.val) (n := i)

lemma and_bits (xs : List Mask) (a : Fin 16) :
    (xs.foldr (· &&& ·) (BitVec.allOnes 16)).getLsbD a.val =
      (xs.map (fun v => v.getLsbD a.val)).all id := by
  induction xs with
  | nil => simp only [List.foldr_nil, BitVec.getLsbD_allOnes, a.isLt, decide_true,
      List.map_nil, List.all_nil]
  | cons x xs ih =>
    simp only [List.foldr_cons, BitVec.getLsbD_and, ih, List.map_cons, List.all_cons, id_eq]

lemma or_bits (xs : List Mask) (a : Fin 16) :
    (xs.foldr (· ||| ·) 0).getLsbD a.val =
      (xs.map (fun v => v.getLsbD a.val)).any id := by
  induction xs with
  | nil => exact BitVec.getLsbD_zero
  | cons x xs ih =>
    simp only [List.foldr_cons, BitVec.getLsbD_or, ih, List.map_cons, List.any_cons, id_eq]

lemma gate_bits (g : Gate) (xs : List Mask) (a : Fin 16)
    (hop : g.op = .and ∨ g.op = .or) :
    (gateTable g xs).getLsbD a.val =
      g.op.eval (g.inputs.map (fun i => (xs.map (fun v => v.getLsbD a.val)).getD i false)) := by
  rcases g with ⟨op, ins⟩
  rcases hop with rfl | rfl
  · simp only [gateTable, opTable, and_bits, List.map_map, getD_bits, GateOp.eval,
      Function.comp_def]
  · simp only [gateTable, opTable, or_bits, List.map_map, getD_bits, GateOp.eval,
      Function.comp_def]

def runBool (gs : List Gate) (xs : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map (fun i => w.getD i false))]) xs

lemma run_bits (gs : List Gate) (xs : List Mask) (a : Fin 16)
    (hop : ∀ g ∈ gs, g.op = .and ∨ g.op = .or) :
    (runTable gs xs).map (fun v => v.getLsbD a.val) =
      runBool gs (xs.map (fun v => v.getLsbD a.val)) := by
  induction gs generalizing xs with
  | nil => rfl
  | cons g gs ih =>
    change (runTable gs (xs ++ [gateTable g xs])).map (fun v => v.getLsbD a.val) = _
    rw [ih _ (fun g hg => hop g (by simp [hg]))]
    simp only [List.map_append, List.map_singleton, gate_bits g xs a (hop g (by simp))]
    rfl

def assignment (a : Fin 16) (i : Fin 4) : Bool :=
  (inputs.getD i.val 0).getLsbD a.val

lemma input_bits (a : Fin 16) : inputs.map (fun v => v.getLsbD a.val) =
    List.ofFn (assignment a) := by
  simp [inputs, assignment, List.ofFn_succ]

lemma output_bits (C : Circuit) (hm : Monotone2 C) (a : Fin 16) :
    (outputTable C).getLsbD a.val = circuitFun 4 C (assignment a) := by
  have hr := run_bits C.gates inputs a (fun g hg => by simpa using (hm g hg).1)
  rw [input_bits] at hr
  have hg := congrArg (fun xs : List Bool => xs.getD C.output false) hr
  rw [getD_bits] at hg
  exact hg

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma target_bits : ∀ r a : Fin 16,
    (target r).getLsbD a.val =
      ((r.val.testBit 0 && assignment a 0 && assignment a 2) ||
       (r.val.testBit 1 && assignment a 0 && assignment a 3) ||
       (r.val.testBit 2 && assignment a 1 && assignment a 2) ||
       (r.val.testBit 3 && assignment a 1 && assignment a 3)) := by
  decide +kernel

set_option maxHeartbeats 2000000 in
lemma lower_bound_with_certificate
    (cert : ∀ r : Fin 16, 0 < bound r → possible (bound r - 1) inputs (target r) = false)
    (r : Fin 16) (C : Circuit) (hm : Monotone2 C) (hb : NestedCover.ReadsBack 4 C)
    (hs : ∀ a : Fin 16, circuitFun 4 C (assignment a) = (target r).getLsbD a.val) :
    bound r ≤ C.size := by
  by_contra hbound
  have hp : 0 < bound r := by omega
  have ho : outputTable C = target r := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    exact (output_bits C hm ⟨i, hi⟩).trans (hs ⟨i, hi⟩)
  have hpossible : possible C.size inputs (target r) = true := ho ▸ output_possible C hm hb
  have hsmall := possible_mono C.size (bound r - 1) (by omega) inputs (target r) hpossible
  exact Bool.false_ne_true ((cert r hp).symm.trans hsmall)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma certificate : ∀ r : Fin 16, 0 < bound r →
    possible (bound r - 1) inputs (target r) = false := by
  decide +kernel

lemma lower_bound (r : Fin 16) (C : Circuit)
    (hm : Monotone2 C) (hb : NestedCover.ReadsBack 4 C)
    (hs : ∀ a : Fin 16, circuitFun 4 C (assignment a) = (target r).getLsbD a.val) :
    bound r ≤ C.size :=
  lower_bound_with_certificate certificate r C hm hb hs

end Four

namespace Two

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def witness : Bool → Bool → Bool → Bool → Circuit
  | false, false, false, false => ⟨[], 4⟩
  | true, false, false, false => ⟨[⟨.and, [0, 2]⟩], 4⟩
  | false, true, false, false => ⟨[⟨.and, [0, 3]⟩], 4⟩
  | true, true, false, false => ⟨[⟨.or, [2, 3]⟩, ⟨.and, [0, 4]⟩], 5⟩
  | false, false, true, false => ⟨[⟨.and, [1, 2]⟩], 4⟩
  | true, false, true, false => ⟨[⟨.or, [0, 1]⟩, ⟨.and, [4, 2]⟩], 5⟩
  | false, true, true, false =>
      ⟨[⟨.and, [0, 3]⟩, ⟨.and, [1, 2]⟩, ⟨.or, [4, 5]⟩], 6⟩
  | true, true, true, false =>
      ⟨[⟨.or, [2, 3]⟩, ⟨.and, [0, 4]⟩, ⟨.and, [1, 2]⟩, ⟨.or, [5, 6]⟩], 7⟩
  | false, false, false, true => ⟨[⟨.and, [1, 3]⟩], 4⟩
  | true, false, false, true =>
      ⟨[⟨.and, [0, 2]⟩, ⟨.and, [1, 3]⟩, ⟨.or, [4, 5]⟩], 6⟩
  | false, true, false, true => ⟨[⟨.or, [0, 1]⟩, ⟨.and, [4, 3]⟩], 5⟩
  | true, true, false, true =>
      ⟨[⟨.or, [2, 3]⟩, ⟨.and, [0, 4]⟩, ⟨.and, [1, 3]⟩, ⟨.or, [5, 6]⟩], 7⟩
  | false, false, true, true => ⟨[⟨.or, [2, 3]⟩, ⟨.and, [1, 4]⟩], 5⟩
  | true, false, true, true =>
      ⟨[⟨.or, [2, 3]⟩, ⟨.and, [1, 4]⟩, ⟨.and, [0, 2]⟩, ⟨.or, [5, 6]⟩], 7⟩
  | false, true, true, true =>
      ⟨[⟨.or, [2, 3]⟩, ⟨.and, [1, 4]⟩, ⟨.and, [0, 3]⟩, ⟨.or, [5, 6]⟩], 7⟩
  | true, true, true, true =>
      ⟨[⟨.or, [0, 1]⟩, ⟨.or, [2, 3]⟩, ⟨.and, [4, 5]⟩], 6⟩

def relation (a b c d : Bool) (p l : Fin 2) : Prop :=
  (if p = 0 then if l = 0 then a else b else if l = 0 then c else d) = true

def truth (a b c d : Bool) (z : Fin 4 → Bool) : Bool :=
  (a && z 0 && z 2) || (b && z 0 && z 3) ||
    (c && z 1 && z 2) || (d && z 1 && z 3)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
lemma witness_props : ∀ a b c d : Bool,
    Monotone2 (witness a b c d) ∧ NestedCover.ReadsBack 4 (witness a b c d) ∧
    (∀ z : Fin 4 → Bool, circuitFun 4 (witness a b c d) z = truth a b c d z) ∧
    (∀ j < (witness a b c d).gates.length,
      (NestedCover.gateAt (witness a b c d) j).op = GateOp.and →
      ∀ p l : Fin 2, ¬ relation a b c d p l →
        ((witness a b c d).wires (List.ofFn (fun k : Fin 4 =>
          decide (k = Fin.castAdd 2 p ∨ k = Fin.natAdd 2 l)))).getD (4 + j) false = false) ∧
    (∀ j < (witness a b c d).gates.length,
      (NestedCover.gateAt (witness a b c d) j).op = GateOp.and →
      (∀ p : Fin 2, ((witness a b c d).wires (List.ofFn (fun k : Fin 4 =>
        decide (k = Fin.castAdd 2 p)))).getD (4 + j) false = false) ∧
      ∀ l : Fin 2, ((witness a b c d).wires (List.ofFn (fun k : Fin 4 =>
        decide (k = Fin.natAdd 2 l)))).getD (4 + j) false = false) := by
  let _ : DecidableEq GateOp := NestedCover.gateOpDecEq
  unfold Monotone2 NestedCover.ReadsBack relation
  decide

lemma relation_truth (a b c d : Bool) (z : Fin 4 → Bool) :
    truth a b c d z = true ↔
      ∃ p l : Fin 2, relation a b c d p l ∧
        z (Fin.castAdd 2 p) = true ∧ z (Fin.natAdd 2 l) = true := by
  simp only [Fin.exists_fin_succ, Fin.exists_fin_zero, or_false, relation, truth]
  simp
  tauto

lemma relation_encode (I : Fin 2 → Fin 2 → Prop) [DecidableRel I] :
    ∀ p l : Fin 2, relation (decide (I 0 0)) (decide (I 0 1))
      (decide (I 1 0)) (decide (I 1 1)) p l ↔ I p l := by
  intro p l
  fin_cases p <;> fin_cases l <;> simp [relation]

def code (a b c d : Bool) : Fin 16 :=
  Fin.ofNat 16 (a.toNat + 2 * b.toNat + 4 * c.toNat + 8 * d.toNat)

lemma code_bits : ∀ a b c d : Bool,
    (code a b c d).val.testBit 0 = a ∧ (code a b c d).val.testBit 1 = b ∧
    (code a b c d).val.testBit 2 = c ∧ (code a b c d).val.testBit 3 = d := by
  decide

lemma witness_size : ∀ a b c d : Bool, (witness a b c d).size =
    ([0, 1, 1, 2, 1, 2, 3, 4, 1, 3, 2, 4, 2, 4, 4, 3] : List ℕ).getD
      (code a b c d).val 0 := by
  decide

lemma witness_size_le_four : ∀ a b c d : Bool, (witness a b c d).size ≤ 4 := by
  decide

lemma circuit_truth (I : Fin 2 → Fin 2 → Prop) [DecidableRel I] (C : Circuit)
    (sem : ∀ z : Fin 4 → Bool, circuitFun 4 C z = true ↔
      ∃ p l : Fin 2, I p l ∧ z (Fin.castAdd 2 p) = true ∧ z (Fin.natAdd 2 l) = true) :
    ∀ z : Fin 4 → Bool, circuitFun 4 C z =
      truth (decide (I 0 0)) (decide (I 0 1)) (decide (I 1 0)) (decide (I 1 1)) z := by
  intro z
  apply Bool.eq_iff_iff.mpr
  rw [sem, relation_truth]
  constructor
  · rintro ⟨p, l, hi, hp, hl⟩
    exact ⟨p, l, (relation_encode I p l).mpr hi, hp, hl⟩
  · rintro ⟨p, l, hi, hp, hl⟩
    exact ⟨p, l, (relation_encode I p l).mp hi, hp, hl⟩

lemma from_size (I : Fin 2 → Fin 2 → Prop) [DecidableRel I] (C : Circuit)
    (hsize : (witness (decide (I 0 0)) (decide (I 0 1))
      (decide (I 1 0)) (decide (I 1 1))).size ≤ C.size) :
    ∃ D : Circuit, Monotone2 D ∧ NestedCover.ReadsBack 4 D ∧ D.size ≤ C.size ∧
      (∀ z : Fin 4 → Bool, circuitFun 4 D z = true ↔
        ∃ p l : Fin 2, I p l ∧ z (Fin.castAdd 2 p) = true ∧ z (Fin.natAdd 2 l) = true) ∧
      (∀ j < D.gates.length, (NestedCover.gateAt D j).op = GateOp.and →
        ∀ p l : Fin 2, ¬ I p l →
          (D.wires (List.ofFn (fun k : Fin 4 =>
            decide (k = Fin.castAdd 2 p ∨ k = Fin.natAdd 2 l)))).getD (4 + j) false = false) ∧
      (∀ j < D.gates.length, (NestedCover.gateAt D j).op = GateOp.and →
        (∀ p : Fin 2, (D.wires (List.ofFn (fun k : Fin 4 =>
          decide (k = Fin.castAdd 2 p)))).getD (4 + j) false = false) ∧
        ∀ l : Fin 2, (D.wires (List.ofFn (fun k : Fin 4 =>
          decide (k = Fin.natAdd 2 l)))).getD (4 + j) false = false) := by
  let a := decide (I 0 0)
  let b := decide (I 0 1)
  let c := decide (I 1 0)
  let d := decide (I 1 1)
  obtain ⟨hm, hb, he, hp, hz⟩ := witness_props a b c d
  have rel : ∀ p l, relation a b c d p l ↔ I p l := relation_encode I
  refine ⟨witness a b c d, hm, hb, hsize, ?_, ?_, hz⟩
  · intro z
    rw [he, relation_truth]
    constructor
    · rintro ⟨p, l, hi, hzp, hzl⟩
      exact ⟨p, l, (rel p l).mp hi, hzp, hzl⟩
    · rintro ⟨p, l, hi, hzp, hzl⟩
      exact ⟨p, l, (rel p l).mpr hi, hzp, hzl⟩
  · intro j hj hand p l hn
    exact hp j hj hand p l (fun hi => hn ((rel p l).mp hi))

lemma large_enough (I : Fin 2 → Fin 2 → Prop) [DecidableRel I] (C : Circuit)
    (hsize : 4 ≤ C.size) :
    ∃ D : Circuit, Monotone2 D ∧ NestedCover.ReadsBack 4 D ∧ D.size ≤ C.size ∧
      (∀ z : Fin 4 → Bool, circuitFun 4 D z = true ↔
        ∃ p l : Fin 2, I p l ∧ z (Fin.castAdd 2 p) = true ∧ z (Fin.natAdd 2 l) = true) ∧
      (∀ j < D.gates.length, (NestedCover.gateAt D j).op = GateOp.and →
        ∀ p l : Fin 2, ¬ I p l →
          (D.wires (List.ofFn (fun k : Fin 4 =>
            decide (k = Fin.castAdd 2 p ∨ k = Fin.natAdd 2 l)))).getD (4 + j) false = false) ∧
      (∀ j < D.gates.length, (NestedCover.gateAt D j).op = GateOp.and →
        (∀ p : Fin 2, (D.wires (List.ofFn (fun k : Fin 4 =>
          decide (k = Fin.castAdd 2 p)))).getD (4 + j) false = false) ∧
        ∀ l : Fin 2, (D.wires (List.ofFn (fun k : Fin 4 =>
          decide (k = Fin.natAdd 2 l)))).getD (4 + j) false = false) :=
  from_size I C ((witness_size_le_four _ _ _ _).trans hsize)

end Two

namespace Two

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

lemma normalize_with_certificate
    (cert : ∀ r : Fin 16, 0 < Four.bound r →
      Four.possible (Four.bound r - 1) Four.inputs (Four.target r) = false)
    (I : Fin 2 → Fin 2 → Prop) [DecidableRel I] (C : Circuit)
    (hm : Monotone2 C) (hb : NestedCover.ReadsBack 4 C)
    (sem : ∀ z : Fin 4 → Bool, circuitFun 4 C z = true ↔
      ∃ p l : Fin 2, I p l ∧ z (Fin.castAdd 2 p) = true ∧ z (Fin.natAdd 2 l) = true) :
    ∃ D : Circuit, Monotone2 D ∧ NestedCover.ReadsBack 4 D ∧ D.size ≤ C.size ∧
      (∀ z : Fin 4 → Bool, circuitFun 4 D z = true ↔
        ∃ p l : Fin 2, I p l ∧ z (Fin.castAdd 2 p) = true ∧ z (Fin.natAdd 2 l) = true) ∧
      (∀ j < D.gates.length, (NestedCover.gateAt D j).op = GateOp.and →
        ∀ p l : Fin 2, ¬ I p l →
          (D.wires (List.ofFn (fun k : Fin 4 =>
            decide (k = Fin.castAdd 2 p ∨ k = Fin.natAdd 2 l)))).getD (4 + j) false = false) ∧
      (∀ j < D.gates.length, (NestedCover.gateAt D j).op = GateOp.and →
        (∀ p : Fin 2, (D.wires (List.ofFn (fun k : Fin 4 =>
          decide (k = Fin.castAdd 2 p)))).getD (4 + j) false = false) ∧
        ∀ l : Fin 2, (D.wires (List.ofFn (fun k : Fin 4 =>
          decide (k = Fin.natAdd 2 l)))).getD (4 + j) false = false) := by
  apply from_size I C
  rw [witness_size]
  apply Four.lower_bound_with_certificate cert _ C hm hb
  intro x
  rw [circuit_truth I C sem, Four.target_bits]
  obtain ⟨ha, hb, hc, hd⟩ := code_bits (decide (I 0 0)) (decide (I 0 1))
    (decide (I 1 0)) (decide (I 1 1))
  simp only [ha, hb, hc, hd, truth]

lemma normalize
    (I : Fin 2 → Fin 2 → Prop) [DecidableRel I] (C : Circuit)
    (hm : Monotone2 C) (hb : NestedCover.ReadsBack 4 C)
    (sem : ∀ z : Fin 4 → Bool, circuitFun 4 C z = true ↔
      ∃ p l : Fin 2, I p l ∧ z (Fin.castAdd 2 p) = true ∧ z (Fin.natAdd 2 l) = true) :
    ∃ D : Circuit, Monotone2 D ∧ NestedCover.ReadsBack 4 D ∧ D.size ≤ C.size ∧
      (∀ z : Fin 4 → Bool, circuitFun 4 D z = true ↔
        ∃ p l : Fin 2, I p l ∧ z (Fin.castAdd 2 p) = true ∧ z (Fin.natAdd 2 l) = true) ∧
      (∀ j < D.gates.length, (NestedCover.gateAt D j).op = GateOp.and →
        ∀ p l : Fin 2, ¬ I p l →
          (D.wires (List.ofFn (fun k : Fin 4 =>
            decide (k = Fin.castAdd 2 p ∨ k = Fin.natAdd 2 l)))).getD (4 + j) false = false) ∧
      (∀ j < D.gates.length, (NestedCover.gateAt D j).op = GateOp.and →
        (∀ p : Fin 2, (D.wires (List.ofFn (fun k : Fin 4 =>
          decide (k = Fin.castAdd 2 p)))).getD (4 + j) false = false) ∧
        ∀ l : Fin 2, (D.wires (List.ofFn (fun k : Fin 4 =>
          decide (k = Fin.natAdd 2 l)))).getD (4 + j) false = false) :=
  normalize_with_certificate Four.certificate I C hm hb sem

end Two

end PEqualNP.Outside.L_meta_3451_aux
