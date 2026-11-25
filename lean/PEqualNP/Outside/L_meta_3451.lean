import Mathlib.Tactic
import PEqualNP.Defs

/- Checked partial results for L-meta-3451. The unrestricted posted theorem remains unproved. -/

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

def contextOld (n : ℕ) (gs : List Gate) (a b c d : ℕ) (ts : List Gate) (out : ℕ) : Circuit :=
  ⟨(oldCircuit n gs a b c d).gates ++ ts, out⟩

def contextNew (n : ℕ) (gs : List Gate) (a b c d : ℕ) (ts : List Gate) (out : ℕ) : Circuit :=
  ⟨(newCircuit n gs a b c d).gates ++ ts, out⟩

lemma gate_imp (g : Gate) (hop : g.op = GateOp.and ∨ g.op = GateOp.or)
    (f f' : ℕ → Bool) (h : ∀ i ∈ g.inputs, f i = true → f' i = true) :
    g.op.eval (g.inputs.map f) = true → g.op.eval (g.inputs.map f') = true := by
  rcases hop with hop | hop
  · rw [hop]
    simp only [GateOp.eval, List.all_eq_true, List.mem_map, id]
    intro H x hx
    obtain ⟨i, hi, rfl⟩ := hx
    exact h i hi (H (f i) ⟨i, hi, rfl⟩)
  · rw [hop]
    simp only [GateOp.eval, List.any_eq_true, List.mem_map, id]
    rintro ⟨x, ⟨i, hi, rfl⟩, hx⟩
    exact ⟨f' i, ⟨i, hi, rfl⟩, h i hi hx⟩

lemma fold_rel_except (R : Bool → Bool → Prop) (hfalse : R false false)
    (k : ℕ) (ts : List Gate)
    (hread : ∀ g ∈ ts, ∀ i ∈ g.inputs, i ≠ k ∧ i ≠ k + 1)
    (hlift : ∀ g ∈ ts, ∀ f f' : ℕ → Bool, (∀ i ∈ g.inputs, R (f i) (f' i)) →
      R (g.op.eval (g.inputs.map f)) (g.op.eval (g.inputs.map f'))) :
    ∀ w w' : List Bool, w.length = w'.length →
      (∀ i, i ≠ k → i ≠ k + 1 → R (w.getD i false) (w'.getD i false)) →
      ∀ i, i ≠ k → i ≠ k + 1 →
        R ((ts.foldl step w).getD i false) ((ts.foldl step w').getD i false) := by
  induction ts with
  | nil => intro w w' _ h i hi hi'; exact h i hi hi'
  | cons g ts ih =>
    intro w w' hlen h i hi hi'
    rw [List.foldl_cons, List.foldl_cons]
    apply ih (fun g' hg' => hread g' (List.mem_cons_of_mem _ hg'))
      (fun g' hg' => hlift g' (List.mem_cons_of_mem _ hg')) (step w g) (step w' g)
      (by simp [step, hlen]) _ i hi hi'
    intro j hj hj'
    unfold step
    by_cases hlt : j < w.length
    · rw [List.getD_append _ _ _ _ hlt, List.getD_append _ _ _ _ (by omega)]
      exact h j hj hj'
    · rw [List.getD_append_right _ _ _ _ (by omega),
        List.getD_append_right _ _ _ _ (by omega), ← hlen]
      by_cases he : j - w.length = 0
      · rw [he]
        simp only [List.getD_cons_zero]
        apply hlift g List.mem_cons_self
        intro r hr
        exact h r (hread g List.mem_cons_self r hr).1 (hread g List.mem_cons_self r hr).2
      · obtain ⟨m, hm⟩ : ∃ m, j - w.length = m + 1 := ⟨j - w.length - 1, by omega⟩
        rw [hm]
        simpa using hfalse

lemma triple_rel_except (R : Bool → Bool → Prop) (hrefl : ∀ v, R v v)
    (w : List Bool) (A B H A' B' H' : Bool) (hH : R H H') :
    ∀ i, i ≠ w.length → i ≠ w.length + 1 →
      R ((w ++ [A, B, H]).getD i false) ((w ++ [A', B', H']).getD i false) := by
  intro i hi hi'
  by_cases hlt : i < w.length
  · rw [List.getD_append _ _ _ _ hlt, List.getD_append _ _ _ _ hlt]
    exact hrefl _
  · rw [List.getD_append_right _ _ _ _ (by omega), List.getD_append_right _ _ _ _ (by omega)]
    have hidx : i - w.length = 2 ∨ 3 ≤ i - w.length := by omega
    rcases hidx with he | he
    · rw [he]
      simpa only [List.getD_cons_succ, List.getD_cons_zero] using hH
    · rw [List.getD_eq_default _ _ (by simp; omega),
        List.getD_eq_default _ _ (by simp; omega)]
      exact hrefl false

lemma wires_old (n : ℕ) (gs : List Gate) (a b c d : ℕ)
    (hc : c < n + gs.length) (hd : d < n + gs.length) (x : Fin n → Bool) :
    let w := (⟨gs, 0⟩ : Circuit).wires (List.ofFn x)
    (oldCircuit n gs a b c d).wires (List.ofFn x) =
      w ++ [w.getD a false && w.getD b false, w.getD c false || w.getD d false,
        (w.getD a false && w.getD b false) && (w.getD c false || w.getD d false)] := by
  let w := gs.foldl step (List.ofFn x)
  have hw : w.length = n + gs.length := by simp [w, fold_length]
  have h := run_three_wires w a b c d (by omega) (by omega)
    GateOp.and GateOp.or GateOp.and
  rw [hw] at h
  change (gs ++ ([⟨.and, [a, b]⟩, ⟨.or, [c, d]⟩,
    ⟨.and, [n + gs.length, n + gs.length + 1]⟩] : List Gate)).foldl step (List.ofFn x) =
    w ++ [w.getD a false && w.getD b false, w.getD c false || w.getD d false,
      (w.getD a false && w.getD b false) && (w.getD c false || w.getD d false)]
  rw [List.foldl_append]
  simpa only [GateOp.eval, List.all_cons, List.all_nil, List.any_cons, List.any_nil,
    id_eq, Bool.and_true, Bool.or_false] using h

lemma context_rel (n : ℕ) (gs : List Gate) (a b c d : ℕ)
    (ha : a < n + gs.length) (hc : c < n + gs.length) (hd : d < n + gs.length)
    (ts : List Gate) (out : ℕ)
    (hread : ∀ g ∈ ts, ∀ i ∈ g.inputs, i ≠ n + gs.length ∧ i ≠ n + gs.length + 1)
    (hout : out ≠ n + gs.length ∧ out ≠ n + gs.length + 1)
    (R : Bool → Bool → Prop) (hrefl : ∀ v, R v v)
    (hlift : ∀ g ∈ ts, ∀ f f' : ℕ → Bool, (∀ i ∈ g.inputs, R (f i) (f' i)) →
      R (g.op.eval (g.inputs.map f)) (g.op.eval (g.inputs.map f')))
    (x : Fin n → Bool)
    (hlocal : let w := (⟨gs, 0⟩ : Circuit).wires (List.ofFn x)
      R ((w.getD a false && w.getD b false) && (w.getD c false || w.getD d false))
        ((w.getD c false && w.getD b false) || (w.getD d false && w.getD a false))) :
    R (circuitFun n (contextOld n gs a b c d ts out) x)
      (circuitFun n (contextNew n gs a b c d ts out) x) := by
  change R (((oldCircuit n gs a b c d).gates ++ ts).foldl step (List.ofFn x) |>.getD out false)
    (((newCircuit n gs a b c d).gates ++ ts).foldl step (List.ofFn x) |>.getD out false)
  rw [List.foldl_append, List.foldl_append]
  change R ((ts.foldl step ((oldCircuit n gs a b c d).wires (List.ofFn x))).getD out false)
    ((ts.foldl step ((newCircuit n gs a b c d).wires (List.ofFn x))).getD out false)
  rw [wires_old n gs a b c d hc hd x, wires_new n gs a b c d ha hd x]
  apply fold_rel_except R (hrefl false) (n + gs.length) ts hread hlift _ _ (by simp) _ out hout.1 hout.2
  have hw : ((⟨gs, 0⟩ : Circuit).wires (List.ofFn x)).length = n + gs.length := by
    exact (fold_length gs (List.ofFn x)).trans (by simp)
  simpa only [hw] using triple_rel_except R hrefl ((⟨gs, 0⟩ : Circuit).wires (List.ofFn x))
    _ _ _ _ _ _ hlocal

lemma bool_split_increases : ∀ a b c d : Bool,
    ((a && b) && (c || d)) = true → ((c && b) || (d && a)) = true := by
  decide

lemma contextual_same_function (n : ℕ) (gs : List Gate) (a b c d : ℕ)
    (ha : a < n + gs.length) (hc : c < n + gs.length) (hd : d < n + gs.length)
    (ts : List Gate) (out : ℕ)
    (hmono : ∀ g ∈ ts, g.op = GateOp.and ∨ g.op = GateOp.or)
    (hread : ∀ g ∈ ts, ∀ i ∈ g.inputs, i ≠ n + gs.length ∧ i ≠ n + gs.length + 1)
    (hout : out ≠ n + gs.length ∧ out ≠ n + gs.length + 1)
    (hca : ∀ x : Fin n → Bool, circuitFun n (contextOld n gs a b c d ts out) x = false →
      ((⟨gs, 0⟩ : Circuit).wires (List.ofFn x)).getD c false = true →
      ((⟨gs, 0⟩ : Circuit).wires (List.ofFn x)).getD a false = true)
    (hdb : ∀ x : Fin n → Bool, circuitFun n (contextOld n gs a b c d ts out) x = false →
      ((⟨gs, 0⟩ : Circuit).wires (List.ofFn x)).getD d false = true →
      ((⟨gs, 0⟩ : Circuit).wires (List.ofFn x)).getD b false = true) :
    circuitFun n (contextNew n gs a b c d ts out) =
      circuitFun n (contextOld n gs a b c d ts out) := by
  funext x
  cases hx : circuitFun n (contextOld n gs a b c d ts out) x with
  | false =>
    have h := context_rel n gs a b c d ha hc hd ts out hread hout Eq (fun _ => rfl)
      (fun g _ f f' h => congrArg g.op.eval (List.map_congr_left h)) x
      (bool_split _ _ _ _ (hca x hx) (hdb x hx))
    simpa only [hx] using h.symm
  | true =>
    have h := context_rel n gs a b c d ha hc hd ts out hread hout
      (fun u v => u = true → v = true) (fun _ h => h)
      (fun g hg f f' h => gate_imp g (hmono g hg) f f' h) x
      (bool_split_increases _ _ _ _)
    exact h hx

lemma context_equal_size (n : ℕ) (gs : List Gate) (a b c d : ℕ) (ts : List Gate) (out : ℕ) :
    (contextNew n gs a b c d ts out).size = (contextOld n gs a b c d ts out).size := by
  simp [contextNew, contextOld, newCircuit, oldCircuit, Circuit.size]

lemma context_monotone_models (n : ℕ) (gs : List Gate) (a b c d : ℕ) (ts : List Gate) (out : ℕ)
    (hp : Monotone2 (⟨gs, 0⟩ : Circuit)) (ht : Monotone2 (⟨ts, 0⟩ : Circuit)) :
    Monotone2 (contextOld n gs a b c d ts out) ∧
      Monotone2 (contextNew n gs a b c d ts out) := by
  constructor
  · intro g hg
    rcases List.mem_append.mp hg with hg | hg
    · exact (monotone_models n gs a b c d hp).1 g hg
    · exact ht g hg
  · intro g hg
    rcases List.mem_append.mp hg with hg | hg
    · exact (monotone_models n gs a b c d hp).2 g hg
    · exact ht g hg

lemma context_back (n : ℕ) (gs : List Gate) (a b c d : ℕ)
    (ha : a < n + gs.length) (hb : b < n + gs.length)
    (hc : c < n + gs.length) (hd : d < n + gs.length)
    (ts : List Gate) (out : ℕ)
    (hp : ReadsBack n (⟨gs, 0⟩ : Circuit))
    (ht : ReadsBack n (contextOld n gs a b c d ts out)) :
    ReadsBack n (contextNew n gs a b c d ts out) := by
  intro j hj i hi
  by_cases hlt : j < (newCircuit n gs a b c d).gates.length
  · have he : gateAt (contextNew n gs a b c d ts out) j = gateAt (newCircuit n gs a b c d) j :=
      List.getD_append _ _ _ _ hlt
    rw [he] at hi
    exact (back_models n gs a b c d ha hb hc hd hp).2 j hlt i hi
  · have he : gateAt (contextNew n gs a b c d ts out) j =
        gateAt (contextOld n gs a b c d ts out) j := by
      unfold gateAt contextNew contextOld
      rw [List.getD_append_right _ _ _ _ (by omega),
        List.getD_append_right _ _ _ _ (by simpa [newCircuit, oldCircuit] using Nat.le_of_not_gt hlt)]
      simp only [newCircuit, oldCircuit, List.length_append, List.length_cons, List.length_nil]
    rw [he] at hi
    apply ht j _ i hi
    simpa [contextNew, contextOld, newCircuit, oldCircuit] using hj

lemma bool_mass_nonincrease : ∀ a b c d : Bool,
    (c = true → a = true) → (d = true → b = true) →
    (c && b).toNat + (d && a).toNat ≤
      (a && b).toNat + ((a && b) && (c || d)).toNat := by
  decide

lemma bool_mass_strict : ∀ a b c d : Bool,
    (c = true → a = true) → (d = true → b = true) →
    (a && b) = true → ((a && b) && (c || d)) = false →
    (c && b).toNat + (d && a).toNat + 1 ≤
      (a && b).toNat + ((a && b) && (c || d)).toNat := by
  decide

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

namespace Support

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

noncomputable def pick {N : ℕ} (e : Fin 2 ↪ Fin N) (p : Fin N) : Option (Fin 2) :=
  if h : ∃ i, e i = p then some h.choose else none

lemma pick_embed {N : ℕ} (e : Fin 2 ↪ Fin N) (i : Fin 2) : pick e (e i) = some i := by
  unfold pick
  have h : ∃ j, e j = e i := ⟨i, rfl⟩
  rw [dite_eq_left h]
  exact congrArg some (e.injective h.choose_spec)

lemma pick_some {N : ℕ} (e : Fin 2 ↪ Fin N) (p : Fin N) (i : Fin 2)
    (h : pick e p = some i) : e i = p := by
  unfold pick at h
  split_ifs at h with hex
  have he := Option.some.inj h
  rw [← he]
  exact hex.choose_spec

def embed {N : ℕ} (ep el : Fin 2 ↪ Fin N) : Fin 4 → Fin (N + N) :=
  Fin.addCases (m := 2) (n := 2) (motive := fun _ => Fin (N + N))
    (fun p => Fin.castAdd N (ep p)) (fun l => Fin.natAdd N (el l))

noncomputable def project {N : ℕ} (ep el : Fin 2 ↪ Fin N) :
    Fin (N + N) → Option (Fin 4) :=
  Fin.addCases (fun p => (pick ep p).map (Fin.castAdd 2))
    (fun l => (pick el l).map (Fin.natAdd 2))

lemma project_embed {N : ℕ} (ep el : Fin 2 ↪ Fin N) (i : Fin 4) :
    project ep el (embed ep el i) = some i := by
  refine Fin.addCases (m := 2) (n := 2) (fun p => ?_) (fun l => ?_) i
  · rw [embed, Fin.addCases_left, project, Fin.addCases_left, pick_embed]
    rfl
  · rw [embed, Fin.addCases_right, project, Fin.addCases_right, pick_embed]
    rfl

lemma input_point {N : ℕ} (ep el : Fin 2 ↪ Fin N) (z : Fin 4 → Bool) (p : Fin 2) :
    Restriction.input (project ep el) z (Fin.castAdd N (ep p)) = z (Fin.castAdd 2 p) := by
  simp only [Restriction.input, project, Fin.addCases_left, pick_embed,
    Option.map_some, Option.getD_some]

lemma input_line {N : ℕ} (ep el : Fin 2 ↪ Fin N) (z : Fin 4 → Bool) (l : Fin 2) :
    Restriction.input (project ep el) z (Fin.natAdd N (el l)) = z (Fin.natAdd 2 l) := by
  simp only [Restriction.input, project, Fin.addCases_right, pick_embed,
    Option.map_some, Option.getD_some]

lemma rename_point {N : ℕ} (ep el : Fin 2 ↪ Fin N) (z : Fin (N + N) → Bool) (p : Fin 2) :
    Restriction.input (fun i => some (embed ep el i)) z (Fin.castAdd 2 p) =
      z (Fin.castAdd N (ep p)) := by
  simp only [Restriction.input, embed, Fin.addCases_left, Option.map_some, Option.getD_some]

lemma rename_line {N : ℕ} (ep el : Fin 2 ↪ Fin N) (z : Fin (N + N) → Bool) (l : Fin 2) :
    Restriction.input (fun i => some (embed ep el i)) z (Fin.natAdd 2 l) =
      z (Fin.natAdd N (el l)) := by
  simp only [Restriction.input, embed, Fin.addCases_right, Option.map_some, Option.getD_some]

lemma computes_project {N : ℕ} (ep el : Fin 2 ↪ Fin N) (I : Fin N → Fin N → Prop)
    (support : ∀ p l, I p l → ∃ a b : Fin 2, p = ep a ∧ l = el b)
    (C : Circuit) (hm : Monotone2 C)
    (sem : ∀ z : Fin (N + N) → Bool, circuitFun (N + N) C z = true ↔
      ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) :
    ∀ z : Fin 4 → Bool, circuitFun 4 (Restriction.circuit (project ep el) C) z = true ↔
      ∃ p l : Fin 2, I (ep p) (el l) ∧
        z (Fin.castAdd 2 p) = true ∧ z (Fin.natAdd 2 l) = true := by
  intro z
  rw [Restriction.eval _ C hm, sem]
  constructor
  · rintro ⟨p, l, hi, hp, hl⟩
    obtain ⟨a, b, rfl, rfl⟩ := support p l hi
    exact ⟨a, b, hi, by simpa only [input_point] using hp,
      by simpa only [input_line] using hl⟩
  · rintro ⟨p, l, hi, hp, hl⟩
    exact ⟨ep p, el l, hi, by simpa only [input_point] using hp,
      by simpa only [input_line] using hl⟩

lemma computes_rename {N : ℕ} (ep el : Fin 2 ↪ Fin N) (I : Fin N → Fin N → Prop)
    (support : ∀ p l, I p l → ∃ a b : Fin 2, p = ep a ∧ l = el b)
    (C : Circuit) (hm : Monotone2 C)
    (sem : ∀ z : Fin 4 → Bool, circuitFun 4 C z = true ↔
      ∃ p l : Fin 2, I (ep p) (el l) ∧ z (Fin.castAdd 2 p) = true ∧ z (Fin.natAdd 2 l) = true) :
    ∀ z : Fin (N + N) → Bool,
      circuitFun (N + N) (Restriction.circuit (fun i => some (embed ep el i)) C) z = true ↔
      ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true := by
  intro z
  rw [Restriction.eval _ C hm, sem]
  constructor
  · rintro ⟨p, l, hi, hp, hl⟩
    exact ⟨ep p, el l, hi, by simpa only [rename_point] using hp,
      by simpa only [rename_line] using hl⟩
  · rintro ⟨p, l, hi, hp, hl⟩
    obtain ⟨a, b, rfl, rfl⟩ := support p l hi
    exact ⟨a, b, hi, by simpa only [rename_point] using hp,
      by simpa only [rename_line] using hl⟩

end Support

namespace Support

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
lemma witness_below : ∀ a b c d : Bool,
    ∀ j < (Two.witness a b c d).gates.length,
      (NestedCover.gateAt (Two.witness a b c d) j).op = GateOp.and →
      ∀ z : Fin 4 → Bool,
        PEqualNP.EdgeOwnership.gateVal 4 (Two.witness a b c d) j z = true →
        circuitFun 4 (Two.witness a b c d) z = true := by
  let _ : DecidableEq GateOp := NestedCover.gateOpDecEq
  decide

lemma canonical_lower (I : Fin 2 → Fin 2 → Prop) [DecidableRel I] (C : Circuit)
    (hm : Monotone2 C) (hb : NestedCover.ReadsBack 4 C)
    (sem : ∀ z : Fin 4 → Bool, circuitFun 4 C z = true ↔
      ∃ p l : Fin 2, I p l ∧ z (Fin.castAdd 2 p) = true ∧ z (Fin.natAdd 2 l) = true) :
    (Two.witness (decide (I 0 0)) (decide (I 0 1))
      (decide (I 1 0)) (decide (I 1 1))).size ≤ C.size := by
  rw [Two.witness_size]
  apply Four.lower_bound_with_certificate Four.certificate _ C hm hb
  intro x
  rw [Two.circuit_truth I C sem, Four.target_bits]
  obtain ⟨ha, hb, hc, hd⟩ := Two.code_bits (decide (I 0 0)) (decide (I 0 1))
    (decide (I 1 0)) (decide (I 1 1))
  simp only [ha, hb, hc, hd, Two.truth]

lemma canonical_sem (I : Fin 2 → Fin 2 → Prop) [DecidableRel I] :
    ∀ z : Fin 4 → Bool,
      circuitFun 4 (Two.witness (decide (I 0 0)) (decide (I 0 1))
        (decide (I 1 0)) (decide (I 1 1))) z = true ↔
      ∃ p l : Fin 2, I p l ∧ z (Fin.castAdd 2 p) = true ∧ z (Fin.natAdd 2 l) = true := by
  intro z
  rw [(Two.witness_props _ _ _ _).2.2.1, Two.relation_truth]
  simp only [Two.relation_encode I]

lemma normalize_supported {N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I]
    (ep el : Fin 2 ↪ Fin N)
    (support : ∀ p l, I p l → ∃ a b : Fin 2, p = ep a ∧ l = el b)
    (C : Circuit) (hm : Monotone2 C) (hb : NestedCover.ReadsBack (N + N) C)
    (sem : ∀ z : Fin (N + N) → Bool, circuitFun (N + N) C z = true ↔
      ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) :
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
  let J : Fin 2 → Fin 2 → Prop := fun p l => I (ep p) (el l)
  let A := Restriction.circuit (project ep el) C
  have am : Monotone2 A := Restriction.mono _ C hm
  have ab : NestedCover.ReadsBack 4 A := Restriction.readsBack _ C hb
  have ae := computes_project ep el I support C hm sem
  let W := Two.witness (decide (J 0 0)) (decide (J 0 1))
    (decide (J 1 0)) (decide (J 1 1))
  have wl : W.size ≤ A.size := canonical_lower J A am ab ae
  have wm : Monotone2 W := (Two.witness_props _ _ _ _).1
  have wb : NestedCover.ReadsBack 4 W := (Two.witness_props _ _ _ _).2.1
  have we := canonical_sem J
  let ρ : Fin 4 → Option (Fin (N + N)) := fun i => some (embed ep el i)
  let D := Restriction.circuit ρ W
  have dm : Monotone2 D := Restriction.mono ρ W wm
  have db : NestedCover.ReadsBack (N + N) D := Restriction.readsBack ρ W wb
  have ds : D.size ≤ C.size := by
    change (Restriction.circuit ρ W).size ≤ C.size
    rw [Restriction.size]
    exact wl.trans_eq (Restriction.size (project ep el) C)
  have de : ∀ z : Fin (N + N) → Bool, circuitFun (N + N) D z = true ↔
      ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true :=
    computes_rename ep el I support W wm we
  have below : ∀ j < D.gates.length, (NestedCover.gateAt D j).op = GateOp.and →
      ∀ z : Fin (N + N) → Bool, PEqualNP.EdgeOwnership.gateVal (N + N) D j z = true →
        circuitFun (N + N) D z = true := by
    intro j hj hand z hz
    change PEqualNP.EdgeOwnership.gateVal (N + N) (Restriction.circuit ρ W) j z = true at hz
    rw [Restriction.gate_value_at ρ W wm] at hz
    change circuitFun (N + N) (Restriction.circuit ρ W) z = true
    rw [Restriction.eval ρ W wm]
    exact witness_below _ _ _ _ j
      (by simpa only [D, Restriction.circuit, List.length_map] using hj)
      (Restriction.and_origin ρ W j hand) _ hz
  refine ⟨D, dm, db, ds, de, ?_, ?_⟩
  · intro j hj hand p l hn
    apply Bool.eq_false_iff.mpr
    intro hv
    have ho := below j hj hand _ hv
    rw [incidence_nonedge_false N I D de p l hn] at ho
    cases ho
  · intro j hj hand
    constructor
    · intro p
      apply Bool.eq_false_iff.mpr
      intro hv
      have ho := below j hj hand _ hv
      rw [incidence_point_false N I D de p] at ho
      cases ho
    · intro l
      apply Bool.eq_false_iff.mpr
      intro hv
      have ho := below j hj hand _ hv
      rw [incidence_line_false N I D de l] at ho
      cases ho

end Support

namespace SingletonFormula

open PEqualNP.MetaComplexity

def Positive {n : ℕ} : DMFormula n → Prop
  | .lit _ b => b = true
  | .and a b => Positive a ∧ Positive b
  | .or a b => Positive a ∧ Positive b

def one {n : ℕ} (i : Fin n) : Fin n → Bool := fun j => decide (j = i)

def Clean {n : ℕ} : DMFormula n → Prop
  | .lit _ _ => True
  | .and a b => Clean a ∧ Clean b ∧ ∀ i, (a.eval (one i) && b.eval (one i)) = false
  | .or a b => Clean a ∧ Clean b

lemma leaves_positive {n : ℕ} (a : DMFormula n) : 0 < a.leaves := by
  induction a <;> simp_all [DMFormula.leaves]

lemma extract {n : ℕ} (a : DMFormula n) (hp : Positive a) (hc : Clean a)
    (i : Fin n) (hi : a.eval (one i) = true) :
    (∀ x, a.eval x = x i) ∨
      ∃ r : DMFormula n, Positive r ∧ Clean r ∧ r.leaves + 1 ≤ a.leaves ∧
        ∀ x, a.eval x = (x i || r.eval x) := by
  induction a with
  | lit j b =>
    have hb : b = true := hp
    subst b
    have hji : j = i := of_decide_eq_true hi
    subst j
    exact Or.inl (by intro x; rfl)
  | and a b ia ib =>
    have hh := hc.2.2 i
    change (a.eval (one i) && b.eval (one i)) = true at hi
    rw [hh] at hi
    contradiction
  | or a b ia ib =>
    change (a.eval (one i) || b.eval (one i)) = true at hi
    simp only [Bool.or_eq_true] at hi
    rcases hi with ha | hb
    · rcases ia hp.1 hc.1 ha with ha | ⟨r, rp, rc, rsize, hr⟩
      · refine Or.inr ⟨b, hp.2, hc.2, ?_, ?_⟩
        · have := leaves_positive a
          simp only [DMFormula.leaves]
          omega
        · intro x
          simp only [DMFormula.eval, ha x]
      · refine Or.inr ⟨.or r b, ⟨rp, hp.2⟩, ⟨rc, hc.2⟩, ?_, ?_⟩
        · simp only [DMFormula.leaves]
          omega
        · intro x
          simp only [DMFormula.eval, hr x, Bool.or_assoc]
    · rcases ib hp.2 hc.2 hb with hb | ⟨r, rp, rc, rsize, hr⟩
      · refine Or.inr ⟨a, hp.1, hc.1, ?_, ?_⟩
        · have := leaves_positive b
          simp only [DMFormula.leaves]
          omega
        · intro x
          simp only [DMFormula.eval, hb x, Bool.or_comm]
      · refine Or.inr ⟨.or a r, ⟨hp.1, rp⟩, ⟨hc.1, rc⟩, ?_, ?_⟩
        · simp only [DMFormula.leaves]
          omega
        · intro x
          simp only [DMFormula.eval, hr x]
          cases x i <;> cases a.eval x <;> cases r.eval x <;> rfl

lemma normalize_bounded {n : ℕ} (k : ℕ) :
    ∀ a : DMFormula n, a.leaves ≤ k → Positive a →
      ∃ b : DMFormula n, Positive b ∧ Clean b ∧ b.leaves ≤ a.leaves ∧
        ∀ x, b.eval x = a.eval x := by
  induction k using Nat.strong_induction_on with
  | ind k ih =>
    intro a hsize hp
    cases a with
    | lit i b => exact ⟨.lit i b, hp, trivial, le_rfl, fun _ => rfl⟩
    | or a b =>
      have aless : a.leaves < k := by
        have := leaves_positive b
        simp only [DMFormula.leaves] at hsize
        omega
      have bless : b.leaves < k := by
        have := leaves_positive a
        simp only [DMFormula.leaves] at hsize
        omega
      obtain ⟨a', ap, ac, asize, ae⟩ := ih a.leaves aless a le_rfl hp.1
      obtain ⟨b', bp, bc, bsize, be⟩ := ih b.leaves bless b le_rfl hp.2
      refine ⟨.or a' b', ⟨ap, bp⟩, ⟨ac, bc⟩, ?_, ?_⟩
      · change a'.leaves + b'.leaves ≤ a.leaves + b.leaves
        omega
      · intro x
        simp only [DMFormula.eval, ae, be]
    | and a b =>
      have aless : a.leaves < k := by
        have := leaves_positive b
        simp only [DMFormula.leaves] at hsize
        omega
      have bless : b.leaves < k := by
        have := leaves_positive a
        simp only [DMFormula.leaves] at hsize
        omega
      obtain ⟨a', ap, ac, asize, ae⟩ := ih a.leaves aless a le_rfl hp.1
      obtain ⟨b', bp, bc, bsize, be⟩ := ih b.leaves bless b le_rfl hp.2
      by_cases hclean : ∀ i, (a'.eval (one i) && b'.eval (one i)) = false
      · refine ⟨.and a' b', ⟨ap, bp⟩, ⟨ac, bc, hclean⟩, ?_, ?_⟩
        · change a'.leaves + b'.leaves ≤ a.leaves + b.leaves
          omega
        · intro x
          simp only [DMFormula.eval, ae, be]
      · push Not at hclean
        obtain ⟨i, hi⟩ := hclean
        have hai : a'.eval (one i) = true := by
          cases ha : a'.eval (one i) <;> simp_all
        have hbi : b'.eval (one i) = true := by
          cases hb : b'.eval (one i) <;> simp_all
        rcases extract a' ap ac i hai with ha | ⟨r, rp, rc, rsize, hr⟩
        · rcases extract b' bp bc i hbi with hb | ⟨s, sp, sc, ssize, hs⟩
          · refine ⟨.lit i true, rfl, trivial, ?_, ?_⟩
            · have := leaves_positive a
              change 1 ≤ a.leaves + b.leaves
              omega
            · intro x
              change x i = (a.eval x && b.eval x)
              rw [← ae x, ← be x, ha x, hb x]
              simp
          · refine ⟨.lit i true, rfl, trivial, ?_, ?_⟩
            · have := leaves_positive a
              change 1 ≤ a.leaves + b.leaves
              omega
            · intro x
              change x i = (a.eval x && b.eval x)
              rw [← ae x, ← be x, ha x, hs x]
              cases x i <;> simp
        · rcases extract b' bp bc i hbi with hb | ⟨s, sp, sc, ssize, hs⟩
          · refine ⟨.lit i true, rfl, trivial, ?_, ?_⟩
            · have := leaves_positive a
              change 1 ≤ a.leaves + b.leaves
              omega
            · intro x
              change x i = (a.eval x && b.eval x)
              rw [← ae x, ← be x, hr x, hb x]
              cases x i <;> simp
          · let c : DMFormula n := .or (.lit i true) (.and r s)
            have csize : c.leaves < k := by
              simp only [c, DMFormula.leaves] at *
              omega
            have cp : Positive c := ⟨rfl, rp, sp⟩
            obtain ⟨d, dp, dc, dsize, de⟩ := ih c.leaves csize c le_rfl cp
            refine ⟨d, dp, dc, ?_, ?_⟩
            · simp only [c, DMFormula.leaves] at dsize ⊢
              omega
            · intro x
              rw [de x]
              change (x i || (r.eval x && s.eval x)) = (a.eval x && b.eval x)
              rw [← ae x, ← be x, hr x, hs x]
              cases x i <;> cases r.eval x <;> cases s.eval x <;> rfl

lemma normalize {n : ℕ} (a : DMFormula n) (hp : Positive a) :
    ∃ b : DMFormula n, Positive b ∧ Clean b ∧ b.leaves ≤ a.leaves ∧
      ∀ x, b.eval x = a.eval x :=
  normalize_bounded a.leaves a le_rfl hp

end SingletonFormula

namespace Dependency

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

variable {n : ℕ}

lemma getD_snoc_ne {α : Type} (L : List α) (S d : α) (j : ℕ) (h : j ≠ L.length) :
    (L ++ [S]).getD j d = L.getD j d := by
  by_cases hj : j < L.length
  · exact List.getD_append _ _ _ _ hj
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

lemma getD_snoc_eq {α : Type} (L : List α) (S d : α) : (L ++ [S]).getD L.length d = S := by
  simp


def gateSupp (L : List (Finset (Fin n))) (g : Gate) : Finset (Fin n) :=
  (g.inputs.map fun a => L.getD a ∅).foldr (· ∪ ·) ∅

lemma mem_foldr_union (l : List ℕ) (F : ℕ → Finset (Fin n)) (i : Fin n) :
    i ∈ (l.map F).foldr (· ∪ ·) ∅ ↔ ∃ a ∈ l, i ∈ F a := by
  induction l with
  | nil => simp
  | cons b l ih => simp [ih]

lemma mem_gateSupp (L : List (Finset (Fin n))) (g : Gate) (i : Fin n) :
    i ∈ gateSupp L g ↔ ∃ a ∈ g.inputs, i ∈ L.getD a ∅ :=
  mem_foldr_union _ _ _


def suppsFrom (gs : List Gate) (L : List (Finset (Fin n))) : List (Finset (Fin n)) :=
  gs.foldl (fun L g => L ++ [gateSupp L g]) L


def inputSupps (n : ℕ) : List (Finset (Fin n)) := List.ofFn fun i : Fin n => {i}


def Agree (x y : Fin n → Bool) (L : List (Finset (Fin n))) (w w' : List Bool) : Prop :=
  L.length = w.length ∧ w.length = w'.length ∧
    ∀ j : ℕ, (∀ i ∈ L.getD j ∅, x i = y i) → w.getD j false = w'.getD j false

lemma agree_wiresFrom (x y : Fin n → Bool) (gs : List Gate) :
    ∀ (L : List (Finset (Fin n))) (w w' : List Bool), Agree x y L w w' →
      Agree x y (suppsFrom gs L) (wiresFrom gs w) (wiresFrom gs w') := by
  induction gs with
  | nil => intro L w w' h; exact h
  | cons g gs ih =>
    intro L w w' h
    obtain ⟨h1, h2, h3⟩ := h
    apply ih (L ++ [gateSupp L g])
      (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
      (w' ++ [g.op.eval (g.inputs.map fun i => w'.getD i false)])
    refine ⟨by simp [h1], by simp [h2], ?_⟩
    intro j hj
    by_cases hjl : j = L.length
    · subst hjl
      rw [getD_snoc_eq] at hj
      rw [h1, getD_snoc_eq, h2, getD_snoc_eq]
      congr 1
      apply List.map_congr_left
      intro a ha
      exact h3 a (fun i hi => hj i ((mem_gateSupp L g i).2 ⟨a, ha, hi⟩))
    · rw [getD_snoc_ne _ _ _ _ hjl] at hj
      rw [getD_snoc_ne _ _ _ _ (by omega), getD_snoc_ne _ _ _ _ (by omega)]
      exact h3 j hj

lemma agree_inputs (x y : Fin n → Bool) :
    Agree x y (inputSupps n) (List.ofFn x) (List.ofFn y) := by
  refine ⟨by simp [inputSupps], by simp, ?_⟩
  intro j hj
  by_cases hjn : j < n
  · have hx : x ⟨j, hjn⟩ = y ⟨j, hjn⟩ := hj _ (by simp [inputSupps, hjn])
    simp [hjn, hx]
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]


def Cnt (t : ℕ) (L : List (Finset (Fin n))) : Prop :=
  ∀ W : Finset ℕ, (W.biUnion fun j => L.getD j ∅).card ≤ t + W.card

lemma cnt_inputs : Cnt 0 (inputSupps n) := by
  intro W
  refine le_trans Finset.card_biUnion_le ?_
  rw [zero_add, Finset.card_eq_sum_ones]
  apply Finset.sum_le_sum
  intro j _
  by_cases hjn : j < n
  · simp [inputSupps, hjn]
  · rw [List.getD_eq_default _ _ (by simp [inputSupps]; omega)]; simp

lemma cnt_step (t : ℕ) (L : List (Finset (Fin n))) (g : Gate) (hg : g.inputs.length ≤ 2)
    (h : Cnt t L) : Cnt (t + 1) (L ++ [gateSupp L g]) := by
  intro W
  by_cases hW : L.length ∈ W
  · have hsub : (W.biUnion fun j => (L ++ [gateSupp L g]).getD j ∅)
        ⊆ ((W.erase L.length ∪ g.inputs.toFinset).biUnion fun j => L.getD j ∅) := by
      intro i hi
      rw [Finset.mem_biUnion] at hi ⊢
      obtain ⟨j, hjW, hij⟩ := hi
      by_cases hjl : j = L.length
      · subst hjl
        rw [getD_snoc_eq] at hij
        obtain ⟨a, ha, hia⟩ := (mem_gateSupp L g i).1 hij
        exact ⟨a, Finset.mem_union_right _ (List.mem_toFinset.2 ha), hia⟩
      · rw [getD_snoc_ne _ _ _ _ hjl] at hij
        exact ⟨j, Finset.mem_union_left _ (Finset.mem_erase.2 ⟨hjl, hjW⟩), hij⟩
    have hc1 : (W.erase L.length ∪ g.inputs.toFinset).card ≤ (W.card - 1) + 2 := by
      refine le_trans (Finset.card_union_le _ _) ?_
      rw [Finset.card_erase_of_mem hW]
      exact Nat.add_le_add_left (le_trans (List.toFinset_card_le _) hg) _
    have hWpos : 1 ≤ W.card := Finset.card_pos.2 ⟨_, hW⟩
    have := h (W.erase L.length ∪ g.inputs.toFinset)
    have := Finset.card_le_card hsub
    omega
  · have heq : (W.biUnion fun j => (L ++ [gateSupp L g]).getD j ∅)
        = (W.biUnion fun j => L.getD j ∅) := by
      apply Finset.biUnion_congr rfl
      intro j hj
      exact getD_snoc_ne _ _ _ _ (fun e => hW (e ▸ hj))
    rw [heq]
    have := h W
    omega

lemma cnt_suppsFrom (gs : List Gate) : ∀ (t : ℕ) (L : List (Finset (Fin n))),
    (∀ g ∈ gs, g.inputs.length ≤ 2) → Cnt t L → Cnt (t + gs.length) (suppsFrom gs L) := by
  induction gs with
  | nil => intro t L _ h; exact h
  | cons g gs ih =>
    intro t L hok h
    have := ih (t + 1) (L ++ [gateSupp L g]) (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
      (cnt_step t L g (hok g List.mem_cons_self) h)
    rw [List.length_cons, show t + (gs.length + 1) = t + 1 + gs.length by omega]
    exact this

def support (n : ℕ) (C : Circuit) : Finset (Fin n) :=
  (suppsFrom C.gates (inputSupps n)).getD C.output ∅

lemma support_card (n : ℕ) (C : Circuit)
    (hfan : ∀ g ∈ C.gates, g.inputs.length ≤ 2) : (support n C).card ≤ C.size + 1 := by
  have hc := cnt_suppsFrom C.gates 0 (inputSupps n) hfan cnt_inputs {C.output}
  simpa [support, Circuit.size] using hc

lemma agree_support (n : ℕ) (C : Circuit) (x y : Fin n → Bool)
    (h : ∀ i ∈ support n C, x i = y i) : circuitFun n C x = circuitFun n C y := by
  exact (agree_wiresFrom x y C.gates _ _ _ (agree_inputs _ _)).2.2 C.output h

lemma essential_card_le (n : ℕ) (C : Circuit)
    (hfan : ∀ g ∈ C.gates, g.inputs.length ≤ 2) (S : Finset (Fin n))
    (hdep : ∀ i ∈ S, ∃ x : Fin n → Bool,
      circuitFun n C (Function.update x i (!x i)) ≠ circuitFun n C x) :
    S.card ≤ C.size + 1 := by
  have hsub : S ⊆ support n C := by
    intro i hi
    by_contra hnot
    obtain ⟨x, hx⟩ := hdep i hi
    apply hx
    apply agree_support
    intro k hk
    have hki : k ≠ i := by
      intro he
      exact hnot (he ▸ hk)
    simp [Function.update_of_ne hki]
  exact (Finset.card_le_card hsub).trans (support_card n C hfan)

lemma all_inputs_lower (n : ℕ) (C : Circuit)
    (hfan : ∀ g ∈ C.gates, g.inputs.length ≤ 2)
    (hdep : ∀ i : Fin n, ∃ x : Fin n → Bool,
      circuitFun n C (Function.update x i (!x i)) ≠ circuitFun n C x) :
    n ≤ C.size + 1 := by
  have h := essential_card_le n C hfan Finset.univ (fun i _ => hdep i)
  simpa using h

def activePoints (N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] : Finset (Fin N) :=
  Finset.univ.filter (fun p => ∃ l, I p l)

def activeLines (N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] : Finset (Fin N) :=
  Finset.univ.filter (fun l => ∃ p, I p l)

def activeInputs (N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] : Finset (Fin (N + N)) :=
  (activePoints N I).image (Fin.castAdd N) ∪ (activeLines N I).image (Fin.natAdd N)

lemma point_ne_line {N : ℕ} (p l : Fin N) : Fin.castAdd N p ≠ Fin.natAdd N l := by
  intro h
  have hv := congrArg Fin.val h
  simp only [Fin.val_castAdd, Fin.val_natAdd] at hv
  omega

lemma activeInputs_card (N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] :
    (activeInputs N I).card = (activePoints N I).card + (activeLines N I).card := by
  have hp : Function.Injective (Fin.castAdd N : Fin N → Fin (N + N)) := by
    intro a b h
    have hv := congrArg (fun k : Fin (N + N) => k.val) h
    exact Fin.ext hv
  have hl : Function.Injective (Fin.natAdd N : Fin N → Fin (N + N)) := by
    intro a b h
    apply Fin.ext
    have hv := congrArg Fin.val h
    simp only [Fin.val_natAdd] at hv
    omega
  have hd : Disjoint ((activePoints N I).image (Fin.castAdd N))
      ((activeLines N I).image (Fin.natAdd N)) := by
    apply Finset.disjoint_left.mpr
    intro k hkP hkL
    obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp hkP
    obtain ⟨l, _, he⟩ := Finset.mem_image.mp hkL
    exact point_ne_line p l he.symm
  rw [activeInputs, Finset.card_union_of_disjoint hd,
    Finset.card_image_of_injective _ hp, Finset.card_image_of_injective _ hl]

lemma incident_point_essential (N : ℕ) (I : Fin N → Fin N → Prop) (C : Circuit)
    (hfun : ∀ z : Fin (N + N) → Bool, circuitFun (N + N) C z = true ↔
      ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true)
    (p l : Fin N) (hI : I p l) :
    ∃ x : Fin (N + N) → Bool,
      circuitFun (N + N) C (Function.update x (Fin.castAdd N p) (!x (Fin.castAdd N p))) ≠
        circuitFun (N + N) C x := by
  let x : Fin (N + N) → Bool := fun k => decide (k = Fin.natAdd N l)
  have hx : x (Fin.castAdd N p) = false := by
    simp only [x, decide_eq_false_iff_not]
    exact point_ne_line p l
  have hf : circuitFun (N + N) C x = false := by
    apply Bool.eq_false_iff.mpr
    intro h
    obtain ⟨q, m, _, hq, _⟩ := (hfun x).mp h
    have he : Fin.castAdd N q = Fin.natAdd N l := of_decide_eq_true hq
    exact point_ne_line q l he
  have ht : circuitFun (N + N) C (Function.update x (Fin.castAdd N p) (!x (Fin.castAdd N p))) = true := by
    apply (hfun _).mpr
    refine ⟨p, l, hI, ?_, ?_⟩
    · rw [Function.update_self, hx]
      rfl
    · rw [Function.update_of_ne (point_ne_line p l).symm]
      simp [x]
  exact ⟨x, by rw [ht, hf]; decide⟩

lemma incident_line_essential (N : ℕ) (I : Fin N → Fin N → Prop) (C : Circuit)
    (hfun : ∀ z : Fin (N + N) → Bool, circuitFun (N + N) C z = true ↔
      ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true)
    (p l : Fin N) (hI : I p l) :
    ∃ x : Fin (N + N) → Bool,
      circuitFun (N + N) C (Function.update x (Fin.natAdd N l) (!x (Fin.natAdd N l))) ≠
        circuitFun (N + N) C x := by
  let x : Fin (N + N) → Bool := fun k => decide (k = Fin.castAdd N p)
  have hx : x (Fin.natAdd N l) = false := by
    simp only [x, decide_eq_false_iff_not]
    exact (point_ne_line p l).symm
  have hf : circuitFun (N + N) C x = false := by
    apply Bool.eq_false_iff.mpr
    intro h
    obtain ⟨q, m, _, _, hm⟩ := (hfun x).mp h
    have he : Fin.natAdd N m = Fin.castAdd N p := of_decide_eq_true hm
    exact point_ne_line p m he.symm
  have ht : circuitFun (N + N) C (Function.update x (Fin.natAdd N l) (!x (Fin.natAdd N l))) = true := by
    apply (hfun _).mpr
    refine ⟨p, l, hI, ?_, ?_⟩
    · rw [Function.update_of_ne (point_ne_line p l)]
      simp [x]
    · rw [Function.update_self, hx]
      rfl
  exact ⟨x, by rw [ht, hf]; decide⟩

lemma incidence_active_bound (N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I]
    (C : Circuit) (hfan : ∀ g ∈ C.gates, g.inputs.length ≤ 2)
    (hfun : ∀ z : Fin (N + N) → Bool, circuitFun (N + N) C z = true ↔
      ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) :
    (activePoints N I).card + (activeLines N I).card ≤ C.size + 1 := by
  rw [← activeInputs_card]
  apply essential_card_le (N + N) C hfan
  intro k hk
  rcases Finset.mem_union.mp hk with hk | hk
  · obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hk
    obtain ⟨l, hI⟩ := (Finset.mem_filter.mp hp).2
    exact incident_point_essential N I C hfun p l hI
  · obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp hk
    obtain ⟨p, hI⟩ := (Finset.mem_filter.mp hl).2
    exact incident_line_essential N I C hfun p l hI

lemma active_sides_bound (N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I]
    (C : Circuit) (hfan : ∀ g ∈ C.gates, g.inputs.length ≤ 2)
    (hfun : ∀ z : Fin (N + N) → Bool, circuitFun (N + N) C z = true ↔
      ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) :
    (activePoints N I).card ≤ C.size ∧ (activeLines N I).card ≤ C.size := by
  by_cases hI : ∃ p l, I p l
  · obtain ⟨p, l, hpl⟩ := hI
    have hp : 0 < (activePoints N I).card := by
      apply Finset.card_pos.mpr
      refine ⟨p, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
      exact ⟨l, hpl⟩
    have hl : 0 < (activeLines N I).card := by
      apply Finset.card_pos.mpr
      refine ⟨l, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
      exact ⟨p, hpl⟩
    have h := incidence_active_bound N I C hfan hfun
    omega
  · have hn : ∀ p l, ¬ I p l := by
      intro p l hpl
      exact hI ⟨p, l, hpl⟩
    simp [activePoints, activeLines, hn]

end Dependency

namespace Star

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def run (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

lemma run_append (gs hs : List Gate) (w : List Bool) :
    run (gs ++ hs) w = run hs (run gs w) := by
  simp [run, List.foldl_append]

lemma run_prefix (gs : List Gate) : ∀ w : List Bool,
    ∃ t : List Bool, run gs w = w ++ t ∧ t.length = gs.length := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp [run], rfl⟩
  | cons g gs ih =>
    intro w
    obtain ⟨t, ht, hl⟩ := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: t, ?_, by simp [hl]⟩
    change run gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) = _
    rw [ht]
    simp

lemma run_length (gs : List Gate) (w : List Bool) :
    (run gs w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := run_prefix gs w
  rw [ht]
  simp [hl]

lemma run_input (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (run gs w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := run_prefix gs w
  rw [ht, List.getD_append _ _ _ _ hi]

def chain (n out : ℕ) : List ℕ → List Gate
  | [] => []
  | i :: xs => ⟨.or, [out, i]⟩ :: chain (n + 1) n xs

def chainOut (n out : ℕ) : List ℕ → ℕ
  | [] => out
  | _ :: xs => chainOut (n + 1) n xs

lemma chain_length (xs : List ℕ) (n out : ℕ) : (chain n out xs).length = xs.length := by
  induction xs generalizing n out with
  | nil => rfl
  | cons i xs ih => simp [chain, ih]

lemma chain_pure (xs : List ℕ) (n out : ℕ) :
    ∀ g ∈ chain n out xs, g.op = GateOp.or ∧ g.inputs.length = 2 := by
  induction xs generalizing n out with
  | nil => simp [chain]
  | cons i xs ih =>
    intro g hg
    rcases List.mem_cons.mp hg with rfl | hg
    · simp
    · exact ih (n + 1) n g hg

lemma chain_out_lt (xs : List ℕ) (n out : ℕ) (ho : out < n) :
    chainOut n out xs < n + xs.length := by
  induction xs generalizing n out with
  | nil => simpa [chainOut] using ho
  | cons i xs ih =>
    have h := ih (n + 1) n (by omega)
    simp only [chainOut, List.length_cons]
    omega

lemma chain_back (xs : List ℕ) (n out : ℕ) (ho : out < n) (hx : ∀ i ∈ xs, i < n) :
    ∀ j < (chain n out xs).length,
      ∀ i ∈ ((chain n out xs).getD j ⟨.or, []⟩).inputs, i < n + j := by
  induction xs generalizing n out with
  | nil => simp [chain]
  | cons x xs ih =>
    intro j hj i hi
    cases j with
    | zero =>
      simp only [chain, List.getD_cons_zero, List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with hi | hi
      · omega
      · have h := hx x List.mem_cons_self
        omega
    | succ j =>
      have h := ih (n + 1) n (by omega)
        (fun i hi => Nat.lt_succ_of_lt (hx i (List.mem_cons_of_mem x hi))) j
        (by simpa [chain] using hj) i (by simpa [chain] using hi)
      omega

lemma chain_op (xs : List ℕ) (n out j : ℕ) (hj : j < (chain n out xs).length) :
    ((chain n out xs).getD j ⟨.or, []⟩).op = GateOp.or := by
  rw [List.getD_eq_getElem _ _ hj]
  exact (chain_pure xs n out _ (List.getElem_mem hj)).1

lemma chain_eval (xs : List ℕ) : ∀ (n out : ℕ) (w : List Bool), w.length = n →
    out < n → (∀ i ∈ xs, i < n) →
    (run (chain n out xs) w).getD (chainOut n out xs) false =
      (w.getD out false || xs.any (fun i => w.getD i false)) := by
  induction xs with
  | nil => intro n out w hw ho hx; simp [chain, chainOut, run]
  | cons i xs ih =>
    intro n out w hw ho hx
    let v := w ++ [w.getD out false || w.getD i false]
    have hv : v.length = n + 1 := by simp [v, hw]
    have hn : v.getD n false = (w.getD out false || w.getD i false) := by
      rw [show n = w.length from hw.symm]
      simp [v]
    have hxs : xs.any (fun i => v.getD i false) = xs.any (fun i => w.getD i false) := by
      have hm : xs.map (fun i => v.getD i false) = xs.map (fun i => w.getD i false) := by
        apply List.map_congr_left
        intro k hk
        exact List.getD_append _ _ _ _ (by rw [hw]; exact hx k (List.mem_cons_of_mem i hk))
      have hh := congrArg (fun l : List Bool => l.any id) hm
      simpa only [List.any_map, Function.comp_def, id] using hh
    have hrec := ih (n + 1) n v hv (by omega)
      (fun k hk => Nat.lt_succ_of_lt (hx k (List.mem_cons_of_mem i hk)))
    change (run (chain (n + 1) n xs)
      (w ++ [GateOp.or.eval ([out, i].map fun k => w.getD k false)] )).getD
        (chainOut (n + 1) n xs) false = _
    simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons,
      List.any_nil, Bool.or_false, id]
    rw [hrec, hn, hxs]
    exact Bool.or_assoc _ _ _

lemma construct (n : ℕ) (p : Fin n) (xs : List (Fin n)) :
    ∃ D : Circuit, Monotone2 D ∧ NestedCover.ReadsBack n D ∧ D.size ≤ xs.length ∧
      (∀ z : Fin n → Bool, circuitFun n D z = (z p && xs.any z)) ∧
      (∀ j < D.gates.length, (NestedCover.gateAt D j).op = GateOp.and →
        ∀ z : Fin n → Bool, PEqualNP.EdgeOwnership.gateVal n D j z = true →
          circuitFun n D z = true) := by
  cases xs with
  | nil =>
    refine ⟨⟨[], n⟩, ?_, ?_, ?_, ?_, ?_⟩
    · simp [Monotone2]
    · simp [NestedCover.ReadsBack]
    · simp [Circuit.size]
    · intro z
      simp [circuitFun, Circuit.eval, Circuit.wires]
    · simp
  | cons x xs =>
    let ys := xs.map Fin.val
    let gs := chain n x.val ys
    let out := chainOut n x.val ys
    let D : Circuit := ⟨gs ++ [⟨.and, [p.val, out]⟩], n + gs.length⟩
    have hys : ∀ i ∈ ys, i < n := by
      intro i hi
      obtain ⟨q, _, rfl⟩ := List.mem_map.mp hi
      exact q.isLt
    have hout : out < n + gs.length := by
      simpa only [out, gs, chain_length] using chain_out_lt ys n x.val x.isLt
    refine ⟨D, ?_, ?_, ?_, ?_, ?_⟩
    · intro g hg
      rcases List.mem_append.mp hg with hg | hg
      · obtain ⟨hop, hlen⟩ := chain_pure ys n x.val g hg
        simp [hop, hlen]
      · simp only [List.mem_singleton] at hg
        subst g
        simp
    · intro j hj i hi
      change i ∈ ((gs ++ [(⟨.and, [p.val, out]⟩ : Gate)]).getD j (⟨.or, []⟩ : Gate)).inputs at hi
      by_cases hj' : j < gs.length
      · rw [List.getD_append _ _ _ _ hj'] at hi
        exact chain_back ys n x.val x.isLt hys j hj' i hi
      · have he : j = gs.length := by
          simp only [D, List.length_append, List.length_singleton] at hj
          omega
        subst j
        rw [List.getD_append_right _ _ _ _ (by omega)] at hi
        simp only [Nat.sub_self, List.getD_cons_zero, List.mem_cons,
          List.not_mem_nil, or_false] at hi
        rcases hi with rfl | rfl
        · omega
        · exact hout
    · simp [D, Circuit.size, gs, chain_length, ys]
    · intro z
      let v := run gs (List.ofFn z)
      have hv : v.length = n + gs.length := by simp [v, run_length]
      have hp : v.getD p.val false = z p := by
        rw [run_input _ _ _ (by simp)]
        simp
      have hor : v.getD out false = (z x || xs.any z) := by
        have h := chain_eval ys n x.val (List.ofFn z) (by simp) x.isLt hys
        have hxs : ys.any (fun i => (List.ofFn z).getD i false) = xs.any z := by
          dsimp [ys]
          rw [List.any_map]
          apply List.any_congr rfl
          intro q
          simp
        simpa only [hxs, show (List.ofFn z).getD x.val false = z x by simp] using h
      change (run (gs ++ [⟨.and, [p.val, out]⟩]) (List.ofFn z)).getD
        (n + gs.length) false = _
      rw [run_append]
      change (v ++ [GateOp.and.eval ([p.val, out].map fun i => v.getD i false)]).getD
        (n + gs.length) false = _
      rw [← hv, List.getD_append_right _ _ _ _ (by omega)]
      simp only [Nat.sub_self, List.getD_cons_zero, GateOp.eval, List.map_cons,
        List.map_nil, List.all_cons, List.all_nil, id, Bool.and_true, hp, hor, List.any_cons]
    · intro j hj hand z hz
      by_cases hj' : j < gs.length
      · have hor : (NestedCover.gateAt D j).op = GateOp.or := by
          unfold NestedCover.gateAt
          change ((gs ++ [(⟨.and, [p.val, out]⟩ : Gate)]).getD j (⟨.or, []⟩ : Gate)).op = GateOp.or
          rw [List.getD_append _ _ _ _ hj']
          exact chain_op ys n x.val j hj'
        rw [hor] at hand
        cases hand
      · have he : j = gs.length := by
          simp only [D, List.length_append, List.length_singleton] at hj
          omega
        subst j
        exact hz

end Star

namespace Star

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def NormalForm (N : ℕ) (I : Fin N → Fin N → Prop) (C : Circuit) : Prop :=
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
        decide (k = Fin.natAdd N l)))).getD (N + N + j) false = false)

lemma complete (N : ℕ) (I : Fin N → Fin N → Prop) (C D : Circuit)
    (hm : Monotone2 D) (hb : NestedCover.ReadsBack (N + N) D) (hs : D.size ≤ C.size)
    (sem : ∀ z : Fin (N + N) → Bool, circuitFun (N + N) D z = true ↔
      ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true)
    (below : ∀ j < D.gates.length, (NestedCover.gateAt D j).op = GateOp.and →
      ∀ z : Fin (N + N) → Bool, PEqualNP.EdgeOwnership.gateVal (N + N) D j z = true →
        circuitFun (N + N) D z = true) : NormalForm N I C := by
  refine ⟨D, hm, hb, hs, sem, ?_, ?_⟩
  · intro j hj hand p l hn
    apply Bool.eq_false_iff.mpr
    intro hv
    have ho := below j hj hand _ hv
    rw [incidence_nonedge_false N I D sem p l hn] at ho
    cases ho
  · intro j hj hand
    constructor
    · intro p
      apply Bool.eq_false_iff.mpr
      intro hv
      have ho := below j hj hand _ hv
      rw [incidence_point_false N I D sem p] at ho
      cases ho
    · intro l
      apply Bool.eq_false_iff.mpr
      intro hv
      have ho := below j hj hand _ hv
      rw [incidence_line_false N I D sem l] at ho
      cases ho

lemma point_star (N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (C : Circuit)
    (hfan : ∀ g ∈ C.gates, g.inputs.length ≤ 2)
    (sem : ∀ z : Fin (N + N) → Bool, circuitFun (N + N) C z = true ↔
      ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true)
    (p0 : Fin N) (center : ∀ p l, I p l → p = p0) : NormalForm N I C := by
  let S := Dependency.activeLines N I
  let xs := S.toList.map (Fin.natAdd N)
  obtain ⟨D, dm, db, ds, de, below⟩ := construct (N + N) (Fin.castAdd N p0) xs
  have size : D.size ≤ C.size := ds.trans (by
    simpa [xs, S] using (Dependency.active_sides_bound N I C hfan sem).2)
  have semantics : ∀ z : Fin (N + N) → Bool, circuitFun (N + N) D z = true ↔
      ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true := by
    intro z
    rw [de, Bool.and_eq_true, List.any_eq_true]
    constructor
    · rintro ⟨hp, k, hk, hzk⟩
      obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hk
      have hl' : l ∈ Dependency.activeLines N I := Finset.mem_toList.mp hl
      obtain ⟨p, hip⟩ := (Finset.mem_filter.mp hl').2
      have hip0 : I p0 l := (center p l hip) ▸ hip
      exact ⟨p0, l, hip0, hp, hzk⟩
    · rintro ⟨p, l, hip, hp, hl⟩
      refine ⟨?_, Fin.natAdd N l, ?_, hl⟩
      · simpa only [center p l hip] using hp
      · exact List.mem_map.mpr ⟨l,
          Finset.mem_toList.mpr (Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨p, hip⟩⟩), rfl⟩
  exact complete N I C D dm db size semantics below

lemma line_star (N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (C : Circuit)
    (hfan : ∀ g ∈ C.gates, g.inputs.length ≤ 2)
    (sem : ∀ z : Fin (N + N) → Bool, circuitFun (N + N) C z = true ↔
      ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true)
    (l0 : Fin N) (center : ∀ p l, I p l → l = l0) : NormalForm N I C := by
  let S := Dependency.activePoints N I
  let xs := S.toList.map (Fin.castAdd N)
  obtain ⟨D, dm, db, ds, de, below⟩ := construct (N + N) (Fin.natAdd N l0) xs
  have size : D.size ≤ C.size := ds.trans (by
    simpa [xs, S] using (Dependency.active_sides_bound N I C hfan sem).1)
  have semantics : ∀ z : Fin (N + N) → Bool, circuitFun (N + N) D z = true ↔
      ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true := by
    intro z
    rw [de, Bool.and_eq_true, List.any_eq_true]
    constructor
    · rintro ⟨hl, k, hk, hzk⟩
      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hk
      have hp' : p ∈ Dependency.activePoints N I := Finset.mem_toList.mp hp
      obtain ⟨l, hip⟩ := (Finset.mem_filter.mp hp').2
      have hil0 : I p l0 := (center p l hip) ▸ hip
      exact ⟨p, l0, hil0, hzk, hl⟩
    · rintro ⟨p, l, hip, hp, hl⟩
      refine ⟨?_, Fin.castAdd N p, ?_, hp⟩
      · simpa only [center p l hip] using hl
      · exact List.mem_map.mpr ⟨p,
          Finset.mem_toList.mpr (Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨l, hip⟩⟩), rfl⟩
  exact complete N I C D dm db size semantics below

end Star

namespace Small

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

lemma embedding_of_card_two {α : Type} [DecidableEq α] (S : Finset α) (hs : S.card = 2) :
    ∃ e : Fin 2 ↪ α, ∀ x ∈ S, ∃ i : Fin 2, x = e i := by
  classical
  have hc : Fintype.card {x // x ∈ S} = 2 := by simpa using hs
  let e := (Fintype.equivFinOfCardEq hc).symm
  let emb : Fin 2 ↪ α := ⟨fun i => (e i).val, by
    intro i j h
    apply e.injective
    exact Subtype.ext h⟩
  refine ⟨emb, ?_⟩
  intro x hx
  refine ⟨e.symm ⟨x, hx⟩, ?_⟩
  change x = (e (e.symm ⟨x, hx⟩)).val
  rw [e.apply_symm_apply]

lemma normalize_three (N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (C : Circuit)
    (hm : Monotone2 C) (hb : NestedCover.ReadsBack (N + N) C)
    (sem : ∀ z : Fin (N + N) → Bool, circuitFun (N + N) C z = true ↔
      ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true)
    (small : C.size ≤ 3) : Star.NormalForm N I C := by
  classical
  let P := Dependency.activePoints N I
  let L := Dependency.activeLines N I
  have point_mem (p l : Fin N) (hi : I p l) : p ∈ P :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨l, hi⟩⟩
  have line_mem (p l : Fin N) (hi : I p l) : l ∈ L :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨p, hi⟩⟩
  have hfan : ∀ g ∈ C.gates, g.inputs.length ≤ 2 := fun g hg => (hm g hg).2
  by_cases hp0 : P = ∅
  · apply no_incidence N I C
    intro p l hi
    have hp := point_mem p l hi
    rw [hp0] at hp
    exact Finset.notMem_empty p hp
  by_cases hl0 : L = ∅
  · apply no_incidence N I C
    intro p l hi
    have hl := line_mem p l hi
    rw [hl0] at hl
    exact Finset.notMem_empty l hl
  by_cases hp1 : P.card = 1
  · obtain ⟨p0, hp⟩ := Finset.card_eq_one.mp hp1
    apply Star.point_star N I C hfan sem p0
    intro p l hi
    have h := point_mem p l hi
    rw [hp] at h
    exact Finset.mem_singleton.mp h
  by_cases hl1 : L.card = 1
  · obtain ⟨l0, hl⟩ := Finset.card_eq_one.mp hl1
    apply Star.line_star N I C hfan sem l0
    intro p l hi
    have h := line_mem p l hi
    rw [hl] at h
    exact Finset.mem_singleton.mp h
  have hp_pos : 0 < P.card := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hp0)
  have hl_pos : 0 < L.card := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hl0)
  have total : P.card + L.card ≤ C.size + 1 :=
    Dependency.incidence_active_bound N I C hfan sem
  have hp2 : P.card = 2 := by omega
  have hl2 : L.card = 2 := by omega
  obtain ⟨ep, coverP⟩ := embedding_of_card_two P hp2
  obtain ⟨el, coverL⟩ := embedding_of_card_two L hl2
  apply Support.normalize_supported I ep el ?_ C hm hb sem
  intro p l hi
  obtain ⟨a, ha⟩ := coverP p (point_mem p l hi)
  obtain ⟨b, hb⟩ := coverL l (line_mem p l hi)
  exact ⟨a, b, ha, hb⟩

end Small

namespace Prune

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

def zeroGate (b : Bool) (g : Gate) : Gate := if b then ⟨.or, []⟩ else g

def zeroGates (bad : ℕ → Bool) : ℕ → List Gate → List Gate
  | _, [] => []
  | j, g :: gs => zeroGate (bad j) g :: zeroGates bad (j + 1) gs

def zeroCircuit (C : Circuit) (bad : ℕ → Bool) : Circuit :=
  ⟨zeroGates bad 0 C.gates, C.output⟩

lemma zero_length (bad : ℕ → Bool) (gs : List Gate) (j : ℕ) :
    (zeroGates bad j gs).length = gs.length := by
  induction gs generalizing j with
  | nil => rfl
  | cons g gs ih => simp only [zeroGates, List.length_cons, ih]

lemma zero_getD (bad : ℕ → Bool) (gs : List Gate) (j r : ℕ) (hr : r < gs.length) :
    (zeroGates bad j gs).getD r ⟨.or, []⟩ =
      zeroGate (bad (j + r)) (gs.getD r ⟨.or, []⟩) := by
  induction gs generalizing j r with
  | nil => simp at hr
  | cons g gs ih =>
    cases r with
    | zero => simp only [zeroGates, List.getD_cons_zero, Nat.add_zero]
    | succ r =>
      simp only [List.length_cons, Nat.succ_lt_succ_iff] at hr
      simpa only [zeroGates, List.getD_cons_succ, Nat.succ_eq_add_one,
        Nat.add_assoc, Nat.add_comm 1] using ih (j + 1) r hr

lemma step_zero_le (b : Bool) (g : Gate) (w : List Bool) :
    wireLE (wireStep w (zeroGate b g)) (wireStep w g) := by
  intro i hi
  cases b with
  | false => exact hi
  | true =>
    change (w ++ [false]).getD i false = true at hi
    change (w ++ [g.op.eval (g.inputs.map fun k => w.getD k false)]).getD i false = true
    by_cases hlt : i < w.length
    · rw [List.getD_append _ _ _ _ hlt] at hi ⊢
      exact hi
    · rw [List.getD_append_right _ _ _ _ (by omega)] at hi
      have hz : ([false] : List Bool).getD (i - w.length) false = false := by
        cases i - w.length <;> rfl
      rw [hz] at hi
      cases hi

lemma zero_fold_le (bad : ℕ → Bool) (gs : List Gate)
    (hgs : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) (j : ℕ) (w : List Bool) :
    wireLE ((zeroGates bad j gs).foldl wireStep w) (gs.foldl wireStep w) := by
  induction gs generalizing j w with
  | nil => intro i hi; exact hi
  | cons g gs ih =>
    simp only [zeroGates, List.foldl_cons]
    intro i hi
    have htail := fun g' hg' => hgs g' (List.mem_cons_of_mem _ hg')
    have hz := ih htail (j + 1) (wireStep w (zeroGate (bad j) g)) i hi
    exact fold_mono gs htail _ _ (by simp [wireStep]) (step_zero_le _ _ _) i hz

lemma fold_length (gs : List Gate) (w : List Bool) :
    (gs.foldl wireStep w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [wireStep]
    omega

lemma fold_early (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl wireStep w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [List.foldl_cons, ih (wireStep w g) (by simp [wireStep]; omega)]
    exact List.getD_append _ _ _ _ hi

lemma zero_fold_eq (bad : ℕ → Bool) (gs : List Gate) (j : ℕ) (w : List Bool)
    (hz : ∀ r, r < gs.length → bad (j + r) = true →
      (gs.foldl wireStep w).getD (w.length + r) false = false) :
    (zeroGates bad j gs).foldl wireStep w = gs.foldl wireStep w := by
  induction gs generalizing j w with
  | nil => rfl
  | cons g gs ih =>
    have hs : wireStep w (zeroGate (bad j) g) = wireStep w g := by
      cases hb : bad j with
      | false => rfl
      | true =>
        have hzero := hz 0 (by simp) (by simpa using hb)
        simp only [List.foldl_cons, Nat.add_zero] at hzero
        rw [fold_early gs (wireStep w g) w.length (by simp [wireStep])] at hzero
        have hv : g.op.eval (g.inputs.map fun i => w.getD i false) = false := by
          simpa [wireStep, List.getD_eq_getElem?_getD] using hzero
        change w ++ [false] = w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
        rw [hv]
    simp only [zeroGates, List.foldl_cons, hs]
    apply ih
    intro r hr hb
    have hzero := hz (r + 1) (by simpa using Nat.succ_lt_succ hr)
      (by simpa [Nat.add_assoc, Nat.add_comm 1] using hb)
    simpa [List.foldl_cons, wireStep, Nat.add_assoc, Nat.add_comm 1] using hzero

lemma zero_monotone (C : Circuit) (bad : ℕ → Bool) (hC : Monotone2 C) :
    Monotone2 (zeroCircuit C bad) := by
  intro g hg
  have hm : ∀ gs : List Gate, (∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧
      g.inputs.length ≤ 2) → ∀ j, ∀ g ∈ zeroGates bad j gs,
        (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
    intro gs
    induction gs with
    | nil => simp [zeroGates]
    | cons g gs ih =>
      intro h j g' hg'
      simp only [zeroGates, List.mem_cons] at hg'
      rcases hg' with rfl | hg'
      · cases hb : bad j with
        | false => simpa [zeroGate] using h g List.mem_cons_self
        | true => simp [zeroGate]
      · exact ih (fun g'' hg'' => h g'' (List.mem_cons_of_mem _ hg'')) (j + 1) g' hg'
  exact hm C.gates hC 0 g hg

lemma zero_back (n : ℕ) (C : Circuit) (bad : ℕ → Bool) (hC : ReadsBack n C) :
    ReadsBack n (zeroCircuit C bad) := by
  intro j hj i hi
  have hj' : j < C.gates.length := by simpa only [zeroCircuit, zero_length] using hj
  have he : gateAt (zeroCircuit C bad) j = zeroGate (bad j) (gateAt C j) := by
    simpa only [zeroCircuit, gateAt, Nat.zero_add] using zero_getD bad C.gates 0 j hj'
  rw [he] at hi
  cases hb : bad j with
  | false => exact hC j hj' i (by simpa [zeroGate, hb] using hi)
  | true => simp [zeroGate, hb] at hi

lemma edge_active_normalization (N : ℕ) (I : Fin N → Fin N → Prop) (C : Circuit)
    (hC : Monotone2 C) (hback : ReadsBack (N + N) C)
    (hsem : ∀ z : Fin (N + N) → Bool, circuitFun (N + N) C z = true ↔
      ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) :
    ∃ D : Circuit, D.size = C.size ∧ Monotone2 D ∧ ReadsBack (N + N) D ∧
      (∀ z : Fin (N + N) → Bool, circuitFun (N + N) D z = true ↔
        ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) ∧
      (∀ j : ℕ, j < D.gates.length → (gateAt D j).op = GateOp.and →
        ∃ p l : Fin N, I p l ∧ (D.wires (List.ofFn (fun k : Fin (N + N) =>
          decide (k = Fin.castAdd N p ∨ k = Fin.natAdd N l)))).getD (N + N + j) false = true) := by
  classical
  let pair := fun p l : Fin N => fun k : Fin (N + N) =>
    decide (k = Fin.castAdd N p ∨ k = Fin.natAdd N l)
  let bad := fun j : ℕ => decide ((gateAt C j).op = GateOp.and ∧
    ∀ p l : Fin N, I p l → (C.wires (List.ofFn (pair p l))).getD (N + N + j) false = false)
  let D := zeroCircuit C bad
  have hm : Monotone2 D := zero_monotone C bad hC
  have heq : ∀ p l : Fin N, I p l → D.wires (List.ofFn (pair p l)) =
      C.wires (List.ofFn (pair p l)) := by
    intro p l hpl
    apply zero_fold_eq bad C.gates 0 (List.ofFn (pair p l))
    intro j hj hbad
    have hb := of_decide_eq_true hbad
    rw [List.length_ofFn]
    change (C.wires (List.ofFn (pair p l))).getD (N + N + j) false = false
    simpa only [Nat.zero_add] using hb.2 p l hpl
  have hsemD : ∀ z : Fin (N + N) → Bool, circuitFun (N + N) D z = true ↔
      ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true := by
    intro z
    constructor
    · intro hz
      apply (hsem z).mp
      exact zero_fold_le bad C.gates (fun g hg => (hC g hg).1) 0 (List.ofFn z) C.output hz
    · rintro ⟨p, l, hpl, hp, hl⟩
      have hold : circuitFun (N + N) C (pair p l) = true :=
        (hsem _).mpr ⟨p, l, hpl, by simp [pair], by simp [pair]⟩
      have hnew : circuitFun (N + N) D (pair p l) = true := by
        change (D.wires (List.ofFn (pair p l))).getD C.output false = true
        rw [heq p l hpl]
        exact hold
      apply wires_mono (N + N) D hm (pair p l) z _ D.output hnew
      intro k hk
      rcases of_decide_eq_true hk with rfl | rfl
      · exact hp
      · exact hl
  refine ⟨D, ?_, hm, zero_back _ C bad hback, hsemD, ?_⟩
  · exact zero_length bad C.gates 0
  · intro j hj hand
    have hj' : j < C.gates.length := by simpa only [D, zeroCircuit, zero_length] using hj
    have hgate : gateAt D j = zeroGate (bad j) (gateAt C j) := by
      simpa only [D, zeroCircuit, gateAt, Nat.zero_add] using zero_getD bad C.gates 0 j hj'
    have hb : bad j = false := by
      cases h : bad j with
      | false => rfl
      | true => simp [hgate, zeroGate, h] at hand
    have hop : (gateAt C j).op = GateOp.and := by simpa [hgate, zeroGate, hb] using hand
    by_contra hnone
    have hall : ∀ p l : Fin N, I p l →
        (C.wires (List.ofFn (pair p l))).getD (N + N + j) false = false := by
      intro p l hpl
      cases hv : (C.wires (List.ofFn (pair p l))).getD (N + N + j) false with
      | false => rfl
      | true =>
        apply False.elim
        apply hnone
        refine ⟨p, l, hpl, ?_⟩
        change (D.wires (List.ofFn (pair p l))).getD (N + N + j) false = true
        rw [heq p l hpl]
        exact hv
    have htrue : bad j = true := by exact decide_eq_true ⟨hop, hall⟩
    rw [hb] at htrue
    cases htrue

end Prune

namespace Prune

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

def andFlag : GateOp → ℕ
  | .and => 1
  | _ => 0

def ands : List Gate → ℕ
  | [] => 0
  | g :: gs => (andFlag g.op) + ands gs

lemma ands_zero_le (bad : ℕ → Bool) (gs : List Gate) (j : ℕ) :
    ands (zeroGates bad j gs) ≤ ands gs := by
  induction gs generalizing j with
  | nil => exact Nat.le_refl _
  | cons g gs ih =>
    have ht := ih (j + 1)
    cases hb : bad j with
    | false => simpa [zeroGates, ands, zeroGate, hb] using
        Nat.add_le_add_left ht (andFlag g.op)
    | true =>
      simp only [zeroGates, ands, zeroGate, hb, ite_true, andFlag, Nat.zero_add]
      omega

lemma ands_zero_lt (bad : ℕ → Bool) (gs : List Gate) (j r : ℕ)
    (hr : r < gs.length) (hb : bad (j + r) = true)
    (hop : (gs.getD r ⟨.or, []⟩).op = GateOp.and) :
    ands (zeroGates bad j gs) < ands gs := by
  induction gs generalizing j r with
  | nil => simp at hr
  | cons g gs ih =>
    cases r with
    | zero =>
      have ht := ands_zero_le bad gs (j + 1)
      simp only [Nat.add_zero] at hb
      simp only [List.getD_cons_zero] at hop
      simp only [zeroGates, ands, zeroGate, hb, ite_true, hop, andFlag, Nat.zero_add]
      omega
    | succ r =>
      have ht := ih (j + 1) r (by simpa using hr)
        (by simpa [Nat.add_assoc, Nat.add_comm 1] using hb)
        (by simpa only [List.getD_cons_succ] using hop)
      cases hb0 : bad j with
      | false => simpa [zeroGates, ands, zeroGate, hb0] using
          Nat.add_lt_add_left ht (andFlag g.op)
      | true =>
        simp only [zeroGates, ands, zeroGate, hb0, ite_true, andFlag, Nat.zero_add]
        omega

lemma edge_sensitive_normalization (N : ℕ) (I : Fin N → Fin N → Prop) (C : Circuit)
    (hC : Monotone2 C) (hback : ReadsBack (N + N) C)
    (hsem : ∀ z : Fin (N + N) → Bool, circuitFun (N + N) C z = true ↔
      ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) :
    ∃ D : Circuit, D.size ≤ C.size ∧ Monotone2 D ∧ ReadsBack (N + N) D ∧
      (∀ z : Fin (N + N) → Bool, circuitFun (N + N) D z = true ↔
        ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) ∧
      (∀ E : Circuit, Monotone2 E → ReadsBack (N + N) E →
        (∀ z : Fin (N + N) → Bool, circuitFun (N + N) E z = true ↔
          ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) →
        D.size ≤ E.size) ∧
      (∀ j : ℕ, j < D.gates.length → (gateAt D j).op = GateOp.and →
        ∃ p l : Fin N, I p l ∧ circuitFun (N + N)
          (zeroCircuit D (fun k => decide (k = j)))
          (fun k => decide (k = Fin.castAdd N p ∨ k = Fin.natAdd N l)) = false) := by
  classical
  let Model := fun D : Circuit => Monotone2 D ∧ ReadsBack (N + N) D ∧
    (∀ z : Fin (N + N) → Bool, circuitFun (N + N) D z = true ↔
      ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true)
  have hsizeEx : ∃ k : ℕ, ∃ D : Circuit, Model D ∧ D.size = k :=
    ⟨C.size, C, ⟨hC, hback, hsem⟩, rfl⟩
  let sz := Nat.find hsizeEx
  let Good := fun D : Circuit => D.size = sz ∧ Model D
  obtain ⟨B, hB, hBsize⟩ := Nat.find_spec hsizeEx
  have hex : ∃ k : ℕ, ∃ D : Circuit, Good D ∧ ands D.gates = k :=
    ⟨ands B.gates, B, ⟨hBsize, hB⟩, rfl⟩
  obtain ⟨D, hD, hmin⟩ := Nat.find_spec hex
  obtain ⟨hsizeEq, hmono, hread, hfun⟩ := hD
  have hglobalmin : ∀ E : Circuit, Model E → D.size ≤ E.size := by
    intro E hE
    exact hsizeEq.trans_le (Nat.find_min' hsizeEx ⟨E, hE, rfl⟩)
  have hsize : D.size ≤ C.size := hglobalmin C ⟨hC, hback, hsem⟩
  refine ⟨D, hsize, hmono, hread, hfun,
    (fun E hm hr hf => hglobalmin E ⟨hm, hr, hf⟩), ?_⟩
  intro j hj hand
  by_contra hnone
  let bad := fun k : ℕ => decide (k = j)
  let E := zeroCircuit D bad
  have hEmono : Monotone2 E := zero_monotone D bad hmono
  have hedge : ∀ p l : Fin N, I p l → circuitFun (N + N) E
      (fun k => decide (k = Fin.castAdd N p ∨ k = Fin.natAdd N l)) = true := by
    intro p l hpl
    cases hv : circuitFun (N + N) E
        (fun k => decide (k = Fin.castAdd N p ∨ k = Fin.natAdd N l)) with
    | false => exact (hnone ⟨p, l, hpl, hv⟩).elim
    | true => rfl
  have hEfun : ∀ z : Fin (N + N) → Bool, circuitFun (N + N) E z = true ↔
      ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true := by
    intro z
    constructor
    · intro hz
      apply (hfun z).mp
      exact zero_fold_le bad D.gates (fun g hg => (hmono g hg).1) 0 (List.ofFn z) D.output hz
    · rintro ⟨p, l, hpl, hp, hl⟩
      apply wires_mono (N + N) E hEmono
        (fun k => decide (k = Fin.castAdd N p ∨ k = Fin.natAdd N l)) z _ E.output (hedge p l hpl)
      intro k hk
      rcases of_decide_eq_true hk with rfl | rfl
      · exact hp
      · exact hl
  have hEgood : Good E := by
    refine ⟨?_, hEmono, zero_back _ D bad hread, hEfun⟩
    exact (zero_length bad D.gates 0).trans hsizeEq
  have hlo : Nat.find hex ≤ ands E.gates := Nat.find_min' hex ⟨E, hEgood, rfl⟩
  have hlt : ands E.gates < ands D.gates :=
    ands_zero_lt bad D.gates 0 j hj (by simp [bad]) hand
  omega

end Prune

end PEqualNP.Outside.L_meta_3451_aux
