import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Tactic.Choose
import Mathlib.Algebra.BigOperators.Group.Finset.Pi
import PEqualNP.Defs
import Mathlib.Algebra.Field.Rat
import Mathlib.Data.Fintype.Sum
import Mathlib.LinearAlgebra.Dimension.Constructions

namespace PEqualNP.Outside.L_meta_1890.ReadTwice

private theorem cover531_splitUnique {m n : ℕ} {P : Fin (m + n) → Prop}
    (h : ((∃! i : Fin m, P (Fin.castAdd n i)) ∧ (∀ j : Fin n, ¬ P (Fin.natAdd m j))) ∨
      ((∀ i : Fin m, ¬ P (Fin.castAdd n i)) ∧ (∃! j : Fin n, P (Fin.natAdd m j)))) :
    ∃! i, P i := by
  rcases h with ⟨⟨i, hi, hunique⟩, hnone⟩ | ⟨hnone, ⟨j, hj, hunique⟩⟩
  · refine ⟨Fin.castAdd n i, hi, ?_⟩
    intro k
    refine Fin.addCases (motive := fun k => P k → k = Fin.castAdd n i) ?_ ?_ k
    · intro k hk
      exact congrArg (Fin.castAdd n) (hunique k hk)
    · intro k hk
      exact (hnone k hk).elim
  · refine ⟨Fin.natAdd m j, hj, ?_⟩
    intro k
    refine Fin.addCases (motive := fun k => P k → k = Fin.natAdd m j) ?_ ?_ k
    · intro k hk
      exact (hnone k hk).elim
    · intro k hk
      exact congrArg (Fin.natAdd m) (hunique k hk)

private theorem cover531_formulaRectanglesStrong {n : ℕ}
    (φ : PEqualNP.MetaComplexity.DMFormula n)
    (mono : PEqualNP.MetaComplexity.DMFormula.rec
      (motive := fun _ : PEqualNP.MetaComplexity.DMFormula n => Prop)
      (fun (_ : Fin n) (c : Bool) => c = true) (fun _ _ p q => p ∧ q) (fun _ _ p q => p ∧ q) φ) :
    ∃ (X Y : Fin φ.leaves → (Fin n → Bool) → Prop) (label : Fin φ.leaves → Fin n),
      (∀ x y, φ.eval x = true → φ.eval y = false → ∃! i, X i x ∧ Y i y) ∧
        (∀ i x, X i x → φ.eval x = true ∧ x (label i) = true) ∧
        (∀ i y, Y i y → φ.eval y = false ∧ y (label i) = false) := by
  induction φ with
  | lit v c =>
      change c = true at mono
      subst c
      refine ⟨fun _ x => x v = true, fun _ y => y v = false, fun _ => v, ?_, ?_, ?_⟩
      · intro x y hx hy
        change ∃! _i : Fin 1, x v = true ∧ y v = false
        exact ⟨0, ⟨by simpa [PEqualNP.MetaComplexity.DMFormula.eval] using hx,
          by simpa [PEqualNP.MetaComplexity.DMFormula.eval] using hy⟩,
          fun i _ => Subsingleton.elim i 0⟩
      · intro i x hx
        exact ⟨by simpa [PEqualNP.MetaComplexity.DMFormula.eval] using hx, hx⟩
      · intro i y hy
        exact ⟨by simpa [PEqualNP.MetaComplexity.DMFormula.eval] using hy, hy⟩
  | and a b ihA ihB =>
      obtain ⟨XA, YA, LA, totalA, xA, yA⟩ := ihA mono.1
      obtain ⟨XB, YB, LB, totalB, xB, yB⟩ := ihB mono.2
      let X : Fin (a.leaves + b.leaves) → (Fin n → Bool) → Prop :=
        Fin.addCases (fun i x => XA i x ∧ b.eval x = true) (fun i x => XB i x ∧ a.eval x = true)
      let Y : Fin (a.leaves + b.leaves) → (Fin n → Bool) → Prop :=
        Fin.addCases YA (fun i y => YB i y ∧ a.eval y = true)
      let label : Fin (a.leaves + b.leaves) → Fin n := Fin.addCases LA LB
      refine ⟨X, Y, label, ?_, ?_, ?_⟩
      · intro x y hx hy
        have hx' : a.eval x = true ∧ b.eval x = true := by
          simpa only [PEqualNP.MetaComplexity.DMFormula.eval, Bool.and_eq_true_iff] using hx
        apply cover531_splitUnique
        cases ha : a.eval y with
        | false =>
            left
            constructor
            · simpa [X, Y, hx'.2] using totalA x y hx'.1 ha
            · intro i
              simp [X, Y, ha, Fin.addCases_right]
        | true =>
            right
            have hb : b.eval y = false := by
              simpa [PEqualNP.MetaComplexity.DMFormula.eval, ha] using hy
            constructor
            · intro i hi
              have hLeft : YA i y := by simpa [Y] using hi.2
              have hFalse := (yA i y hLeft).1
              simp [ha] at hFalse
            · simpa [X, Y, hx'.1, ha, Fin.addCases_right] using totalB x y hx'.2 hb
      · intro i
        induction i using Fin.addCases with
        | left i =>
            intro x hx
            have h : XA i x ∧ b.eval x = true := by simpa [X] using hx
            obtain ⟨ha, hv⟩ := xA i x h.1
            exact ⟨by simp [PEqualNP.MetaComplexity.DMFormula.eval, ha, h.2],
              by simpa [label] using hv⟩
        | right i =>
            intro x hx
            have h : XB i x ∧ a.eval x = true := by simpa [X, Fin.addCases_right] using hx
            obtain ⟨hb, hv⟩ := xB i x h.1
            exact ⟨by simp [PEqualNP.MetaComplexity.DMFormula.eval, hb, h.2],
              by simpa [label, Fin.addCases_right] using hv⟩
      · intro i
        induction i using Fin.addCases with
        | left i =>
            intro y hy
            have h : YA i y := by simpa [Y] using hy
            obtain ⟨ha, hv⟩ := yA i y h
            exact ⟨by simp [PEqualNP.MetaComplexity.DMFormula.eval, ha],
              by simpa [label] using hv⟩
        | right i =>
            intro y hy
            have h : YB i y ∧ a.eval y = true := by simpa [Y, Fin.addCases_right] using hy
            obtain ⟨hb, hv⟩ := yB i y h.1
            exact ⟨by simp [PEqualNP.MetaComplexity.DMFormula.eval, hb],
              by simpa [label, Fin.addCases_right] using hv⟩
  | or a b ihA ihB =>
      obtain ⟨XA, YA, LA, totalA, xA, yA⟩ := ihA mono.1
      obtain ⟨XB, YB, LB, totalB, xB, yB⟩ := ihB mono.2
      let X : Fin (a.leaves + b.leaves) → (Fin n → Bool) → Prop :=
        Fin.addCases XA (fun i x => XB i x ∧ a.eval x = false)
      let Y : Fin (a.leaves + b.leaves) → (Fin n → Bool) → Prop :=
        Fin.addCases (fun i y => YA i y ∧ b.eval y = false) (fun i y => YB i y ∧ a.eval y = false)
      let label : Fin (a.leaves + b.leaves) → Fin n := Fin.addCases LA LB
      refine ⟨X, Y, label, ?_, ?_, ?_⟩
      · intro x y hx hy
        have hy' : a.eval y = false ∧ b.eval y = false := by
          simpa only [PEqualNP.MetaComplexity.DMFormula.eval, Bool.or_eq_false_iff] using hy
        apply cover531_splitUnique
        cases ha : a.eval x with
        | false =>
            right
            have hb : b.eval x = true := by
              simpa [PEqualNP.MetaComplexity.DMFormula.eval, ha] using hx
            constructor
            · intro i hi
              have hLeft : XA i x := by simpa [X] using hi.1
              have hTrue := (xA i x hLeft).1
              simp [ha] at hTrue
            · simpa [X, Y, hy'.1, ha, Fin.addCases_right] using totalB x y hb hy'.2
        | true =>
            left
            constructor
            · simpa [X, Y, hy'.2] using totalA x y ha hy'.1
            · intro i
              simp [X, Y, ha, Fin.addCases_right]
      · intro i
        induction i using Fin.addCases with
        | left i =>
            intro x hx
            have h : XA i x := by simpa [X] using hx
            obtain ⟨ha, hv⟩ := xA i x h
            exact ⟨by simp [PEqualNP.MetaComplexity.DMFormula.eval, ha],
              by simpa [label] using hv⟩
        | right i =>
            intro x hx
            have h : XB i x ∧ a.eval x = false := by simpa [X, Fin.addCases_right] using hx
            obtain ⟨hb, hv⟩ := xB i x h.1
            exact ⟨by simp [PEqualNP.MetaComplexity.DMFormula.eval, hb],
              by simpa [label, Fin.addCases_right] using hv⟩
      · intro i
        induction i using Fin.addCases with
        | left i =>
            intro y hy
            have h : YA i y ∧ b.eval y = false := by simpa [Y] using hy
            obtain ⟨ha, hv⟩ := yA i y h.1
            exact ⟨by simp [PEqualNP.MetaComplexity.DMFormula.eval, ha, h.2],
              by simpa [label] using hv⟩
        | right i =>
            intro y hy
            have h : YB i y ∧ a.eval y = false := by simpa [Y, Fin.addCases_right] using hy
            obtain ⟨hb, hv⟩ := yB i y h.1
            exact ⟨by simp [PEqualNP.MetaComplexity.DMFormula.eval, hb, h.2],
              by simpa [label, Fin.addCases_right] using hv⟩

private theorem cover531_formulaRectangles {n : ℕ} (φ : PEqualNP.MetaComplexity.DMFormula n)
    (mono : PEqualNP.MetaComplexity.DMFormula.rec
      (motive := fun _ : PEqualNP.MetaComplexity.DMFormula n => Prop)
      (fun (_ : Fin n) (c : Bool) => c = true) (fun _ _ p q => p ∧ q) (fun _ _ p q => p ∧ q) φ) :
    ∃ (X Y : Fin φ.leaves → (Fin n → Bool) → Prop) (label : Fin φ.leaves → Fin n),
      (∀ x y, φ.eval x = true → φ.eval y = false → ∃! i, X i x ∧ Y i y) ∧
        (∀ i x y, φ.eval x = true → φ.eval y = false → X i x → Y i y →
          x (label i) = true ∧ y (label i) = false) := by
  obtain ⟨X, Y, label, total, goodX, goodY⟩ := cover531_formulaRectanglesStrong φ mono
  exact ⟨X, Y, label, total, fun i x y _ _ hx hy => ⟨(goodX i x hx).2, (goodY i y hy).2⟩⟩

private lemma cover531_starIndependent {n : ℕ} (G : SimpleGraph (Fin n))
    (triangle : ∀ a b c : Fin n, ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c a))
    (v : Fin n) : ∀ u w, G.Adj u w → ¬ (G.Adj v u ∧ G.Adj v w) := by
  intro u w huw h
  exact triangle v u w ⟨h.1, huw, h.2.symm⟩

private lemma cover531_pairIndependent {n : ℕ} (G : SimpleGraph (Fin n))
    (triangle : ∀ a b c : Fin n, ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c a))
    (square : ∀ a b c d : Fin n, a ≠ c → b ≠ d →
      ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a))
    (a b : Fin n) (edge : G.Adj a b) : ∀ u w, G.Adj u w →
      ¬ (((G.Adj a u ∨ G.Adj b u) ∧ u ≠ a ∧ u ≠ b) ∧
         ((G.Adj a w ∨ G.Adj b w) ∧ w ≠ a ∧ w ≠ b)) := by
  intro u w huw h
  rcases h with ⟨⟨hu, hua, hub⟩, ⟨hw, hwa, hwb⟩⟩
  rcases hu with hau | hbu <;> rcases hw with haw | hbw
  · exact triangle a u w ⟨hau, huw, haw.symm⟩
  · exact square a u w b hwa.symm hub ⟨hau, huw, hbw.symm, edge.symm⟩
  · exact square b u w a hwb.symm hua ⟨hbu, huw, haw.symm, edge⟩
  · exact triangle b u w ⟨hbu, huw, hbw.symm⟩

private theorem cover531_rank {V E : Type} [Fintype V] [DecidableEq V] [Fintype E]
    [DecidableEq E] {m : ℕ} (a b reject : E → V) (T : Finset V) (R : Fin m → (V × E → ℚ))
    (anchor : ∀ v ∈ T, ∃ e, v ≠ reject e ∧ (a e = v ∨ b e = v))
    (units : ∀ e, Pi.single (reject e, e) 1 ∈ Submodule.span ℚ (Set.range R))
    (stars : ∀ v ∈ T, (fun p : V × E => if p.1 = v ∧ (a p.2 = v ∨ b p.2 = v)
      then 1 else 0) ∈ Submodule.span ℚ (Set.range R)) :
    Fintype.card E + T.card ≤ m := by
  classical
  let unit (e : E) : V × E → ℚ := Pi.single (reject e, e) 1
  let star (v : V) : V × E → ℚ :=
    fun p => if p.1 = v ∧ (a p.2 = v ∨ b p.2 = v) then 1 else 0
  let family : E ⊕ ↥T → (V × E → ℚ) := Sum.elim unit (fun v => star v.val)
  let W := Submodule.span ℚ (Set.range R)
  have inSpan (i : E ⊕ ↥T) : family i ∈ W := by
    cases i with
    | inl e => exact units e
    | inr v => exact stars v.val v.property
  have independent : LinearIndependent ℚ family := by
    rw [Fintype.linearIndependent_iff]
    intro c relation
    have atCoord (p : V × E) :
        (Finset.univ.sum fun e : E => c (Sum.inl e) * unit e p) +
          (Finset.univ.sum fun v : ↥T => c (Sum.inr v) * star v.val p) = 0 := by
      simpa [Fintype.sum_sum_type, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, family] using
        congrFun relation p
    have starZero (v : ↥T) : c (Sum.inr v) = 0 := by
      obtain ⟨e, different, incident⟩ := anchor v.val v.property
      have unitSum : (Finset.univ.sum fun j : E => c (Sum.inl j) * unit j (v.val, e)) = 0 := by
        apply Finset.sum_eq_zero
        intro j _
        have h : (v.val, e) ≠ (reject j, j) := by
          intro same
          have ej : e = j := congrArg Prod.snd same
          subst j
          exact different (congrArg Prod.fst same)
        simp [unit, Pi.single_eq_of_ne h]
      have starSum : (Finset.univ.sum fun w : ↥T => c (Sum.inr w) * star w.val (v.val, e)) =
          c (Sum.inr v) := by
        rw [Finset.sum_eq_single_of_mem v (Finset.mem_univ v)]
        · simp [star, incident]
        · intro w _ differentSub
          have h : v.val ≠ w.val := fun same => differentSub (Subtype.ext same.symm)
          simp [star, h]
      simpa only [unitSum, starSum, zero_add] using atCoord (v.val, e)
    intro i
    cases i with
    | inr v => exact starZero v
    | inl e =>
      have starSum : (Finset.univ.sum fun v : ↥T => c (Sum.inr v) * star v.val (reject e, e)) = 0 := by
        apply Finset.sum_eq_zero
        intro v _
        simp [starZero v]
      have unitSum : (Finset.univ.sum fun j : E => c (Sum.inl j) * unit j (reject e, e)) = c (Sum.inl e) := by
        rw [Finset.sum_eq_single_of_mem e (Finset.mem_univ e)]
        · simp [unit]
        · intro j _ different
          have h : (reject e, e) ≠ (reject j, j) := fun same =>
            different (congrArg Prod.snd same).symm
          simp [unit, Pi.single_eq_of_ne h]
      simpa only [unitSum, starSum, add_zero] using atCoord (reject e, e)
  have : Module.Finite ℚ ↥W := Module.Finite.span_of_finite ℚ (Set.finite_range R)
  let lifted (i : E ⊕ ↥T) : ↥W := ⟨family i, inSpan i⟩
  have liftedIndependent : LinearIndependent ℚ lifted := by
    apply LinearIndependent.of_comp W.subtype
    change LinearIndependent ℚ family
    exact independent
  have lower : Fintype.card E + T.card ≤ Module.finrank ℚ ↥W := by
    simpa only [Fintype.card_sum, Fintype.card_coe] using liftedIndependent.fintype_card_le_finrank
  have upper : Module.finrank ℚ W ≤ m := by
    change Module.finrank ℚ (Submodule.span ℚ (Set.range R)) ≤ m
    refine (finrank_span_le_card (Set.range R)).trans ?_
    rw [Set.toFinset_card]
    simpa only [Fintype.card_fin] using Fintype.card_range_le R
  exact lower.trans upper

set_option maxHeartbeats 1000000 in
lemma cover_formula : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], (∀ a b c : Fin n, ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c a)) → (∀ a b c d : Fin n, a ≠ c → b ≠ d → ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a)) → ∀ φ : PEqualNP.MetaComplexity.DMFormula n, PEqualNP.MetaComplexity.DMFormula.rec (motive := fun _ : PEqualNP.MetaComplexity.DMFormula n => Prop) (fun (_ : Fin n) (c : Bool) => c = true) (fun _ _ p q => p ∧ q) (fun _ _ p q => p ∧ q) φ → (∀ x : Fin n → Bool, φ.eval x = decide (∃ i j : Fin n, G.Adj i j ∧ x i = true ∧ x j = true)) → ∃ T : Finset (Fin n), (∀ u w : Fin n, G.Adj u w → u ∈ T ∨ w ∈ T) ∧ G.edgeFinset.card + T.card ≤ φ.leaves := by
  intro n G _ triangle square φ monotone evaluates
  classical
  obtain ⟨X, Y, label, partitions, labels⟩ := cover531_formulaRectangles φ monotone
  let E := {e : Sym2 (Fin n) // e ∈ G.edgeFinset}
  have endpoints (e : E) : ∃ u v : Fin n, G.Adj u v ∧ Sym2.mk u v = e.val := by
    have member : e.val ∈ G.edgeSet := SimpleGraph.mem_edgeFinset.mp e.property
    revert member
    refine Sym2.inductionOn e.val ?_
    intro u v member
    exact ⟨u, v, member, rfl⟩
  choose a b adjacent represented using endpoints
  let row (e : E) (v : Fin n) : Bool := decide (v = a e ∨ v = b e)
  let starColumn (v w : Fin n) : Bool := decide (G.Adj v w)
  let edgeColumn (e : E) (w : Fin n) : Bool :=
    decide ((G.Adj (a e) w ∨ G.Adj (b e) w) ∧ w ≠ a e ∧ w ≠ b e)
  have rowPositive (e : E) : φ.eval (row e) = true := by
    rw [evaluates]
    exact decide_eq_true ⟨a e, b e, adjacent e, by simp [row], by simp [row]⟩
  have starNegative (v : Fin n) : φ.eval (starColumn v) = false := by
    rw [evaluates]
    apply decide_eq_false
    rintro ⟨u, w, edge, hu, hw⟩
    exact cover531_starIndependent G triangle v u w edge
      ⟨of_decide_eq_true hu, of_decide_eq_true hw⟩
  have edgeNegative (e : E) : φ.eval (edgeColumn e) = false := by
    rw [evaluates]
    apply decide_eq_false
    rintro ⟨u, w, edge, hu, hw⟩
    exact cover531_pairIndependent G triangle square (a e) (b e) (adjacent e) u w edge
      ⟨of_decide_eq_true hu, of_decide_eq_true hw⟩
  let route (e : E) (y : Fin n → Bool) (hy : φ.eval y = false) : Fin φ.leaves :=
    Classical.choose (partitions (row e) y (rowPositive e) hy)
  have routeMem (e : E) (y : Fin n → Bool) (hy : φ.eval y = false) :
      X (route e y hy) (row e) ∧ Y (route e y hy) y :=
    (Classical.choose_spec (partitions (row e) y (rowPositive e) hy)).1
  have routeUnique (e : E) (y : Fin n → Bool) (hy : φ.eval y = false)
      (i : Fin φ.leaves) (hi : X i (row e) ∧ Y i y) : i = route e y hy :=
    (Classical.choose_spec (partitions (row e) y (rowPositive e) hy)).2 i hi
  let selected (e : E) (y : Fin n → Bool) (hy : φ.eval y = false) := label (route e y hy)
  have labelProperties (e : E) (y : Fin n → Bool) (hy : φ.eval y = false) :
      (selected e y hy = a e ∨ selected e y hy = b e) ∧ y (selected e y hy) = false := by
    have result := labels (route e y hy) (row e) y (rowPositive e) hy
      (routeMem e y hy).1 (routeMem e y hy).2
    exact ⟨of_decide_eq_true result.1, result.2⟩
  have leftSelected (e : E) (y : Fin n → Bool) (hy : φ.eval y = false)
      (opposite : y (b e) = true) : selected e y hy = a e := by
    rcases labelProperties e y hy with ⟨chosen | chosen, missing⟩
    · exact chosen
    · simp [chosen, opposite] at missing
  have rightSelected (e : E) (y : Fin n → Bool) (hy : φ.eval y = false)
      (opposite : y (a e) = true) : selected e y hy = b e := by
    rcases labelProperties e y hy with ⟨chosen | chosen, missing⟩
    · simp [chosen, opposite] at missing
    · exact chosen
  let chosen (e : E) := selected e (edgeColumn e) (edgeNegative e)
  let reject (e : E) := if chosen e = a e then b e else a e
  have chosenEnd (e : E) : chosen e = a e ∨ chosen e = b e :=
    (labelProperties e (edgeColumn e) (edgeNegative e)).1
  have rejectEnd (e : E) : a e = reject e ∨ b e = reject e := by
    dsimp only [reject]
    split <;> simp
  have differentEnd (e : E) : chosen e ≠ reject e := by
    have distinct := (adjacent e).ne
    rcases chosenEnd e with left | right
    · simp [reject, left, distinct]
    · simp [reject, right, distinct.symm]
  let R (i : Fin φ.leaves) (p : Fin n × E) : ℚ :=
    if p.1 = label i ∧ X i (row p.2) then 1 else 0
  let col (v : Fin n) (y : Fin n → Bool) : Fin n × E → ℚ :=
    Finset.univ.sum fun i : Fin φ.leaves => if Y i y ∧ label i = v then R i else 0
  let span := Submodule.span ℚ (Set.range R)
  have colInSpan (v : Fin n) (y : Fin n → Bool) : col v y ∈ span := by
    apply Submodule.sum_mem
    intro i _
    split
    · exact Submodule.subset_span ⟨i, rfl⟩
    · exact span.zero_mem
  have colValue (v : Fin n) (y : Fin n → Bool) (hy : φ.eval y = false) (p : Fin n × E) :
      col v y p = if p.1 = v ∧ selected p.2 y hy = v then 1 else 0 := by
    simp only [col, Finset.sum_apply]
    rw [Finset.sum_eq_single (route p.2 y hy)]
    · by_cases same : label (route p.2 y hy) = v
      · simp [R, selected, same, (routeMem p.2 y hy).1, (routeMem p.2 y hy).2]
      · simp [selected, same]
    · intro i _ other
      by_cases inColumn : Y i y ∧ label i = v
      · have noRow : ¬ X i (row p.2) := fun hx => other (routeUnique p.2 y hy i ⟨hx, inColumn.1⟩)
        simp [inColumn, R, noRow]
      · simp [inColumn]
    · simp
  have columnOpposite (e : E) (v w : Fin n) (hv : a e = v ∨ b e = v)
      (edge : G.Adj v w) (other : Sym2.mk v w ≠ e.val) : edgeColumn e w = true := by
    rcases hv with rfl | rfl
    · have notLeft : w ≠ a e := edge.ne.symm
      have notRight : w ≠ b e := by
        intro equal
        apply other
        rw [equal]
        exact represented e
      exact decide_eq_true ⟨Or.inl edge, notLeft, notRight⟩
    · have notRight : w ≠ b e := edge.ne.symm
      have notLeft : w ≠ a e := by
        intro equal
        apply other
        rw [equal]
        exact Sym2.eq_swap.trans (represented e)
      exact decide_eq_true ⟨Or.inr edge, notLeft, notRight⟩
  have starSelected (v : Fin n) (e : E) :
      selected e (starColumn v) (starNegative v) = v ↔ a e = v ∨ b e = v := by
    constructor
    · intro equals
      simpa [equals, eq_comm] using (labelProperties e (starColumn v) (starNegative v)).1
    · rintro (rfl | rfl)
      · exact leftSelected e (starColumn (a e)) (starNegative (a e)) (decide_eq_true (adjacent e))
      · exact rightSelected e (starColumn (b e)) (starNegative (b e)) (decide_eq_true (adjacent e).symm)
  have otherSelected (e e' : E) (different : e' ≠ e) (v : Fin n) (hv : a e = v ∨ b e = v) :
      selected e' (edgeColumn e) (edgeNegative e) = v ↔ a e' = v ∨ b e' = v := by
    have diffRep : e'.val ≠ e.val := fun equals => different (Subtype.ext equals)
    constructor
    · intro equals
      simpa [equals, eq_comm] using (labelProperties e' (edgeColumn e) (edgeNegative e)).1
    · rintro (rfl | rfl)
      · exact leftSelected e' (edgeColumn e) (edgeNegative e)
          (columnOpposite e _ _ hv (adjacent e') (by simpa [represented e'] using diffRep))
      · have notReversed : Sym2.mk (b e') (a e') ≠ e.val := by
          rw [Sym2.eq_swap, represented e']
          exact diffRep
        exact rightSelected e' (edgeColumn e) (edgeNegative e)
          (columnOpposite e _ _ hv (adjacent e').symm notReversed)
  let T : Finset (Fin n) := Finset.univ.image chosen
  have starInSpan (v : Fin n) :
      (fun p : Fin n × E => if p.1 = v ∧ (a p.2 = v ∨ b p.2 = v) then 1 else 0) ∈ span := by
    have equals : col v (starColumn v) =
        (fun p : Fin n × E => if p.1 = v ∧ (a p.2 = v ∨ b p.2 = v) then 1 else 0) := by
      funext p
      simp only [colValue v _ (starNegative v), starSelected]
    rw [← equals]
    exact colInSpan v (starColumn v)
  have units (e : E) : Pi.single (reject e, e) (1 : ℚ) ∈ span := by
    let v := reject e
    have equals : col v (starColumn v) - col v (edgeColumn e) = Pi.single (v, e) (1 : ℚ) := by
      funext p
      rcases p with ⟨w, e'⟩
      change col v (starColumn v) (w, e') - col v (edgeColumn e) (w, e') = (Pi.single (v, e) 1 : Fin n × E → ℚ) (w, e')
      simp only [colValue v _ (starNegative v), colValue v _ (edgeNegative e), starSelected]
      by_cases first : w = v
      · subst w
        by_cases second : e' = e
        · subst e'
          have miss : selected e (edgeColumn e) (edgeNegative e) ≠ v := differentEnd e
          simp [rejectEnd e, miss, v]
        · simp only [otherSelected e e' second v (rejectEnd e)]
          simp [second]
      · simp [first]
    rw [← equals]
    exact span.sub_mem (colInSpan v (starColumn v)) (colInSpan v (edgeColumn e))
  have anchor : ∀ v ∈ T, ∃ e, v ≠ reject e ∧ (a e = v ∨ b e = v) := by
    intro v hv
    obtain ⟨e, _, rfl⟩ := Finset.mem_image.mp hv
    rcases chosenEnd e with first | second
    · exact ⟨e, differentEnd e, Or.inl first.symm⟩
    · exact ⟨e, differentEnd e, Or.inr second.symm⟩
  refine ⟨T, ?_, ?_⟩
  · intro u w edge
    let e : E := ⟨Sym2.mk u w, SimpleGraph.mem_edgeFinset.mpr edge⟩
    have inCover : chosen e ∈ T := Finset.mem_image_of_mem chosen (Finset.mem_univ e)
    have pair : Sym2.mk (a e) (b e) = Sym2.mk u w := represented e
    rcases Sym2.eq_iff.mp pair with ⟨left, right⟩ | ⟨left, right⟩
    · rcases chosenEnd e with first | second
      · exact Or.inl ((first.trans left) ▸ inCover)
      · exact Or.inr ((second.trans right) ▸ inCover)
    · rcases chosenEnd e with first | second
      · exact Or.inr ((first.trans left) ▸ inCover)
      · exact Or.inl ((second.trans right) ▸ inCover)
  · have bound := cover531_rank a b reject T R anchor units (fun v _ => starInSpan v)
    have count : Fintype.card E = G.edgeFinset.card := Fintype.card_coe _
    rwa [count] at bound

def pairs : List (Fin 10 × Fin 10) :=
  [(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(4,9),
   (5,7),(7,9),(9,6),(6,8),(8,5)]

abbrev graph : SimpleGraph (Fin 10) :=
  SimpleGraph.fromRel (fun u v => (u,v) ∈ pairs)

def edge (x : Fin 10 → Bool) : Bool :=
  x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
  x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 4 && x 9 ||
  x 5 && x 7 || x 7 && x 9 || x 9 && x 6 || x 6 && x 8 || x 8 && x 5

set_option maxRecDepth 20000 in
set_option maxHeartbeats 10000000 in
set_option synthInstance.maxSize 100000 in
lemma no_triangle : ∀ a b c : Fin 10, ¬ (graph.Adj a b ∧ graph.Adj b c ∧ graph.Adj c a) := by
  simp only [graph, SimpleGraph.fromRel_adj]
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 10000000 in
set_option synthInstance.maxSize 100000 in
lemma no_square : ∀ a b c d : Fin 10, a ≠ c → b ≠ d →
    ¬ (graph.Adj a b ∧ graph.Adj b c ∧ graph.Adj c d ∧ graph.Adj d a) := by
  simp only [graph, SimpleGraph.fromRel_adj]
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 10000000 in
lemma edge_count : graph.edgeFinset.card = 15 := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 10000000 in
lemma cover_bound : ∀ T : Finset (Fin 10),
    (∀ u w : Fin 10, graph.Adj u w → u ∈ T ∨ w ∈ T) → 6 ≤ T.card := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 10000000 in
lemma edge_eq (x : Fin 10 → Bool) : edge x =
    decide (∃ i j : Fin 10, graph.Adj i j ∧ x i = true ∧ x j = true) := by
  revert x
  decide +kernel

lemma positive_formula_lower (φ : PEqualNP.MetaComplexity.DMFormula 10)
    (positive : PEqualNP.MetaComplexity.DMFormula.rec
      (motive := fun _ : PEqualNP.MetaComplexity.DMFormula 10 => Prop)
      (fun (_ : Fin 10) (c : Bool) => c = true)
      (fun _ _ p q => p ∧ q) (fun _ _ p q => p ∧ q) φ)
    (computes : ∀ x : Fin 10 → Bool, φ.eval x = edge x) :
    21 ≤ φ.leaves := by
  obtain ⟨T, hc, hb⟩ := cover_formula 10 graph no_triangle no_square φ positive
    (fun x => (computes x).trans (edge_eq x))
  have ht := cover_bound T hc
  rw [edge_count] at hb
  omega

namespace Unfold

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

noncomputable def degree {n : ℕ} (i : Fin n) (F : DMFormula n) : ℕ :=
  DMFormula.rec (motive := fun _ => ℕ) (fun j _ => if j = i then 1 else 0)
    (fun _ _ a b => a + b) (fun _ _ a b => max a b) F

noncomputable def positive {n : ℕ} (F : DMFormula n) : Bool :=
  DMFormula.rec (motive := fun _ => Bool) (fun _ b => b)
    (fun _ _ a b => a && b) (fun _ _ a b => a && b) F

def shaped (n : ℕ) (gs : List Gate) : Prop :=
  ∀ j g, gs[j]? = some g →
    (g.op = GateOp.and ∨ g.op = GateOp.or) ∧
    ∃ a b, g.inputs = [a,b] ∧ a ≠ b ∧ a < n+j ∧ b < n+j

def leafAt {n : ℕ} (T : List (DMFormula n)) (i : ℕ) : ℕ :=
  (T[i]?.map DMFormula.leaves).getD 0

def leafSum {n : ℕ} (T : List (DMFormula n)) (R : List ℕ) : ℕ :=
  (R.map (leafAt T)).sum

lemma leafSum_append {n : ℕ} (T : List (DMFormula n)) (R S : List ℕ) :
    leafSum T (R ++ S) = leafSum T R + leafSum T S := by
  simp [leafSum]

lemma leafSum_old {n : ℕ} (T : List (DMFormula n)) (F : DMFormula n)
    (R : List ℕ) (h : ∀ i ∈ R, i < T.length) :
    leafSum (T ++ [F]) R = leafSum T R := by
  unfold leafSum
  congr 1
  apply List.map_congr_left
  intro i hi
  simp only [leafAt, List.getElem?_append_left (h i hi)]

lemma leafAt_last {n : ℕ} (T : List (DMFormula n)) (F : DMFormula n) :
    leafAt (T ++ [F]) T.length = F.leaves := by
  simp [leafAt]

lemma getMap {n : ℕ} {α : Type} {T : List (DMFormula n)} {i : ℕ} {F : DMFormula n}
    (h : T[i]? = some F) (f : DMFormula n → α) (base : α) :
    (T.map f).getD i base = f F := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_map, h]

-- For several queried wires, count the leaves of their expansions together.
-- A final gate may be expanded at most once because its wire has one use.
lemma snocBudget {n : ℕ} (gs : List Gate) (g : Gate)
    (T : List (DMFormula n)) (F : DMFormula n) (a b : ℕ)
    (len : T.length = n + gs.length) (inputs : g.inputs = [a,b])
    (oldA : a < T.length) (oldB : b < T.length)
    (newLeaves : F.leaves = leafAt T a + leafAt T b)
    (earlier : ∀ R : List ℕ,
      ((R ++ gs.flatMap Gate.inputs).filter (fun i => decide (n ≤ i))).Nodup →
      (∀ r ∈ R, r < T.length) → leafSum T R ≤ R.length + gs.length) :
    ∀ R : List ℕ,
      ((R ++ (gs ++ [g]).flatMap Gate.inputs).filter (fun i => decide (n ≤ i))).Nodup →
      (∀ r ∈ R, r < (T ++ [F]).length) →
      leafSum (T ++ [F]) R ≤ R.length + (gs ++ [g]).length := by
  intro R unique valid
  let p := fun i : ℕ => decide (n ≤ i)
  let prev := (gs.flatMap Gate.inputs).filter p
  let pair := ([a,b] : List ℕ).filter p
  have packed : (R.filter p ++ (prev ++ pair)).Nodup := by
    simpa only [p, prev, pair, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
      List.append_nil, inputs, List.filter_append] using unique
  by_cases hR : T.length ∈ R
  · obtain ⟨L, S, rfl⟩ := List.append_of_mem hR
    have pop : p T.length = true := by simp [p, len]
    have packSplit : (L.filter p ++ T.length :: (S.filter p ++ (prev ++ pair))).Nodup := by
      simpa only [List.filter_append, List.filter_cons, pop, ite_true, List.append_assoc, List.cons_append] using packed
    have htail := (List.nodup_append.mp packSplit).2.1
    have noLeft : T.length ∉ L := by
      intro h
      have disjoint := (List.nodup_append.mp packSplit).2.2
      exact disjoint _ (List.mem_filter.mpr ⟨h,pop⟩) _ (by simp) rfl
    have noRight : T.length ∉ S := by
      intro h
      have miss := (List.nodup_cons.mp htail).1
      exact miss (List.mem_append_left _ (List.mem_filter.mpr ⟨h,pop⟩))
    have validL : ∀ i ∈ L, i < T.length := by
      intro i hi
      have inR : i ∈ L ++ T.length :: S := List.mem_append_left _ hi
      have bound := valid i inR
      have different : i ≠ T.length := fun he => noLeft (he ▸ hi)
      simp at bound
      omega
    have validS : ∀ i ∈ S, i < T.length := by
      intro i hi
      have inR : i ∈ L ++ T.length :: S := List.mem_append_right _
        (List.mem_cons_of_mem _ hi)
      have bound := valid i inR
      have different : i ≠ T.length := fun he => noRight (he ▸ hi)
      simp at bound
      omega
    let R' := (L ++ S) ++ [a,b]
    have deleted : ((L.filter p ++ S.filter p) ++ (prev ++ pair)).Nodup := by
      rw [List.append_assoc]
      exact ((List.sublist_cons_self _ _).append_left _).nodup packSplit
    have swapped : ((L.filter p ++ S.filter p) ++ (pair ++ prev)).Nodup :=
      (List.Perm.append_left _ List.perm_append_comm).nodup_iff.mp deleted
    have earlierNodup : ((R' ++ gs.flatMap Gate.inputs).filter p).Nodup := by
      simpa only [R', prev, pair, List.filter_append, List.append_assoc] using swapped
    have earlierValid : ∀ i ∈ R', i < T.length := by
      intro i hi
      simp only [R', List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with (h | h) | rfl | rfl
      · exact validL i h
      · exact validS i h
      · exact oldA
      · exact oldB
    have earlierBound := earlier R' earlierNodup earlierValid
    have comparison : leafSum (T ++ [F]) (L ++ T.length :: S) = leafSum T R' := by
      rw [leafSum_append, leafSum_old _ _ _ validL]
      have one : (T.length :: S) = [T.length] ++ S := rfl
      rw [one, leafSum_append, leafSum_old _ _ _ validS]
      simp only [R', leafSum_append]
      have hsingle : leafSum (T ++ [F]) [T.length] = F.leaves := by
        simpa [leafSum] using leafAt_last T F
      rw [hsingle, newLeaves]
      simp [leafSum]
      omega
    rw [comparison]
    simp only [R', List.length_append, List.length_cons, List.length_nil] at earlierBound ⊢
    omega
  · have validOld : ∀ i ∈ R, i < T.length := by
      intro i hi
      have bound := valid i hi
      have different : i ≠ T.length := fun he => hR (he ▸ hi)
      simp at bound
      omega
    have simpler : ((R ++ gs.flatMap Gate.inputs).filter p).Nodup := by
      have initialPart : ((R.filter p ++ prev) ++ pair).Nodup := by
        simpa only [List.append_assoc] using packed
      simpa only [prev, List.filter_append] using (List.nodup_append.mp initialPart).1
    rw [leafSum_old _ _ _ validOld]
    have bound := earlier R simpler validOld
    simp
    omega

lemma expandAll (n : ℕ) (gs : List Gate) (ok : shaped n gs) :
    ∃ T : List (DMFormula n), T.length = n + gs.length ∧
      (∀ (i : ℕ) (F : DMFormula n), T[i]? = some F → positive F = true) ∧
      (∀ x, T.map (fun F => F.eval x) = (Circuit.mk gs 0).wires (List.ofFn x)) ∧
      (∀ i : Fin n, T.map (degree i) = (Circuit.mk gs 0).lineDegrees n {i.val}) ∧
      ∀ R : List ℕ, ((R ++ gs.flatMap Gate.inputs).filter (fun i => decide (n ≤ i))).Nodup →
        (∀ r ∈ R, r < T.length) → leafSum T R ≤ R.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil =>
    let T := List.ofFn (fun i : Fin n => DMFormula.lit i true)
    refine ⟨T, by simp [T], ?_, ?_, ?_, ?_⟩
    · intro i F hi
      obtain ⟨bound, rfl⟩ := List.getElem?_eq_some_iff.mp hi
      have payload : T[i] = DMFormula.lit ⟨i, by simpa [T] using bound⟩ true := by simp [T]
      rw [payload]
      rfl
    · intro x
      simp [T, Circuit.wires, Function.comp_def, DMFormula.eval]
    · intro i
      apply List.ext_getElem
      · simp [Circuit.lineDegrees, T]
      · intro j hj hj'
        simp only [Circuit.lineDegrees, List.foldl_nil]
        rw [List.getElem_map, List.getElem_map]
        have jT : j < T.length := by simpa using hj
        have eqn : T[j]'jT = DMFormula.lit ⟨j, by simpa [T] using jT⟩ true := by simp [T]
        rw [eqn]
        simp [degree, List.getElem_range, Fin.ext_iff]
    · intro R _ valid
      have single (r : ℕ) (hr : r ∈ R) : leafAt T r = 1 := by
        have br := valid r hr
        have eqn : T[r] = DMFormula.lit ⟨r, by simpa [T] using br⟩ true := by simp [T]
        simp [leafAt, List.getElem?_eq_getElem br, eqn, DMFormula.leaves]
      have eqn : R.map (leafAt T) = R.map (fun _ => 1) := List.map_congr_left single
      simp [leafSum, eqn]
  | append_singleton gs g ih =>
    have early : shaped n gs := by
      intro j h atj
      have bound := (List.getElem?_eq_some_iff.mp atj).choose
      apply ok j h
      rwa [List.getElem?_append_left bound]
    obtain ⟨T, len, pos, evals, degs, budget⟩ := ih early
    have gateAt : (gs ++ [g])[gs.length]? = some g := by simp
    obtain ⟨operator, a, b, inputs, _, ha, hb⟩ := ok gs.length g gateAt
    have ba : a < T.length := len.symm ▸ ha
    have bb : b < T.length := len.symm ▸ hb
    let A := T[a]
    let B := T[b]
    have aAt : T[a]? = some A := List.getElem?_eq_getElem ba
    have bAt : T[b]? = some B := List.getElem?_eq_getElem bb
    let F := match g.op with
      | GateOp.and => DMFormula.and A B
      | _ => DMFormula.or A B
    have posF : positive F = true := by
      rcases operator with op | op <;>
        simpa [F, op, positive] using Bool.and_eq_true_iff.mpr ⟨pos a A aAt, pos b B bAt⟩
    have leafF : F.leaves = leafAt T a + leafAt T b := by
      rcases operator with op | op <;> simp [F, op, DMFormula.leaves, leafAt, aAt, bAt]
    refine ⟨T ++ [F], by simp [len, Nat.add_assoc], ?_, ?_, ?_,
      snocBudget gs g T F a b len inputs ba bb leafF budget⟩
    · intro j H h
      by_cases before : j < T.length
      · rw [List.getElem?_append_left before] at h
        exact pos j H h
      · have inside := (List.getElem?_eq_some_iff.mp h).choose
        have equality : j = T.length := by simp at inside; omega
        subst j
        simp only [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self,
          List.getElem?_cons_zero, Option.some.injEq] at h
        exact h ▸ posF
    · intro x
      simp only [List.map_append, List.map_cons, List.map_nil]
      have unfoldStep :
          (Circuit.mk (gs ++ [g]) 0).wires (List.ofFn x) =
            (Circuit.mk gs 0).wires (List.ofFn x) ++
              [g.op.eval (g.inputs.map fun j => ((Circuit.mk gs 0).wires (List.ofFn x)).getD j false)] := by
        simp [Circuit.wires, List.foldl_append]
      rw [unfoldStep, ← evals x, inputs]
      simp only [List.map_cons, List.map_nil, getMap aAt, getMap bAt]
      rcases operator with op | op <;> simp [F, op, DMFormula.eval, GateOp.eval]
    · intro i
      simp only [List.map_append, List.map_cons, List.map_nil]
      have unfoldStep :
          (Circuit.mk (gs ++ [g]) 0).lineDegrees n {i.val} =
            (Circuit.mk gs 0).lineDegrees n {i.val} ++
              [g.lineDegree ((Circuit.mk gs 0).lineDegrees n {i.val})] := by
        simp [Circuit.lineDegrees, List.foldl_append]
      rw [unfoldStep, ← degs i]
      rcases operator with op | op <;>
        simp [F, op, degree, Gate.lineDegree, inputs, List.getD_eq_getElem?_getD, aAt, bAt]

lemma unfoldTree (n : ℕ) (C : Circuit) (shape : shaped n C.gates)
    (single : ((C.output :: C.gates.flatMap Gate.inputs).filter (fun i => decide (n ≤ i))).Nodup)
    (accepts : C.eval (List.ofFn (fun _ : Fin n => true)) = true) :
    ∃ F : DMFormula n, positive F = true ∧ F.leaves ≤ C.size + 1 ∧
      (∀ x, F.eval x = C.eval (List.ofFn x)) ∧
      (∀ i : Fin n, degree i F = C.lineDeg n {i.val}) := by
  obtain ⟨T, len, pos, evals, degs, budget⟩ := expandAll n C.gates shape
  have bound : C.output < T.length := by
    by_contra hn
    change (C.wires (List.ofFn (fun _ : Fin n => true))).getD C.output false = true at accepts
    change ((Circuit.mk C.gates 0).wires (List.ofFn (fun _ : Fin n => true))).getD C.output false = true at accepts
    rw [← evals, List.getD_eq_default _ _ (by simpa using Nat.le_of_not_lt hn)] at accepts
    cases accepts
  let F := T[C.output]
  have found : T[C.output]? = some F := List.getElem?_eq_getElem bound
  have b := budget [C.output] single (by simpa using bound)
  have small : F.leaves ≤ C.size + 1 := by
    simpa [leafSum, leafAt, found, Circuit.size, Nat.add_comm] using b
  refine ⟨F, pos _ _ found, small, ?_, ?_⟩
  · intro x
    change F.eval x = ((Circuit.mk C.gates 0).wires (List.ofFn x)).getD C.output false
    rw [← evals, getMap found]
  · intro i
    change degree i F = ((Circuit.mk C.gates 0).lineDegrees n {i.val}).getD C.output 0
    rw [← degs, getMap found]

end Unfold

lemma positive_rec (F : PEqualNP.MetaComplexity.DMFormula 10)
    (h : Unfold.positive F = true) :
    PEqualNP.MetaComplexity.DMFormula.rec
      (motive := fun _ : PEqualNP.MetaComplexity.DMFormula 10 => Prop)
      (fun (_ : Fin 10) (c : Bool) => c = true)
      (fun _ _ p q => p ∧ q) (fun _ _ p q => p ∧ q) F := by
  induction F with
  | lit i b => exact h
  | and a b ha hb =>
      change Unfold.positive a && Unfold.positive b = true at h
      exact ⟨ha (Bool.and_eq_true_iff.mp h).1, hb (Bool.and_eq_true_iff.mp h).2⟩
  | or a b ha hb =>
      change Unfold.positive a && Unfold.positive b = true at h
      exact ⟨ha (Bool.and_eq_true_iff.mp h).1, hb (Bool.and_eq_true_iff.mp h).2⟩

lemma no_sharing_lower (C : PEqualNP.CircuitLowerBounds.Circuit)
    (shape : Unfold.shaped 10 C.gates)
    (single : ((C.output :: C.gates.flatMap PEqualNP.CircuitLowerBounds.Gate.inputs).filter
      (fun i => decide (10 ≤ i))).Nodup)
    (computes : ∀ x : Fin 10 → Bool, C.eval (List.ofFn x) = edge x) :
    20 ≤ C.size := by
  have allTrue : C.eval (List.ofFn (fun _ : Fin 10 => true)) = true := by
    rw [computes]
    rfl
  obtain ⟨F, hp, hs, he, _⟩ := Unfold.unfoldTree 10 C shape single allTrue
  have lower := positive_formula_lower F (positive_rec F hp)
    (fun x => (he x).trans (computes x))
  omega

lemma nodup_of_complete_and_short (l : List ℕ) (n k : ℕ)
    (complete : ∀ j < k, n + j ∈ l) (short : l.length ≤ k) : l.Nodup := by
  have subset : (Finset.range k).image (fun j => n + j) ⊆ l.toFinset := by
    intro i hi
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hi
    exact List.mem_toFinset.mpr (complete j (Finset.mem_range.mp hj))
  have lower := Finset.card_le_card subset
  have injective : Function.Injective (fun j : ℕ => n + j) := fun _ _ h => Nat.add_left_cancel h
  rw [Finset.card_image_of_injective _ injective, Finset.card_range] at lower
  have upper := List.toFinset_card_le l
  change (l : Multiset ℕ).Nodup
  apply (Multiset.toFinset_card_eq_card_iff_nodup (m := (l : Multiset ℕ))).mp
  change l.toFinset.card = l.length
  omega

lemma internal_nodup_of_input_mass (l : List ℕ) (n k : ℕ)
    (edges : l.length ≤ 2 * k + 1)
    (input_mass : 2 * n ≤ (l.filter (fun i => decide (i < n))).length)
    (small : k + 1 ≤ 2 * n)
    (live : ∀ j < k, n + j ∈ l) :
    (l.filter (fun i => decide (n ≤ i))).Nodup := by
  have partition := List.length_eq_length_filter_add (l := l) (fun i => decide (i < n))
  have complement : (fun i : ℕ => !(decide (i < n))) = (fun i => decide (n ≤ i)) := by
    funext i
    by_cases h : i < n
    · simp [h, show ¬ n ≤ i by omega]
    · simp [h, show n ≤ i by omega]
  rw [complement] at partition
  apply nodup_of_complete_and_short _ n k
  · intro j hj
    exact List.mem_filter.mpr ⟨live j hj, by simp⟩
  · omega

end PEqualNP.Outside.L_meta_1890.ReadTwice
