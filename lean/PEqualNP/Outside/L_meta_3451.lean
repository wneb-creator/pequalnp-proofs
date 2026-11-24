import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3451

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

def decStep (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma decEvalMono (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or) (l : List ℕ)
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

lemma decFoldMono (gs : List Gate)
    (hgs : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) :
    ∀ a b : List Bool, a.length = b.length →
      (∀ i, a.getD i false = true → b.getD i false = true) →
      ∀ i, (gs.foldl decStep a).getD i false = true →
        (gs.foldl decStep b).getD i false = true := by
  induction gs with
  | nil => intro a b _ h; exact h
  | cons g gs ih =>
    intro a b hl h
    rw [List.foldl_cons, List.foldl_cons]
    apply ih (fun g' hg' => hgs g' (List.mem_cons_of_mem _ hg'))
    · simp [decStep, hl]
    · intro i hi
      unfold decStep at hi ⊢
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
          exact decEvalMono g.op (hgs g List.mem_cons_self) _ _ _ (fun k => h k) hi
        · obtain ⟨m, hm⟩ : ∃ m, i - a.length = m + 1 := ⟨i - a.length - 1, by omega⟩
          rw [hm] at hi
          simp at hi

lemma decWireMono (n : ℕ) (C : Circuit) (hC : Monotone2 C)
    (x y : Fin n → Bool) (hxy : ∀ i, x i = true → y i = true) (w : ℕ) :
    (C.wires (List.ofFn x)).getD w false = true →
      (C.wires (List.ofFn y)).getD w false = true := by
  refine decFoldMono C.gates (fun g hg => (hC g hg).1) _ _ (by simp) ?_ w
  intro i hi
  by_cases hin : i < n
  · rw [List.getD_eq_getElem _ _ (by simpa using hin), List.getElem_ofFn] at hi ⊢
    exact hxy ⟨i, hin⟩ hi
  · rw [List.getD_eq_default _ _ (by simp; omega)] at hi
    cases hi

lemma decSingletonPoint (N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I]
    (C : Circuit) (hC : Monotone2 C) (j : ℕ) (p : Fin N)
    (hp : ∃ l, ¬ I p l)
    (hpair : ∀ l, ¬ I p l →
      (C.wires (List.ofFn (fun k : Fin (N + N) =>
        decide (k = Fin.castAdd N p ∨ k = Fin.natAdd N l)))).getD (N + N + j) false = false) :
    (C.wires (List.ofFn (fun k : Fin (N + N) =>
      decide (k = Fin.castAdd N p)))).getD (N + N + j) false = false := by
  obtain ⟨l, hl⟩ := hp
  apply Bool.eq_false_iff.mpr
  intro ht
  have hm := decWireMono (N + N) C hC
    (fun k => decide (k = Fin.castAdd N p))
    (fun k => decide (k = Fin.castAdd N p ∨ k = Fin.natAdd N l))
    (by intro k hk; exact decide_eq_true_iff.mpr (Or.inl (of_decide_eq_true hk)))
    (N + N + j) ht
  rw [hpair l hl] at hm
  cases hm

lemma decSingletonLine (N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I]
    (C : Circuit) (hC : Monotone2 C) (j : ℕ) (l : Fin N)
    (hl : ∃ p, ¬ I p l)
    (hpair : ∀ p, ¬ I p l →
      (C.wires (List.ofFn (fun k : Fin (N + N) =>
        decide (k = Fin.castAdd N p ∨ k = Fin.natAdd N l)))).getD (N + N + j) false = false) :
    (C.wires (List.ofFn (fun k : Fin (N + N) =>
      decide (k = Fin.natAdd N l)))).getD (N + N + j) false = false := by
  obtain ⟨p, hp⟩ := hl
  apply Bool.eq_false_iff.mpr
  intro ht
  have hm := decWireMono (N + N) C hC
    (fun k => decide (k = Fin.natAdd N l))
    (fun k => decide (k = Fin.castAdd N p ∨ k = Fin.natAdd N l))
    (by intro k hk; exact decide_eq_true_iff.mpr (Or.inr (of_decide_eq_true hk)))
    (N + N + j) ht
  rw [hpair p hp] at hm
  cases hm

lemma decAndSingletons (N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I]
    (D : Circuit) (hD : Monotone2 D)
    (hp : ∀ p, ∃ l, ¬ I p l) (hl : ∀ l, ∃ p, ¬ I p l)
    (hpair : ∀ j < D.gates.length, (gateAt D j).op = GateOp.and →
      ∀ p l : Fin N, ¬ I p l →
      (D.wires (List.ofFn (fun k : Fin (N + N) =>
        decide (k = Fin.castAdd N p ∨ k = Fin.natAdd N l)))).getD (N + N + j) false = false) :
    ∀ j < D.gates.length, (gateAt D j).op = GateOp.and →
      (∀ p : Fin N, (D.wires (List.ofFn (fun k : Fin (N + N) =>
        decide (k = Fin.castAdd N p)))).getD (N + N + j) false = false) ∧
      ∀ l : Fin N, (D.wires (List.ofFn (fun k : Fin (N + N) =>
        decide (k = Fin.natAdd N l)))).getD (N + N + j) false = false := by
  intro j hj ha
  constructor
  · intro p
    exact decSingletonPoint N I D hD j p (hp p) (hpair j hj ha p)
  · intro l
    exact decSingletonLine N I D hD j l (hl l) (fun p h => hpair j hj ha p l h)

lemma decFinish (N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I]
    (C : Circuit) (hp : ∀ p, ∃ l, ¬ I p l) (hl : ∀ l, ∃ p, ¬ I p l)
    (hclean : ∃ D : Circuit, Monotone2 D ∧ ReadsBack (N + N) D ∧ D.size ≤ C.size ∧
      (∀ z : Fin (N + N) → Bool, circuitFun (N + N) D z = true ↔
        ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) ∧
      (∀ j < D.gates.length, (gateAt D j).op = GateOp.and →
        ∀ p l : Fin N, ¬ I p l →
        (D.wires (List.ofFn (fun k : Fin (N + N) =>
          decide (k = Fin.castAdd N p ∨ k = Fin.natAdd N l)))).getD (N + N + j) false = false)) :
    ∃ D : Circuit, Monotone2 D ∧ ReadsBack (N + N) D ∧ D.size ≤ C.size ∧
      (∀ z : Fin (N + N) → Bool, circuitFun (N + N) D z = true ↔
        ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) ∧
      (∀ j < D.gates.length, (gateAt D j).op = GateOp.and →
        ∀ p l : Fin N, ¬ I p l →
        (D.wires (List.ofFn (fun k : Fin (N + N) =>
          decide (k = Fin.castAdd N p ∨ k = Fin.natAdd N l)))).getD (N + N + j) false = false) ∧
      (∀ j < D.gates.length, (gateAt D j).op = GateOp.and →
        (∀ p : Fin N, (D.wires (List.ofFn (fun k : Fin (N + N) =>
          decide (k = Fin.castAdd N p)))).getD (N + N + j) false = false) ∧
        ∀ l : Fin N, (D.wires (List.ofFn (fun k : Fin (N + N) =>
          decide (k = Fin.natAdd N l)))).getD (N + N + j) false = false) := by
  obtain ⟨D, hm, hr, hs, hf, hpair⟩ := hclean
  exact ⟨D, hm, hr, hs, hf, hpair, decAndSingletons N I D hm hp hl hpair⟩

lemma decUniversalPointDegree (N : ℕ) (I : Fin N → Fin N → Prop)
    (hfour : ∀ p p' l l' : Fin N, p ≠ p' → l ≠ l' →
      ¬ (I p l ∧ I p l' ∧ I p' l ∧ I p' l'))
    (p : Fin N) (hp : ∀ l, I p l) (q : Fin N) (hq : q ≠ p)
    (l l' : Fin N) (hl : I q l) (hl' : I q l') : l = l' := by
  by_contra hne
  exact hfour p q l l' (Ne.symm hq) hne ⟨hp l, hp l', hl, hl'⟩

lemma decUniversalLineDegree (N : ℕ) (I : Fin N → Fin N → Prop)
    (hfour : ∀ p p' l l' : Fin N, p ≠ p' → l ≠ l' →
      ¬ (I p l ∧ I p l' ∧ I p' l ∧ I p' l'))
    (l : Fin N) (hl : ∀ p, I p l) (k : Fin N) (hk : k ≠ l)
    (p p' : Fin N) (hp : I p k) (hp' : I p' k) : p = p' := by
  by_contra hne
  exact hfour p p' l k hne (Ne.symm hk) ⟨hl p, hp, hl p', hp'⟩

end PEqualNP.Outside.L_meta_3451
