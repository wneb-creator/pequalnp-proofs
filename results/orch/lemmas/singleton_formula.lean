import PEqualNP.Defs
import Mathlib.Tactic

namespace PEqualNP.Outside.L_meta_3451_aux.SingletonFormula

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

end PEqualNP.Outside.L_meta_3451_aux.SingletonFormula
