import Mathlib.Order.Monotone.Defs
import Mathlib.Data.Bool.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fin.VecNotation

namespace PEqualNP.Outside.L_meta_2592.OneNot

lemma replace_true {α : Type*} (f h : α → Bool) (G : α → Bool → Bool)
    (mono : ∀ x, G x false ≤ G x true)
    (correct : ∀ x, G x (!h x) = f x)
    (below : ∀ x, h x ≤ f x) :
    ∀ x, G x true = f x := by
  intro x
  have hm := mono x
  have hc := correct x
  have hb := below x
  cases hh : h x <;> cases hf : f x <;>
    cases h0 : G x false <;> cases h1 : G x true <;> simp_all [Bool.le_iff_imp]

lemma replace_false {α : Type*} (f h : α → Bool) (G : α → Bool → Bool)
    (mono : ∀ x, G x false ≤ G x true)
    (correct : ∀ x, G x (!h x) = f x)
    (above : ∀ x, f x ≤ h x) :
    ∀ x, G x false = f x := by
  intro x
  have hm := mono x
  have hc := correct x
  have ha := above x
  cases hh : h x <;> cases hf : f x <;>
    cases h0 : G x false <;> cases h1 : G x true <;> simp_all [Bool.le_iff_imp]

lemma essential_witnesses {α : Type*} (f h : α → Bool) (G : α → Bool → Bool)
    (mono : ∀ x, G x false ≤ G x true)
    (correct : ∀ x, G x (!h x) = f x)
    (essentialFalse : ∃ x, G x false ≠ f x)
    (essentialTrue : ∃ x, G x true ≠ f x) :
    (∃ x, h x = false ∧ f x = true) ∧
      (∃ x, h x = true ∧ f x = false) := by
  obtain ⟨a, ha⟩ := essentialFalse
  obtain ⟨b, hb⟩ := essentialTrue
  constructor
  · refine ⟨a, ?_⟩
    have hm := mono a
    have hc := correct a
    cases hh : h a <;> cases hf : f a <;>
      cases h0 : G a false <;> cases h1 : G a true <;> simp_all [Bool.le_iff_imp]
  · refine ⟨b, ?_⟩
    have hm := mono b
    have hc := correct b
    cases hh : h b <;> cases hf : f b <;>
      cases h0 : G b false <;> cases h1 : G b true <;> simp_all [Bool.le_iff_imp]

def petersen (x : Fin 10 → Bool) : Bool :=
  (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) ||
    (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) ||
    (x 3 && x 8) || (x 4 && x 9) || (x 5 && x 7) || (x 7 && x 9) ||
    (x 9 && x 6) || (x 6 && x 8) || (x 8 && x 5)

def bits (m : ℕ) : Fin 10 → Bool := fun i => m.testBit i.val

def edgeMask : Fin 15 → ℕ :=
  ![3, 6, 12, 24, 17, 33, 66, 132, 264, 528, 160, 640, 576, 320, 288]

def independentMask : Fin 15 → ℕ :=
  ![50, 69, 104, 116, 138, 201, 208, 276, 385, 402, 521, 548, 554, 770, 773]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
lemma edge_support : ∀ x : Fin 10 → Bool,
    petersen x = true → ∃ e : Fin 15, bits (edgeMask e) ≤ x := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
lemma independent_support : ∀ x : Fin 10 → Bool,
    petersen x = false → ∃ i : Fin 15, x ≤ bits (independentMask i) := by
  decide

lemma essential_graph_witnesses (h : (Fin 10 → Bool) → Bool)
    (G : (Fin 10 → Bool) → Bool → Bool)
    (mono : ∀ x, G x false ≤ G x true)
    (hmono : Monotone h)
    (correct : ∀ x, G x (!h x) = petersen x)
    (essentialFalse : ∃ x, G x false ≠ petersen x)
    (essentialTrue : ∃ x, G x true ≠ petersen x) :
    (∃ e : Fin 15, h (bits (edgeMask e)) = false) ∧
      (∃ i : Fin 15, h (bits (independentMask i)) = true) := by
  obtain ⟨⟨a, ha, fa⟩, ⟨b, hb, fb⟩⟩ :=
    essential_witnesses petersen h G mono correct essentialFalse essentialTrue
  obtain ⟨e, he⟩ := edge_support a fa
  obtain ⟨i, hi⟩ := independent_support b fb
  constructor
  · refine ⟨e, ?_⟩
    have hm := hmono he
    rw [ha] at hm
    cases hh : h (bits (edgeMask e)) <;> simp_all [Bool.le_iff_imp]
  · refine ⟨i, ?_⟩
    have hm := hmono hi
    rw [hb] at hm
    cases hh : h (bits (independentMask i)) <;> simp_all [Bool.le_iff_imp]

end PEqualNP.Outside.L_meta_2592.OneNot
