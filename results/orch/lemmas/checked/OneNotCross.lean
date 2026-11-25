import Mathlib.Order.Lattice
import Mathlib.Order.Monotone.Basic

namespace PEqualNP.Outside.L_meta_2592_aux

lemma oneNot_cross {α : Type*} [Lattice α] (f h : α → Bool) (G : α → Bool → Bool)
    (outputMono : Monotone f) (sourceMono : Monotone h)
    (bitMono : ∀ x, Monotone (G x)) (correct : ∀ x, G x (!h x) = f x)
    (a b : α) (trueAt : f a = true) (falseAt : f b = false)
    (sourceFalse : h a = false) (sourceTrue : h b = true)
    (falseChanges : G a false = false) (trueChanges : G b true = true) :
    h (a ⊓ b) = false ∧ h (a ⊔ b) = true ∧
      ∀ z, G (a ⊓ b) z = false ∧ G a z = z ∧ G b z = z ∧ G (a ⊔ b) z = true := by
  have sourceLow : h (a ⊓ b) = false := by
    apply Bool.eq_false_of_le_false
    simpa only [sourceFalse] using sourceMono (show a ⊓ b ≤ a from inf_le_left)
  have sourceHigh : h (a ⊔ b) = true := by
    apply Bool.eq_true_of_true_le
    simpa only [sourceTrue] using sourceMono (show b ≤ a ⊔ b from le_sup_right)
  have outputLow : f (a ⊓ b) = false := by
    apply Bool.eq_false_of_le_false
    simpa only [falseAt] using outputMono (show a ⊓ b ≤ b from inf_le_right)
  have outputHigh : f (a ⊔ b) = true := by
    apply Bool.eq_true_of_true_le
    simpa only [trueAt] using outputMono (show a ≤ a ⊔ b from le_sup_left)
  have lowTrue : G (a ⊓ b) true = false := by
    simpa only [sourceLow, Bool.not_false, outputLow] using correct (a ⊓ b)
  have lowFalse : G (a ⊓ b) false = false := by
    apply Bool.eq_false_of_le_false
    simpa only [lowTrue] using bitMono (a ⊓ b) (show false ≤ true from Bool.false_le _)
  have highFalse : G (a ⊔ b) false = true := by
    simpa only [sourceHigh, Bool.not_true, outputHigh] using correct (a ⊔ b)
  have highTrue : G (a ⊔ b) true = true := by
    apply Bool.eq_true_of_true_le
    simpa only [highFalse] using bitMono (a ⊔ b) (show false ≤ true from Bool.false_le _)
  have aTrue : G a true = true := by
    simpa only [sourceFalse, Bool.not_false, trueAt] using correct a
  have bFalse : G b false = false := by
    simpa only [sourceTrue, Bool.not_true, falseAt] using correct b
  refine ⟨sourceLow, sourceHigh, ?_⟩
  intro z
  cases z
  · exact ⟨lowFalse, falseChanges, bFalse, highFalse⟩
  · exact ⟨lowTrue, aTrue, trueChanges, highTrue⟩

end PEqualNP.Outside.L_meta_2592_aux
