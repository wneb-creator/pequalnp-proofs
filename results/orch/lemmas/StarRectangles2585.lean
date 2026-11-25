import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Tactic

namespace PEqualNP.Outside.L_meta_2585

theorem rectangle_is_star {P L:ℕ} (I:Fin P→Fin L→Prop)
 (noFour:∀p p':Fin P,∀l l':Fin L,p≠p'→l≠l'→¬(I p l∧I p l'∧I p' l∧I p' l'))
 (A:Finset (Fin P)) (B:Finset (Fin L))
 (rectangle:∀p∈A,∀l∈B,I p l):A.card≤1∨B.card≤1 := by
 by_contra neither
 push_neg at neither
 obtain ⟨p,hp,p',hp',hpp⟩:=Finset.one_lt_card.mp neither.1
 obtain ⟨l,hl,l',hl',hll⟩:=Finset.one_lt_card.mp neither.2
 exact noFour p p' l l' hpp hll ⟨rectangle p hp l hl,rectangle p hp l' hl',
   rectangle p' hp' l hl,rectangle p' hp' l' hl'⟩

theorem rectangle_star_cost {P L:ℕ} (I:Fin P→Fin L→Prop)
 (noFour:∀p p':Fin P,∀l l':Fin L,p≠p'→l≠l'→¬(I p l∧I p l'∧I p' l∧I p' l'))
 (A:Finset (Fin P)) (B:Finset (Fin L)) (ha:A.Nonempty) (hb:B.Nonempty)
 (rectangle:∀p∈A,∀l∈B,I p l):
 (A×ˢB).card=A.card+B.card-1 := by
 rw [Finset.card_product]
 have hca:=Finset.card_pos.mpr ha
 have hcb:=Finset.card_pos.mpr hb
 rcases rectangle_is_star I noFour A B rectangle with h|h
 · have eq:A.card=1:=by omega
   rw [eq]
   omega
 · have eq:B.card=1:=by omega
   rw [eq]
   omega

end PEqualNP.Outside.L_meta_2585
