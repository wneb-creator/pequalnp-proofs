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

theorem rectangle_below_iff {P L:ℕ} (I:Fin P→Fin L→Prop)
 (A:Finset (Fin P)) (B:Finset (Fin L)):
 (∀z:Fin (P+L)→Bool,
   (∃p∈A,z (Fin.castAdd L p)=true)→(∃l∈B,z (Fin.natAdd P l)=true)→
   ∃p:Fin P,∃l:Fin L,I p l∧z (Fin.castAdd L p)=true∧z (Fin.natAdd P l)=true) ↔
 (∀p∈A,∀l∈B,I p l) := by
 constructor
 · intro below p hp l hl
   let z:Fin (P+L)→Bool:=Fin.addCases (fun q=>decide (q=p)) (fun r=>decide (r=l))
   obtain ⟨q,r,edge,hq,hr⟩:=below z ⟨p,hp,by simp [z]⟩ ⟨l,hl,by simp [z]⟩
   have eqp:q=p:=by simpa [z] using hq
   have eql:r=l:=by simpa [z] using hr
   simpa [eqp,eql] using edge
 · intro rectangle z hp hl
   obtain ⟨p,hp,hpz⟩:=hp
   obtain ⟨l,hl,hlz⟩:=hl
   exact ⟨p,l,rectangle p hp l hl,hpz,hlz⟩

theorem clean_block_star_cost {P L:ℕ} (I:Fin P→Fin L→Prop)
 (noFour:∀p p':Fin P,∀l l':Fin L,p≠p'→l≠l'→¬(I p l∧I p l'∧I p' l∧I p' l'))
 (A:Finset (Fin P)) (B:Finset (Fin L)) (ha:A.Nonempty) (hb:B.Nonempty)
 (below:∀z:Fin (P+L)→Bool,
   (∃p∈A,z (Fin.castAdd L p)=true)→(∃l∈B,z (Fin.natAdd P l)=true)→
   ∃p:Fin P,∃l:Fin L,I p l∧z (Fin.castAdd L p)=true∧z (Fin.natAdd P l)=true):
 (A.card=1∨B.card=1) ∧ (A×ˢB).card=A.card+B.card-1 := by
 have rectangle:=(rectangle_below_iff I A B).mp below
 refine ⟨?_,rectangle_star_cost I noFour A B ha hb rectangle⟩
 have hca:=Finset.card_pos.mpr ha
 have hcb:=Finset.card_pos.mpr hb
 rcases rectangle_is_star I noFour A B rectangle with h|h
 · left; omega
 · right; omega

theorem pure_line_support_unique_center {P L:ℕ} (I:Fin P→Fin L→Prop)
 (noFour:∀p p':Fin P,∀l l':Fin L,p≠p'→l≠l'→¬(I p l∧I p l'∧I p' l∧I p' l'))
 (B:Finset (Fin L)) (many:2≤B.card) (p p':Fin P)
 (left:∀l∈B,I p l) (right:∀l∈B,I p' l):p=p' := by
 by_contra distinct
 obtain ⟨l,hl,l',hl',hll⟩:=Finset.one_lt_card.mp (by omega:1<B.card)
 exact noFour p p' l l' distinct hll ⟨left l hl,left l' hl',right l hl,right l' hl'⟩

theorem pure_point_support_unique_center {P L:ℕ} (I:Fin P→Fin L→Prop)
 (noFour:∀p p':Fin P,∀l l':Fin L,p≠p'→l≠l'→¬(I p l∧I p l'∧I p' l∧I p' l'))
 (A:Finset (Fin P)) (many:2≤A.card) (l l':Fin L)
 (left:∀p∈A,I p l) (right:∀p∈A,I p l'):l=l' := by
 by_contra distinct
 obtain ⟨p,hp,p',hp',hpp⟩:=Finset.one_lt_card.mp (by omega:1<A.card)
 exact noFour p p' l l' hpp distinct ⟨left p hp,right p hp,left p' hp',right p' hp'⟩

theorem distinct_centers_share_at_most_one {P L:ℕ} (I:Fin P→Fin L→Prop)
 (noFour:∀p p':Fin P,∀l l':Fin L,p≠p'→l≠l'→¬(I p l∧I p l'∧I p' l∧I p' l'))
 (A B:Finset (Fin L)) (p p':Fin P) (distinct:p≠p')
 (left:∀l∈A,I p l) (right:∀l∈B,I p' l):(A∩B).card≤1 := by
 by_contra many
 have big:2≤(A∩B).card:=by omega
 exact distinct (pure_line_support_unique_center I noFour (A∩B) big p p'
   (fun l hl=>left l (Finset.mem_inter.mp hl).1)
   (fun l hl=>right l (Finset.mem_inter.mp hl).2))

theorem binary_reader_budget {α:Type*} [DecidableEq α]
 (leaves gates roots:Finset α) (children:α→Finset α)
 (separate:Disjoint leaves gates)
 (fanin:∀g∈gates,(children g).card≤2)
 (covered:∀w∈leaves∪gates,w∈roots∨∃g∈gates,w∈children g):
 leaves.card≤gates.card+roots.card := by
 have sub:leaves∪gates⊆roots∪gates.biUnion children := by
   intro w hw
   rcases covered w hw with root|⟨g,hg,child⟩
   · exact Finset.mem_union_left _ root
   · exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨g,hg,child⟩)
 have count:=Finset.card_le_card sub
 rw [Finset.card_union_of_disjoint separate] at count
 have unions:=Finset.card_union_le roots (gates.biUnion children)
 have childsum:(gates.biUnion children).card≤∑g∈gates,(children g).card:=Finset.card_biUnion_le
 have maxsum:(∑g∈gates,(children g).card)≤2*gates.card := by
   calc
     _≤∑g∈gates,2:=Finset.sum_le_sum (fun g hg=>fanin g hg)
     _=2*gates.card:=by simp [Nat.mul_comm]
 omega

end PEqualNP.Outside.L_meta_2585
