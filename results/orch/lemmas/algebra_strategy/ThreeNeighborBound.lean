import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_650_aux.ThreeNeighborBound

set_option maxRecDepth 8192
set_option maxHeartbeats 0

theorem one_forbids {α β : Type} [DecidableEq α] [DecidableEq β]
    (N : α → Finset β) (P : Finset α) (L T : Finset β)
    (degree : ∀ a, (N a).card = 4)
    (ambient : ∀ a ∈ P, N a ⊆ T) (LT : L ⊆ T) (cardT : T.card = 13)
    (apart : ∀ a ∈ P, ∀ b ∈ L, b ∉ N a) (nonempty : P.Nonempty) :
    L.card ≤ 9 := by
  obtain ⟨a, ha⟩ := nonempty
  have hd : Disjoint (N a) L := by
    rw [Finset.disjoint_left]
    intro b hb hbL
    exact apart a ha b hbL hb
  have hs : N a ∪ L ⊆ T := Finset.union_subset (ambient a ha) LT
  have h := Finset.card_le_card hs
  rw [Finset.card_union_of_disjoint hd, degree, cardT] at h
  omega

theorem three_forbid {α β : Type} [DecidableEq α] [DecidableEq β]
    (N : α → Finset β) (P : Finset α) (L T : Finset β)
    (degree : ∀ a, (N a).card = 4)
    (common : ∀ a b, a ≠ b → (N a ∩ N b).card ≤ 1)
    (ambient : ∀ a ∈ P, N a ⊆ T) (LT : L ⊆ T) (cardT : T.card = 13)
    (apart : ∀ a ∈ P, ∀ b ∈ L, b ∉ N a) (large : 3 ≤ P.card) :
    L.card ≤ 4 := by
  obtain ⟨a, ha, b, hb, c, hc, hab, hac, hbc⟩ :=
    Finset.two_lt_card.mp (show 2 < P.card by omega)
  have h1 := Finset.card_union_add_card_inter (N a) (N b)
  have h2 := Finset.card_union_add_card_inter (N a ∪ N b) (N c)
  have hs : (N a ∪ N b) ∩ N c ⊆ (N a ∩ N c) ∪ (N b ∩ N c) := by
    intro x hx
    simp only [Finset.mem_inter, Finset.mem_union] at hx ⊢
    tauto
  have h3 := Finset.card_le_card hs
  have h4 := Finset.card_union_le (N a ∩ N c) (N b ∩ N c)
  have habc := common a b hab
  have hacc := common a c hac
  have hbcc := common b c hbc
  rw [degree, degree] at h1
  rw [degree] at h2
  have hnine : 9 ≤ ((N a ∪ N b) ∪ N c).card := by omega
  have hd : Disjoint ((N a ∪ N b) ∪ N c) L := by
    rw [Finset.disjoint_left]
    intro x hx hxL
    rcases Finset.mem_union.mp hx with hx | hx
    · rcases Finset.mem_union.mp hx with hx | hx
      · exact apart a ha x hxL hx
      · exact apart b hb x hxL hx
    · exact apart c hc x hxL hx
  have hsub : ((N a ∪ N b) ∪ N c) ∪ L ⊆ T :=
    Finset.union_subset
      (Finset.union_subset (Finset.union_subset (ambient a ha) (ambient b hb)) (ambient c hc)) LT
  have hh := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint hd, cardT] at hh
  omega

theorem mixed_less_twelve {α β : Type} [DecidableEq α] [DecidableEq β]
    (N : α → Finset β) (M : β → Finset α)
    (P A : Finset α) (L B : Finset β)
    (ndegree : ∀ a, (N a).card = 4) (mdegree : ∀ b, (M b).card = 4)
    (ncommon : ∀ a b, a ≠ b → (N a ∩ N b).card ≤ 1)
    (mcommon : ∀ a b, a ≠ b → (M a ∩ M b).card ≤ 1)
    (nambient : ∀ a ∈ P, N a ⊆ B) (mambient : ∀ b ∈ L, M b ⊆ A)
    (PA : P ⊆ A) (LB : L ⊆ B) (cardA : A.card = 13) (cardB : B.card = 13)
    (napart : ∀ a ∈ P, ∀ b ∈ L, b ∉ N a)
    (mapart : ∀ b ∈ L, ∀ a ∈ P, a ∉ M b)
    (np : P.Nonempty) (nl : L.Nonempty) : P.card + L.card ≤ 11 := by
  have lp := one_forbids N P L B ndegree nambient LB cardB napart np
  have pp := one_forbids M L P A mdegree mambient PA cardA mapart nl
  by_contra h
  have hp : 3 ≤ P.card := by omega
  have hl : 3 ≤ L.card := by omega
  have l4 := three_forbid N P L B ndegree ncommon nambient LB cardB napart hp
  have p4 := three_forbid M L P A mdegree mcommon mambient PA cardA mapart hl
  omega

end PEqualNP.Outside.L_meta_650_aux.ThreeNeighborBound
