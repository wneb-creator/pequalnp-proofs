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

namespace PEqualNP.Outside.L_meta_650_aux.TightCoverGeometry
set_option maxRecDepth 8192
set_option maxHeartbeats 0

theorem biUnion_tight {α β : Type} [DecidableEq α] [DecidableEq β]
    (K : Finset α) (F : α → Finset β)
    (tight : (K.biUnion F).card = ∑ u ∈ K, (F u).card) :
    (K : Set α).PairwiseDisjoint F := by
  classical
  induction K using Finset.induction_on with
  | empty => simp
  | @insert u K hnew ih =>
    rw [Finset.biUnion_insert, Finset.sum_insert hnew] at tight
    have hcount := Finset.card_union_add_card_inter (F u) (K.biUnion F)
    have hbound := Finset.card_biUnion_le (s := K) (t := F)
    have hz : (F u ∩ K.biUnion F).card = 0 := by omega
    have hd : Disjoint (F u) (K.biUnion F) :=
      Finset.disjoint_iff_inter_eq_empty.mpr (Finset.card_eq_zero.mp hz)
    have hrest : (K.biUnion F).card = ∑ v ∈ K, (F v).card := by omega
    have hp := ih hrest
    intro a ha b hb hab
    rcases Finset.mem_insert.mp ha with hea | ha
    · subst a
      have hbK : b ∈ K := (Finset.mem_insert.mp hb).resolve_left (Ne.symm hab)
      change Disjoint (F u) (F b)
      rw [Finset.disjoint_left]
      intro x hx hxB
      exact Finset.disjoint_left.mp hd hx (Finset.mem_biUnion.mpr ⟨b, hbK, hxB⟩)
    · rcases Finset.mem_insert.mp hb with heb | hb
      · subst b
        change Disjoint (F a) (F u)
        rw [Finset.disjoint_left]
        intro x hxA hx
        exact Finset.disjoint_left.mp hd hx (Finset.mem_biUnion.mpr ⟨a, ha, hxA⟩)
      · exact hp ha hb hab

theorem tight_deleted_cover_independent {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (d : ℕ)
    (degree : ∀ v : Fin n, (G.edgeFinset.filter fun e => v ∈ e).card ≤ d)
    (U : Finset (Sym2 (Fin n))) (K : Finset (Fin n))
    (cover : (G.deleteEdges ↑U).IsVertexCover ↑K)
    (tight : G.edgeFinset.card = U.card + d * K.card) :
    ∀ u ∈ K, ∀ v ∈ K, ¬ G.Adj u v := by
  classical
  let F := fun v : Fin n => G.edgeFinset.filter fun e => v ∈ e
  have sub : G.edgeFinset ⊆ U ∪ K.biUnion F := by
    intro e he
    by_cases hu : e ∈ U
    · exact Finset.mem_union_left _ hu
    · apply Finset.mem_union_right
      induction e using Sym2.ind with
      | _ a b =>
        have hab := SimpleGraph.mem_edgeFinset.mp he
        rcases cover (SimpleGraph.deleteEdges_adj.mpr ⟨hab, hu⟩) with ha | hb
        · exact Finset.mem_biUnion.mpr ⟨a, ha, by simp [F, he]⟩
        · exact Finset.mem_biUnion.mpr ⟨b, hb, by simp [F, he]⟩
  have h1 := Finset.card_le_card sub
  have h2 := Finset.card_union_le U (K.biUnion F)
  have h3 := Finset.card_biUnion_le (s := K) (t := F)
  have h4 : (∑ v ∈ K, (F v).card) ≤ d * K.card := by
    calc
      (∑ v ∈ K, (F v).card) ≤ ∑ _v ∈ K, d := Finset.sum_le_sum (fun v hv => degree v)
      _ = d * K.card := by simp [Nat.mul_comm]
  have heq : (K.biUnion F).card = ∑ v ∈ K, (F v).card := by omega
  have hp := biUnion_tight K F heq
  intro u hu v hv huv
  have hd := hp hu hv huv.ne
  have he : s(u,v) ∈ G.edgeFinset := SimpleGraph.mem_edgeFinset.mpr huv
  have heu : s(u,v) ∈ F u := by simp [F, he]
  have hev : s(u,v) ∈ F v := by simp [F, he]
  exact Finset.disjoint_left.mp hd heu hev

theorem independent_twelve_pure {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (A B : Finset (Fin n)) (disjoint : Disjoint A B) (partition : A ∪ B = Finset.univ)
    (cardA : A.card = 13) (cardB : B.card = 13)
    (degree : ∀ a : Fin n, (Finset.univ.filter (G.Adj a)).card = 4)
    (common : ∀ a b : Fin n, a ≠ b →
      ((Finset.univ.filter (G.Adj a)) ∩ (Finset.univ.filter (G.Adj b))).card ≤ 1)
    (ab : ∀ a ∈ A, ∀ b, G.Adj a b → b ∈ B)
    (ba : ∀ b ∈ B, ∀ a, G.Adj b a → a ∈ A)
    (K : Finset (Fin n)) (independent : ∀ u ∈ K, ∀ v ∈ K, ¬ G.Adj u v)
    (cardK : K.card = 12) : K ⊆ A ∨ K ⊆ B := by
  classical
  let P := K ∩ A
  let L := K ∩ B
  let N := fun a : Fin n => Finset.univ.filter (G.Adj a)
  have unite : P ∪ L = K := by
    simp [P, L, ← Finset.inter_union_distrib_left, partition]
  have hd : Disjoint P L := disjoint.mono Finset.inter_subset_right Finset.inter_subset_right
  have hsum : P.card + L.card = 12 := by
    rw [← Finset.card_union_of_disjoint hd, unite, cardK]
  by_cases hp : P.Nonempty
  · by_cases hl : L.Nonempty
    · have hbound := ThreeNeighborBound.mixed_less_twelve N N P A L B degree degree common common
        (by intro a ha b hb; exact ab a (Finset.mem_inter.mp ha).2 b (Finset.mem_filter.mp hb).2)
        (by intro b hb a ha; exact ba b (Finset.mem_inter.mp hb).2 a (Finset.mem_filter.mp ha).2)
        Finset.inter_subset_right Finset.inter_subset_right cardA cardB
        (by
          intro a ha b hb hn
          exact independent a (Finset.mem_inter.mp ha).1 b (Finset.mem_inter.mp hb).1
            (Finset.mem_filter.mp hn).2)
        (by
          intro b hb a ha hn
          exact independent b (Finset.mem_inter.mp hb).1 a (Finset.mem_inter.mp ha).1
            (Finset.mem_filter.mp hn).2) hp hl
      omega
    · have hz := Finset.not_nonempty_iff_eq_empty.mp hl
      have hk : K = P := by simpa [hz] using unite.symm
      exact Or.inl (hk ▸ Finset.inter_subset_right)
  · have hz := Finset.not_nonempty_iff_eq_empty.mp hp
    have hk : K = L := by simpa [hz] using unite.symm
    exact Or.inr (hk ▸ Finset.inter_subset_right)

end PEqualNP.Outside.L_meta_650_aux.TightCoverGeometry

namespace PEqualNP.Outside.L_meta_650_aux.TightCoverGeometry

theorem pure_cover_missing_star {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (A B : Finset (Fin n)) (disjoint : Disjoint A B) (cardA : A.card = 13)
    (across : ∀ a ∈ A, ∀ b, G.Adj a b → b ∈ B)
    (degree : ∀ v : Fin n, (G.edgeFinset.filter fun e => v ∈ e).card = 4)
    (U : Finset (Sym2 (Fin n))) (cardU : U.card = 4)
    (K : Finset (Fin n)) (cardK : K.card = 12) (KA : K ⊆ A)
    (cover : (G.deleteEdges ↑U).IsVertexCover ↑K) :
    ∃ v : Fin n, U = G.edgeFinset.filter (fun e => v ∈ e) := by
  classical
  have hd : (A \ K).card = 1 := by
    rw [Finset.card_sdiff_of_subset KA, cardA, cardK]
  obtain ⟨v, hdiff⟩ := Finset.card_eq_one.mp hd
  have hv : v ∈ A \ K := by rw [hdiff]; simp
  have hvA := (Finset.mem_sdiff.mp hv).1
  have hvK := (Finset.mem_sdiff.mp hv).2
  have sub : G.edgeFinset.filter (fun e => v ∈ e) ⊆ U := by
    intro e he
    obtain ⟨heG, hve⟩ := Finset.mem_filter.mp he
    by_contra hnot
    induction e using Sym2.ind with
    | _ a b =>
      have hab : G.Adj a b := SimpleGraph.mem_edgeFinset.mp heG
      have hvab : v = a ∨ v = b := by simpa using hve
      have hcov : a ∈ K ∨ b ∈ K := cover (SimpleGraph.deleteEdges_adj.mpr ⟨hab, hnot⟩)
      rcases hvab with hva | hvb
      · subst a
        have hbB := across v hvA b hab
        have hbK : b ∉ K := by
          intro hb
          exact Finset.disjoint_left.mp disjoint (KA hb) hbB
        exact hcov.elim hvK hbK
      · subst b
        have haB := across v hvA a hab.symm
        have haK : a ∉ K := by
          intro ha
          exact Finset.disjoint_left.mp disjoint (KA ha) haB
        exact hcov.elim haK hvK
  have heq : G.edgeFinset.filter (fun e => v ∈ e) = U :=
    Finset.eq_of_subset_of_card_le sub (by rw [degree, cardU])
  exact ⟨v, heq.symm⟩

end PEqualNP.Outside.L_meta_650_aux.TightCoverGeometry
