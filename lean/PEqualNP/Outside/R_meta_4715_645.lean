import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Nat.BitIndices
import Mathlib.Tactic.FinCases
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.EdgeOwnership PEqualNP.MetaComplexity.NestedCover

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem PEqualNP.Outside.R_meta_4715_645
    (low : let G := edgeGraph 11 [(0,9),(0,10),(1,4),(1,8),(2,5),(2,10),(3,6),(3,7),(4,8),(4,10),(5,8),(5,9),(6,7),(6,10),(7,9),(8,9)]
      let blocks : List Nat := [513,1025,18,258,36,1028,72,136,272,1040,288,544,192,1088,640,768,274,200,800,1573,1809,1729,1332]
      ∀ C : Circuit, C.size ≤ 21 → IsLeastAO G C → TopForm G C → 2 ≤ (junk G C).card →
      let U := Ustar G C
      let B := 2*(centreless G C).card + (junk G C).card + (orN G C \ lam G C).card
      U.card ≤ B → B < 2*U.card → B-U.card < 7 →
      B-U.card ≤ 4 → ∃ K : Finset (Fin 11), IsMinCover (G.deleteEdges ↑U) K ∧
        ∀ P : List Nat, List.Pairwise (fun a b => a &&& b = 0) P →
        (∀ b ∈ P, b ∈ blocks ∧ ∀ v ∈ K, b.testBit v.val = false) →
        (P.map fun b => (b.bitIndices.length + 1)/2).sum ≤ B-U.card)
    (small : let G := edgeGraph 11 [(0,9),(0,10),(1,4),(1,8),(2,5),(2,10),(3,6),(3,7),(4,8),(4,10),(5,8),(5,9),(6,7),(6,10),(7,9),(8,9)]
      let blocks : List Nat := [513,1025,18,258,36,1028,72,136,272,1040,288,544,192,1088,640,768,274,200,800,1573,1809,1729,1332]
      ∀ C : Circuit, C.size ≤ 21 → IsLeastAO G C → TopForm G C → 2 ≤ (junk G C).card →
      let U := Ustar G C
      let B := 2*(centreless G C).card + (junk G C).card + (orN G C \ lam G C).card
      U.card ≤ B → B < 2*U.card → B-U.card < 7 →
      5 ≤ B-U.card →
      (∃ K : Finset (Fin 11), IsMinCover (G.deleteEdges ↑U) K ∧ K.card + (B-U.card) ≤ 6) →
      ∃ K : Finset (Fin 11), IsMinCover (G.deleteEdges ↑U) K ∧
        ∀ P : List Nat, List.Pairwise (fun a b => a &&& b = 0) P →
        (∀ b ∈ P, b ∈ blocks ∧ ∀ v ∈ K, b.testBit v.val = false) →
        (P.map fun b => (b.bitIndices.length + 1)/2).sum ≤ B-U.card) :
    (let x1 : SimpleGraph (Fin (11 : ℕ)) := PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) [((0 : ℕ), (9 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (4 : ℕ)), ((1 : ℕ), (8 : ℕ)), ((2 : ℕ), (5 : ℕ)), ((2 : ℕ), (10 : ℕ)), ((3 : ℕ), (6 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((4 : ℕ), (8 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((5 : ℕ), (8 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((6 : ℕ), (7 : ℕ)), ((6 : ℕ), (10 : ℕ)), ((7 : ℕ), (9 : ℕ)), ((8 : ℕ), (9 : ℕ))]; have x2 : List ℕ := [(513 : ℕ), (1025 : ℕ), (18 : ℕ), (258 : ℕ), (36 : ℕ), (1028 : ℕ), (72 : ℕ), (136 : ℕ), (272 : ℕ), (1040 : ℕ), (288 : ℕ), (544 : ℕ), (192 : ℕ), (1088 : ℕ), (640 : ℕ), (768 : ℕ), (274 : ℕ), (200 : ℕ), (800 : ℕ), (1573 : ℕ), (1809 : ℕ), (1729 : ℕ), (1332 : ℕ)]; ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit),   x3.size ≤ (21 : ℕ) →     PEqualNP.TopForm.IsLeastAO x1 x3 →       PEqualNP.TopForm.TopForm x1 x3 →         (2 : ℕ) ≤ (PEqualNP.TopForm.junk x1 x3).card →           have x8 : Finset (Sym2 (Fin (11 : ℕ))) := PEqualNP.TopForm.Ustar x1 x3;           have x9 : ℕ := (2 : ℕ) * (PEqualNP.TopForm.centreless x1 x3).card + (PEqualNP.TopForm.junk x1 x3).card + (PEqualNP.TopForm.orN x1 x3 \ PEqualNP.TopForm.lam x1 x3).card;           x8.card ≤ x9 → x9 < (2 : ℕ) * x8.card → x9 - x8.card < (7 : ℕ) → ∃ (x13 : Finset (Fin (11 : ℕ))), PEqualNP.MetaComplexity.NestedCover.IsMinCover (x1.deleteEdges ↑x8) x13 ∧ ∀ (x14 : List ℕ), List.Pairwise (fun (x15 x16 : ℕ) => x15 &&& x16 = (0 : ℕ)) x14 → (∀ x16 ∈ x14, x16 ∈ x2 ∧ ∀ x18 ∈ x13, x16.testBit ↑x18 = Bool.false) → (List.map (fun (x17 : ℕ) => (x17.bitIndices.length + (1 : ℕ)) / (2 : ℕ)) x14).sum ≤ x9 - x8.card) := by
  have pack :
      ∀ (P : List Nat) (X : Finset (Fin 11)),
        List.Pairwise (fun a b => a &&& b = 0) P →
        (∀ b ∈ P,
          (b.bitIndices.length + 1) / 2 ≤ (X.filter fun v => b.testBit v.val).card) →
        (P.map fun b => (b.bitIndices.length + 1) / 2).sum ≤ X.card := by
    intro P
    induction P with
    | nil =>
        intro X _ _
        simp
    | cons b bs ih =>
        intro X hpair hweight
        rw [List.pairwise_cons] at hpair
        rcases hpair with ⟨hhead, htail⟩
        let A : Finset (Fin 11) := X.filter fun v => b.testBit v.val
        have hAsub : A ⊆ X := Finset.filter_subset _ _
        have hheadWeight : (b.bitIndices.length + 1) / 2 ≤ A.card := by
          exact hweight b (by simp)
        have hmaskDisjoint : ∀ c ∈ bs,
            Disjoint A (X.filter fun v => c.testBit v.val) := by
          intro c hc
          apply Finset.disjoint_left.mpr
          intro v hvA hvC
          have hb : b.testBit v.val = true := (Finset.mem_filter.mp hvA).2
          have hcbit : c.testBit v.val = true := (Finset.mem_filter.mp hvC).2
          have hbits : (b &&& c).testBit v.val = true := by
            simp [Nat.testBit_and, hb, hcbit]
          rw [hhead c hc] at hbits
          simp at hbits
        have hfilterEq (c : ℕ) (hc : c ∈ bs) :
            (X \ A).filter (fun v => c.testBit v.val) =
              X.filter (fun v => c.testBit v.val) := by
          ext v
          constructor
          · intro hv
            have hmem := Finset.mem_filter.mp hv
            exact Finset.mem_filter.mpr
              ⟨(Finset.mem_sdiff.mp hmem.1).1, hmem.2⟩
          · intro hv
            have hmem := Finset.mem_filter.mp hv
            have hrem : v ∈ X \ A := by
              refine Finset.mem_sdiff.mpr ⟨hmem.1, ?_⟩
              intro hvA
              exact Finset.disjoint_left.mp (hmaskDisjoint c hc) hvA hv
            exact Finset.mem_filter.mpr ⟨hrem, hmem.2⟩
        have hweightTail : ∀ c ∈ bs,
            (c.bitIndices.length + 1) / 2 ≤
              ((X \ A).filter fun v => c.testBit v.val).card := by
          intro c hc
          have h := hweight c (by simp [hc])
          rw [hfilterEq c hc]
          exact h
        have htailBound := ih (X \ A) htail hweightTail
        have hcard : (X \ A).card + A.card = X.card :=
          Finset.card_sdiff_add_card_eq_card hAsub
        simp only [List.map_cons, List.sum_cons]
        omega
  let blocks : List Nat := [513,1025,18,258,36,1028,72,136,272,1040,288,544,192,1088,640,768,274,200,800,1573,1809,1729,1332]
  let W1 : List Nat := [500,1449,497,853,485,469,437,373,245,349,427]
  let W2 : List Nat := [0,1448,496,852,484,468,436,372,244,348,426,1448,0,1864,1441,1640,1417,1441,1321,1193,1144,425,496,1864,0,849,481,465,433,369,241,345,842,852,1441,849,0,837,1411,789,1315,597,341,419,484,1640,481,837,0,453,421,357,229,333,425,468,1417,465,1411,453,0,405,341,213,1114,395,436,1441,433,789,421,405,0,309,181,285,419,372,1321,369,1315,357,341,309,0,117,341,299,244,1193,241,597,229,213,181,117,0,93,171,348,1144,345,341,333,1114,285,341,93,0,122,426,425,842,419,425,395,419,299,171,122,0]
  have one : ∀ u : Fin 11,
      let X := Finset.univ.filter (fun v : Fin 11 => (W1[u.val]!).testBit v.val)
      X.card ≤ 6 ∧ ∀ b ∈ blocks, b.testBit u.val = false →
        (b.bitIndices.length + 1)/2 ≤ (X.filter fun v => b.testBit v.val).card := by
    intro u
    fin_cases u <;> decide +kernel
  have two : ∀ u v : Fin 11, u ≠ v →
      let X := Finset.univ.filter (fun w : Fin 11 => (W2[u.val*11+v.val]!).testBit w.val)
      X.card ≤ 5 ∧ ∀ b ∈ blocks, b.testBit u.val = false → b.testBit v.val = false →
        (b.bitIndices.length + 1)/2 ≤ (X.filter fun w => b.testBit w.val).card := by
    intro u v huv
    fin_cases u <;> fin_cases v <;> first | exact (huv rfl).elim | decide +kernel
  dsimp only
  let G := edgeGraph 11 [(0,9),(0,10),(1,4),(1,8),(2,5),(2,10),(3,6),(3,7),(4,8),(4,10),(5,8),(5,9),(6,7),(6,10),(7,9),(8,9)]
  intro C hsize hleast htop hjunk
  let U := Ustar G C
  let B := 2*(centreless G C).card + (junk G C).card + (orN G C \ lam G C).card
  change U.card ≤ B → B < 2*U.card → B-U.card < 7 → _
  intro hlow hhigh hbudget
  by_cases hr : B-U.card ≤ 4
  · exact low C hsize hleast htop hjunk hlow hhigh hbudget hr
  have rge : 5 ≤ B-U.card := by omega
  classical
  let H := G.deleteEdges (↑U)
  let Q (k : Nat) := ∃ K : Finset (Fin 11), H.IsVertexCover (↑K) ∧ K.card = k
  have ex : ∃ k, Q k := ⟨_, Finset.univ, by simp [H], rfl⟩
  obtain ⟨K, hk, card⟩ := Nat.find_spec ex
  have least : IsMinCover H K := ⟨hk, fun T ht => card.trans_le (Nat.find_min' ex ⟨T,ht,rfl⟩)⟩
  by_cases little : K.card + (B-U.card) ≤ 6
  · exact small C hsize hleast htop hjunk hlow hhigh hbudget rge ⟨K,least,little⟩
  refine ⟨K,least,?_⟩
  intro P hp good
  by_cases r6 : B-U.card = 6
  · have kne : K.Nonempty := Finset.card_pos.mp (by omega)
    obtain ⟨u,hu⟩ := kne
    have cert := one u
    exact (pack P _ hp (fun b hb => cert.2 b (good b hb).1 ((good b hb).2 u hu))).trans
      (cert.1.trans (Nat.le_of_eq r6.symm))
  · have k2 : 1 < K.card := by omega
    obtain ⟨u,hu,v,hv,huv⟩ := Finset.one_lt_card.mp k2
    have cert := two u v huv
    exact (pack P _ hp (fun b hb => cert.2 b (good b hb).1
      ((good b hb).2 u hu) ((good b hb).2 v hv))).trans (cert.1.trans rge)
