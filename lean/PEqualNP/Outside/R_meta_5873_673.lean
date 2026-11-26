import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership PEqualNP.TopForm
open PEqualNP.MetaComplexity.NestedCover

set_option maxRecDepth 10000 in
theorem PEqualNP.Outside.R_meta_5873_673
    (cert :
      let G := edgeGraph 11 ([(0,9),(0,10),(1,4),(1,8),(2,5),(2,10),(3,6),(3,7),
        (4,8),(4,10),(5,8),(5,9),(6,7),(6,10),(7,9),(8,9)] : List (ℕ × ℕ))
      let blocks : List ℕ := [513,1025,18,258,36,1028,72,136,272,1040,288,544,192,1088,640,768,
        274,200,800,1573,1809,1729,1332]
      ∀ (K : Finset (Fin 11)) (q : ℕ), q ≤ 4 →
      (∃ T : Finset (Fin 11), G.IsVertexCover ↑T ∧ (T \ K).card ≤ q) ∨
      ∃ P : List ℕ, P.Pairwise (fun a b => a &&& b = 0) ∧
        (∀ a ∈ P, a ∈ blocks ∧ ∀ i : Fin 11, a.testBit i.val = true → i ∉ K) ∧
        q < (P.map fun a => (a.bitIndices.length + 1) / 2).sum)
    (matchingCharge :
      let G := edgeGraph 11 ([(0,9),(0,10),(1,4),(1,8),(2,5),(2,10),(3,6),(3,7),
        (4,8),(4,10),(5,8),(5,9),(6,7),(6,10),(7,9),(8,9)] : List (ℕ × ℕ))
      let blocks : List ℕ := [513,1025,18,258,36,1028,72,136,272,1040,288,544,192,1088,640,768,
        274,200,800,1573,1809,1729,1332]
      ∀ C : Circuit, C.size ≤ 21 → IsLeastAO G C → TopForm G C → 2 ≤ (junk G C).card →
      let U := Ustar G C
      let B := 2 * (centreless G C).card + (junk G C).card + (orN G C \ lam G C).card
      4 ≤ B → U.card ≤ B → B < 2 * U.card → B - U.card ≤ 4 →
      ∀ K : Finset (Fin 11), IsMinCover (G.deleteEdges ↑U) K → ∀ P : List ℕ,
        P.Pairwise (fun a b => a &&& b = 0) →
        (∀ a ∈ P, a ∈ blocks ∧ ∀ i : Fin 11, a.testBit i.val = true → i ∉ K) →
        (∀ a ∈ P, a.bitIndices.length = 2) →
        (P.map fun a => (a.bitIndices.length + 1) / 2).sum ≤ B - U.card)
    (oddCharge :
      let G := edgeGraph 11 ([(0,9),(0,10),(1,4),(1,8),(2,5),(2,10),(3,6),(3,7),
        (4,8),(4,10),(5,8),(5,9),(6,7),(6,10),(7,9),(8,9)] : List (ℕ × ℕ))
      let blocks : List ℕ := [513,1025,18,258,36,1028,72,136,272,1040,288,544,192,1088,640,768,
        274,200,800,1573,1809,1729,1332]
      ∀ C : Circuit, C.size ≤ 21 → IsLeastAO G C → TopForm G C → 2 ≤ (junk G C).card →
      let U := Ustar G C
      let B := 2 * (centreless G C).card + (junk G C).card + (orN G C \ lam G C).card
      4 ≤ B → U.card ≤ B → B < 2 * U.card → B - U.card ≤ 4 →
      ∀ K : Finset (Fin 11), IsMinCover (G.deleteEdges ↑U) K → ∀ P : List ℕ,
        P.Pairwise (fun a b => a &&& b = 0) →
        (∀ a ∈ P, a ∈ blocks ∧ ∀ i : Fin 11, a.testBit i.val = true → i ∉ K) →
        (∃ a ∈ P, a.bitIndices.length ≠ 2) →
        (P.map fun a => (a.bitIndices.length + 1) / 2).sum ≤ B - U.card)
    (remainingEdges :
      let G := edgeGraph 11 ([(0,9),(0,10),(1,4),(1,8),(2,5),(2,10),(3,6),(3,7),
        (4,8),(4,10),(5,8),(5,9),(6,7),(6,10),(7,9),(8,9)] : List (ℕ × ℕ))
      ∀ C : Circuit, C.size ≤ 21 → IsLeastAO G C → TopForm G C → 2 ≤ (junk G C).card →
      let U := Ustar G C
      let B := 2 * (centreless G C).card + (junk G C).card + (orN G C \ lam G C).card
      let H := G.deleteEdges ↑U
      4 ≤ B → U.card ≤ B → B < 2 * U.card → 5 ≤ B - U.card → B - U.card ≤ 6 →
      (∃ u v : Fin 11, H.Adj u v) ∧
        (B - U.card = 5 → ∀ w : Fin 11, ∃ u v : Fin 11, H.Adj u v ∧ w ≠ u ∧ w ≠ v)) :
    let G := edgeGraph 11 ([(0,9),(0,10),(1,4),(1,8),(2,5),(2,10),(3,6),(3,7),
      (4,8),(4,10),(5,8),(5,9),(6,7),(6,10),(7,9),(8,9)] : List (ℕ × ℕ))
    ∀ C : Circuit, C.size ≤ 21 → IsLeastAO G C → TopForm G C → 2 ≤ (junk G C).card →
    let B := 2 * (centreless G C).card + (junk G C).card + (orN G C \ lam G C).card
    let U := Ustar G C
    4 ≤ B → U.card ≤ B → B < 2 * U.card →
    ∃ K X : Finset (Fin 11), IsMinCover (G.deleteEdges ↑U) K ∧ G.IsVertexCover ↑(K ∪ X) ∧
      X.card ≤ B - U.card := by
  intro G C short least top dirty B U budget lo hi
  let H := G.deleteEdges ↑U
  let q := B - U.card
  have extend {K T : Finset (Fin 11)} (hK : IsMinCover H K) (hT : G.IsVertexCover ↑T)
      (hX : (T \ K).card ≤ q) :
      ∃ K X : Finset (Fin 11), IsMinCover H K ∧ G.IsVertexCover ↑(K ∪ X) ∧ X.card ≤ q := by
    refine ⟨K, T \ K, hK, ?_, hX⟩
    have covered : ∀ v ∈ T, v ∈ K ∪ (T \ K) := by
      intro v hv
      by_cases h : v ∈ K
      · exact Finset.mem_union_left _ h
      · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hv,h⟩)
    intro u v huv
    exact (hT huv).imp (fun h => covered u h) (fun h => covered v h)
  have existsMin : ∃ K : Finset (Fin 11), IsMinCover H K := by
    classical
    let covers (k : ℕ) := ∃ K : Finset (Fin 11), H.IsVertexCover ↑K ∧ K.card = k
    have ex : ∃ k, covers k := ⟨_, Finset.univ, by simp, rfl⟩
    have found : covers (Nat.find ex) := Nat.find_spec ex
    obtain ⟨K,hK,hk⟩ := found
    exact ⟨K, hK, fun T hT => hk.trans_le (Nat.find_min' ex ⟨T,hT,rfl⟩)⟩
  obtain ⟨K,hmin⟩ := existsMin
  by_cases hs : q ≤ 4
  · rcases cert K q hs with ⟨T,hT,hXT⟩ | ⟨P,hP,hblocks,hweight⟩
    · exact extend hmin hT hXT
    by_cases hM : ∀ a ∈ P, a.bitIndices.length = 2
    · exact (Nat.not_lt_of_ge (matchingCharge C short least top dirty budget lo hi hs K hmin P hP hblocks hM) hweight).elim
    · push_neg at hM
      exact (Nat.not_lt_of_ge (oddCharge C short least top dirty budget lo hi hs K hmin P hP hblocks hM) hweight).elim
  have hK := hmin.1
  let family : List (Finset (Fin 11)) :=
    [{0,1,3,5,7,8,10}, {0,2,3,4,6,8,9}, {0,2,4,5,6,7,8}, {1,2,3,6,8,9,10}, {1,3,4,5,7,9,10}]
  have pairHits : ∀ u v : Fin 11, family.any (fun T => decide (u ∈ T ∧ v ∈ T)) = true := by
    decide +kernel
  have familyCovers : ∀ T ∈ family, T.card = 7 ∧ ∀ i j : Fin 11, G.Adj i j → i ∈ T ∨ j ∈ T := by
    intro T hT
    simp only [family, List.mem_cons, List.not_mem_nil, or_false] at hT
    rcases hT with rfl | rfl | rfl | rfl | rfl <;> (dsimp only [G]; decide +kernel)
  have cardSeven (u v : Fin 11) : ∃ T : Finset (Fin 11), T.card = 7 ∧ u ∈ T ∧ v ∈ T ∧
      ∀ i j : Fin 11, G.Adj i j → i ∈ T ∨ j ∈ T := by
    obtain ⟨T,hT,h⟩ := List.any_eq_true.mp (pairHits u v)
    obtain ⟨hu,hv⟩ := of_decide_eq_true h
    exact ⟨T,(familyCovers T hT).1,hu,hv,(familyCovers T hT).2⟩
  have withOverlap {T : Finset (Fin 11)} (hT : T.card = 7)
      (hInt : 7 ≤ q + (T ∩ K).card) : (T \ K).card ≤ q := by
    have hCount := Finset.card_sdiff_add_card_inter T K
    omega
  by_cases h7 : 7 ≤ q
  · obtain ⟨T, ht, _, _, hc⟩ := cardSeven 0 0
    exact extend hmin (by intro u v h; exact hc u v h) (withOverlap ht (by omega))
  have qlo : 5 ≤ q := by omega
  have qhi : q ≤ 6 := by omega
  obtain ⟨⟨u,v,edge⟩, other⟩ := remainingEdges C short least top dirty budget lo hi qlo qhi
  have vertex : K.Nonempty := by
    rcases hK edge with hu | hv
    · exact ⟨u,hu⟩
    · exact ⟨v,hv⟩
  obtain ⟨w,hw⟩ := vertex
  by_cases h6 : q = 6
  · obtain ⟨T,ht,hwT,_,hc⟩ := cardSeven w w
    have one : 1 ≤ (T ∩ K).card := Finset.card_pos.mpr ⟨w, Finset.mem_inter.mpr ⟨hwT,hw⟩⟩
    exact extend hmin (by intro u v h; exact hc u v h) (withOverlap ht (by omega))
  · have h5 : q = 5 := by omega
    obtain ⟨a,b,ab,ha,hb⟩ := other h5 w
    have second : ∃ z ∈ K, z ≠ w := by
      rcases hK ab with haK | hbK
      · exact ⟨a,haK,Ne.symm ha⟩
      · exact ⟨b,hbK,Ne.symm hb⟩
    obtain ⟨z,hz,hzw⟩ := second
    obtain ⟨T,ht,hwT,hzT,hc⟩ := cardSeven w z
    have hpair : ({w,z} : Finset (Fin 11)) ⊆ T ∩ K := by
      intro i hi
      simp only [Finset.mem_insert, Finset.mem_singleton] at hi
      rcases hi with rfl | rfl
      · exact Finset.mem_inter.mpr ⟨hwT,hw⟩
      · exact Finset.mem_inter.mpr ⟨hzT,hz⟩
    have two : 2 ≤ (T ∩ K).card := by
      simpa [Finset.card_pair (Ne.symm hzw)] using Finset.card_le_card hpair
    exact extend hmin (by intro u v h; exact hc u v h) (withOverlap ht (by omega))
