
namespace PEqualNP.Outside.L_meta_2962_aux.CountingPathFamily

open PEqualNP.Outside.L_meta_2962_aux.CountingGeometry

/-- A function constant on the fibers of another has no more image values. -/
theorem image_card_of_fibers {ι α β : Type*} [DecidableEq ι]
    [DecidableEq α] [DecidableEq β] (K : Finset ι) (f : ι → α) (g : ι → β)
    (fibers : ∀ i ∈ K, ∀ j ∈ K, g i = g j → f i = f j) :
    (K.image f).card ≤ (K.image g).card := by
  classical
  let lift : (K.image g) → (K.image f) := fun b =>
    ⟨f (Classical.choose (Finset.mem_image.mp b.property)),
      Finset.mem_image_of_mem f (Classical.choose_spec (Finset.mem_image.mp b.property)).1⟩
  apply Finset.card_le_card_of_surjective (f := lift)
  intro a
  obtain ⟨i, hi, hai⟩ := Finset.mem_image.mp a.property
  refine ⟨⟨g i, Finset.mem_image_of_mem g hi⟩, ?_⟩
  apply Subtype.ext
  dsimp [lift]
  let j := Classical.choose (Finset.mem_image.mp (Finset.mem_image_of_mem g hi))
  have hj : j ∈ K ∧ g j = g i :=
    Classical.choose_spec (Finset.mem_image.mp (Finset.mem_image_of_mem g hi))
  exact (fibers j hj.1 i hi hj.2).trans hai

/-- The common-edge and middle-vertex data determine the middle edge. -/
theorem middle_edges_le {ι : Type*} [DecidableEq ι] {n : ℕ}
    (G : SimpleGraph (Fin n)) (s : Fin n → Bool)
    (bipartite : ∀ u v, G.Adj u v → s u ≠ s v)
    (K : Finset ι) (x y z : ι → Fin n)
    (xy : ∀ i ∈ K, G.Adj (x i) (y i))
    (yz : ∀ i ∈ K, G.Adj (y i) (z i)) :
    (K.image (fun i => s(y i, z i))).card ≤
      (K.image (fun i => (s(x i, y i), z i))).card := by
  apply image_card_of_fibers
  intro i hi j hj same
  have edge := congrArg Prod.fst same
  have middle := congrArg Prod.snd same
  rcases Sym2.eq_iff.mp edge with ⟨hxx, hyy⟩ | ⟨hxy, hyx⟩
  · exact congrArg₂ (fun a b => s(a, b)) hyy middle
  · exfalso
    apply no_center_flip G s bipartite (x i) (y i) (z i) (xy i hi) (yz i hi)
    rw [hxy, middle]
    exact yz j hj

/-- The shared two-vertex clause determines its middle vertex. -/
theorem middles_le_clauses {ι : Type*} [DecidableEq ι] {n : ℕ}
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (no_four : PEqualNP.TopForm.NoFourCycle G)
    (K : Finset ι) (y z w : ι → Fin n)
    (different : ∀ i ∈ K, y i ≠ w i)
    (yz : ∀ i ∈ K, G.Adj (y i) (z i))
    (wz : ∀ i ∈ K, G.Adj (w i) (z i)) :
    (K.image z).card ≤ (K.image (fun i => s(y i, w i))).card := by
  apply image_card_of_fibers
  intro i hi j hj same
  rcases Sym2.eq_iff.mp same with ⟨hyy, hww⟩ | ⟨hyw, hwy⟩
  · apply unique_middle G no_four (y i) (w i) (z i) (z j)
      (different i hi) (yz i hi) (wz i hi)
    · rw [hyy]; exact yz j hj
    · rw [hww]; exact wz j hj
  · apply unique_middle G no_four (y i) (w i) (z i) (z j)
      (different i hi) (yz i hi) (wz i hi)
    · rw [hyw]; exact wz j hj
    · rw [hwy]; exact yz j hj

/-- A counting budget for canonical four-gate path-core families. -/
theorem path_family_budget {ι : Type*} [DecidableEq ι] {n : ℕ}
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (s : Fin n → Bool)
    (bipartite : ∀ u v, G.Adj u v → s u ≠ s v)
    (no_four : PEqualNP.TopForm.NoFourCycle G)
    (K : Finset ι) (x y z w : ι → Fin n)
    (different : ∀ i ∈ K, y i ≠ w i)
    (xy : ∀ i ∈ K, G.Adj (x i) (y i))
    (yz : ∀ i ∈ K, G.Adj (y i) (z i))
    (zw : ∀ i ∈ K, G.Adj (z i) (w i)) :
    ((K.image (fun i => s(x i, y i)) ∪ K.image (fun i => s(y i, z i))) ∪
      K.image (fun i => s(z i, w i))).card +
      (K.image y ∪ K.image z).card ≤
    (K.image (fun i => s(x i, y i))).card +
      (K.image (fun i => (s(x i, y i), z i))).card +
      (K.image (fun i => s(y i, w i))).card + 2 * K.card := by
  have hm := middle_edges_le G s bipartite K x y z xy yz
  have hz := middles_le_clauses G no_four K y z w different yz (fun i hi => (zw i hi).symm)
  have he1 := Finset.card_union_le
    (K.image (fun i => s(x i, y i))) (K.image (fun i => s(y i, z i)))
  have he2 := Finset.card_union_le
    (K.image (fun i => s(x i, y i)) ∪ K.image (fun i => s(y i, z i)))
    (K.image (fun i => s(z i, w i)))
  have hlast := Finset.card_image_le (s := K) (f := fun i => s(z i, w i))
  have hys := Finset.card_image_le (s := K) (f := y)
  have hcover := Finset.card_union_le (K.image y) (K.image z)
  omega

end PEqualNP.Outside.L_meta_2962_aux.CountingPathFamily
