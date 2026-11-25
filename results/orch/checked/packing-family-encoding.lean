import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1896_aux.PackingFamilies

variable {V R I A : Type*} [DecidableEq V] [DecidableEq I]

noncomputable def Valid (vertices : I → Finset V) (rows : R → V → Bool)
    (capacity : Nat) (family : Finset I) : Prop := by
  classical
  exact (family : Set I).PairwiseDisjoint vertices ∧
    ∀ r : R, (family.filter fun i => ∃ v ∈ vertices i, rows r v = true).card ≤ capacity

noncomputable def removed [Fintype A] (vertices : I → Finset V)
    (flags : A → V → Bool) (family : Finset I) : Finset A := by
  classical
  exact Finset.univ.filter fun a => ∃ v ∈ family.biUnion vertices, flags a v = true

lemma encode_blocks (vertices : I → Finset V) (rows : R → V → Bool)
    (complete : ∀ B : Finset V, B.Nonempty → B.card ≤ 2 → ∃ i : I, vertices i = B)
    (blocks : Finset (Finset V))
    (hne : ∀ B ∈ blocks, B.Nonempty) (hsize : ∀ B ∈ blocks, B.card ≤ 2)
    (hdis : (blocks : Set (Finset V)).PairwiseDisjoint id)
    (capacity : Nat)
    (hcap : ∀ r : R, (blocks.filter fun B => ∃ v ∈ B, rows r v = true).card ≤ capacity) :
    ∃ family : Finset I, Valid vertices rows capacity family ∧
      family.card = blocks.card ∧ family.biUnion vertices = blocks.biUnion id := by
  classical
  have hw : ∀ B : {B : Finset V // B ∈ blocks}, ∃ i : I, vertices i = B.val := by
    intro B
    exact complete B.val (hne B.val B.property) (hsize B.val B.property)
  choose f hf using hw
  have hinj : Function.Injective f := by
    intro B D he
    apply Subtype.ext
    exact (hf B).symm.trans ((congrArg vertices he).trans (hf D))
  let family := blocks.attach.image f
  have hcard : family.card = blocks.card := by
    rw [Finset.card_image_of_injective _ hinj]
    exact Finset.card_attach
  have hunion : family.biUnion vertices = blocks.biUnion id := by
    ext v
    constructor
    · intro hv
      obtain ⟨i, hi, hvi⟩ := Finset.mem_biUnion.mp hv
      obtain ⟨B, hB, rfl⟩ := Finset.mem_image.mp hi
      exact Finset.mem_biUnion.mpr ⟨B.val, B.property, by simpa [hf B] using hvi⟩
    · intro hv
      obtain ⟨B, hB, hvB⟩ := Finset.mem_biUnion.mp hv
      refine Finset.mem_biUnion.mpr ⟨f ⟨B, hB⟩, ?_, ?_⟩
      · exact Finset.mem_image.mpr ⟨⟨B, hB⟩, Finset.mem_attach _ _, rfl⟩
      · simpa [hf ⟨B, hB⟩] using hvB
  have hpair : (family : Set I).PairwiseDisjoint vertices := by
    intro i hi j hj hij
    obtain ⟨B, hB, rfl⟩ := Finset.mem_image.mp hi
    obtain ⟨D, hD, rfl⟩ := Finset.mem_image.mp hj
    change Disjoint (vertices (f B)) (vertices (f D))
    rw [hf B, hf D]
    apply hdis B.property D.property
    intro he
    exact hij (congrArg f (Subtype.ext he))
  have hcounts (r : R) :
      (family.filter fun i => ∃ v ∈ vertices i, rows r v = true).card =
        (blocks.filter fun B => ∃ v ∈ B, rows r v = true).card := by
    symm
    refine Finset.card_bij (fun B hB => f ⟨B, (Finset.mem_filter.mp hB).1⟩) ?_ ?_ ?_
    · intro B hB
      have hb := (Finset.mem_filter.mp hB).1
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_image.mpr ⟨⟨B, hb⟩, Finset.mem_attach _ _, rfl⟩, ?_⟩
      simpa [hf ⟨B, hb⟩] using (Finset.mem_filter.mp hB).2
    · intro B hB D hD he
      exact congrArg Subtype.val (hinj he)
    · intro i hi
      obtain ⟨him, hit⟩ := Finset.mem_filter.mp hi
      obtain ⟨B, hB, rfl⟩ := Finset.mem_image.mp him
      have htouch : ∃ v ∈ B.val, rows r v = true := by simpa [hf B] using hit
      exact ⟨B.val, Finset.mem_filter.mpr ⟨B.property, htouch⟩, rfl⟩
  refine ⟨family, ⟨hpair, ?_⟩, hcard, hunion⟩
  intro r
  rw [hcounts]
  exact hcap r

end PEqualNP.Outside.L_meta_1896_aux.PackingFamilies
