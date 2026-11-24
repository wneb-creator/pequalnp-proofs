import FirstOrbitBase
namespace PEqualNP.Outside.L_meta_670_aux.FirstOrbit
open LiveCheck LiteralBinary

lemma literal_sign {a : Sig} (ha : a ∈ literals) :
    a = raw.getD (LiteralBinary.index a).val zero ∨
      a = neg (raw.getD (LiteralBinary.index a).val zero) := by
  have hc : literals.all (fun a =>
      (a == raw.getD (LiteralBinary.index a).val zero) ||
      (a == neg (raw.getD (LiteralBinary.index a).val zero))) = true := by
    decide +kernel
  simpa only [Bool.or_eq_true, beq_iff_eq] using List.all_eq_true.mp hc a ha

lemma raw_literal : ∀ i : Fin 9, raw.getD i.val zero ∈ literals := by decide +kernel

lemma signed_indices : ∀ i : Fin 9,
    LiteralBinary.index (raw.getD i.val zero) = i ∧
      LiteralBinary.index (neg (raw.getD i.val zero)) = i := by decide +kernel

lemma action_literal (g : Fin 12) {a : Sig} (ha : a ∈ literals) :
    action g a ∈ literals := by
  rcases literal_sign ha with h | h
  · rw [h, ← rawImage_eq]
    exact raw_literal _
  · rw [h, action_neg, ← rawImage_eq]
    exact neg_literal (raw_literal _)

lemma action_index (g : Fin 12) {a : Sig} (ha : a ∈ literals) :
    LiteralBinary.index (action g a) = rawSym g (LiteralBinary.index a) := by
  rcases literal_sign ha with h | h
  · conv_lhs => rw [h, ← rawImage_eq]
    exact (signed_indices _).1
  · conv_lhs => rw [h, action_neg, ← rawImage_eq]
    exact (signed_indices _).2

lemma bin_swap (d : Bool) (a b : Sig) : bin d a b = bin d b a := by
  cases d <;> simp [bin, BitVec.and_comm, BitVec.or_comm]

lemma constant_pair (d : Bool) (a : Sig) : ¬ proper (bin d a (neg a)) := by
  cases d <;> simp [bin, neg, proper, zero, one, top]

lemma indices_distinct {a b : Sig} {d : Bool}
    (ha : a ∈ literals) (hb : b ∈ literals) (hab : a ≠ b)
    (hp : proper (bin d a b)) : LiteralBinary.index a ≠ LiteralBinary.index b := by
  intro hi
  obtain ha' | ha' := literal_sign ha
  · obtain hb' | hb' := literal_sign hb
    · exact hab (ha'.trans (by simpa [← hi] using hb'.symm))
    · have hb'' : b = neg a := by rw [hb', ← hi, ← ha']
      rw [hb''] at hp
      exact constant_pair d a hp
  · obtain hb' | hb' := literal_sign hb
    · have ha'' : a = neg b := by rw [ha', hi, ← hb']
      rw [bin_swap, ha''] at hp
      exact constant_pair d b hp
    · exact hab (ha'.trans (by simpa [← hi] using hb'.symm))

lemma live_proper {k t : Nat} {S : Finset Sig} (h : Live k t S) :
    ∀ a ∈ S, proper a := by
  induction h with
  | stop =>
      have hp : proper target := by unfold proper target zero one top; decide
      simpa using hp
  | unary ha hf tail ih =>
      simpa using And.intro ha (fun a h => ih a (Finset.mem_insert_of_mem h))
  | binary ha hb hab hf tail ih =>
      simp only [Finset.forall_mem_insert]
      exact ⟨ha, hb, fun a h => ih a (Finset.mem_insert_of_mem h)⟩

lemma first_cut {k t : Nat} {U : Finset Sig} {a b : Sig} {d : Bool}
    (ha : a ∈ literals) (hb : b ∈ literals) (hab : a ≠ b)
    (hu : ∀ z ∈ U, z ∈ literals) (hf : bin d a b ∉ U)
    (h : Live k t (insert (bin d a b) U)) :
    ∃ a' b' : Sig, ∃ U' : Finset Sig,
      a' ∈ literals ∧ b' ∈ literals ∧ a' ≠ b' ∧
      (LiteralBinary.index a', LiteralBinary.index b') ∈ pairReps ∧
      (∀ z ∈ U', z ∈ literals) ∧ U'.card = U.card ∧
      bin d a' b' ∉ U' ∧ Live k t (insert (bin d a' b') U') := by
  have hi := indices_distinct ha hb hab (live_proper h _ (Finset.mem_insert_self _ _))
  obtain ⟨g, hg⟩ := pair_orbits (LiteralBinary.index a) (LiteralBinary.index b) hi
  have htail : Live k t (insert (bin d (action g a) (action g b)) (U.image (action g))) := by
    simpa only [Finset.image_insert, action_bin] using live_action h g
  have hual : ∀ z ∈ U.image (action g), z ∈ literals := by
    intro z hz
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hz
    exact action_literal g (hu x hx)
  have hc : (U.image (action g)).card = U.card := Finset.card_image_of_injective _ (action_injective g)
  have hne : action g a ≠ action g b := fun he => hab (action_injective g he)
  have hf' : bin d (action g a) (action g b) ∉ U.image (action g) := by
    rw [← action_bin]
    intro hx
    obtain ⟨z, hz, he⟩ := Finset.mem_image.mp hx
    exact hf ((action_injective g he) ▸ hz)
  rcases hg with hg | hg
  · refine ⟨action g a, action g b, U.image (action g), action_literal g ha,
      action_literal g hb, hne, ?_, hual, hc, hf', htail⟩
    simpa only [action_index g ha, action_index g hb] using hg
  · refine ⟨action g b, action g a, U.image (action g), action_literal g hb,
      action_literal g ha, Ne.symm hne, ?_, hual, hc, ?_, ?_⟩
    · simpa only [action_index g ha, action_index g hb] using hg
    · simpa only [bin_swap d (action g b) (action g a)] using hf'
    · simpa only [bin_swap d (action g b) (action g a)] using htail

end PEqualNP.Outside.L_meta_670_aux.FirstOrbit

#print axioms PEqualNP.Outside.L_meta_670_aux.FirstOrbit.first_cut
