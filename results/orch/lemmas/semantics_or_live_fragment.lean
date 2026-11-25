namespace PEqualNP.Outside.L_meta_2592_aux

lemma or_pair_distinguishes (a b t : Fin 10) (hab : a ≠ b) :
    ∃ x y : Fin 10 → Bool,
      (∀ j, j ≠ t → x j = y j) ∧ (x a || x b) = (y a || y b) ∧
      searchEdge x = false ∧ searchEdge y = true := by
  by_cases hta : t = a
  · subst t
    have h := orPairWitnesses_sound a b hab
    exact ⟨_, _, h⟩
  by_cases htb : t = b
  · subst t
    have h := orPairWitnesses_sound b a (Ne.symm hab)
    exact ⟨_, _, h.1, by simpa [Bool.or_comm] using h.2.1, h.2.2⟩
  have h := andPairWitnesses_sound t a hta
  refine ⟨_, _, h.1, ?_, h.2.2⟩
  rw [h.1 a (Ne.symm hta), h.1 b (Ne.symm htb)]

end PEqualNP.Outside.L_meta_2592_aux

namespace PEqualNP.Outside.L_meta_2592_aux.Binary16

open PEqualNP.Outside.L_meta_2592_aux

lemma encoded_pin_bit (x : Fin 10 → Bool) (j : Fin 10) :
    Extended.bit (RowEncoding.encode x) (inputPin j) = x j := by
  change Extended.assign (RowEncoding.encode x) j = x j
  rw [assign_decode, RowEncoding.decode_encode]

lemma encoded_assignment (x : Fin 10 → Bool) :
    Extended.assign (RowEncoding.encode x) = x := by
  funext j
  exact encoded_pin_bit x j

lemma or_suffix_pin_needed {k : ℕ} {S : Finset Extended.Sig} (a b t : Fin 10)
    (hab : a ≠ b) (run : Extended.Live true Extended.target k S)
    (raw : ∀ v ∈ S, v ∈ Extended.initial ++ [Extended.bin 1 (inputPin a) (inputPin b)]) :
    inputPin t ∈ S := by
  by_contra ht
  obtain ⟨x, y, hagree, hor, hx, hy⟩ := or_pair_distinguishes a b t hab
  have diff : Extended.bit (RowEncoding.encode x) Extended.target ≠
      Extended.bit (RowEncoding.encode y) Extended.target := by
    rw [Extended.rowTarget, Extended.rowTarget, encoded_assignment, encoded_assignment]
    change searchEdge x ≠ searchEdge y
    rw [hx, hy]
    decide
  obtain ⟨v, hv, hchange⟩ := Extended.live_row_difference run diff
  rcases List.mem_append.mp (raw v hv) with hpin | hextra
  · obtain ⟨j, rfl⟩ := member_pin hpin
    have hj : j ≠ t := by intro he; subst j; exact ht hv
    apply hchange
    rw [encoded_pin_bit, encoded_pin_bit]
    exact hagree j hj
  · have he : v = Extended.bin 1 (inputPin a) (inputPin b) := by simpa using hextra
    subst v
    apply hchange
    change (Extended.bit (RowEncoding.encode x) (inputPin a ||| inputPin b)) =
      (Extended.bit (RowEncoding.encode y) (inputPin a ||| inputPin b))
    simp only [Extended.bit, BitVec.getLsbD_or]
    change (Extended.bit (RowEncoding.encode x) (inputPin a) ||
      Extended.bit (RowEncoding.encode x) (inputPin b)) =
      (Extended.bit (RowEncoding.encode y) (inputPin a) ||
      Extended.bit (RowEncoding.encode y) (inputPin b))
    rw [encoded_pin_bit, encoded_pin_bit, encoded_pin_bit, encoded_pin_bit]
    exact hor

lemma or_suffix_roots_exact {k : ℕ} {S : Finset Extended.Sig} (a b : Fin 10)
    (hab : a ≠ b) (run : Extended.Live true Extended.target k S)
    (extra : Extended.bin 1 (inputPin a) (inputPin b) ∈ S)
    (raw : ∀ v ∈ S, v ∈ Extended.initial ++ [Extended.bin 1 (inputPin a) (inputPin b)]) :
    S = insert (Extended.bin 1 (inputPin a) (inputPin b)) Extended.initial.toFinset := by
  ext v
  constructor
  · intro hv
    rcases List.mem_append.mp (raw v hv) with hpin | hextra
    · exact Finset.mem_insert_of_mem (List.mem_toFinset.mpr hpin)
    · have he : v = Extended.bin 1 (inputPin a) (inputPin b) := by simpa using hextra
      exact he ▸ Finset.mem_insert_self _ _
  · intro hv
    rcases Finset.mem_insert.mp hv with rfl | hpin
    · exact extra
    · obtain ⟨j, rfl⟩ := member_pin (List.mem_toFinset.mp hpin)
      exact or_suffix_pin_needed a b j hab run raw

end PEqualNP.Outside.L_meta_2592_aux.Binary16
