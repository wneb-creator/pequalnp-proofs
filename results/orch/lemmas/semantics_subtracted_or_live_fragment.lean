namespace PEqualNP.Outside.L_meta_2592_aux

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
lemma neighbor_outside_pair : ∀ a b c : Fin 10, ∃ v : Fin 10,
    v ≠ a ∧ v ≠ b ∧ v ≠ c ∧
    searchEdge (fun j => decide (j = v)) = false ∧
    searchEdge (fun j => decide (j = v ∨ j = c)) = true := by
  decide

lemma subtracted_or_distinguishes (a b c t : Fin 10)
    (hab : a ≠ b) (hca : c ≠ a) (hcb : c ≠ b) :
    ∃ x y : Fin 10 → Bool,
      (∀ j, j ≠ t → x j = y j) ∧
      (x a || x b) = (y a || y b) ∧
      ((x a || x b) && !x c) = ((y a || y b) && !y c) ∧
      searchEdge x = false ∧ searchEdge y = true := by
  by_cases htc : t = c
  · subst t
    obtain ⟨v, hva, hvb, hvc, hx, hy⟩ := neighbor_outside_pair a b c
    refine ⟨(fun j => decide (j = v)), (fun j => decide (j = v ∨ j = c)), ?_, ?_, ?_, hx, hy⟩
    · intro j hj
      simp [hj]
    · simp [Ne.symm hva, Ne.symm hvb, Ne.symm hca, Ne.symm hcb]
    · simp [Ne.symm hva, Ne.symm hvb, Ne.symm hca, Ne.symm hcb]
  · obtain ⟨x, y, hagree, hor, hx, hy⟩ := or_pair_distinguishes a b t hab
    refine ⟨x, y, hagree, hor, ?_, hx, hy⟩
    rw [hor, hagree c (Ne.symm htc)]

end PEqualNP.Outside.L_meta_2592_aux

namespace PEqualNP.Outside.L_meta_2592_aux.Binary16

open PEqualNP.Outside.L_meta_2592_aux

lemma subtracted_or_suffix_pin_needed {k : ℕ} {S : Finset Extended.Sig}
    (a b c t : Fin 10) (hab : a ≠ b) (hca : c ≠ a) (hcb : c ≠ b)
    (run : Extended.Live true Extended.target k S)
    (raw : ∀ v ∈ S, v ∈ Extended.initial ++
      [Extended.bin 1 (inputPin a) (inputPin b),
        Extended.bin 2 (Extended.bin 1 (inputPin a) (inputPin b)) (inputPin c)]) :
    inputPin t ∈ S := by
  by_contra ht
  obtain ⟨x, y, hagree, hor, hsub, hx, hy⟩ :=
    subtracted_or_distinguishes a b c t hab hca hcb
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
  · rcases List.mem_cons.mp hextra with rfl | hlast
    · apply hchange
      change (Extended.bit (RowEncoding.encode x) (inputPin a ||| inputPin b)) =
        (Extended.bit (RowEncoding.encode y) (inputPin a ||| inputPin b))
      simp only [Extended.bit, BitVec.getLsbD_or]
      change (Extended.bit (RowEncoding.encode x) (inputPin a) ||
        Extended.bit (RowEncoding.encode x) (inputPin b)) =
        (Extended.bit (RowEncoding.encode y) (inputPin a) ||
        Extended.bit (RowEncoding.encode y) (inputPin b))
      rw [encoded_pin_bit, encoded_pin_bit, encoded_pin_bit, encoded_pin_bit]
      exact hor
    · have he : v = Extended.bin 2
          (Extended.bin 1 (inputPin a) (inputPin b)) (inputPin c) := by simpa using hlast
      subst v
      apply hchange
      change Extended.bit (RowEncoding.encode x) ((inputPin a ||| inputPin b) &&& ~~~inputPin c) =
        Extended.bit (RowEncoding.encode y) ((inputPin a ||| inputPin b) &&& ~~~inputPin c)
      simp only [Extended.bit, BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_not,
        Fin.isLt, decide_true, Bool.true_and]
      change ((Extended.bit (RowEncoding.encode x) (inputPin a) ||
        Extended.bit (RowEncoding.encode x) (inputPin b)) &&
        !Extended.bit (RowEncoding.encode x) (inputPin c)) =
        ((Extended.bit (RowEncoding.encode y) (inputPin a) ||
        Extended.bit (RowEncoding.encode y) (inputPin b)) &&
        !Extended.bit (RowEncoding.encode y) (inputPin c))
      rw [encoded_pin_bit, encoded_pin_bit, encoded_pin_bit,
        encoded_pin_bit, encoded_pin_bit, encoded_pin_bit]
      exact hsub

lemma subtracted_or_suffix_roots {k : ℕ} {S : Finset Extended.Sig}
    (a b c : Fin 10) (hab : a ≠ b) (hca : c ≠ a) (hcb : c ≠ b)
    (run : Extended.Live true Extended.target k S)
    (extra : Extended.bin 2 (Extended.bin 1 (inputPin a) (inputPin b)) (inputPin c) ∈ S)
    (raw : ∀ v ∈ S, v ∈ Extended.initial ++
      [Extended.bin 1 (inputPin a) (inputPin b),
        Extended.bin 2 (Extended.bin 1 (inputPin a) (inputPin b)) (inputPin c)]) :
    ∃ keep : Bool, S = insert
      (Extended.bin 2 (Extended.bin 1 (inputPin a) (inputPin b)) (inputPin c))
      (if keep then insert (Extended.bin 1 (inputPin a) (inputPin b)) Extended.initial.toFinset
        else Extended.initial.toFinset) := by
  classical
  let seed := Extended.bin 1 (inputPin a) (inputPin b)
  refine ⟨decide (seed ∈ S), ?_⟩
  ext v
  constructor
  · intro hv
    rcases List.mem_append.mp (raw v hv) with hpin | hextra
    · apply Finset.mem_insert_of_mem
      split_ifs
      · exact Finset.mem_insert_of_mem (List.mem_toFinset.mpr hpin)
      · exact List.mem_toFinset.mpr hpin
    · rcases List.mem_cons.mp hextra with rfl | hlast
      · apply Finset.mem_insert_of_mem
        have hs : seed ∈ S := hv
        change seed ∈ (if decide (seed ∈ S) then insert seed Extended.initial.toFinset
          else Extended.initial.toFinset)
        simp only [decide_eq_true_eq, hs, ite_true, Finset.mem_insert_self]
      · have he : v = Extended.bin 2 seed (inputPin c) := by simpa [seed] using hlast
        exact he ▸ Finset.mem_insert_self _ _
  · intro hv
    rcases Finset.mem_insert.mp hv with rfl | hpin
    · exact extra
    split_ifs at hpin with hseed
    · rcases Finset.mem_insert.mp hpin with rfl | hpin
      · simpa [seed] using hseed
      · obtain ⟨j, rfl⟩ := member_pin (List.mem_toFinset.mp hpin)
        exact subtracted_or_suffix_pin_needed a b c j hab hca hcb run raw
    · obtain ⟨j, rfl⟩ := member_pin (List.mem_toFinset.mp hpin)
      exact subtracted_or_suffix_pin_needed a b c j hab hca hcb run raw

end PEqualNP.Outside.L_meta_2592_aux.Binary16
