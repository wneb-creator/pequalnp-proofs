import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2585

open PEqualNP.CircuitLowerBounds

lemma single_point_replacement (L : ℕ) (I : Fin 1 → Fin L → Prop)
    [DecidableRel I] (C : Circuit) (hC : PEqualNP.TopForm.IsAO2 (1 + L) C)
    (hf : ∀ y : Fin (1 + L) → Bool,
      PEqualNP.MetaComplexity.circuitFun (1 + L) C y =
        decide (∃ p : Fin 1, ∃ l : Fin L, I p l ∧
          y (Fin.castAdd L p) = true ∧ y (Fin.natAdd 1 l) = true)) :
    ∃ D : Circuit, PEqualNP.TopForm.IsAO2 (1 + L) D ∧
      (∀ y : Fin (1 + L) → Bool,
        PEqualNP.MetaComplexity.circuitFun (1 + L) D y =
          decide (∃ p : Fin 1, ∃ l : Fin L, I p l ∧
            y (Fin.castAdd L p) = true ∧ y (Fin.natAdd 1 l) = true)) ∧
      D.size ≤ C.size ∧ PEqualNP.ReadK.IsReadK (1 + L) D 1 := by
  let N : Finset (Fin L) := Finset.univ.filter (fun l => I 0 l)
  let ls : List (Fin L) := N.toList
  have memls (l : Fin L) : l ∈ ls ↔ I 0 l := by simp [ls, N]
  cases hls : ls with
  | nil =>
    apply empty_incidence_replacement 1 L I C
    intro p l hi
    have hp : p = 0 := Subsingleton.elim _ _
    subst p
    have hl := (memls l).2 hi
    simp [hls] at hl
  | cons a bs =>
    have hIa : I 0 a := (memls a).1 (by simp [hls])
    let ns := bs.map (fun l : Fin L => 1 + l.val)
    have hna : 1 + a.val < 1 + L := by omega
    have hns : ∀ b ∈ ns, b < 1 + L := by
      intro b hb
      obtain ⟨l, _, rfl⟩ := List.mem_map.mp hb
      omega
    let D := Star.starCircuit (1 + L) 0 (1 + a.val) ns
    have hDvalid : PEqualNP.TopForm.IsAO2 (1 + L) D :=
      Star.starCircuit_valid (1 + L) 0 (1 + a.val) ns (by omega) hna hns
    have hDread : PEqualNP.ReadK.IsReadK (1 + L) D 1 := by
      apply Star.starCircuit_read_one (1 + L) 0 (1 + a.val) ns (by omega) hna hns
      intro b hb
      rcases List.mem_cons.mp hb with rfl | hb
      · omega
      · obtain ⟨l, _, rfl⟩ := List.mem_map.mp hb
        omega
    have hDfun (y : Fin (1 + L) → Bool) :
        PEqualNP.MetaComplexity.circuitFun (1 + L) D y =
          decide (∃ p : Fin 1, ∃ l : Fin L, I p l ∧
            y (Fin.castAdd L p) = true ∧ y (Fin.natAdd 1 l) = true) := by
      have getp : (List.ofFn y).getD 0 false = y (Fin.castAdd L (0 : Fin 1)) := by
        simp [List.getD_eq_getElem?_getD]
        rfl
      have getl (l : Fin L) : (List.ofFn y).getD (1 + l.val) false = y (Fin.natAdd 1 l) := by
        rw [List.getD_eq_getElem _ _ (by simpa using l.isLt), List.getElem_ofFn]
        rfl
      change (Star.starCircuit (1 + L) 0 (1 + a.val) ns).eval (List.ofFn y) = _
      rw [Star.starCircuit_eval (1 + L) 0 (1 + a.val) ns (by omega) hna hns _ (by simp), getp, getl]
      apply Bool.eq_iff_iff.mpr
      simp only [Bool.and_eq_true, Bool.or_eq_true, List.any_eq_true, decide_eq_true_eq]
      constructor
      · rintro ⟨hp, ha | ⟨b, hb, hby⟩⟩
        · exact ⟨0, a, hIa, hp, ha⟩
        · obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hb
          rw [getl] at hby
          exact ⟨0, l, (memls l).1 (by simp [hls, hl]), hp, hby⟩
      · rintro ⟨p, l, hi, hp, hl⟩
        have hpeq : p = 0 := Subsingleton.elim _ _
        subst p
        refine ⟨hp, ?_⟩
        have hmem : l ∈ a :: bs := by simpa only [hls] using (memls l).2 hi
        rcases List.mem_cons.mp hmem with rfl | hmem
        · exact Or.inl hl
        · exact Or.inr ⟨1 + l.val, List.mem_map.mpr ⟨l, hmem, rfl⟩, by rw [getl]; exact hl⟩
    let A : Finset (Fin (1 + L)) :=
      insert (Fin.castAdd L (0 : Fin 1)) (N.image (Fin.natAdd 1))
    have hinj : Function.Injective (Fin.natAdd 1 : Fin L → Fin (1 + L)) := by
      intro l m h
      apply Fin.ext
      have hv := congrArg Fin.val h
      change 1 + l.val = 1 + m.val at hv
      omega
    have hnot : Fin.castAdd L (0 : Fin 1) ∉ N.image (Fin.natAdd 1) := by
      intro h
      obtain ⟨l, _, hl⟩ := Finset.mem_image.mp h
      exact Support.cast_ne_nat (0 : Fin 1) l hl.symm
    have hAcard : A.card = N.card + 1 := by
      rw [Finset.card_insert_of_notMem hnot, Finset.card_image_of_injective _ hinj]
    have hbound : A.card ≤ C.size + 1 := by
      apply Support.essential_card_le
      · intro g hg
        exact (hC.2.2 g hg).le
      · intro v hv
        rcases Finset.mem_insert.mp hv with rfl | hv
        · exact Support.incident_point_essential 1 L I C hf 0 a hIa
        · obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp hv
          exact Support.incident_line_essential 1 L I C hf 0 l ((Finset.mem_filter.mp hl).2)
    have hNbound : N.card ≤ C.size := by rw [hAcard] at hbound; omega
    have hlen : bs.length + 1 = N.card := by
      have h := congrArg List.length hls
      simpa [ls] using h.symm
    refine ⟨D, hDvalid, hDfun, ?_, hDread⟩
    calc
      D.size = bs.length + 1 := by simp [D, Star.starCircuit_size, ns]
      _ = N.card := hlen
      _ ≤ C.size := hNbound

end PEqualNP.Outside.L_meta_2585
