namespace component

def renameWire (n m : ℕ) (rho : ℕ → ℕ) (i : ℕ) : ℕ :=
  if i < n then rho i else m + (i - n)

def renameGate (rho : ℕ → ℕ) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map rho⟩

lemma wf_rename_prefix_aux (gs : List Gate) (old new : List Bool) (rho : ℕ → ℕ)
    (hread : ∀ g ∈ gs, ∀ i ∈ g.inputs, i < old.length →
      rho i < new.length ∧ new.getD (rho i) false = old.getD i false)
    (acc : List Bool) :
    wf (gs.map (renameGate (renameWire old.length new.length rho))) (new ++ acc) =
      new ++ (wf gs (old ++ acc)).drop old.length := by
  induction gs generalizing acc with
  | nil => simp [wf]
  | cons g gs ih =>
    have hvals : (renameGate (renameWire old.length new.length rho) g).inputs.map
        (fun i => (new ++ acc).getD i false) =
        g.inputs.map (fun i => (old ++ acc).getD i false) := by
      simp only [renameGate, List.map_map]
      apply List.map_congr_left
      intro i hi
      change (new ++ acc).getD (renameWire old.length new.length rho i) false = _
      by_cases hio : i < old.length
      · obtain ⟨hir, he⟩ := hread g List.mem_cons_self i hi hio
        simp only [renameWire, hio, ite_true]
        rw [List.getD_append _ _ _ _ hir, List.getD_append _ _ _ _ hio]
        exact he
      · simp only [renameWire, hio, ite_false]
        rw [getD_shift, List.getD_append_right _ _ _ _ (by omega)]
    change wf (gs.map (renameGate (renameWire old.length new.length rho)))
        ((new ++ acc) ++ [(renameGate _ g).op.eval _]) =
      new ++ (wf gs ((old ++ acc) ++ [g.op.eval _])).drop old.length
    rw [hvals]
    change wf (gs.map (renameGate (renameWire old.length new.length rho)))
        ((new ++ acc) ++ [g.op.eval _]) =
      new ++ (wf gs ((old ++ acc) ++ [g.op.eval _])).drop old.length
    rw [List.append_assoc, List.append_assoc]
    exact ih (fun a ha i hi hio => hread a (List.mem_cons_of_mem g ha) i hi hio) _

lemma wf_rename_prefix (gs : List Gate) (old new : List Bool) (rho : ℕ → ℕ)
    (hread : ∀ g ∈ gs, ∀ i ∈ g.inputs, i < old.length →
      rho i < new.length ∧ new.getD (rho i) false = old.getD i false) :
    wf (gs.map (renameGate (renameWire old.length new.length rho))) new =
      new ++ (wf gs old).drop old.length := by
  simpa using wf_rename_prefix_aux gs old new rho hread []

lemma output_rename_prefix (gs : List Gate) (old new : List Bool) (rho : ℕ → ℕ)
    (hread : ∀ g ∈ gs, ∀ i ∈ g.inputs, i < old.length →
      rho i < new.length ∧ new.getD (rho i) false = old.getD i false)
    (o : ℕ) (hout : o < old.length →
      rho o < new.length ∧ new.getD (rho o) false = old.getD o false) :
    (wf (gs.map (renameGate (renameWire old.length new.length rho))) new).getD
        (renameWire old.length new.length rho o) false = (wf gs old).getD o false := by
  by_cases ho : o < old.length
  · obtain ⟨hr, he⟩ := hout ho
    simp only [renameWire, ho, ite_true]
    rw [wf_keep _ _ _ hr, wf_keep _ _ _ ho]
    exact he
  · rw [wf_rename_prefix gs old new rho hread]
    simp only [renameWire, ho, ite_false]
    rw [getD_shift]
    simp [List.getD_eq_getElem?_getD, List.getElem?_drop, Nat.add_sub_of_le (by omega : old.length ≤ o)]

lemma rename_mono (gs : List Gate) (rho : ℕ → ℕ) (o : ℕ)
    (h : PEqualNP.MetaComplexity.Monotone2 ⟨gs, 0⟩) :
    PEqualNP.MetaComplexity.Monotone2 ⟨gs.map (renameGate rho), o⟩ := by
  intro g hg
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hg
  simpa [renameGate] using h a ha

lemma renameGate_length (gs : List Gate) (rho : ℕ → ℕ) :
    (gs.map (renameGate rho)).length = gs.length := by simp

end component
