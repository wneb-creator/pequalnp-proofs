namespace PEqualNP.Outside.L_meta_2592_aux.Stronger.Extended

lemma realizeRawPins (C : PEqualNP.CircuitLowerBounds.Circuit)
    (legal : PEqualNP.MetaComplexity.FanInTwo C)
    (computes : ∀ x : Fin 10 → Bool, C.eval (List.ofFn x) = f10 x) :
    ∃ k S, k ≤ C.gates.countP (fun g => !isNot g) ∧ Live true target k S ∧
      ∀ a ∈ S, a ∈ pins := by
  have he : (execute C.gates pins).getD C.output zero = target := by
    apply bit_ext
    intro r
    rw [←b_read,execute_bits _ _ _ (fun g hg => (legal g hg).1)]
    change (C.wires (pins.map (bit r))).getD C.output false = _
    rw [rowPins]
    exact (computes _).trans (rowTarget r).symm
  have hp : proper target := by unfold proper; decide +kernel
  have out := get_rep (u:=true) (execute C.gates pins) C.output
  rw [he] at out
  unfold Repr at out
  rw [nrm_id (show bit 0 target=false by decide +kernel)] at out
  obtain ⟨k,S,hk,run,hs⟩ := extract C.gates pins legal (u:=true) (by simp) hp
    (out.resolve_right (fun h => h hp))
  have ns : pins.all plainWord = true := by decide +kernel
  rw [nrm_map ns] at hs
  exact ⟨k,S,hk,run,hs⟩

lemma first_proper_binary {k S} (run : Live true target k S)
    (raw : ∀ a ∈ S, a ∈ pins) :
    ∃ j a b d T, k = j + 1 ∧ a ∈ pins ∧ b ∈ pins ∧ a ≠ b ∧ d < 4 ∧
      Live true target j T ∧ ∀ c ∈ T, c ∈ pins ++ [bin d a b] := by
  cases k with
  | zero =>
    obtain ⟨rfl, _⟩ := run
    have hm := raw target (by simp)
    have hn : target ∉ pins := by decide +kernel
    exact (hn hm).elim
  | succ j =>
    obtain ⟨U,a,b,d,hd,rfl,_,_,hab,_,tail⟩ := run
    refine ⟨j,a,b,d,insert (bin d a b) U,rfl,raw a (by simp),raw b (by simp),hab,?_,tail,?_⟩
    · rcases hd with h | ⟨_,h⟩ <;> omega
    · intro c hc
      rcases Finset.mem_insert.mp hc with rfl | hc
      · exact List.mem_append_right _ (by simp)
      · exact List.mem_append_left _ (raw c (by simp [hc]))

end PEqualNP.Outside.L_meta_2592_aux.Stronger.Extended
