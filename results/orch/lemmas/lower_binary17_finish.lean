import lower_binary17_base

namespace PEqualNP.Outside.L_meta_2592_aux.Binary17

def restricted (i : Fin 10) (a : Extended.Sig) : Wire Row :=
  restrictRows (pinRows i) (Extended.observe a)

lemma restricted_target (i : Fin 10) : restricted i Extended.target = observe graph := by
  funext r
  exact pinRows_target i r

lemma restricted_pin (i j : Fin 10) : restricted i (pinAt j) = observe (pinProjection i j) := by
  funext r
  exact pinRows_pin i j r

lemma restricted_self (i : Fin 10) : restricted i (pinAt i) = fun _ => false := by
  rw [restricted_pin, pinProjection_self]
  funext r
  simp [observe, bit, zero]

lemma available_restricted_raw (i : Fin 10) (a : Extended.Sig) (ha : a ∈ Extended.initial) :
    Available true (inputs.map observe) (restricted i a) := by
  obtain ⟨j, rfl⟩ := mem_pinAt a ha
  rw [restricted_pin]
  rcases pinProjection_supply i j with hzero | hmem
  · right
    left
    refine ⟨false, ?_⟩
    rw [hzero]
    funext r
    simp [observe, bit, zero]
  · exact Or.inl (List.mem_map.mpr ⟨_, hmem, rfl⟩)

lemma restricted_bin_eq (i : Fin 10) (b : Extended.Sig) (d : Nat) :
    restricted i (Extended.bin d (pinAt i) b) =
      if d = 0 then (fun _ => false) else if d = 2 then (fun _ => false) else restricted i b := by
  funext r
  have ha : Extended.bit (pinRows i r) (pinAt i) = false := congrFun (restricted_self i) r
  change Extended.bit (pinRows i r) (Extended.bin d (pinAt i) b) = _
  rw [Extended.bit_bin, ha]
  by_cases h0 : d = 0 <;> by_cases h1 : d = 1 <;> by_cases h2 : d = 2 <;>
    simp [h0, h1, h2, restricted, restrictRows, Extended.observe]

lemma available_restricted_bin (i : Fin 10) (b : Extended.Sig) (d : Nat)
    (hb : b ∈ Extended.initial) :
    Available true (inputs.map observe) (restricted i (Extended.bin d (pinAt i) b)) := by
  rw [restricted_bin_eq]
  split_ifs
  · exact Or.inr (Or.inl ⟨false, rfl⟩)
  · exact Or.inr (Or.inl ⟨false, rfl⟩)
  · exact available_restricted_raw i b hb

lemma initial_left_retained {k U a b d}
    (tail : Extended.Live true Extended.target k (insert (Extended.bin d a b) U))
    (hd : Extended.allowed true d)
    (ha : a ∈ Extended.initial) (hb : b ∈ Extended.initial) (hab : a ≠ b)
    (raw : ∀ v ∈ U, v ∈ Extended.initial) : a ∈ U := by
  obtain ⟨i, rfl⟩ := mem_pinAt a ha
  obtain ⟨j, rfl⟩ := mem_pinAt b hb
  have hij : i ≠ j := fun h => hab (congrArg pinAt h)
  have hdlt : d < 4 := by
    rcases hd with h | ⟨_, h⟩ <;> omega
  have sep := Extended.separating_rows i j ⟨d, hdlt⟩ hij
  apply Extended.retain_operand_of_separating_rows tail
  refine ⟨(Extended.choose i j ⟨d, hdlt⟩).1, (Extended.choose i j ⟨d, hdlt⟩).2,
    sep.1, sep.2.1, ?_⟩
  intro v hv hne
  obtain ⟨t, rfl⟩ := mem_pinAt v (raw v hv)
  exact sep.2.2 t (fun ht => hne (congrArg pinAt ht))

lemma tail_bound_retained {k U b d} (i : Fin 10)
    (tail : Extended.Live true Extended.target k (insert (Extended.bin d (pinAt i) b) U))
    (hb : b ∈ Extended.initial)
    (raw : ∀ v ∈ U, v ∈ Extended.initial)
    (hi : pinAt i ∈ U) : 16 ≤ k := by
  have hs : ∀ v ∈ insert (Extended.bin d (pinAt i) b) U,
      Available true (inputs.map observe) (restricted i v) := by
    intro v hv
    rcases Finset.mem_insert.mp hv with rfl | hv
    · exact available_restricted_bin i b d hb
    · exact available_restricted_raw i v (raw v hv)
  have hconst : Constant (restricted i (pinAt i)) := by
    rw [restricted_self]
    exact ⟨false, rfl⟩
  have hnc : ¬ Constant (restricted i Extended.target) := by
    rw [restricted_target]
    exact observe_proper graph_proper
  have lower : ∀ q bs, Reach true (inputs.map observe) q bs →
      Available true bs (restricted i Extended.target) → 15 ≤ q := by
    intro q bs hr hav
    rw [restricted_target] at hav
    exact nineFloor q bs hr hav
  exact tail_lower_of_constant (pinRows i) (inputs.map observe) tail
    (Finset.mem_insert_of_mem hi) hconst hs hnc lower

lemma atLeastSeventeen {k S} (run : Extended.Live true Extended.target k S)
    (raw : ∀ a ∈ S, a ∈ Extended.initial) : 17 ≤ k := by
  have old := atLeastSixteen run raw
  cases k with
  | zero => omega
  | succ k =>
    obtain ⟨U, a, b, d, hd, rfl, _ha, _hb, hab, _fresh, tail⟩ := run
    have ha : a ∈ Extended.initial := raw a (by simp)
    have hb : b ∈ Extended.initial := raw b (by simp)
    have hu : ∀ v ∈ U, v ∈ Extended.initial := by
      intro v hv
      exact raw v (by simp [hv])
    have retained := initial_left_retained tail hd ha hb hab hu
    obtain ⟨i, rfl⟩ := mem_pinAt a ha
    have lower := tail_bound_retained i tail hb hu retained
    omega

lemma binary_floor_seventeen (C : PEqualNP.CircuitLowerBounds.Circuit)
    (legal : PEqualNP.MetaComplexity.FanInTwo C)
    (computes : ∀ x : Fin 10 → Bool, C.eval (List.ofFn x) = Extended.f10 x) :
    17 ≤ C.gates.countP (fun g => !Extended.isNot g) := by
  obtain ⟨k, S, hk, run, raw⟩ := Extended.realize C legal computes
  exact le_trans (atLeastSeventeen run raw) hk

end PEqualNP.Outside.L_meta_2592_aux.Binary17
