namespace PEqualNP.Outside.L_meta_2373_aux.Count.PhysicalAnd

open Seventeen
open PEqualNP.CircuitLowerBounds

-- Reuses the independently checked two-constant projection argument.
lemma restricted_and_zero (rows : Row → Extended.Row) (a b : Extended.Sig)
    (vanishes : restrictRows rows (Extended.observe a) = fun _ => false) :
    Constant (restrictRows rows (Extended.observe (Extended.bin 0 a b))) := by
  refine ⟨false, ?_⟩
  rw [Extended.obs_bin, restrict_comb]
  funext r
  change (restrictRows rows (Extended.observe a) r &&
    restrictRows rows (Extended.observe b) r) = false
  rw [vanishes]
  rfl

lemma restricted_and_not_zero (rows : Row → Extended.Row) (a b : Extended.Sig)
    (vanishes : restrictRows rows (Extended.observe a) = fun _ => false) :
    Constant (restrictRows rows (Extended.observe (Extended.bin 2 a b))) := by
  refine ⟨false, ?_⟩
  rw [Extended.obs_bin, restrict_comb]
  funext r
  change (restrictRows rows (Extended.observe a) r &&
    !(restrictRows rows (Extended.observe b) r)) = false
  rw [vanishes]
  rfl

lemma projected_floor_two (rows : Row → Extended.Row)
    (same : restrictRows rows (Extended.observe Extended.target) = observe graph)
    {k : ℕ} {S : Finset Extended.Sig}
    (run : Extended.Live true Extended.target k S)
    (supplied : ∀ a ∈ S, Available true (inputs.map observe)
      (restrictRows rows (Extended.observe a)))
    (a b : Extended.Sig) (present_a : a ∈ S) (present_b : b ∈ S)
    (different : a ≠ b)
    (constant_a : Constant (restrictRows rows (Extended.observe a)))
    (constant_b : Constant (restrictRows rows (Extended.observe b))) : 17 ≤ k := by
  classical
  let front := a :: b :: ((S.erase a).erase b).toList
  have nd : front.Nodup := by
    simp [front, different, Finset.nodup_toList]
  have eqS : front.toFinset = S := by
    ext c
    by_cases ca : c = a <;> by_cases cb : c = b <;>
      simp [front, ca, cb, present_a, present_b]
  have hrun := Extended.list_run run front nd eqS
  have supplyRoots : supply true (inputs.map observe)
      ((front.map Extended.observe).map (restrictRows rows)) := by
    intro v hv
    obtain ⟨_, hin, rfl⟩ := List.mem_map.mp hv
    obtain ⟨c, hmFront, rfl⟩ := List.mem_map.mp hin
    exact supplied c (eqS ▸ List.mem_toFinset.mpr hmFront)
  have need := projected_bound rows hrun (same ▸ observe_proper graph_proper)
    Reach.start supplyRoots (L := 15) (same ▸ nineFloor)
  have charge : 2 ≤ mass ((front.map Extended.observe).map (restrictRows rows)) := by
    simp only [front, List.map_cons, mass_cons, cost,
      if_pos constant_a, if_pos constant_b]
    omega
  omega


def and_extra (i j : Fin 10) : Extended.Sig := Extended.bin 0 (pin i) (pin j)

lemma and_diagonal (i : Fin 10) : and_extra i i = pin i := by
  simp [and_extra, Extended.bin]

lemma and_extra_floor (i j : Fin 10) {k : ℕ} {S : Finset Extended.Sig}
    (run : Extended.Live true Extended.target k S)
    (raw : ∀ a ∈ S, a ∈ and_extra i j :: Extended.initial) : 17 ≤ k := by
  classical
  by_cases equal : i = j
  · subst j
    apply signed_floor_seventeen run
    intro a ha
    rcases List.mem_cons.mp (raw a ha) with rfl | ha
    · rw [and_diagonal, initial_pins]
      exact List.mem_ofFn.mpr ⟨i, rfl⟩
    · exact ha
  by_cases present : and_extra i j ∈ S
  · let U := S.erase (and_extra i j)
    have run' : Extended.Live true Extended.target k (insert (and_extra i j) U) := by
      simpa [U, Finset.insert_erase present] using run
    have rawU : ∀ a ∈ U, a ∈ Extended.initial := by
      intro a ha
      obtain ⟨different, member⟩ := Finset.mem_erase.mp ha
      exact (List.mem_cons.mp (raw a member)).resolve_left different
    have selected : pin i ∈ U := selected_pin (d := ⟨0, by decide⟩) equal run' rawU
    have extra_constant : Constant
        (restrictRows (embedAt i) (Extended.observe (and_extra i j))) :=
      restricted_and_zero (embedAt i) (pin i) (pin j) (pin_zero i)
    exact projected_floor_two (embedAt i) (target_embedding i) run'
      (fun a ha => by
        rcases Finset.mem_insert.mp ha with rfl | ha
        · exact Or.inr (Or.inl extra_constant)
        · obtain ⟨v, rfl⟩ := pin_mem (rawU a ha)
          exact pin_available i v)
      (and_extra i j) (pin i) (Finset.mem_insert_self _ _)
      (Finset.mem_insert_of_mem selected) (Ne.symm (Finset.mem_erase.mp selected).1)
      extra_constant (pin_vanishes i)
  · apply signed_floor_seventeen run
    intro a ha
    rcases List.mem_cons.mp (raw a ha) with rfl | h
    · exact False.elim (present ha)
    · exact h

lemma first_extra_binary_floor (g : Gate) (gs : List Gate) (output : ℕ)
    (legal : PEqualNP.MetaComplexity.FanInTwo (⟨g :: gs, output⟩ : Circuit))
    (computes : ∀ x : Fin 10 → Bool,
      (⟨g :: gs, output⟩ : Circuit).eval (List.ofFn x) = Extended.f10 x)
    (binary : Extended.isNot g = false)
    (plain : Extended.bit 0 (Extended.gv Extended.initial g) = false)
    (tail_floor : ∀ {k : ℕ} {S : Finset Extended.Sig},
      Extended.Live true Extended.target k S →
      (∀ a ∈ S, a ∈ Extended.gv Extended.initial g :: Extended.initial) → 17 ≤ k) :
    18 ≤ (g :: gs).countP (fun h => !Extended.isNot h) := by
  let w := Extended.initial ++ [Extended.gv Extended.initial g]
  have he : (Extended.execute gs w).getD output Extended.zero = Extended.target := by
    change (Extended.execute (g :: gs) Extended.initial).getD output Extended.zero = _
    apply Extended.bit_ext
    intro r
    rw [← Extended.b_read, Extended.execute_bits _ _ _ (fun h hh => (legal h hh).1)]
    change ((⟨g :: gs, output⟩ : Circuit).wires
      (Extended.initial.map (Extended.bit r))).getD output false = _
    rw [Extended.rowInputs]
    exact (computes _).trans (Extended.rowTarget r).symm
  have hp : Extended.proper Extended.target := by
    unfold Extended.proper
    decide +kernel
  have out := Extended.get_rep (u := true) (Extended.execute gs w) output
  rw [he] at out
  unfold Extended.Repr at out
  rw [Extended.nrm_id (show Extended.bit 0 Extended.target = false by decide +kernel)] at out
  obtain ⟨k, S, hk, run, raw⟩ := Extended.extract gs w
    (fun h hh => legal h (List.mem_cons_of_mem g hh)) (u := true) (by simp) hp
    (out.resolve_right (fun h => h hp))
  have ns : w.all Extended.plainWord = true := by
    have original : Extended.initial.all Extended.plainWord = true := by decide +kernel
    simp only [w, List.all_append, List.all_cons, List.all_nil, original,
      Extended.plainWord, plain, Bool.not_false, Bool.and_self]
  rw [Extended.nrm_map ns] at raw
  have lower := tail_floor run
    (fun a ha => by simpa [w, or_comm] using raw a ha)
  rw [List.countP_cons]
  simp only [binary, Bool.not_false, ite_true]
  omega

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
lemma first_and_signature : ∀ i j : Fin 10,
    Extended.gv Extended.initial ⟨.and, [i.val, j.val]⟩ = and_extra i j := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
lemma first_and_plain : ∀ i j : Fin 10,
    Extended.bit 0 (Extended.gv Extended.initial ⟨.and, [i.val, j.val]⟩) = false := by
  decide +kernel

lemma first_and_binary_floor_eighteen (i j : Fin 10) (gs : List Gate) (output : ℕ)
    (legal : PEqualNP.MetaComplexity.FanInTwo
      (⟨⟨.and, [i.val, j.val]⟩ :: gs, output⟩ : Circuit))
    (computes : ∀ x : Fin 10 → Bool,
      (⟨⟨.and, [i.val, j.val]⟩ :: gs, output⟩ : Circuit).eval (List.ofFn x) = Extended.f10 x) :
    18 ≤ (⟨.and, [i.val, j.val]⟩ :: gs).countP (fun h => !Extended.isNot h) := by
  apply first_extra_binary_floor _ _ _ legal computes rfl (first_and_plain i j)
  intro k S run raw
  apply and_extra_floor i j run
  simpa only [first_and_signature i j] using raw

lemma first_and_not_count_at_most_one (i j : Fin 10) (gs : List Gate) (output : ℕ)
    (legal : PEqualNP.MetaComplexity.FanInTwo
      (⟨⟨.and, [i.val, j.val]⟩ :: gs, output⟩ : Circuit))
    (computes : ∀ x : Fin 10 → Bool,
      (⟨⟨.and, [i.val, j.val]⟩ :: gs, output⟩ : Circuit).eval (List.ofFn x) = Extended.f10 x)
    (small : (⟨⟨.and, [i.val, j.val]⟩ :: gs, output⟩ : Circuit).size ≤ 19) :
    PEqualNP.NotBracket.notCount (⟨⟨.and, [i.val, j.val]⟩ :: gs, output⟩ : Circuit) ≤ 1 := by
  have lower := first_and_binary_floor_eighteen i j gs output legal computes
  have partition : ∀ gates : List Gate,
      gates.countP (fun g => !Extended.isNot g) +
        gates.countP (fun g => Extended.isNot g) = gates.length := by
    intro gates
    induction gates with
    | nil => rfl
    | cons g gates ih =>
      cases h : Extended.isNot g <;> simp_all [List.countP_cons] <;> omega
  have count_eq : (⟨.and, [i.val, j.val]⟩ :: gs).countP Extended.isNot =
      PEqualNP.NotBracket.notCount (⟨⟨.and, [i.val, j.val]⟩ :: gs, output⟩ : Circuit) := by
    unfold PEqualNP.NotBracket.notCount
    rw [← List.countP_eq_length_filter]
    apply List.countP_congr
    intro g hg
    obtain ⟨op, ins⟩ := g
    cases op <;> rfl
  have total := partition (⟨.and, [i.val, j.val]⟩ :: gs)
  rw [count_eq] at total
  change (⟨.and, [i.val, j.val]⟩ :: gs).length ≤ 19 at small
  omega

end PEqualNP.Outside.L_meta_2373_aux.Count.PhysicalAnd
