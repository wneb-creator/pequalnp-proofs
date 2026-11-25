import TwoPrefixFloor

namespace PEqualNP.Outside.L_meta_1884.GlobalProjectionCut

open PEqualNP.Outside.L_meta_2592.Binary17
open PEqualNP.Outside.L_meta_2592.Binary17.Geometry

lemma projected_available_of_supply {R T : Type} (rows : T → R) {u : Bool}
    {old : List (Wire R)} {new : List (Wire T)}
    (hs : supply u new (old.map (restrictRows rows))) {a : Wire R}
    (ha : Available u old a) : Available u new (restrictRows rows a) := by
  rcases ha with hm | hc | ⟨hu, hn⟩
  · exact hs _ (List.mem_map.mpr ⟨a, hm, rfl⟩)
  · obtain ⟨b, hb⟩ := hc
    exact Or.inr (Or.inl ⟨b, by rw [hb]; rfl⟩)
  · have h := hs _ (List.mem_map.mpr ⟨inv a, hn, rfl⟩)
    have h' := avail_inv hu h
    have he : inv (restrictRows rows (inv a)) = restrictRows rows a := by
      funext t
      simp [inv, restrictRows]
    exact he ▸ h'

lemma replay {R T : Type} (rows : T → R) {u : Bool}
    {oldRoots oldBank : List (Wire R)} {steps : Nat}
    (old : Reach u oldRoots steps oldBank)
    {newRoots newBank : List (Wire T)} {spent : Nat}
    (start : Reach u newRoots spent newBank)
    (supplyRoots : supply u newBank (oldRoots.map (restrictRows rows))) :
    ∃ out, Reach u newRoots (spent + steps) out ∧
      supply u out (oldBank.map (restrictRows rows)) := by
  induction old using Reach.ind with
  | start => exact ⟨newBank, by simpa using start, supplyRoots⟩
  | @two p bank a b op old ha hb ih =>
    obtain ⟨out, reached, supplied⟩ := ih
    have pa := projected_available_of_supply rows supplied ha
    have pb := projected_available_of_supply rows supplied hb
    refine ⟨combine op (restrictRows rows a) (restrictRows rows b) :: out, ?_, ?_⟩
    · simpa [Nat.add_assoc] using Reach.two op reached pa pb
    · intro w hw
      simp only [List.map_cons, List.mem_cons] at hw
      rcases hw with rfl | hm
      · have he : restrictRows rows (combine op a b) =
            combine op (restrictRows rows a) (restrictRows rows b) := by
          cases op <;> rfl
        rw [he]
        exact Or.inl (List.mem_cons_self)
      · exact available_cons _ (supplied w hm)

lemma replay_skip_constant {R T : Type} (rows : T → R) {u : Bool}
    {oldRoots oldBank : List (Wire R)} {before after : Nat}
    (beforeRun : Reach u oldRoots before oldBank)
    {a b : Wire R} (op : Bool)
    (ha : Available u oldBank a) (hb : Available u oldBank b)
    (constant : Constant (restrictRows rows a) ∨ Constant (restrictRows rows b))
    {last : List (Wire R)}
    (suffix : Reach u (combine op a b :: oldBank) after last)
    {newRoots : List (Wire T)}
    (supplied : supply u newRoots (oldRoots.map (restrictRows rows))) :
    ∃ out, Reach u newRoots (before + after) out ∧
      supply u out (last.map (restrictRows rows)) := by
  obtain ⟨middle, reached, covered⟩ := replay rows beforeRun Reach.start supplied
  have pa := projected_available_of_supply rows covered ha
  have pb := projected_available_of_supply rows covered hb
  have pc := from_constant op constant pa pb
  have sup : supply u middle ((combine op a b :: oldBank).map (restrictRows rows)) := by
    intro w hw
    simp only [List.map_cons, List.mem_cons] at hw
    rcases hw with rfl | hm
    · have he : restrictRows rows (combine op a b) =
          combine op (restrictRows rows a) (restrictRows rows b) := by
        cases op <;> rfl
      exact he ▸ pc
    · exact covered w hm
  simpa using replay rows suffix reached sup

lemma initial_projection (v : Fin 10) : supply true (inputs.map observe)
    ((Extended.initial.map Extended.observe).map (restrictRows (embedV v))) := by
  intro z hz
  obtain ⟨_, hm, rfl⟩ := List.mem_map.mp hz
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hm
  rw [observe_projectV]
  obtain ⟨i, rfl⟩ := (pin_mem_iff a).mp ha
  rcases project_pin v i with he | hm
  · exact projected_available _ (Or.inl he)
  · exact projected_available _ (Or.inr (Or.inr (Or.inl hm)))

lemma two_constant_cut (v : Fin 10) (r : Extended.Sig)
    {p k : Nat} {bank : List (Wire Extended.Row)} {S : Finset Extended.Sig}
    (beforeRun : Reach true (Extended.initial.map Extended.observe) p bank)
    (run : Extended.Live true Extended.target k S)
    (covered : ∀ a ∈ S, Available true bank (Extended.observe a) ∨ a = r)
    (hv : pin v ∈ S) (hr : r ∈ S) (hne : r ≠ pin v)
    (hz : projectV v r = zero) : 18 ≤ p + 1 + k := by
  classical
  obtain ⟨out, reached, supplied⟩ := replay (embedV v) beforeRun Reach.start (initial_projection v)
  let front := pin v :: r :: ((S.erase (pin v)).erase r).toList
  have nd : front.Nodup := by
    apply List.nodup_cons.mpr
    refine ⟨?_, ?_⟩
    · simp [Ne.symm hne]
    · apply List.nodup_cons.mpr
      exact ⟨by simp, Finset.nodup_toList _⟩
  have eqS : front.toFinset = S := by
    ext a
    by_cases ha : a = pin v <;> by_cases hqa : a = r <;>
      simp [front, ha, hqa, hv, hr]
  have hrun := Extended.list_run run front nd eqS
  have same : restrictRows (embedV v) (Extended.observe Extended.target) = observe graph := by
    rw [observe_projectV, project_target]
  have cr : Constant (restrictRows (embedV v) (Extended.observe r)) := by
    rw [observe_projectV, hz]
    exact ⟨false, by funext t; simp [observe, bit, zero]⟩
  have cp : Constant (restrictRows (embedV v) (Extended.observe (pin v))) := by
    rw [observe_projectV, project_self]
    exact ⟨false, by funext t; simp [observe, bit, zero]⟩
  have roots : supply true out ((front.map Extended.observe).map (restrictRows (embedV v))) := by
    intro z hzmem
    obtain ⟨_, hm, rfl⟩ := List.mem_map.mp hzmem
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hm
    rcases covered a (eqS ▸ List.mem_toFinset.mpr ha) with hp | he
    · exact projected_available_of_supply (embedV v) supplied hp
    · rw [he]
      exact Or.inr (Or.inl cr)
  have bound := projected_bound (embedV v) hrun
    (same ▸ observe_proper graph_proper) reached roots (L := 15) (same ▸ nineFloor)
  have charge : 2 ≤ mass ((front.map Extended.observe).map (restrictRows (embedV v))) := by
    simp [front, mass_cons, cost, cp, cr]
    omega
  omega

lemma one_constant_after_skipped_step (v : Fin 10) (r : Extended.Sig)
    {p q k : Nat} {middle last : List (Wire Extended.Row)}
    (beforeRun : Reach true (Extended.initial.map Extended.observe) p middle)
    {a b : Wire Extended.Row} (op : Bool)
    (ha : Available true middle a) (hb : Available true middle b)
    (hc : Constant (restrictRows (embedV v) a) ∨ Constant (restrictRows (embedV v) b))
    (afterRun : Reach true (combine op a b :: middle) q last)
    {S : Finset Extended.Sig}
    (run : Extended.Live true Extended.target k S)
    (covered : ∀ z ∈ S, Available true last (Extended.observe z) ∨ z = r)
    (hr : r ∈ S) (hz : projectV v r = zero) : 18 ≤ p + 1 + q + 1 + k := by
  classical
  obtain ⟨out, reached, supplied⟩ := replay_skip_constant (embedV v)
    beforeRun op ha hb hc afterRun (initial_projection v)
  let front := r :: (S.erase r).toList
  have nd : front.Nodup := by
    exact List.nodup_cons.mpr ⟨by simp, Finset.nodup_toList _⟩
  have eqS : front.toFinset = S := by
    ext z
    by_cases he : z = r <;> simp [front, he, hr]
  have hrun := Extended.list_run run front nd eqS
  have same : restrictRows (embedV v) (Extended.observe Extended.target) = observe graph := by
    rw [observe_projectV, project_target]
  have cr : Constant (restrictRows (embedV v) (Extended.observe r)) := by
    rw [observe_projectV, hz]
    exact ⟨false, by funext t; simp [observe, bit, zero]⟩
  have roots : supply true out ((front.map Extended.observe).map (restrictRows (embedV v))) := by
    intro z hzmem
    obtain ⟨_, hm, rfl⟩ := List.mem_map.mp hzmem
    obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hm
    rcases covered w (eqS ▸ List.mem_toFinset.mpr hw) with hp | he
    · exact projected_available_of_supply (embedV v) supplied hp
    · rw [he]
      exact Or.inr (Or.inl cr)
  have bound := projected_bound (embedV v) hrun
    (same ▸ observe_proper graph_proper) reached roots (L := 15) (same ▸ nineFloor)
  have charge : 1 ≤ mass ((front.map Extended.observe).map (restrictRows (embedV v))) := by
    simp [front, mass_cons, cost, cr]
  omega

end PEqualNP.Outside.L_meta_1884.GlobalProjectionCut
