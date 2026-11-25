import PEqualNP.Outside.L_meta_2592

namespace PEqualNP.Outside.L_meta_2592_aux.Stronger.NegativeSeed

def seed (i j : Fin 10) : Extended.Sig :=
  Extended.bin 1 (Extended.pins.getD i.val Extended.zero) (Extended.pins.getD j.val Extended.zero)

def extra (i j : Fin 10) : Extended.Sig :=
  Extended.bin 2 (Extended.pins.getD 0 Extended.zero) (seed i j)

def bank (i j : Fin 10) := Extended.pins ++ [seed i j,extra i j]

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma projected_pin_available : ∀ i : Fin 10,
    ((projected (Extended.pins.getD i.val Extended.zero) == zero) ||
      inputs.contains (projected (Extended.pins.getD i.val Extended.zero))) = true := by
  decide +kernel

lemma pin_available (i : Fin 10) : Available true (inputs.map observe)
    (restrictRows embed (Extended.observe (Extended.pins.getD i.val Extended.zero))) := by
  rw [observe_projected]
  have check := projected_pin_available i
  simp only [Bool.or_eq_true,beq_iff_eq] at check
  rcases check with hz | hm
  · right; left
    refine ⟨false,?_⟩
    rw [hz]
    funext r
    simp [observe,bit,zero]
  · exact Or.inl (List.mem_map.mpr ⟨_,by simpa using hm,rfl⟩)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma extra_projects_zero : ∀ i j : Fin 10, projected (extra i j) = zero := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma extra_ne_first : ∀ i j : Fin 10,
    extra i j ≠ Extended.pins.getD 0 Extended.zero := by decide +kernel

lemma lower (i j : Fin 10) {k S} (run : Extended.Live true Extended.target k S)
    (raw : ∀ a ∈ S, a ∈ bank i j)
    (needed : Extended.pins.getD 0 Extended.zero ∈ S) (used : extra i j ∈ S) : 16 ≤ k := by
  classical
  have ne := extra_ne_first i j
  let front := Extended.pins.getD 0 Extended.zero :: extra i j ::
    ((S.erase (Extended.pins.getD 0 Extended.zero)).erase (extra i j)).toList
  have nd : front.Nodup := by
    simp [front,ne,ne.symm,Finset.nodup_toList,-List.getD_eq_getElem?_getD]
  have eqS : front.toFinset = S := by
    ext a
    by_cases ha : a = Extended.pins.getD 0 Extended.zero <;>
      by_cases hb : a = extra i j <;> simp [front,ha,hb,needed,used,-List.getD_eq_getElem?_getD]
  have hrun := Extended.list_run run front nd eqS
  have same : restrictRows embed (Extended.observe Extended.target) = observe graph := by
    rw [observe_projected]
    exact congrArg observe (by decide +kernel)
  have isZero : observe zero = fun _ => false := by funext r; simp [observe,bit,zero]
  let seedWire := restrictRows embed (Extended.observe (seed i j))
  have seedEq : seedWire = combine true
      (restrictRows embed (Extended.observe (Extended.pins.getD i.val Extended.zero)))
      (restrictRows embed (Extended.observe (Extended.pins.getD j.val Extended.zero))) := by
    dsimp only [seedWire,seed]
    rw [Extended.obs_bin,restrict_comb]
    rfl
  have reachSeed : Reach true (inputs.map observe) 1 (seedWire :: inputs.map observe) := by
    rw [seedEq]
    exact Reach.two true Reach.start (pin_available i) (pin_available j)
  have supplyRoots : supply true (seedWire :: inputs.map observe)
      ((front.map Extended.observe).map (restrictRows embed)) := by
    intro v hv
    obtain ⟨_,hin,rfl⟩ := List.mem_map.mp hv
    obtain ⟨a,hm,rfl⟩ := List.mem_map.mp hin
    have hr := raw a (eqS ▸ List.mem_toFinset.mpr hm)
    simp only [bank,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with hp | hs | he
    · have hlist : List.ofFn (fun t : Fin 10 => Extended.pins.getD t.val Extended.zero) = Extended.pins := rfl
      rw [← hlist] at hp
      obtain ⟨t,rfl⟩ := List.mem_ofFn.mp hp
      exact available_cons _ (pin_available t)
    · subst a
      exact Or.inl (by simp [seedWire])
    · subst a
      rw [observe_projected,extra_projects_zero]
      exact Or.inr (Or.inl ⟨false,isZero⟩)
  have bound := projected_bound embed hrun (same ▸ observe_proper graph_proper)
    reachSeed supplyRoots (L:=15) (same ▸ nineFloor)
  have charge : 2 ≤ mass ((front.map Extended.observe).map (restrictRows embed)) := by
    have firstConstant : Constant (restrictRows embed (Extended.observe (Extended.pins.getD 0 Extended.zero))) := by
      rw [observe_projected,show projected (Extended.pins.getD 0 Extended.zero) = zero by decide +kernel]
      exact ⟨false,isZero⟩
    have extraConstant : Constant (restrictRows embed (Extended.observe (extra i j))) := by
      rw [observe_projected,extra_projects_zero]
      exact ⟨false,isZero⟩
    simp only [front,List.map_cons,List.map_map,mass_cons,cost,firstConstant,extraConstant,ite_true]
    omega
  omega

end PEqualNP.Outside.L_meta_2592_aux.Stronger.NegativeSeed
