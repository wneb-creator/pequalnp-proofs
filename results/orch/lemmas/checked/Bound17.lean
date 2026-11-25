import ProjectionChecked
open PEqualNP.CircuitLowerBounds
namespace PEqualNP.Outside.L_meta_2592
namespace Projection

lemma pin_observe (v i : Fin 10) :
    restrictRows (row v) (Extended.observe (pin i)) = observe (image v i) := by
  funext r
  exact pin_values v i r

lemma available_pin (v i : Fin 10) :
    Available true (inputs.map observe)
      (restrictRows (row v) (Extended.observe (pin i))) := by
  rw [pin_observe]
  rcases image_allowed v i with h | h
  · apply Or.inr
    apply Or.inl
    refine ⟨false, ?_⟩
    rw [h]
    funext r
    simp [observe, bit, zero]
  · exact Or.inl (List.mem_map.mpr ⟨_, h, rfl⟩)

lemma bin_bits (r : Extended.Row) (d : Nat) (a b : Extended.Sig) :
    Extended.bit r (Extended.bin d a b) =
      (if d = 0 then Extended.bit r a && Extended.bit r b else
       if d = 1 then Extended.bit r a || Extended.bit r b else
       if d = 2 then Extended.bit r a && !(Extended.bit r b) else
       !(Extended.bit r a) && Extended.bit r b) := by
  unfold Extended.bin
  split_ifs <;> simp [Extended.bit]

lemma created_left_zero (d : Nat) (i j : Fin 10) (hd : d = 0 ∨ d = 2) :
    restrictRows (row i) (Extended.observe (Extended.bin d (pin i) (pin j))) =
      fun _ => false := by
  funext r
  change Extended.bit (row i r) (Extended.bin d (pin i) (pin j)) = false
  rcases hd with rfl | rfl <;> simp [bin_bits, deleted_value]

lemma created_left_copy (d : Nat) (i j : Fin 10) (hd : d = 1 ∨ d = 3) :
    restrictRows (row i) (Extended.observe (Extended.bin d (pin i) (pin j))) =
      restrictRows (row i) (Extended.observe (pin j)) := by
  funext r
  change Extended.bit (row i r) (Extended.bin d (pin i) (pin j)) =
    Extended.bit (row i r) (pin j)
  rcases hd with rfl | rfl <;> simp [bin_bits, deleted_value]

lemma available_created (d : Nat) (i j : Fin 10) (hd : Extended.allowed true d) :
    Available true (inputs.map observe)
      (restrictRows (row i) (Extended.observe (Extended.bin d (pin i) (pin j)))) := by
  rcases Extended.allowed_four hd with rfl | rfl | ⟨_, rfl⟩ | ⟨_, rfl⟩
  · exact Or.inr (Or.inl ⟨false, created_left_zero 0 i j (Or.inl rfl)⟩)
  · rw [created_left_copy 1 i j (Or.inl rfl)]
    exact available_pin i j
  · exact Or.inr (Or.inl ⟨false, created_left_zero 2 i j (Or.inr rfl)⟩)
  · rw [created_left_copy 3 i j (Or.inr rfl)]
    exact available_pin i j

lemma tail_project_bound {d k : Nat} {i j : Fin 10} {U : Finset Extended.Sig}
    (hd : Extended.allowed true d)
    (raw : ∀ a ∈ U, a ∈ Extended.initial)
    (run : Extended.Live true Extended.target k (insert (Extended.bin d (pin i) (pin j)) U))
    (front : List Extended.Sig) (nd : front.Nodup)
    (eqS : front.toFinset = insert (Extended.bin d (pin i) (pin j)) U) :
    15 + mass ((front.map Extended.observe).map (restrictRows (row i))) ≤ k := by
  have hrun := Extended.list_run run front nd eqS
  have same : restrictRows (row i) (Extended.observe Extended.target) = observe graph := by
    funext r
    exact target_values i r
  have supplyRoots : supply true (inputs.map observe)
      ((front.map Extended.observe).map (restrictRows (row i))) := by
    intro f hf
    obtain ⟨_, hin, rfl⟩ := List.mem_map.mp hf
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hin
    have hm : a ∈ insert (Extended.bin d (pin i) (pin j)) U :=
      eqS ▸ List.mem_toFinset.mpr ha
    rcases Finset.mem_insert.mp hm with rfl | hu
    · exact available_created d i j hd
    · obtain ⟨v, rfl⟩ := initial_pin (raw a hu)
      exact available_pin i v
  have need := projected_bound (row i) hrun (same ▸ observe_proper graph_proper)
    Reach.start supplyRoots (L := 15) (same ▸ nineFloor)
  simpa only [Nat.zero_add] using need

lemma tail_bound_left {d k : Nat} {i j : Fin 10} {U : Finset Extended.Sig}
    (hd : Extended.allowed true d) (retained : pin i ∈ U)
    (raw : ∀ a ∈ U, a ∈ Extended.initial)
    (run : Extended.Live true Extended.target k (insert (Extended.bin d (pin i) (pin j)) U)) :
    16 ≤ k := by
  classical
  let S := insert (Extended.bin d (pin i) (pin j)) U
  let front := pin i :: (S.erase (pin i)).toList
  have nd : front.Nodup := by
    apply List.nodup_cons.mpr
    exact ⟨by simp, Finset.nodup_toList _⟩
  have eqS : front.toFinset = S := by
    ext a
    by_cases h : a = pin i <;> simp [front, h, S, retained]
  have need := tail_project_bound hd raw run front nd eqS
  have ac : Constant (restrictRows (row i) (Extended.observe (pin i))) := by
    refine ⟨false, ?_⟩
    funext r
    exact deleted_value i r
  have charge : 1 ≤ mass ((front.map Extended.observe).map (restrictRows (row i))) := by
    simp [front, mass_cons, cost, ac]
  omega

end Projection

lemma atLeastSeventeen {k S} (run : Extended.Live true Extended.target k S)
    (raw : ∀ a ∈ S, a ∈ Extended.initial) : 17 ≤ k := by
  classical
  cases k with
  | zero =>
    have hm := raw Extended.target (run.1.symm ▸ Finset.mem_singleton_self _)
    exact False.elim ((by decide +kernel : Extended.target ∉ Extended.initial) hm)
  | succ k =>
    obtain ⟨U, a, b, d, hd, rfl, ha, hb, hab, fresh, tail⟩ := run
    have ha0 := raw a (by simp)
    have hb0 := raw b (by simp)
    have rawU : ∀ c ∈ U, c ∈ Extended.initial := by
      intro c hc
      exact raw c (by simp [hc])
    have retained := Extended.initial_retained hd ha0 hb0 hab rawU tail
    obtain ⟨i, rfl⟩ := Projection.initial_pin ha0
    obtain ⟨j, rfl⟩ := Projection.initial_pin hb0
    have bound := Projection.tail_bound_left hd retained.1 rawU tail
    omega

lemma binary_floor17 (C : Circuit) (legal : PEqualNP.MetaComplexity.FanInTwo C)
    (computes : ∀ x : Fin 10 → Bool, C.eval (List.ofFn x) = Extended.f10 x) :
    17 + PEqualNP.NotBracket.notCount C ≤ C.size := by
  obtain ⟨k, S, hk, run, raw⟩ := Extended.realize C legal computes
  have floor := atLeastSeventeen run raw
  have sameNot :
      (fun g : Gate => @decide (g.op = GateOp.not) (lineDegreeGateOpDecEq g.op GateOp.not)) =
        Extended.isNot := by
    funext g
    obtain ⟨op, operands⟩ := g
    cases op <;> rfl
  rw [PEqualNP.NotBracket.notCount, sameNot, ← List.countP_eq_length_filter]
  have negSame : (fun g : Gate => decide (¬ Extended.isNot g = true)) =
      (fun g => !Extended.isNot g) := by
    funext g
    cases Extended.isNot g <;> rfl
  have count := List.length_eq_countP_add_countP Extended.isNot (l := C.gates)
  rw [negSame] at count
  change 17 + C.gates.countP Extended.isNot ≤ C.gates.length
  omega


lemma atMostTwoNots (C : Circuit) (fan : PEqualNP.MetaComplexity.FanInTwo C)
    (small : C.size ≤ 19)
    (correct : ∀ x : Fin 10 → Bool, C.eval (List.ofFn x) = Extended.f10 x) :
    PEqualNP.NotBracket.notCount C ≤ 2 := by
  have bound := binary_floor17 C fan correct
  omega

namespace Projection

lemma tail_bound_two_constants {d k : Nat} {i j : Fin 10} {U : Finset Extended.Sig}
    (hd : d = 0 ∨ d = 2) (retained : pin i ∈ U)
    (fresh : Extended.bin d (pin i) (pin j) ∉ insert (pin i) U)
    (raw : ∀ a ∈ U, a ∈ Extended.initial)
    (run : Extended.Live true Extended.target k (insert (Extended.bin d (pin i) (pin j)) U)) :
    17 ≤ k := by
  classical
  let c := Extended.bin d (pin i) (pin j)
  have hne : c ≠ pin i := fun h => fresh (by simp [c, h])
  have hn : c ∉ U := fun h => fresh (Finset.mem_insert_of_mem h)
  let front := c :: pin i :: (U.erase (pin i)).toList
  have nd : front.Nodup := by
    apply List.nodup_cons.mpr
    refine ⟨?_, List.nodup_cons.mpr ⟨?_, Finset.nodup_toList _⟩⟩
    · intro hc
      rcases List.mem_cons.mp hc with he | hc
      · exact hne he
      · exact hn (Finset.mem_erase.mp (Finset.mem_toList.mp hc)).2
    · simp
  have eqS : front.toFinset = insert c U := by
    simp only [front, List.toFinset_cons, Finset.toList_toFinset, Finset.insert_erase retained]
  have allowed : Extended.allowed true d := by
    rcases hd with rfl | rfl <;> simp [Extended.allowed]
  have need := tail_project_bound allowed raw run front nd eqS
  have ac : Constant (restrictRows (row i) (Extended.observe (pin i))) := by
    refine ⟨false, ?_⟩
    funext r
    exact deleted_value i r
  have cc : Constant (restrictRows (row i) (Extended.observe c)) :=
    ⟨false, created_left_zero d i j hd⟩
  have charge : 2 ≤ mass ((front.map Extended.observe).map (restrictRows (row i))) := by
    simp only [front, List.map_cons, mass_cons, cost, if_pos ac, if_pos cc]
    omega
  omega


end Projection
end PEqualNP.Outside.L_meta_2592
