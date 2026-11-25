import ElimManyCount
import PairReaderCharge
import RestrictionEight

namespace PEqualNP.Outside.L_meta_1884.SoleAndRestriction

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.Helpers ElimManyCount

lemma and_false_step (n : Nat) (acc : List Stat × List Gate) (t a : Nat)
    (ht : acc.1.getD t (Stat.const false) = Stat.const false) :
    elimStep n acc ⟨GateOp.and,[t,a]⟩ = (acc.1 ++ [Stat.const false],acc.2) := by
  cases ha : acc.1.getD a (Stat.const false) <;>
    simp only [elimStep, List.map_cons, List.map_nil, ht, ha, simplify, simpAnd]
  all_goals simp

lemma and_false_step_right (n : Nat) (acc : List Stat × List Gate) (t a : Nat)
    (ht : acc.1.getD t (Stat.const false) = Stat.const false) :
    elimStep n acc ⟨GateOp.and,[a,t]⟩ = (acc.1 ++ [Stat.const false],acc.2) := by
  cases ha : acc.1.getD a (Stat.const false) with
  | const b =>
    cases b <;>
      simp only [elimStep, List.map_cons, List.map_nil, ht, ha, simplify, simpAnd] <;> simp
  | wire j =>
    simp only [elimStep, List.map_cons, List.map_nil, ht, ha, simplify, simpAnd]
    simp

theorem two_losses (n : Nat) (pre post : List Gate) (acc : List Stat × List Gate)
    (t a : Nat) (hp : ∀ g ∈ pre, NOk g) (hs : ∀ g ∈ post, NOk g)
    (ht : t < acc.1.length)
    (hfalse : acc.1.getD t (Stat.const false) = Stat.const false)
    (hreader : ∃ g ∈ post, acc.1.length + pre.length ∈ g.inputs) :
    (elim n (pre ++ ⟨GateOp.and,[t,a]⟩ :: post) acc).2.length + 2 ≤
      acc.2.length + (pre ++ ⟨GateOp.and,[t,a]⟩ :: post).length := by
  have hc : constant {t} acc.1 := by
    intro k hk
    have heq : k = t := Finset.mem_singleton.mp hk
    subst k
    exact ⟨ht,false,hfalse⟩
  have hmid : (elim n pre acc).1.getD t (Stat.const false) = Stat.const false := by
    rw [elim_getD n t _ pre acc ht]
    exact hfalse
  have hcost := constant_step_count n {t} pre post acc hp hs hc
    ⟨GateOp.and,[t,a]⟩ false (and_false_step n (elim n pre acc) t a hmid)
  obtain ⟨g,hg,hq⟩ := hreader
  have hread : reads (insert (acc.1.length + pre.length) {t}) g = true := by
    apply List.any_eq_true.mpr
    refine ⟨acc.1.length + pre.length,hq,?_⟩
    simp
  have hcount := PairReaderCharge.count_one (reads (insert (acc.1.length + pre.length) {t}))
    post g hg hread
  dsimp only at hcost
  omega

theorem constant_with_reader_losses (n : Nat) (pre post : List Gate)
    (acc : List Stat × List Gate) (g : Gate) (b : Bool)
    (hp : ∀ g ∈ pre, NOk g) (hs : ∀ g ∈ post, NOk g)
    (hstep : elimStep n (elim n pre acc) g =
      ((elim n pre acc).1 ++ [Stat.const b],(elim n pre acc).2))
    (hreader : ∃ g ∈ post, acc.1.length + pre.length ∈ g.inputs) :
    (elim n (pre ++ g :: post) acc).2.length + 2 ≤
      acc.2.length + (pre ++ g :: post).length := by
  have hcost := constant_step_count n ∅ pre post acc hp hs (by simp [constant]) g b hstep
  obtain ⟨g',hg',hq⟩ := hreader
  have hread : reads (insert (acc.1.length + pre.length) ∅) g' = true := by
    exact List.any_eq_true.mpr ⟨acc.1.length + pre.length,hq,by simp⟩
  have hcount := PairReaderCharge.count_one (reads (insert (acc.1.length + pre.length) ∅))
    post g' hg' hread
  dsimp only at hcost
  omega

theorem and_reader_floor (pre post : List Gate) (g : Gate) (a o : Nat)
    (hgate : g = ⟨GateOp.and,[2,a]⟩ ∨ g = ⟨GateOp.and,[a,2]⟩)
    (hm : PEqualNP.MetaComplexity.Monotone2 ⟨pre ++ g :: post,o⟩)
    (hreader : ∃ r ∈ post, 9 + pre.length ∈ r.inputs)
    (hcorrect : ∀ y : Fin 8 → Bool,
      Circuit.eval ⟨pre ++ g :: post,o⟩ (RestrictionEight.seed y) = EightExtension.eight y) :
    14 ≤ (Circuit.mk (pre ++ g :: post) o).size := by
  let acc : List Stat × List Gate := (RestrictionEight.inputMap,[])
  have hnok := RestrictionEight.mono_nok ⟨pre ++ g :: post,o⟩ hm
  have hp : ∀ r ∈ pre, NOk r := by
    intro r hr
    exact hnok r (List.mem_append.mpr (Or.inl hr))
  have hs : ∀ r ∈ post, NOk r := by
    intro r hr
    exact hnok r (List.mem_append.mpr (Or.inr (List.mem_cons_of_mem _ hr)))
  have hmid : (elim 8 pre acc).1.getD 2 (Stat.const false) = Stat.const false := by
    rw [elim_getD 8 2 _ pre acc (by decide)]
    rfl
  have hstep : elimStep 8 (elim 8 pre acc) g =
      ((elim 8 pre acc).1 ++ [Stat.const false],(elim 8 pre acc).2) := by
    rcases hgate with rfl | rfl
    · exact and_false_step 8 (elim 8 pre acc) 2 a hmid
    · exact and_false_step_right 8 (elim 8 pre acc) 2 a hmid
  have hcost := constant_with_reader_losses 8 pre post acc g false hp hs hstep hreader
  have hfloor := RestrictionEight.compiled_floor ⟨pre ++ g :: post,o⟩ hm hcorrect
  change _ ≤ (pre ++ g :: post).length
  change (elim 8 (pre ++ g :: post) acc).2.length ≥ 12 at hfloor
  simp only [acc, List.length_nil, zero_add] at hcost
  dsimp only [acc] at hfloor
  omega

end PEqualNP.Outside.L_meta_1884.SoleAndRestriction
