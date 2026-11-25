import PEqualNP.Defs

/- Draft source only. This file has not been checked by Lean.
   Audited data: the generic row with points 0, 1, 5 and lines 3, 6, 7, 8.
   The 98-wire tables require a separate connection to actual base-circuit semantics. -/

namespace PEqualNP.Outside.L_meta_1896_aux.MarginalCoverFinite

open scoped BigOperators

def maximalMasks : List Nat := [
    15, 2147488260, 4311779328, 77376520200, 1030792151040, 29842525407360, 263882806395120,
    477480406517760, 567427524465152, 3694638917517600, 4222124650663680, 4238790332719584]

def maximalSupport (i : Fin 12) : Finset (Fin 52) :=
  Finset.univ.filter fun a => (maximalMasks.getD i.val 0).testBit a.val

def witnessFlags : Finset (Fin 52) := {0, 39, 14, 4, 25, 29, 10, 13, 12}

lemma witnessFlags_card : witnessFlags.card = 9 := by decide

lemma maximal_hits_at_most_one :
    ∀ i : Fin 12, (maximalSupport i ∩ witnessFlags).card ≤ 1 := by decide

lemma nine_le_maximal_cover_card (s : Finset (Fin 12))
    (hcover : ∀ a : Fin 52, ∃ i ∈ s, a ∈ maximalSupport i) : 9 ≤ s.card := by
  have hsub : witnessFlags ⊆ s.biUnion (fun i => maximalSupport i ∩ witnessFlags) := by
    intro a ha
    obtain ⟨i, hi, hai⟩ := hcover a
    exact Finset.mem_biUnion.mpr ⟨i, hi, Finset.mem_inter.mpr ⟨hai, ha⟩⟩
  calc
    9 = witnessFlags.card := witnessFlags_card.symm
    _ ≤ (s.biUnion (fun i => maximalSupport i ∩ witnessFlags)).card :=
      Finset.card_le_card hsub
    _ ≤ ∑ i ∈ s, (maximalSupport i ∩ witnessFlags).card := Finset.card_biUnion_le
    _ ≤ ∑ _i ∈ s, (1 : Nat) :=
      Finset.sum_le_sum (fun i _ => maximal_hits_at_most_one i)
    _ = s.card := by simp

lemma small_maximal_subsets_fail :
    ∀ s : Finset (Fin 12), s.card ≤ 8 →
      ¬ (∀ a : Fin 52, ∃ i ∈ s, a ∈ maximalSupport i) := by
  intro s hsize hcover
  have h := nine_le_maximal_cover_card s hcover
  omega

lemma nine_le_cover_card {ι : Type} [DecidableEq ι]
    (s : Finset ι) (support : ι → Finset (Fin 52)) (dominator : ι → Fin 12)
    (hdom : ∀ i ∈ s, support i ⊆ maximalSupport (dominator i))
    (hcover : ∀ a : Fin 52, ∃ i ∈ s, a ∈ support i) : 9 ≤ s.card := by
  have hmax : ∀ a : Fin 52, ∃ j ∈ s.image dominator, a ∈ maximalSupport j := by
    intro a
    obtain ⟨i, hi, hai⟩ := hcover a
    exact ⟨dominator i, Finset.mem_image.mpr ⟨i, hi, rfl⟩, hdom i hi hai⟩
  exact (nine_le_maximal_cover_card (s.image dominator) hmax).trans Finset.card_image_le

def wireMasks : List Nat := [
    567348000456705, 70368752566290, 1125900041060640, 2147488260, 34359812160, 549756994560, 8796111912960,
    140737790607360, 2251804649717760, 77376520200, 1238024323200, 19808389171200, 316934226739200, 15,
    240, 3840, 61440, 983040, 15728640, 251658240, 4026531840,
    64424509440, 1030792151040, 16492674416640, 263882790666240, 4222124650659840, 1125934400872800, 1127172425196000,
    2252354406712320, 2261150518625280, 457672017346560, 477480406517760, 3377704690778400, 3694638917517600, 584116806720,
    141321907414080, 10034136236160, 29842525407360, 4222124651642880, 4238617326059520, 65280, 4026597120,
    64676167680, 1095468318720, 4222124650663680, 4222124902321920, 1044480, 64425553920, 16496700948480,
    17527493099520, 4238790332719584, 536888320, 292091330560, 292628218880, 554067558400, 268470272,
    554336028672, 3659174831456512, 34360205312, 12233140600832, 3659209191661824, 3671442332262656, 33555456,
    17179885568, 275414777856, 17213441024, 292628218880, 16779264, 4295000064, 550024249344,
    4311779328, 554336028672, 3671442332262656, 292628218880, 554336028672, 3671734960481536, 3672289296510208,
    224, 7340032, 193514046488576, 7340256, 193514053828832, 567348000456704, 2147488256,
    77376520192, 567350147944960, 567427524465152, 15728880, 263882806395120, 70368752566288, 637716753022995,
    637718900511255, 637796277031455, 15, 3865803350339040, 4433230874804192, 4503599627370480, 4503599627370495]

def wireBadValues : List Bool := [
    true, true, false, false, false, true, false,
    false, false, false, false, false, false, false,
    false, false, true, false, false, true, true,
    true, false, false, false, false, false, false,
    true, true, false, false, false, false, true,
    true, false, false, false, false, true, true,
    true, true, false, true, true, true, true,
    true, false, true, false, true, true, false,
    true, false, true, false, true, true, true,
    false, false, true, true, false, false, true,
    false, true, false, true, true, true, true,
    false, false, false, false, false, false, false,
    false, false, false, false, false, false, true,
    true, true, false, true, true, true, true]

def wireDominators : List (Fin 12) := [
    0, 0, 9, 1, 11, 0, 5,
    7, 9, 3, 5, 5, 7, 0,
    6, 10, 0, 11, 6, 0, 0,
    0, 4, 11, 6, 10, 11, 11,
    0, 0, 7, 7, 9, 9, 0,
    0, 5, 5, 11, 11, 0, 0,
    0, 0, 10, 0, 0, 0, 0,
    0, 11, 0, 7, 0, 0, 7,
    0, 9, 0, 5, 0, 0, 0,
    5, 9, 0, 0, 2, 2, 0,
    2, 0, 11, 0, 0, 0, 0,
    6, 6, 6, 6, 6, 8, 1,
    3, 8, 8, 6, 6, 6, 0,
    0, 0, 0, 0, 0, 0, 0]

lemma table_lengths : maximalMasks.length = 12 ∧ wireMasks.length = 98 ∧
    wireBadValues.length = 98 ∧ wireDominators.length = 98 := by decide

def wireGood (a : Fin 52) (i : Fin 98) : Bool := (wireMasks.getD i.val 0).testBit a.val

def wireBad (i : Fin 98) : Bool := wireBadValues.getD i.val false

def wireDominator (i : Fin 98) : Fin 12 := wireDominators.getD i.val 0

def wireSupport (i : Fin 98) : Finset (Fin 52) :=
  Finset.univ.filter fun a => wireGood a i = true

lemma false_wire_dominated : ∀ i : Fin 98, wireBad i = false →
    wireSupport i ⊆ maximalSupport (wireDominator i) := by decide

lemma nine_le_table_cover_card (s : Finset (Fin 98))
    (hfalse : ∀ i ∈ s, wireBad i = false)
    (hcover : ∀ a : Fin 52, ∃ i ∈ s, wireGood a i = true) : 9 ≤ s.card := by
  apply nine_le_cover_card s wireSupport wireDominator
  · intro i hi
    exact false_wire_dominated i (hfalse i hi)
  · intro a
    obtain ⟨i, hi, hai⟩ := hcover a
    exact ⟨i, hi, by simp [wireSupport, hai]⟩

lemma eight_le_appended_or_count (k : Nat)
    (hcover : ∃ s : Finset (Fin 98), s.card ≤ k + 1 ∧
      (∀ i ∈ s, wireBad i = false) ∧
      (∀ a : Fin 52, ∃ i ∈ s, wireGood a i = true)) : 8 ≤ k := by
  obtain ⟨s, hsize, hfalse, hflags⟩ := hcover
  have h := nine_le_table_cover_card s hfalse hflags
  omega

end PEqualNP.Outside.L_meta_1896_aux.MarginalCoverFinite
