import PetersenSeventeenFull

namespace PEqualNP.Outside.L_meta_2373.Live1024

theorem restrict_available {R S : Type} {u : Bool} (rows : S → R)
    {pool : List (Wire R)} {v : Wire R} (h : Available u pool v) :
    Available u (pool.map (restrictRows rows)) (restrictRows rows v) := by
  rcases h with h | ⟨b, rfl⟩ | ⟨hu, h⟩
  · exact Or.inl (List.mem_map.mpr ⟨v, h, rfl⟩)
  · exact Or.inr (Or.inl ⟨b, rfl⟩)
  · exact Or.inr (Or.inr ⟨hu, List.mem_map.mpr ⟨inv v, h, rfl⟩⟩)

theorem restrict_combine {R S : Type} (rows : S → R) (op : Bool) (a b : Wire R) :
    restrictRows rows (combine op a b) =
      combine op (restrictRows rows a) (restrictRows rows b) := by
  cases op <;> rfl

theorem restrict_reach {R S : Type} {u : Bool} (rows : S → R)
    {roots : List (Wire R)} {p bank} (h : Reach u roots p bank) :
    Reach u (roots.map (restrictRows rows)) p (bank.map (restrictRows rows)) := by
  induction h using Reach.ind with
  | start => exact Reach.start
  | two op h ha hb ih =>
    simpa only [List.map_cons, restrict_combine] using
      Reach.two op ih (restrict_available rows ha) (restrict_available rows hb)

def sliceNineCoarse (r : Row) : NineSigned.Row := Fin.ofNat 512 r.val

def sliceNineSection (r : NineSigned.Row) : Row := ⟨r.val, by omega⟩

theorem sliceNineCoarse_section (r : NineSigned.Row) :
    sliceNineCoarse (sliceNineSection r) = r := by
  apply Fin.ext
  simp [sliceNineCoarse, sliceNineSection, Nat.mod_eq_of_lt r.isLt]

def sliceNineLift (a : NineSigned.Sig) : Sig :=
  table (restrictRows sliceNineCoarse (NineSigned.observe a))

theorem observe_sliceNineLift (a : NineSigned.Sig) :
    observe (sliceNineLift a) = restrictRows sliceNineCoarse (NineSigned.observe a) :=
  observe_table _

theorem restrict_sliceNineLift (a : NineSigned.Sig) :
    restrictRows sliceNineSection (observe (sliceNineLift a)) = NineSigned.observe a := by
  rw [observe_sliceNineLift]
  funext r
  simp only [restrictRows, sliceNineCoarse_section]

theorem nine_reach_of_reach {u : Bool} {roots : List (Wire NineSigned.Row)}
    {p bank} (h : Reach u roots p bank) : NineSigned.Reach u roots p bank := by
  induction h using Reach.ind with
  | start => exact NineSigned.Reach.start
  | two op h ha hb ih => exact NineSigned.Reach.two op ih ha hb

theorem Slice_from_nine {u : Bool}
    (rows : NineSigned.Row → Row) (raw : List Sig) (T d : Sig)
    (roots9 : List NineSigned.Sig) (G9 : NineSigned.Sig) (L : Nat)
    (domain : ∀ r, bit (rows r) d = true)
    (goal : restrictRows rows (observe T) = NineSigned.observe G9)
    (covered : ∀ a ∈ raw, NineSigned.Available u (roots9.map NineSigned.observe)
      (restrictRows rows (observe a)))
    (properG : NineSigned.proper G9)
    (prior : NineSigned.Lower u roots9 G9 L) : Slice u raw T d L := by
  let f : Row → Row := fun r => rows (sliceNineCoarse r)
  let roots10 := roots9.map sliceNineLift
  have roots_lift : roots10.map observe =
      (roots9.map NineSigned.observe).map (restrictRows sliceNineCoarse) := by
    simp only [roots10, List.map_map, Function.comp_def, observe_sliceNineLift]
  have roots_section : (roots10.map observe).map (restrictRows sliceNineSection) =
      roots9.map NineSigned.observe := by
    simp only [roots10, List.map_map, Function.comp_def, restrict_sliceNineLift]
  have target_section : restrictRows sliceNineSection (restrictRows f (observe T)) =
      NineSigned.observe G9 := by
    calc
      _ = restrictRows rows (observe T) := by
        funext r
        simp only [restrictRows, f, sliceNineCoarse_section]
      _ = _ := goal
  refine ⟨f, roots10, fun r => domain _, ?_, ?_, ?_⟩
  · intro a ha
    rw [roots_lift]
    exact restrict_available sliceNineCoarse (covered a ha)
  · intro h
    obtain ⟨b, hb⟩ := h
    apply NineSigned.observe_proper properG
    refine ⟨b, ?_⟩
    rw [← target_section, hb]
    rfl
  · intro p bank hp hv
    have hp' := restrict_reach sliceNineSection hp
    rw [roots_section] at hp'
    have hv' := restrict_available sliceNineSection hv
    rw [target_section] at hv'
    exact prior p _ (nine_reach_of_reach hp') hv'

end PEqualNP.Outside.L_meta_2373.Live1024

namespace PEqualNP.Outside.L_meta_2373.NineSigned

def positiveNine : Sig :=
  graph ||| inputs.getD 4 zero ||| inputs.getD 6 zero ||| inputs.getD 7 zero

def positiveNineRaw : List Sig := inputs

def positiveAdjacentZero : Sig :=
  graphGoal 495 ||| inputs.getD 6 zero ||| inputs.getD 7 zero

def positiveAdjacentZeroRaw : List Sig := vars 495

def zeroPositiveMoves : List Move :=
  [(inputs.getD 4 zero, zero, 496),
   (inputs.getD 6 zero, zero, 448),
   (inputs.getD 7 zero, zero, 384)]

def positiveNineWitnesses : List (Sig × Row × Row) :=
  [(inputs.getD 4 zero, 0, 16), (inputs.getD 6 zero, 0, 64),
   (inputs.getD 7 zero, 0, 128)]

def positiveAdjacentZeroWitnesses : List (Sig × Row × Row) :=
  [(inputs.getD 6 zero, 0, 64), (inputs.getD 7 zero, 0, 128)]

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
lemma cofactor_cycle_lower8 : Lower true (vars 303) (graphGoal 303) 8 := by
  have h := valid189 (303, 8) (by decide +kernel)
  simpa only [varsX, show (303 : Nat) < 512 from by decide, ite_true] using h

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
lemma positiveNine_lower11 : Lower true positiveNineRaw positiveNine 11 := by
  have h := lift_ok (u := true) (ms := zeroPositiveMoves)
    (T := positiveNine) (raw := positiveNineRaw) (base := vars 303)
    (G := graphGoal 303) (xs := positiveNineWitnesses) (L := 8)
    (by decide +kernel) (by unfold proper; decide +kernel) (by unfold proper; decide +kernel) cofactor_cycle_lower8
  have count : (positiveNineWitnesses.map Prod.fst).toFinset.card = 3 := by decide +kernel
  simpa only [count] using h

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
lemma positiveAdjacentZero_lower10 : Lower true positiveAdjacentZeroRaw positiveAdjacentZero 10 := by
  have h := lift_ok (u := true) (ms := zeroPositiveMoves)
    (T := positiveAdjacentZero) (raw := positiveAdjacentZeroRaw) (base := vars 303)
    (G := graphGoal 303) (xs := positiveAdjacentZeroWitnesses) (L := 8)
    (by decide +kernel) (by unfold proper; decide +kernel) (by unfold proper; decide +kernel) cofactor_cycle_lower8
  have count : (positiveAdjacentZeroWitnesses.map Prod.fst).toFinset.card = 2 := by decide +kernel
  simpa only [count] using h

lemma available_signed_of_available {R : Type} {u : Bool} {bank : List (Wire R)}
    {w : Wire R} (h : Available u bank w) : Available true bank w := by
  rcases h with h | h | ⟨_, h⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr ⟨rfl, h⟩)

lemma reach_signed_of_reach {R : Type} {u : Bool} {roots bank : List (Wire R)}
    {p : Nat} (h : Reach u roots p bank) : Reach true roots p bank := by
  induction h using Reach.ind with
  | start => exact Reach.start
  | two op _ ha hb ih =>
    exact Reach.two op ih (available_signed_of_available ha) (available_signed_of_available hb)

lemma lower_mode_of_signed {u : Bool} {roots : List Sig} {T : Sig} {L : Nat}
    (h : Lower true roots T L) : Lower u roots T L := by
  intro p bank run available
  exact h p bank (reach_signed_of_reach run) (available_signed_of_available available)

lemma positiveNine_mono_lower11 : Lower false positiveNineRaw positiveNine 11 :=
  lower_mode_of_signed positiveNine_lower11

lemma positiveAdjacentZero_mono_lower10 : Lower false positiveAdjacentZeroRaw positiveAdjacentZero 10 :=
  lower_mode_of_signed positiveAdjacentZero_lower10

end PEqualNP.Outside.L_meta_2373.NineSigned

namespace PEqualNP.Outside.L_meta_2373.PositiveProfiles

open PEqualNP.Outside.L_meta_2373

def permutation (c : Fin 4) : Fin 10 → Fin 10 :=
  ![![1, 2, 7, 5, 0, 6, 3, 9, 8, 4],
    ![7, 2, 3, 8, 5, 9, 1, 4, 6, 0],
    ![8, 3, 4, 9, 6, 5, 2, 0, 7, 1],
    ![5, 0, 4, 9, 7, 8, 1, 3, 6, 2]] c

def inverse (c : Fin 4) : Fin 10 → Fin 10 :=
  ![![4, 0, 1, 6, 9, 3, 5, 2, 8, 7],
    ![9, 6, 1, 2, 7, 4, 8, 0, 3, 5],
    ![7, 9, 6, 1, 2, 5, 4, 8, 0, 3],
    ![1, 6, 9, 7, 2, 0, 8, 4, 5, 3]] c

def rows (c : Fin 4) (r : NineSigned.Row) : Live1024.Row :=
  Fin.ofNat 1024 (2 ^ (permutation c 9).val + ∑ i : Fin 9,
    if (c = 0 ∨ i ≠ 4) ∧ r.val.testBit i.val then
      2 ^ (permutation c i.castSucc).val else 0)

def domain (c : Fin 4) : Live1024.Sig :=
  Live1024.inputs.getD (permutation c 9).val Live1024.zero &&&
    (if c = 0 then Live1024.one else
      ~~~(Live1024.inputs.getD (permutation c 4).val Live1024.zero))

def target (c : Fin 4) : NineSigned.Sig :=
  if c = 0 then NineSigned.positiveNine else NineSigned.positiveAdjacentZero

def roots (c : Fin 4) : List NineSigned.Sig :=
  if c = 0 then NineSigned.positiveNineRaw else NineSigned.positiveAdjacentZeroRaw

def bound (c : Fin 4) : Nat := if c = 0 then 11 else 10

def inputMap (c : Fin 4) (i : Fin 10) : NineSigned.Sig :=
  if inverse c i = 9 then NineSigned.one
  else if c ≠ 0 ∧ inverse c i = 4 then NineSigned.zero
  else NineSigned.inputs.getD (inverse c i).val NineSigned.zero

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
lemma rows_domain : ∀ (c : Fin 4) (r : NineSigned.Row),
    Live1024.bit (rows c r) (domain c) = true := by
  intro c
  fin_cases c <;> decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
lemma rows_goal : ∀ (c : Fin 4) (r : NineSigned.Row),
    Live1024.observe Live1024.graph (rows c r) = NineSigned.observe (target c) r := by
  intro c
  fin_cases c <;> decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
lemma rows_input : ∀ (c : Fin 4) (i : Fin 10) (r : NineSigned.Row),
    Live1024.observe (Live1024.inputs.getD i.val Live1024.zero) (rows c r) =
      NineSigned.observe (inputMap c i) r := by
  intro c i
  fin_cases c <;> fin_cases i <;> decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
lemma inputMap_free : ∀ (c : Fin 4) (i : Fin 10),
    NineSigned.freeWord (roots c) (inputMap c i) = true := by
  decide +kernel

lemma rows_available {u : Bool} (c : Fin 4) (i : Fin 10) :
    NineSigned.Available u ((roots c).map NineSigned.observe)
      (Live1024.restrictRows (rows c)
        (Live1024.observe (Live1024.inputs.getD i.val Live1024.zero))) := by
  have heq : Live1024.restrictRows (rows c)
      (Live1024.observe (Live1024.inputs.getD i.val Live1024.zero)) =
      NineSigned.observe (inputMap c i) := by
    funext r
    exact rows_input c i r
  rw [heq]
  exact NineSigned.freeWord_ok (inputMap_free c i)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
lemma target_proper : ∀ c : Fin 4, NineSigned.proper (target c) := by
  unfold NineSigned.proper
  decide +kernel

lemma target_lower {u : Bool} (c : Fin 4) :
    NineSigned.Lower u (roots c) (target c) (bound c) := by
  by_cases h : c = 0
  · simpa only [roots, target, bound, if_pos h] using
      (NineSigned.lower_mode_of_signed (u := u) NineSigned.positiveNine_lower11)
  · simpa only [roots, target, bound, if_neg h] using
      (NineSigned.lower_mode_of_signed (u := u) NineSigned.positiveAdjacentZero_lower10)

end PEqualNP.Outside.L_meta_2373.PositiveProfiles

namespace PEqualNP.Outside.L_meta_2373.ZeroProfiles

open PEqualNP.Outside.L_meta_2373

def domain (v : Fin 10) : Live1024.Sig :=
  ~~~(Live1024.inputs.getD v.val Live1024.zero)

lemma rows_domain (v : Fin 10) (r : NineSigned.Row) :
    Live1024.bit (rowMap v r) (domain v) = true := by
  have hm := rowMap_missing v r
  change Live1024.bit (rowMap v r) (Live1024.inputs.getD v.val Live1024.zero) = false at hm
  simpa [domain, Live1024.bit, (rowMap v r).isLt] using congrArg Bool.not hm

lemma rows_available {u : Bool} (v i : Fin 10) :
    NineSigned.Available u (NineSigned.inputs.map NineSigned.observe)
      (Live1024.restrictRows (rowMap v)
        (Live1024.observe (Live1024.inputs.getD i.val Live1024.zero))) := by
  by_cases hi : i = v
  · subst i
    exact Or.inr (Or.inl ⟨false, funext (rowMap_missing v)⟩)
  · obtain ⟨j, hj⟩ := (relabel_bijective v).2 i
    have hne : j ≠ (9 : Fin 10) := by
      intro h
      subst j
      exact hi (hj.symm.trans (relabel_last v))
    have hjlt : j.val < 9 := by
      have hlt := j.isLt
      have hn : j.val ≠ 9 := fun h => hne (Fin.ext h)
      omega
    let k : Fin 9 := ⟨j.val, hjlt⟩
    have hk : relabel v k.castSucc = i := hj
    have heq : Live1024.restrictRows (rowMap v)
        (Live1024.observe (Live1024.inputs.getD i.val Live1024.zero)) =
          NineSigned.observe (NineSigned.inputs.getD k.val NineSigned.zero) := by
      funext r
      rw [← hk]
      exact rowMap_input v k r
    apply Or.inl
    rw [heq]
    apply List.mem_map.mpr
    refine ⟨NineSigned.inputs.getD k.val NineSigned.zero, ?_, rfl⟩
    have hm : NineSigned.inputs.getD k.val NineSigned.zero ∈
        List.ofFn (fun j : Fin 9 => NineSigned.inputs.getD j.val NineSigned.zero) :=
      List.mem_ofFn.mpr ⟨k, rfl⟩
    rw [NineSigned.input_list] at hm
    exact hm

end PEqualNP.Outside.L_meta_2373.ZeroProfiles

namespace PEqualNP.Outside.L_meta_2373.ZeroProfiles

open PEqualNP.Outside.L_meta_2373

lemma slice {u : Bool} (v : Fin 10) :
    Live1024.Slice u Live1024.inputs Live1024.graph (domain v) 15 := by
  apply Live1024.Slice_from_nine (rowMap v) Live1024.inputs Live1024.graph (domain v)
    NineSigned.inputs NineSigned.graph 15
  · exact rows_domain v
  · funext r
    exact rowMap_graph v r
  · intro a ha
    rw [← Live1024.input_list] at ha
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp ha
    exact rows_available v i
  · exact NineSigned.graph_proper
  · exact NineSigned.lower_mode_of_signed NineSigned.nine_reach_lower

end PEqualNP.Outside.L_meta_2373.ZeroProfiles

namespace PEqualNP.Outside.L_meta_2373.PositiveProfiles

open PEqualNP.Outside.L_meta_2373

lemma slice {u : Bool} (c : Fin 4) :
    Live1024.Slice u Live1024.inputs Live1024.graph (domain c) (bound c) := by
  apply Live1024.Slice_from_nine (rows c) Live1024.inputs Live1024.graph (domain c)
    (roots c) (target c) (bound c)
  · exact rows_domain c
  · funext r
    exact rows_goal c r
  · intro a ha
    rw [← Live1024.input_list] at ha
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp ha
    exact rows_available c i
  · exact target_proper c
  · exact target_lower c

end PEqualNP.Outside.L_meta_2373.PositiveProfiles

namespace PEqualNP.Outside.L_meta_2373.SliceProfiles

open PEqualNP.Outside.L_meta_2373

def domains : List Live1024.Sig :=
  List.ofFn ZeroProfiles.domain ++ List.ofFn PositiveProfiles.domain

def bounds : List Nat := List.replicate 10 15 ++ [11, 10, 10, 10]

lemma all_slices {u : Bool} : ∀ i : Fin 14,
    Live1024.Slice u Live1024.inputs Live1024.graph
      (domains.getD i.val Live1024.zero) (bounds.getD i.val 0) := by
  intro i
  fin_cases i
  · exact ZeroProfiles.slice 0
  · exact ZeroProfiles.slice 1
  · exact ZeroProfiles.slice 2
  · exact ZeroProfiles.slice 3
  · exact ZeroProfiles.slice 4
  · exact ZeroProfiles.slice 5
  · exact ZeroProfiles.slice 6
  · exact ZeroProfiles.slice 7
  · exact ZeroProfiles.slice 8
  · exact ZeroProfiles.slice 9
  · exact PositiveProfiles.slice 0
  · exact PositiveProfiles.slice 1
  · exact PositiveProfiles.slice 2
  · exact PositiveProfiles.slice 3

end PEqualNP.Outside.L_meta_2373.SliceProfiles
