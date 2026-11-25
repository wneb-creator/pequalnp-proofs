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
