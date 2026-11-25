import SliceFromNine

namespace PEqualNP.Outside.L_meta_2373.MonotoneNineFromPetersen
open Live1024

def embed (v : NineSigned.Wire NineSigned.Row) : Wire Row := restrictRows sliceNineCoarse v

def col (i : Fin 10) : Wire Row := observe (inputs.getD i.val zero)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma input_lift_bits : ∀ (i : Fin 9) (r : Row),
    embed (NineSigned.observe (NineSigned.inputs.getD i.val NineSigned.zero)) r =
      col i.castSucc r := by
  decide +kernel

lemma input_lift (i : Fin 9) :
    embed (NineSigned.observe (NineSigned.inputs.getD i.val NineSigned.zero)) = col i.castSucc :=
  funext (input_lift_bits i)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma extension_bits : ∀ r : Row,
    combine true (embed (NineSigned.observe NineSigned.graph))
      (combine false (col 9) (combine true (combine true (col 4) (col 6)) (col 7))) r =
        observe graph r := by
  decide +kernel

lemma extension_identity :
    combine true (embed (NineSigned.observe NineSigned.graph))
      (combine false (col 9) (combine true (combine true (col 4) (col 6)) (col 7))) =
        observe graph := funext extension_bits

lemma input_member (i : Fin 10) : col i ∈ inputs.map observe := by
  apply List.mem_map.mpr
  refine ⟨inputs.getD i.val zero, ?_, rfl⟩
  rw [← input_list]
  exact List.mem_ofFn.mpr ⟨i, rfl⟩

lemma embedded_available {pool : List (NineSigned.Wire NineSigned.Row)}
    {bank : List (Wire Row)} {v : NineSigned.Wire NineSigned.Row}
    (supply : ∀ a ∈ pool, Available false bank (embed a))
    (available : NineSigned.Available false pool v) : Available false bank (embed v) := by
  rcases available with h | ⟨b, hb⟩ | ⟨bad, _⟩
  · exact supply v h
  · exact Or.inr (Or.inl ⟨b, by rw [hb]; rfl⟩)
  · cases bad

lemma lift_reach {p : Nat} {pool : List (NineSigned.Wire NineSigned.Row)}
    (trace : NineSigned.Reach false (NineSigned.inputs.map NineSigned.observe) p pool) :
    ∃ bank, Reach false (inputs.map observe) p bank ∧
      ∀ a ∈ pool, Available false bank (embed a) := by
  induction trace using NineSigned.Reach.ind with
  | start =>
    refine ⟨inputs.map observe, Reach.start, ?_⟩
    intro a ha
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp ha
    rw [← NineSigned.input_list] at hv
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hv
    rw [input_lift]
    exact Or.inl (input_member _)
  | @two p pool a b op trace ha hb ih =>
    obtain ⟨bank, reach, supply⟩ := ih
    refine ⟨combine op (embed _) (embed _) :: bank,
      Reach.two op reach (embedded_available supply ha) (embedded_available supply hb), ?_⟩
    intro v hv
    rcases List.mem_cons.mp hv with rfl | old
    · have eq : embed (NineSigned.combine op a b) = combine op (embed a) (embed b) := by
        cases op <;> rfl
      rw [eq]
      exact Or.inl (by simp)
    · exact available_cons _ (supply v old)

lemma initial_available {R : Type} {roots bank : List (Wire R)} {p : Nat}
    (trace : Reach false roots p bank) {v : Wire R} (mem : v ∈ roots) :
    Available false bank v := by
  induction trace using Reach.ind with
  | start => exact Or.inl mem
  | two op trace ha hb ih => exact available_cons _ ih

lemma nine_monotone16_of_petersen20 (prior : Lower false inputs graph 20) :
    NineSigned.Lower false NineSigned.inputs NineSigned.graph 16 := by
  intro p pool trace goal
  obtain ⟨bank, reach, supply⟩ := lift_reach trace
  have target := embedded_available supply goal
  have x4 := initial_available reach (input_member 4)
  have x6 := initial_available reach (input_member 6)
  have x7 := initial_available reach (input_member 7)
  have x9 := initial_available reach (input_member 9)
  have one := Reach.two true reach x4 x6
  have two := Reach.two true one (Or.inl List.mem_cons_self) (available_cons _ x7)
  have three := Reach.two false two (available_cons _ (available_cons _ x9))
    (Or.inl List.mem_cons_self)
  have four := Reach.two true three
    (available_cons _ (available_cons _ (available_cons _ target)))
    (Or.inl List.mem_cons_self)
  have lower := prior (p + 1 + 1 + 1 + 1) _ four (by
    rw [← extension_identity]
    exact Or.inl (by simp))
  omega

end PEqualNP.Outside.L_meta_2373.MonotoneNineFromPetersen
