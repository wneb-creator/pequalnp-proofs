import SignedCore

namespace PEqualNP.Outside.L_meta_2592.SignedFloor

lemma available_restrict {R S : Type} (rows : S → R) {u : Bool}
    {bank : List (Wire R)} {v : Wire R} (h : Available u bank v) :
    Available u (bank.map (restrictRows rows)) (restrictRows rows v) := by
  rcases h with hm | hc | ⟨hu,hm⟩
  · exact Or.inl (List.mem_map.mpr ⟨v,hm,rfl⟩)
  · obtain ⟨b,hb⟩ := hc
    exact Or.inr (Or.inl ⟨b,congrArg (restrictRows rows) hb⟩)
  · refine Or.inr (Or.inr ⟨hu,?_⟩)
    exact List.mem_map.mpr ⟨inv v,hm,rfl⟩

lemma reach_restrict {R S : Type} (rows : S → R) {u : Bool}
    {roots bank : List (Wire R)} {p : Nat} (h : Reach u roots p bank) :
    Reach u (roots.map (restrictRows rows)) p (bank.map (restrictRows rows)) := by
  induction h using Reach.ind with
  | start => exact Reach.start
  | two op h ha hb ih =>
    have hnew := Reach.two op ih (available_restrict rows ha) (available_restrict rows hb)
    cases op <;> exact hnew

end PEqualNP.Outside.L_meta_2592.SignedFloor
