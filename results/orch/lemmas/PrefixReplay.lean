import PEqualNP.Outside.L_meta_2592

namespace PEqualNP.Outside.L_meta_2592
namespace PrefixReplay

lemma transfer {R : Type} {u : Bool} {roots bank : List (Wire R)}
    (hs : supply u bank roots) {v : Wire R} (hv : Available u roots v) :
    Available u bank v := by
  rcases hv with hv | hv | ⟨hu, hv⟩
  · exact hs v hv
  · exact Or.inr (Or.inl hv)
  · simpa only [inv_inv'] using avail_inv hu (hs (inv v) hv)

lemma replay {R : Type} {u : Bool} {xs roots : List (Wire R)}
    {s : Nat} {ws : List (Wire R)} (run : Reach u xs s ws)
    {p : Nat} {bank : List (Wire R)} (before : Reach u roots p bank)
    (hs : supply u bank xs) :
    ∃ q next, Reach u roots q next ∧ supply u next ws ∧ q ≤ p + s := by
  induction run using Reach.ind generalizing p bank with
  | start => exact ⟨p, bank, before, hs, by omega⟩
  | @two t bs a b op h ha hb ih =>
    obtain ⟨q, next, hq, hnext, bound⟩ := ih before hs
    have aa := transfer hnext ha
    have bb := transfer hnext hb
    refine ⟨q + 1, combine op a b :: next, Reach.two op hq aa bb, ?_, by omega⟩
    intro v hv
    rcases List.mem_cons.mp hv with rfl | hv
    · exact Or.inl (by simp)
    · exact available_cons _ (hnext v hv)

lemma restrict_available {R S : Type} (rows : S → R) {u : Bool}
    {bank : List (Wire R)} {a : Wire R} (h : Available u bank a) :
    Available u (bank.map (restrictRows rows)) (restrictRows rows a) := by
  rcases h with h | ⟨v, rfl⟩ | ⟨hu, h⟩
  · exact Or.inl (List.mem_map.mpr ⟨a, h, rfl⟩)
  · exact Or.inr (Or.inl ⟨v, rfl⟩)
  · refine Or.inr (Or.inr ⟨hu, ?_⟩)
    exact List.mem_map.mpr ⟨inv a, h, rfl⟩

lemma restrict_combine {R S : Type} (rows : S → R) (op : Bool)
    (a b : Wire R) :
    restrictRows rows (combine op a b) =
      combine op (restrictRows rows a) (restrictRows rows b) := by
  cases op <;> rfl

lemma restrict_reach {R S : Type} (rows : S → R) {u : Bool}
    {roots bank : List (Wire R)} {p : Nat} (run : Reach u roots p bank) :
    Reach u (roots.map (restrictRows rows)) p (bank.map (restrictRows rows)) := by
  induction run using Reach.ind with
  | start => exact Reach.start
  | two op h ha hb ih =>
    simpa only [List.map_cons, restrict_combine] using
      Reach.two op ih (restrict_available rows ha) (restrict_available rows hb)

lemma saved_projection {R S : Type} (rows : S → R) {u : Bool}
    {original bank out : List (Wire R)} {p q : Nat}
    (before : Reach u original p bank) {a b : Wire R} (op : Bool)
    (ha : Available u bank a) (hb : Available u bank b)
    (after : Reach u (combine op a b :: bank) q out)
    (constant : Constant (restrictRows rows a) ∨ Constant (restrictRows rows b))
    {roots initial : List (Wire S)} {r : Nat}
    (initialRun : Reach u roots r initial)
    (initialSupply : supply u initial (original.map (restrictRows rows))) :
    ∃ t next, Reach u roots t next ∧ supply u next (out.map (restrictRows rows)) ∧
      t ≤ r + p + q := by
  obtain ⟨j, middle, hm, supplyMiddle, jm⟩ :=
    replay (restrict_reach rows before) initialRun initialSupply
  have aa := transfer supplyMiddle (restrict_available rows ha)
  have bb := transfer supplyMiddle (restrict_available rows hb)
  have outputAvailable := from_constant op constant aa bb
  have supplyAfter : supply u middle ((combine op a b :: bank).map (restrictRows rows)) := by
    intro v hv
    simp only [List.map_cons, restrict_combine] at hv
    rcases List.mem_cons.mp hv with rfl | hv
    · exact outputAvailable
    · exact supplyMiddle v hv
  obtain ⟨t, next, ht, hnext, tq⟩ := replay (restrict_reach rows after) hm supplyAfter
  exact ⟨t, next, ht, hnext, by omega⟩

end PrefixReplay
end PEqualNP.Outside.L_meta_2592
