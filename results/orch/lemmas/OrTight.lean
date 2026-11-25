import Restriction

namespace PEqualNP.Outside.L_meta_2592_aux.SignedFloor

lemma tight_constant_step {R u} {goal : Wire R} {s d ka kb a b rest}
    (hd : allowed u d)
    (tail : Run u goal s (comb d a b :: kept ka a (kept kb b rest)))
    (nc : ¬Constant goal) {roots : List (Wire R)} {p bank L}
    (hp : Reach u roots p bank)
    (hs : supply u bank (a :: b :: rest))
    (hc : Constant a ∨ Constant b)
    (hl : ∀ q bs, Reach u roots q bs → Available u bs goal → L ≤ q)
    (budget : p + s + 1 ≤ L + 1) :
    (Constant a → ka = false) ∧ (Constant b → kb = false) ∧
      ¬Constant (comb d a b) := by
  classical
  have havA := hs a (by simp)
  have havB := hs b (by simp)
  have havG := from_constant_comb hd hc havA havB
  have hsTail : supply u bank
      (comb d a b :: kept ka a (kept kb b rest)) := by
    intro v hv
    rcases List.mem_cons.mp hv with rfl | hv
    · exact havG
    · rcases mem_kept hv with rfl | hv
      · exact havA
      · rcases mem_kept hv with rfl | hv
        · exact havB
        · exact hs v (by simp [hv])
  obtain ⟨q, bs, hq, hg, hmass⟩ := contraction nc tail roots hp hsTail
  have hlow := hl q bs hq hg
  have hm : mass (comb d a b :: kept ka a (kept kb b rest)) = 0 := by omega
  refine ⟨?_, ?_, ?_⟩
  · intro ha
    cases hka : ka
    · rfl
    · have h := mass_retained_constant (comb d a b) a b rest ka kb
        (Or.inl ⟨ha, hka⟩)
      omega
  · intro hb
    cases hkb : kb
    · rfl
    · have h := mass_retained_constant (comb d a b) a b rest ka kb
        (Or.inr ⟨hb, hkb⟩)
      omega
  · intro hg
    rw [mass_cons] at hm
    have hcost : cost (comb d a b) = 1 := by simp [cost, hg]
    omega

lemma nonconstant_false_left {R u d} {b : Wire R} (hd : allowed u d)
    (nc : ¬Constant (comb d (fun _ => false) b)) : d = 1 ∨ d = 3 := by
  rcases allowed_four hd with rfl | rfl | ⟨_, rfl⟩ | ⟨_, rfl⟩
  · exact False.elim (nc ⟨false, by funext r; simp [comb, combine]⟩)
  · exact Or.inl rfl
  · exact False.elim (nc ⟨false, by funext r; simp [comb, combine]⟩)
  · exact Or.inr rfl

lemma nonconstant_false_right {R u d} {a : Wire R} (hd : allowed u d)
    (nc : ¬Constant (comb d a (fun _ => false))) : d = 1 ∨ d = 2 := by
  rcases allowed_four hd with rfl | rfl | ⟨_, rfl⟩ | ⟨_, rfl⟩
  · exact False.elim (nc ⟨false, by funext r; simp [comb, combine]⟩)
  · exact Or.inl rfl
  · exact Or.inr rfl
  · exact False.elim (nc ⟨false, by funext r; simp [comb, combine]⟩)

end PEqualNP.Outside.L_meta_2592_aux.SignedFloor
