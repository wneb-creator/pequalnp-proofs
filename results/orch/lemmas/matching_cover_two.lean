import Mathlib.Tactic
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2602_aux.MatchingCover

lemma injective_three {α : Type*} (a b c : α)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    Function.Injective ![a, b, c] := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all

lemma cover_two_branch {α β : Type*} [DecidableEq α] [DecidableEq β]
    (R : α → β → Prop)
    (noThree : ∀ a b c : α, ∀ u v w : β,
      a ≠ b → a ≠ c → b ≠ c → u ≠ v → u ≠ w → v ≠ w →
      R a u → R b v → R c w → False)
    (a b c : α) (u v : β)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (huv : u ≠ v)
    (hau : R a u) (hbv : R b v) (hcu : R c u) :
    ∃ P : Finset α, ∃ Q : Finset β, P.card + Q.card ≤ 2 ∧
      ∀ p q, R p q → p ∈ P ∨ q ∈ Q := by
  classical
  have alternate (d : α) : ∃ x, R x u ∧ x ≠ b ∧ x ≠ d := by
    by_cases hda : d = a
    · exact ⟨c, hcu, (Ne.symm hbc), by simpa [hda] using (Ne.symm hac)⟩
    · exact ⟨a, hau, hab, (Ne.symm hda)⟩
  by_cases cols : ∀ p q, R p q → q = u ∨ q = v
  · refine ⟨∅, {u, v}, by simp [huv], ?_⟩
    intro p q hpq
    exact Or.inr (by simpa using cols p q hpq)
  · push Not at cols
    obtain ⟨d, z, hdz, hzu, hzv⟩ := cols
    have hdb : d = b := by
      by_contra hdb
      obtain ⟨x, hxu, hxb, hxd⟩ := alternate d
      exact noThree x b d u v z hxb hxd (Ne.symm hdb) huv (Ne.symm hzu) (Ne.symm hzv)
        hxu hbv hdz
    subst d
    refine ⟨{b}, {u}, by simp, ?_⟩
    intro p q hpq
    by_cases hpb : p = b
    · exact Or.inl (by simp [hpb])
    by_cases hqu : q = u
    · exact Or.inr (by simp [hqu])
    obtain ⟨x, hxu, hxb, hxp⟩ := alternate p
    by_cases hqv : q = v
    · exact False.elim (noThree x b p u z v hxb hxp (Ne.symm hpb) (Ne.symm hzu) huv hzv
        hxu hdz (hqv ▸ hpq))
    · exact False.elim (noThree x b p u v q hxb hxp (Ne.symm hpb) huv (Ne.symm hqu) (Ne.symm hqv)
        hxu hbv hpq)

lemma cover_two_of_no_three {α β : Type*} [DecidableEq α] [DecidableEq β]
    (R : α → β → Prop)
    (noThree : ∀ a b c : α, ∀ u v w : β,
      a ≠ b → a ≠ c → b ≠ c → u ≠ v → u ≠ w → v ≠ w →
      R a u → R b v → R c w → False) :
    ∃ P : Finset α, ∃ Q : Finset β, P.card + Q.card ≤ 2 ∧
      ∀ p q, R p q → p ∈ P ∨ q ∈ Q := by
  classical
  by_cases two : ∃ a b : α, ∃ u v : β, a ≠ b ∧ u ≠ v ∧ R a u ∧ R b v
  · obtain ⟨a, b, u, v, hab, huv, hau, hbv⟩ := two
    by_cases rows : ∀ p q, R p q → p = a ∨ p = b
    · refine ⟨{a, b}, ∅, by simp [hab], ?_⟩
      intro p q hpq
      exact Or.inl (by simpa using rows p q hpq)
    · push Not at rows
      obtain ⟨c, w, hcw, hca, hcb⟩ := rows
      have hwu : w = u ∨ w = v := by
        by_contra h
        push Not at h
        exact noThree a b c u v w hab (Ne.symm hca) (Ne.symm hcb) huv (Ne.symm h.1) (Ne.symm h.2)
          hau hbv hcw
      rcases hwu with hwu | hwv
      · exact cover_two_branch R noThree a b c u v hab (Ne.symm hca) (Ne.symm hcb) huv
          hau hbv (hwu ▸ hcw)
      · exact cover_two_branch R noThree b a c v u (Ne.symm hab) (Ne.symm hcb) (Ne.symm hca)
          (Ne.symm huv) hbv hau (hwv ▸ hcw)
  · by_cases edge : ∃ a u, R a u
    · obtain ⟨a, u, hau⟩ := edge
      refine ⟨{a}, {u}, by simp, ?_⟩
      intro p q hpq
      by_cases hpa : p = a
      · exact Or.inl (by simp [hpa])
      by_cases hqu : q = u
      · exact Or.inr (by simp [hqu])
      exact False.elim (two ⟨a, p, u, q, (Ne.symm hpa), (Ne.symm hqu), hau, hpq⟩)
    · refine ⟨∅, ∅, by simp, ?_⟩
      intro p q hpq
      exact False.elim (edge ⟨p, q, hpq⟩)

lemma cover_two_of_no_matching_three {α β : Type*} [DecidableEq α] [DecidableEq β]
    (R : α → β → Prop)
    (noMatching : ¬∃ (P : Fin 3 → α) (Q : Fin 3 → β),
      Function.Injective P ∧ Function.Injective Q ∧ ∀ i, R (P i) (Q i)) :
    ∃ P : Finset α, ∃ Q : Finset β, P.card + Q.card ≤ 2 ∧
      ∀ p q, R p q → p ∈ P ∨ q ∈ Q := by
  apply cover_two_of_no_three R
  intro a b c u v w hab hac hbc huv huw hvw hau hbv hcw
  apply noMatching
  refine ⟨![a, b, c], ![u, v, w], injective_three a b c hab hac hbc,
    injective_three u v w huv huw hvw, ?_⟩
  intro i
  fin_cases i <;> simp_all

end PEqualNP.Outside.L_meta_2602_aux.MatchingCover
