import PEqualNP.Defs
import Mathlib.Tactic

namespace PEqualNP.Outside.L_meta_2583.ThreeLines

open PEqualNP.ReadK

lemma avoid_two_points {N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I]
    (hu : ∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l)
    (L : Finset (Fin N)) (hL : 3 ≤ L.card) (p a b : Fin N)
    (hpL : ∀ l ∈ L, I p l) (hap : a ≠ p) (hbp : b ≠ p) :
    ∃ l ∈ L, ¬ I a l ∧ ¬ I b l := by
  have hone (a : Fin N) (hap : a ≠ p) : (L.filter (I a)).card ≤ 1 := by
    rw [Finset.card_le_one]
    intro l hl m hm
    obtain ⟨hlL, hal⟩ := Finset.mem_filter.mp hl
    obtain ⟨hmL, ham⟩ := Finset.mem_filter.mp hm
    exact (hu a p hap).unique ⟨hal, hpL l hlL⟩ ⟨ham, hpL m hmL⟩
  by_contra h
  have hsub : L ⊆ L.filter (I a) ∪ L.filter (I b) := by
    intro l hl
    by_cases ha : I a l
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hl, ha⟩)
    · have hb : I b l := by
        by_contra hb
        exact h ⟨l, hl, ha, hb⟩
      exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hl, hb⟩)
  have hcard := Finset.card_le_card hsub
  have hbound := Finset.card_union_le (L.filter (I a)) (L.filter (I b))
  have ha := hone a hap
  have hb := hone b hbp
  omega

lemma accepts_superset {n : ℕ} (A : (Fin n → Bool) → Bool) (hA : Monotone A)
    (S T : Finset (Fin n)) (hst : S ⊆ T) (hs : A (setInput S) = true) :
    A (setInput T) = true := by
  have hle : setInput S ≤ setInput T := by
    intro i
    by_cases hi : i ∈ S
    · simp [setInput, hi, hst hi]
    · simp [setInput, hi]
  have h := hA hle
  by_contra hn
  have hf : A (setInput T) = false := by simpa using hn
  rw [hs, hf] at h
  exact (show ¬ ((true : Bool) ≤ false) by decide) h

lemma singleton_point_orientation {N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I]
    (hu : ∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l)
    (A B T : (Fin (N + N) → Bool) → Bool)
    (hA : Monotone A) (hB : Monotone B) (hT : Monotone T)
    (hbelow : ∀ z : Fin (N + N) → Bool, A z = true → B z = true → T z = true →
      ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true)
    (p : Fin N) (L : Finset (Fin N)) (hL : 3 ≤ L.card)
    (hpL : ∀ l ∈ L, I p l)
    (hTL : ∀ l ∈ L, T (setInput {Fin.natAdd N l}) = true) :
    (∀ a : Fin N, A (setInput {Fin.castAdd N a}) = true → a = p) ∨
      (∀ b : Fin N, B (setInput {Fin.castAdd N b}) = true → b = p) := by
  by_cases hleft : ∀ a : Fin N, A (setInput {Fin.castAdd N a}) = true → a = p
  · exact Or.inl hleft
  · push Not at hleft
    obtain ⟨a, ha, hap⟩ := hleft
    refine Or.inr ?_
    intro b hb
    by_contra hbp
    obtain ⟨l, hl, hal, hbl⟩ := avoid_two_points I hu L hL p a b hpL hap hbp
    let S : Finset (Fin (N + N)) := {Fin.castAdd N a, Fin.castAdd N b, Fin.natAdd N l}
    have hAS : A (setInput S) = true :=
      accepts_superset A hA _ S (by simp [S]) ha
    have hBS : B (setInput S) = true :=
      accepts_superset B hB _ S (by simp [S]) hb
    have hTS : T (setInput S) = true :=
      accepts_superset T hT _ S (by simp [S]) (hTL l hl)
    obtain ⟨c, m, hcm, hc, hm⟩ := hbelow (setInput S) hAS hBS hTS
    simp only [setInput, decide_eq_true_eq, S, Finset.mem_insert, Finset.mem_singleton] at hc hm
    have hmL : m = l := by
      rcases hm with h | h | h
      · have hv := congrArg Fin.val h
        change N + m.val = a.val at hv
        omega
      · have hv := congrArg Fin.val h
        change N + m.val = b.val at hv
        omega
      · exact Fin.ext (Nat.add_left_cancel (congrArg Fin.val h))
    subst m
    rcases hc with h | h | h
    · have hv := congrArg Fin.val h
      have hca : c = a := Fin.ext hv
      exact hal (hca ▸ hcm)
    · have hv := congrArg Fin.val h
      have hcb : c = b := Fin.ext hv
      exact hbl (hcb ▸ hcm)
    · have hv := congrArg Fin.val h
      change c.val = N + l.val at hv
      omega

end PEqualNP.Outside.L_meta_2583.ThreeLines
