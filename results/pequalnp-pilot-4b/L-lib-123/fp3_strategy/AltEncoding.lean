import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.FP3Strategy

open PEqualNP.Library

lemma take_append_exact (a b : List Bool) (s : ℕ) (ha : a.length = s) :
    (a ++ b).take s = a := by
  rw [← ha]
  exact List.take_left

lemma drop_append_exact (a b : List Bool) (s : ℕ) (ha : a.length = s) :
    (a ++ b).drop s = b := by
  rw [← ha]
  simp

lemma parsed_three_blocks (R : List Bool → List Bool → List Bool → Prop)
    (a b c : List Bool) (s : ℕ) (ha : a.length = s) (hb : b.length = s) :
    R ((a ++ b ++ c).take s) (((a ++ b ++ c).drop s).take s)
      (((a ++ b ++ c).drop s).drop s) ↔ R a b c := by
  simp only [List.append_assoc]
  rw [take_append_exact a (b ++ c) s ha, drop_append_exact a (b ++ c) s ha,
    take_append_exact b c s hb, drop_append_exact b c s hb]

lemma alt_three_block_relation (s : ℕ) (R : List Bool → List Bool → List Bool → Prop) :
    Alt 3 s (fun w => R (w.take s) ((w.drop s).take s) ((w.drop s).drop s)) ↔
      ∃ a : List Bool, a.length = s ∧
        ∀ b : List Bool, b.length = s → ∃ c : List Bool, c.length = s ∧ R a b c := by
  have hnormal (P : List Bool → Prop) : Alt 3 s P ↔
      ∃ a : List Bool, a.length = s ∧
        ∀ b : List Bool, b.length = s →
          ∃ c : List Bool, c.length = s ∧ P (a ++ b ++ c) := by
    simp [Alt, List.append_assoc]
  rw [hnormal]
  constructor
  · rintro ⟨a, ha, h⟩
    refine ⟨a, ha, ?_⟩
    intro b hb
    obtain ⟨c, hc, hr⟩ := h b hb
    exact ⟨c, hc, (parsed_three_blocks R a b c s ha hb).mp hr⟩
  · rintro ⟨a, ha, h⟩
    refine ⟨a, ha, ?_⟩
    intro b hb
    obtain ⟨c, hc, hr⟩ := h b hb
    exact ⟨c, hc, (parsed_three_blocks R a b c s ha hb).mpr hr⟩

def decodedGame {A B C : Type*} (decodeA : List Bool → Option A)
    (decodeB : List Bool → Option B) (decodeC : List Bool → Option C)
    (R : A → B → C → Prop) (a b c : List Bool) : Prop :=
  ∃ x : A, decodeA a = some x ∧
    match decodeB b with
    | none => True
    | some y => ∃ z : C, decodeC c = some z ∧ R x y z

lemma typed_game_to_alt_three {A B C : Type*} (s : ℕ)
    (decodeA : List Bool → Option A) (decodeB : List Bool → Option B)
    (decodeC : List Bool → Option C) (R : A → B → C → Prop)
    (hA : ∀ a : A, ∃ w : List Bool, w.length = s ∧ decodeA w = some a)
    (hB : ∀ b : B, ∃ w : List Bool, w.length = s ∧ decodeB w = some b)
    (hC : ∀ c : C, ∃ w : List Bool, w.length = s ∧ decodeC w = some c) :
    (∃ a : A, ∀ b : B, ∃ c : C, R a b c) ↔
      Alt 3 s (fun w => decodedGame decodeA decodeB decodeC R
        (w.take s) ((w.drop s).take s) ((w.drop s).drop s)) := by
  rw [alt_three_block_relation]
  constructor
  · rintro ⟨a, h⟩
    obtain ⟨wa, hwa, hda⟩ := hA a
    refine ⟨wa, hwa, ?_⟩
    intro wb _
    cases hdb : decodeB wb with
    | none =>
      refine ⟨List.replicate s false, by simp, a, hda, ?_⟩
      simp [hdb]
    | some b =>
      obtain ⟨c, hr⟩ := h b
      obtain ⟨wc, hwc, hdc⟩ := hC c
      refine ⟨wc, hwc, a, hda, ?_⟩
      simpa [hdb] using (show ∃ z : C, decodeC wc = some z ∧ R a b z from ⟨c, hdc, hr⟩)
  · rintro ⟨wa, _, h⟩
    obtain ⟨wc₀, _, a, hda, _⟩ := h (List.replicate s false) (by simp)
    refine ⟨a, ?_⟩
    intro b
    obtain ⟨wb, hwb, hdb⟩ := hB b
    obtain ⟨wc, _, a', hda', hrel⟩ := h wb hwb
    have haa : a' = a := Option.some.inj (hda'.symm.trans hda)
    subst a'
    simp only [hdb] at hrel
    obtain ⟨c, _, hr⟩ := hrel
    exact ⟨c, hr⟩

lemma alt_congr_exact_length (j s : ℕ) (P Q : List Bool → Prop)
    (h : ∀ w : List Bool, w.length = j * s → (P w ↔ Q w)) :
    Alt j s P ↔ Alt j s Q := by
  induction j generalizing P Q with
  | zero => simpa only [Alt] using h [] (by simp)
  | succ j ih =>
    simp only [Alt]
    apply exists_congr
    intro y
    apply and_congr_right
    intro hy
    apply not_congr
    apply ih
    intro w hw
    apply not_congr
    apply h
    simp only [List.length_append, hy, hw, Nat.succ_mul]
    omega

lemma alt_self_sized_parser (s : ℕ) (R : List Bool → List Bool → List Bool → Prop) :
    Alt 3 s (fun w => R (w.take (w.length / 3)) ((w.drop (w.length / 3)).take (w.length / 3))
      ((w.drop (w.length / 3)).drop (w.length / 3))) ↔
    Alt 3 s (fun w => R (w.take s) ((w.drop s).take s) ((w.drop s).drop s)) := by
  apply alt_congr_exact_length
  intro w hw
  have hsize : w.length / 3 = s := by omega
  simp [hsize]

end PEqualNP.Outside.FP3Strategy
