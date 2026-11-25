import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace PEqualNP.Outside.L_meta_4970.Pruning

lemma pruning_countUnion {α : Type*} [DecidableEq α] (support : ℕ → Finset α)
    (paid : Finset ℕ) (m : ℕ)
    (step : ∀ w < m, 1 < (support w).card → ∃ cs : Finset ℕ,
      cs ⊆ Finset.range w ∧ support w ⊆ cs.biUnion support ∧
      cs.card ≤ 1 + (if w ∈ paid then 1 else 0))
    (roots : Finset ℕ) (hr : roots ⊆ Finset.range m) :
    (roots.biUnion support).card ≤ roots.card + ((Finset.range m) ∩ paid).card := by
  classical
  induction m generalizing roots with
  | zero =>
    have : roots = ∅ := by simpa using hr
    simp [this]
  | succ m ih =>
    have old := ih (fun w hw => step w (by omega))
    have hpre : roots.erase m ⊆ Finset.range m := by
      intro w hw
      have ⟨hne, hmem⟩ := Finset.mem_erase.mp hw
      have hlt := Finset.mem_range.mp (hr hmem)
      exact Finset.mem_range.mpr (by omega)
    have hcost : ((Finset.range (m + 1)) ∩ paid).card =
        ((Finset.range m) ∩ paid).card + (if m ∈ paid then 1 else 0) := by
      by_cases h : m ∈ paid
      · have he : Finset.range (m + 1) ∩ paid = insert m (Finset.range m ∩ paid) := by
          ext w
          by_cases hw : w = m <;> simp [Finset.range_add_one, hw, h]
        simp [he, h]
      · have he : Finset.range (m + 1) ∩ paid = Finset.range m ∩ paid := by
          ext w
          by_cases hw : w = m <;> simp [Finset.range_add_one, hw, h]
        simp [he, h]
    rw [hcost]
    by_cases hm : m ∈ roots
    · have hrins := Finset.insert_erase hm
      have hroots : (roots.erase m).card + 1 = roots.card :=
        Finset.card_erase_add_one hm
      by_cases hb : 1 < (support m).card
      · obtain ⟨cs, hcpre, hcov, hcard⟩ := step m (by omega) hb
        have hsub : roots.biUnion support ⊆ ((roots.erase m) ∪ cs).biUnion support := by
          intro a ha
          obtain ⟨w, hw, haw⟩ := Finset.mem_biUnion.mp ha
          by_cases heq : w = m
          · subst w
            obtain ⟨v, hv, hav⟩ := Finset.mem_biUnion.mp (hcov haw)
            exact Finset.mem_biUnion.mpr ⟨v, Finset.mem_union_right _ hv, hav⟩
          · exact Finset.mem_biUnion.mpr
              ⟨w, Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨heq, hw⟩), haw⟩
        have hh := old ((roots.erase m) ∪ cs) (Finset.union_subset hpre hcpre)
        have hh' := Finset.card_le_card hsub
        have hu := Finset.card_union_le (roots.erase m) cs
        omega
      · have hh := old (roots.erase m) hpre
        have he : roots.biUnion support = support m ∪ (roots.erase m).biUnion support := by
          conv_lhs => rw [← hrins]
          rw [Finset.biUnion_insert]
        rw [he]
        have hu := Finset.card_union_le (support m) ((roots.erase m).biUnion support)
        omega
    · rw [Finset.erase_eq_of_notMem hm] at hpre
      have hh := old roots hpre
      omega

lemma selected_dag_cover
    {A B V : Type*} [DecidableEq V]
    (left : A → V) (right : B → V) (edges : Finset (A × B))
    (base total root : ℕ) (support : ℕ → Finset V)
    (hit : ℕ → A → B → Prop) (paid : Finset ℕ)
    (hroot : root < total)
    (haccepted : ∀ a b, (a, b) ∈ edges → hit root a b)
    (hbase : ∀ w < base, (support w).card ≤ 1 ∧
      ∀ a b, hit w a b → left a ∈ support w ∨ right b ∈ support w)
    (hstep : ∀ w, base ≤ w → w < total →
      (∃ j < w, support w = support j ∧ ∀ a b, hit w a b → hit j a b) ∨
      (w ∈ paid ∧ ∃ i < w, ∃ j < w, support w = support i ∪ support j ∧
        ∀ a b, hit w a b → hit i a b ∨ hit j a b) ∨
      (support w = ∅ ∧ ∀ a b, ¬ hit w a b)) :
    (∀ a b, (a, b) ∈ edges → left a ∈ support root ∨ right b ∈ support root) ∧
      (support root).card ≤ 1 + (Finset.range total ∩ paid).card := by
  classical
  have covers : ∀ w < total, ∀ a b, hit w a b →
      left a ∈ support w ∨ right b ∈ support w := by
    intro w
    induction w using Nat.strong_induction_on with
    | ind w ih =>
      intro hw a b hab
      by_cases hlow : w < base
      · exact (hbase w hlow).2 a b hab
      · rcases hstep w (Nat.le_of_not_gt hlow) hw with
          ⟨j, hj, he, hh⟩ | ⟨hp, i, hi, j, hj, he, hh⟩ | ⟨he, hh⟩
        · rw [he]
          exact ih j hj (hj.trans hw) a b (hh a b hab)
        · rw [he]
          rcases hh a b hab with ha | hb
          · rcases ih i hi (hi.trans hw) a b ha with ha | hb
            · exact Or.inl (Finset.mem_union_left _ ha)
            · exact Or.inr (Finset.mem_union_left _ hb)
          · rcases ih j hj (hj.trans hw) a b hb with ha | hb
            · exact Or.inl (Finset.mem_union_right _ ha)
            · exact Or.inr (Finset.mem_union_right _ hb)
        · exact False.elim (hh a b hab)
  refine ⟨fun a b hab => covers root hroot a b (haccepted a b hab), ?_⟩
  have hc := pruning_countUnion support paid total ?_ {root} ?_
  · simpa using hc
  · intro w hw hcard
    by_cases hlow : w < base
    · exact False.elim ((Nat.not_lt_of_ge (hbase w hlow).1) hcard)
    · rcases hstep w (Nat.le_of_not_gt hlow) hw with
        ⟨j, hj, he, hh⟩ | ⟨hp, i, hi, j, hj, he, hh⟩ | ⟨he, hh⟩
      · refine ⟨{j}, ?_, ?_, ?_⟩
        · simpa using hj
        · simp [he]
        · simp
      · refine ⟨{i, j}, ?_, ?_, ?_⟩
        · intro k hk
          rcases Finset.mem_insert.mp hk with rfl | hk
          · exact Finset.mem_range.mpr hi
          · rw [Finset.mem_singleton.mp hk]
            exact Finset.mem_range.mpr hj
        · simp [he]
        · simp only [hp, ite_true]
          exact Finset.card_le_two
      · simp [he] at hcard
  · simpa using hroot

end PEqualNP.Outside.L_meta_4970.Pruning

