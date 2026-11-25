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

def selectedSupport (n : ℕ) (a b : ℕ → ℕ) (fork chooseLeft : ℕ → Bool)
    (w : ℕ) : Finset (Fin n) :=
  if hw : w < n then {⟨w, hw⟩}
  else if h : a w < w ∧ b w < w then
    if fork w = true then selectedSupport n a b fork chooseLeft (a w) ∪
      selectedSupport n a b fork chooseLeft (b w)
    else if chooseLeft w = true then selectedSupport n a b fork chooseLeft (a w)
      else selectedSupport n a b fork chooseLeft (b w)
  else ∅
termination_by w
decreasing_by all_goals first | exact h.1 | exact h.2

def selectedStep (n total : ℕ) (a b : ℕ → ℕ) (fork chooseLeft : ℕ → Bool)
    (w v : ℕ) : Prop :=
  n ≤ w ∧ w < total ∧
    if fork w = true then v = a w ∨ v = b w
    else if chooseLeft w = true then v = a w else v = b w

def follows (step : ℕ → ℕ → Prop) (root w : ℕ) : Prop :=
  ∀ S : Set ℕ, root ∈ S → (∀ u ∈ S, ∀ v, step u v → v ∈ S) → w ∈ S

lemma follows_refl (step : ℕ → ℕ → Prop) (root : ℕ) : follows step root root := by
  intro S hS _
  exact hS

lemma follows_step (step : ℕ → ℕ → Prop) (root w v : ℕ)
    (hw : follows step root w) (hv : step w v) : follows step root v := by
  intro S hS hclosed
  exact hclosed w (hw S hS hclosed) v hv

noncomputable def selectedActive (n total : ℕ) (a b : ℕ → ℕ)
    (fork chooseLeft : ℕ → Bool) (root : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range total).filter (follows (selectedStep n total a b fork chooseLeft) root)

noncomputable def selectedUnions (n total : ℕ) (a b : ℕ → ℕ)
    (fork chooseLeft : ℕ → Bool) (root : ℕ) : Finset ℕ := by
  classical
  exact (selectedActive n total a b fork chooseLeft root).filter
    (fun w => n ≤ w ∧ fork w = true)

lemma selectedSupport_input (n : ℕ) (a b : ℕ → ℕ) (fork chooseLeft : ℕ → Bool)
    (w : ℕ) (hw : w < n) : selectedSupport n a b fork chooseLeft w = {⟨w, hw⟩} := by
  rw [selectedSupport, dite_eq_left hw]

lemma selectedSupport_gate (n : ℕ) (a b : ℕ → ℕ) (fork chooseLeft : ℕ → Bool)
    (w : ℕ) (hw : n ≤ w) (hp : a w < w ∧ b w < w) :
    selectedSupport n a b fork chooseLeft w =
      if fork w = true then selectedSupport n a b fork chooseLeft (a w) ∪
        selectedSupport n a b fork chooseLeft (b w)
      else if chooseLeft w = true then selectedSupport n a b fork chooseLeft (a w)
        else selectedSupport n a b fork chooseLeft (b w) := by
  rw [selectedSupport, dite_eq_right (Nat.not_lt.mpr hw), dite_eq_left hp]

lemma selected_cover
    {A B : Type*} (n total root : ℕ) (left : A → Fin n) (right : B → Fin n)
    (edges : Finset (A × B)) (a b : ℕ → ℕ) (fork chooseLeft : ℕ → Bool)
    (hit : ℕ → A → B → Prop)
    (hroot : root < total)
    (hparents : ∀ w, n ≤ w → w < total → a w < w ∧ b w < w)
    (hinput : ∀ w (hw : w < n), ∀ u v, hit w u v → left u = ⟨w, hw⟩ ∨ right v = ⟨w, hw⟩)
    (hfork : ∀ w, n ≤ w → w < total → fork w = true →
      ∀ u v, hit w u v → hit (a w) u v ∨ hit (b w) u v)
    (hchoose : ∀ w, n ≤ w → w < total → fork w ≠ true →
      ∀ u v, hit w u v → hit (a w) u v ∧ hit (b w) u v)
    (haccepted : ∀ u v, (u, v) ∈ edges → hit root u v) :
    (∀ u v, (u, v) ∈ edges →
      left u ∈ selectedSupport n a b fork chooseLeft root ∨
      right v ∈ selectedSupport n a b fork chooseLeft root) ∧
    (selectedSupport n a b fork chooseLeft root).card ≤
      1 + (selectedUnions n total a b fork chooseLeft root).card := by
  classical
  let active := selectedActive n total a b fork chooseLeft root
  let paid := selectedUnions n total a b fork chooseLeft root
  let supp := selectedSupport n a b fork chooseLeft
  let support : ℕ → Finset (Fin n) := fun w => if w ∈ active then supp w else ∅
  let hits : ℕ → A → B → Prop := fun w u v => w ∈ active ∧ hit w u v
  have root_mem : root ∈ active := by
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hroot, follows_refl _ _⟩
  have mem_next (w v : ℕ) (hw : w ∈ active)
      (hv : selectedStep n total a b fork chooseLeft w v) (hvw : v < w) : v ∈ active := by
    have hs := Finset.mem_filter.mp hw
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (hvw.trans (Finset.mem_range.mp hs.1)),
      follows_step _ root w v hs.2 hv⟩
  have hpaid : Finset.range total ∩ paid = paid := by
    apply Finset.inter_eq_right.mpr
    intro w hw
    exact (Finset.mem_filter.mp (Finset.mem_filter.mp hw).1).1
  have result := selected_dag_cover left right edges n total root support hits paid hroot
    (fun u v huv => ⟨root_mem, haccepted u v huv⟩) ?_ ?_
  · simpa only [support, root_mem, ite_eq_left, hpaid] using result
  · intro w hw
    constructor
    · dsimp only [support, supp]
      split_ifs
      · rw [selectedSupport_input n a b fork chooseLeft w hw]
        simp
      · simp
    · intro u v ⟨hactive, hhit⟩
      dsimp only [support]
      rw [ite_eq_left hactive]
      change left u ∈ selectedSupport n a b fork chooseLeft w ∨
        right v ∈ selectedSupport n a b fork chooseLeft w
      rw [selectedSupport_input n a b fork chooseLeft w hw]
      simpa using hinput w hw u v hhit
  · intro w hn hw
    by_cases hactive : w ∈ active
    · have hp := hparents w hn hw
      have hs : supp w = if fork w = true then supp (a w) ∪ supp (b w)
          else if chooseLeft w = true then supp (a w) else supp (b w) :=
        selectedSupport_gate n a b fork chooseLeft w hn hp
      by_cases hor : fork w = true
      · have ha : a w ∈ active := mem_next w (a w) hactive
          ⟨hn, hw, by simp only [hor, ite_eq_left, true_or]⟩ hp.1
        have hb : b w ∈ active := mem_next w (b w) hactive
          ⟨hn, hw, by simp only [hor, ite_eq_left, or_true]⟩ hp.2
        right
        left
        refine ⟨Finset.mem_filter.mpr ⟨hactive, hn, hor⟩, a w, hp.1, b w, hp.2, ?_, ?_⟩
        · simp only [support, hactive, ha, hb, ite_eq_left, hor] at hs ⊢
          exact hs
        · intro u v ⟨_, hv⟩
          rcases hfork w hn hw hor u v hv with h | h
          · exact Or.inl ⟨ha, h⟩
          · exact Or.inr ⟨hb, h⟩
      · left
        by_cases hl : chooseLeft w = true
        · have ha : a w ∈ active := mem_next w (a w) hactive
            ⟨hn, hw, by simp [hor, hl]⟩ hp.1
          refine ⟨a w, hp.1, ?_, ?_⟩
          · simp only [support, hactive, ha, ite_eq_left, hor, ite_eq_right, hl] at hs ⊢
            exact hs
          · intro u v ⟨_, hv⟩
            exact ⟨ha, (hchoose w hn hw hor u v hv).1⟩
        · have hb : b w ∈ active := mem_next w (b w) hactive
            ⟨hn, hw, by simp [hor, hl]⟩ hp.2
          refine ⟨b w, hp.2, ?_, ?_⟩
          · simp only [support, hactive, hb, ite_eq_left, hor, ite_eq_right, hl] at hs ⊢
            exact hs
          · intro u v ⟨_, hv⟩
            exact ⟨hb, (hchoose w hn hw hor u v hv).2⟩
    · right
      right
      refine ⟨by simp [support, hactive], ?_⟩
      intro u v hv
      exact hactive hv.1



lemma selectedSupport_zero (n total : ℕ) (a b : ℕ → ℕ)
    (fork chooseLeft : ℕ → Bool) (value : ℕ → Bool)
    (hparents : ∀ w, n ≤ w → w < total → a w < w ∧ b w < w)
    (hfork : ∀ w, n ≤ w → w < total → fork w = true → value w = false →
      value (a w) = false ∧ value (b w) = false)
    (hchoose : ∀ w, n ≤ w → w < total → fork w ≠ true → value w = false →
      (if chooseLeft w = true then value (a w) else value (b w)) = false) :
    ∀ w, w < total → value w = false →
      ∀ i ∈ selectedSupport n a b fork chooseLeft w, value i.val = false := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw hv i hi
    by_cases hin : w < n
    · rw [selectedSupport_input n a b fork chooseLeft w hin] at hi
      have hi1 : i = ⟨w, hin⟩ := by simpa using hi
      subst i
      exact hv
    · have hn : n ≤ w := Nat.le_of_not_lt hin
      have hp := hparents w hn hw
      rw [selectedSupport_gate n a b fork chooseLeft w hn hp] at hi
      by_cases hor : fork w = true
      · simp only [hor, ite_eq_left, Finset.mem_union] at hi
        rcases hi with hi | hi
        · exact ih _ hp.1 (hp.1.trans hw) (hfork w hn hw hor hv).1 i hi
        · exact ih _ hp.2 (hp.2.trans hw) (hfork w hn hw hor hv).2 i hi
      · have hc := hchoose w hn hw hor hv
        by_cases hl : chooseLeft w = true
        · simp [hor, hl] at hi hc
          exact ih _ hp.1 (hp.1.trans hw) hc i hi
        · simp [hor, hl] at hi hc
          exact ih _ hp.2 (hp.2.trans hw) hc i hi

lemma selectedActive_zero (n total root : ℕ) (a b : ℕ → ℕ)
    (fork chooseLeft : ℕ → Bool) (value : ℕ → Bool)
    (hzero : value root = false)
    (hfork : ∀ w, n ≤ w → w < total → fork w = true → value w = false →
      value (a w) = false ∧ value (b w) = false)
    (hchoose : ∀ w, n ≤ w → w < total → fork w ≠ true → value w = false →
      (if chooseLeft w = true then value (a w) else value (b w)) = false) :
    ∀ w ∈ selectedActive n total a b fork chooseLeft root, value w = false := by
  classical
  intro w hw
  have hr := (Finset.mem_filter.mp hw).2
  apply hr {v | value v = false} hzero
  intro u hu v ⟨hn, ht, hv⟩
  change value v = false
  by_cases hor : fork u = true
  · simp only [hor, ite_eq_left] at hv
    rcases hv with rfl | rfl
    · exact (hfork u hn ht hor hu).1
    · exact (hfork u hn ht hor hu).2
  · have hc := hchoose u hn ht hor hu
    by_cases hl : chooseLeft u = true
    · simp [hor, hl] at hv hc
      rw [hv]
      exact hc
    · simp [hor, hl] at hv hc
      rw [hv]
      exact hc

end PEqualNP.Outside.L_meta_4970.Pruning
