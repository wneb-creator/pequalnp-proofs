import Mathlib.Data.Finset.Card
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Pi

namespace PEqualNP.Outside.L_meta_4970

lemma star_centre_unique {p l : ℕ} (E : Finset (Fin p × Fin l))
    (hE : ∀ (a a' : Fin p) (b b' : Fin l), a ≠ a' → b ≠ b' →
      ¬ ((a, b) ∈ E ∧ (a, b') ∈ E ∧ (a', b) ∈ E ∧ (a', b') ∈ E))
    {a a' : Fin p} {Q : Finset (Fin l)} (hQ : 2 ≤ Q.card)
    (ha : ∀ b ∈ Q, (a, b) ∈ E) (ha' : ∀ b ∈ Q, (a', b) ∈ E) : a = a' := by
  by_cases h : a = a'
  · exact h
  · obtain ⟨b, hb, b', hb', hbb'⟩ := Finset.one_lt_card.mp
      (lt_of_lt_of_le (by decide : 1 < 2) hQ)
    exact False.elim (hE a a' b b' h hbb' ⟨ha b hb, ha b' hb', ha' b hb, ha' b' hb'⟩)

lemma distinct_centres_intersection_card {p l : ℕ} (E : Finset (Fin p × Fin l))
    (hE : ∀ (a a' : Fin p) (b b' : Fin l), a ≠ a' → b ≠ b' →
      ¬ ((a, b) ∈ E ∧ (a, b') ∈ E ∧ (a', b) ∈ E ∧ (a', b') ∈ E))
    {a a' : Fin p} {Q Q' : Finset (Fin l)} (haa' : a ≠ a')
    (ha : ∀ b ∈ Q, (a, b) ∈ E) (ha' : ∀ b ∈ Q', (a', b) ∈ E) :
    (Q ∩ Q').card ≤ 1 := by
  by_cases h : (Q ∩ Q').card ≤ 1
  · exact h
  · have hQ : 2 ≤ (Q ∩ Q').card := Nat.lt_of_not_ge h
    exact False.elim (haa' (star_centre_unique E hE hQ
      (fun b hb => ha b (Finset.mem_inter.mp hb).1)
      (fun b hb => ha' b (Finset.mem_inter.mp hb).2)))

lemma or_function_determines_leaves {α : Type*} [DecidableEq α]
    (Q R : Finset α)
    (h : ∀ x : α → Bool, decide (∃ b ∈ Q, x b = true) =
      decide (∃ b ∈ R, x b = true)) : Q = R := by
  ext b
  have hb := h (fun a => decide (a = b))
  simpa using hb

lemma line_or_function_determines_leaves {p l : ℕ} (Q R : Finset (Fin l))
    (h : ∀ x : Fin (p + l) → Bool,
      decide (∃ b ∈ Q, x (Fin.natAdd p b) = true) =
        decide (∃ b ∈ R, x (Fin.natAdd p b) = true)) : Q = R := by
  apply or_function_determines_leaves
  intro x
  simpa using h (Fin.addCases (fun _ => false) x)

lemma point_or_function_determines_leaves {p l : ℕ} (P R : Finset (Fin p))
    (h : ∀ x : Fin (p + l) → Bool,
      decide (∃ a ∈ P, x (Fin.castAdd l a) = true) =
        decide (∃ a ∈ R, x (Fin.castAdd l a) = true)) : P = R := by
  apply or_function_determines_leaves
  intro x
  simpa using h (Fin.addCases x (fun _ => false))

lemma point_or_ne_line_or {p l : ℕ} (P : Finset (Fin p)) (Q : Finset (Fin l))
    (hP : P.Nonempty) :
    ¬ (∀ x : Fin (p + l) → Bool,
      decide (∃ a ∈ P, x (Fin.castAdd l a) = true) =
        decide (∃ b ∈ Q, x (Fin.natAdd p b) = true)) := by
  intro h
  have heq := h (Fin.addCases (fun _ => true) (fun _ => false))
  have hnot : ∀ a, a ∉ P := by simpa using heq
  obtain ⟨a, ha⟩ := hP
  exact hnot a ha

lemma star_family_cover_card {p l : ℕ} {ι : Type*} [DecidableEq ι]
    (E : Finset (Fin p × Fin l)) (I : Finset ι)
    (B : ι → Finset (Fin p × Fin l)) (c : ι → Fin (p + l))
    (hcover : ∀ e ∈ E, ∃ i ∈ I, e ∈ B i)
    (hstar : ∀ i ∈ I, ∀ e ∈ B i, Fin.castAdd l e.1 = c i ∨ Fin.natAdd p e.2 = c i) :
    ∃ S : Finset (Fin (p + l)),
      (∀ (a : Fin p) (b : Fin l), (a, b) ∈ E →
        Fin.castAdd l a ∈ S ∨ Fin.natAdd p b ∈ S) ∧
      S.card ≤ I.card ∧ E.card ≤ ∑ i ∈ I, (B i).card := by
  refine ⟨I.image c, ?_, Finset.card_image_le, ?_⟩
  · intro a b hab
    obtain ⟨i, hi, hib⟩ := hcover (a, b) hab
    have hci : c i ∈ I.image c := Finset.mem_image_of_mem c hi
    rcases hstar i hi (a, b) hib with h | h
    · exact Or.inl (h ▸ hci)
    · exact Or.inr (h ▸ hci)
  · have hsub : E ⊆ I.biUnion B := by
      intro e he
      obtain ⟨i, hi, hib⟩ := hcover e he
      exact Finset.mem_biUnion.mpr ⟨i, hi, hib⟩
    exact (Finset.card_le_card hsub).trans Finset.card_biUnion_le

lemma star_family_ledger {p l s : ℕ} {ι : Type*} [DecidableEq ι]
    (E : Finset (Fin p × Fin l)) (I : Finset ι)
    (B : ι → Finset (Fin p × Fin l)) (c : ι → Fin (p + l))
    (hcover : ∀ e ∈ E, ∃ i ∈ I, e ∈ B i)
    (hstar : ∀ i ∈ I, ∀ e ∈ B i, Fin.castAdd l e.1 = c i ∨ Fin.natAdd p e.2 = c i)
    (hsize : (∑ i ∈ I, (B i).card) + I.card ≤ s + 1) :
    ∃ S : Finset (Fin (p + l)),
      (∀ (a : Fin p) (b : Fin l), (a, b) ∈ E →
        Fin.castAdd l a ∈ S ∨ Fin.natAdd p b ∈ S) ∧ E.card + S.card ≤ s + 1 := by
  obtain ⟨S, hS, hScard, hEcard⟩ := star_family_cover_card E I B c hcover hstar
  exact ⟨S, hS, (Nat.add_le_add hEcard hScard).trans hsize⟩

lemma star_line_centre_unique {p l : ℕ} (E : Finset (Fin p × Fin l))
    (hE : ∀ (a a' : Fin p) (b b' : Fin l), a ≠ a' → b ≠ b' →
      ¬ ((a, b) ∈ E ∧ (a, b') ∈ E ∧ (a', b) ∈ E ∧ (a', b') ∈ E))
    {b b' : Fin l} {P : Finset (Fin p)} (hP : 2 ≤ P.card)
    (hb : ∀ a ∈ P, (a, b) ∈ E) (hb' : ∀ a ∈ P, (a, b') ∈ E) : b = b' := by
  by_cases h : b = b'
  · exact h
  · obtain ⟨a, ha, a', ha', haa'⟩ := Finset.one_lt_card.mp
      (lt_of_lt_of_le (by decide : 1 < 2) hP)
    exact False.elim (hE a a' b b' haa' h ⟨hb a ha, hb' a ha, hb a' ha', hb' a' ha'⟩)

lemma point_centre_unique_of_same_function {p l : ℕ} (E : Finset (Fin p × Fin l))
    (hE : ∀ (a a' : Fin p) (b b' : Fin l), a ≠ a' → b ≠ b' →
      ¬ ((a, b) ∈ E ∧ (a, b') ∈ E ∧ (a', b) ∈ E ∧ (a', b') ∈ E))
    {a a' : Fin p} {Q Q' : Finset (Fin l)} (hQ : 2 ≤ Q.card)
    (ha : ∀ b ∈ Q, (a, b) ∈ E) (ha' : ∀ b ∈ Q', (a', b) ∈ E)
    (f : (Fin (p + l) → Bool) → Bool)
    (hf : ∀ x, f x = decide (∃ b ∈ Q, x (Fin.natAdd p b) = true))
    (hf' : ∀ x, f x = decide (∃ b ∈ Q', x (Fin.natAdd p b) = true)) : a = a' := by
  have heq : Q = Q' := line_or_function_determines_leaves Q Q'
    (fun x => (hf x).symm.trans (hf' x))
  apply star_centre_unique E hE hQ ha
  intro b hb
  exact ha' b (heq ▸ hb)

lemma line_centre_unique_of_same_function {p l : ℕ} (E : Finset (Fin p × Fin l))
    (hE : ∀ (a a' : Fin p) (b b' : Fin l), a ≠ a' → b ≠ b' →
      ¬ ((a, b) ∈ E ∧ (a, b') ∈ E ∧ (a', b) ∈ E ∧ (a', b') ∈ E))
    {b b' : Fin l} {P P' : Finset (Fin p)} (hP : 2 ≤ P.card)
    (hb : ∀ a ∈ P, (a, b) ∈ E) (hb' : ∀ a ∈ P', (a, b') ∈ E)
    (f : (Fin (p + l) → Bool) → Bool)
    (hf : ∀ x, f x = decide (∃ a ∈ P, x (Fin.castAdd l a) = true))
    (hf' : ∀ x, f x = decide (∃ a ∈ P', x (Fin.castAdd l a) = true)) : b = b' := by
  have heq : P = P' := point_or_function_determines_leaves P P'
    (fun x => (hf x).symm.trans (hf' x))
  apply star_line_centre_unique E hE hP hb
  intro a ha
  exact hb' a (heq ▸ ha)

lemma reverse_star_centre_unique {p l : ℕ} {E : Finset (Fin p × Fin l)}
    (hfour : ∀ (a a' : Fin p) (b b' : Fin l), a ≠ a' → b ≠ b' →
      ¬ ((a, b) ∈ E ∧ (a, b') ∈ E ∧ (a', b) ∈ E ∧ (a', b') ∈ E))
    {b b' : Fin l} {P : Finset (Fin p)} (hP : 2 ≤ P.card)
    (hb : ∀ a ∈ P, (a, b) ∈ E) (hb' : ∀ a ∈ P, (a, b') ∈ E) : b = b' := by
  by_contra hne
  obtain ⟨a, ha, a', ha', haa'⟩ := Finset.one_lt_card.mp
    (lt_of_lt_of_le (by decide : 1 < 2) hP)
  exact hfour a a' b b' haa' hne ⟨hb a ha, hb' a ha, hb a' ha', hb' a' ha'⟩

end PEqualNP.Outside.L_meta_4970

namespace PEqualNP.Outside.L_meta_4970_aux.Structural

def IsIncreasing {α : Type*} (f : (α → Bool) → Bool) : Prop :=
  ∀ x y, (∀ i, x i = true → y i = true) → f x = true → f y = true

lemma below_or_of_complement {α : Type*} [DecidableEq α]
    (Q : Finset α) (f : (α → Bool) → Bool)
    (hf : IsIncreasing f)
    (hzero : f (fun i => decide (i ∉ Q)) ≠ true) :
    ∀ x, f x = true → ∃ i ∈ Q, x i = true := by
  intro x hx
  by_contra hn
  apply hzero
  apply hf x (fun i => decide (i ∉ Q)) _ hx
  intro i hi
  simp only [decide_eq_true_eq]
  intro hiQ
  exact hn ⟨i, hiQ, hi⟩

lemma and_below_or_child {α : Type*} [DecidableEq α]
    (Q : Finset α) (f g : (α → Bool) → Bool)
    (hf : IsIncreasing f) (hg : IsIncreasing g)
    (hbound : ∀ x, (f x && g x) = true → ∃ i ∈ Q, x i = true) :
    (∀ x, f x = true → ∃ i ∈ Q, x i = true) ∨
      (∀ x, g x = true → ∃ i ∈ Q, x i = true) := by
  let z : α → Bool := fun i => decide (i ∉ Q)
  have hz : ¬ (f z = true ∧ g z = true) := by
    intro h
    obtain ⟨i, hiQ, hiz⟩ := hbound z (by simp [h.1, h.2])
    simp [z, hiQ] at hiz
  by_cases h : f z = true
  · exact Or.inr (below_or_of_complement Q g hg (fun h' => hz ⟨h, h'⟩))
  · exact Or.inl (below_or_of_complement Q f hf h)

lemma and_eq_or_child {α : Type*} [DecidableEq α]
    (Q : Finset α) (f g : (α → Bool) → Bool)
    (hf : IsIncreasing f) (hg : IsIncreasing g)
    (heq : ∀ x, (f x && g x) = decide (∃ i ∈ Q, x i = true)) :
    (∀ x, f x = decide (∃ i ∈ Q, x i = true)) ∨
      (∀ x, g x = decide (∃ i ∈ Q, x i = true)) := by
  have hb : ∀ x, (f x && g x) = true → ∃ i ∈ Q, x i = true := by
    intro x hx
    rw [heq x] at hx
    exact of_decide_eq_true hx
  rcases and_below_or_child Q f g hf hg hb with h | h
  · left
    intro x
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq]
    constructor
    · exact h x
    · intro hx
      have hx' : (f x && g x) = true := by
        rw [heq x]
        exact decide_eq_true hx
      rw [Bool.and_eq_true] at hx'
      exact hx'.1
  · right
    intro x
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq]
    constructor
    · exact h x
    · intro hx
      have hx' : (f x && g x) = true := by
        rw [heq x]
        exact decide_eq_true hx
      rw [Bool.and_eq_true] at hx'
      exact hx'.2

lemma countUnion {α : Type*} [DecidableEq α] (support : ℕ → Finset α)
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

lemma pure_or_rt_count {α : Type*} [DecidableEq α] [Fintype α]
    (k N : ℕ) (Q : Finset α)
    (W : ℕ → (α → Bool) → Bool) (S : ℕ → Finset α)
    (a b : ℕ → ℕ) (isAnd : ℕ → Bool)
    (hmono : ∀ w < N, IsIncreasing (W w))
    (hsmall : ∀ w < k, (S w).card ≤ 1)
    (hparents : ∀ w, k ≤ w → w < N → a w < w ∧ b w < w)
    (hsupport : ∀ w < N, ∀ i,
      i ∈ S w ↔ W w (fun j => decide (j = i)) = true)
    (heval : ∀ w, k ≤ w → w < N → ∀ x,
      W w x = if isAnd w then (W (a w) x && W (b w) x)
        else (W (a w) x || W (b w) x))
    (R : Finset ℕ)
    (hR : ∀ w ∈ R, w < N ∧ (∀ x, W w x = true → ∃ i ∈ Q, x i = true)) :
    (R.biUnion S).card ≤ R.card +
      ((Finset.range N).filter (fun w => k ≤ w ∧ isAnd w = false ∧
        1 < (S w).card ∧ ∀ x, W w x = true → ∃ i ∈ Q, x i = true)).card := by
  classical
  let below (w : ℕ) := ∀ x, W w x = true → ∃ i ∈ Q, x i = true
  let F (w : ℕ) := if w < N ∧ below w then S w else ∅
  let paid := (Finset.range N).filter fun w =>
    k ≤ w ∧ isAnd w = false ∧ 1 < (S w).card ∧ below w
  have hstep : ∀ w < N, 1 < (F w).card → ∃ cs : Finset ℕ,
      cs ⊆ Finset.range w ∧ F w ⊆ cs.biUnion F ∧
        cs.card ≤ 1 + (if w ∈ paid then 1 else 0) := by
    intro w hw hlarge
    have hgood : w < N ∧ below w := by
      by_contra hn
      simp [F, hn] at hlarge
    have hF : F w = S w := ite_eq_left hgood
    have hk : k ≤ w := by
      by_contra hn
      have ht := hsmall w (by omega)
      rw [hF] at hlarge
      omega
    have ⟨ha, hb⟩ := hparents w hk hw
    cases hop : isAnd w with
    | true =>
      have hbound : ∀ x, (W (a w) x && W (b w) x) = true → ∃ i ∈ Q, x i = true := by
        intro x hx
        apply hgood.2 x
        simpa [heval w hk hw x, hop] using hx
      have hchoice := and_below_or_child Q (W (a w)) (W (b w))
        (hmono _ (ha.trans hw)) (hmono _ (hb.trans hw)) hbound
      have hsubA : S w ⊆ S (a w) := by
        intro i hi
        apply (hsupport _ (ha.trans hw) i).mpr
        have ht := (hsupport w hw i).mp hi
        rw [heval w hk hw, hop] at ht
        simp only [ite_true, Bool.and_eq_true] at ht
        exact ht.1
      have hsubB : S w ⊆ S (b w) := by
        intro i hi
        apply (hsupport _ (hb.trans hw) i).mpr
        have ht := (hsupport w hw i).mp hi
        rw [heval w hk hw, hop] at ht
        simp only [ite_true, Bool.and_eq_true] at ht
        exact ht.2
      rcases hchoice with hA | hB
      · have hFA : F (a w) = S (a w) := ite_eq_left ⟨ha.trans hw, hA⟩
        refine ⟨{a w}, by simpa using ha, ?_, by simp⟩
        simpa [hF, hFA] using hsubA
      · have hFB : F (b w) = S (b w) := ite_eq_left ⟨hb.trans hw, hB⟩
        refine ⟨{b w}, by simpa using hb, ?_, by simp⟩
        simpa [hF, hFB] using hsubB
    | false =>
      have hA : below (a w) := by
        intro x hx
        apply hgood.2 x
        simp [heval w hk hw x, hop, hx]
      have hB : below (b w) := by
        intro x hx
        apply hgood.2 x
        simp [heval w hk hw x, hop, hx]
      have hFA : F (a w) = S (a w) := ite_eq_left ⟨ha.trans hw, hA⟩
      have hFB : F (b w) = S (b w) := ite_eq_left ⟨hb.trans hw, hB⟩
      have hsub : S w ⊆ S (a w) ∪ S (b w) := by
        intro i hi
        have ht := (hsupport w hw i).mp hi
        rw [heval w hk hw, hop] at ht
        simp only [Bool.false_eq_true, ite_false, Bool.or_eq_true] at ht
        rcases ht with ht | ht
        · exact Finset.mem_union_left _ ((hsupport _ (ha.trans hw) i).mpr ht)
        · exact Finset.mem_union_right _ ((hsupport _ (hb.trans hw) i).mpr ht)
      have hp : w ∈ paid := by
        simp only [paid, Finset.mem_filter, Finset.mem_range]
        exact ⟨hw, hk, hop, hF ▸ hlarge, hgood.2⟩
      refine ⟨{a w, b w}, ?_, ?_, ?_⟩
      · intro v hv
        rcases Finset.mem_insert.mp hv with rfl | hv
        · exact Finset.mem_range.mpr ha
        · rw [Finset.mem_singleton.mp hv]
          exact Finset.mem_range.mpr hb
      · simpa [hF, hFA, hFB] using hsub
      · simp only [hp, ite_true]
        exact Finset.card_le_two
  have hRrange : R ⊆ Finset.range N := by
    intro w hw
    exact Finset.mem_range.mpr (hR w hw).1
  have hroots : R.biUnion F = R.biUnion S := by
    apply Finset.biUnion_congr rfl
    intro w hw
    exact ite_eq_left (hR w hw)
  have hpaid : Finset.range N ∩ paid = paid := by
    exact Finset.inter_eq_right.mpr (Finset.filter_subset _ _)
  have hc := countUnion F paid N hstep R hRrange
  simpa only [hroots, hpaid] using hc

end PEqualNP.Outside.L_meta_4970_aux.Structural
