import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Union
import Mathlib.Data.Fintype.Card
import Mathlib.Algebra.Order.BigOperators.Group.Finset

namespace PEqualNP.Outside.L_meta_2602_aux.ProductiveBound

lemma unary_union_bound {α : Type} [DecidableEq α] (U : Finset ℕ) (f : ℕ → Finset α) (l r : ℕ → ℕ)
    (N0 : ℕ) (hleaf : ∀ j < N0, j ∉ U → (f j).card ≤ 1 ∨ ∃ p < j, f j ⊆ f p)
    (hU : ∀ j ∈ U, l j < j ∧ r j < j ∧ f j = f (l j) ∪ f (r j)) :
    ∀ N ≤ N0, ∀ V : Finset ℕ, V ⊆ Finset.range N →
      (V.biUnion f).card ≤ V.card + (U.filter (fun j => j < N)).card := by
  intro N
  induction N with
  | zero =>
    intro _ V hV
    have : V = ∅ := by simpa using hV
    subst this
    simp
  | succ N ih =>
    intro hN V hV
    have hmono : (U.filter (fun j => j < N)).card ≤ (U.filter (fun j => j < N + 1)).card :=
      Finset.card_le_card (fun j hj => by
        rw [Finset.mem_filter] at hj ⊢
        exact ⟨hj.1, by omega⟩)
    by_cases hNV : N ∈ V
    · have hV' : V.erase N ⊆ Finset.range N := by
        intro j hj
        have h1 := Finset.mem_erase.1 hj
        have h2 := Finset.mem_range.1 (hV h1.2)
        exact Finset.mem_range.2 (by omega)
      have hcard : (V.erase N).card + 1 = V.card := Finset.card_erase_add_one hNV
      have hsplit : V.biUnion f = f N ∪ (V.erase N).biUnion f := by
        conv_lhs => rw [← Finset.insert_erase hNV]
        rw [Finset.biUnion_insert]
      by_cases hNU : N ∈ U
      · obtain ⟨hl, hr, hf⟩ := hU N hNU
        have hV2 : insert (l N) (insert (r N) (V.erase N)) ⊆ Finset.range N := by
          intro j hj
          rcases Finset.mem_insert.1 hj with rfl | hj
          · exact Finset.mem_range.2 hl
          · rcases Finset.mem_insert.1 hj with rfl | hj
            · exact Finset.mem_range.2 hr
            · exact hV' hj
        have h1 := ih (by omega) _ hV2
        have hsub : V.biUnion f ⊆ (insert (l N) (insert (r N) (V.erase N))).biUnion f := by
          rw [hsplit, hf, Finset.biUnion_insert, Finset.biUnion_insert, Finset.union_assoc]
        have h2 := Finset.card_le_card hsub
        have h3 : (insert (l N) (insert (r N) (V.erase N))).card ≤ (V.erase N).card + 2 :=
          (Finset.card_insert_le _ _).trans (by
            have := Finset.card_insert_le (r N) (V.erase N)
            omega)
        have h4 : (U.filter (fun j => j < N + 1)).card = (U.filter (fun j => j < N)).card + 1 := by
          have : U.filter (fun j => j < N + 1) = insert N (U.filter (fun j => j < N)) := by
            ext j
            simp only [Finset.mem_filter, Finset.mem_insert]
            constructor
            · rintro ⟨hj, hlt⟩
              by_cases e : j = N
              · exact Or.inl e
              · exact Or.inr ⟨hj, by omega⟩
            · rintro (rfl | ⟨hj, hlt⟩)
              · exact ⟨hNU, by omega⟩
              · exact ⟨hj, by omega⟩
          rw [this, Finset.card_insert_of_notMem (by simp)]
        omega
      · rcases hleaf N (by omega) hNU with hleaf | ⟨p, hp, hsub⟩
        · have h1 := ih (by omega) _ hV'
          have h3 : (V.biUnion f).card ≤ (f N).card + ((V.erase N).biUnion f).card := by
            rw [hsplit]
            exact Finset.card_union_le _ _
          omega
        · have hV2 : insert p (V.erase N) ⊆ Finset.range N := by
            intro j hj
            rcases Finset.mem_insert.1 hj with rfl | hj
            · exact Finset.mem_range.2 hp
            · exact hV' hj
          have h1 := ih (by omega) _ hV2
          have hsubV : V.biUnion f ⊆ (insert p (V.erase N)).biUnion f := by
            rw [hsplit, Finset.biUnion_insert]
            exact Finset.union_subset_union_left hsub
          have h2 := Finset.card_le_card hsubV
          have h3 := Finset.card_insert_le p (V.erase N)
          omega
    · have hV' : V ⊆ Finset.range N := by
        intro j hj
        have h2 := Finset.mem_range.1 (hV hj)
        have : j ≠ N := fun e => hNV (e ▸ hj)
        exact Finset.mem_range.2 (by omega)
      have h1 := ih (by omega) V hV'
      omega


def BitMonotone {n : ℕ} (f : (Fin n → Bool) → Bool) : Prop :=
  ∀ x y, (∀ i, x i = true → y i = true) → f x = true → f y = true

def singleton {n : ℕ} (i : Fin n) : Fin n → Bool := fun j => decide (j = i)

def Below {n : ℕ} (A : Finset (Fin n)) (f : (Fin n → Bool) → Bool) : Prop :=
  ∀ x, f x = true → ∃ i ∈ A, x i = true

lemma and_below {n : ℕ} (A : Finset (Fin n)) (f g : (Fin n → Bool) → Bool)
    (hf : BitMonotone f) (hg : BitMonotone g)
    (hfg : Below A (fun x => f x && g x)) : Below A f ∨ Below A g := by
  let z : Fin n → Bool := fun i => decide (i ∉ A)
  have hzero : (f z && g z) = false := by
    apply Bool.eq_false_iff.mpr
    intro h
    have := hfg z h
    simp [z] at this
  have recover (h : (Fin n → Bool) → Bool) (hm : BitMonotone h)
      (hz : h z = false) : Below A h := by
    intro x hx
    by_contra hno
    have hle : ∀ i, x i = true → z i = true := by
      intro i hi
      simp only [z, decide_eq_true_eq]
      exact fun hiA => hno ⟨i, hiA, hi⟩
    have ht := hm x z hle hx
    rw [hz] at ht
    contradiction
  cases hF : f z
  · exact Or.inl (recover f hf hF)
  · exact Or.inr (recover g hg (by simpa [hF] using hzero))

def support (n : ℕ) (F : ℕ → (Fin n → Bool) → Bool) (i : ℕ) : Finset (Fin n) :=
  Finset.univ.filter (fun p => F i (singleton p) = true)

noncomputable def productive (v n k : ℕ) (A : Finset (Fin v))
    (F : ℕ → (Fin v → Bool) → Bool) (op : ℕ → Bool) (a b : ℕ → ℕ) : Finset ℕ := by
  classical
  exact (Finset.range (n + k)).filter (fun i => n ≤ i ∧ op (i - n) = true ∧
    Below A (F i) ∧ ¬ support v F (a (i - n)) ⊆ support v F (b (i - n)) ∧
    ¬ support v F (b (i - n)) ⊆ support v F (a (i - n)))

lemma productive_charge_bound (v n k : ℕ) (A : Finset (Fin v))
    (F : ℕ → (Fin v → Bool) → Bool) (op : ℕ → Bool) (a b : ℕ → ℕ)
    (hseed : ∀ i < n, Below A (F i) → (support v F i).card ≤ 1)
    (hgate : ∀ j < k, ∀ x, F (n + j) x =
      if op j then F (a j) x || F (b j) x else F (a j) x && F (b j) x)
    (ha : ∀ j < k, a j < n + j) (hb : ∀ j < k, b j < n + j)
    (hmono : ∀ i < n + k, BitMonotone (F i))
    (out : ℕ) (hout : out < n + k)
    (hspec : ∀ x, F out x = true ↔ ∃ i ∈ A, x i = true) :
    A.card ≤ (productive v n k A F op a b).card + 1 := by
  classical
  let fs (i : ℕ) := if Below A (F i) then support v F i else ∅
  let l (i : ℕ) := a (i - n)
  let r (i : ℕ) := b (i - n)
  have input_small (i : ℕ) (hi : i < n) : (fs i).card ≤ 1 := by
    by_cases hbelow : Below A (F i)
    · simpa only [fs, if_pos hbelow] using hseed i hi hbelow
    · simp [fs, hbelow]
  have or_below (w : ℕ) (hwn : n ≤ w) (hw : w < n + k)
      (hop : op (w - n) = true) (hbelow : Below A (F w)) :
      Below A (F (a (w - n))) ∧ Below A (F (b (w - n))) := by
    have hj : w - n < k := by omega
    have heq : n + (w - n) = w := by omega
    constructor
    · intro x hx
      apply hbelow x
      rw [← heq, hgate (w - n) hj x, hop]
      simp [hx]
    · intro x hx
      apply hbelow x
      rw [← heq, hgate (w - n) hj x, hop]
      simp [hx]
  have or_union (w : ℕ) (hwn : n ≤ w) (hw : w < n + k)
      (hop : op (w - n) = true) (hbelow : Below A (F w)) :
      fs w = fs (l w) ∪ fs (r w) := by
    have hj : w - n < k := by omega
    have heq : n + (w - n) = w := by omega
    obtain ⟨hba, hbb⟩ := or_below w hwn hw hop hbelow
    simp only [fs, l, r, if_pos hbelow, if_pos hba, if_pos hbb]
    ext p
    simp only [support, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
    rw [← heq, hgate (w - n) hj (singleton p), hop]
    simp
  have union_step (w : ℕ) (hw : w ∈ productive v n k A F op a b) :
      l w < w ∧ r w < w ∧ fs w = fs (l w) ∪ fs (r w) := by
    simp only [productive, Finset.mem_filter, Finset.mem_range] at hw
    obtain ⟨hwk, hwn, hop, hbelow, _, _⟩ := hw
    have hj : w - n < k := by omega
    refine ⟨by dsimp [l]; have := ha (w - n) hj; omega,
      by dsimp [r]; have := hb (w - n) hj; omega,
      or_union w hwn hwk hop hbelow⟩
  have unary_step (w : ℕ) (hw : w < n + k)
      (hnu : w ∉ productive v n k A F op a b) :
      (fs w).card ≤ 1 ∨ ∃ p < w, fs w ⊆ fs p := by
    by_cases hsmall : (fs w).card ≤ 1
    · exact Or.inl hsmall
    · right
      have hbelow : Below A (F w) := by
        by_contra hno
        simp [fs, hno] at hsmall
      have hwn : n ≤ w := by
        by_contra hno
        exact hsmall (input_small w (by omega))
      have hj : w - n < k := by omega
      have heq : n + (w - n) = w := by omega
      have haj : a (w - n) < w := by have := ha (w - n) hj; omega
      have hbj : b (w - n) < w := by have := hb (w - n) hj; omega
      cases hop : op (w - n)
      · have hand : Below A (fun x => F (a (w - n)) x && F (b (w - n)) x) := by
          intro x hx
          apply hbelow x
          rw [← heq, hgate (w - n) hj x, hop]
          exact hx
        rcases and_below A (F (a (w - n))) (F (b (w - n)))
            (hmono _ (by omega)) (hmono _ (by omega)) hand with hba | hbb
        · refine ⟨a (w - n), haj, ?_⟩
          intro p hp
          have ht : F w (singleton p) = true := by simpa [fs, hbelow, support] using hp
          rw [← heq, hgate (w - n) hj (singleton p), hop] at ht
          have hpa := (Bool.and_eq_true_iff.mp ht).1
          simpa [fs, hba, support] using hpa
        · refine ⟨b (w - n), hbj, ?_⟩
          intro p hp
          have ht : F w (singleton p) = true := by simpa [fs, hbelow, support] using hp
          rw [← heq, hgate (w - n) hj (singleton p), hop] at ht
          have hpb := (Bool.and_eq_true_iff.mp ht).2
          simpa [fs, hbb, support] using hpb
      · obtain ⟨hba, hbb⟩ := or_below w hwn hw hop hbelow
        have hor := or_union w hwn hw hop hbelow
        by_cases hab : support v F (a (w - n)) ⊆ support v F (b (w - n))
        · refine ⟨b (w - n), hbj, ?_⟩
          rw [hor]
          have hsub : fs (l w) ⊆ fs (r w) := by
            simpa only [fs, l, r, if_pos hba, if_pos hbb] using hab
          exact Finset.union_subset hsub (Finset.Subset.refl _)
        · have hba' : support v F (b (w - n)) ⊆ support v F (a (w - n)) := by
            by_contra hn
            apply hnu
            simp only [productive, Finset.mem_filter, Finset.mem_range]
            exact ⟨hw, hwn, hop, hbelow, hab, hn⟩
          refine ⟨a (w - n), haj, ?_⟩
          rw [hor]
          have hsub : fs (r w) ⊆ fs (l w) := by
            simpa only [fs, l, r, if_pos hba, if_pos hbb] using hba'
          exact Finset.union_subset (Finset.Subset.refl _) hsub
  have hbelowout : Below A (F out) := fun x hx => (hspec x).1 hx
  have hfout : fs out = A := by
    ext p
    simp only [fs, if_pos hbelowout, support, Finset.mem_filter, Finset.mem_univ, true_and]
    simpa [singleton] using hspec (singleton p)
  have hfil : (productive v n k A F op a b).filter (fun j => j < n + k) =
      productive v n k A F op a b := by
    apply Finset.filter_true_of_mem
    intro j hj
    exact Finset.mem_range.mp (Finset.mem_filter.mp hj).1
  have h := unary_union_bound (productive v n k A F op a b) fs l r (n + k)
    unary_step union_step (n + k) le_rfl {out} (by simpa using hout)
  simpa only [Finset.singleton_biUnion, Finset.card_singleton, hfout, hfil, Nat.add_comm] using h

lemma cofactor_productive_sum_bound (v n k m d : ℕ) (A : Fin m → Finset (Fin v))
    (F : Fin m → ℕ → (Fin v → Bool) → Bool) (op : ℕ → Bool) (a b : ℕ → ℕ)
    (hseed : ∀ t i, i < n → Below (A t) (F t i) → (support v (F t) i).card ≤ 1)
    (hgate : ∀ t j, j < k → ∀ x, F t (n + j) x =
      if op j then F t (a j) x || F t (b j) x else F t (a j) x && F t (b j) x)
    (ha : ∀ j < k, a j < n + j) (hb : ∀ j < k, b j < n + j)
    (hmono : ∀ t i, i < n + k → BitMonotone (F t i))
    (out : Fin m → ℕ) (hout : ∀ t, out t < n + k)
    (hspec : ∀ t x, F t (out t) x = true ↔ ∃ i ∈ A t, x i = true)
    (hsize : ∀ t, (A t).card = d) :
    m * (d - 1) ≤ ∑ t : Fin m, (productive v n k (A t) (F t) op a b).card := by
  classical
  have each (t : Fin m) : d - 1 ≤ (productive v n k (A t) (F t) op a b).card := by
    have h := productive_charge_bound v n k (A t) (F t) op a b (hseed t) (hgate t)
      ha hb (hmono t) (out t) (hout t) (hspec t)
    rw [hsize t] at h
    omega
  calc
    m * (d - 1) = ∑ _ : Fin m, (d - 1) := by simp
    _ ≤ _ := Finset.sum_le_sum (fun t _ => each t)

end PEqualNP.Outside.L_meta_2602_aux.ProductiveBound
