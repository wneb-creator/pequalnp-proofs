import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Union
import Mathlib.Data.Fintype.Card
import Mathlib.Algebra.Order.BigOperators.Group.Finset

namespace PEqualNP.Outside.L_meta_2602_aux.OrFamilyBound

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

noncomputable def charged (n k : ℕ) (A : Finset (Fin n))
    (F : ℕ → (Fin n → Bool) → Bool) (op : ℕ → Bool) : Finset ℕ := by
  classical
  exact (Finset.range (n + k)).filter (fun i => n ≤ i ∧ op (i - n) = true ∧
    Below A (F i) ∧ 2 ≤ (support n F i).card)

lemma clause_charge_bound (n k : ℕ) (A : Finset (Fin n))
    (F : ℕ → (Fin n → Bool) → Bool) (op : ℕ → Bool) (a b : ℕ → ℕ)
    (hinput : ∀ i (hi : i < n) x, F i x = x ⟨i, hi⟩)
    (hgate : ∀ j < k, ∀ x, F (n + j) x =
      if op j then F (a j) x || F (b j) x else F (a j) x && F (b j) x)
    (ha : ∀ j < k, a j < n + j) (hb : ∀ j < k, b j < n + j)
    (hmono : ∀ i < n + k, BitMonotone (F i))
    (out : ℕ) (hout : out < n + k)
    (hspec : ∀ x, F out x = true ↔ ∃ i ∈ A, x i = true) :
    A.card ≤ (charged n k A F op).card + 1 := by
  classical
  let fs (i : ℕ) := if Below A (F i) then support n F i else ∅
  let l (i : ℕ) := a (i - n)
  let r (i : ℕ) := b (i - n)
  have input_small (i : ℕ) (hi : i < n) : (fs i).card ≤ 1 := by
    by_cases hbelow : Below A (F i)
    · have hsub : support n F i ⊆ {⟨i, hi⟩} := by
        intro p hp
        have ht := (Finset.mem_filter.mp hp).2
        rw [hinput i hi] at ht
        simp only [singleton, decide_eq_true_eq] at ht
        exact Finset.mem_singleton.mpr ht.symm
      simpa [fs, hbelow] using Finset.card_le_card hsub
    · simp [fs, hbelow]
  have union_step (w : ℕ) (hw : w ∈ charged n k A F op) :
      l w < w ∧ r w < w ∧ fs w = fs (l w) ∪ fs (r w) := by
    simp only [charged, Finset.mem_filter, Finset.mem_range] at hw
    obtain ⟨hwk, hwn, hop, hbelow, _⟩ := hw
    have hj : w - n < k := by omega
    have heq : n + (w - n) = w := by omega
    have hba : Below A (F (a (w - n))) := by
      intro x hx
      apply hbelow x
      rw [← heq, hgate (w - n) hj x, hop]
      simp [hx]
    have hbb : Below A (F (b (w - n))) := by
      intro x hx
      apply hbelow x
      rw [← heq, hgate (w - n) hj x, hop]
      simp [hx]
    refine ⟨by dsimp [l]; have := ha (w - n) hj; omega,
      by dsimp [r]; have := hb (w - n) hj; omega, ?_⟩
    simp only [fs, l, r, if_pos hbelow, if_pos hba, if_pos hbb]
    ext p
    simp only [support, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
    rw [← heq, hgate (w - n) hj (singleton p), hop]
    simp
  have unary_step (w : ℕ) (hw : w < n + k) (hnu : w ∉ charged n k A F op) :
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
      have hcard : 2 ≤ (support n F w).card := by
        simp only [fs, if_pos hbelow] at hsmall
        omega
      have hop : op (w - n) = false := by
        cases hop : op (w - n)
        · rfl
        · exact False.elim (hnu (by
            simp only [charged, Finset.mem_filter, Finset.mem_range]
            exact ⟨hw, hwn, hop, hbelow, hcard⟩))
      have haj : a (w - n) < w := by have := ha (w - n) hj; omega
      have hbj : b (w - n) < w := by have := hb (w - n) hj; omega
      have hand : Below A (fun x => F (a (w - n)) x && F (b (w - n)) x) := by
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
  have hbelowout : Below A (F out) := fun x hx => (hspec x).1 hx
  have hfout : fs out = A := by
    ext p
    simp only [fs, if_pos hbelowout, support, Finset.mem_filter, Finset.mem_univ, true_and]
    simpa [singleton] using hspec (singleton p)
  have hfil : (charged n k A F op).filter (fun j => j < n + k) = charged n k A F op := by
    apply Finset.filter_true_of_mem
    intro j hj
    exact Finset.mem_range.mp (Finset.mem_filter.mp hj).1
  have h := unary_union_bound (charged n k A F op) fs l r (n + k) unary_step union_step
    (n + k) le_rfl {out} (by simpa using hout)
  simpa only [Finset.singleton_biUnion, Finset.card_singleton, hfout, hfil, Nat.add_comm] using h

lemma charged_disjoint (n k : ℕ) (A B : Finset (Fin n))
    (F : ℕ → (Fin n → Bool) → Bool) (op : ℕ → Bool)
    (hsmall : ∀ p q, p ∈ A → p ∈ B → q ∈ A → q ∈ B → p = q) :
    Disjoint (charged n k A F op) (charged n k B F op) := by
  classical
  apply Finset.disjoint_left.mpr
  intro w hwA hwB
  simp only [charged, Finset.mem_filter, Finset.mem_range] at hwA hwB
  obtain ⟨_, _, _, hA, hsize⟩ := hwA
  obtain ⟨_, _, _, hB, _⟩ := hwB
  have mem (T : Finset (Fin n)) (hT : Below T (F w)) (p : Fin n)
      (hp : p ∈ support n F w) : p ∈ T := by
    have h := hT (singleton p) (Finset.mem_filter.mp hp).2
    simpa [singleton] using h
  have hcard : (support n F w).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro p hp q hq
    exact hsmall p q (mem A hA p hp) (mem B hB p hp) (mem A hA q hq) (mem B hB q hq)
  omega

lemma family_or_lower_bound (n k m d : ℕ) (A : Fin m → Finset (Fin n))
    (F : ℕ → (Fin n → Bool) → Bool) (op : ℕ → Bool) (a b : ℕ → ℕ)
    (hinput : ∀ i (hi : i < n) x, F i x = x ⟨i, hi⟩)
    (hgate : ∀ j < k, ∀ x, F (n + j) x =
      if op j then F (a j) x || F (b j) x else F (a j) x && F (b j) x)
    (ha : ∀ j < k, a j < n + j) (hb : ∀ j < k, b j < n + j)
    (hmono : ∀ i < n + k, BitMonotone (F i))
    (out : Fin m → ℕ) (hout : ∀ i, out i < n + k)
    (hspec : ∀ i x, F (out i) x = true ↔ ∃ p ∈ A i, x p = true)
    (hsize : ∀ i, (A i).card = d)
    (hintersection : ∀ i j, i ≠ j →
      ∀ p q, p ∈ A i → p ∈ A j → q ∈ A i → q ∈ A j → p = q) :
    m * (d - 1) ≤ ((Finset.range k).filter (fun j => op j = true)).card := by
  classical
  have each (i : Fin m) : d - 1 ≤ (charged n k (A i) F op).card := by
    have h := clause_charge_bound n k (A i) F op a b hinput hgate ha hb hmono
      (out i) (hout i) (hspec i)
    rw [hsize i] at h
    omega
  have hd : ((Finset.univ : Finset (Fin m)) : Set (Fin m)).PairwiseDisjoint
      (fun i => charged n k (A i) F op) := by
    intro i _ j _ hij
    exact charged_disjoint n k (A i) (A j) F op (hintersection i j hij)
  let U := Finset.univ.biUnion (fun i : Fin m => charged n k (A i) F op)
  have hU : U.card = ∑ i : Fin m, (charged n k (A i) F op).card :=
    Finset.card_biUnion hd
  have hsub : U ⊆ ((Finset.range k).filter (fun j => op j = true)).image (fun j => n + j) := by
    intro w hw
    obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp hw
    simp only [charged, Finset.mem_filter, Finset.mem_range] at hi
    obtain ⟨hwk, hwn, hop, _, _⟩ := hi
    apply Finset.mem_image.mpr
    refine ⟨w - n, ?_, by omega⟩
    simp only [Finset.mem_filter, Finset.mem_range]
    exact ⟨by omega, hop⟩
  have hupper : U.card ≤ ((Finset.range k).filter (fun j => op j = true)).card :=
    (Finset.card_le_card hsub).trans Finset.card_image_le
  have hlower : m * (d - 1) ≤ ∑ i : Fin m, (charged n k (A i) F op).card := by
    calc
      m * (d - 1) = ∑ _ : Fin m, (d - 1) := by simp
      _ ≤ _ := Finset.sum_le_sum (fun i _ => each i)
  rw [hU] at hupper
  exact hlower.trans hupper

lemma family_size_lower_bound (n k m d : ℕ) (A : Fin m → Finset (Fin n))
    (F : ℕ → (Fin n → Bool) → Bool) (op : ℕ → Bool) (a b : ℕ → ℕ)
    (hinput : ∀ i (hi : i < n) x, F i x = x ⟨i, hi⟩)
    (hgate : ∀ j < k, ∀ x, F (n + j) x =
      if op j then F (a j) x || F (b j) x else F (a j) x && F (b j) x)
    (ha : ∀ j < k, a j < n + j) (hb : ∀ j < k, b j < n + j)
    (hmono : ∀ i < n + k, BitMonotone (F i))
    (out : Fin m → ℕ) (hout : ∀ i, out i < n + k)
    (hspec : ∀ i x, F (out i) x = true ↔ ∃ p ∈ A i, x p = true)
    (hsize : ∀ i, (A i).card = d)
    (hintersection : ∀ i j, i ≠ j →
      ∀ p q, p ∈ A i → p ∈ A j → q ∈ A i → q ∈ A j → p = q) :
    m * (d - 1) ≤ k := by
  have h := family_or_lower_bound n k m d A F op a b hinput hgate ha hb hmono out hout
    hspec hsize hintersection
  apply h.trans
  simpa using Finset.card_le_card (Finset.filter_subset (fun j => op j = true) (Finset.range k))

end PEqualNP.Outside.L_meta_2602_aux.OrFamilyBound
