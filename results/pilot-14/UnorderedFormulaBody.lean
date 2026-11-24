namespace PEqualNP.Outside.L_meta_670_aux.UnorderedFormula
open LiveCheck TightFormula

def test : Nat → List Sig → Bool
  | 0, _ => true
  | n+1, v => decide (v.length ≤ 1) ||
      (UnorderedPairs.steps v).any fun w => (unionSep true w == top) && test n w

lemma cover {k t S} (h : Live k t S) {v : List Sig}
    (hp : v.Perm (S.toList.map phase)) : unionSep true v = top := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  obtain ⟨a, ha, hs⟩ := LiveCheck.live_sep h j hj
  have ht := LiveCheck.sep_weaken t a j hj hs
  have hm : phase a ∈ v := hp.mem_iff.mpr (List.mem_map.mpr ⟨a, Finset.mem_toList.mpr ha, rfl⟩)
  have hu := (LiveCheck.mem_unionSep true v j).mpr ⟨phase a, hm, by simpa only [phase_sep] using ht⟩
  simpa only [top, BitVec.getLsbD_allOnes, hj, decide_true] using hu

lemma tight_test {k t S} (h : Live k t S) (ht : S.card + t = k+1) :
    ∀ n v, v.Perm (S.toList.map phase) → test n v = true := by
  induction h with
  | stop =>
    intro n v hp
    have hl : v.length = 1 := by simpa using hp.length_eq
    cases n <;> simp [test, hl]
  | @unary k t U a ha hf tail ih =>
    have hn : neg a ∉ U := fun hm => hf (Finset.mem_insert_of_mem hm)
    have hs := LiveCheck.live_size tail
    rw [Finset.card_insert_of_notMem hn] at hs
    have hu : a ∉ U := by
      intro hm
      rw [Finset.insert_eq_of_mem hm] at ht
      omega
    have ht' : (insert (neg a) U).card + t = k+1 := by
      rw [Finset.card_insert_of_notMem hu] at ht
      rw [Finset.card_insert_of_notMem hn]
      omega
    intro n v hp
    apply ih ht' n v
    have p₁ := (Finset.toList_insert hu).map phase
    have p₂ := (Finset.toList_insert hn).map phase
    simp only [List.map_cons, phase_neg] at p₁ p₂
    exact hp.trans (p₁.trans p₂.symm)
  | @binary k t U a b d ha hb hab hf tail ih =>
    have hn : bin d a b ∉ U := fun hm => hf (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hm))
    have hs := LiveCheck.live_size tail
    rw [Finset.card_insert_of_notMem hn] at hs
    have hu : a ∉ insert b U := by
      intro hm
      rw [Finset.insert_eq_of_mem hm] at ht
      have hc := Finset.card_insert_le b U
      omega
    have hv : b ∉ U := by
      intro hm
      rw [Finset.insert_eq_of_mem hm] at ht
      have hc := Finset.card_insert_le a U
      omega
    have ht' : (insert (bin d a b) U).card + t = k+1 := by
      rw [Finset.card_insert_of_notMem hu, Finset.card_insert_of_notMem hv] at ht
      rw [Finset.card_insert_of_notMem hn]
      omega
    intro n v hp
    cases n with
    | zero => rfl
    | succ n =>
      have p₁ := (Finset.toList_insert hu).map phase
      have p₂ := (Finset.toList_insert hv).map phase
      have p : v.Perm (phase a :: phase b :: U.toList.map phase) := by
        exact hp.trans (p₁.trans (p₂.cons (phase a)))
      obtain ⟨w, hw, hpw⟩ := UnorderedPairs.step_mem p (op_mem d a b)
      have hq : w.Perm ((insert (bin d a b) U).toList.map phase) :=
        hpw.trans ((Finset.toList_insert hn).map phase).symm
      simp only [test, Bool.or_eq_true]
      right
      exact List.any_eq_true.mpr ⟨w, hw, by simp [cover tail hq, ih ht' n w hq]⟩
def testOne : Nat → List Sig → Bool
  | 0, _ => true
  | n+1, v => decide (v.length ≤ 1) ||
      v.any (fun a => test (n+1) (a :: v)) ||
      (UnorderedPairs.steps v).any (fun w => (unionSep true w == top) && testOne n w) ||
      (UnorderedPairs.keepSteps v).any (fun w => (unionSep true w == top) && test n w)

lemma one_test {k t S} (h : Live k t S) (ht : S.card + t = k) :
    ∀ n v, v.Perm (S.toList.map phase) → testOne n v = true := by
  induction h with
  | stop =>
    intro n v hp
    have hl : v.length = 1 := by simpa using hp.length_eq
    cases n <;> simp [testOne, hl]
  | @unary k t U a ha hf tail ih =>
    have hn : neg a ∉ U := fun hm => hf (Finset.mem_insert_of_mem hm)
    intro n v hp
    by_cases hu : a ∈ U
    · have ht' : (insert (neg a) U).card + t = k+1 := by
        rw [Finset.insert_eq_of_mem hu] at ht
        rw [Finset.card_insert_of_notMem hn]
        omega
      have hv : v.Perm (U.toList.map phase) := by
        simpa only [Finset.insert_eq_of_mem hu] using hp
      have hm : phase a ∈ v :=
        hv.mem_iff.mpr (List.mem_map.mpr ⟨a, Finset.mem_toList.mpr hu, rfl⟩)
      have hq : (phase a :: v).Perm ((insert (neg a) U).toList.map phase) := by
        have p := (Finset.toList_insert hn).map phase
        simp only [List.map_cons, phase_neg] at p
        exact (hv.cons (phase a)).trans p.symm
      cases n with
      | zero => rfl
      | succ n =>
        simp only [testOne, Bool.or_eq_true]
        exact Or.inl (Or.inl (Or.inr (List.any_eq_true.mpr
          ⟨phase a, hm, tight_test tail ht' (n+1) _ hq⟩)))
    · have ht' : (insert (neg a) U).card + t = k := by
        rw [Finset.card_insert_of_notMem hu] at ht
        rw [Finset.card_insert_of_notMem hn]
        omega
      apply ih ht' n v
      have p₁ := (Finset.toList_insert hu).map phase
      have p₂ := (Finset.toList_insert hn).map phase
      simp only [List.map_cons, phase_neg] at p₁ p₂
      exact hp.trans (p₁.trans p₂.symm)
  | @binary k t U a b d ha hb hab hf tail ih =>
    have hn : bin d a b ∉ U := fun hm =>
      hf (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hm))
    have hs := LiveCheck.live_size tail
    rw [Finset.card_insert_of_notMem hn] at hs
    intro n v hp
    cases n with
    | zero => rfl
    | succ n =>
      by_cases hau : a ∈ U
      · have hbu : b ∉ U := by
          intro hbU
          rw [Finset.insert_eq_of_mem hbU, Finset.insert_eq_of_mem hau] at ht
          omega
        have hai : a ∈ insert b U := Finset.mem_insert_of_mem hau
        have ht' : (insert (bin d a b) U).card + t = k+1 := by
          rw [Finset.insert_eq_of_mem hai, Finset.card_insert_of_notMem hbu] at ht
          rw [Finset.card_insert_of_notMem hn]
          omega
        have hpU : U.toList.Perm (a :: (U.erase a).toList) := by
          simpa only [Finset.insert_erase hau] using
            (Finset.toList_insert (Finset.notMem_erase a U))
        have p : v.Perm (phase b :: phase a :: (U.erase a).toList.map phase) := by
          rw [Finset.insert_eq_of_mem hai] at hp
          exact hp.trans (((Finset.toList_insert hbu).map phase).trans
            ((hpU.map phase).cons (phase b)))
        obtain ⟨w, hw, hpw⟩ := UnorderedPairs.keep_step_mem p (op_mem d b a) false
        have he : bin d b a = bin d a b := by cases d <;> simp [bin, BitVec.and_comm, BitVec.or_comm]
        have hq : w.Perm ((insert (bin d a b) U).toList.map phase) := by
          simp only [Bool.false_eq_true, ↓reduceIte, he] at hpw
          exact (hpw.trans ((hpU.map phase).symm.cons _)).trans
            ((Finset.toList_insert hn).map phase).symm
        simp only [testOne, Bool.or_eq_true]
        exact Or.inr (List.any_eq_true.mpr ⟨w, hw,
          by simp [cover tail hq, tight_test tail ht' n w hq]⟩)
      · by_cases hbu : b ∈ U
        · have hai : a ∉ insert b U := by simpa [Finset.mem_insert, hab] using hau
          have ht' : (insert (bin d a b) U).card + t = k+1 := by
            rw [Finset.insert_eq_of_mem hbu, Finset.card_insert_of_notMem hau] at ht
            rw [Finset.card_insert_of_notMem hn]
            omega
          have hpU : U.toList.Perm (b :: (U.erase b).toList) := by
            simpa only [Finset.insert_erase hbu] using
              (Finset.toList_insert (Finset.notMem_erase b U))
          have p : v.Perm (phase a :: phase b :: (U.erase b).toList.map phase) := by
            rw [Finset.insert_eq_of_mem hbu] at hp
            exact hp.trans (((Finset.toList_insert hau).map phase).trans
              ((hpU.map phase).cons (phase a)))
          obtain ⟨w, hw, hpw⟩ := UnorderedPairs.keep_step_mem p (op_mem d a b) false
          have hq : w.Perm ((insert (bin d a b) U).toList.map phase) := by
            simp only [Bool.false_eq_true, ↓reduceIte] at hpw
            exact (hpw.trans ((hpU.map phase).symm.cons _)).trans
              ((Finset.toList_insert hn).map phase).symm
          simp only [testOne, Bool.or_eq_true]
          exact Or.inr (List.any_eq_true.mpr ⟨w, hw,
            by simp [cover tail hq, tight_test tail ht' n w hq]⟩)
        · have hai : a ∉ insert b U := by simpa [Finset.mem_insert, hab] using hau
          have ht' : (insert (bin d a b) U).card + t = k := by
            rw [Finset.card_insert_of_notMem hai, Finset.card_insert_of_notMem hbu] at ht
            rw [Finset.card_insert_of_notMem hn]
            omega
          have p : v.Perm (phase a :: phase b :: U.toList.map phase) := by
            exact hp.trans (((Finset.toList_insert hai).map phase).trans
              (((Finset.toList_insert hbu).map phase).cons (phase a)))
          obtain ⟨w, hw, hpw⟩ := UnorderedPairs.step_mem p (op_mem d a b)
          have hq : w.Perm ((insert (bin d a b) U).toList.map phase) :=
            hpw.trans ((Finset.toList_insert hn).map phase).symm
          simp only [testOne, Bool.or_eq_true]
          exact Or.inl (Or.inr (List.any_eq_true.mpr ⟨w, hw,
            by simp [cover tail hq, ih ht' n w hq]⟩))
lemma any_false_fin {α : Type} (xs : List α) (f : α → Bool)
    (h : ∀ i : Fin xs.length, f xs[i] = false) : xs.any f = false := by
  apply List.any_eq_false.mpr
  intro a ha
  obtain ⟨i, hi⟩ := List.mem_iff_get.mp ha
  have hx : xs[i] = a := hi
  have he := h i
  rw [hx] at he
  simp only [he, Bool.false_eq_true, not_false_eq_true]

lemma testOne_succ_false (n : Nat) (v : List Sig)
    (hl : ¬v.length ≤ 1)
    (hd : ∀ i : Fin v.length, test (n+1) (v[i] :: v) = false)
    (hc : ∀ i : Fin (UnorderedPairs.steps v).length,
      ((unionSep true (UnorderedPairs.steps v)[i] == top) && testOne n (UnorderedPairs.steps v)[i]) = false)
    (hk : ∀ i : Fin (UnorderedPairs.keepSteps v).length,
      ((unionSep true (UnorderedPairs.keepSteps v)[i] == top) && test n (UnorderedPairs.keepSteps v)[i]) = false) :
    testOne (n+1) v = false := by
  have h₁ := any_false_fin v (fun a => test (n+1) (a :: v)) hd
  have h₂ := any_false_fin (UnorderedPairs.steps v) (fun w => (unionSep true w == top) && testOne n w) hc
  have h₃ := any_false_fin (UnorderedPairs.keepSteps v) (fun w => (unionSep true w == top) && test n w) hk
  simp only [testOne, h₁, h₂, h₃, hl, decide_false, Bool.false_or]

lemma test_succ_false (n : Nat) (v : List Sig)
    (hl : ¬v.length ≤ 1)
    (hc : ∀ i : Fin (UnorderedPairs.steps v).length,
      ((unionSep true (UnorderedPairs.steps v)[i] == top) && test n (UnorderedPairs.steps v)[i]) = false) :
    test (n+1) v = false := by
  have h₁ := any_false_fin (UnorderedPairs.steps v) (fun w => (unionSep true w == top) && test n w) hc
  simp only [test, h₁, hl, decide_false, Bool.false_or]

end PEqualNP.Outside.L_meta_670_aux.UnorderedFormula
