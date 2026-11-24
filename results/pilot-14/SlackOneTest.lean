import TightFormulaTest
namespace PEqualNP.Outside.L_meta_670_aux.TightFormula
open LiveCheck

def keepSteps (v : List Sig) : List (List Sig) :=
  (singles v).flatMap fun (a, r) =>
    (singles r).flatMap fun (b, s) =>
      (ops a b).flatMap fun z => [z :: a :: s, z :: b :: s]

lemma keep_step_mem {v r : List Sig} {a b z : Sig}
    (hp : v.Perm (a :: b :: r)) (hz : z ∈ ops a b) (keep : Bool) :
    ∃ w ∈ keepSteps v, w.Perm (z :: (if keep then a else b) :: r) := by
  obtain ⟨r₁, h₁, p₁⟩ := pick_one (hp.mem_iff.mpr (by simp : a ∈ a :: b :: r))
  have q₁ : r₁.Perm (b :: r) := List.Perm.cons_inv (p₁.symm.trans hp)
  obtain ⟨r₂, h₂, p₂⟩ := pick_one (q₁.mem_iff.mpr (by simp : b ∈ b :: r))
  have q₂ : r₂.Perm r := List.Perm.cons_inv (p₂.symm.trans q₁)
  refine ⟨z :: (if keep then a else b) :: r₂, ?_, (q₂.cons _).cons z⟩
  exact List.mem_flatMap.mpr ⟨(a, r₁), h₁,
    List.mem_flatMap.mpr ⟨(b, r₂), h₂,
      List.mem_flatMap.mpr ⟨z, hz, by cases keep <;> simp⟩⟩⟩

def testOne : Nat → List Sig → Bool
  | 0, _ => true
  | n+1, v => decide (v.length ≤ 1) ||
      v.any (fun a => test (n+1) (a :: v)) ||
      (steps v).any (fun w => (unionSep true w == top) && testOne n w) ||
      (keepSteps v).any (fun w => (unionSep true w == top) && test n w)

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
        obtain ⟨w, hw, hpw⟩ := keep_step_mem p (op_mem d b a) false
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
          obtain ⟨w, hw, hpw⟩ := keep_step_mem p (op_mem d a b) false
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
          obtain ⟨w, hw, hpw⟩ := step_mem p (op_mem d a b)
          have hq : w.Perm ((insert (bin d a b) U).toList.map phase) :=
            hpw.trans ((Finset.toList_insert hn).map phase).symm
          simp only [testOne, Bool.or_eq_true]
          exact Or.inl (Or.inr (List.any_eq_true.mpr ⟨w, hw,
            by simp [cover tail hq, ih ht' n w hq]⟩))
end PEqualNP.Outside.L_meta_670_aux.TightFormula
