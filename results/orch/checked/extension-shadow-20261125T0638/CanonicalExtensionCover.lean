import CanonicalCompilerDefs

namespace PEqualNP.Outside.L_meta_1896_aux.CanonicalCompiler

lemma false_all_witness {n : Nat} (xs : List (Fin n)) (bad : Fin n → Bool)
    (h : xs.all bad = false) : ∃ i ∈ xs, bad i = false := by
  induction xs with
  | nil => simp at h
  | cons i xs ih =>
    cases hi : bad i with
    | false => exact ⟨i, by simp, hi⟩
    | true =>
      have ht : xs.all bad = false := by simpa [hi] using h
      obtain ⟨j, hj, hb⟩ := ih ht
      exact ⟨j, by simp [hj], hb⟩

def oldMembers {n : Nat} (s : Finset (Fin (n + 1))) : Finset (Fin n) :=
  Finset.univ.filter (fun i => i.castSucc ∈ s)

lemma oldMembers_image {n : Nat} (s : Finset (Fin (n + 1))) :
    (oldMembers s).image Fin.castSucc = s.erase (Fin.last n) := by
  ext j
  refine Fin.lastCases ?_ (fun i => ?_) j
  · simp [oldMembers]
  · simp [oldMembers]

lemma oldMembers_card {n : Nat} (s : Finset (Fin (n + 1))) :
    (oldMembers s).card = (s.erase (Fin.last n)).card := by
  rw [← oldMembers_image]
  symm
  apply Finset.card_image_of_injOn
  intro a ha b hb hab
  apply Fin.ext
  exact congrArg (fun j : Fin (n + 1) => j.val) hab

lemma false_sample_cover {n : Nat} (k : Nat) (program : Program n k)
    (bad : Fin n → Bool) (hbad : evaluate k program bad = false) :
    ∃ s : Finset (Fin n), s.card ≤ k + 1 ∧
      (∀ i ∈ s, bad i = false) ∧
      (∀ values : Fin n → Bool, evaluate k program values = true →
        ∃ i ∈ s, values i = true) := by
  classical
  induction k generalizing n with
  | zero =>
    change List (Fin n) at program
    obtain ⟨i, hi, hbi⟩ := false_all_witness program bad hbad
    refine ⟨{i}, by simp, ?_, ?_⟩
    · intro j hj
      rcases Finset.mem_singleton.mp hj with rfl
      exact hbi
    · intro values hv
      refine ⟨i, by simp, ?_⟩
      exact List.all_eq_true.mp hv i hi
  | succ k ih =>
    let left := program.1.1
    let right := program.1.2
    let nextBad : Fin (n + 1) → Bool :=
      Fin.snoc bad (left.all bad || right.all bad)
    obtain ⟨s, hcard, hsbad, hscover⟩ := ih program.2 nextBad hbad
    have hold (i : Fin n) (hi : i ∈ oldMembers s) : bad i = false := by
      have hm : i.castSucc ∈ s := by simpa [oldMembers] using hi
      simpa [nextBad] using hsbad i.castSucc hm
    by_cases hlast : Fin.last n ∈ s
    · have hor : (left.all bad || right.all bad) = false := by
        simpa [nextBad] using hsbad (Fin.last n) hlast
      have hl : left.all bad = false := by
        cases ha : left.all bad <;> cases hb : right.all bad <;> simp_all
      have hr : right.all bad = false := by
        cases ha : left.all bad <;> cases hb : right.all bad <;> simp_all
      obtain ⟨a, ha, hba⟩ := false_all_witness left bad hl
      obtain ⟨b, hb, hbb⟩ := false_all_witness right bad hr
      have hcc : (oldMembers s).card + 1 = s.card := by
        rw [oldMembers_card]
        exact Finset.card_erase_add_one hlast
      refine ⟨insert a (insert b (oldMembers s)), ?_, ?_, ?_⟩
      · have h1 := Finset.card_insert_le a (insert b (oldMembers s))
        have h2 := Finset.card_insert_le b (oldMembers s)
        omega
      · intro i hi
        rcases Finset.mem_insert.mp hi with rfl | hi
        · exact hba
        rcases Finset.mem_insert.mp hi with rfl | hi
        · exact hbb
        · exact hold i hi
      · intro values hv
        let nextValues : Fin (n + 1) → Bool :=
          Fin.snoc values (left.all values || right.all values)
        obtain ⟨j, hj, hval⟩ := hscover nextValues hv
        revert hj hval
        refine Fin.lastCases ?_ (fun i => ?_) j
        · intro hj hval
          have horv : (left.all values || right.all values) = true := by
            simpa [nextValues] using hval
          cases hlv : left.all values with
          | true =>
            exact ⟨a, by simp, List.all_eq_true.mp hlv a ha⟩
          | false =>
            have hrv : right.all values = true := by simpa [hlv] using horv
            exact ⟨b, by simp, List.all_eq_true.mp hrv b hb⟩
        · intro hi hval
          refine ⟨i, ?_, ?_⟩
          · simp [oldMembers, hi]
          · simpa [nextValues] using hval
    · have hcc : (oldMembers s).card ≤ s.card := by
        rw [oldMembers_card]
        exact Finset.card_le_card (Finset.erase_subset _ _)
      refine ⟨oldMembers s, by omega, hold, ?_⟩
      intro values hv
      let nextValues : Fin (n + 1) → Bool :=
        Fin.snoc values (left.all values || right.all values)
      obtain ⟨j, hj, hval⟩ := hscover nextValues hv
      revert hj hval
      refine Fin.lastCases ?_ (fun i => ?_) j
      · intro hj hval
        exact (hlast hj).elim
      · intro hi hval
        refine ⟨i, ?_, ?_⟩
        · simpa [oldMembers] using hi
        · simpa [nextValues] using hval

lemma extension_cover_lower_bound {n : Nat} {α : Type} (k : Nat)
    (program : Program n k) (bad : Fin n → Bool) (good : α → Fin n → Bool)
    (m : Nat)
    (hminimum : ∀ s : Finset (Fin n), (∀ i ∈ s, bad i = false) →
      (∀ a : α, ∃ i ∈ s, good a i = true) → m ≤ s.card)
    (hbad : evaluate k program bad = false)
    (hgood : ∀ a : α, evaluate k program (good a) = true) : m ≤ k + 1 := by
  obtain ⟨s, hcard, hsbad, hscover⟩ := false_sample_cover k program bad hbad
  exact (hminimum s hsbad (fun a => hscover (good a) (hgood a))).trans hcard

lemma fixed_forty_eight_extension_bound {n : Nat} {α : Type} (k : Nat)
    (program : Program n k) (bad : Fin n → Bool) (good : α → Fin n → Bool)
    (hminimum : ∀ s : Finset (Fin n), (∀ i ∈ s, bad i = false) →
      (∀ a : α, ∃ i ∈ s, good a i = true) → 9 ≤ s.card)
    (hbad : evaluate k program bad = false)
    (hgood : ∀ a : α, evaluate k program (good a) = true) : 56 ≤ 48 + k := by
  have h := extension_cover_lower_bound k program bad good 9 hminimum hbad hgood
  omega

end PEqualNP.Outside.L_meta_1896_aux.CanonicalCompiler
