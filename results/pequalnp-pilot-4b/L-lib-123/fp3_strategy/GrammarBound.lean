import Mathlib

namespace PEqualNP.Outside.FP3Strategy

def Occurs (u w : List Bool) : Prop :=
  ∃ i : ℕ, i + u.length ≤ w.length ∧ u = (w.drop i).take u.length

lemma occurs_length {u w : List Bool} (h : Occurs u w) : u.length ≤ w.length := by
  obtain ⟨i, hi, _⟩ := h
  omega

lemma occurs_append {u a b : List Bool} (h : Occurs u (a ++ b)) :
    Occurs u a ∨ Occurs u b ∨
      ∃ k : ℕ, k < u.length ∧
        u = a.drop (a.length - k) ++ b.take (u.length - k) := by
  obtain ⟨i, hi, hu⟩ := h
  simp only [List.length_append] at hi
  by_cases hib : a.length ≤ i
  · right
    left
    refine ⟨i - a.length, by omega, ?_⟩
    simpa [List.drop_append, List.drop_eq_nil_iff.mpr hib] using hu
  · have hil : i ≤ a.length := by omega
    by_cases him : i + u.length ≤ a.length
    · left
      refine ⟨i, him, ?_⟩
      have htake : u.length ≤ (a.drop i).length := by simp; omega
      have hz : u.length - (a.length - i) = 0 := by omega
      simpa [List.drop_append, Nat.sub_eq_zero_of_le hil, List.take_append,
        hz] using hu
    · right
      right
      refine ⟨a.length - i, by omega, ?_⟩
      have hdrop : a.length - (a.length - i) = i := by omega
      have htake : (a.drop i).length ≤ u.length := by simp; omega
      simpa [List.drop_append, Nat.sub_eq_zero_of_le hil, List.take_append,
        List.take_of_length_le htake, hdrop] using hu

def crossingTable (g m : ℕ) (words : Fin g → List Bool) (left right : Fin g → Fin g) :
    Finset (List Bool) :=
  Finset.univ.image fun z : Fin g × Fin m =>
    (words (left z.1)).drop ((words (left z.1)).length - z.2.val) ++
      (words (right z.1)).take (m - z.2.val)

lemma crossingTable_card (g m : ℕ) (words : Fin g → List Bool)
    (left right : Fin g → Fin g) :
    (crossingTable g m words left right).card ≤ g * m := by
  unfold crossingTable
  calc
    _ ≤ (Finset.univ : Finset (Fin g × Fin m)).card := Finset.card_image_le
    _ = g * m := by simp

lemma grammar_occurs_in_table (g m : ℕ) (hm : 2 ≤ m)
    (words : Fin g → List Bool) (left right : Fin g → Fin g)
    (hgrammar : ∀ i : Fin g, (words i).length ≤ 1 ∨
      ((left i).val < i.val ∧ (right i).val < i.val ∧
        words i = words (left i) ++ words (right i)))
    (root : Fin g) (u : List Bool) (hu : u.length = m)
    (hocc : Occurs u (words root)) :
    u ∈ crossingTable g m words left right := by
  have key : ∀ n : ℕ, ∀ i : Fin g, i.val = n → ∀ v : List Bool,
      v.length = m → Occurs v (words i) →
        v ∈ crossingTable g m words left right := by
    intro n
    induction n using Nat.strong_induction_on with
    | ind n ih =>
      intro i hi v hv hvi
      rcases hgrammar i with hshort | ⟨hl, hr, heq⟩
      · have := occurs_length hvi
        omega
      · rw [heq] at hvi
        rcases occurs_append hvi with hleft | hright | ⟨k, hk, hcross⟩
        · exact ih (left i).val (by omega) (left i) rfl v hv hleft
        · exact ih (right i).val (by omega) (right i) rfl v hv hright
        · unfold crossingTable
          apply Finset.mem_image.mpr
          refine ⟨(i, ⟨k, by omega⟩), Finset.mem_univ _, ?_⟩
          simpa [hv] using hcross.symm
  exact key root.val root rfl u hu hocc

lemma grammar_all_binary_words_bound (g m : ℕ) (hm : 2 ≤ m)
    (words : Fin g → List Bool) (left right : Fin g → Fin g)
    (hgrammar : ∀ i : Fin g, (words i).length ≤ 1 ∨
      ((left i).val < i.val ∧ (right i).val < i.val ∧
        words i = words (left i) ++ words (right i)))
    (root : Fin g)
    (hall : ∀ u : List Bool, u.length = m → Occurs u (words root)) :
    2 ^ m ≤ g * m := by
  let allWords : Finset (List Bool) :=
    Finset.univ.image fun f : Fin m → Bool => List.ofFn f
  have hcard : allWords.card = 2 ^ m := by
    unfold allWords
    rw [Finset.card_image_of_injective _ List.ofFn_injective]
    simp
  have hsub : allWords ⊆ crossingTable g m words left right := by
    intro u hu
    obtain ⟨f, _, rfl⟩ := Finset.mem_image.mp hu
    apply grammar_occurs_in_table g m hm words left right hgrammar root
    · simp
    · apply hall
      simp
  rw [← hcard]
  exact (Finset.card_le_card hsub).trans (crossingTable_card g m words left right)

def binaryWords : ℕ → List (List Bool)
  | 0 => [[]]
  | m + 1 => (binaryWords m).map (false :: ·) ++ (binaryWords m).map (true :: ·)

lemma mem_binaryWords (m : ℕ) (u : List Bool) :
    u ∈ binaryWords m ↔ u.length = m := by
  induction m generalizing u with
  | zero => simp [binaryWords]
  | succ m ih =>
    cases u with
    | nil => simp [binaryWords]
    | cons b u => cases b <;> simp [binaryWords, ih]

lemma length_binaryWords (m : ℕ) : (binaryWords m).length = 2 ^ m := by
  induction m with
  | zero => simp [binaryWords]
  | succ m ih => simp [binaryWords, ih, pow_succ, Nat.mul_two]

lemma occurs_of_infix {u w : List Bool} (h : u <:+: w) : Occurs u w := by
  obtain ⟨p, q, rfl⟩ := h
  refine ⟨p.length, by simp, ?_⟩
  simp

lemma occurs_in_flatten {u : List Bool} {ws : List (List Bool)}
    (h : u ∈ ws) : Occurs u ws.flatten := by
  obtain ⟨p, q, rfl⟩ := List.mem_iff_append.mp h
  apply occurs_of_infix
  refine ⟨p.flatten, q.flatten, ?_⟩
  simp

lemma enumeration_contains_all (m : ℕ) (u : List Bool) (hu : u.length = m) :
    Occurs u (binaryWords m).flatten := by
  exact occurs_in_flatten ((mem_binaryWords m u).mpr hu)

lemma enumeration_length (m : ℕ) : (binaryWords m).flatten.length = m * 2 ^ m := by
  have hlen : ∀ ws : List (List Bool), (∀ u ∈ ws, u.length = m) →
      ws.flatten.length = ws.length * m := by
    intro ws
    induction ws with
    | nil => simp
    | cons u ws ih =>
      intro h
      have hu := h u (by simp)
      have ht := ih (fun v hv => h v (by simp [hv]))
      simp [hu, ht, Nat.add_mul, Nat.add_comm]
  rw [hlen (binaryWords m) (fun u hu => (mem_binaryWords m u).mp hu), length_binaryWords]
  exact Nat.mul_comm _ _

lemma enumeration_grammar_bound (g m : ℕ) (hm : 2 ≤ m)
    (words : Fin g → List Bool) (left right : Fin g → Fin g)
    (hgrammar : ∀ i : Fin g, (words i).length ≤ 1 ∨
      ((left i).val < i.val ∧ (right i).val < i.val ∧
        words i = words (left i) ++ words (right i)))
    (root : Fin g) (hroot : words root = (binaryWords m).flatten) :
    2 ^ m ≤ g * m := by
  apply grammar_all_binary_words_bound g m hm words left right hgrammar root
  intro u hu
  rw [hroot]
  exact enumeration_contains_all m u hu

end PEqualNP.Outside.FP3Strategy
