import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4970_aux.FeatureCover

def NoFour {p l : ℕ} (E : Finset (Fin p × Fin l)) : Prop :=
  ∀ a a' b b', a ≠ a' → b ≠ b' →
    ¬ ((a, b) ∈ E ∧ (a, b') ∈ E ∧ (a', b) ∈ E ∧ (a', b') ∈ E)

lemma feature_vertex {p l : ℕ} (E : Finset (Fin p × Fin l))
    (square_free : NoFour E) (Q : Finset (Fin p))
    (useful : ∃ a b, a ∈ Q ∧ ∀ a' ∈ Q, (a', b) ∈ E) :
    ∃ v : Fin (p + l), ∀ a b, a ∈ Q → (∀ a' ∈ Q, (a', b) ∈ E) →
      Fin.castAdd l a = v ∨ Fin.natAdd p b = v := by
  classical
  obtain ⟨a₀, b₀, ha₀, hb₀⟩ := useful
  by_cases singleton : ∀ a ∈ Q, a = a₀
  · refine ⟨Fin.castAdd l a₀, ?_⟩
    intro a b ha _
    exact Or.inl (congrArg (Fin.castAdd l) (singleton a ha))
  · push Not at singleton
    obtain ⟨a₁, ha₁, different⟩ := singleton
    refine ⟨Fin.natAdd p b₀, ?_⟩
    intro a b ha hb
    right
    have same : b = b₀ := by
      by_contra ne
      exact square_free a₀ a₁ b b₀ (Ne.symm different) ne
        ⟨hb a₀ ha₀, hb₀ a₀ ha₀, hb a₁ ha₁, hb₀ a₁ ha₁⟩
    exact congrArg (Fin.natAdd p) same

lemma point_features_cover {p l k : ℕ} (E : Finset (Fin p × Fin l))
    (square_free : NoFour E) (Q : Fin k → Finset (Fin p))
    (covers : ∀ a b, (a, b) ∈ E →
      ∃ i, a ∈ Q i ∧ ∀ a' ∈ Q i, (a', b) ∈ E) :
    ∃ S : Finset (Fin (p + l)), S.card ≤ k ∧
      ∀ a b, (a, b) ∈ E → Fin.castAdd l a ∈ S ∨ Fin.natAdd p b ∈ S := by
  classical
  let U : Finset (Fin k) := Finset.univ.filter fun i =>
    ∃ a b, a ∈ Q i ∧ ∀ a' ∈ Q i, (a', b) ∈ E
  have choose_vertex : ∀ i : {i // i ∈ U},
      ∃ v : Fin (p + l), ∀ a b, a ∈ Q i.val →
        (∀ a' ∈ Q i.val, (a', b) ∈ E) →
          Fin.castAdd l a = v ∨ Fin.natAdd p b = v := by
    intro i
    apply feature_vertex E square_free (Q i.val)
    exact (Finset.mem_filter.mp i.property).2
  choose vertex vertex_spec using choose_vertex
  let S : Finset (Fin (p + l)) := Finset.univ.image vertex
  refine ⟨S, ?_, ?_⟩
  · have small : S.card ≤ U.card := by
      simpa [S] using Finset.card_image_le (s := Finset.univ) (f := vertex)
    have bounded : U.card ≤ k := by
      calc
        U.card ≤ (Finset.univ : Finset (Fin k)).card := Finset.card_le_card (by
          intro i _
          exact Finset.mem_univ i)
        _ = k := by simp
    exact small.trans bounded
  · intro a b hab
    obtain ⟨i, hai, hbi⟩ := covers a b hab
    have hi : i ∈ U := Finset.mem_filter.mpr ⟨Finset.mem_univ i, ⟨a, b, hai, hbi⟩⟩
    have mem : vertex ⟨i, hi⟩ ∈ S := Finset.mem_image.mpr
      ⟨⟨i, hi⟩, Finset.mem_univ _, rfl⟩
    rcases vertex_spec ⟨i, hi⟩ a b hai hbi with h | h
    · exact Or.inl (h.symm ▸ mem)
    · exact Or.inr (h.symm ▸ mem)

def singleton {n : ℕ} (a : Fin n) : Fin n → Bool := fun i => decide (i = a)

def nonNeighbors {p l : ℕ} (E : Finset (Fin p × Fin l)) (b : Fin l) :
    Fin p → Bool := fun a => decide ((a, b) ∉ E)

def edgeFun {p l : ℕ} (E : Finset (Fin p × Fin l))
    (x : Fin p → Bool) (y : Fin l → Bool) : Bool :=
  decide (∃ a b, (a, b) ∈ E ∧ x a = true ∧ y b = true)

lemma edge_pair {p l : ℕ} (E : Finset (Fin p × Fin l))
    (a : Fin p) (b : Fin l) (edge : (a, b) ∈ E) :
    edgeFun E (singleton a) (singleton b) = true := by
  simp [edgeFun, singleton, edge]

lemma non_neighbors_false {p l : ℕ} (E : Finset (Fin p × Fin l)) (b : Fin l) :
    edgeFun E (nonNeighbors E b) (singleton b) = false := by
  simp [edgeFun, nonNeighbors, singleton]

lemma monotone_factor_separates {p l k : ℕ}
    (E : Finset (Fin p × Fin l))
    (features : Fin k → (Fin p → Bool) → Bool)
    (factor : (Fin k → Bool) → (Fin l → Bool) → Bool)
    (factor_mono : ∀ u v y, (∀ i, u i = true → v i = true) →
      factor u y = true → factor v y = true)
    (correct : ∀ x y, factor (fun i => features i x) y = edgeFun E x y)
    (a : Fin p) (b : Fin l) (edge : (a, b) ∈ E) :
    ∃ i, features i (singleton a) = true ∧
      features i (nonNeighbors E b) = false := by
  classical
  by_contra none
  have order : ∀ i, features i (singleton a) = true →
      features i (nonNeighbors E b) = true := by
    intro i hi
    cases h : features i (nonNeighbors E b)
    · exact False.elim (none ⟨i, hi, h⟩)
    · rfl
  have positive : factor (fun i => features i (singleton a)) (singleton b) = true := by
    rw [correct]
    exact edge_pair E a b edge
  have wrong := factor_mono _ _ (singleton b) order positive
  rw [correct, non_neighbors_false] at wrong
  cases wrong

lemma monotone_features_cover {p l k : ℕ}
    (E : Finset (Fin p × Fin l)) (square_free : NoFour E)
    (features : Fin k → (Fin p → Bool) → Bool)
    (feature_mono : ∀ i x y, (∀ a, x a = true → y a = true) →
      features i x = true → features i y = true)
    (separates : ∀ a b, (a, b) ∈ E →
      ∃ i, features i (singleton a) = true ∧
        features i (nonNeighbors E b) = false) :
    ∃ S : Finset (Fin (p + l)), S.card ≤ k ∧
      ∀ a b, (a, b) ∈ E → Fin.castAdd l a ∈ S ∨ Fin.natAdd p b ∈ S := by
  classical
  let Q : Fin k → Finset (Fin p) := fun i =>
    Finset.univ.filter fun a => features i (singleton a) = true
  apply point_features_cover E square_free Q
  intro a b edge
  obtain ⟨i, hi, hno⟩ := separates a b edge
  refine ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ a, hi⟩, ?_⟩
  intro a' ha'
  have accepted : features i (singleton a') = true := (Finset.mem_filter.mp ha').2
  by_contra nonedge
  have order : ∀ c, singleton a' c = true → nonNeighbors E b c = true := by
    intro c hc
    simp only [singleton, decide_eq_true_eq] at hc
    subst c
    simp [nonNeighbors, nonedge]
  have bad := feature_mono i _ _ order accepted
  rw [hno] at bad
  cases bad

lemma monotone_factor_cover {p l k : ℕ}
    (E : Finset (Fin p × Fin l)) (square_free : NoFour E)
    (features : Fin k → (Fin p → Bool) → Bool)
    (feature_mono : ∀ i x y, (∀ a, x a = true → y a = true) →
      features i x = true → features i y = true)
    (factor : (Fin k → Bool) → (Fin l → Bool) → Bool)
    (factor_mono : ∀ u v y, (∀ i, u i = true → v i = true) →
      factor u y = true → factor v y = true)
    (correct : ∀ x y, factor (fun i => features i x) y = edgeFun E x y) :
    ∃ S : Finset (Fin (p + l)), S.card ≤ k ∧
      ∀ a b, (a, b) ∈ E → Fin.castAdd l a ∈ S ∨ Fin.natAdd p b ∈ S := by
  apply monotone_features_cover E square_free features feature_mono
  intro a b edge
  exact monotone_factor_separates E features factor factor_mono correct a b edge

lemma frontier_count {α : Type*} [DecidableEq α]
    (boundary gates : Finset α) (output : α) (pins : List α)
    (separate : Disjoint boundary gates) (output_gate : output ∈ gates)
    (live : ∀ v ∈ boundary ∪ gates, v ≠ output → v ∈ pins)
    (arity : pins.length ≤ 2 * gates.card) : boundary.card ≤ gates.card + 1 := by
  have used : (boundary ∪ gates).erase output ⊆ pins.toFinset := by
    intro v hv
    obtain ⟨different, inside⟩ := Finset.mem_erase.mp hv
    exact List.mem_toFinset.mpr (live v inside different)
  have count := Finset.card_le_card used
  have output_mem : output ∈ boundary ∪ gates := Finset.mem_union_right boundary output_gate
  rw [Finset.card_erase_of_mem output_mem, Finset.card_union_of_disjoint separate] at count
  have distinct := List.toFinset_card_le pins
  have nonempty : 1 ≤ gates.card := Finset.one_le_card.mpr ⟨output, output_gate⟩
  omega

lemma balanced_cover {p l k₁ k₂ r : ℕ}
    (E : Finset (Fin p × Fin l))
    (left : ∃ S : Finset (Fin (p + l)), S.card ≤ k₁ ∧
      ∀ a b, (a, b) ∈ E → Fin.castAdd l a ∈ S ∨ Fin.natAdd p b ∈ S)
    (right : ∃ S : Finset (Fin (p + l)), S.card ≤ k₂ ∧
      ∀ a b, (a, b) ∈ E → Fin.castAdd l a ∈ S ∨ Fin.natAdd p b ∈ S)
    (budget : k₁ + k₂ ≤ r + 1) :
    ∃ S : Finset (Fin (p + l)), 2 * S.card ≤ r + 1 ∧
      ∀ a b, (a, b) ∈ E → Fin.castAdd l a ∈ S ∨ Fin.natAdd p b ∈ S := by
  obtain ⟨S₁, h₁, c₁⟩ := left
  obtain ⟨S₂, h₂, c₂⟩ := right
  by_cases h : S₁.card ≤ S₂.card
  · exact ⟨S₁, by omega, c₁⟩
  · exact ⟨S₂, by omega, c₂⟩

def transpose {p l : ℕ} (E : Finset (Fin p × Fin l)) : Finset (Fin l × Fin p) :=
  Finset.univ.filter fun e => (e.2, e.1) ∈ E

lemma transpose_mem {p l : ℕ} (E : Finset (Fin p × Fin l)) (a : Fin p) (b : Fin l) :
    (b, a) ∈ transpose E ↔ (a, b) ∈ E := by simp [transpose]

lemma transpose_no_four {p l : ℕ} (E : Finset (Fin p × Fin l))
    (square_free : NoFour E) : NoFour (transpose E) := by
  intro b b' a a' hb ha h
  simp only [transpose_mem] at h
  exact square_free a a' b b' ha hb ⟨h.1, h.2.2.1, h.2.1, h.2.2.2⟩

lemma transpose_edge_fun {p l : ℕ} (E : Finset (Fin p × Fin l))
    (x : Fin p → Bool) (y : Fin l → Bool) :
    edgeFun (transpose E) y x = edgeFun E x y := by
  unfold edgeFun
  congr 1
  apply propext
  constructor
  · rintro ⟨b, a, hab, hy, hx⟩
    exact ⟨a, b, (transpose_mem E a b).mp hab, hx, hy⟩
  · rintro ⟨a, b, hab, hx, hy⟩
    exact ⟨b, a, (transpose_mem E a b).mpr hab, hy, hx⟩

def swapVertex {p l : ℕ} : Fin (l + p) → Fin (p + l) :=
  Fin.addCases (fun b => Fin.natAdd p b) (fun a => Fin.castAdd l a)

lemma line_factor_cover {p l k : ℕ}
    (E : Finset (Fin p × Fin l)) (square_free : NoFour E)
    (features : Fin k → (Fin l → Bool) → Bool)
    (feature_mono : ∀ i x y, (∀ a, x a = true → y a = true) →
      features i x = true → features i y = true)
    (factor : (Fin p → Bool) → (Fin k → Bool) → Bool)
    (factor_mono : ∀ u v x, (∀ i, u i = true → v i = true) →
      factor x u = true → factor x v = true)
    (correct : ∀ x y, factor x (fun i => features i y) = edgeFun E x y) :
    ∃ S : Finset (Fin (p + l)), S.card ≤ k ∧
      ∀ a b, (a, b) ∈ E → Fin.castAdd l a ∈ S ∨ Fin.natAdd p b ∈ S := by
  have reversed : ∀ y x, factor x (fun i => features i y) =
      edgeFun (transpose E) y x := by
    intro y x
    rw [correct, transpose_edge_fun]
  obtain ⟨S, small, cover⟩ := monotone_factor_cover (transpose E)
    (transpose_no_four E square_free) features feature_mono
    (fun u x => factor x u) factor_mono reversed
  refine ⟨S.image swapVertex, (Finset.card_image_le).trans small, ?_⟩
  intro a b hab
  rcases cover b a ((transpose_mem E a b).mpr hab) with hb | ha
  · right
    have hm := Finset.mem_image_of_mem swapVertex hb
    simpa [swapVertex] using hm
  · left
    have hm := Finset.mem_image_of_mem swapVertex ha
    simpa [swapVertex] using hm

lemma two_sided_factor_cover {p l k₁ k₂ r : ℕ}
    (E : Finset (Fin p × Fin l)) (square_free : NoFour E)
    (points : Fin k₁ → (Fin p → Bool) → Bool)
    (lines : Fin k₂ → (Fin l → Bool) → Bool)
    (point_mono : ∀ i x y, (∀ a, x a = true → y a = true) →
      points i x = true → points i y = true)
    (line_mono : ∀ i x y, (∀ a, x a = true → y a = true) →
      lines i x = true → lines i y = true)
    (factor : (Fin k₁ → Bool) → (Fin k₂ → Bool) → Bool)
    (factor_left : ∀ u v y, (∀ i, u i = true → v i = true) →
      factor u y = true → factor v y = true)
    (factor_right : ∀ u v x, (∀ i, u i = true → v i = true) →
      factor x u = true → factor x v = true)
    (correct : ∀ x y,
      factor (fun i => points i x) (fun j => lines j y) = edgeFun E x y)
    (budget : k₁ + k₂ ≤ r + 1) :
    ∃ S : Finset (Fin (p + l)), 2 * S.card ≤ r + 1 ∧
      ∀ a b, (a, b) ∈ E → Fin.castAdd l a ∈ S ∨ Fin.natAdd p b ∈ S := by
  apply balanced_cover E (k₁ := k₁) (k₂ := k₂)
  · apply monotone_factor_cover E square_free points point_mono
      (fun u y => factor u (fun j => lines j y))
    · intro u v y huv h
      exact factor_left u v _ huv h
    · exact correct
  · apply line_factor_cover E square_free lines line_mono
      (fun x v => factor (fun i => points i x) v)
    · intro u v x huv h
      exact factor_right u v _ huv h
    · exact correct
  · exact budget

end PEqualNP.Outside.L_meta_4970_aux.FeatureCover
