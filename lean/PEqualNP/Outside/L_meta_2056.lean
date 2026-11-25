import PEqualNP.Defs

-- Supporting lemmas only; the posted existential statement remains unproved.

namespace PEqualNP.Outside.L_meta_2056

def singletonInput {α : Type*} [DecidableEq α] (u : α) : α → Bool :=
  fun w => decide (w = u)

def twoInput {α : Type*} [DecidableEq α] (u v : α) : α → Bool :=
  fun w => decide (w = u ∨ w = v)

def increasing {α : Type*} (f : (α → Bool) → Bool) : Prop :=
  ∀ x y, (∀ w, x w = true → y w = true) → f x = true → f y = true

def belowEdges {α : Type*} (G : SimpleGraph α) (f : (α → Bool) → Bool) : Prop :=
  ∀ x, f x = true → ∃ u v, G.Adj u v ∧ x u = true ∧ x v = true

def pairMinterm {α : Type*} [DecidableEq α] (f : (α → Bool) → Bool) (u v : α) : Prop :=
  f (twoInput u v) = true ∧ f (singletonInput u) = false ∧ f (singletonInput v) = false

lemma clean_and_singleton {α : Type*} [DecidableEq α] (G : SimpleGraph α)
    (f g : (α → Bool) → Bool) (hclean : belowEdges G (fun x => f x && g x)) (u : α) :
    ¬ (f (singletonInput u) = true ∧ g (singletonInput u) = true) := by
  rintro ⟨hf, hg⟩
  obtain ⟨a, b, hab, ha, hb⟩ := hclean (singletonInput u) (by simp [hf, hg])
  have ha' : a = u := by simpa [singletonInput] using ha
  have hb' : b = u := by simpa [singletonInput] using hb
  subst a
  subst b
  exact G.ne_of_adj hab rfl

lemma clean_and_cross {α : Type*} [DecidableEq α] (G : SimpleGraph α)
    (f g : (α → Bool) → Bool) (hf : increasing f) (hg : increasing g)
    (hclean : belowEdges G (fun x => f x && g x)) (u v : α)
    (hu : f (singletonInput u) = true) (hv : g (singletonInput v) = true) : G.Adj u v := by
  have hfu : f (twoInput u v) = true := by
    apply hf (singletonInput u) (twoInput u v) _ hu
    intro w hw
    simp only [singletonInput, decide_eq_true_eq] at hw
    simp [twoInput, hw]
  have hgv : g (twoInput u v) = true := by
    apply hg (singletonInput v) (twoInput u v) _ hv
    intro w hw
    simp only [singletonInput, decide_eq_true_eq] at hw
    simp [twoInput, hw]
  obtain ⟨a, b, hab, ha, hb⟩ := hclean (twoInput u v) (by simp [hfu, hgv])
  simp only [twoInput, decide_eq_true_eq] at ha hb
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
  · exact False.elim (G.ne_of_adj hab rfl)
  · exact hab
  · exact hab.symm
  · exact False.elim (G.ne_of_adj hab rfl)

lemma clean_and_pair_origin {α : Type*} [DecidableEq α] (G : SimpleGraph α)
    (f g : (α → Bool) → Bool) (hclean : belowEdges G (fun x => f x && g x)) (u v : α)
    (hpair : (f (twoInput u v) && g (twoInput u v)) = true) :
    (f (singletonInput u) = true ∧ g (singletonInput v) = true) ∨
    (f (singletonInput v) = true ∧ g (singletonInput u) = true) ∨
    pairMinterm f u v ∨ pairMinterm g u v := by
  have hu := clean_and_singleton G f g hclean u
  have hv := clean_and_singleton G f g hclean v
  have hf : f (twoInput u v) = true := (Bool.and_eq_true_iff.mp hpair).1
  have hg : g (twoInput u v) = true := (Bool.and_eq_true_iff.mp hpair).2
  cases hfu : f (singletonInput u) <;>
    cases hfv : f (singletonInput v) <;>
    cases hgu : g (singletonInput u) <;>
    cases hgv : g (singletonInput v) <;>
    simp_all [pairMinterm]

lemma rectangle_is_star {α : Type*} [DecidableEq α] (G : SimpleGraph α)
    (hfour : ∀ a b : α, a ≠ b → ∀ c d : α,
      G.Adj a c → G.Adj a d → G.Adj b c → G.Adj b d → c = d)
    (A B : Finset α) (hrect : ∀ a ∈ A, ∀ b ∈ B, G.Adj a b) :
    A.card ≤ 1 ∨ B.card ≤ 1 := by
  by_cases hA : A.card ≤ 1
  · exact Or.inl hA
  · right
    obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp (lt_of_not_ge hA)
    rw [Finset.card_le_one]
    intro c hc d hd
    exact hfour a b hab c d (hrect a ha c hc) (hrect a ha d hd)
      (hrect b hb c hc) (hrect b hb d hd)

lemma clean_and_singleton_star {α : Type*} [Fintype α] [DecidableEq α]
    (G : SimpleGraph α)
    (hfour : ∀ a b : α, a ≠ b → ∀ c d : α,
      G.Adj a c → G.Adj a d → G.Adj b c → G.Adj b d → c = d)
    (f g : (α → Bool) → Bool) (hf : increasing f) (hg : increasing g)
    (hclean : belowEdges G (fun x => f x && g x)) :
    (Finset.univ.filter fun u => f (singletonInput u) = true).card ≤ 1 ∨
    (Finset.univ.filter fun u => g (singletonInput u) = true).card ≤ 1 := by
  apply rectangle_is_star G hfour
  intro u hu v hv
  exact clean_and_cross G f g hf hg hclean u v (Finset.mem_filter.mp hu).2
    (Finset.mem_filter.mp hv).2

lemma shared_two_neighbors_center_eq {α : Type*} (G : SimpleGraph α)
    (hfour : ∀ a b : α, a ≠ b → ∀ c d : α,
      G.Adj a c → G.Adj a d → G.Adj b c → G.Adj b d → c = d)
    {a b c d : α} (hcd : c ≠ d)
    (hac : G.Adj a c) (had : G.Adj a d) (hbc : G.Adj b c) (hbd : G.Adj b d) : a = b := by
  by_contra hab
  exact hcd (hfour a b hab c d hac had hbc hbd)

lemma shared_or_support_single_center {α : Type*} [DecidableEq α] (G : SimpleGraph α)
    (hfour : ∀ a b : α, a ≠ b → ∀ c d : α,
      G.Adj a c → G.Adj a d → G.Adj b c → G.Adj b d → c = d)
    (centers leaves : Finset α) (hleaves : 1 < leaves.card)
    (hrect : ∀ a ∈ centers, ∀ b ∈ leaves, G.Adj a b) : centers.card ≤ 1 := by
  rcases rectangle_is_star G hfour centers leaves hrect with h | h
  · exact h
  · omega

lemma last_or_mask_false_of_neighbor_card
    {α : Type*} [Fintype α] [DecidableEq α]
    (G : SimpleGraph α) [DecidableRel G.Adj]
    (g : Finset α → Bool) (S U : Finset α)
    (mono : ∀ A B : Finset α, A ⊆ B → g A = true → g B = true)
    (computes : ∀ A : Finset α,
      (g A && decide (∃ v ∈ A, v ∈ S)) =
        decide (∃ u ∈ A, ∃ v ∈ A, G.Adj u v))
    (independent : ∀ u ∈ U, ∀ v ∈ U, ¬ G.Adj u v)
    (small : (Finset.univ.filter fun v => ∃ u ∈ U, G.Adj u v).card < S.card) :
    g U = false := by
  let N := Finset.univ.filter fun v => ∃ u ∈ U, G.Adj u v
  obtain ⟨v, hv, hvN⟩ : ∃ v ∈ S, v ∉ N := by
    by_contra! h
    have bound : S.card ≤ N.card := Finset.card_le_card h
    change N.card < S.card at small
    omega
  have outside : ∀ u ∈ U, ¬ G.Adj u v := by
    intro u hu hadj
    exact hvN (Finset.mem_filter.mpr ⟨Finset.mem_univ _, u, hu, hadj⟩)
  have enlarged : ∀ a ∈ insert v U, ∀ b ∈ insert v U, ¬ G.Adj a b := by
    intro a ha b hb
    simp only [Finset.mem_insert] at ha hb
    rcases ha with rfl | ha <;> rcases hb with rfl | hb
    · simp
    · exact fun h => outside b hb h.symm
    · exact outside a ha
    · exact independent a ha b hb
  cases hg : g U with
  | false => rfl
  | true =>
    have positive : g (insert v U) = true :=
      mono U (insert v U) (Finset.subset_insert v U) hg
    have mask : decide (∃ w ∈ insert v U, w ∈ S) = true := by
      simp only [decide_eq_true_eq]
      exact ⟨v, Finset.mem_insert_self _ _, hv⟩
    have absent : decide (∃ a ∈ insert v U, ∃ b ∈ insert v U, G.Adj a b) = false := by
      simp only [decide_eq_false_iff_not]
      rintro ⟨a, ha, b, hb, hab⟩
      exact enlarged a ha b hb hab
    have bad := computes (insert v U)
    rw [positive, mask, absent] at bad
    contradiction

lemma neighbor_union_card_le
    {α : Type*} [Fintype α] [DecidableEq α]
    (G : SimpleGraph α) [DecidableRel G.Adj] (d : ℕ)
    (degree : ∀ u, (Finset.univ.filter fun v => G.Adj u v).card ≤ d)
    (U : Finset α) :
    (Finset.univ.filter fun v => ∃ u ∈ U, G.Adj u v).card ≤ d * U.card := by
  induction U using Finset.induction_on with
  | empty => simp
  | @insert u U hu ih =>
    have separate : (Finset.univ.filter fun v => ∃ a ∈ insert u U, G.Adj a v) =
        (Finset.univ.filter fun v => G.Adj u v) ∪
          (Finset.univ.filter fun v => ∃ a ∈ U, G.Adj a v) := by
      ext v
      simp
    rw [separate]
    calc
      _ ≤ (Finset.univ.filter fun v => G.Adj u v).card +
          (Finset.univ.filter fun v => ∃ a ∈ U, G.Adj a v).card :=
        Finset.card_union_le _ _
      _ ≤ d + d * U.card := Nat.add_le_add (degree u) ih
      _ = d * (insert u U).card := by
        simp [Finset.card_insert_of_notMem hu, Nat.mul_add, Nat.add_comm]

lemma last_or_mask_false_of_degree_four
    {α : Type*} [Fintype α] [DecidableEq α]
    (G : SimpleGraph α) [DecidableRel G.Adj]
    (g : Finset α → Bool) (S U : Finset α)
    (degree : ∀ u, (Finset.univ.filter fun v => G.Adj u v).card ≤ 4)
    (large : 13 ≤ S.card) (few : U.card ≤ 3)
    (mono : ∀ A B : Finset α, A ⊆ B → g A = true → g B = true)
    (computes : ∀ A : Finset α,
      (g A && decide (∃ v ∈ A, v ∈ S)) =
        decide (∃ u ∈ A, ∃ v ∈ A, G.Adj u v))
    (independent : ∀ u ∈ U, ∀ v ∈ U, ¬ G.Adj u v) :
    g U = false := by
  apply last_or_mask_false_of_neighbor_card G g S U mono computes independent
  have bound := neighbor_union_card_le G 4 degree U
  omega

lemma last_or_mask_is_cover
    {α : Type*} [Fintype α] [DecidableEq α]
    (G : SimpleGraph α) [DecidableRel G.Adj]
    (g : Finset α → Bool) (S : Finset α)
    (computes : ∀ A : Finset α,
      (g A && decide (∃ v ∈ A, v ∈ S)) =
        decide (∃ u ∈ A, ∃ v ∈ A, G.Adj u v)) :
    ∀ u v, G.Adj u v → u ∈ S ∨ v ∈ S := by
  intro u v huv
  have hit : decide (∃ a ∈ ({u, v} : Finset α),
      ∃ b ∈ ({u, v} : Finset α), G.Adj a b) = true := by
    simp only [decide_eq_true_eq]
    exact ⟨u, by simp, v, by simp, huv⟩
  have mask : decide (∃ w ∈ ({u, v} : Finset α), w ∈ S) = true := by
    have eqn := computes {u, v}
    rw [hit] at eqn
    cases hg : g ({u, v} : Finset α) with
    | false => simp [hg] at eqn
    | true => simpa [hg] using eqn
  obtain ⟨w, hw, hs⟩ := of_decide_eq_true mask
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl
  · exact Or.inl hs
  · exact Or.inr hs

lemma last_or_mask_false_positive_dominates
    {α : Type*} [Fintype α] [DecidableEq α]
    (G : SimpleGraph α) [DecidableRel G.Adj]
    (g : Finset α → Bool) (S U : Finset α)
    (mono : ∀ A B : Finset α, A ⊆ B → g A = true → g B = true)
    (computes : ∀ A : Finset α,
      (g A && decide (∃ v ∈ A, v ∈ S)) =
        decide (∃ u ∈ A, ∃ v ∈ A, G.Adj u v))
    (independent : ∀ u ∈ U, ∀ v ∈ U, ¬ G.Adj u v)
    (accepted : g U = true) :
    (∀ u ∈ U, u ∉ S) ∧ (∀ s ∈ S, ∃ u ∈ U, G.Adj u s) := by
  constructor
  · intro u hu hs
    have mask : decide (∃ v ∈ U, v ∈ S) = true := by
      simp only [decide_eq_true_eq]
      exact ⟨u, hu, hs⟩
    have absent : decide (∃ a ∈ U, ∃ b ∈ U, G.Adj a b) = false := by
      simp only [decide_eq_false_iff_not]
      rintro ⟨a, ha, b, hb, hab⟩
      exact independent a ha b hb hab
    have bad := computes U
    rw [accepted, mask, absent] at bad
    contradiction
  · intro s hs
    have positive : g (insert s U) = true :=
      mono U (insert s U) (Finset.subset_insert s U) accepted
    have mask : decide (∃ v ∈ insert s U, v ∈ S) = true := by
      simp only [decide_eq_true_eq]
      exact ⟨s, Finset.mem_insert_self _ _, hs⟩
    have edge : ∃ a ∈ insert s U, ∃ b ∈ insert s U, G.Adj a b := by
      have eqn := computes (insert s U)
      rw [positive, mask] at eqn
      exact of_decide_eq_true eqn.symm
    obtain ⟨a, ha, b, hb, hab⟩ := edge
    simp only [Finset.mem_insert] at ha hb
    rcases ha with rfl | ha <;> rcases hb with rfl | hb
    · simp at hab
    · exact ⟨b, hb, hab.symm⟩
    · exact ⟨a, ha, hab⟩
    · exact (independent a ha b hb hab).elim

lemma maximal_independent_mask_identity
    {α : Type*} [Fintype α] [DecidableEq α]
    (G : SimpleGraph α) [DecidableRel G.Adj] (U A : Finset α)
    (independent : ∀ u ∈ U, ∀ v ∈ U, ¬ G.Adj u v)
    (maximal : ∀ v ∉ U, ∃ u ∈ U, G.Adj u v) :
    ((decide (∃ u ∈ A, ∃ v ∈ A, G.Adj u v) || decide (U ⊆ A)) &&
      decide (∃ v ∈ A, v ∉ U)) = decide (∃ u ∈ A, ∃ v ∈ A, G.Adj u v) := by
  by_cases he : ∃ u ∈ A, ∃ v ∈ A, G.Adj u v
  · have hm : ∃ v ∈ A, v ∉ U := by
      obtain ⟨u, hu, v, hv, huv⟩ := he
      by_cases huU : u ∈ U
      · exact ⟨v, hv, fun hvU => independent u huU v hvU huv⟩
      · exact ⟨u, hu, huU⟩
    simp [he, hm]
  · by_cases hsub : U ⊆ A
    · have hm : ¬ ∃ v ∈ A, v ∉ U := by
        rintro ⟨v, hv, hvU⟩
        obtain ⟨u, hu, huv⟩ := maximal v hvU
        exact he ⟨u, hsub hu, v, hv, huv⟩
      simp [he, hm]
    · simp [he, hsub]

abbrev planeGraph : SimpleGraph (Fin 26) :=
  SimpleGraph.fromRel fun u v => u.val < 13 ∧ 13 ≤ v.val ∧
    (u.val + v.val) % 13 ∈ ([0, 1, 3, 9] : List ℕ)

def pointWire (p : Fin 13) : Fin 26 := ⟨p.val, by omega⟩

def lineWire (l : Fin 13) : Fin 26 := ⟨13 + l.val, by omega⟩

lemma plane_degree_four :
    ∀ u : Fin 26, (Finset.univ.filter fun v => planeGraph.Adj u v).card = 4 := by
  decide +kernel

lemma plane_matching : ∀ p : Fin 13, planeGraph.Adj (pointWire p) (lineWire (-p)) := by
  decide +kernel

lemma plane_common_neighbors : ∀ a b : Fin 26, a ≠ b →
    (Finset.univ.filter fun v => planeGraph.Adj a v ∧ planeGraph.Adj b v).card ≤ 1 := by
  decide +kernel

lemma plane_four_cycle (a b : Fin 26) (hab : a ≠ b) (c d : Fin 26)
    (hac : planeGraph.Adj a c) (had : planeGraph.Adj a d)
    (hbc : planeGraph.Adj b c) (hbd : planeGraph.Adj b d) : c = d := by
  apply Finset.card_le_one.mp (plane_common_neighbors a b hab)
  · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hac, hbc⟩
  · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, had, hbd⟩

def mixedIndependent : Finset (Fin 26) := {0, 1, 2, 17, 18, 19, 23}

lemma mixedIndependent_independent :
    ∀ u ∈ mixedIndependent, ∀ v ∈ mixedIndependent, ¬ planeGraph.Adj u v := by
  decide +kernel

lemma mixedIndependent_maximal :
    ∀ v ∉ mixedIndependent, ∃ u ∈ mixedIndependent, planeGraph.Adj u v := by
  decide +kernel

lemma mixed_mask_identity (A : Finset (Fin 26)) :
    ((decide (∃ u ∈ A, ∃ v ∈ A, planeGraph.Adj u v) || decide (mixedIndependent ⊆ A)) &&
      decide (∃ v ∈ A, v ∉ mixedIndependent)) =
        decide (∃ u ∈ A, ∃ v ∈ A, planeGraph.Adj u v) := by
  have h := maximal_independent_mask_identity planeGraph mixedIndependent A
    mixedIndependent_independent mixedIndependent_maximal
  by_cases he : ∃ u ∈ A, ∃ v ∈ A, planeGraph.Adj u v <;>
    by_cases hu : mixedIndependent ⊆ A <;>
    by_cases hm : ∃ v ∈ A, v ∉ mixedIndependent <;>
    simpa only [he, hu, hm, decide_true, decide_false] using h

lemma pointWire_injective : Function.Injective pointWire := by
  intro p q h
  apply Fin.ext
  exact congrArg (fun r : Fin 26 => r.val) h

lemma lineWire_injective : Function.Injective lineWire := by
  intro p q h
  apply Fin.ext
  have hv := congrArg Fin.val h
  simp only [lineWire] at hv
  omega

lemma pointWire_ne_lineWire (p l : Fin 13) : pointWire p ≠ lineWire l := by
  intro h
  have hv := congrArg Fin.val h
  simp only [pointWire, lineWire] at hv
  omega

lemma plane_cover_card (S : Finset (Fin 26))
    (cover : ∀ u v, planeGraph.Adj u v → u ∈ S ∨ v ∈ S) : 13 ≤ S.card := by
  let pick : Fin 13 → Fin 26 := fun p => if pointWire p ∈ S then pointWire p else lineWire (-p)
  have hpick : ∀ p, pick p ∈ S := by
    intro p
    rcases cover _ _ (plane_matching p) with h | h
    · simp [pick, h]
    · simp only [pick]
      split
      · assumption
      · exact h
  have hinj : Function.Injective pick := by
    intro p q h
    dsimp only [pick] at h
    split_ifs at h with hp hq hq
    · exact pointWire_injective h
    · exact False.elim (pointWire_ne_lineWire _ _ h)
    · exact False.elim (pointWire_ne_lineWire _ _ h.symm)
    · exact neg_injective (lineWire_injective h)
  have hsub : Finset.univ.image pick ⊆ S := by
    intro v hv
    obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp hv
    exact hpick p
  have := Finset.card_le_card hsub
  rw [Finset.card_image_of_injective _ hinj] at this
  simpa using this

lemma plane_last_or_mask_rejects_small (g : Finset (Fin 26) → Bool)
    (S U : Finset (Fin 26))
    (mono : ∀ A B : Finset (Fin 26), A ⊆ B → g A = true → g B = true)
    (computes : ∀ A : Finset (Fin 26),
      (g A && decide (∃ v ∈ A, v ∈ S)) =
        decide (∃ u ∈ A, ∃ v ∈ A, planeGraph.Adj u v))
    (few : U.card ≤ 3)
    (independent : ∀ u ∈ U, ∀ v ∈ U, ¬ planeGraph.Adj u v) : g U = false := by
  apply last_or_mask_false_of_degree_four planeGraph g S U
  · intro u
    exact le_of_eq (plane_degree_four u)
  · apply plane_cover_card S
    apply last_or_mask_is_cover planeGraph g S
    intro A
    by_cases h : ∃ v ∈ A, v ∈ S <;>
      by_cases he : ∃ u ∈ A, ∃ v ∈ A, planeGraph.Adj u v <;>
      simpa only [h, he, decide_true, decide_false] using computes A
  · exact few
  · exact mono
  · intro A
    by_cases h : ∃ v ∈ A, v ∈ S <;>
      by_cases he : ∃ u ∈ A, ∃ v ∈ A, planeGraph.Adj u v <;>
      simpa only [h, he, decide_true, decide_false] using computes A
  · exact independent

lemma plane_clean_and_singleton_star (f g : (Fin 26 → Bool) → Bool)
    (hf : increasing f) (hg : increasing g)
    (hclean : belowEdges planeGraph (fun x => f x && g x)) :
    (Finset.univ.filter fun u => f (singletonInput u) = true).card ≤ 1 ∨
    (Finset.univ.filter fun u => g (singletonInput u) = true).card ≤ 1 :=
  clean_and_singleton_star planeGraph plane_four_cycle f g hf hg hclean

set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
set_option synthInstance.maxSize 100000 in
lemma four_line_cover_is_pencil :
    ∀ a b c d : Fin 13, a < b → b < c → c < d →
      (∀ p : Fin 13,
        (p.val + a.val) % 13 ∈ ([0, 1, 3, 9] : List ℕ) ∨
        (p.val + b.val) % 13 ∈ ([0, 1, 3, 9] : List ℕ) ∨
        (p.val + c.val) % 13 ∈ ([0, 1, 3, 9] : List ℕ) ∨
        (p.val + d.val) % 13 ∈ ([0, 1, 3, 9] : List ℕ)) →
      ∃ p : Fin 13,
        (p.val + a.val) % 13 ∈ ([0, 1, 3, 9] : List ℕ) ∧
        (p.val + b.val) % 13 ∈ ([0, 1, 3, 9] : List ℕ) ∧
        (p.val + c.val) % 13 ∈ ([0, 1, 3, 9] : List ℕ) ∧
        (p.val + d.val) % 13 ∈ ([0, 1, 3, 9] : List ℕ) := by
  decide +kernel

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def maskedPath : Circuit :=
  ⟨[⟨GateOp.or, [0, 2]⟩, ⟨GateOp.or, [1, 3]⟩,
    ⟨GateOp.and, [4, 5]⟩, ⟨GateOp.or, [1, 2]⟩,
    ⟨GateOp.and, [6, 7]⟩], 8⟩

lemma maskedPath_monotone : Monotone2 maskedPath := by
  simp [Monotone2, maskedPath]

lemma maskedPath_size : maskedPath.size = 5 := rfl

lemma maskedPath_eval (a b c d : Bool) :
    maskedPath.eval [a, b, c, d] = ((a && b) || (b && c) || (c && d)) := by
  cases a <;> cases b <;> cases c <;> cases d <;> rfl

lemma maskedPath_shadow :
    (maskedPath.wires [true, false, false, true]).getD 6 false = true ∧
    (maskedPath.wires [true, false, false, false]).getD 6 false = false ∧
    (maskedPath.wires [false, false, false, true]).getD 6 false = false ∧
    maskedPath.eval [true, false, false, true] = false := by
  decide +kernel

end PEqualNP.Outside.L_meta_2056

namespace PEqualNP.Outside.L_meta_2056.OrCompile

open PEqualNP.CircuitLowerBounds

def meet {α : Type*} (a : List (α → Bool)) (x : α) : Bool :=
  a.all fun k => k x

def good {α : Type*} (D V : List (α → Bool)) : Prop :=
  ∀ i : Fin V.length, ∃ a b : List (α → Bool),
    (∀ k ∈ a ++ b, k ∈ ((fun _ => false) :: D) ++ V.take i.val) ∧
    V.get i = fun x => meet a x || meet b x

def available {α : Type*} (D V : List (α → Bool))
    (W : List (List (α → Bool))) : Prop :=
  ∀ a ∈ W, ∀ k ∈ a, k ∈ ((fun _ => false) :: D) ++ V

def orBit (g : Gate) : Bool :=
  match g.op with
  | .or => true
  | _ => false

lemma rep_eval {α : Type*} (W : List (List (α → Bool))) (i : ℕ) (x : α) :
    meet (W.getD i [fun _ => false]) x =
      (W.map fun a => meet a x).getD i false := by
  simpa [meet] using
    (List.getD_map W [fun _ => false] (fun a => meet a x) (n := i)).symm

lemma rep_available {α : Type*} {D V : List (α → Bool)}
    {W : List (List (α → Bool))} (h : available D V W) (i : ℕ) :
    ∀ k ∈ W.getD i [fun _ => false], k ∈ ((fun _ => false) :: D) ++ V := by
  intro k hk
  by_cases hi : i < W.length
  · rw [List.getD_eq_getElem W _ hi] at hk
    exact h _ (List.getElem_mem hi) k hk
  · rw [List.getD_eq_default W _ (by omega)] at hk
    simp only [List.mem_singleton] at hk
    subst k
    simp

lemma good_append {α : Type*} {D V : List (α → Bool)}
    (h : good D V) (a b : List (α → Bool))
    (hab : ∀ k ∈ a ++ b, k ∈ ((fun _ => false) :: D) ++ V) :
    good D (V ++ [fun x => meet a x || meet b x]) := by
  intro i
  by_cases hi : i.val < V.length
  · obtain ⟨c, d, hcd, heq⟩ := h ⟨i.val, hi⟩
    refine ⟨c, d, ?_, ?_⟩
    · simpa [List.take_append_of_le_length (Nat.le_of_lt hi)] using hcd
    · change (V ++ [fun x => meet a x || meet b x])[i.val] = _
      rw [List.getElem_append_left hi]
      exact heq
  · have hi' : i.val = V.length := by have := i.isLt; simp only [List.length_append, List.length_singleton] at this; omega
    refine ⟨a, b, ?_, ?_⟩
    · simpa [hi'] using hab
    · change (V ++ [fun x => meet a x || meet b x])[i.val] = _
      simp [hi']

lemma available_append {α : Type*} {D V : List (α → Bool)}
    {W : List (List (α → Bool))} (h : available D V W) (f : α → Bool) :
    available D (V ++ [f]) W := by
  intro a ha k hk
  have := h a ha k hk
  rcases List.mem_append.mp this with hb | hv
  · exact List.mem_append.mpr (Or.inl hb)
  · exact List.mem_append.mpr (Or.inr (List.mem_append.mpr (Or.inl hv)))

lemma or_arms {α : Type*} {D V : List (α → Bool)}
    {W : List (List (α → Bool))} (h : available D V W)
    (inputs : List ℕ) (hlen : inputs.length ≤ 2) :
    ∃ a b : List (α → Bool),
      (∀ k ∈ a ++ b, k ∈ ((fun _ => false) :: D) ++ V) ∧
      ∀ x, (meet a x || meet b x) =
        GateOp.or.eval (inputs.map fun i => (W.map fun a => meet a x).getD i false) := by
  cases inputs with
  | nil =>
    refine ⟨[fun _ => false], [fun _ => false], ?_, ?_⟩
    · intro k hk
      simp only [List.mem_append, List.mem_singleton, or_self] at hk
      subst k
      simp
    · intro x
      rfl
  | cons i inputs =>
    cases inputs with
    | nil =>
      refine ⟨W.getD i [fun _ => false], [fun _ => false], ?_, ?_⟩
      · intro k hk
        rcases List.mem_append.mp hk with hk | hk
        · exact rep_available h i k hk
        · simp only [List.mem_singleton] at hk
          subst k
          simp
      · intro x
        change (meet (W.getD i [fun _ => false]) x || false) =
          ((W.map fun a => meet a x).getD i false || false)
        rw [rep_eval]
    | cons j inputs =>
      cases inputs with
      | nil =>
        refine ⟨W.getD i [fun _ => false], W.getD j [fun _ => false], ?_, ?_⟩
        · intro k hk
          rcases List.mem_append.mp hk with hk | hk
          · exact rep_available h i k hk
          · exact rep_available h j k hk
        · intro x
          change (meet (W.getD i [fun _ => false]) x ||
              meet (W.getD j [fun _ => false]) x) =
            ((W.map fun a => meet a x).getD i false ||
              ((W.map fun a => meet a x).getD j false || false))
          simp only [Bool.or_false, rep_eval]
      | cons l inputs => simp at hlen

set_option maxHeartbeats 1000000 in
lemma compile_step {α : Type*} (D V : List (α → Bool))
    (W : List (List (α → Bool))) (g : Gate)
    (hgood : good D V) (havail : available D V W)
    (hop : g.op = .and ∨ g.op = .or) (hlen : g.inputs.length ≤ 2) :
    ∃ V' W', good D V' ∧ available D V' W' ∧
      V'.length = V.length + (if orBit g then 1 else 0) ∧
      ∀ x, (W'.map fun a => meet a x) =
        (W.map fun a => meet a x) ++
          [g.op.eval (g.inputs.map fun i => (W.map fun a => meet a x).getD i false)] := by
  rcases hop with hand | hor
  · let a := (g.inputs.map fun i => W.getD i [fun _ => false]).flatten
    refine ⟨V, W ++ [a], hgood, ?_, ?_, ?_⟩
    · intro b hb k hk
      rcases List.mem_append.mp hb with hb | hb
      · exact havail b hb k hk
      · simp only [List.mem_singleton] at hb
        subst b
        obtain ⟨c, hc, hk⟩ := List.mem_flatten.mp hk
        obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hc
        exact rep_available havail i k hk
    · simp [orBit, hand]
    · intro x
      simp only [List.map_append, List.map_singleton]
      congr 2
      rw [hand]
      change a.all (fun k => k x) =
        (g.inputs.map fun i => (W.map fun a => meet a x).getD i false).all id
      simp only [a, List.all_flatten, List.all_map]
      congr 1
      funext i
      exact rep_eval W i x
  · obtain ⟨a, b, hab, heval⟩ := or_arms havail g.inputs hlen
    let f : α → Bool := fun x => meet a x || meet b x
    refine ⟨V ++ [f], W ++ [[f]], good_append hgood a b hab, ?_, ?_, ?_⟩
    · intro c hc k hk
      rcases List.mem_append.mp hc with hc | hc
      · exact available_append havail f c hc k hk
      · simp only [List.mem_singleton] at hc
        subst c
        simp only [List.mem_singleton] at hk
        subst k
        simp
    · simp [orBit, hor]
    · intro x
      simp only [List.map_append, List.map_singleton]
      congr 2
      simpa [meet, f, hor] using heval x

set_option maxHeartbeats 1000000 in
lemma compile_aux {α : Type*} (D : List (α → Bool)) (gs : List Gate)
    (hm : ∀ g ∈ gs, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2)
    (V : List (α → Bool)) (W : List (List (α → Bool)))
    (hgood : good D V) (havail : available D V W) :
    ∃ V' W', good D V' ∧ available D V' W' ∧
      V'.length = V.length + gs.countP orBit ∧
      ∀ x, (W'.map fun a => meet a x) =
        gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
          (W.map fun a => meet a x) := by
  induction gs generalizing V W with
  | nil => exact ⟨V, W, hgood, havail, by simp, fun _ => rfl⟩
  | cons g gs ih =>
    obtain ⟨V₁, W₁, hg₁, ha₁, hc₁, he₁⟩ :=
      compile_step D V W g hgood havail (hm g (by simp)).1 (hm g (by simp)).2
    obtain ⟨V₂, W₂, hg₂, ha₂, hc₂, he₂⟩ :=
      ih (fun h hh => hm h (by simp [hh])) V₁ W₁ hg₁ ha₁
    refine ⟨V₂, W₂, hg₂, ha₂, ?_, ?_⟩
    · rw [hc₂, hc₁]
      simp only [List.countP_cons]
      split <;> omega
    · intro x
      rw [he₂, he₁]
      rfl

lemma countP_ncard {β : Type*} (l : List β) (p : β → Bool) :
    l.countP p = {i : Fin l.length | p (l.get i) = true}.ncard := by
  classical
  have hrange : (List.finRange l.length).toFinset = Finset.univ := by
    ext i
    simp
  have hc := (List.nodup_finRange l.length).card_eq_countP
    (P := fun i => p (l.get i) = true)
  rw [hrange] at hc
  calc
    l.countP p = ((List.finRange l.length).map l.get).countP p := by
      rw [← List.ofFn_eq_map, List.ofFn_get]
    _ = (List.finRange l.length).countP (fun i => p (l.get i)) := by
      rw [List.countP_map]
      rfl
    _ = (Finset.univ.filter fun i => p (l.get i) = true).card := by
      simpa using hc.symm
    _ = {i : Fin l.length | p (l.get i) = true}.ncard := by
      rw [← Set.ncard_coe_finset]
      congr 1
      ext i
      simp

lemma or_count_ncard (gs : List Gate) :
    gs.countP orBit = {i : Fin gs.length | (gs.get i).op = GateOp.or}.ncard := by
  rw [countP_ncard]
  congr 1
  ext i
  change orBit (gs.get i) = true ↔ (gs.get i).op = GateOp.or
  cases h : (gs.get i).op <;> simp only [orBit, h] <;> simp

set_option maxHeartbeats 1000000 in
lemma compile {α : Type*} (D : List (α → Bool)) (C : Circuit)
    (hm : PEqualNP.MetaComplexity.Monotone2 C) :
    ∃ V o : List (α → Bool),
      (∀ i : Fin V.length, ∃ a b : List (α → Bool),
        (∀ k ∈ a ++ b, k ∈ ((fun _ => false) :: D) ++ V.take i.val) ∧
        V.get i = fun x => meet a x || meet b x) ∧
      V.length = {i : Fin C.gates.length | (C.gates.get i).op = GateOp.or}.ncard ∧
      (∀ k ∈ o, k ∈ ((fun _ => false) :: D) ++ V) ∧
      ∀ x, meet o x = C.eval (D.map fun k => k x) := by
  have hg : good D [] := by intro i; exact Fin.elim0 i
  have ha : available D [] (D.map fun k => [k]) := by
    intro a ha k hk
    obtain ⟨f, hf, rfl⟩ := List.mem_map.mp ha
    simp only [List.mem_singleton] at hk
    subst k
    simp [hf]
  have hmono : ∀ g ∈ C.gates, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2 := by
    intro g hg
    simpa using hm g hg
  obtain ⟨V, W, hv, hw, hcount, heval⟩ :=
    compile_aux D C.gates hmono [] (D.map fun k => [k]) hg ha
  refine ⟨V, W.getD C.output [fun _ => false], hv, ?_, rep_available hw C.output, ?_⟩
  · simpa only [List.length_nil, Nat.zero_add, or_count_ncard] using hcount
  · intro x
    rw [rep_eval, heval]
    have hinit : ((D.map fun k => [k]).map fun a => meet a x) = D.map fun k => k x := by
      simp [List.map_map, meet]
    rw [hinit]
    rfl

end PEqualNP.Outside.L_meta_2056.OrCompile

namespace PEqualNP.Outside.L_meta_2056

lemma neighborhood_cover_mask_identity
    {α : Type*} [Fintype α] [DecidableEq α]
    (G : SimpleGraph α) [DecidableRel G.Adj] (U : Finset α)
    (cover : ∀ a b, G.Adj a b →
      (∃ u ∈ U, G.Adj u a) ∨ (∃ u ∈ U, G.Adj u b))
    (A : Finset α) :
    ((decide (∃ a ∈ A, ∃ b ∈ A, G.Adj a b) || decide (U ⊆ A)) &&
      decide (∃ v ∈ A, ∃ u ∈ U, G.Adj u v)) =
        decide (∃ a ∈ A, ∃ b ∈ A, G.Adj a b) := by
  by_cases edge : ∃ a ∈ A, ∃ b ∈ A, G.Adj a b
  · have hit : ∃ v ∈ A, ∃ u ∈ U, G.Adj u v := by
      obtain ⟨a, ha, b, hb, hab⟩ := edge
      rcases cover a b hab with h | h
      · exact ⟨a, ha, h⟩
      · exact ⟨b, hb, h⟩
    simp [edge, hit]
  · by_cases subset : U ⊆ A
    · have miss : ¬ ∃ v ∈ A, ∃ u ∈ U, G.Adj u v := by
        rintro ⟨v, hv, u, hu, huv⟩
        exact edge ⟨u, subset hu, v, hv, huv⟩
      simp [edge, miss]
    · simp [edge, subset]

end PEqualNP.Outside.L_meta_2056

namespace PEqualNP.Outside.L_meta_2056

namespace OrSaturation

def conjunction {α : Type*} (atoms : List (α → Bool)) (x : α) : Bool :=
  atoms.all fun f => f x

noncomputable def saturate {α : Type*} (positives : Finset α)
    (available atoms : List (α → Bool)) : List (α → Bool) := by
  classical
  exact available.filter fun f => ∀ x ∈ positives, conjunction atoms x = true → f x = true

lemma saturate_implies {α : Type*} (positives : Finset α)
    (available atoms : List (α → Bool))
    (members : ∀ f ∈ atoms, f ∈ available) (x : α)
    (h : conjunction (saturate positives available atoms) x = true) :
    conjunction atoms x = true := by
  classical
  simp only [conjunction, List.all_eq_true] at h ⊢
  intro f hf
  apply h f
  simp only [saturate, List.mem_filter, decide_eq_true_eq]
  refine ⟨members f hf, ?_⟩
  intro y _ hy
  exact List.all_eq_true.mp hy f hf

lemma saturate_eq_on_positives {α : Type*} (positives : Finset α)
    (available atoms : List (α → Bool))
    (members : ∀ f ∈ atoms, f ∈ available) (x : α) (hx : x ∈ positives) :
    conjunction (saturate positives available atoms) x = conjunction atoms x := by
  classical
  cases old : conjunction atoms x with
  | false =>
    cases new : conjunction (saturate positives available atoms) x with
    | false => rfl
    | true =>
      have := saturate_implies positives available atoms members x new
      simp [old] at this
  | true =>
    apply List.all_eq_true.mpr
    intro f hf
    simp only [saturate, List.mem_filter, decide_eq_true_eq] at hf
    exact hf.2 x hx old

end OrSaturation
end PEqualNP.Outside.L_meta_2056

namespace PEqualNP.Outside.L_meta_2056

lemma last_or_mask_false_positive_neighborhood_cover
    {α : Type*} [Fintype α] [DecidableEq α]
    (G : SimpleGraph α) [DecidableRel G.Adj]
    (g : Finset α → Bool) (S U : Finset α)
    (mono : ∀ A B : Finset α, A ⊆ B → g A = true → g B = true)
    (computes : ∀ A : Finset α,
      (g A && decide (∃ v ∈ A, v ∈ S)) =
        decide (∃ u ∈ A, ∃ v ∈ A, G.Adj u v))
    (independent : ∀ u ∈ U, ∀ v ∈ U, ¬ G.Adj u v)
    (accepted : g U = true) :
    ∀ a b, G.Adj a b →
      (∃ u ∈ U, G.Adj u a) ∨ (∃ u ∈ U, G.Adj u b) := by
  have hdom := (last_or_mask_false_positive_dominates G g S U mono computes independent accepted).2
  intro a b hab
  rcases last_or_mask_is_cover G g S computes a b hab with ha | hb
  · exact Or.inl (hdom a ha)
  · exact Or.inr (hdom b hb)

end PEqualNP.Outside.L_meta_2056

namespace PEqualNP.Outside.L_meta_2056

lemma finset_monotone_cover {α : Type*} [LinearOrder α]
    (A : Finset α) (hne : A.Nonempty) (n : ℕ) (hn : A.card ≤ n) :
    ∃ f : Fin n → α, Monotone f ∧ (∀ i, f i ∈ A) ∧
      (∀ a ∈ A, ∃ i, f i = a) := by
  have hpos : 0 < A.card := Finset.card_pos.mpr hne
  let clamp : Fin n → Fin A.card :=
    fun i => ⟨min i.val (A.card - 1), by omega⟩
  let f : Fin n → α := fun i => A.orderEmbOfFin rfl (clamp i)
  refine ⟨f, ?_, ?_, ?_⟩
  · intro i j hij
    apply (A.orderEmbOfFin rfl).monotone
    change min i.val (A.card - 1) ≤ min j.val (A.card - 1)
    have hval : i.val ≤ j.val := hij
    omega
  · intro i
    exact A.orderEmbOfFin_mem rfl (clamp i)
  · intro a ha
    have hr : a ∈ Set.range (A.orderEmbOfFin rfl) := by
      rw [Finset.range_orderEmbOfFin]
      exact ha
    obtain ⟨j, hj⟩ := hr
    let i : Fin n := ⟨j.val, by omega⟩
    refine ⟨i, ?_⟩
    have hc : clamp i = j := by
      apply Fin.ext
      change min j.val (A.card - 1) = j.val
      omega
    simpa only [f, hc] using hj



abbrev mixedNear (a b : Fin 13) : Prop :=
  (a.val + b.val) % 13 ∈ ([0, 1, 3, 9] : List ℕ)

def mixedOff (B : Finset (Fin 13)) : Finset (Fin 13) :=
  Finset.univ.filter fun p => ∀ b ∈ B, ¬ mixedNear p b

lemma mixed_near_symm (a b : Fin 13) : mixedNear a b ↔ mixedNear b a := by
  simp only [mixedNear, Nat.add_comm]

lemma mixed_near_degree : ∀ p : Fin 13,
    (Finset.univ.filter fun l => mixedNear p l).card = 4 := by
  decide +kernel

lemma mixed_near_common : ∀ p q : Fin 13, p ≠ q →
    (Finset.univ.filter fun l => mixedNear p l ∧ mixedNear q l).card ≤ 1 := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 64000000 in
set_option synthInstance.maxSize 1000000 in
lemma mixed_off_three : ∀ a b c : Fin 13, a < b → b < c →
    3 ≤ (mixedOff {a, b, c}).card := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 64000000 in
set_option synthInstance.maxSize 1000000 in
lemma mixed_off_four_ne_one : ∀ a b c d : Fin 13, a < b → b < c → c < d →
    (mixedOff {a, b, c, d}).card ≠ 1 := by
  decide +kernel

lemma mixed_neighbor_avoids_small (A : Finset (Fin 13)) (hA : A.card ≤ 3)
    (p : Fin 13) (hp : p ∉ A) :
    ∃ l : Fin 13, mixedNear p l ∧ ∀ a ∈ A, ¬ mixedNear a l := by
  have bound : ∀ T : Finset (Fin 13), p ∉ T →
      (Finset.univ.filter fun l => mixedNear p l ∧ ∃ a ∈ T, mixedNear a l).card ≤ T.card := by
    intro T
    induction T using Finset.induction_on with
    | empty => simp
    | @insert a T ha ih =>
      intro hpT
      have hpa : p ≠ a := fun h => hpT (Finset.mem_insert.mpr (Or.inl h))
      have hpT' : p ∉ T := fun h => hpT (Finset.mem_insert.mpr (Or.inr h))
      have sep : (Finset.univ.filter fun l => mixedNear p l ∧ ∃ b ∈ insert a T, mixedNear b l) =
          (Finset.univ.filter fun l => mixedNear p l ∧ mixedNear a l) ∪
            (Finset.univ.filter fun l => mixedNear p l ∧ ∃ b ∈ T, mixedNear b l) := by
        ext l
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
          exists_eq_or_imp, Finset.mem_union]
        tauto
      rw [sep]
      have hc := mixed_near_common p a hpa
      have hu := Finset.card_union_le
        (Finset.univ.filter fun l => mixedNear p l ∧ mixedNear a l)
        (Finset.univ.filter fun l => mixedNear p l ∧ ∃ b ∈ T, mixedNear b l)
      have hi := ih hpT'
      rw [Finset.card_insert_of_notMem ha]
      omega
  let N := Finset.univ.filter fun l => mixedNear p l
  let bad := Finset.univ.filter fun l => mixedNear p l ∧ ∃ a ∈ A, mixedNear a l
  have hbad : bad.card ≤ 3 := (bound A hp).trans hA
  have hN : N.card = 4 := mixed_near_degree p
  obtain ⟨l, hl, hlbad⟩ : ∃ l ∈ N, l ∉ bad := by
    by_contra! h
    have hc := Finset.card_le_card h
    omega
  refine ⟨l, (Finset.mem_filter.mp hl).2, ?_⟩
  intro a ha hal
  exact hlbad (Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hl).2, a, ha, hal⟩)

lemma mixed_missing_edge_of_off_large (A B : Finset (Fin 13))
    (hA : A.card ≤ 3) (hoff : A.card < (mixedOff B).card) :
    ∃ p l : Fin 13, mixedNear p l ∧
      (∀ a ∈ A, ¬ mixedNear a l) ∧ (∀ b ∈ B, ¬ mixedNear p b) := by
  obtain ⟨p, hp, hpA⟩ : ∃ p ∈ mixedOff B, p ∉ A := by
    by_contra! h
    have hc := Finset.card_le_card h
    omega
  obtain ⟨l, hpl, hl⟩ := mixed_neighbor_avoids_small A hA p hpA
  exact ⟨p, l, hpl, hl, (Finset.mem_filter.mp hp).2⟩



lemma mixed_off_two : ∀ a b : Fin 13, 5 ≤ (mixedOff {a, b}).card := by
  decide +kernel

lemma mixed_off_three_small (B : Finset (Fin 13)) (hne : B.Nonempty) (hB : B.card ≤ 3) :
    3 ≤ (mixedOff B).card := by
  by_cases hsmall : B.card ≤ 2
  · obtain ⟨f, _, hmem, hcover⟩ := finset_monotone_cover B hne 2 hsmall
    have heq : B = {f 0, f 1} := by
      ext b
      constructor
      · intro hb
        obtain ⟨i, rfl⟩ := hcover b hb
        fin_cases i <;> simp
      · intro hb
        simp only [Finset.mem_insert, Finset.mem_singleton] at hb
        rcases hb with rfl | rfl
        · exact hmem 0
        · exact hmem 1
    rw [heq]
    exact (by omega : 3 ≤ 5).trans (mixed_off_two _ _)
  have hcard : B.card = 3 := by omega
  let f := B.orderEmbOfFin hcard
  have heq : B = {f 0, f 1, f 2} := by
    ext b
    constructor
    · intro hb
      have hr : b ∈ Set.range f := by
        rw [Finset.range_orderEmbOfFin]
        exact hb
      obtain ⟨i, rfl⟩ := hr
      fin_cases i <;> simp
    · intro hb
      simp only [Finset.mem_insert, Finset.mem_singleton] at hb
      rcases hb with rfl | rfl | rfl
      · exact B.orderEmbOfFin_mem hcard 0
      · exact B.orderEmbOfFin_mem hcard 1
      · exact B.orderEmbOfFin_mem hcard 2
  rw [heq]
  exact mixed_off_three _ _ _ (f.strictMono (by decide)) (f.strictMono (by decide))

lemma mixed_off_four_small_ne_one (B : Finset (Fin 13)) (hne : B.Nonempty) (hB : B.card ≤ 4) :
    (mixedOff B).card ≠ 1 := by
  by_cases hsmall : B.card ≤ 3
  · have h := mixed_off_three_small B hne hsmall
    omega
  have hcard : B.card = 4 := by omega
  let f := B.orderEmbOfFin hcard
  have heq : B = {f 0, f 1, f 2, f 3} := by
    ext b
    constructor
    · intro hb
      have hr : b ∈ Set.range f := by
        rw [Finset.range_orderEmbOfFin]
        exact hb
      obtain ⟨i, rfl⟩ := hr
      fin_cases i <;> simp
    · intro hb
      simp only [Finset.mem_insert, Finset.mem_singleton] at hb
      rcases hb with rfl | rfl | rfl | rfl
      · exact B.orderEmbOfFin_mem hcard 0
      · exact B.orderEmbOfFin_mem hcard 1
      · exact B.orderEmbOfFin_mem hcard 2
      · exact B.orderEmbOfFin_mem hcard 3
  rw [heq]
  exact mixed_off_four_ne_one _ _ _ _ (f.strictMono (by decide))
    (f.strictMono (by decide)) (f.strictMono (by decide))

lemma mixed_missing_edge_two_three (A B : Finset (Fin 13))
    (hBne : B.Nonempty) (hA : A.card ≤ 2) (hB : B.card ≤ 3) :
    ∃ p l : Fin 13, mixedNear p l ∧
      (∀ a ∈ A, ¬ mixedNear a l) ∧ (∀ b ∈ B, ¬ mixedNear p b) := by
  apply mixed_missing_edge_of_off_large A B (by omega)
  have hc := mixed_off_three_small B hBne hB
  omega

lemma mixed_missing_edge_one_four (A B : Finset (Fin 13))
    (hAne : A.Nonempty) (hBne : B.Nonempty) (hA : A.card ≤ 1) (hB : B.card ≤ 4)
    (hind : ∀ a ∈ A, ∀ b ∈ B, ¬ mixedNear a b) :
    ∃ p l : Fin 13, mixedNear p l ∧
      (∀ a ∈ A, ¬ mixedNear a l) ∧ (∀ b ∈ B, ¬ mixedNear p b) := by
  apply mixed_missing_edge_of_off_large A B (by omega)
  have hne := mixed_off_four_small_ne_one B hBne hB
  obtain ⟨a, ha⟩ := hAne
  have hpos : 0 < (mixedOff B).card := by
    apply Finset.card_pos.mpr
    exact ⟨a, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hind a ha⟩⟩
  omega

lemma mixed_missing_edge_swap (A B : Finset (Fin 13))
    (h : ∃ p l : Fin 13, mixedNear p l ∧
      (∀ b ∈ B, ¬ mixedNear b l) ∧ (∀ a ∈ A, ¬ mixedNear p a)) :
    ∃ p l : Fin 13, mixedNear p l ∧
      (∀ a ∈ A, ¬ mixedNear a l) ∧ (∀ b ∈ B, ¬ mixedNear p b) := by
  obtain ⟨p, l, hpl, hB, hA⟩ := h
  refine ⟨l, p, (mixed_near_symm p l).mp hpl, ?_, ?_⟩
  · intro a ha hpa
    exact hA a ha ((mixed_near_symm a p).mp hpa)
  · intro b hb hlb
    exact hB b hb ((mixed_near_symm l b).mp hlb)

lemma mixed_small_independent_has_uncovered_edge (A B : Finset (Fin 13))
    (hAne : A.Nonempty) (hBne : B.Nonempty) (hsmall : A.card + B.card ≤ 5)
    (hind : ∀ a ∈ A, ∀ b ∈ B, ¬ mixedNear a b) :
    ∃ p l : Fin 13, mixedNear p l ∧
      (∀ a ∈ A, ¬ mixedNear a l) ∧ (∀ b ∈ B, ¬ mixedNear p b) := by
  have hApos := Finset.card_pos.mpr hAne
  have hBpos := Finset.card_pos.mpr hBne
  have hswap : ∀ b ∈ B, ∀ a ∈ A, ¬ mixedNear b a := by
    intro b hb a ha hba
    exact hind a ha b hb ((mixed_near_symm b a).mp hba)
  by_cases hA1 : A.card ≤ 1
  · exact mixed_missing_edge_one_four A B hAne hBne hA1 (by omega) hind
  by_cases hB1 : B.card ≤ 1
  · apply mixed_missing_edge_swap
    exact mixed_missing_edge_one_four B A hBne hAne hB1 (by omega) hswap
  by_cases hA2 : A.card ≤ 2
  · exact mixed_missing_edge_two_three A B hBne hA2 (by omega)
  · apply mixed_missing_edge_swap
    exact mixed_missing_edge_two_three B A hAne (by omega) (by omega)



lemma mixed_small_shore_closed_of_neighborhood_cover (A B : Finset (Fin 13))
    (hA : A.card ≤ 3) (hind : ∀ a ∈ A, ∀ b ∈ B, ¬ mixedNear a b)
    (hcover : ∀ p l : Fin 13, mixedNear p l →
      (∃ b ∈ B, mixedNear p b) ∨ (∃ a ∈ A, mixedNear a l)) : A = mixedOff B := by
  apply Finset.Subset.antisymm
  · intro a ha
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hind a ha⟩
  · intro p hp
    by_contra hpA
    obtain ⟨l, hpl, hl⟩ := mixed_neighbor_avoids_small A hA p hpA
    rcases hcover p l hpl with ⟨b, hb, hpb⟩ | ⟨a, ha, hal⟩
    · exact (Finset.mem_filter.mp hp).2 b hb hpb
    · exact hl a ha hal

lemma mixed_small_independent_neighborhood_not_cover (A B : Finset (Fin 13))
    (hAne : A.Nonempty) (hBne : B.Nonempty) (hsmall : A.card + B.card ≤ 5)
    (hind : ∀ a ∈ A, ∀ b ∈ B, ¬ mixedNear a b) :
    ¬ (∀ p l : Fin 13, mixedNear p l →
      (∃ b ∈ B, mixedNear p b) ∨ (∃ a ∈ A, mixedNear a l)) := by
  intro hcover
  obtain ⟨p, l, hpl, hA, hB⟩ := mixed_small_independent_has_uncovered_edge A B hAne hBne hsmall hind
  rcases hcover p l hpl with ⟨b, hb, hpb⟩ | ⟨a, ha, hal⟩
  · exact hB b hb hpb
  · exact hA a ha hal

end PEqualNP.Outside.L_meta_2056

namespace PEqualNP.Outside.L_meta_2056

lemma bipartite_mask_rejects_uncovered
    {α β : Type*} [DecidableEq α] [DecidableEq β]
    (R : α → β → Prop) [∀ a b, Decidable (R a b)]
    (g : Finset α → Finset β → Bool) (S : Finset α) (T : Finset β)
    (mono : ∀ A B A' B', A ⊆ A' → B ⊆ B' → g A B = true → g A' B' = true)
    (computes : ∀ A B,
      (g A B && decide ((∃ a ∈ A, a ∈ S) ∨ (∃ b ∈ B, b ∈ T))) =
        decide (∃ a ∈ A, ∃ b ∈ B, R a b))
    (A : Finset α) (B : Finset β)
    (independent : ∀ a ∈ A, ∀ b ∈ B, ¬ R a b)
    (uncovered : ∃ p l, R p l ∧ (∀ a ∈ A, ¬ R a l) ∧ (∀ b ∈ B, ¬ R p b)) :
    g A B = false := by
  obtain ⟨p, l, hpl, hA, hB⟩ := uncovered
  have maskCover : p ∈ S ∨ l ∈ T := by
    have eqn := computes {p} {l}
    have hit : decide (∃ a ∈ ({p} : Finset α), ∃ b ∈ ({l} : Finset β), R a b) = true := by
      simpa using hpl
    rw [hit] at eqn
    have mask := (Bool.and_eq_true_iff.mp eqn).2
    simpa only [decide_eq_true_eq, Finset.mem_singleton, exists_eq_left] using mask
  cases hg : g A B with
  | false => rfl
  | true =>
    rcases maskCover with hp | hl
    · have hpos := mono A B (insert p A) B (Finset.subset_insert p A) (Finset.Subset.refl B) hg
      have hmask : decide ((∃ a ∈ insert p A, a ∈ S) ∨ (∃ b ∈ B, b ∈ T)) = true := by
        simp only [decide_eq_true_eq]
        exact Or.inl ⟨p, Finset.mem_insert_self _ _, hp⟩
      have hfalse : decide (∃ a ∈ insert p A, ∃ b ∈ B, R a b) = false := by
        simp only [decide_eq_false_iff_not]
        rintro ⟨a, ha, b, hb, hab⟩
        rcases Finset.mem_insert.mp ha with rfl | ha
        · exact hB b hb hab
        · exact independent a ha b hb hab
      have eqn := computes (insert p A) B
      rw [hpos, hmask, hfalse] at eqn
      contradiction
    · have hpos := mono A B A (insert l B) (Finset.Subset.refl A) (Finset.subset_insert l B) hg
      have hmask : decide ((∃ a ∈ A, a ∈ S) ∨ (∃ b ∈ insert l B, b ∈ T)) = true := by
        simp only [decide_eq_true_eq]
        exact Or.inr ⟨l, Finset.mem_insert_self _ _, hl⟩
      have hfalse : decide (∃ a ∈ A, ∃ b ∈ insert l B, R a b) = false := by
        simp only [decide_eq_false_iff_not]
        rintro ⟨a, ha, b, hb, hab⟩
        rcases Finset.mem_insert.mp hb with rfl | hb
        · exact hA a ha hab
        · exact independent a ha b hb hab
      have eqn := computes A (insert l B)
      rw [hpos, hmask, hfalse] at eqn
      contradiction

end PEqualNP.Outside.L_meta_2056

namespace PEqualNP.Outside.L_meta_2056

lemma mixed_last_or_mask_rejects_small
    (g : Finset (Fin 13) → Finset (Fin 13) → Bool)
    (S T A B : Finset (Fin 13))
    (mono : ∀ A B A' B', A ⊆ A' → B ⊆ B' → g A B = true → g A' B' = true)
    (computes : ∀ A B,
      (g A B && decide ((∃ a ∈ A, a ∈ S) ∨ (∃ b ∈ B, b ∈ T))) =
        decide (∃ a ∈ A, ∃ b ∈ B, mixedNear a b))
    (hA : A.Nonempty) (hB : B.Nonempty) (small : A.card + B.card ≤ 5)
    (independent : ∀ a ∈ A, ∀ b ∈ B, ¬ mixedNear a b) : g A B = false := by
  refine bipartite_mask_rejects_uncovered mixedNear g S T mono ?_ A B independent ?_
  · intro X Y
    by_cases hm : (∃ a ∈ X, a ∈ S) ∨ (∃ b ∈ Y, b ∈ T) <;>
      by_cases he : ∃ a ∈ X, ∃ b ∈ Y, mixedNear a b <;>
      simpa only [hm, he, decide_true, decide_false] using computes X Y
  · exact mixed_small_independent_has_uncovered_edge A B hA hB small independent

end PEqualNP.Outside.L_meta_2056

namespace PEqualNP.Outside.L_meta_2056.FirstOrOrbit

abbrev graph : SimpleGraph (Fin 26) :=
  SimpleGraph.fromRel fun u v => u.val < 13 ∧ 13 ≤ v.val ∧
    (u.val + v.val) % 13 ∈ ([0, 1, 3, 9] : List ℕ)

def generatorData : List (List (Fin 26)) :=
  [[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25],
   [4, 1, 3, 2, 0, 5, 8, 7, 6, 10, 9, 11, 12, 25, 23, 15, 18, 17, 16, 20, 19, 21, 22, 14, 24, 13],
   [0, 4, 2, 5, 1, 3, 6, 9, 12, 7, 10, 11, 8, 22, 14, 18, 16, 19, 15, 17, 20, 23, 13, 21, 24, 25],
   [3, 1, 2, 0, 10, 8, 6, 7, 5, 9, 4, 12, 11, 13, 24, 15, 23, 18, 17, 22, 20, 21, 19, 16, 14, 25],
   [13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]

def generator (g : Fin 5) (v : Fin 26) : Fin 26 :=
  ((generatorData.getD g.val []).getD v.val 0)

lemma generator_involutive : ∀ g : Fin 5, Function.Involutive (generator g) := by
  unfold Function.Involutive
  decide +kernel

lemma generator_adj : ∀ (g : Fin 5) (u v : Fin 26),
    graph.Adj (generator g u) (generator g v) ↔ graph.Adj u v := by
  decide +kernel

def wordMap : ℕ → ℕ → Fin 26 → Fin 26
  | 0, _, v => v
  | n + 1, code, v =>
    generator ⟨code % 5, Nat.mod_lt _ (by decide)⟩ (wordMap n (code / 5) v)

lemma wordMap_bijective (n : ℕ) : ∀ code, Function.Bijective (wordMap n code) := by
  induction n with
  | zero => intro code; exact Function.bijective_id
  | succ n ih =>
    intro code
    exact (generator_involutive ⟨code % 5, Nat.mod_lt _ (by decide)⟩).bijective.comp
      (ih (code / 5))

lemma wordMap_adj (n : ℕ) : ∀ (code : ℕ) (u v : Fin 26),
    graph.Adj (wordMap n code u) (wordMap n code v) ↔ graph.Adj u v := by
  induction n with
  | zero => intro code u v; rfl
  | succ n ih =>
    intro code u v
    simp only [wordMap, generator_adj, ih]

def modeData : List (Finset (Fin 26)) :=
  [∅, {0}, {1}, {2}, {3}, {4}, {5}, {6}, {7}, {8}, {9}, {10}, {11}, {12}, {13}, {14}, {15}, {16}, {17}, {18}, {19}, {20}, {21}, {22}, {23}, {24}, {25}, {0, 13}, {0, 14}, {0, 16}, {0, 22}, {1, 13}, {1, 15}, {1, 21}, {1, 25}, {2, 14}, {2, 20}, {2, 24}, {2, 25}, {3, 13}, {3, 19}, {3, 23}, {3, 24}, {4, 18}, {4, 22}, {4, 23}, {4, 25}, {5, 17}, {5, 21}, {5, 22}, {5, 24}, {6, 16}, {6, 20}, {6, 21}, {6, 23}, {7, 15}, {7, 19}, {7, 20}, {7, 22}, {8, 14}, {8, 18}, {8, 19}, {8, 21}, {9, 13}, {9, 17}, {9, 18}, {9, 20}, {10, 16}, {10, 17}, {10, 19}, {10, 25}, {11, 15}, {11, 16}, {11, 18}, {11, 24}, {12, 14}, {12, 15}, {12, 17}, {12, 23}]

def mode (i : Fin 79) : Finset (Fin 26) := modeData.getD i.val ∅

def representativeData : List (Fin 79 × Fin 79) :=
  [(1, 2), (1, 14), (1, 16), (1, 31), (1, 32), (27, 32), (27, 36)]

def representative (i : Fin 7) : Fin 79 × Fin 79 :=
  representativeData.getD i.val (0, 0)

set_option maxRecDepth 32768 in
def certificateData : List (List ℕ) :=
  [[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
   [0, 0, 0, 78197, 2877, 14, 602, 11837, 7252, 18788, 1477, 78211, 833, 12572, 1, 1289, 2, 134, 3383, 16, 2543, 6729, 2585, 15, 6799, 6463, 758, 0, 0, 0, 0, 3, 4, 291673, 471167, 84675, 297301, 1020765, 84676, 12932, 62717, 12933, 304448, 18, 17, 58335, 260502, 18967, 2587, 2586, 60890, 51215, 841712, 51216, 256078, 41003, 37328, 33506, 33505, 18791, 18792, 94217, 93937, 6730, 7466, 8201, 6731, 78214, 78215, 303545, 203627, 837, 836, 4183, 1305140, 39189, 39190, 42795, 42340],
   [0, 0, 0, 112, 21, 7, 12138, 1673, 97944, 7798, 287, 56, 17213, 11844, 253, 6414, 3375, 254, 268, 51, 7471, 37354, 6924, 10215, 1283, 32083, 50, 255, 167927, 256, 186841, 0, 0, 0, 0, 6416, 257527, 32085, 6415, 1284, 256267, 1285, 160416, 53, 37370, 38840, 52, 173135, 51516, 51517, 170265, 6927, 1287941, 6926, 34640, 489422, 489423, 1482667, 1813683, 34052, 34626, 257590, 34051, 1340, 1341, 6710, 37356, 7767, 270, 7473, 269, 17216, 17217, 20878, 1280535, 256106, 51222, 104395, 51223],
   [0, 0, 0, 0, 40873, 574, 40922, 15162, 2324, 16898, 462, 2891, 8498, 19047, 30, 3438, 114, 135, 65, 338, 331, 463, 1556, 156, 310, 8499, 113, 204390, 78200, 78201, 294802, 60652, 116, 296951, 115, 0, 0, 0, 0, 40877, 362842, 362212, 40876, 578, 72370, 73840, 577, 84515, 72587, 204383, 72586, 15677, 15676, 64691, 58587, 11673, 2328, 2327, 11645, 16901, 16902, 59427, 84487, 52252, 466, 2335, 465, 14767, 2895, 14473, 2894, 8502, 42417, 42326, 8501, 20940, 20941, 104591, 212090],
   [0, 0, 0, 0, 0, 15638, 8183, 19558, 11627, 3031, 7406, 91, 7833, 3808, 22, 1290, 23, 1689, 93, 674, 92, 1654, 6876, 506, 687, 6462, 149, 2880, 292758, 2881, 52308, 24, 25, 59392, 261503, 204152, 1486510, 172126, 172127, 0, 0, 0, 0, 15642, 60708, 15641, 303503, 40842, 34437, 40933, 34436, 78152, 297126, 256085, 78151, 58356, 11630, 11631, 58216, 12177, 78376, 12176, 12940, 14465, 14466, 37335, 33660, 11666, 95, 94, 261251, 7837, 8467, 8558, 7836, 261027, 4190, 20920, 4189],
   [0, 0, 0, 0, 0, 0, 119, 8379, 1449, 2366, 19586, 294, 3836, 2513, 3789, 1360, 9, 79, 1493, 673, 1346, 12714, 3110, 78, 6448, 32188, 8, 63627, 255210, 81, 80, 168620, 11, 168767, 10, 32078, 313576, 160423, 32077, 16937, 59462, 16936, 489710, 0, 0, 0, 0, 63760, 6423, 6422, 304315, 34633, 294837, 173198, 34632, 33548, 6703, 186631, 6702, 303937, 10244, 521973, 10245, 362737, 97885, 97884, 908660, 1642, 1495, 1348, 1347, 4176, 20906, 4175, 1521545, 170258, 10392, 86545, 10391],
   [0, 0, 0, 0, 0, 0, 0, 40761, 37044, 19054, 2352, 469, 1708, 12558, 100, 275, 1710, 604, 470, 121, 471, 2354, 3445, 120, 1374, 1709, 499, 10462, 58552, 606, 605, 12142, 14802, 12141, 60701, 860906, 844176, 40925, 40926, 8187, 168837, 172183, 8186, 123, 122, 19170, 52301, 0, 0, 0, 0, 72552, 476466, 72551, 172015, 95645, 72328, 168298, 72327, 60792, 20948, 95295, 20947, 291078, 2355, 16951, 2356, 3392, 472, 473, 422377, 1712, 39092, 39183, 1711, 60883, 51937, 51936, 64698],
   [0, 0, 0, 0, 0, 0, 0, 0, 12754, 8148, 2548, 41916, 3983, 12523, 12539, 15164, 1675, 484, 3089, 2375, 15451, 1653, 1674, 11839, 2059, 6939, 2564, 59203, 84816, 11840, 11841, 102687, 1677, 1676, 303566, 15166, 15165, 64362, 78502, 19562, 59210, 19561, 424085, 8383, 294585, 8382, 204691, 40765, 40764, 95281, 935890, 0, 0, 0, 0, 52133, 15453, 15452, 63683, 187177, 8152, 168802, 8151, 12737, 3091, 10427, 3090, 41919, 41920, 58916, 859926, 3987, 3986, 19933, 1522091, 471531, 19940, 99670, 19939],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 19124, 12663, 7266, 19838, 58919, 33665, 10201, 2339, 7254, 7268, 1451, 2080, 10200, 37046, 505, 36283, 51018, 64381, 168578, 205328, 7256, 7255, 99187, 97947, 97948, 495926, 10203, 10202, 51020, 64383, 41437, 36284, 36285, 255091, 1453, 1452, 41465, 842881, 97717, 37048, 37047, 1026673, 12758, 12757, 63823, 63795, 0, 0, 0, 0, 318966, 40667, 40666, 185245, 386642, 36341, 41451, 36340, 8292, 7270, 7269, 1016502, 19841, 19842, 20633, 2480335, 496066, 99214, 103170, 99215],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 11781, 616, 17248, 3773, 513, 1380, 7800, 3831, 618, 2367, 330, 11783, 1555, 2368, 3033, 1388, 2508, 40940, 40939, 41906, 844190, 60715, 7802, 7801, 303510, 95252, 296041, 1281487, 95253, 52315, 3034, 3035, 292765, 2369, 2370, 16965, 296006, 64208, 19057, 19058, 303965, 34402, 843427, 34401, 362765, 19128, 19127, 77256, 313058, 0, 0, 0, 0, 171987, 84760, 11784, 11785, 3833, 620, 619, 63676, 17252, 20458, 17251, 304420, 8564, 8565, 195920, 94308],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3913, 4123, 3822, 99, 2039, 289, 1479, 414, 624, 36346, 2038, 10229, 33714, 7408, 10208, 12875, 1480, 41066, 1481, 33716, 290, 291, 205356, 168606, 2041, 2040, 10210, 12877, 7409, 168585, 7410, 205335, 19589, 181745, 19590, 423441, 10230, 10231, 207183, 1275453, 2552, 2551, 52112, 12765, 12667, 181703, 12666, 167591, 510402, 40736, 203592, 40737, 0, 0, 0, 0, 3917, 3916, 36348, 469627, 4127, 20542, 4126, 2613335, 522666, 20640, 20639, 102715],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3458, 763, 18958, 6435, 58, 3123, 2045, 296, 407, 63583, 2046, 6743, 408, 6813, 57, 84690, 97941, 84689, 297315, 33723, 60, 41073, 59, 37041, 842916, 160395, 37040, 64376, 409, 410, 51041, 298, 6745, 8215, 297, 2047, 2048, 160892, 255203, 173169, 296552, 203676, 173170, 34542, 33519, 908506, 33520, 60862, 12751, 12750, 32120, 167598, 19575, 19576, 181731, 0, 0, 0, 0, 3462, 3461, 17308, 851295, 304308, 20885, 20884, 104535],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4088, 19063, 19189, 1695, 1562, 12588, 337, 12868, 64339, 6960, 15493, 3838, 1387, 34750, 19065, 19191, 19064, 64215, 59245, 19197, 19198, 296160, 170426, 173576, 34751, 34752, 38812, 34717, 34087, 34086, 3839, 15495, 3840, 95316, 18890, 6962, 170342, 6961, 62639, 1287752, 161487, 62640, 95672, 95673, 294620, 173058, 170237, 62814, 510073, 62815, 34612, 19135, 19134, 77410, 12589, 12590, 62948, 173051, 0, 0, 0, 0, 102316, 20464, 102015, 20465],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3810, 274, 589, 765, 64, 2515, 3096, 15479, 12560, 2571, 309, 6946, 12546, 194065, 12575, 12576, 173590, 11848, 11847, 84823, 59231, 19050, 64201, 313737, 19051, 3812, 12842, 3811, 95960, 2517, 303573, 2516, 865260, 12561, 12562, 261573, 851190, 12527, 1604376, 94301, 12526, 58922, 294606, 58923, 478370, 3776, 3777, 320877, 18862, 62612, 3825, 3826, 15481, 767, 766, 3098, 94252, 4091, 4092, 20402, 511585, 0, 0, 0, 0],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 28, 58954, 12537, 98, 511, 37086, 12502, 3752, 7413, 20412, 161, 62594, 0, 31, 12540, 33666, 0, 62730, 3755, 185377, 32, 12506, 165, 185378, 0, 168339, 20415, 164, 3791, 37342, 20416, 213987, 102, 3756, 37083, 20381, 12541, 186652, 18841, 62710, 926503, 168340, 167542, 33667, 64166, 515, 185420, 18785, 0, 101, 514, 12505, 64677, 18960, 186715, 211712, 313660, 203620, 255308, 471160, 94231, 62731, 52098, 40723],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 588, 133, 63, 2422, 329, 19831, 1554, 154, 308, 3437, 4081, 1291, 0, 6436, 6457, 33583, 32092, 6808, 807895, 0, 296530, 3440, 161584, 1292, 1383, 1551, 3441, 96065, 6717, 1362, 360441, 277, 7753, 6458, 17203, 51251, 807335, 173548, 34710, 51503, 851673, 296531, 186792, 0, 10300, 1382, 6807, 261041, 170335, 10301, 839710, 6437, 168676, 172960, 161585, 34745, 802092, 173723, 1484466, 0, 32091, 276, 1361],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8169, 2898, 14511, 3129, 11648, 3374, 2338, 2947, 1694, 12544, 1021962, 12128, 8173, 10448, 58957, 0, 3377, 51922, 592, 15656, 1698, 51923, 259606, 3133, 2951, 8481, 40856, 2342, 14487, 522967, 2902, 3378, 11687, 39078, 72566, 11652, 11883, 72377, 0, 3132, 11651, 2341, 195395, 14515, 58251, 16895, 58958, 361862, 362191, 58237, 72440, 204285, 11715, 294781, 0, 8172, 14514, 1697, 591, 0, 2901, 2950],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3122, 1631, 3906, 8281, 2429, 37058, 483, 1561, 756, 14416, 136, 0, 58950, 361708, 40828, 2433, 52203, 137, 34535, 1565, 15201, 14417, 15628, 14781, 1691, 8166, 72342, 487, 10441, 3126, 73756, 72083, 8453, 0, 34534, 2432, 486, 843448, 804423, 58167, 58951, 11876, 6885, 161410, 64712, 261552, 160885, 168690, 290833, 0, 3125, 15627, 10440, 34422, 0, 6884, 1564, 59378, 34423, 807048, 323558],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 623, 36372, 7273, 11858, 72541, 322, 3969, 497, 12723, 37426, 3385, 72545, 58545, 160402, 60785, 292716, 67, 63298, 3973, 2076, 417, 173177, 326, 12135, 16916, 362716, 7487, 63606, 0, 51236, 72544, 3972, 11890, 33527, 256176, 6752, 1567892, 58965, 294816, 296083, 33751, 3140, 167626, 51237, 416, 0, 3139, 33526, 3384, 0, 58964, 2075, 362870, 321731, 64348, 1517590, 66, 160401, 0, 325],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 14504, 19537, 12152, 11788, 672, 336, 2506, 2090, 2426, 1635, 361701, 11708, 204131, 12156, 304427, 2958, 78131, 340, 10385, 3042, 14508, 676, 7816, 0, 11791, 675, 10384, 627, 14753, 84767, 42256, 33765, 58258, 323551, 2377, 1810953, 290826, 291183, 11792, 2425, 0, 14507, 12155, 2089, 626, 0, 58257, 37440, 58573, 860087, 318035, 72572, 1634, 0, 339, 303517, 72573, 261517, 84473],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 12656, 1624, 504, 59304, 791, 2499, 37090, 20535, 3910, 2545, 424092, 51090, 37433, 317881, 333, 12660, 795, 10378, 37089, 0, 99165, 794, 41416, 15467, 99166, 498362, 36376, 1628, 2083, 60673, 59448, 77277, 33758, 294592, 12869, 0, 12659, 2082, 332, 41415, 0, 1627, 59217, 294823, 476417, 317916, 3909, 36375, 0, 10377, 12870, 469620, 1814348, 1604145, 168753, 15698, 838128, 256183],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8127, 2527, 1652, 3962, 185437, 181465, 19835, 8285, 77326, 63578, 51027, 181808, 927203, 19834, 0, 3965, 185440, 36292, 36383, 1656, 3966, 19541, 12716, 36362, 185441, 7277, 8131, 10406, 19828, 8284, 0, 8130, 1655, 51026, 36382, 0, 10405, 99145, 36390, 52035, 40660, 36291, 7276, 19540, 0, 181437, 97710, 63585, 296076, 64341, 1016495, 321703, 2478620, 495723, 78481, 260173, 203298],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8141, 3108, 3444, 749, 167878, 15551, 38910, 34395, 161255, 51257, 0, 32252, 1558, 34381, 3448, 32253, 161256, 6878, 7781, 17231, 194541, 171966, 3112, 839381, 11861, 0, 34394, 3447, 10307, 34380, 0, 3111, 160878, 168683, 386292, 58937, 1557, 51530, 6877, 0, 1305231, 11862, 51531, 1020856, 10308, 59301, 204173, 261048, 256295, 1276083, 860598, 1056745, 211348, 51258, 1480042, 318392],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 777, 819, 12516, 7416, 157, 37061, 0, 186708, 10217, 102078, 933531, 158, 2531, 823, 37076, 7417, 508, 781, 4106, 51166, 0, 780, 37075, 97961, 8144, 0, 822, 62703, 52091, 40716, 94203, 2572, 507, 2530, 0, 303370, 51167, 10420, 8145, 168333, 489801, 185301, 319176, 37062, 97962, 63837, 513587, 51062, 1018098, 1568298, 843770, 320828, 2573, 927098, 93923],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 686, 147, 72090, 6801, 73910, 33576, 489717, 160451, 12170, 167906, 312, 6906, 690, 6451, 72089, 59307, 0, 689, 10251, 32280, 0, 6450, 1376, 38756, 32281, 59385, 2061, 6905, 12169, 0, 257506, 59308, 290840, 908667, 42270, 10252, 360420, 160612, 294683, 33737, 32176, 167612, 2062, 40835, 296503, 52210, 172120, 255217, 1276027, 296895, 311, 160450, 1375, 0],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 812, 6465, 17210, 7760, 6920, 95967, 160465, 34045, 161578, 17209, 161465, 0, 32315, 6464, 32294, 32189, 0, 38791, 34591, 32190, 32316, 19211, 34044, 6919, 0, 6941, 161466, 193841, 256260, 170328, 257548, 839703, 387062, 86020, 1390, 32295, 38770, 321087, 51510, 34066, 167941, 6815, 19212, 33590, 102337, 6947, 6814, 1389, 0, 430098, 6948, 161473, 193848],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 62598, 4085, 760, 12520, 62597, 12547, 752, 0, 4084, 294626, 815, 0, 62892, 2503, 151, 816, 2509, 12519, 150, 0, 501, 753, 19142, 4078, 2566, 927091, 64173, 12835, 321017, 387090, 294627, 77417, 20395, 2510, 95715, 3770, 387083, 94791, 323376, 933566, 759, 500, 2502, 0, 62745, 94245, 313723, 509870, 101973, 12548, 260481, 18848],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5, 167879, 62599, 33, 6, 367310, 2925, 0, 37091, 12934, 6466, 161342, 37343, 10254, 34467, 257935, 8203, 10463, 39185, 12542, 36679, 36560, 41950, 34, 7335, 63797, 33668, 40941, 14412, 17142, 185310, 0, 7467, 2091, 6732, 64678, 2050, 14587, 300, 95675, 19066, 168762, 38793, 94232, 6733, 15175, 1504],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 33584, 6460, 42342, 93918, 0, 19836, 17211, 4086, 1293, 6719, 18794, 362928, 1294, 6718, 94219, 51253, 33585, 6439, 6459, 211658, 51252, 36364, 364489, 183154, 78168, 317953, 36385, 186793, 0, 2427, 20536, 15552, 41067, 85168, 72904, 7279, 6438, 93939, 33564, 312668, 807589, 19192, 161678, 34803, 0, 12129, 37427, 6802],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 257, 72085, 32255, 41047, 138, 839, 168314, 51218, 2882, 72344, 101919, 37589, 14419, 82, 6453, 168769, 51239, 170022, 607, 34047, 0, 8286, 38911, 73911, 139, 72960, 63804, 7257, 11877, 58953, 37435, 6880, 1482, 14594, 685, 20054, 0, 3386, 3911, 761, 838, 0, 1636, 7761, 12577, 14503, 7489, 1378],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 186709, 259622, 51260, 172325, 159, 20, 73464, 587, 7418, 51589, 41005, 7839, 19, 0, 33577, 12521, 18968, 2588, 0, 6921, 11842, 15462, 8392, 7314, 10449, 2546, 33507, 0, 303371, 11787, 3037, 7510, 33717, 1469, 160, 304303, 37063, 20887, 412, 62, 102262, 64216, 19137, 62887, 173591, 32108, 7419, 37064],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 32304, 78560, 161517, 60653, 0, 256268, 1286, 95968, 94212, 183147, 18787, 168621, 258, 3757, 14580, 471547, 1343, 63685, 18842, 6712, 99188, 7272, 10205, 1455, 94310, 1287, 72897, 18786, 0, 1342, 6711, 37357, 3758, 18843, 36630, 33724, 59246, 478330, 194193, 173585, 38828, 11849, 187578, 209705],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 522010, 17219, 161468, 117, 26, 51925, 360422, 32297, 360408, 471050, 32283, 12, 20880, 3379, 51225, 6922, 34537, 99385, 1678, 6908, 0, 51091, 51028, 10218, 1385, 14510, 187130, 7803, 292, 16897, 3380, 317925, 16883, 84468, 170169, 61, 0, 17218, 20879, 160466, 32093, 0, 104396, 51224],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 6929, 60969, 34642, 32254, 59393, 256297, 34628, 8469, 97747, 93925, 170267, 168768, 60786, 0, 51518, 34046, 2434, 181809, 0, 12171, 97949, 183210, 182510, 213814, 6809, 12157, 37434, 0, 205357, 42839, 41719, 260469, 34054, 19550, 85175, 41074, 19199, 161685, 513372, 34810, 167719, 51259, 102675, 38779],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 6417, 257528, 32086, 0, 62893, 392783, 8210, 42279, 54, 37371, 38841, 0, 55, 754, 7475, 167712, 6418, 364468, 64174, 32087, 321018, 36287, 36343, 7258, 33543, 272, 37372, 3771, 168607, 3772, 755, 183133, 7768, 271, 7474, 0, 62746, 38842, 187592, 38800, 193997, 12549, 37519, 7769],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 84510, 20943, 84419, 3442, 104404, 74192, 34635, 32079, 85203, 72554, 16904, 17204, 259629, 15167, 170008, 34033, 3443, 496929, 10204, 807897, 0, 2959, 334, 1559, 1298114, 203692, 17205, 2042, 102703, 17093, 34544, 37042, 172080, 161489, 34418, 170427, 0, 593, 68, 313],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 27, 97, 4192, 3967, 19837, 15714, 16939, 185442, 475, 12144, 125, 19829, 15678, 0, 34382, 6907, 11674, 2329, 0, 2532, 99146, 2372, 622, 8378, 12507, 467, 2336, 0, 3464, 3968, 12214, 296077, 19200, 12592, 3842, 173577, 64202, 4094, 769, 2519],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 166, 796, 691, 0, 73814, 39178, 72589, 32317, 3974, 3449, 824, 0, 40879, 64363, 160943, 160614, 17212, 161580, 51021, 802969, 86021, 426012, 8504, 42419, 511314, 32318, 40739, 10211, 173172, 74185, 14839, 102338, 1699, 1566, 341, 0, 313738, 361864, 42510, 33739],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 14622, 118, 73835, 817, 579, 37077, 6452, 0, 580, 14769, 17128, 4079, 102269, 78503, 8154, 40760, 818, 40669, 64384, 20033, 20396, 2897, 33760, 41733, 34453, 20397, 4080, 12878, 14768, 2077, 10379, 0, 72372, 203608, 33767, 34753, 19052, 14475, 6754, 73394],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 10247, 2918, 16938, 1497, 2883, 73828, 3429, 8188, 14468, 168783, 8350, 19563, 167, 41438, 12760, 4010, 18885, 102010, 52316, 34404, 0, 418, 3043, 33661, 20383, 32269, 64377, 6894, 33662, 7517, 40725, 38813, 41705, 72358, 33753, 3813],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4178, 83, 59463, 13, 2358, 14804, 608, 60674, 11843, 3093, 1679, 59211, 3134, 0, 11632, 509, 1384, 14509, 0, 6879, 59218, 797, 7342, 61053, 11667, 96, 0, 2504, 8175, 19193, 37092, 34718, 12578, 20453, 3828, 12843],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 677, 782, 0, 152, 17044, 34397, 78154, 59386, 14782, 1657, 7782, 0, 692, 36286, 195075, 209019, 6810, 72435, 3036, 34005, 7411, 3422, 20544, 12669, 32262, 72092, 411, 808464, 72512, 6887, 37442, 34088, 1552, 2952, 327, 0],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 34600, 167817, 32191, 838550, 12136, 17232, 4107, 0, 95969, 42503, 212078, 256261, 62964, 255092, 42755, 478435, 211455, 167922, 32296, 32192, 205336, 364517, 96060, 36392, 34439, 6467, 33591, 256262, 7838, 1692, 7817, 0, 168678, 1018044, 208550, 95961],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 10387, 511279, 124, 8189, 11794, 19879, 34383, 2378, 678, 36497, 63587, 1454, 96066, 0, 41417, 10246, 3792, 16917, 0, 19542, 3408, 72953, 36637, 299, 4177, 8167, 0, 38792, 279, 2904, 37428, 2518],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 63761, 6424, 0, 34592, 3989, 12739, 20614, 94204, 2343, 6704, 12717, 0, 8567, 2371, 52317, 41943, 293, 36350, 181746, 2043, 783, 7328, 60864, 6746, 51897, 95668, 15496, 34719, 18864, 6425, 37078, 93924],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 60787, 10394, 19171, 42335, 488, 36363, 3113, 0, 15637, 12662, 63594, 41466, 97754, 10253, 20537, 86162, 62537, 36644, 19591, 36504, 170260, 17037, 3912, 8216, 303162, 32339, 3841, 6964, 1363, 10393, 7488, 0],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 170092, 1644, 19143, 38772, 19144, 85693, 160425, 12836, 153, 18850, 36658, 77418, 209733, 2511, 20012, 38835, 1483, 10233, 323377, 36462, 1643, 1496, 1349, 0, 73387, 194200, 95317, 7762, 7503, 1350, 39087, 18849],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 20894, 8287, 40766, 8385, 12137, 3975, 19858, 97718, 41908, 102255, 19130, 51238, 103, 0, 628, 2357, 3127, 0, 474, 502, 14762, 8168, 1637, 18891, 278, 2903, 0, 1377],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 72553, 8132, 0, 38757, 11864, 7797, 38968, 37049, 7754, 14754, 1629, 0, 58939, 10232, 3450, 39017, 17233, 2049, 195068, 194172, 187200, 34425, 172108, 6963, 1364, 14489, 12563, 6803],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 36714, 78504, 40717, 1672, 11688, 2084, 10407, 0, 8343, 17254, 61004, 8146, 804, 207184, 825, 2554, 4108, 97963, 10464, 4003, 8147, 37575, 168300, 170343, 3779, 20404, 261574, 12529],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 185464, 208543, 193842, 362879, 19214, 260462, 181950, 387063, 843380, 209537, 41712, 38771, 95689, 51511, 314810, 8553, 172185, 19213, 1714, 211294, 1713, 8454, 39184, 0, 42293, 74087, 161474, 8462],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 489, 2085, 12759, 51575, 212358, 2960, 335, 34403, 10317, 419, 2435, 2553, 0, 11891, 58917, 2567, 3988, 0, 19934, 6942, 173767, 594, 69, 12528],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 11653, 15454, 0, 52092, 907185, 1658, 194564, 40661, 12738, 3092, 10428, 0, 181438, 20593, 63692, 20068, 40662, 1016496, 203300, 94443, 181439, 8133, 94254, 203299],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3114, 38912, 63824, 7783, 173549, 8153, 33759, 0, 15189, 60997, 12200, 52113, 10309, 86218, 39003, 187753, 1700, 161488, 14825, 34068, 170337, 8497, 74122, 94302],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2442, 257872, 63796, 10422, 425879, 42475, 183567, 160613, 2064, 12172, 2092, 12766, 2063, 19564, 19942, 95717, 2967, 62641, 342, 34754, 34711, 19941, 6753, 0],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 12193, 2428, 19129, 15553, 104, 3142, 629, 12668, 3128, 3387, 11716, 503, 0, 19843, 20634, 170329, 51504, 0, 103171, 99216],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 318967, 40668, 0, 168684, 51085, 2547, 15700, 181704, 8293, 7271, 0, 387091, 12871, 182342, 100372, 34705, 195033, 15699, 20600, 39122],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 181460, 10408, 52036, 194543, 167543, 36342, 41452, 0, 78483, 12718, 63586, 36455, 64342, 195047, 319122, 173508, 181719, 58924, 63825, 39010],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 52093, 14685, 10421, 1560, 185233, 10219, 510, 167592, 2533, 7300, 33521, 37050, 51063, 7825, 39108, 173669, 173522, 2574, 20075, 36469],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 256304, 97803, 10302, 42762, 10443, 40942, 60863, 7755, 14818, 1693, 170238, 173753, 0, 8566, 33752, 42271],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 516, 3141, 0, 11786, 12158, 2078, 12752, 34019, 14516, 6886, 0, 1391, 3778, 2953, 328, 40837],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4017, 4122, 203593, 12767, 3834, 621, 0, 63677, 102017, 62642, 510074, 18892, 168754, 1630, 471253, 187872],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 37554, 17247, 40738, 7804, 51967, 304968, 32121, 8217, 8483, 34012, 62816, 6817, 18863, 42468, 194179, 41089],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 12508, 18961, 1462, 7412, 14692, 1567, 34613, 187543, 205358, 2939, 52099, 314],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3918, 0, 36349, 94792, 60647, 100092, 19136, 6943, 170336, 20641, 0, 33738],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 15630, 19577, 8364, 2505, 4128, 20543, 0, 34067, 34712, 12130, 3827, 20019],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 41803, 97711, 10212, 7293, 160593, 362858, 77411, 34733, 36294, 51883, 15482, 185254],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3463, 0, 17309, 6816, 34817, 60633, 768, 161692],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 14517, 12591, 160600, 1392, 168677, 20886, 0, 40836],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 32122, 62949, 72575, 6950, 160439, 10380, 3099, 181453],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 6747, 94246, 7818, 37512, 1553, 14678, 94253, 41075],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 34746, 0, 102016, 20466],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8455, 4093, 211287, 170050],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 74080, 20403, 193864, 42258],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 170358, 6949, 38814, 34075],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]

def certificate (i j : Fin 79) : ℕ :=
  (certificateData.getD i.val []).getD j.val 0

def certificateRepresentative (code : ℕ) : Fin 79 × Fin 79 :=
  representative ⟨code % 7, Nat.mod_lt _ (by decide)⟩

def certificateMap (code : ℕ) : Fin 26 → Fin 26 :=
  wordMap 8 (code / 7)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 16000000 in
lemma finite_certificate : ∀ i j : Fin 79, i ≠ 0 → i < j → Disjoint (mode i) (mode j) →
    let code := certificate i j
    let r := certificateRepresentative code
    (((mode r.1).image (certificateMap code) = mode i ∧
      (mode r.2).image (certificateMap code) = mode j) ∨
      ((mode r.1).image (certificateMap code) = mode j ∧
      (mode r.2).image (certificateMap code) = mode i)) := by
  decide +kernel

lemma seven_representatives (i j : Fin 79) (hi : i ≠ 0) (hij : i < j)
    (hd : Disjoint (mode i) (mode j)) :
    ∃ (k : Fin 7) (e : Equiv.Perm (Fin 26)),
      (∀ u v, graph.Adj (e u) (e v) ↔ graph.Adj u v) ∧
      (((mode (representative k).1).image e = mode i ∧
        (mode (representative k).2).image e = mode j) ∨
        ((mode (representative k).1).image e = mode j ∧
        (mode (representative k).2).image e = mode i)) := by
  let code := certificate i j
  let k : Fin 7 := ⟨code % 7, Nat.mod_lt _ (by decide)⟩
  let e : Equiv.Perm (Fin 26) := Equiv.ofBijective (certificateMap code)
    (wordMap_bijective 8 (code / 7))
  refine ⟨k, e, ?_, ?_⟩
  · exact wordMap_adj 8 (code / 7)
  · exact finite_certificate i j hi hij hd

def basicArm (S : Finset (Fin 26)) : Prop :=
  (∃ v : Fin 26, S = {v}) ∨ ∃ u v : Fin 26, graph.Adj u v ∧ S = {u, v}

lemma singleton_mode : ∀ v : Fin 26, ∃ i : Fin 79, i ≠ 0 ∧ mode i = {v} := by
  decide +kernel

lemma edge_mode : ∀ u v : Fin 26, graph.Adj u v →
    ∃ i : Fin 79, i ≠ 0 ∧ mode i = {u, v} := by
  decide +kernel

lemma basicArm_nonempty (S : Finset (Fin 26)) (hS : basicArm S) : S.Nonempty := by
  rcases hS with ⟨v, rfl⟩ | ⟨u, v, _, rfl⟩ <;> simp

lemma basicArm_mode (S : Finset (Fin 26)) (hS : basicArm S) :
    ∃ i : Fin 79, i ≠ 0 ∧ mode i = S := by
  rcases hS with ⟨v, rfl⟩ | ⟨u, v, huv, rfl⟩
  · exact singleton_mode v
  · exact edge_mode u v huv

lemma disjoint_arms_seven_representatives (A B : Finset (Fin 26))
    (hA : basicArm A) (hB : basicArm B) (hd : Disjoint A B) :
    ∃ (k : Fin 7) (e : Equiv.Perm (Fin 26)),
      (∀ u v, graph.Adj (e u) (e v) ↔ graph.Adj u v) ∧
      (((mode (representative k).1).image e = A ∧
        (mode (representative k).2).image e = B) ∨
        ((mode (representative k).1).image e = B ∧
        (mode (representative k).2).image e = A)) := by
  obtain ⟨i, hi, ha⟩ := basicArm_mode A hA
  obtain ⟨j, hj, hb⟩ := basicArm_mode B hB
  have hne : i ≠ j := by
    intro heq
    subst j
    have hAB : A = B := ha.symm.trans hb
    rw [← hAB] at hd
    obtain ⟨v, hv⟩ := basicArm_nonempty A hA
    exact Finset.disjoint_left.mp hd hv hv
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · obtain ⟨k, e, he, hm⟩ := seven_representatives i j hi hlt (by simpa only [ha, hb] using hd)
    exact ⟨k, e, he, by simpa only [ha, hb] using hm⟩
  · obtain ⟨k, e, he, hm⟩ := seven_representatives j i hj hgt (by simpa only [ha, hb] using hd.symm)
    refine ⟨k, e, he, ?_⟩
    rcases hm with hm | hm
    · exact Or.inr (by simpa only [ha, hb] using hm)
    · exact Or.inl (by simpa only [ha, hb] using hm)

lemma disjoint_arms_normalize (A B : Finset (Fin 26))
    (hA : basicArm A) (hB : basicArm B) (hd : Disjoint A B) :
    ∃ (k : Fin 7) (e : Equiv.Perm (Fin 26)),
      (∀ u v, graph.Adj (e u) (e v) ↔ graph.Adj u v) ∧
      ((A.image e = mode (representative k).1 ∧
        B.image e = mode (representative k).2) ∨
        (A.image e = mode (representative k).2 ∧
        B.image e = mode (representative k).1)) := by
  obtain ⟨k, e, he, hm⟩ := disjoint_arms_seven_representatives A B hA hB hd
  have inverse_image (S T : Finset (Fin 26)) (h : S.image e = T) : T.image e.symm = S := by
    rw [← h]
    simp [Finset.image_image, Function.comp_def]
  refine ⟨k, e.symm, ?_, ?_⟩
  · intro u v
    have h := he (e.symm u) (e.symm v)
    simpa only [Equiv.apply_symm_apply] using h.symm
  · rcases hm with ⟨ha, hb⟩ | ⟨hb, ha⟩
    · exact Or.inl ⟨inverse_image _ _ ha, inverse_image _ _ hb⟩
    · exact Or.inr ⟨inverse_image _ _ ha, inverse_image _ _ hb⟩

end PEqualNP.Outside.L_meta_2056.FirstOrOrbit
