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
